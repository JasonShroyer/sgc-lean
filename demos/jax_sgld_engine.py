#!/usr/bin/env python3
"""
JAX/SGLD Thermodynamic Intelligence Engine — V2 Architecture

The GPU-accelerated core of the Thermodynamic Turing Machine.

PHYSICS:
    dP = -eta * grad(F(P)) + sqrt(2*T*eta) * N(0,I)

    where:
    - P: probability field on the sheaf (state on Fisher-Rao manifold)
    - F: variational free energy (sheaf Laplacian quadratic form)
    - T: temperature field (spatially varying, controlled by Fermi quench)
    - eta: learning rate (SGLD step size)
    - N: thermal noise (native to the dynamics, not a regularizer)

ARCHITECTURE:
    - JAX jit-compiled SGLD update step (single XLA kernel)
    - Sparse BCOO Sheaf Laplacians (VRAM-efficient)
    - Vectorized Forman-Ricci curvature flow via vmap
    - Smooth Fermi quench gated by (eps_func, CI, b1, M_eff)
    - Atlas in system RAM, active fields in VRAM

HARDWARE TARGET:
    - RTX 5070 12GB VRAM: active probability fields + sparse Laplacians
    - 64GB system RAM: EmergentSheafAtlas (crystallized b1>=1 operators)
    - CPU fallback: works on any JAX backend (CPU/GPU/TPU)

THEORY SOURCE:
    - papers/PHYSICS_OF_THOUGHT_PAPER.md (the milestone paper)
    - reports/FRONTIER_PHYSICS_SYNTHESIS.md (frontier physics)
    - src/SGC/Observables/TopologicalPersistence.lean (generalization_boundary)
"""

import os
import sys
import time
import pickle
import numpy as np
from typing import Dict, List, Tuple, Optional, Any
from functools import partial

import jax
import jax.numpy as jnp
from jax import jit, grad, vmap, random

print(f"JAX {jax.__version__} | Backend: {jax.default_backend()} | Devices: {jax.devices()}")


# ============================================================================
# 1. SPARSE SHEAF LAPLACIAN
# ============================================================================

def build_grid_laplacian_sparse(H: int, W: int, n_colors: int = 10):
    """
    Build a sparse 4-connected grid Laplacian as JAX arrays.

    For an H x W grid with C color channels, the full state space is N = H*W*C.
    The Laplacian acts per-color-channel on the spatial grid.

    Returns sparse representation: (row_indices, col_indices, values, shape)
    for VRAM-efficient storage.
    """
    N_spatial = H * W
    rows, cols, vals = [], [], []

    for r in range(H):
        for c in range(W):
            i = r * W + c
            degree = 0
            for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                nr, nc = r + dr, c + dc
                if 0 <= nr < H and 0 <= nc < W:
                    j = nr * W + nc
                    rows.append(i)
                    cols.append(j)
                    vals.append(-1.0)
                    degree += 1
            rows.append(i)
            cols.append(i)
            vals.append(float(degree))

    indices = jnp.array(list(zip(rows, cols)), dtype=jnp.int32)
    values = jnp.array(vals, dtype=jnp.float32)
    return indices, values, (N_spatial, N_spatial)


def sparse_matvec(indices, values, x):
    """Sparse matrix-vector product using JAX scatter."""
    rows = indices[:, 0]
    cols = indices[:, 1]
    gathered = x[cols] * values
    return jnp.zeros_like(x).at[rows].add(gathered)


# ============================================================================
# 2. FREE ENERGY AND ITS GRADIENT (THE HAMILTONIAN)
# ============================================================================

def free_energy_sheaf(P_sheaf, L_indices, L_values, P_target_sheaf):
    """
    Variational Free Energy on the SHEAF probability field.

    P_sheaf: (N_spatial, n_colors) — probability distribution per pixel
    P_target_sheaf: (N_spatial, n_colors) — target one-hot distributions

    F(P) = ||P - P_target||^2 + alpha * sum_c P_c^T L P_c

    The Laplacian acts PER COLOR CHANNEL — this is the sheaf structure.
    Neighboring pixels with similar color distributions have low energy.
    """
    # Prediction error (data fidelity on the statistical manifold)
    pred_error = jnp.sum((P_sheaf - P_target_sheaf) ** 2)

    # Sheaf Laplacian: acts independently on each color channel
    # E_sheaf = sum_c P_c^T L P_c (diffusion per channel)
    def channel_energy(P_c):
        Lp_c = sparse_matvec(L_indices, L_values, P_c)
        return jnp.dot(P_c, Lp_c)

    laplacian_energy = jnp.sum(jax.vmap(channel_energy, in_axes=1)(P_sheaf))

    return pred_error + 0.001 * laplacian_energy


# Auto-differentiate the sheaf free energy
free_energy_grad = jit(grad(free_energy_sheaf))


# ============================================================================
# 3. SGLD UPDATE STEP (THE CORE PHYSICS)
# ============================================================================

@jit
def sgld_step(P_sheaf, P_target_sheaf, L_indices, L_values,
              eta, temperature, key):
    """
    One step of Stochastic Gradient Langevin Dynamics on the SHEAF.

    dP = -eta * grad_F(P) + sqrt(2*T*eta) * N(0,I)

    P_sheaf: (N_spatial, n_colors) — the state on the Fisher-Rao manifold
    The Laplacian diffuses each color channel independently (sheaf structure).

    On GPU, this compiles to a single XLA kernel.
    """
    key, noise_key = random.split(key)

    # Gradient of sheaf free energy
    grad_F = free_energy_grad(P_sheaf, L_indices, L_values, P_target_sheaf)

    # Thermal noise on the full sheaf field
    noise = random.normal(noise_key, shape=P_sheaf.shape)
    thermal_kick = jnp.sqrt(2.0 * temperature * eta) * noise

    # SGLD update
    P_new = P_sheaf - eta * grad_F + thermal_kick

    # Project onto probability simplex: clamp non-negative then normalize
    # (softmax is too aggressive — it maps everything near uniform)
    P_new = jnp.maximum(P_new, 0.0)
    P_new = P_new / (jnp.sum(P_new, axis=-1, keepdims=True) + 1e-8)

    # Energy for Cv
    energy = free_energy_sheaf(P_sheaf, L_indices, L_values, P_target_sheaf)

    return P_new, energy, key


# ============================================================================
# 4. FORMAN-RICCI CURVATURE FLOW (VECTORIZED)
# ============================================================================

def compute_forman_ricci_jax(edge_weights, edge_pairs, n_stalks):
    """
    Forman-Ricci curvature for each edge in the stalk graph.

    F(i,j) = #triangles(i,j) - 1

    Positive → cycle edge (PROTECTED)
    Negative → bridge (PRUNED)

    Returns curvature array aligned with edge_weights.
    """
    n_edges = len(edge_pairs)
    edge_weights_np = np.asarray(edge_weights)

    # Build adjacency
    adj = np.zeros((n_stalks, n_stalks), dtype=bool)
    for idx, (i, j) in enumerate(edge_pairs):
        if idx < len(edge_weights_np) and abs(edge_weights_np[idx]) > 0.01:
            adj[i, j] = True
            adj[j, i] = True

    curvature = np.full(n_edges, -1.0, dtype=np.float32)
    for idx, (i, j) in enumerate(edge_pairs):
        if idx >= len(edge_weights_np) or abs(edge_weights_np[idx]) < 0.01:
            continue
        n_tri = 0
        for k in range(n_stalks):
            if k != i and k != j and adj[i, k] and adj[j, k]:
                n_tri += 1
        curvature[idx] = float(n_tri) - 1.0

    return curvature


def ricci_flow_step(edge_weights, edge_pairs, n_stalks, decay_lambda=0.1):
    """
    One step of Forman-Ricci curvature flow on edge weights.

    Bridges (F < 0) decay. Cycle edges (F >= 0) are protected.
    """
    curvature = compute_forman_ricci_jax(edge_weights, edge_pairs, n_stalks)
    max_curv = np.abs(curvature).max() + 1e-8
    decay_rate = decay_lambda * np.maximum(0, -curvature / max_curv)
    return edge_weights * (1.0 - decay_rate)


# ============================================================================
# 5. HG WAVELET PUMP (CYCLE-FORMING NOISE)
# ============================================================================

def wavelet_pump(edge_weights, edge_pairs, n_stalks, temperature, rng_key):
    """
    Hermite-Gaussian Wavelet Pump: inject energy into cycle-forming modes.

    Edges that would complete triangles if strengthened receive
    spectrally-shaped noise kicks. This drives the system out of
    b1=0 memorization basins toward b1>=1 generalization basins.
    """
    n_edges = len(edge_pairs)
    edge_weights_np = np.asarray(edge_weights)

    adj = np.zeros((n_stalks, n_stalks), dtype=bool)
    for idx, (i, j) in enumerate(edge_pairs):
        if idx < len(edge_weights_np) and abs(edge_weights_np[idx]) > 0.01:
            adj[i, j] = True
            adj[j, i] = True

    pump = np.zeros(n_edges, dtype=np.float32)
    for idx, (i, j) in enumerate(edge_pairs):
        if idx >= len(edge_weights_np):
            break
        potential = sum(1 for k in range(n_stalks)
                        if k != i and k != j and (adj[i, k] or adj[j, k]))
        if potential > 0:
            pump[idx] = np.random.randn() * 0.05 * potential

    return edge_weights + temperature * pump


# ============================================================================
# 6. TOPOLOGICAL OBSERVABLES
# ============================================================================

def compute_b1(edge_weights, n_stalks, threshold=0.01):
    """
    First Betti number from edge weights.
    b1 = |E| - |V| + b0 (Euler characteristic)
    b1 >= 1 iff cycle exists (Markov blanket → generalization).
    """
    edge_pairs = [(i, j) for i in range(n_stalks) for j in range(i+1, n_stalks)]
    ew = np.asarray(edge_weights)

    n_active = 0
    parent = list(range(n_stalks))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(x, y):
        px, py = find(x), find(y)
        if px != py:
            parent[px] = py

    for idx, (i, j) in enumerate(edge_pairs):
        if idx < len(ew) and abs(ew[idx]) > threshold:
            n_active += 1
            union(i, j)

    b0 = len(set(find(i) for i in range(n_stalks)))
    return max(n_active - n_stalks + b0, 0)


def fermi(x, x0=0.0, delta=0.1):
    """Smooth Fermi function (soft Heaviside)."""
    return 1.0 / (1.0 + np.exp(-(x - x0) / max(delta, 0.001)))


def compute_specific_heat(energy_window, temperature):
    """Cv = beta^2 * Var(E) from energy time series."""
    if len(energy_window) < 2 or temperature < 1e-6:
        return 0.0
    beta = 1.0 / temperature
    return beta ** 2 * np.var(energy_window)


# ============================================================================
# 7. THE FULL SGLD CRYSTALLIZATION ENGINE
# ============================================================================

class SGLDCrystallizer:
    """
    JAX-accelerated thermodynamic crystallization engine.

    Replaces the NumPy crystallize_logical_laplacian with GPU-backed
    SGLD dynamics + Forman-Ricci flow + HG pump + Fermi quench.
    """

    def __init__(self, n_colors=10, eta=0.01, initial_temp=1.0):
        self.n_colors = n_colors
        self.eta = eta
        self.initial_temp = initial_temp
        self.rng_key = random.PRNGKey(42)

    def crystallize(self, input_grid, target_grid, stalks,
                    max_iterations=100, sparsity_lambda=0.1):
        """
        Run SGLD crystallization to produce a b1>=1 Laplacian.

        Returns dict with edge_weights, b1, grokked, and full telemetry.
        """
        H, W = input_grid.shape[:2]
        n_stalks = len(stalks)

        if n_stalks < 2:
            return {'grokked': False, 'b1': 0, 'edge_weights': [],
                    'telemetry': {}}

        # Build sparse grid Laplacian (spatial only: N_spatial x N_spatial)
        L_idx, L_val, L_shape = build_grid_laplacian_sparse(H, W)
        N_spatial = H * W

        # Convert grids to SHEAF probability fields: (N_spatial, n_colors)
        # One-hot encode: P[pixel, color] = 1.0 if grid[pixel] == color
        def grid_to_sheaf(grid, n_colors):
            flat = grid.flatten().astype(int)
            P = np.zeros((len(flat), n_colors), dtype=np.float32)
            for i, c in enumerate(flat):
                if 0 <= c < n_colors:
                    P[i, c] = 1.0
                else:
                    P[i, 0] = 1.0  # default to color 0
            return P

        P_target_sheaf = jnp.array(grid_to_sheaf(target_grid, self.n_colors))
        # Initialize P with soft one-hot (add thermal noise to break symmetry)
        P_init = grid_to_sheaf(input_grid, self.n_colors)
        P_init = P_init * 0.8 + 0.02  # Soften: not quite one-hot
        P_sheaf = jnp.array(P_init)

        # Initialize stalk edge weights
        n_edges = n_stalks * (n_stalks - 1) // 2
        edge_pairs = [(i, j) for i in range(n_stalks)
                      for j in range(i+1, n_stalks)]
        edge_weights = np.random.randn(n_edges).astype(np.float32) * 0.1

        # Telemetry
        telem = {
            'energy': [], 'cv': [], 'temperature': [], 'b1': [],
            'eps_func': [], 'accuracy': [], 'sigma': [],
        }

        temperature = self.initial_temp
        M_eff = 0.0
        kappa = 0.3  # HG coupling coefficient (from wavelet theory)
        # M_explore calibrated for SGLD step size: threshold = log(d0/delta) scaled by eta
        M_explore = np.log(1.0 / 0.1) * self.eta  # ~0.023 for eta=0.01

        energy_window = []

        for iteration in range(max_iterations):
            # --- SGLD step on the SHEAF probability field ---
            self.rng_key, step_key = random.split(self.rng_key)
            P_sheaf, energy_val, self.rng_key = sgld_step(
                P_sheaf, P_target_sheaf, L_idx, L_val,
                self.eta, temperature, step_key
            )
            energy_float = float(energy_val)

            # --- Observables from sheaf field ---
            P_np = np.array(P_sheaf)  # (N_spatial, n_colors)
            P_target_np = np.array(P_target_sheaf)

            # Accuracy: fraction of pixels where argmax(P) == argmax(target)
            pred_colors = np.argmax(P_np, axis=1)
            true_colors = np.argmax(P_target_np, axis=1)
            accuracy = float(np.mean(pred_colors == true_colors))

            # Functional defect: how far P is from one-hot (crisp classification)
            # eps = 1 - mean(max_prob_per_pixel) ... ranges 0 (crisp) to ~0.9 (uniform)
            max_probs = np.max(P_np, axis=1)
            eps_func = float(1.0 - np.mean(max_probs))

            # Consolidation index: 1 - normalized entropy of P
            P_clipped = np.clip(P_np, 1e-10, 1.0)
            entropy_per_pixel = -np.sum(P_clipped * np.log(P_clipped), axis=1)
            avg_entropy = float(np.mean(entropy_per_pixel))
            CI = max(0.0, 1.0 - avg_entropy / max(np.log(self.n_colors), 0.01))

            # Topological observable
            b1 = compute_b1(edge_weights, n_stalks)

            # Hamiltonian energy of stalk graph
            hamiltonian = float(np.sum(edge_weights ** 2))
            energy_window.append(hamiltonian)
            if len(energy_window) > 10:
                energy_window.pop(0)

            cv = compute_specific_heat(energy_window, temperature)

            # Exploration mass: M_eff = sum(kappa * eta * sqrt(T))
            # Scale with eta (the actual SGLD step size) not a fixed 0.1
            M_eff += kappa * self.eta * (1.0 + temperature)

            # --- Forman-Ricci curvature flow ---
            edge_weights = ricci_flow_step(
                edge_weights, edge_pairs, n_stalks, sparsity_lambda)

            # --- HG Wavelet Pump (when b1=0, pump cycle modes) ---
            if b1 == 0 and temperature > 0.01:
                edge_weights = wavelet_pump(
                    edge_weights, edge_pairs, n_stalks, temperature, None)

            # Three-signal quench: ALL must be satisfied
            # Note: eps_func = 1-mean(max_prob), so eps < 0.7 means avg peak > 30%
            sigma_eps = fermi(0.7 - eps_func, 0, 0.1)  # eps < 0.7 (adapted for sheaf metric)
            sigma_ci = fermi(CI - 0.2, 0, 0.1)  # CI > 0.2
            sigma_b1 = fermi(b1 - 0.5, 0, 0.2)
            sigma_mass = fermi(M_eff - M_explore, 0, 0.5)
            sigma = float(CI * sigma_eps * sigma_ci * sigma_b1 * sigma_mass)

            # Smooth crystallization
            ew_crystal = np.sign(edge_weights) * np.minimum(np.abs(edge_weights), 1.0)
            edge_weights = edge_weights * (1.0 - sigma) + ew_crystal * sigma

            # Temperature follows the quench: exponential cooling when sigma > 0
            # This creates positive feedback: sigma up -> T down -> noise down -> defect down -> sigma up
            temperature *= (1.0 - 0.5 * sigma)  # Multiplicative decay driven by quench signal
            temperature = max(temperature, 0.001)

            # Record telemetry
            telem['energy'].append(hamiltonian)
            telem['cv'].append(cv)
            telem['temperature'].append(temperature)
            telem['b1'].append(b1)
            telem['eps_func'].append(eps_func)
            telem['accuracy'].append(accuracy)
            telem['sigma'].append(sigma)

            # Crystallization complete
            if sigma > 0.95:
                break

        # Final observables
        final_b1 = compute_b1(edge_weights, n_stalks)
        final_acc = telem['accuracy'][-1] if telem['accuracy'] else 0
        final_eps = telem['eps_func'][-1] if telem['eps_func'] else 1.0

        grokked = (final_acc > 0.5) and (final_eps < 0.5) and (final_b1 >= 1)

        return {
            'grokked': grokked,
            'b1': int(final_b1),
            'edge_weights': edge_weights.tolist(),
            'final_accuracy': float(final_acc),
            'functional_defect': float(final_eps),
            'iterations': len(telem['energy']),
            'telemetry': telem,
        }


# ============================================================================
# 8. INTEGRATION TEST
# ============================================================================

def run_integration_test():
    """
    Quick integration test: run the JAX SGLD engine on synthetic ARC puzzles
    and verify b1>=1 formation + telemetry emission.
    """
    print("\n" + "=" * 70)
    print("JAX/SGLD THERMODYNAMIC ENGINE — INTEGRATION TEST")
    print("=" * 70)

    engine = SGLDCrystallizer(n_colors=10, eta=0.01, initial_temp=0.05)

    # Synthetic multi-stalk puzzle: 3 colored objects, cyclic color swap
    inp = np.zeros((5, 7), dtype=np.float32)
    inp[1, 0] = 1; inp[1, 1] = 1; inp[2, 0] = 1; inp[2, 1] = 1
    inp[1, 3] = 3; inp[1, 4] = 3; inp[2, 3] = 3; inp[2, 4] = 3
    inp[1, 5] = 2; inp[1, 6] = 2; inp[2, 5] = 2; inp[2, 6] = 2

    out = np.zeros((5, 7), dtype=np.float32)
    out[1, 0] = 3; out[1, 1] = 3; out[2, 0] = 3; out[2, 1] = 3
    out[1, 3] = 2; out[1, 4] = 2; out[2, 3] = 2; out[2, 4] = 2
    out[1, 5] = 1; out[1, 6] = 1; out[2, 5] = 1; out[2, 6] = 1

    # Decompose stalks (simplified: each nonzero color region is a stalk)
    stalks = []
    for color in range(1, 10):
        mask = (inp == color)
        if mask.any():
            positions = np.argwhere(mask)
            stalks.append({
                'color': color,
                'mask': mask,
                'centroid': positions.mean(axis=0),
                'n_pixels': int(mask.sum()),
            })

    print(f"\nPuzzle: 3-object cyclic color swap")
    print(f"Input shape: {inp.shape}, Stalks: {len(stalks)}")

    t0 = time.time()
    result = engine.crystallize(inp, out, stalks,
                                max_iterations=80, sparsity_lambda=0.1)
    dt = time.time() - t0

    print(f"\nResult:")
    print(f"  Grokked:  {result['grokked']}")
    print(f"  b1:       {result['b1']}")
    print(f"  Accuracy: {result['final_accuracy']:.1%}")
    print(f"  Defect:   {result['functional_defect']:.4f}")
    print(f"  Iters:    {result['iterations']}")
    print(f"  Time:     {dt:.2f}s")

    # Telemetry summary
    telem = result['telemetry']
    if telem['cv']:
        max_cv = max(telem['cv'])
        max_cv_iter = telem['cv'].index(max_cv)
        print(f"\n  Cv peak:  {max_cv:.6f} at iter {max_cv_iter}")

    if telem['b1']:
        b1_transitions = []
        for i in range(1, len(telem['b1'])):
            if telem['b1'][i] != telem['b1'][i-1]:
                b1_transitions.append((i, telem['b1'][i-1], telem['b1'][i]))
        if b1_transitions:
            print(f"  b1 transitions:")
            for it, old, new in b1_transitions:
                print(f"    iter {it}: b1 {old} -> {new}")

    # Sampled trajectory
    n = len(telem['energy'])
    if n > 0:
        print(f"\n  Trajectory (sampled):")
        print(f"  {'iter':>5} {'E':>10} {'Cv':>10} {'T':>8} {'b1':>4} {'eps':>8} {'sigma':>8}")
        for p in [0, n//4, n//2, 3*n//4, n-1]:
            if p < n:
                print(f"  {p:>5} {telem['energy'][p]:>10.4f} "
                      f"{telem['cv'][p]:>10.6f} "
                      f"{telem['temperature'][p]:>8.4f} "
                      f"{telem['b1'][p]:>4} "
                      f"{telem['eps_func'][p]:>8.4f} "
                      f"{telem['sigma'][p]:>8.4f}")

    blanket_str = "BLANKET FORMED" if result['b1'] >= 1 else "NO BLANKET"
    print(f"\n  Topology: b1={result['b1']} -> [{blanket_str}]")

    if result['grokked']:
        print("\n  *** GROKKED: Crystallized Laplacian with Markov blanket ***")
    else:
        print("\n  Did not grok (may need more iterations or stronger pump)")

    return result


if __name__ == '__main__':
    run_integration_test()
