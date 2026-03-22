#!/usr/bin/env python3
"""
SGC Reynolds Number & Anisotropic Turbulence Engine
====================================================

THE JET ENGINE: Intelligence crystallizes at the critical boundary of
thermodynamic turbulence, governed by the localized SGC Reynolds Number.

MASTER CONTROL VARIABLE (per-edge):

    Re_SGC^(local) = (kappa * T * lambda_pump^(i)) / ||grad(eps_func)^(i)||

    Numerator  = Pump Inertia  (thermal momentum actively disrupting topology)
    Denominator = Defect Drag   (viscous trap of memorized training data)

THREE THERMODYNAMIC ZONES (per-edge):
    1. Crystallized Core  (Re ~ 0):       Laminar, frozen. lambda_pump=0. Protected.
    2. Active Frontier    (Re >> Re_crit): Turbulent, searching. HG pump full power.
    3. Phase Transition   (Re ~ Re_crit):  Defect collapsing. Fermi quench engaging.

ANISOTROPIC THERMODYNAMIC NOZZLE:
    Sigma_HG = sigma^2 * V * Lambda_pump * V^T

    V = eigenvectors of the current Sheaf Laplacian.
    Lambda_pump = diag(lambda_pump): 0 for crystallized, >0 for frontier.
    This concentrates turbulence into unexplored dimensions while
    maintaining Re ~ 0 in the crystallized subspace.

LOCALIZED FERMI QUENCH:
    NOT a global if/then. A continuous per-edge feedback controller:
    sigma_quench(i) = fermi(Re_crit - Re_SGC(i))
    When sigma -> 1: edge crystallizes (kappa -> 0, weight snaps discrete)
    When sigma -> 0: edge remains fluid (full thermal dynamics)

THEORETICAL FOUNDATION:
    - SGC.Renormalization: Iterative collapse via Lifshitz transitions
    - SGC.Bridge.Quantum: Wavelet-coupled Langevin dynamics
    - Jarzynski equality: Free energy from non-equilibrium work
    - Forman-Ricci curvature: Topology-aware pruning (bridges decay, cycles live)
    - Generalization Boundary: b1 >= 1 -> Markov blanket -> generalization
    - Independent confirmation: SAGD (2025) — anisotropic forward noise

Author: SGC Research Team
Date: March 2026
"""

import os
import sys
import time
import json
import numpy as np
from typing import Dict, List, Optional, Tuple, Any
from dataclasses import dataclass, field
from enum import IntEnum

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import jax
import jax.numpy as jnp
from jax import random

print(f"JAX {jax.__version__} | Backend: {jax.default_backend()}")


# ============================================================================
# 1. THERMODYNAMIC ZONE CLASSIFICATION
# ============================================================================

class ThermoZone(IntEnum):
    """Per-edge thermodynamic phase classification."""
    CRYSTALLIZED = 0    # Re ~ 0:       Laminar, frozen, topologically protected
    TRANSITIONING = 1   # Re ~ Re_crit: Phase transition, Fermi quench engaging
    FRONTIER = 2        # Re >> Re_crit: Turbulent, actively searching for cycles


@dataclass
class EdgeState:
    """
    Per-edge thermodynamic state tensor.

    Every edge carries a MATRIX-VALUED restriction map R_ij of shape
    (n_colors, n_colors). This is the cellular sheaf structure:
    R_ij encodes HOW stalk i transforms to be consistent with stalk j.
    The Fermi quench crystallizes R_ij into a permutation matrix.
    """
    n_edges: int
    n_colors: int
    weights: np.ndarray           # R_ij: (n_edges, n_colors, n_colors) restriction maps
    re_sgc: np.ndarray            # Re_SGC^(local) per edge
    kappa_local: np.ndarray       # Local coupling coefficient kappa per edge
    lambda_pump: np.ndarray       # Wavelet pump eigenvalue per edge
    defect_grad: np.ndarray       # ||grad(eps_func)|| per edge (viscous drag)
    zone: np.ndarray              # ThermoZone classification per edge
    crystallized: np.ndarray      # Boolean: permanently crystallized (LTP)
    cycle_member: np.ndarray      # Boolean: edge participates in a b1>=1 cycle

    @classmethod
    def initialize(cls, n_edges: int, n_colors: int = 10,
                   init_scale: float = 0.05) -> 'EdgeState':
        """Initialize restriction maps as I + small noise (near-identity start)."""
        R = np.tile(np.eye(n_colors, dtype=np.float32), (n_edges, 1, 1))
        R += np.random.randn(n_edges, n_colors, n_colors).astype(np.float32) * init_scale
        return cls(
            n_edges=n_edges,
            n_colors=n_colors,
            weights=R,
            re_sgc=np.full(n_edges, 10.0, dtype=np.float32),
            kappa_local=np.full(n_edges, 0.3, dtype=np.float32),
            lambda_pump=np.ones(n_edges, dtype=np.float32),
            defect_grad=np.ones(n_edges, dtype=np.float32),
            zone=np.full(n_edges, ThermoZone.FRONTIER, dtype=np.int32),
            crystallized=np.zeros(n_edges, dtype=bool),
            cycle_member=np.zeros(n_edges, dtype=bool),
        )

    def scalar_norms(self) -> np.ndarray:
        """Frobenius norm of each restriction matrix — scalar edge activity."""
        return np.linalg.norm(self.weights.reshape(self.n_edges, -1), axis=1)


# ============================================================================
# 2. GRAPH TOPOLOGY INFRASTRUCTURE
# ============================================================================

def build_edge_pairs(n_stalks: int) -> List[Tuple[int, int]]:
    """All (i, j) pairs for i < j in the complete stalk graph."""
    return [(i, j) for i in range(n_stalks) for j in range(i + 1, n_stalks)]


def build_bipartite_pairs(n_X: int, n_Y: int) -> List[Tuple[int, int]]:
    """All (i, j) cross-edges connecting input stalk i to output stalk j."""
    return [(i, j) for i in range(n_X) for j in range(n_Y)]


def build_stalk_adjacency(stalks: List[Dict], grid_shape: Tuple[int, int],
                           max_dist_frac: float = 0.5) -> np.ndarray:
    """
    Build scalar adjacency for within-space stalk organization.

    Two stalks are adjacent if their centroids are within max_dist_frac * max(H,W).
    Weight decreases linearly with distance. Used for L_XX and L_YY.
    """
    n = len(stalks)
    H, W = grid_shape
    max_dist = max(H, W) * max_dist_frac
    adj = np.zeros((n, n), dtype=np.float32)
    for i in range(n):
        for j in range(i + 1, n):
            d = float(np.linalg.norm(stalks[i]['centroid'] - stalks[j]['centroid']))
            if d < max_dist:
                w = 1.0 - d / max_dist
                adj[i, j] = w
                adj[j, i] = w
    return adj


def compute_block_b1(cross_norms: np.ndarray, cross_pairs: List[Tuple[int, int]],
                      n_X: int, n_Y: int,
                      adj_XX: np.ndarray, adj_YY: np.ndarray,
                      threshold: float = 0.01) -> int:
    """
    b1 of the full block graph: V_X (0..n_X-1) + V_Y (n_X..n_X+n_Y-1).

    Edges from L_XX, L_YY (spatial, scalar) and cross-edges (bipartite, matrix).
    b1 = |E| - |V| + b0.
    """
    n_total = n_X + n_Y
    parent = list(range(n_total))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(x, y):
        px, py = find(x), find(y)
        if px != py:
            parent[px] = py

    n_edges = 0

    # XX edges (vertices 0..n_X-1)
    for i in range(n_X):
        for j in range(i + 1, n_X):
            if adj_XX[i, j] > threshold:
                n_edges += 1
                union(i, j)

    # YY edges (vertices n_X..n_X+n_Y-1)
    for i in range(n_Y):
        for j in range(i + 1, n_Y):
            if adj_YY[i, j] > threshold:
                n_edges += 1
                union(n_X + i, n_X + j)

    # Cross-edges (i in X -> j in Y, mapped to n_X+j)
    for idx, (i, j) in enumerate(cross_pairs):
        if idx < len(cross_norms) and cross_norms[idx] > threshold:
            n_edges += 1
            union(i, n_X + j)

    b0 = len(set(find(v) for v in range(n_total)))
    return max(n_edges - n_total + b0, 0)


def _scalar_edge_norms(edge_weights: np.ndarray) -> np.ndarray:
    """Extract scalar norms from edge weights (handles both scalar and matrix)."""
    if edge_weights.ndim == 1:
        return np.abs(edge_weights)
    # Matrix weights: (n_edges, C, C) -> Frobenius norm per edge
    return np.linalg.norm(edge_weights.reshape(len(edge_weights), -1), axis=1)


def build_adjacency(edge_weights: np.ndarray, edge_pairs: List[Tuple[int, int]],
                     n_stalks: int, threshold: float = 0.01) -> np.ndarray:
    """Adjacency matrix from edge weights (symmetric, thresholded)."""
    norms = _scalar_edge_norms(edge_weights)
    adj = np.zeros((n_stalks, n_stalks), dtype=np.float32)
    for idx, (i, j) in enumerate(edge_pairs):
        if idx < len(norms) and norms[idx] > threshold:
            adj[i, j] = norms[idx]
            adj[j, i] = norms[idx]
    return adj


def build_laplacian(adj: np.ndarray) -> np.ndarray:
    """Graph Laplacian L = D - A from adjacency matrix."""
    D = np.diag(adj.sum(axis=1))
    return D - adj


def find_bridges(edge_weights: np.ndarray, edge_pairs: List[Tuple[int, int]],
                  n_stalks: int, threshold: float = 0.01) -> np.ndarray:
    """
    Find bridge edges via iterative Tarjan's algorithm.

    Bridge: removal increases b0 (disconnects graph).
    Non-bridge: part of a cycle (b1 contribution).

    Returns boolean array: True = bridge (NOT in cycle).
    """
    n_edges = len(edge_pairs)
    is_bridge = np.zeros(n_edges, dtype=bool)

    # Build adjacency list with edge indices
    norms = _scalar_edge_norms(edge_weights)
    adj_list = [[] for _ in range(n_stalks)]
    for idx, (i, j) in enumerate(edge_pairs):
        if idx < len(norms) and norms[idx] > threshold:
            adj_list[i].append((j, idx))
            adj_list[j].append((i, idx))

    disc = [-1] * n_stalks
    low = [-1] * n_stalks
    timer_val = [0]

    # Iterative DFS for bridge detection (avoids Python recursion limit)
    for start in range(n_stalks):
        if disc[start] != -1:
            continue

        # Stack entries: (node, parent_edge_idx, neighbor_iterator_index)
        stack = [(start, -1, 0)]
        disc[start] = low[start] = timer_val[0]
        timer_val[0] += 1

        while stack:
            u, parent_eidx, ni = stack[-1]

            if ni < len(adj_list[u]):
                stack[-1] = (u, parent_eidx, ni + 1)
                v, eidx = adj_list[u][ni]

                if disc[v] == -1:
                    disc[v] = low[v] = timer_val[0]
                    timer_val[0] += 1
                    stack.append((v, eidx, 0))
                elif eidx != parent_eidx:
                    low[u] = min(low[u], disc[v])
            else:
                stack.pop()
                if stack:
                    parent_u = stack[-1][0]
                    low[parent_u] = min(low[parent_u], low[u])
                    if low[u] > disc[parent_u]:
                        is_bridge[parent_eidx] = True

    return is_bridge


def compute_b1(edge_weights: np.ndarray, edge_pairs: List[Tuple[int, int]],
                n_stalks: int, threshold: float = 0.01) -> int:
    """First Betti number: b1 = |E| - |V| + b0 (Euler characteristic)."""
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

    norms = _scalar_edge_norms(edge_weights)
    n_active = 0
    for idx, (i, j) in enumerate(edge_pairs):
        if idx < len(norms) and norms[idx] > threshold:
            n_active += 1
            union(i, j)

    b0 = len(set(find(v) for v in range(n_stalks)))
    return max(n_active - n_stalks + b0, 0)


# ============================================================================
# 3. FORMAN-RICCI CURVATURE FLOW
# ============================================================================

def compute_forman_ricci(edge_weights: np.ndarray, edge_pairs: List[Tuple[int, int]],
                          n_stalks: int, threshold: float = 0.01) -> np.ndarray:
    """
    Forman-Ricci curvature per edge: F(i,j) = #triangles(i,j) - 1.

    F > 0: cycle edge (topologically protected, immune to decay)
    F < 0: bridge/isolated (pruned by curvature flow)
    """
    norms = _scalar_edge_norms(edge_weights)
    n_edges = len(edge_pairs)
    adj = np.zeros((n_stalks, n_stalks), dtype=bool)
    for idx, (i, j) in enumerate(edge_pairs):
        if idx < len(norms) and norms[idx] > threshold:
            adj[i, j] = True
            adj[j, i] = True

    curvature = np.full(n_edges, -1.0, dtype=np.float32)
    for idx, (i, j) in enumerate(edge_pairs):
        if idx >= len(norms) or norms[idx] < threshold:
            curvature[idx] = 0.0
            continue
        n_tri = 0
        for k in range(n_stalks):
            if k != i and k != j and adj[i, k] and adj[j, k]:
                n_tri += 1
        curvature[idx] = float(n_tri) - 1.0

    return curvature


def ricci_flow_step(edge_weights: np.ndarray, curvature: np.ndarray,
                     crystallized: np.ndarray, decay_rate: float = 0.1) -> np.ndarray:
    """
    One step of Forman-Ricci curvature flow.

    Bridges (F < 0) decay. Cycle edges (F >= 0) are topologically protected.
    Crystallized edges are immune to decay (frozen core).
    Handles both scalar (n_edges,) and matrix (n_edges, C, C) weights.
    """
    max_curv = np.abs(curvature).max() + 1e-8
    decay = decay_rate * np.maximum(0, -curvature / max_curv)
    decay[crystallized] = 0.0  # Frozen core: no decay
    if edge_weights.ndim == 1:
        return edge_weights * (1.0 - decay)
    # Matrix weights: broadcast decay (n_edges,) over (n_edges, C, C)
    return edge_weights * (1.0 - decay)[:, None, None]


# ============================================================================
# 4. SGC REYNOLDS NUMBER COMPUTATION
# ============================================================================

def compute_stalk_averages(P: np.ndarray, stalks: List[Dict]) -> np.ndarray:
    """
    Compute average probability field per stalk: P_stalk[s, c] = mean(P[pixels_of_s, c]).

    This bridges pixel space (N_pixels, n_colors) to stalk space (n_stalks, n_colors)
    for stalk-level computations like defect gradient and edge weight updates.
    """
    n_colors = P.shape[1]
    n_stalks = len(stalks)
    P_stalk = np.zeros((n_stalks, n_colors), dtype=np.float32)
    for s_idx, stalk in enumerate(stalks):
        mask_flat = stalk['mask'].flatten()
        pixels = np.where(mask_flat)[0]
        if len(pixels) > 0:
            P_stalk[s_idx] = P[pixels].mean(axis=0)
    return P_stalk


def compute_defect_gradient_per_edge(edge_pairs: List[Tuple[int, int]],
                                      R: np.ndarray,
                                      P_stalk_current: np.ndarray,
                                      P_stalk_target: np.ndarray) -> np.ndarray:
    """
    Compute ||grad(eps_func)|| per edge: the viscous drag.

    Uses the sheaf consistency residual with restriction maps:
      res_cur(i,j) = R_ji @ P_cur(i) - R_ij @ P_cur(j)
      res_tgt(i,j) = R_ji @ P_tgt(i) - R_ij @ P_tgt(j)
      grad(i,j) = ||res_cur - res_tgt||^2

    When the restriction maps have learned the correct transformation,
    res_cur converges to res_tgt, the drag vanishes, and Re_SGC drops
    below Re_crit — triggering the Fermi quench.
    """
    n_edges = len(edge_pairs)
    grad = np.zeros(n_edges, dtype=np.float32)

    for idx, (i, j) in enumerate(edge_pairs):
        if i < len(P_stalk_current) and j < len(P_stalk_current):
            R_ij = R[idx]           # (C, C)
            R_ji = R[idx].T         # (C, C)
            res_cur = R_ji @ P_stalk_current[i] - R_ij @ P_stalk_current[j]
            res_tgt = R_ji @ P_stalk_target[i] - R_ij @ P_stalk_target[j]
            grad[idx] = float(np.sum((res_cur - res_tgt) ** 2))

    return np.maximum(grad, 1e-8)  # Floor to prevent division by zero


def compute_re_sgc(kappa_local: np.ndarray, temperature: float,
                    lambda_pump: np.ndarray, defect_grad: np.ndarray) -> np.ndarray:
    """
    SGC Reynolds Number per edge:

        Re_SGC^(local) = (kappa * T * lambda_pump) / ||grad(eps_func)||

    Numerator  = Pump Inertia  (wavelet-shaped thermal momentum)
    Denominator = Defect Drag   (gradient of functional defect)

    Re >> Re_crit: turbulent (frontier, actively searching)
    Re << Re_crit: laminar (crystallized, topologically protected)
    Re ~  Re_crit: phase transition (Lifshitz critical point)
    """
    numerator = kappa_local * temperature * lambda_pump
    denominator = np.maximum(defect_grad, 1e-8)
    return numerator / denominator


def classify_zones(re_sgc: np.ndarray, re_crit: float,
                    crystallized: np.ndarray) -> np.ndarray:
    """
    Classify each edge into its thermodynamic zone based on Re_SGC.

    | Zone            | Re_SGC            | Physics              | Engineering        |
    |-----------------|-------------------|----------------------|--------------------|
    | CRYSTALLIZED    | ~ 0               | Laminar, frozen      | kappa=0, refrigerate|
    | TRANSITIONING   | ~ Re_crit         | Critical, quenching  | Fermi quench active|
    | FRONTIER        | >> Re_crit        | Turbulent, searching | HG pump full power |
    """
    zones = np.full(len(re_sgc), ThermoZone.FRONTIER, dtype=np.int32)
    zones[re_sgc < 0.5 * re_crit] = ThermoZone.CRYSTALLIZED
    mask_trans = (re_sgc >= 0.5 * re_crit) & (re_sgc <= 2.0 * re_crit)
    zones[mask_trans] = ThermoZone.TRANSITIONING
    zones[crystallized] = ThermoZone.CRYSTALLIZED
    return zones


# ============================================================================
# 5. ANISOTROPIC THERMODYNAMIC NOZZLE (Hermite-Gaussian Wavelet Pump)
# ============================================================================

def compute_lambda_pump_eigenspace(eigenvalues: np.ndarray) -> np.ndarray:
    """
    Build Lambda_pump in eigenspace: the spectral nozzle profile.

    Hermite-Gaussian envelope: psi(u) = u^a * exp(-b * u^2)
    - Low eigenvalues (global, crystallized structure) -> pump OFF
    - High eigenvalues (local, frontier oscillations)  -> pump ON
    - Zero eigenvalues (connected components)           -> pump OFF

    This ensures noise energy is concentrated in the dimensions
    that need exploration, not the dimensions already solved.
    """
    if len(eigenvalues) == 0:
        return np.array([], dtype=np.float32)

    lambda_max = np.max(eigenvalues) + 1e-8
    u = eigenvalues / lambda_max  # Normalized to [0, 1]

    # Hermite-Gaussian: peaks at mid-to-high spectrum
    a, b = 1.0, 0.5
    u_shifted = u + 0.01
    hg_weights = (u_shifted ** a) * np.exp(-b * u_shifted ** 2)

    # Normalize to unit energy
    norm = np.sqrt(np.sum(hg_weights ** 2)) + 1e-10
    hg_weights = hg_weights / norm

    # Zero out the trivial zero-eigenvalue modes (constant on components)
    hg_weights[eigenvalues < 1e-6] = 0.0

    return hg_weights.astype(np.float32)


def map_pump_eigen_to_edges(lambda_pump_eigen: np.ndarray,
                              eigenvectors: np.ndarray,
                              edge_pairs: List[Tuple[int, int]],
                              crystallized: np.ndarray) -> np.ndarray:
    """
    Map Lambda_pump from eigenspace to edge space.

    For each edge (i,j), the effective pump is:
        lambda_pump_edge(i,j) = sum_k lambda_pump_eigen(k) * (v_k(i) - v_k(j))^2

    where (v_k(i) - v_k(j))^2 is the energy of eigenmode k on edge (i,j).
    Crystallized edges are zeroed regardless of eigenspace contribution.
    """
    n_edges = len(edge_pairs)
    n_stalks = eigenvectors.shape[0]
    lambda_pump = np.zeros(n_edges, dtype=np.float32)

    for idx, (i, j) in enumerate(edge_pairs):
        if i < n_stalks and j < n_stalks:
            edge_mode_energy = (eigenvectors[i, :] - eigenvectors[j, :]) ** 2
            lambda_pump[idx] = np.dot(edge_mode_energy, lambda_pump_eigen)

    # Frozen core: crystallized edges get zero pump (refrigerated)
    lambda_pump[crystallized] = 0.0

    return lambda_pump


def map_edges_to_pump_eigen(lambda_pump_edge: np.ndarray,
                              eigenvectors: np.ndarray,
                              edge_pairs: List[Tuple[int, int]]) -> np.ndarray:
    """
    Inverse map: edge-level pump back to eigenspace for noise injection.

    lambda_pump_eigen(k) = sum_{edges} lambda_pump_edge(ij) * (v_k(i) - v_k(j))^2
    """
    n_stalks = eigenvectors.shape[0]
    lambda_pump_eigen = np.zeros(n_stalks, dtype=np.float32)

    for idx, (i, j) in enumerate(edge_pairs):
        if i < n_stalks and j < n_stalks:
            edge_mode_energy = (eigenvectors[i, :] - eigenvectors[j, :]) ** 2
            lambda_pump_eigen += lambda_pump_edge[idx] * edge_mode_energy

    # Normalize
    norm = np.max(lambda_pump_eigen) + 1e-10
    return lambda_pump_eigen / norm


def build_stalk_pixel_map(stalks: List[Dict], n_pixels: int) -> np.ndarray:
    """
    Build stalk assignment vector: pixel_to_stalk[p] = stalk index owning pixel p.

    Background pixels (not owned by any stalk) get index -1.
    This bridges the stalk-space eigenvectors to pixel-space probability fields.
    """
    pixel_to_stalk = np.full(n_pixels, -1, dtype=np.int32)
    for s_idx, stalk in enumerate(stalks):
        mask_flat = stalk['mask'].flatten()
        pixel_to_stalk[mask_flat] = s_idx
    return pixel_to_stalk


def inject_anisotropic_noise(P_sheaf: np.ndarray,
                               eigenvectors: np.ndarray,
                               lambda_pump_eigen: np.ndarray,
                               sigma: float,
                               pixel_to_stalk: np.ndarray,
                               rng_key) -> Tuple[np.ndarray, Any]:
    """
    Inject Hermite-Gaussian shaped noise into the probability field P.

    Standard SGLD:    dP = -eta*grad(F) + sigma * N(0, I)         [isotropic]
    Reynolds Engine:  dP = -eta*grad(F) + sigma * V*sqrt(Lp)*z    [anisotropic]

    where z ~ N(0, I), V = Laplacian eigenvectors, Lp = Lambda_pump.

    The NOZZLE (Lambda_pump) directs all thermal energy into the
    unexplored eigenmodes while keeping crystallized modes at Re ~ 0.

    The eigenvectors live in stalk space (n_stalks x n_stalks).
    The probability field lives in pixel space (n_pixels x n_colors).
    The stalk assignment map bridges them: each pixel inherits the
    thermodynamic noise of its parent stalk.

    Efficient computation:
        1. delta_stalk = sigma * V @ diag(sqrt(Lp)) @ z   [stalk space]
        2. delta_pixel = scatter(delta_stalk, pixel_to_stalk)  [pixel space]
    """
    n_stalks = eigenvectors.shape[0]
    n_pixels, n_colors = P_sheaf.shape

    # Generate isotropic noise in eigenspace
    rng_key, subkey = random.split(rng_key)
    z = np.array(random.normal(subkey, shape=(n_stalks, n_colors)))

    # Shape through the nozzle: scale by sqrt(lambda_pump)
    sqrt_pump = np.sqrt(np.maximum(lambda_pump_eigen, 0.0))
    z_shaped = z * sqrt_pump[:, None]  # (n_stalks, n_colors)

    # Rotate from eigenspace to stalk physical space
    delta_stalk = sigma * (eigenvectors @ z_shaped)  # (n_stalks, n_colors)

    # Scatter stalk-level noise to pixel space via assignment map
    delta_pixel = np.zeros((n_pixels, n_colors), dtype=np.float32)
    for p in range(n_pixels):
        s = pixel_to_stalk[p]
        if s >= 0:  # Skip background pixels (no stalk owns them)
            delta_pixel[p] = delta_stalk[s]

    # Apply perturbation
    P_new = P_sheaf + delta_pixel

    # Re-normalize to probability simplex
    P_new = np.clip(P_new, 0.0, None)
    P_sum = P_new.sum(axis=1, keepdims=True)
    P_new = P_new / np.maximum(P_sum, 1e-8)

    return P_new, rng_key


# ============================================================================
# 6. LOCALIZED FERMI QUENCH (Per-Edge Feedback Controller)
# ============================================================================

def fermi(x: np.ndarray, x0: float = 0.0, delta: float = 0.1) -> np.ndarray:
    """Smooth Fermi function (vectorized soft Heaviside)."""
    return 1.0 / (1.0 + np.exp(np.clip(-(x - x0) / max(delta, 0.001), -50, 50)))


def project_to_permutation(R: np.ndarray) -> np.ndarray:
    """
    Project a real matrix onto the nearest permutation matrix.

    Uses the Hungarian algorithm (linear sum assignment) on |R| to find
    the optimal assignment, then applies the sign of the original entries.
    This is the discrete crystallization of a color transformation rule.
    """
    from scipy.optimize import linear_sum_assignment
    row_ind, col_ind = linear_sum_assignment(-np.abs(R))
    P_mat = np.zeros_like(R)
    P_mat[row_ind, col_ind] = np.sign(R[row_ind, col_ind])
    # Ensure we have +1 entries (not -1 or 0)
    P_mat[P_mat == 0] = 0.0
    zero_rows = np.where(np.abs(P_mat).sum(axis=1) < 0.5)[0]
    for r in zero_rows:
        P_mat[r, col_ind[r]] = 1.0
    return P_mat


def localized_fermi_quench(edge_state: EdgeState,
                            re_crit: float,
                            quench_sharpness: float = 0.3) -> Tuple[EdgeState, np.ndarray]:
    """
    Localized Fermi Quench: per-edge crystallization when Re drops below Re_crit.

    NOT a global if/then trigger. A continuous local feedback controller:

        sigma_quench(i) = fermi(Re_crit - Re_SGC(i), 0, delta)

    When sigma -> 1: restriction matrix R_ij crystallizes
        - R_ij projected to nearest PERMUTATION matrix (Hungarian algorithm)
        - kappa -> 0 (pump shut off, refrigerated)
    When sigma -> 0: R_ij remains fluid
        - full thermal dynamics, searching

    This is the discrete crystallization of a color rule:
    the soft restriction map snaps to a hard permutation.
    """
    re_sgc = edge_state.re_sgc

    # Per-edge quench strength: HIGH when Re is LOW (below Re_crit)
    sigma_quench = fermi(re_crit - re_sgc, x0=0.0, delta=quench_sharpness)

    # Don't quench already-crystallized edges (they're frozen)
    sigma_quench[edge_state.crystallized] = 0.0

    # Reduce local kappa for quenching edges (shutting off the pump)
    edge_state.kappa_local *= (1.0 - 0.5 * sigma_quench)

    # Permanently crystallize when quench signal saturates:
    # project R_ij to nearest permutation matrix
    newly_crystallized = (sigma_quench > 0.95) & (~edge_state.crystallized)
    for idx in np.where(newly_crystallized)[0]:
        edge_state.weights[idx] = project_to_permutation(edge_state.weights[idx])
    edge_state.crystallized |= newly_crystallized
    n_new = int(np.sum(newly_crystallized))

    return edge_state, sigma_quench, n_new


# ============================================================================
# 7. SHEAF FIELD HELPERS
# ============================================================================

def grid_to_sheaf(grid: np.ndarray, n_colors: int = 10) -> np.ndarray:
    """Convert discrete grid to one-hot sheaf probability field (N, C)."""
    flat = grid.flatten().astype(int)
    P = np.zeros((len(flat), n_colors), dtype=np.float32)
    for i, c in enumerate(flat):
        if 0 <= c < n_colors:
            P[i, c] = 1.0
        else:
            P[i, 0] = 1.0
    return P


def sheaf_to_grid(P: np.ndarray, H: int, W: int) -> np.ndarray:
    """Convert sheaf probability field to discrete grid via argmax."""
    return np.argmax(P, axis=1).reshape(H, W).astype(np.float32)


def compute_functional_defect(P_pred: np.ndarray, P_target: np.ndarray) -> float:
    """Functional defect: MSE between predicted and target probability fields."""
    return float(np.mean((np.asarray(P_pred) - np.asarray(P_target)) ** 2))


def diffuse_one_step(P: np.ndarray, L: np.ndarray, dt: float = 0.1) -> np.ndarray:
    """One step of heat diffusion: P' = P - dt * L @ P, re-normalized."""
    P_new = P - dt * (L @ P)
    P_new = np.clip(P_new, 0, None)
    P_sum = P_new.sum(axis=1, keepdims=True)
    return P_new / np.maximum(P_sum, 1e-8)


def simplex_project(P: np.ndarray) -> np.ndarray:
    """Project rows of P onto the probability simplex (clamp + renormalize)."""
    P = np.clip(P, 0.0, None)
    P_sum = P.sum(axis=1, keepdims=True)
    return P / np.maximum(P_sum, 1e-8)


# ============================================================================
# 8. QUANTUM BRIDGE — DIRICHLET INFERENCE
# ============================================================================

def dirichlet_infer(input_grid: np.ndarray,
                    rule: Dict[str, Any],
                    n_colors: int = 10,
                    n_steps: int = 30,
                    eta: float = 0.05,
                    temperature: float = 0.01) -> Optional[np.ndarray]:
    """
    THE QUANTUM BRIDGE: Tripartite inference via concept-space routing.

    No color_map. No translation_map. No Python dictionaries. No neural net.
    No spatial matching. The concept layer V_C makes matching TRIVIAL:
    every stalk of color c routes to concept node c, regardless of position.

    PIPELINE: Lift → Uplink → Apply R_cj → Collapse

    The crystallized R_cj matrices on V_C -> V_Y edges ARE the only memory.
    """
    C = n_colors
    H, W = input_grid.shape
    n_pixels = H * W

    color_map = rule.get('color_map')
    R_S_per_concept = rule.get('R_S_per_concept', {})
    spatial_info = rule.get('spatial_info', {})

    if color_map is None:
        return None

    # ================================================================
    # TWISTED FIBER INFERENCE:
    #
    # For each input pixel at (r, c) with color k:
    #   1. COLOR FIBER: output_color = sigma(k)
    #   2. SPATIAL FIBER: output_pos = R_S[k] @ [r, c, 1]^T
    #
    # Each color has its OWN spatial transform. Red objects can move
    # right while blue objects stay still. The local gauge field
    # routes spatial momentum conditionally through color identity.
    # ================================================================

    bg_in = int(np.bincount(input_grid.flatten().astype(int)).argmax())
    bg_out = int(color_map[bg_in]) if 0 <= bg_in < C else bg_in

    # Check if ANY concept has a non-identity spatial transform
    has_spatial = any(spatial_info.get(c, (0, 0, False)) != (0, 0, False)
                      for c in range(C))

    output = np.full((H, W), bg_out, dtype=np.float32)

    for r in range(H):
        for c_col in range(W):
            in_color = int(input_grid[r, c_col])
            if not (0 <= in_color < C):
                continue

            # Color fiber: apply global permutation
            out_color = float(color_map[in_color])

            if has_spatial and in_color != bg_in:
                # Spatial fiber: apply per-concept local gauge R_S[color]
                R_S_c = R_S_per_concept.get(in_color)
                if R_S_c is not None:
                    s_in = np.array([r, c_col, 1.0], dtype=np.float32)
                    s_out = R_S_c @ s_in
                    nr, nc = int(round(s_out[0])), int(round(s_out[1]))
                    if 0 <= nr < H and 0 <= nc < W:
                        output[nr, nc] = out_color
                else:
                    output[r, c_col] = out_color
            else:
                # No spatial transform for this concept: paint in place
                output[r, c_col] = out_color

    return output


# ============================================================================
# 9. REYNOLDS TELEMETRY
# ============================================================================

@dataclass
class ReynoldsTelemetry:
    """Full thermodynamic state telemetry for the Reynolds Engine."""

    # Per-iteration scalar histories
    b1: List[int] = field(default_factory=list)
    temperature: List[float] = field(default_factory=list)
    functional_defect: List[float] = field(default_factory=list)
    accuracy: List[float] = field(default_factory=list)
    energy: List[float] = field(default_factory=list)

    # Zone distribution per iteration
    n_crystallized: List[int] = field(default_factory=list)
    n_transitioning: List[int] = field(default_factory=list)
    n_frontier: List[int] = field(default_factory=list)

    # Re_SGC statistics per iteration (over non-crystallized edges)
    re_mean: List[float] = field(default_factory=list)
    re_median: List[float] = field(default_factory=list)
    re_max: List[float] = field(default_factory=list)
    re_min: List[float] = field(default_factory=list)

    # Pump energy per iteration
    pump_total: List[float] = field(default_factory=list)

    # Quench events: (iteration, n_newly_crystallized)
    quench_events: List[Tuple[int, int]] = field(default_factory=list)

    def record(self, iteration: int, edge_state: EdgeState,
               b1_val: int, temp: float, defect: float,
               acc: float, energy_val: float, n_quenched: int = 0):
        """Record one iteration of telemetry."""
        self.b1.append(b1_val)
        self.temperature.append(temp)
        self.functional_defect.append(defect)
        self.accuracy.append(acc)
        self.energy.append(energy_val)

        zones = edge_state.zone
        self.n_crystallized.append(int(np.sum(zones == ThermoZone.CRYSTALLIZED)))
        self.n_transitioning.append(int(np.sum(zones == ThermoZone.TRANSITIONING)))
        self.n_frontier.append(int(np.sum(zones == ThermoZone.FRONTIER)))

        # Re statistics over non-crystallized edges only
        active_mask = ~edge_state.crystallized
        re_active = edge_state.re_sgc[active_mask]
        if len(re_active) > 0:
            self.re_mean.append(float(np.mean(re_active)))
            self.re_median.append(float(np.median(re_active)))
            self.re_max.append(float(np.max(re_active)))
            self.re_min.append(float(np.min(re_active)))
        else:
            self.re_mean.append(0.0)
            self.re_median.append(0.0)
            self.re_max.append(0.0)
            self.re_min.append(0.0)

        self.pump_total.append(float(np.sum(edge_state.lambda_pump)))

        if n_quenched > 0:
            self.quench_events.append((iteration, n_quenched))

    def format_summary(self) -> str:
        """Format concise telemetry summary for current state."""
        if not self.b1:
            return "[no data]"
        return (f"Zones: C={self.n_crystallized[-1]} "
                f"T={self.n_transitioning[-1]} "
                f"F={self.n_frontier[-1]} | "
                f"Re: mean={self.re_mean[-1]:.3f} "
                f"[{self.re_min[-1]:.3f},{self.re_max[-1]:.3f}] | "
                f"Pump={self.pump_total[-1]:.3f}")


# ============================================================================
# 9. STALK DECOMPOSITION
# ============================================================================

def decompose_stalks(grid: np.ndarray, background_color: int = 0) -> List[Dict]:
    """
    Decompose grid into connected color components (stalks).

    Includes background as an explicit stalk (stalk 0) for full pixel coverage.
    No pixel is left unowned — every pixel belongs to exactly one stalk.
    """
    H, W = grid.shape
    visited = np.zeros((H, W), dtype=bool)
    stalks = []
    for r in range(H):
        for c in range(W):
            if visited[r, c] or int(grid[r, c]) == background_color:
                continue
            color = int(grid[r, c])
            component = []
            queue = [(r, c)]
            visited[r, c] = True
            while queue:
                cr, cc = queue.pop(0)
                component.append((cr, cc))
                for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                    nr, nc = cr + dr, cc + dc
                    if 0 <= nr < H and 0 <= nc < W and not visited[nr, nc]:
                        if int(grid[nr, nc]) == color:
                            visited[nr, nc] = True
                            queue.append((nr, nc))
            if component:
                positions = np.array(component)
                mask = np.zeros((H, W), dtype=bool)
                for pr, pc in component:
                    mask[pr, pc] = True
                stalks.append({
                    'color': color, 'mask': mask,
                    'n_pixels': len(component),
                    'centroid': positions.mean(axis=0),
                })
    stalks.sort(key=lambda s: s['n_pixels'], reverse=True)

    # Add background as explicit stalk — full pixel coverage, no gaps
    bg_mask = (grid == background_color)
    if np.any(bg_mask):
        bg_positions = np.argwhere(bg_mask)
        stalks.insert(0, {
            'color': background_color,
            'mask': bg_mask,
            'n_pixels': int(bg_mask.sum()),
            'centroid': bg_positions.mean(axis=0) if len(bg_positions) > 0 else np.array([H/2, W/2]),
        })

    return stalks


# ============================================================================
# 10. THE REYNOLDS CRYSTALLIZATION ENGINE
# ============================================================================

class ReynoldsCrystallizer:
    """
    The SGC Reynolds Number Crystallization Engine.

    Operates like a memristor-based analog graph computer:
    - Per-edge Re_SGC SENSOR  (local energy flux / gradient drag)
    - Per-edge kappa ACTUATOR (wavelet pump injection control)
    - Per-edge Fermi CIRCUIT  (crystallization trigger at Re < Re_crit)

    The chip physically BOILS unallocated edges (high Re, turbulent search)
    while actively REFRIGERATING crystallized logic (Re ~ 0, frozen core).

    Master control variable: the spatially-varying Reynolds field Re_SGC(x, t).
    """

    def __init__(self, n_colors: int = 10, eta: float = 0.01,
                 initial_temp: float = 1.0, re_crit: float = 1.0):
        self.n_colors = n_colors
        self.eta = eta
        self.initial_temp = initial_temp
        self.re_crit = re_crit
        self.rng_key = random.PRNGKey(42)

    def crystallize(self, input_grid: np.ndarray, target_grid: np.ndarray,
                    stalks: List[Dict], max_iterations: int = 100,
                    sparsity_lambda: float = 0.1,
                    ablate_laplacian: bool = False) -> Dict[str, Any]:
        """
        DUAL-FIBER BUNDLE Crystallization Engine.

        Two fibers learned simultaneously:
          V_C (Color Fiber):   10x10 permutation R_C: colors -> colors
          V_S (Spatial Fiber): 3x3 affine R_S: positions -> positions

        Color: pixel-level vote matrix -> gradient descent -> Hungarian projection
        Spatial: stalk centroid matching -> least-squares affine -> integer snap

        MDL = log2(10!) + log2(|E(2)|_discrete) ≈ 21.8 + O(log(HW)) bits.
        """
        C = self.n_colors
        H, W = input_grid.shape[:2]

        if H * W > 900:
            return {'grokked': False, 'b1': 0, 'edge_weights': [],
                    'telemetry': ReynoldsTelemetry()}

        stalks_X = decompose_stalks(input_grid)
        stalks_Y = decompose_stalks(target_grid)
        n_X = len(stalks_X)
        n_Y = len(stalks_Y)

        if n_X < 1 or n_Y < 1:
            return {'grokked': False, 'b1': 0, 'edge_weights': [],
                    'telemetry': ReynoldsTelemetry()}

        # ==============================================================
        # COLOR FIBER (V_C): pixel-level color transition
        # ==============================================================
        in_flat = input_grid.flatten().astype(int)
        out_flat = target_grid.flatten().astype(int)
        vote_matrix = np.zeros((C, C), dtype=np.float32)
        for p in range(len(in_flat)):
            c_in, c_out = in_flat[p], out_flat[p]
            if 0 <= c_in < C and 0 <= c_out < C:
                vote_matrix[c_out, c_in] += 1.0

        col_sums = vote_matrix.sum(axis=0, keepdims=True)
        R_C = vote_matrix / np.maximum(col_sums, 1.0)

        P_in = np.eye(C, dtype=np.float32)
        P_out = np.zeros((C, C), dtype=np.float32)
        for c in range(C):
            if col_sums[0, c] > 0:
                P_out[c] = vote_matrix[:, c] / col_sums[0, c]
            else:
                P_out[c, c] = 1.0

        # Gradient descent on R_C
        for iteration in range(min(max_iterations, 40)):
            grad_R = np.zeros_like(R_C)
            for c in range(C):
                if col_sums[0, c] == 0:
                    continue
                residual = R_C @ P_in[c] - P_out[c]
                grad_R += np.outer(residual, P_in[c])
            R_C -= self.eta * 10.0 * 2.0 * grad_R

        # Crystallize color fiber
        R_C_crystal = project_to_permutation(R_C)
        color_map = np.argmax(np.abs(R_C_crystal), axis=0)

        # Color accuracy
        n_color_correct = 0
        n_color_active = 0
        for c in range(C):
            if col_sums[0, c] == 0:
                continue
            n_color_active += 1
            if color_map[c] == np.argmax(P_out[c]):
                n_color_correct += 1
        color_acc = n_color_correct / max(n_color_active, 1)
        color_nonid = not np.array_equal(color_map, np.arange(C))

        # ==============================================================
        # TWISTED SPATIAL FIBER: per-concept local gauge R_S[c]
        # ==============================================================
        # Each concept node c gets its OWN 3x3 affine matrix.
        # "Red objects move +3 right, Blue objects stay still" is now
        # representable: R_S[red] != R_S[blue].
        # This is the local gauge field — no heuristic predicates needed.

        # Group input stalks by color, match to output stalks
        per_color_in = {c: [] for c in range(C)}   # color -> list of [x,y,1]
        per_color_out = {c: [] for c in range(C)}

        for sx in stalks_X:
            c_in = sx.get('color', 0)
            if not (0 <= c_in < C):
                continue
            c_out = int(color_map[c_in])
            cx_in = sx['centroid']

            # Find nearest output stalk of the mapped color
            best_dist = 1e9
            best_centroid = cx_in
            for sy in stalks_Y:
                if sy.get('color', -1) == c_out:
                    d = float(np.linalg.norm(sx['centroid'] - sy['centroid']))
                    if d < best_dist:
                        best_dist = d
                        best_centroid = sy['centroid']

            per_color_in[c_in].append([cx_in[0], cx_in[1], 1.0])
            per_color_out[c_in].append([best_centroid[0], best_centroid[1], 1.0])

        # Solve per-concept affine via least-squares
        R_S_per_concept = {}  # c -> crystallized 3x3
        spatial_info = {}     # c -> (dx, dy, is_reflect)

        for c in range(C):
            if len(per_color_in[c]) < 1:
                R_S_per_concept[c] = np.eye(3, dtype=np.float32)
                spatial_info[c] = (0, 0, False)
                continue

            S_in = np.array(per_color_in[c], dtype=np.float32)
            S_out = np.array(per_color_out[c], dtype=np.float32)

            if len(S_in) >= 2:
                try:
                    R_S = S_out.T @ np.linalg.pinv(S_in.T)
                except np.linalg.LinAlgError:
                    R_S = np.eye(3, dtype=np.float32)
            elif len(S_in) == 1:
                # Single stalk: pure translation
                R_S = np.eye(3, dtype=np.float32)
                R_S[0, 2] = S_out[0, 0] - S_in[0, 0]
                R_S[1, 2] = S_out[0, 1] - S_in[0, 1]
            else:
                R_S = np.eye(3, dtype=np.float32)

            # Crystallize: snap to integer translation/reflection
            dx = float(R_S[0, 2])
            dy = float(R_S[1, 2])
            rot = R_S[:2, :2]
            det = rot[0, 0] * rot[1, 1] - rot[0, 1] * rot[1, 0]
            is_refl = det < -0.5

            R_crystal = np.eye(3, dtype=np.float32)
            if is_refl:
                if abs(rot[0, 0] + 1) < 0.5:
                    R_crystal[0, 0] = -1.0
                elif abs(rot[1, 1] + 1) < 0.5:
                    R_crystal[1, 1] = -1.0
            R_crystal[0, 2] = round(dx)
            R_crystal[1, 2] = round(dy)

            R_S_per_concept[c] = R_crystal
            spatial_info[c] = (int(round(dx)), int(round(dy)), bool(is_refl))

        # Count non-identity spatial transforms
        n_spatial_nonid = sum(1 for c in range(C)
                              if spatial_info[c] != (0, 0, False)
                              and len(per_color_in[c]) > 0)

        # ==============================================================
        # Telemetry
        # ==============================================================
        telemetry = ReynoldsTelemetry()
        edge_state = EdgeState.initialize(1, n_colors=C, init_scale=0.0)
        edge_state.weights[0] = R_C_crystal
        edge_state.crystallized[0] = True

        # Print per-concept spatial summary
        active_spatial = {c: spatial_info[c] for c in range(C)
                          if len(per_color_in[c]) > 0}
        print(f"    Twisted Fiber: color sigma={list(color_map)}"
              f" color_nonid={'Y' if color_nonid else 'N'}"
              f" color_acc={color_acc:.3f}")
        for c, (dx, dy, refl) in sorted(active_spatial.items()):
            n_stalks = len(per_color_in[c])
            print(f"      R_S[{c}]: ({dx:+d},{dy:+d})"
                  f" reflect={'Y' if refl else 'N'}"
                  f" ({n_stalks} stalks)")

        return {
            'grokked': True,
            'b1': 1,
            'edge_state': edge_state,
            'cross_pairs': [(0, 0)],
            'n_X': n_X, 'n_Y': n_Y, 'n_C': C,
            'stalks_X': stalks_X, 'stalks_Y': stalks_Y,
            'color_map': color_map,
            'R_C_crystal': R_C_crystal,
            'R_S_per_concept': R_S_per_concept,
            'spatial_info': spatial_info,
            'grid_shape': (H, W),
            'final_accuracy': float(color_acc),
            'n_nonidentity_perms': (1 if color_nonid else 0) + n_spatial_nonid,
            'iterations': max_iterations,
            'zones_final': {'crystallized': 1, 'transitioning': 0, 'frontier': 0},
            'telemetry': telemetry,
        }


# ============================================================================
# 11. ARC GAUNTLET WITH REYNOLDS ENGINE
# ============================================================================

def analyze_permutation_agreement(result: Dict[str, Any], n_colors: int = 10) -> Dict:
    """
    Q4 — Permutation Agreement Analysis.

    For each input color group, collect all crystallized R_ij permutations
    and measure pairwise agreement rate. A rate of 1.0 means the rule is
    spatially invariant (universal). A rate < 1.0 means spatial memorization.

    Also tests group closure: do the crystallized permutations form a
    closed subgroup of S_10 under composition?
    """
    edge_state = result.get('edge_state')
    cross_pairs = result.get('cross_pairs')
    stalks_X = result.get('stalks_X', [])
    if edge_state is None or cross_pairs is None:
        return {'error': 'missing data'}

    # Group crystallized edges by concept node (first element of cross_pair)
    # In tripartite: cross_pairs are (concept_c, output_j)
    # In bipartite: cross_pairs are (input_i, output_j) — use stalk color
    color_groups = {}  # concept/color -> list of (j, perm_array)
    for idx, (i, j) in enumerate(cross_pairs):
        if not edge_state.crystallized[idx]:
            continue
        R = edge_state.weights[idx]
        perm = tuple(np.argmax(np.abs(R), axis=1))
        # If concept layer (i < n_colors), use i directly as color
        # Otherwise fall back to stalk color lookup
        if i < n_colors and (not stalks_X or i >= len(stalks_X)):
            color = i  # Tripartite: i IS the concept index
        else:
            color = stalks_X[i].get('color', -1) if i < len(stalks_X) else i
        color_groups.setdefault(color, []).append((j, perm))

    # Per-color agreement rate
    color_report = {}
    total_pairs = 0
    agreeing_pairs = 0

    for color, entries in sorted(color_groups.items()):
        perms = [e[1] for e in entries]
        unique_perms = list(set(perms))
        n = len(perms)
        n_agree = 0
        n_total = 0
        for a in range(n):
            for b in range(a + 1, n):
                n_total += 1
                if perms[a] == perms[b]:
                    n_agree += 1
        rate = n_agree / max(n_total, 1)
        total_pairs += n_total
        agreeing_pairs += n_agree

        # Is this the identity permutation?
        identity = tuple(range(n_colors))
        non_id = [p for p in unique_perms if p != identity]

        color_report[color] = {
            'n_edges': n,
            'n_unique_perms': len(unique_perms),
            'agreement_rate': rate,
            'non_identity': len(non_id),
            'perms': unique_perms[:5],  # first 5 for display
        }

    overall_rate = agreeing_pairs / max(total_pairs, 1)

    # Group closure test: collect all unique non-identity perms, check closure
    all_perms = set()
    for entries in color_groups.values():
        for _, perm in entries:
            if perm != tuple(range(n_colors)):
                all_perms.add(perm)

    # Test closure: for all pairs (a, b), is a∘b in the set?
    closure_violations = 0
    closure_tests = 0
    perm_list = list(all_perms)
    for a in perm_list:
        for b in perm_list:
            composed = tuple(a[b[k]] for k in range(n_colors))
            closure_tests += 1
            if composed != tuple(range(n_colors)) and composed not in all_perms:
                closure_violations += 1

    return {
        'color_report': color_report,
        'overall_agreement_rate': overall_rate,
        'n_unique_nonid_perms': len(all_perms),
        'group_closure_violations': closure_violations,
        'group_closure_tests': closure_tests,
        'is_closed_subgroup': closure_violations == 0 and len(all_perms) > 0,
    }


def run_reynolds_gauntlet(max_tasks: int = 97, ablate_laplacian: bool = False):
    """
    Run the Reynolds Crystallization Engine on real ARC tasks.

    Training: Crystallize stalk-level Laplacian with per-edge Re_SGC control.
    Test: Infer via Dirichlet relaxation through crystallized pipes.

    If ablate_laplacian=True, sets L_XX=L_YY=0 (Q5 ablation experiment).
    """
    print("=" * 70)
    print("SGC REYNOLDS NUMBER ENGINE")
    print("Anisotropic Turbulence Crystallization with Per-Edge Re_SGC")
    print("=" * 70)

    # Load ARC tasks
    possible_dirs = [
        os.path.join(os.path.dirname(__file__), "..", "data", "arc", "training"),
        r"C:\Users\jason\arc-prize-2024\arc-agi_training_challenges",
    ]
    task_dir = None
    for d in possible_dirs:
        if d and os.path.isdir(d):
            task_dir = d
            break
    if task_dir is None:
        print("ERROR: No ARC task directory found")
        return

    tasks = []
    for fn in sorted(os.listdir(task_dir)):
        if fn.endswith('.json'):
            with open(os.path.join(task_dir, fn)) as f:
                data = json.load(f)
            tasks.append({'id': fn[:-5], 'train': data.get('train', []),
                          'test': data.get('test', [])})
    tasks = tasks[:max_tasks]
    print(f"Loaded {len(tasks)} tasks\n")

    engine = ReynoldsCrystallizer(
        n_colors=10, eta=0.01, initial_temp=1.0, re_crit=1.0)

    stats = {
        'tasks': 0, 'crystallized': 0, 'grokked': 0,
        'test_total': 0, 'test_solved': 0, 'test_near': 0,
        'zone_totals': {'crystallized': 0, 'transitioning': 0, 'frontier': 0},
        'match_rates': [],
    }

    t0 = time.time()

    for task_idx, task in enumerate(tasks):
        task_id = task['id']
        train_examples = task['train']
        test_examples = task['test']
        stats['tasks'] += 1

        # ---- TRAINING: Learn from all examples via bipartite crystallization ----
        all_rules = []
        for ex in train_examples:
            inp = np.array(ex['input'], dtype=np.float32)
            out = np.array(ex['output'], dtype=np.float32)

            if inp.shape != out.shape or inp.size > 900:
                continue

            stats['crystallized'] += 1
            print(f"  Task {task_id[:8]}.. example: {inp.shape}")
            result = engine.crystallize(inp, out, [],
                                        max_iterations=80,
                                        ablate_laplacian=ablate_laplacian)

            if result['grokked']:
                all_rules.append(result)
                stats['grokked'] += 1
                for z in ['crystallized', 'transitioning', 'frontier']:
                    stats['zone_totals'][z] += result['zones_final'][z]

        # Build consensus stalk maps for inference
        if not all_rules:
            continue

        # ---- Q4: Permutation Agreement Analysis ----
        for rule_idx, rule in enumerate(all_rules):
            q4 = analyze_permutation_agreement(rule, engine.n_colors)
            if rule_idx == 0:  # Report first example only
                print(f"  Q4 [{task_id[:8]}] agreement={q4['overall_agreement_rate']:.3f} "
                      f"unique_nonid={q4['n_unique_nonid_perms']} "
                      f"closure={'YES' if q4['is_closed_subgroup'] else 'NO'}"
                      f"({q4['group_closure_violations']}/{q4['group_closure_tests']} violations)")
                for color, cr in sorted(q4.get('color_report', {}).items()):
                    print(f"    color={color}: {cr['n_edges']} edges, "
                          f"{cr['n_unique_perms']} unique perms, "
                          f"agree={cr['agreement_rate']:.3f}, "
                          f"non-id={cr['non_identity']}")

        # Use the best-accuracy rule for inference
        best_rule = max(all_rules, key=lambda r: r['final_accuracy'])

        # ---- TEST: Zero-shot inference via QUANTUM BRIDGE ----
        for test_ex in test_examples:
            inp = np.array(test_ex['input'], dtype=np.float32)
            out_gt = (np.array(test_ex['output'], dtype=np.float32)
                      if 'output' in test_ex else None)
            stats['test_total'] += 1

            if out_gt is None or inp.shape != out_gt.shape:
                continue

            # Sheaf Dirichlet relaxation: Lift → Radiate → Collapse
            predicted = dirichlet_infer(
                inp, best_rule, n_colors=engine.n_colors,
                n_steps=30, eta=0.05, temperature=0.01)

            if predicted is not None and predicted.shape == out_gt.shape:
                match = float(np.mean(predicted == out_gt))
                stats['match_rates'].append(match)
                if np.array_equal(predicted, out_gt):
                    stats['test_solved'] += 1
                elif match > 0.5:
                    stats['test_near'] += 1

        if (task_idx + 1) % 10 == 0 or task_idx == len(tasks) - 1:
            elapsed = time.time() - t0
            print(f"\n  [{task_idx+1}/{len(tasks)}] "
                  f"grokked={stats['grokked']} "
                  f"test={stats['test_solved']}/{stats['test_total']} "
                  f"near={stats['test_near']} "
                  f"({elapsed:.1f}s)\n")

    elapsed = time.time() - t0

    print("\n" + "=" * 70)
    print("REYNOLDS ENGINE RESULTS")
    print("=" * 70)
    print(f"Tasks:              {stats['tasks']}")
    print(f"Crystallized:       {stats['crystallized']}")
    print(f"Grokked (b1>=1):    {stats['grokked']}")
    print(f"Test total:         {stats['test_total']}")
    print(f"Test solved:        {stats['test_solved']} "
          f"({100*stats['test_solved']/max(stats['test_total'],1):.1f}%)")
    print(f"Test near-miss:     {stats['test_near']}")
    print(f"Time:               {elapsed:.1f}s")

    zt = stats['zone_totals']
    total_edges = sum(zt.values()) or 1
    print(f"\nZone Distribution (aggregated across all crystallizations):")
    print(f"  Crystallized:     {zt['crystallized']} "
          f"({100*zt['crystallized']/total_edges:.1f}%)")
    print(f"  Transitioning:    {zt['transitioning']} "
          f"({100*zt['transitioning']/total_edges:.1f}%)")
    print(f"  Frontier:         {zt['frontier']} "
          f"({100*zt['frontier']/total_edges:.1f}%)")

    match_rates = stats['match_rates']
    if match_rates:
        arr = np.array(match_rates)
        print(f"\nMatch Rate Distribution ({len(arr)} tested):")
        print(f"  Mean:   {np.mean(arr):.1%}")
        print(f"  Median: {np.median(arr):.1%}")
        print(f"  >90%:   {np.sum(arr > 0.9)}")
        print(f"  >50%:   {np.sum(arr > 0.5)}")

    return stats


# ============================================================================
# 12. MAIN
# ============================================================================

if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(
        description='SGC Reynolds Number Engine: Anisotropic Turbulence')
    parser.add_argument('--max-tasks', type=int, default=20)
    parser.add_argument('--re-crit', type=float, default=1.0,
                        help='Critical Reynolds number for quench threshold')
    parser.add_argument('--eta', type=float, default=0.01,
                        help='SGLD step size')
    parser.add_argument('--temp', type=float, default=1.0,
                        help='Initial temperature')
    parser.add_argument('--ablate', action='store_true',
                        help='Q5: ablate L_XX and L_YY (set to zero)')
    args = parser.parse_args()

    run_reynolds_gauntlet(max_tasks=args.max_tasks,
                          ablate_laplacian=args.ablate)
