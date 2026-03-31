"""
Topological Observables: Betti Numbers, Forman-Ricci, and Fermi Quench
=======================================================================

Ported from demos/jax_sgld_engine.py and demos/sgc_reynolds_engine.py
for integration into the perihelion zero-parameter EGI stack.

THEORETICAL FOUNDATION:
    - b1 >= 1: Markov blanket exists -> generalization possible
    - Forman-Ricci F > 0: Cycle edge (protected from decay)
    - Forman-Ricci F < 0: Bridge edge (pruned by curvature flow)
    - Fermi quench: Smooth crystallization at phase boundary

Author: SGC Research Team
Date: March 31, 2026
"""

import numpy as np
import torch
from typing import List, Tuple, Dict, Optional
from dataclasses import dataclass


# =============================================================================
# BETTI NUMBER COMPUTATION (from jax_sgld_engine.py)
# =============================================================================

def compute_b1(edge_weights: np.ndarray, edge_pairs: List[Tuple[int, int]],
               n_stalks: int, threshold: float = 0.01) -> int:
    """
    First Betti number from edge weights.
    
    b1 = |E| - |V| + b0 (Euler characteristic)
    b1 >= 1 iff cycle exists (Markov blanket -> generalization).
    
    This is the GENERALIZATION BOUNDARY from the theory:
    - b1 = 0: Tree structure, memorization regime
    - b1 >= 1: Cycle exists, Markov blanket, generalization possible
    """
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
    
    # Handle both scalar and matrix edge weights
    if edge_weights.ndim == 1:
        norms = np.abs(edge_weights)
    else:
        norms = np.linalg.norm(edge_weights.reshape(len(edge_weights), -1), axis=1)
    
    n_active = 0
    for idx, (i, j) in enumerate(edge_pairs):
        if idx < len(norms) and norms[idx] > threshold:
            n_active += 1
            union(i, j)
    
    b0 = len(set(find(i) for i in range(n_stalks)))
    return max(n_active - n_stalks + b0, 0)


def compute_b1_torch(weight_matrix: torch.Tensor, threshold: float = 0.01) -> int:
    """
    DEPRECATED: Use compute_b1_from_activations instead.
    
    This function computes b1 from the weight matrix bipartite graph,
    which measures structural redundancy, NOT the Markov blanket condition.
    
    The correct graph for the generalization boundary is the activation
    correlation graph (the quotient generator L from SGC theory).
    """
    W = weight_matrix.detach().cpu().numpy()
    n_out, n_in = W.shape
    n_stalks = n_out + n_in
    
    # Build edge pairs and weights
    edge_pairs = [(i, n_in + j) for i in range(n_in) for j in range(n_out)]
    edge_weights = np.abs(W.T.flatten())  # (n_in * n_out,)
    
    return compute_b1(edge_weights, edge_pairs, n_stalks, threshold)


def compute_spectral_gap_from_correlation(corr_matrix: np.ndarray) -> float:
    """
    Compute spectral gap from correlation matrix eigenvalues.
    
    gap = (λ_1 - λ_2) / λ_1
    
    This is used to derive the threshold for b1 computation.
    """
    try:
        eigenvalues = np.linalg.eigvalsh(corr_matrix)
        eigenvalues = np.sort(np.abs(eigenvalues))[::-1]  # Descending
        
        if len(eigenvalues) < 2 or eigenvalues[0] < 1e-10:
            return 0.1  # Default fallback
        
        return (eigenvalues[0] - eigenvalues[1]) / eigenvalues[0]
    except Exception:
        return 0.1


def compute_b1_from_activations(
    activation_corr: torch.Tensor,
    threshold: Optional[float] = None
) -> int:
    """
    Compute b1 from the ACTIVATION CORRELATION MATRIX.
    
    THIS IS THE CORRECT FUNCTION for computing the generalization boundary.
    
    The Markov blanket condition (b1 >= 1) refers to cycles in the STATE
    TRANSITION GRAPH of the dynamical system — the graph whose vertices
    are neurons and whose edges are their co-activation correlations.
    
    This is the quotient generator L from the SGC Lean formalization,
    NOT the weight matrix W.
    
    Args:
        activation_corr: Correlation matrix of activations (n_neurons x n_neurons).
                        This is the empirical transition operator that the
                        SGC engine estimates.
        threshold: Edge threshold. If None, derived from spectral gap.
                  threshold = gap / n_neurons (spectral resolution)
    
    Returns:
        b1: First Betti number. b1 >= 1 implies Markov blanket exists.
    
    ZERO-PARAMETER: When threshold is None, it is derived from the
    spectral gap of the correlation matrix itself.
    """
    if isinstance(activation_corr, torch.Tensor):
        C = activation_corr.detach().cpu().numpy()
    else:
        C = np.asarray(activation_corr)
    
    n_neurons = C.shape[0]
    
    # ZERO-PARAMETER: Derive threshold from spectral gap
    if threshold is None:
        gap = compute_spectral_gap_from_correlation(C)
        threshold = gap / max(n_neurons, 1)
    
    # Build edge pairs: all (i, j) with i < j
    edge_pairs = [(i, j) for i in range(n_neurons) for j in range(i + 1, n_neurons)]
    
    # Edge weights: absolute correlation values (upper triangle)
    edge_weights = np.array([np.abs(C[i, j]) for i, j in edge_pairs])
    
    return compute_b1(edge_weights, edge_pairs, n_neurons, threshold)


def compute_activation_correlation(
    model: torch.nn.Module,
    dataloader: torch.utils.data.DataLoader,
    layer_name: str = 'hidden',
    device: str = 'cuda',
    n_samples: int = 500
) -> torch.Tensor:
    """
    Compute activation correlation matrix from a batch of inputs.
    
    This extracts the QUOTIENT GENERATOR from the network —
    the empirical transition operator that SGC theory analyzes.
    
    Args:
        model: Neural network with named layers
        dataloader: Data source
        layer_name: Name pattern of layer to extract activations from
        device: Computation device
        n_samples: Number of samples to collect
    
    Returns:
        Correlation matrix (n_neurons x n_neurons)
    """
    model.eval()
    activations = []
    
    # Hook to capture activations
    activation_store = {}
    
    def hook_fn(name):
        def hook(module, input, output):
            activation_store[name] = output.detach()
        return hook
    
    # Register hook on target layer
    hook_handle = None
    for name, module in model.named_modules():
        if layer_name in name:
            hook_handle = module.register_forward_hook(hook_fn(name))
            break
    
    if hook_handle is None:
        # Fallback: try to find any linear layer
        for name, module in model.named_modules():
            if isinstance(module, torch.nn.Linear):
                hook_handle = module.register_forward_hook(hook_fn(name))
                break
    
    # Collect activations
    n_collected = 0
    with torch.no_grad():
        for x, _ in dataloader:
            if n_collected >= n_samples:
                break
            x = x.to(device)
            _ = model(x)
            
            if activation_store:
                act = list(activation_store.values())[0]
                if act.dim() > 2:
                    act = act.view(act.size(0), -1)  # Flatten spatial dims
                activations.append(act.cpu())
                n_collected += len(x)
    
    if hook_handle:
        hook_handle.remove()
    
    model.train()
    
    if not activations:
        # Return identity if no activations collected
        return torch.eye(1)
    
    # Stack all activations: (n_samples, n_neurons)
    A = torch.cat(activations, dim=0)[:n_samples]
    
    # Compute correlation matrix
    # Centered activations
    A_centered = A - A.mean(dim=0, keepdim=True)
    
    # Correlation: C = A^T A / (n-1), normalized
    n = A_centered.size(0)
    cov = (A_centered.T @ A_centered) / max(n - 1, 1)
    
    # Normalize to correlation
    std = torch.sqrt(torch.diag(cov) + 1e-8)
    corr = cov / (std.unsqueeze(0) * std.unsqueeze(1))
    
    return corr


# =============================================================================
# FORMAN-RICCI CURVATURE (from sgc_reynolds_engine.py)
# =============================================================================

def compute_forman_ricci(edge_weights: np.ndarray, edge_pairs: List[Tuple[int, int]],
                         n_stalks: int, threshold: float = 0.01) -> np.ndarray:
    """
    Forman-Ricci curvature per edge: F(i,j) = #triangles(i,j) - 1.
    
    F > 0: Cycle edge (topologically protected, immune to decay)
    F < 0: Bridge/isolated (pruned by curvature flow)
    F = 0: Neutral
    
    This implements TOPOLOGICAL PROTECTION for grokked representations:
    edges participating in cycles are protected from being forgotten.
    """
    # Handle both scalar and matrix edge weights
    if edge_weights.ndim == 1:
        norms = np.abs(edge_weights)
    else:
        norms = np.linalg.norm(edge_weights.reshape(len(edge_weights), -1), axis=1)
    
    n_edges = len(edge_pairs)
    
    # Build adjacency
    adj = np.zeros((n_stalks, n_stalks), dtype=bool)
    for idx, (i, j) in enumerate(edge_pairs):
        if idx < len(norms) and norms[idx] > threshold:
            adj[i, j] = True
            adj[j, i] = True
    
    # Compute curvature
    curvature = np.full(n_edges, -1.0, dtype=np.float32)
    for idx, (i, j) in enumerate(edge_pairs):
        if idx >= len(norms) or norms[idx] < threshold:
            curvature[idx] = 0.0
            continue
        
        # Count triangles containing edge (i, j)
        n_tri = 0
        for k in range(n_stalks):
            if k != i and k != j and adj[i, k] and adj[j, k]:
                n_tri += 1
        curvature[idx] = float(n_tri) - 1.0
    
    return curvature


def ricci_flow_step(edge_weights: np.ndarray, edge_pairs: List[Tuple[int, int]],
                    n_stalks: int, decay_lambda: float = 0.1,
                    threshold: float = 0.01) -> np.ndarray:
    """
    One step of Forman-Ricci curvature flow on edge weights.
    
    Bridges (F < 0) decay. Cycle edges (F >= 0) are protected.
    This implements SELECTIVE FORGETTING: only non-essential edges decay.
    """
    curvature = compute_forman_ricci(edge_weights, edge_pairs, n_stalks, threshold)
    max_curv = np.abs(curvature).max() + 1e-8
    
    # Decay rate: positive only for negative curvature (bridges)
    decay_rate = decay_lambda * np.maximum(0, -curvature / max_curv)
    
    return edge_weights * (1.0 - decay_rate)


# =============================================================================
# FERMI QUENCH (from sgc_reynolds_engine.py)
# =============================================================================

def fermi(x: float, x0: float = 0.0, delta: float = 0.1) -> float:
    """
    Smooth Fermi function (soft Heaviside).
    
    Used for smooth phase transitions in the thermal controller.
    fermi(x) -> 0 as x -> -inf
    fermi(x) -> 1 as x -> +inf
    fermi(x0) = 0.5
    """
    return 1.0 / (1.0 + np.exp(-(x - x0) / max(delta, 0.001)))


def fermi_quench_factor(re_sgc: float, re_crit: float = 1.0, 
                        delta: float = 0.2) -> float:
    """
    Fermi quench factor: continuous crystallization control.
    
    sigma_quench = fermi(Re_crit - Re_SGC)
    
    When sigma -> 1: Edge crystallizes (kappa -> 0, weight snaps discrete)
    When sigma -> 0: Edge remains fluid (full thermal dynamics)
    
    This implements CONTINUOUS PHASE TRANSITION, not a hard if/then.
    """
    return fermi(re_crit - re_sgc, x0=0.0, delta=delta)


# =============================================================================
# SPECIFIC HEAT (from jax_sgld_engine.py / thermodynamic_grokking_v2.py)
# =============================================================================

def compute_specific_heat(energy_window: List[float], temperature: float) -> float:
    """
    Specific heat Cv = beta^2 * Var(E) from energy time series.
    
    Peak in Cv indicates PHASE TRANSITION.
    This is the thermodynamic signature of grokking.
    """
    if len(energy_window) < 2 or temperature < 1e-6:
        return 0.0
    
    beta = 1.0 / temperature
    return beta ** 2 * np.var(energy_window)


def compute_binder_cumulant(values: np.ndarray) -> float:
    """
    Binder cumulant U4 = 1 - <m^4> / (3 * <m^2>^2)
    
    U4 -> 0: Gaussian (disordered phase)
    U4 -> 2/3: Sharp distribution (ordered phase)
    
    Crossing point of U4 curves for different system sizes
    gives the critical point.
    """
    m2 = np.mean(values ** 2)
    m4 = np.mean(values ** 4)
    
    if m2 < 1e-12:
        return 0.0
    
    return 1.0 - m4 / (3.0 * m2 ** 2)


# =============================================================================
# TOPOLOGICAL METRICS AGGREGATOR
# =============================================================================

@dataclass
class TopologicalMetrics:
    """Container for topological observables."""
    b1: int                      # First Betti number (cycles)
    forman_ricci_mean: float     # Mean Forman-Ricci curvature
    forman_ricci_min: float      # Min curvature (most bridge-like)
    forman_ricci_max: float      # Max curvature (most cycle-like)
    n_protected_edges: int       # Edges with F >= 0 (cycle edges)
    n_bridge_edges: int          # Edges with F < 0 (bridges)
    specific_heat: float         # Cv from energy history
    binder_cumulant: float       # U4 order parameter
    
    @property
    def has_markov_blanket(self) -> bool:
        """b1 >= 1 implies Markov blanket exists."""
        return self.b1 >= 1
    
    @property
    def protection_ratio(self) -> float:
        """Fraction of edges that are topologically protected."""
        total = self.n_protected_edges + self.n_bridge_edges
        if total == 0:
            return 0.0
        return self.n_protected_edges / total


def compute_topological_metrics(
    weight_matrix: torch.Tensor,
    energy_history: Optional[List[float]] = None,
    temperature: float = 1.0,
    threshold: float = 0.01
) -> TopologicalMetrics:
    """
    Compute full topological metrics from a weight matrix.
    
    This is the main entry point for topological analysis.
    """
    W = weight_matrix.detach().cpu().numpy()
    n_out, n_in = W.shape
    n_stalks = n_out + n_in
    
    # Build edge structure
    edge_pairs = [(i, n_in + j) for i in range(n_in) for j in range(n_out)]
    edge_weights = np.abs(W.T.flatten())
    
    # Compute b1
    b1 = compute_b1(edge_weights, edge_pairs, n_stalks, threshold)
    
    # Compute Forman-Ricci curvature
    curvature = compute_forman_ricci(edge_weights, edge_pairs, n_stalks, threshold)
    active_curvature = curvature[np.abs(edge_weights) > threshold]
    
    if len(active_curvature) > 0:
        fr_mean = float(np.mean(active_curvature))
        fr_min = float(np.min(active_curvature))
        fr_max = float(np.max(active_curvature))
        n_protected = int(np.sum(active_curvature >= 0))
        n_bridge = int(np.sum(active_curvature < 0))
    else:
        fr_mean, fr_min, fr_max = 0.0, 0.0, 0.0
        n_protected, n_bridge = 0, 0
    
    # Compute thermodynamic observables
    if energy_history and len(energy_history) >= 2:
        cv = compute_specific_heat(energy_history, temperature)
        u4 = compute_binder_cumulant(np.array(energy_history))
    else:
        cv, u4 = 0.0, 0.0
    
    return TopologicalMetrics(
        b1=b1,
        forman_ricci_mean=fr_mean,
        forman_ricci_min=fr_min,
        forman_ricci_max=fr_max,
        n_protected_edges=n_protected,
        n_bridge_edges=n_bridge,
        specific_heat=cv,
        binder_cumulant=u4
    )
