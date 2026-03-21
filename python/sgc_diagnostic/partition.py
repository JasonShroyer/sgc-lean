# partition.py
"""
Defect-minimizing partition search.
This is where SGC differs from k-means: the objective is the defect norm ‖D_P‖_π,
not Euclidean distance.
"""
import numpy as np
from typing import Tuple, Dict, Optional


def compute_pi_bar(pi: np.ndarray, assignment: np.ndarray) -> np.ndarray:
    """
    π̄(block) = Σ_{v in block} π(v). The block masses.
    """
    n_blocks = int(assignment.max()) + 1
    pi_bar = np.zeros(n_blocks)
    for v, b in enumerate(assignment):
        pi_bar[int(b)] += pi[v]
    return pi_bar


def compute_projector(pi: np.ndarray, assignment: np.ndarray) -> np.ndarray:
    """
    Π_{xy} = π(y)/π̄(block(x)) if block(x)=block(y), else 0.
    This is StochasticMatrixFromPartition = CoarseProjectorMatrix (proved by rfl).
    [theorem: projector_squared in Lumpability.lean]
    """
    n = len(pi)
    pi_bar = compute_pi_bar(pi, assignment)
    Pi = np.zeros((n, n))
    for x in range(n):
        for y in range(n):
            if assignment[x] == assignment[y]:
                block = int(assignment[x])
                if pi_bar[block] > 1e-15:
                    Pi[x, y] = pi[y] / pi_bar[block]
    return Pi


def compute_defect_operator(L: np.ndarray, Pi: np.ndarray) -> np.ndarray:
    """
    D_P = (I - Π) L Π.
    Measures information leakage from coarse subspace.
    [theorem: generator_decomposition in Approximate.lean]
    """
    I = np.eye(len(L))
    return (I - Pi) @ L @ Pi


def defect_norm_pi(D: np.ndarray, pi: np.ndarray) -> float:
    """
    ‖D‖_π = sup_{‖f‖_π=1} ‖Df‖_π.
    Computed as the largest singular value of the π-weighted operator.
    [theorem: opNorm_pi_bound in Geometry.lean]
    """
    n = len(pi)
    sqrt_pi = np.sqrt(np.clip(pi, 1e-15, None))
    inv_sqrt_pi = 1.0 / sqrt_pi
    # Conjugate: ‖D‖_π = ‖diag(√π) D diag(1/√π)‖_2
    D_weighted = np.diag(sqrt_pi) @ D @ np.diag(inv_sqrt_pi)
    return float(np.linalg.norm(D_weighted, ord=2))


def _compute_epsilon(L: np.ndarray, pi: np.ndarray, assignment: np.ndarray) -> float:
    """Compute defect norm for a given assignment."""
    Pi = compute_projector(pi, assignment)
    D = compute_defect_operator(L, Pi)
    return defect_norm_pi(D, pi)


def _ensure_all_blocks_filled(assignment: np.ndarray, k: int) -> np.ndarray:
    """Ensure all block indices 0..k-1 have at least one member."""
    assignment = assignment.copy()
    present = set(assignment)
    missing = set(range(k)) - present
    if missing:
        # Randomly reassign some states to fill missing blocks
        for b in missing:
            # Find a block with more than one member
            for existing_b in present:
                members = np.where(assignment == existing_b)[0]
                if len(members) > 1:
                    assignment[members[0]] = b
                    break
    return assignment


def _defect_lloyd(
    L: np.ndarray,
    pi: np.ndarray,
    assignment: np.ndarray,
    k: int,
    max_iter: int = 50
) -> Tuple[np.ndarray, float]:
    """
    Lloyd-style iterations minimizing ‖D_P‖_π instead of Euclidean distance.
    Each iteration: reassign each state to the block that minimizes defect,
    keeping all other assignments fixed.
    """
    n = len(L)
    assignment = _ensure_all_blocks_filled(assignment, k)
    prev_epsilon = _compute_epsilon(L, pi, assignment)
    
    for iteration in range(max_iter):
        improved = False
        
        # Try reassigning each state
        for v in range(n):
            current_block = int(assignment[v])
            best_block = current_block
            best_epsilon = prev_epsilon
            
            # Count members in current block
            current_block_size = np.sum(assignment == current_block)
            
            for b in range(k):
                if b == current_block:
                    continue
                # Don't empty a block
                if current_block_size <= 1:
                    continue
                    
                # Tentative reassignment
                trial = assignment.copy()
                trial[v] = b
                trial_epsilon = _compute_epsilon(L, pi, trial)
                
                if trial_epsilon < best_epsilon - 1e-12:
                    best_epsilon = trial_epsilon
                    best_block = b
            
            if best_block != current_block:
                assignment[v] = best_block
                prev_epsilon = best_epsilon
                improved = True
        
        if not improved:
            break
    
    final_epsilon = _compute_epsilon(L, pi, assignment)
    return assignment, final_epsilon


def find_optimal_partition(
    L: np.ndarray,
    pi: np.ndarray,
    k_min: int = 2,
    k_max: int = None,
    n_restarts: int = 20,
    method: str = "spectral_init"
) -> Tuple[np.ndarray, float, Dict[int, float]]:
    """
    Find P* = argmin_{k-partition P} defect_norm(D_P, π).
    
    Returns:
        P_star: optimal partition assignment (n,)
        epsilon_star: defect norm at P*
        defect_curve: {k: best_epsilon(k)} for k in k_min..k_max
    
    [theorem: optimal_partition_exists — existence guaranteed by finiteness]
    
    Algorithm:
    1. Spectral initialization: use eigenvectors of L for initial cluster centers
    2. Defect-minimizing Lloyd iterations (not k-means — objective is ‖D_P‖_π)
    3. Multiple restarts, keep global minimum
    """
    n = len(L)
    if k_max is None:
        k_max = min(n // 2 + 1, 12)
    k_max = min(k_max, n)
    
    # Spectral features for initialization: eigenvectors of L
    eigenvalues, eigenvectors = np.linalg.eig(L)
    # Sort by eigenvalue magnitude (slowest modes first, excluding stationary)
    idx = np.argsort(np.abs(np.real(eigenvalues)))
    slow_modes = np.real(eigenvectors[:, idx[:min(k_max, n)]])
    
    defect_curve = {}
    best_assignment = np.zeros(n, dtype=int)
    best_epsilon = float('inf')
    
    for k in range(k_min, k_max + 1):
        best_k_epsilon = float('inf')
        best_k_assignment = None
        
        for restart in range(n_restarts):
            # Initialize assignment
            if restart == 0 and k <= slow_modes.shape[1]:
                # Spectral initialization: assign by dominant eigenvector component
                # This is the correct prior for Markov chain generators (no sklearn needed)
                features = slow_modes[:, :k]
                # Normalize each row so assignment is by relative eigenvector weight
                row_norms = np.abs(features).sum(axis=1, keepdims=True) + 1e-12
                features_norm = features / row_norms
                assignment = np.argmax(features_norm, axis=1) % k
            else:
                assignment = np.random.randint(0, k, size=n)
            
            # Ensure all blocks are non-empty
            assignment = _ensure_all_blocks_filled(assignment, k)
            
            # Defect-minimizing Lloyd iterations
            assignment, epsilon = _defect_lloyd(L, pi, assignment, k, max_iter=50)
            
            if epsilon < best_k_epsilon:
                best_k_epsilon = epsilon
                best_k_assignment = assignment.copy()
        
        defect_curve[k] = best_k_epsilon
        if best_k_epsilon < best_epsilon:
            best_epsilon = best_k_epsilon
            best_assignment = best_k_assignment.copy()
    
    return best_assignment, best_epsilon, defect_curve


def compute_coarse_generator(L: np.ndarray, pi: np.ndarray, 
                             assignment: np.ndarray) -> np.ndarray:
    """
    Compute the coarse-grained generator L̄ on the block space.
    L̄_{AB} = (1/π̄(A)) Σ_{x∈A, y∈B} π(x) L_{xy}
    
    [theorem: quotient_is_generator in Lumpability.lean]
    """
    n_blocks = int(assignment.max()) + 1
    pi_bar = compute_pi_bar(pi, assignment)
    L_bar = np.zeros((n_blocks, n_blocks))
    
    for A in range(n_blocks):
        for B in range(n_blocks):
            total = 0.0
            for x in range(len(pi)):
                if assignment[x] == A:
                    for y in range(len(pi)):
                        if assignment[y] == B:
                            total += pi[x] * L[x, y]
            if pi_bar[A] > 1e-15:
                L_bar[A, B] = total / pi_bar[A]
    
    return L_bar
