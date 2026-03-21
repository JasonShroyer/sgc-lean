# markov.py
"""
Build empirical generators from various data sources:
- Transition count matrices
- Activation time series
- Connectivity matrices
"""
import numpy as np
from typing import Tuple, Optional, List


def generator_from_transition_matrix(P: np.ndarray, dt: float = 1.0) -> np.ndarray:
    """
    Convert a transition probability matrix P to a generator L.
    L = (P - I) / dt, so that e^{L·dt} ≈ P for small dt.
    
    Args:
        P: Transition probability matrix (rows sum to 1)
        dt: Time step
        
    Returns:
        L: Generator matrix (rows sum to 0)
    """
    n = len(P)
    I = np.eye(n)
    L = (P - I) / dt
    return L


def generator_from_counts(counts: np.ndarray, 
                          regularization: float = 1e-6) -> Tuple[np.ndarray, np.ndarray]:
    """
    Build generator from transition count matrix.
    
    Args:
        counts: Count matrix C[i,j] = number of i→j transitions observed
        regularization: Add to all counts to avoid zeros
        
    Returns:
        L: Generator matrix
        pi: Stationary distribution (empirical)
    """
    counts = counts + regularization
    n = counts.shape[0]
    
    # Row-normalize to get transition probabilities
    row_sums = counts.sum(axis=1, keepdims=True)
    P = counts / np.clip(row_sums, 1e-15, None)
    
    # Convert to generator
    L = generator_from_transition_matrix(P, dt=1.0)
    
    # Compute stationary distribution from left eigenvector
    pi = compute_stationary_distribution(L)
    
    return L, pi


def generator_from_activations(
    activations: np.ndarray,
    n_clusters: int = 10,
    method: str = "kmeans"
) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """
    Build empirical generator from activation time series.
    
    1. Cluster activation vectors into discrete states
    2. Count transitions between states
    3. Build generator from counts
    
    Args:
        activations: Time series of activations, shape (T, d)
        n_clusters: Number of discrete states
        method: Clustering method ("kmeans" or "discretize")
        
    Returns:
        L: Generator matrix (n_clusters × n_clusters)
        pi: Stationary distribution
        labels: Cluster assignment for each time step
    """
    T, d = activations.shape
    
    if method == "kmeans":
        from sklearn.cluster import KMeans
        km = KMeans(n_clusters=n_clusters, n_init=10, random_state=42)
        labels = km.fit_predict(activations)
    elif method == "discretize":
        # Simple grid-based discretization
        labels = _discretize_activations(activations, n_clusters)
    else:
        raise ValueError(f"Unknown method: {method}")
    
    # Count transitions
    counts = np.zeros((n_clusters, n_clusters))
    for t in range(T - 1):
        i, j = labels[t], labels[t + 1]
        counts[i, j] += 1
    
    # Build generator
    L, pi = generator_from_counts(counts)
    
    return L, pi, labels


def _discretize_activations(activations: np.ndarray, n_clusters: int) -> np.ndarray:
    """Simple discretization by binning the first principal component."""
    # Use first PC for discretization
    if activations.shape[1] > 1:
        from sklearn.decomposition import PCA
        pca = PCA(n_components=1)
        proj = pca.fit_transform(activations).flatten()
    else:
        proj = activations.flatten()
    
    # Bin into n_clusters equal-frequency bins
    percentiles = np.linspace(0, 100, n_clusters + 1)
    bins = np.percentile(proj, percentiles)
    labels = np.digitize(proj, bins[1:-1])
    return labels


def generator_from_connectivity(
    W: np.ndarray,
    symmetrize: bool = False,
    normalize: str = "laplacian"
) -> Tuple[np.ndarray, np.ndarray]:
    """
    Build generator from connectivity/adjacency matrix.
    
    Args:
        W: Weighted adjacency matrix (W[i,j] = connection strength i→j)
        symmetrize: If True, use (W + W.T)/2
        normalize: Normalization method
            - "laplacian": L = D^{-1}W - I (random walk Laplacian)
            - "symmetric": L = D^{-1/2}WD^{-1/2} - I
            - "degree": L = W/max(W) - I
            
    Returns:
        L: Generator matrix
        pi: Stationary distribution
    """
    W = np.asarray(W, dtype=float)
    n = W.shape[0]
    
    # Ensure non-negative
    W = np.abs(W)
    
    if symmetrize:
        W = (W + W.T) / 2.0
    
    # Remove self-loops for generator construction
    W_offdiag = W.copy()
    np.fill_diagonal(W_offdiag, 0)
    
    # Degree vector
    d = W_offdiag.sum(axis=1)
    d = np.clip(d, 1e-10, None)  # Avoid division by zero
    
    if normalize == "laplacian":
        # Random walk Laplacian: L_{ij} = W_{ij}/d_i - δ_{ij}
        D_inv = np.diag(1.0 / d)
        P = D_inv @ W_offdiag
        L = P - np.eye(n)
        # Stationary distribution proportional to degree for reversible case
        pi = d / d.sum()
        
    elif normalize == "symmetric":
        # Symmetric normalization
        D_sqrt_inv = np.diag(1.0 / np.sqrt(d))
        P = D_sqrt_inv @ W_offdiag @ D_sqrt_inv
        L = P - np.eye(n)
        # Uniform stationary for symmetric
        pi = np.ones(n) / n
        
    elif normalize == "degree":
        # Simple degree normalization
        W_norm = W_offdiag / (W_offdiag.max() + 1e-10)
        row_sums = W_norm.sum(axis=1, keepdims=True)
        P = W_norm / np.clip(row_sums, 1e-10, None)
        L = P - np.eye(n)
        pi = compute_stationary_distribution(L)
        
    else:
        raise ValueError(f"Unknown normalization: {normalize}")
    
    # Ensure rows sum to zero (generator property)
    row_sums = L.sum(axis=1)
    L = L - np.diag(row_sums)
    
    return L, pi


def compute_stationary_distribution(L: np.ndarray) -> np.ndarray:
    """
    Compute stationary distribution π such that π^T L = 0.
    """
    n = len(L)
    
    # Find left eigenvector with eigenvalue 0
    eigenvalues, eigenvectors = np.linalg.eig(L.T)
    
    # Find eigenvalue closest to 0
    idx = np.argmin(np.abs(eigenvalues))
    pi = np.real(eigenvectors[:, idx])
    
    # Ensure non-negative and normalized
    pi = np.abs(pi)
    if pi.sum() > 1e-15:
        pi = pi / pi.sum()
    else:
        pi = np.ones(n) / n
    
    return pi


def validate_generator(L: np.ndarray, pi: np.ndarray, 
                       tol: float = 1e-6) -> dict:
    """
    Validate that L is a proper generator with stationary distribution π.
    
    Returns dict with validation results.
    """
    n = len(L)
    results = {}
    
    # Check rows sum to zero
    row_sums = L.sum(axis=1)
    results["rows_sum_to_zero"] = np.allclose(row_sums, 0, atol=tol)
    results["max_row_sum_deviation"] = float(np.max(np.abs(row_sums)))
    
    # Check off-diagonal non-negative (for valid generator)
    off_diag = L.copy()
    np.fill_diagonal(off_diag, 0)
    results["off_diagonal_nonneg"] = np.all(off_diag >= -tol)
    results["min_off_diagonal"] = float(np.min(off_diag))
    
    # Check π is stationary: π^T L = 0
    pi_L = pi @ L
    results["pi_is_stationary"] = np.allclose(pi_L, 0, atol=tol)
    results["max_stationarity_deviation"] = float(np.max(np.abs(pi_L)))
    
    # Check π sums to 1
    results["pi_sums_to_one"] = np.isclose(pi.sum(), 1.0, atol=tol)
    
    # Check π is positive
    results["pi_is_positive"] = np.all(pi > 0)
    
    # Overall validity
    results["is_valid"] = (
        results["rows_sum_to_zero"] and
        results["off_diagonal_nonneg"] and
        results["pi_is_stationary"] and
        results["pi_sums_to_one"] and
        results["pi_is_positive"]
    )
    
    return results


def check_detailed_balance(L: np.ndarray, pi: np.ndarray, 
                           tol: float = 1e-6) -> Tuple[bool, float]:
    """
    Check if L satisfies detailed balance: π(x) L(x,y) = π(y) L(y,x).
    
    Returns:
        is_reversible: True if detailed balance holds
        max_violation: Maximum violation of detailed balance
    """
    n = len(L)
    max_violation = 0.0
    
    for x in range(n):
        for y in range(n):
            lhs = pi[x] * L[x, y]
            rhs = pi[y] * L[y, x]
            violation = abs(lhs - rhs)
            max_violation = max(max_violation, violation)
    
    is_reversible = max_violation < tol
    return is_reversible, max_violation
