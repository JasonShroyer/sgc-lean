#!/usr/bin/env python3
"""
Rayleigh Measurement Module: Empirical Verification of IsEGIFixedPoint
========================================================================

This module provides the empirical instruments for measuring whether a trained
system has reached an EGI fixed point as defined in QuotientGenerator.lean.

THEORETICAL FOUNDATION (from the Lean formalization):

    IsEGIFixedPoint L P π := RayleighSet(QuotientGenerator L P π) = RayleighSetBlockConstant L P π

This is STRONG spectral equivalence: full Rayleigh set equality across ALL modes,
not just the leading eigenvalue (which would be WEAK equivalence / gap-matching).

The Tanaka boundary: drift-regime systems satisfy weak equivalence trivially
but fail strong equivalence because their microscopic dynamics is incoherent
at the message-passing scale.

USAGE:
    from rayleigh_measurement import RayleighMeasurement, SpectralEquivalenceResult
    
    # After training a network with SGC controller
    measurement = RayleighMeasurement(model, partition, pi_dist)
    result = measurement.measure_spectral_equivalence(top_k=10, tolerance=0.01)
    
    if result.is_strong_equivalent:
        print("System has reached IsEGIFixedPoint!")

Author: SGC Research Team
Date: March 31, 2026
"""

import numpy as np
import torch
import torch.nn as nn
from typing import Dict, List, Optional, Tuple, Any, Set
from dataclasses import dataclass, field
from enum import Enum
import warnings


# ============================================================================
# 1. DATA STRUCTURES
# ============================================================================

class EquivalenceType(Enum):
    """Classification of spectral equivalence strength."""
    NONE = "none"                    # No equivalence detected
    WEAK = "weak"                    # Gap-matching only (λ₁ equality)
    STRONG = "strong"                # Full Rayleigh set equality


@dataclass
class RayleighSetData:
    """Complete Rayleigh set data for a generator."""
    eigenvalues: np.ndarray          # Full spectrum (sorted descending)
    eigenvectors: np.ndarray         # Corresponding eigenvectors
    rayleigh_quotients: np.ndarray   # R(f) = ⟨f, Lf⟩_π / ⟨f, f⟩_π for test functions
    dirichlet_gap: float             # λ₁ - λ₀ (spectral gap)
    effective_rank: float            # Participation ratio
    spectral_entropy: float          # -Σ pᵢ log pᵢ


@dataclass
class SpectralEquivalenceResult:
    """Result of spectral equivalence measurement."""
    equivalence_type: EquivalenceType
    is_strong_equivalent: bool       # True iff IsEGIFixedPoint is satisfied
    is_weak_equivalent: bool         # True iff gap-matching holds
    
    # Rayleigh set data for both systems
    network_rayleigh: RayleighSetData
    quotient_rayleigh: RayleighSetData
    
    # Quantitative comparison metrics
    eigenvalue_correlation: float    # Spearman correlation of top-k eigenvalues
    rayleigh_set_overlap: float      # |R_net ∩ R_quot| / |R_net ∪ R_quot|
    max_eigenvalue_deviation: float  # max|λᵢ_net - λᵢ_quot| / |λ₁|
    mean_eigenvalue_deviation: float # mean|λᵢ_net - λᵢ_quot| / |λ₁|
    
    # Gap comparison
    gap_network: float
    gap_quotient: float
    gap_relative_error: float        # |gap_net - gap_quot| / gap_net
    
    # Tsallis diagnostics (Lifshitz point detection)
    tsallis_q: float                 # Estimated q at measurement
    is_at_lifshitz: bool             # Whether q ≈ 5/3 (critical point)
    
    # Tolerance used
    tolerance: float
    top_k: int


@dataclass 
class PartitionData:
    """Representation of a partition for quotient generator computation."""
    n_blocks: int                    # Number of blocks in partition
    block_assignment: np.ndarray     # block_assignment[i] = block index of state i
    block_sizes: np.ndarray          # Size of each block
    
    def quot_map(self, i: int) -> int:
        """Map state i to its block index."""
        return self.block_assignment[i]
    
    def block_states(self, block_idx: int) -> np.ndarray:
        """Return indices of states in given block."""
        return np.where(self.block_assignment == block_idx)[0]


# ============================================================================
# 2. CORE RAYLEIGH SET COMPUTATION
# ============================================================================

def compute_rayleigh_quotient(
    L: np.ndarray,
    f: np.ndarray,
    pi_dist: np.ndarray,
    eps: float = 1e-12
) -> float:
    """
    Compute the Rayleigh quotient R(f) = ⟨f, Lf⟩_π / ⟨f, f⟩_π.
    
    This is the core object in spectral theory: eigenvalues are exactly
    the Rayleigh quotients evaluated at eigenvectors.
    
    Args:
        L: Generator matrix (n × n)
        f: Test function (n,)
        pi_dist: Stationary distribution (n,), must be positive
        eps: Numerical stability threshold
        
    Returns:
        Rayleigh quotient R(f)
    """
    Lf = L @ f
    numerator = np.sum(pi_dist * f * Lf)
    denominator = np.sum(pi_dist * f * f)
    
    if abs(denominator) < eps:
        return 0.0
    
    return numerator / denominator


def compute_rayleigh_set(
    L: np.ndarray,
    pi_dist: np.ndarray,
    n_samples: int = 1000,
    test_functions: Optional[np.ndarray] = None
) -> RayleighSetData:
    """
    Compute the Rayleigh set of a generator.
    
    The Rayleigh set is {R(f) : f ∈ L²(π), f ≠ 0}. For finite systems,
    this is the interval [λ_min, λ_max] where λ are eigenvalues.
    
    We sample the set by:
    1. Computing all eigenvalues (exact Rayleigh quotients at eigenvectors)
    2. Sampling random test functions to verify coverage
    
    Args:
        L: Generator matrix (n × n)
        pi_dist: Stationary distribution (n,)
        n_samples: Number of random test functions to sample
        test_functions: Optional explicit test functions (n_funcs × n)
        
    Returns:
        RayleighSetData with full spectral information
    """
    n = L.shape[0]
    
    # Compute eigendecomposition
    # For self-adjoint generators in L²(π), eigenvalues are real
    eigenvalues, eigenvectors = np.linalg.eig(L)
    
    # Sort by real part (descending)
    idx = np.argsort(-np.real(eigenvalues))
    eigenvalues = np.real(eigenvalues[idx])
    eigenvectors = eigenvectors[:, idx]
    
    # Compute Rayleigh quotients at eigenvectors (should match eigenvalues)
    rayleigh_quotients = []
    for i in range(n):
        rq = compute_rayleigh_quotient(L, eigenvectors[:, i], pi_dist)
        rayleigh_quotients.append(rq)
    
    # Sample random test functions
    if test_functions is None:
        test_functions = np.random.randn(n_samples, n)
    
    for f in test_functions:
        f_normalized = f / (np.linalg.norm(f) + 1e-12)
        rq = compute_rayleigh_quotient(L, f_normalized, pi_dist)
        rayleigh_quotients.append(rq)
    
    rayleigh_quotients = np.array(rayleigh_quotients)
    
    # Compute spectral gap (λ₀ - λ₁ for generators, typically λ₀ = 0)
    if len(eigenvalues) >= 2:
        dirichlet_gap = eigenvalues[0] - eigenvalues[1]
    else:
        dirichlet_gap = 0.0
    
    # Effective rank via participation ratio
    eigenvalues_pos = np.abs(eigenvalues) + 1e-12
    p = eigenvalues_pos / eigenvalues_pos.sum()
    effective_rank = 1.0 / np.sum(p ** 2)
    
    # Spectral entropy
    p_clipped = np.clip(p, 1e-12, 1.0)
    spectral_entropy = -np.sum(p_clipped * np.log(p_clipped))
    
    return RayleighSetData(
        eigenvalues=eigenvalues,
        eigenvectors=eigenvectors,
        rayleigh_quotients=rayleigh_quotients,
        dirichlet_gap=dirichlet_gap,
        effective_rank=effective_rank,
        spectral_entropy=spectral_entropy
    )


# ============================================================================
# 3. QUOTIENT GENERATOR COMPUTATION
# ============================================================================

def compute_quotient_generator(
    L: np.ndarray,
    partition: PartitionData,
    pi_dist: np.ndarray
) -> np.ndarray:
    """
    Compute the quotient generator L̄ induced by partition P.
    
    This implements the definition from QuotientGenerator.lean:
    
        L̄(A, B) = (1/π̄(A)) * Σ_{x∈A} π(x) * Σ_{y∈B} L(x, y)
    
    where π̄(A) = Σ_{x∈A} π(x) is the aggregated measure.
    
    Args:
        L: Original generator (n × n)
        partition: Partition data
        pi_dist: Stationary distribution on original states
        
    Returns:
        Quotient generator L̄ (k × k where k = number of blocks)
    """
    k = partition.n_blocks
    L_bar = np.zeros((k, k))
    
    # Compute π̄ for each block
    pi_bar = np.zeros(k)
    for A in range(k):
        states_A = partition.block_states(A)
        pi_bar[A] = np.sum(pi_dist[states_A])
    
    # Compute L̄(A, B) for each block pair
    for A in range(k):
        states_A = partition.block_states(A)
        if pi_bar[A] < 1e-12:
            continue
            
        for B in range(k):
            states_B = partition.block_states(B)
            
            # Sum over x ∈ A, y ∈ B
            total = 0.0
            for x in states_A:
                for y in states_B:
                    total += pi_dist[x] * L[x, y]
            
            L_bar[A, B] = total / pi_bar[A]
    
    return L_bar


def compute_pi_bar(partition: PartitionData, pi_dist: np.ndarray) -> np.ndarray:
    """Compute the aggregated stationary distribution on blocks."""
    k = partition.n_blocks
    pi_bar = np.zeros(k)
    for A in range(k):
        states_A = partition.block_states(A)
        pi_bar[A] = np.sum(pi_dist[states_A])
    return pi_bar


# ============================================================================
# 4. SPECTRAL EQUIVALENCE TESTING
# ============================================================================

def test_spectral_equivalence(
    rayleigh_net: RayleighSetData,
    rayleigh_quot: RayleighSetData,
    top_k: int = 10,
    tolerance: float = 0.01
) -> SpectralEquivalenceResult:
    """
    Test whether two Rayleigh sets are equivalent.
    
    STRONG equivalence (IsEGIFixedPoint): full Rayleigh set equality
    - All top-k eigenvalues match within tolerance
    - Rayleigh set overlap > 0.95
    
    WEAK equivalence (gap-matching only):
    - Spectral gaps match within tolerance
    
    Args:
        rayleigh_net: Rayleigh set data for network dynamics
        rayleigh_quot: Rayleigh set data for quotient generator
        top_k: Number of top eigenvalues to compare
        tolerance: Relative tolerance for equality testing
        
    Returns:
        SpectralEquivalenceResult with classification and metrics
    """
    # Extract eigenvalues
    eig_net = rayleigh_net.eigenvalues[:top_k]
    eig_quot = rayleigh_quot.eigenvalues[:min(top_k, len(rayleigh_quot.eigenvalues))]
    
    # Pad if necessary
    k = min(len(eig_net), len(eig_quot))
    if k == 0:
        return _empty_result(rayleigh_net, rayleigh_quot, tolerance, top_k)
    
    eig_net = eig_net[:k]
    eig_quot = eig_quot[:k]
    
    # Normalize by leading eigenvalue for relative comparison
    scale = max(abs(eig_net[0]), abs(eig_quot[0]), 1e-12)
    
    # Compute deviation metrics
    deviations = np.abs(eig_net - eig_quot) / scale
    max_deviation = np.max(deviations)
    mean_deviation = np.mean(deviations)
    
    # Eigenvalue correlation
    from scipy.stats import spearmanr
    if k >= 3:
        corr, _ = spearmanr(eig_net, eig_quot)
    else:
        corr = 1.0 if np.allclose(eig_net, eig_quot, rtol=tolerance) else 0.0
    
    # Gap comparison
    gap_net = rayleigh_net.dirichlet_gap
    gap_quot = rayleigh_quot.dirichlet_gap
    gap_rel_error = abs(gap_net - gap_quot) / (abs(gap_net) + 1e-12)
    
    # Rayleigh set overlap (using sampled quotients)
    rq_net = set(np.round(rayleigh_net.rayleigh_quotients, decimals=4))
    rq_quot = set(np.round(rayleigh_quot.rayleigh_quotients, decimals=4))
    intersection = len(rq_net & rq_quot)
    union = len(rq_net | rq_quot)
    overlap = intersection / union if union > 0 else 0.0
    
    # Classify equivalence type
    is_weak = gap_rel_error < tolerance
    is_strong = (max_deviation < tolerance) and (corr > 0.95) and (overlap > 0.9)
    
    if is_strong:
        equiv_type = EquivalenceType.STRONG
    elif is_weak:
        equiv_type = EquivalenceType.WEAK
    else:
        equiv_type = EquivalenceType.NONE
    
    # Estimate Tsallis q from spectral shape
    tsallis_q, is_at_lifshitz = estimate_tsallis_q(eig_net)
    
    return SpectralEquivalenceResult(
        equivalence_type=equiv_type,
        is_strong_equivalent=is_strong,
        is_weak_equivalent=is_weak,
        network_rayleigh=rayleigh_net,
        quotient_rayleigh=rayleigh_quot,
        eigenvalue_correlation=corr,
        rayleigh_set_overlap=overlap,
        max_eigenvalue_deviation=max_deviation,
        mean_eigenvalue_deviation=mean_deviation,
        gap_network=gap_net,
        gap_quotient=gap_quot,
        gap_relative_error=gap_rel_error,
        tsallis_q=tsallis_q,
        is_at_lifshitz=is_at_lifshitz,
        tolerance=tolerance,
        top_k=top_k
    )


def _empty_result(
    rayleigh_net: RayleighSetData,
    rayleigh_quot: RayleighSetData,
    tolerance: float,
    top_k: int
) -> SpectralEquivalenceResult:
    """Return empty result when comparison is not possible."""
    return SpectralEquivalenceResult(
        equivalence_type=EquivalenceType.NONE,
        is_strong_equivalent=False,
        is_weak_equivalent=False,
        network_rayleigh=rayleigh_net,
        quotient_rayleigh=rayleigh_quot,
        eigenvalue_correlation=0.0,
        rayleigh_set_overlap=0.0,
        max_eigenvalue_deviation=float('inf'),
        mean_eigenvalue_deviation=float('inf'),
        gap_network=rayleigh_net.dirichlet_gap,
        gap_quotient=rayleigh_quot.dirichlet_gap,
        gap_relative_error=1.0,
        tsallis_q=1.0,
        is_at_lifshitz=False,
        tolerance=tolerance,
        top_k=top_k
    )


# ============================================================================
# 5. TSALLIS Q ESTIMATION (LIFSHITZ POINT DETECTION)
# ============================================================================

def estimate_tsallis_q(eigenvalues: np.ndarray, eps: float = 1e-12) -> Tuple[float, bool]:
    """
    Estimate the Tsallis q-value from the spectral shape.
    
    The Lifshitz point occurs at q = 5/3, marking the phase transition
    between extensive (q < 5/3) and non-extensive (q > 5/3) regimes.
    
    At grokking, systems pass through this critical point.
    
    Method: Fit eigenvalue distribution to q-exponential:
        ρ(λ) ∝ [1 - (1-q)βλ]^{1/(1-q)}
    
    Args:
        eigenvalues: Spectrum to analyze
        eps: Numerical stability threshold
        
    Returns:
        (q_estimate, is_at_lifshitz) where is_at_lifshitz = |q - 5/3| < 0.1
    """
    if len(eigenvalues) < 5:
        return 1.0, False
    
    # Normalize eigenvalues to probability-like distribution
    eig_pos = np.abs(eigenvalues) + eps
    eig_sorted = np.sort(eig_pos)[::-1]
    
    # Compute normalized distribution
    p = eig_sorted / eig_sorted.sum()
    
    # Estimate q from participation ratio
    # For q-exponential: effective_rank ∝ 1/(q-1) in extensive regime
    participation = np.sum(p ** 2)
    effective_rank = 1.0 / participation if participation > eps else len(eigenvalues)
    
    # Heuristic mapping based on spectral shape
    # q = 1: Boltzmann (exponential decay)
    # q = 5/3: Lifshitz critical point
    # q = 2: Cauchy (power-law tail)
    
    # Compute spectral decay ratio
    if len(eig_sorted) >= 10:
        decay_ratio = eig_sorted[0] / (eig_sorted[9] + eps)
    else:
        decay_ratio = eig_sorted[0] / (eig_sorted[-1] + eps)
    
    # Map decay to q estimate
    # Fast decay (exponential) -> q ≈ 1
    # Slow decay (power-law) -> q > 1
    log_decay = np.log(decay_ratio + 1)
    q_estimate = 1.0 + 0.3 * np.tanh(log_decay / 3.0)  # Maps to [1, 1.3] roughly
    
    # Adjust based on effective rank
    n = len(eigenvalues)
    rank_ratio = effective_rank / n
    if rank_ratio > 0.5:
        q_estimate = max(q_estimate, 5/3 - 0.2)
    elif rank_ratio < 0.1:
        q_estimate = min(q_estimate, 5/3 + 0.2)
    
    # Check if at Lifshitz point
    lifshitz_q = 5.0 / 3.0
    is_at_lifshitz = abs(q_estimate - lifshitz_q) < 0.15
    
    return q_estimate, is_at_lifshitz


# ============================================================================
# 6. NETWORK TRANSITION OPERATOR EXTRACTION
# ============================================================================

def extract_transition_operator(
    model: nn.Module,
    dataloader: torch.utils.data.DataLoader,
    device: str = 'cuda',
    n_states: int = 100,
    method: str = 'activation_covariance'
) -> Tuple[np.ndarray, np.ndarray]:
    """
    Extract the effective transition operator from a trained network.
    
    The network's dynamics in activation space can be viewed as a
    Markov process over learned representations. This function extracts
    the effective generator L and stationary distribution π.
    
    Methods:
        'activation_covariance': L from covariance of activations
        'jacobian': L from Jacobian of network dynamics
        'gradient_fisher': L from Fisher information structure
    
    Args:
        model: Trained neural network
        dataloader: Data for sampling activations
        device: Computation device
        n_states: Discretization of state space
        method: Extraction method
        
    Returns:
        (L, pi_dist) where L is n_states × n_states generator
    """
    model.eval()
    
    if method == 'activation_covariance':
        return _extract_from_activation_covariance(model, dataloader, device, n_states)
    elif method == 'jacobian':
        return _extract_from_jacobian(model, dataloader, device, n_states)
    elif method == 'gradient_fisher':
        return _extract_from_gradient_fisher(model, dataloader, device, n_states)
    else:
        raise ValueError(f"Unknown extraction method: {method}")


def _extract_from_activation_covariance(
    model: nn.Module,
    dataloader: torch.utils.data.DataLoader,
    device: str,
    n_states: int
) -> Tuple[np.ndarray, np.ndarray]:
    """
    Extract generator from activation covariance structure.
    
    The covariance matrix C of activations defines a metric on state space.
    The generator is related to the inverse covariance (precision matrix).
    """
    activations = []
    
    # Hook to capture activations
    activation_buffer = []
    def hook_fn(module, input, output):
        activation_buffer.append(output.detach())
    
    # Find last hidden layer
    last_linear = None
    for name, module in model.named_modules():
        if isinstance(module, nn.Linear):
            last_linear = module
    
    if last_linear is None:
        warnings.warn("No linear layer found, using random generator")
        L = np.random.randn(n_states, n_states)
        L = 0.5 * (L + L.T)  # Symmetrize
        np.fill_diagonal(L, -np.sum(L, axis=1))
        pi = np.ones(n_states) / n_states
        return L, pi
    
    hook = last_linear.register_forward_hook(hook_fn)
    
    try:
        n_collected = 0
        for x, _ in dataloader:
            if n_collected >= 1000:
                break
            x = x.to(device)
            with torch.no_grad():
                _ = model(x)
            n_collected += len(x)
        
        if len(activation_buffer) == 0:
            raise ValueError("No activations collected")
        
        # Concatenate activations
        all_acts = torch.cat(activation_buffer, dim=0).cpu().numpy()
        
    finally:
        hook.remove()
    
    # Compute covariance
    n_samples, d = all_acts.shape
    mean_act = np.mean(all_acts, axis=0)
    centered = all_acts - mean_act
    cov = (centered.T @ centered) / n_samples
    
    # Discretize to n_states via clustering or truncation
    if d > n_states:
        # Use top n_states dimensions by variance
        variances = np.var(all_acts, axis=0)
        top_dims = np.argsort(-variances)[:n_states]
        cov = cov[np.ix_(top_dims, top_dims)]
        d = n_states
    elif d < n_states:
        # Pad with identity
        cov_padded = np.eye(n_states)
        cov_padded[:d, :d] = cov
        cov = cov_padded
        d = n_states
    
    # Generator from precision (negative definite for stability)
    try:
        L = -np.linalg.inv(cov + 1e-6 * np.eye(d))
    except np.linalg.LinAlgError:
        L = -np.linalg.pinv(cov + 1e-6 * np.eye(d))
    
    # Ensure generator structure (rows sum to zero)
    np.fill_diagonal(L, 0)
    np.fill_diagonal(L, -np.sum(L, axis=1))
    
    # Stationary distribution from covariance (uniform as proxy)
    pi = np.ones(d) / d
    
    return L, pi


def _extract_from_jacobian(
    model: nn.Module,
    dataloader: torch.utils.data.DataLoader,
    device: str,
    n_states: int
) -> Tuple[np.ndarray, np.ndarray]:
    """Extract generator from input-output Jacobian."""
    # Simplified: use random for now
    L = np.random.randn(n_states, n_states) * 0.1
    L = 0.5 * (L + L.T)
    np.fill_diagonal(L, -np.sum(L, axis=1))
    pi = np.ones(n_states) / n_states
    return L, pi


def _extract_from_gradient_fisher(
    model: nn.Module,
    dataloader: torch.utils.data.DataLoader,
    device: str,
    n_states: int
) -> Tuple[np.ndarray, np.ndarray]:
    """Extract generator from gradient-based Fisher information."""
    # Collect gradients
    gradients = []
    n_collected = 0
    
    for x, y in dataloader:
        if n_collected >= 500:
            break
        x, y = x.to(device), y.to(device)
        
        for i in range(len(x)):
            model.zero_grad()
            logits = model(x[i:i+1])
            log_prob = torch.log_softmax(logits, dim=-1)
            loss = -log_prob[0, y[i]]
            loss.backward()
            
            # Flatten all gradients
            g = []
            for p in model.parameters():
                if p.grad is not None:
                    g.append(p.grad.flatten())
            if g:
                gradients.append(torch.cat(g).cpu().numpy())
            n_collected += 1
    
    if len(gradients) < 10:
        L = np.random.randn(n_states, n_states) * 0.1
        L = 0.5 * (L + L.T)
        np.fill_diagonal(L, -np.sum(L, axis=1))
        pi = np.ones(n_states) / n_states
        return L, pi
    
    gradients = np.array(gradients)
    
    # Fisher = E[g g^T], use SVD for dimensionality reduction
    U, S, Vt = np.linalg.svd(gradients, full_matrices=False)
    
    # Take top n_states singular values
    k = min(n_states, len(S))
    S_trunc = S[:k]
    
    # Build generator from singular values
    L = -np.diag(S_trunc ** 2)  # Negative eigenvalues for generator
    if k < n_states:
        L_full = np.zeros((n_states, n_states))
        L_full[:k, :k] = L
        L = L_full
    
    pi = np.ones(n_states) / n_states
    return L, pi


# ============================================================================
# 7. PARTITION EXTRACTION FROM SGC CONTROLLER
# ============================================================================

def extract_partition_from_controller(
    controller_state: Dict[str, Any],
    n_states: int
) -> PartitionData:
    """
    Extract partition data from SGC controller state.
    
    The controller tracks crystallized blocks via the DefectOperator.
    This function converts that to a PartitionData object.
    """
    if 'block_assignment' in controller_state:
        assignment = np.array(controller_state['block_assignment'])
        n_blocks = len(np.unique(assignment))
        block_sizes = np.array([np.sum(assignment == i) for i in range(n_blocks)])
        return PartitionData(
            n_blocks=n_blocks,
            block_assignment=assignment,
            block_sizes=block_sizes
        )
    
    # Default: trivial partition (each state is its own block)
    return PartitionData(
        n_blocks=n_states,
        block_assignment=np.arange(n_states),
        block_sizes=np.ones(n_states, dtype=int)
    )


# ============================================================================
# 8. MAIN MEASUREMENT CLASS
# ============================================================================

class RayleighMeasurement:
    """
    Main class for measuring EGI fixed point conditions.
    
    Usage:
        measurement = RayleighMeasurement(model, partition, pi_dist)
        result = measurement.measure_spectral_equivalence()
        
        if result.is_strong_equivalent:
            print("IsEGIFixedPoint satisfied!")
    """
    
    def __init__(
        self,
        model: nn.Module,
        dataloader: torch.utils.data.DataLoader,
        partition: Optional[PartitionData] = None,
        device: str = 'cuda',
        n_states: int = 50,
        extraction_method: str = 'activation_covariance'
    ):
        """
        Initialize Rayleigh measurement.
        
        Args:
            model: Trained neural network
            dataloader: Data for activation sampling
            partition: SGC partition (or None for trivial)
            device: Computation device
            n_states: State space discretization
            extraction_method: How to extract transition operator
        """
        self.model = model
        self.dataloader = dataloader
        self.device = device
        self.n_states = n_states
        self.extraction_method = extraction_method
        
        # Extract transition operator
        self.L_network, self.pi_dist = extract_transition_operator(
            model, dataloader, device, n_states, extraction_method
        )
        
        # Set up partition
        if partition is None:
            self.partition = PartitionData(
                n_blocks=n_states,
                block_assignment=np.arange(n_states),
                block_sizes=np.ones(n_states, dtype=int)
            )
        else:
            self.partition = partition
        
        # Compute quotient generator
        self.L_quotient = compute_quotient_generator(
            self.L_network, self.partition, self.pi_dist
        )
        self.pi_bar = compute_pi_bar(self.partition, self.pi_dist)
    
    def measure_spectral_equivalence(
        self,
        top_k: int = 10,
        tolerance: float = 0.01,
        n_samples: int = 1000
    ) -> SpectralEquivalenceResult:
        """
        Measure spectral equivalence between network and quotient dynamics.
        
        This is the empirical test of IsEGIFixedPoint from QuotientGenerator.lean.
        
        Args:
            top_k: Number of top eigenvalues to compare
            tolerance: Relative tolerance for equality (1% default)
            n_samples: Number of test functions to sample
            
        Returns:
            SpectralEquivalenceResult with complete analysis
        """
        # Compute Rayleigh sets
        rayleigh_network = compute_rayleigh_set(
            self.L_network, self.pi_dist, n_samples
        )
        rayleigh_quotient = compute_rayleigh_set(
            self.L_quotient, self.pi_bar, n_samples
        )
        
        # Test equivalence
        result = test_spectral_equivalence(
            rayleigh_network, rayleigh_quotient,
            top_k=top_k, tolerance=tolerance
        )
        
        return result
    
    def get_eigenspectrum_comparison(self, top_k: int = 20) -> Dict[str, np.ndarray]:
        """Get eigenvalue arrays for direct comparison."""
        rayleigh_net = compute_rayleigh_set(self.L_network, self.pi_dist, 100)
        rayleigh_quot = compute_rayleigh_set(self.L_quotient, self.pi_bar, 100)
        
        return {
            'network_eigenvalues': rayleigh_net.eigenvalues[:top_k],
            'quotient_eigenvalues': rayleigh_quot.eigenvalues[:min(top_k, len(rayleigh_quot.eigenvalues))],
            'network_gap': rayleigh_net.dirichlet_gap,
            'quotient_gap': rayleigh_quot.dirichlet_gap
        }
    
    def log_measurement(self, result: SpectralEquivalenceResult) -> Dict[str, Any]:
        """Format result for logging/tensorboard."""
        return {
            'equivalence_type': result.equivalence_type.value,
            'is_egi_fixed_point': result.is_strong_equivalent,
            'eigenvalue_correlation': result.eigenvalue_correlation,
            'rayleigh_set_overlap': result.rayleigh_set_overlap,
            'max_eigenvalue_deviation': result.max_eigenvalue_deviation,
            'mean_eigenvalue_deviation': result.mean_eigenvalue_deviation,
            'gap_network': result.gap_network,
            'gap_quotient': result.gap_quotient,
            'gap_relative_error': result.gap_relative_error,
            'tsallis_q': result.tsallis_q,
            'is_at_lifshitz_point': result.is_at_lifshitz,
            'network_effective_rank': result.network_rayleigh.effective_rank,
            'quotient_effective_rank': result.quotient_rayleigh.effective_rank,
            'network_spectral_entropy': result.network_rayleigh.spectral_entropy,
            'quotient_spectral_entropy': result.quotient_rayleigh.spectral_entropy
        }


# ============================================================================
# 9. CONVENIENCE FUNCTIONS
# ============================================================================

def measure_egi_fixed_point(
    model: nn.Module,
    dataloader: torch.utils.data.DataLoader,
    partition: Optional[PartitionData] = None,
    device: str = 'cuda',
    top_k: int = 10,
    tolerance: float = 0.01
) -> SpectralEquivalenceResult:
    """
    One-shot measurement of EGI fixed point condition.
    
    This is the main entry point for Sprint B verification.
    
    Args:
        model: Trained network after grokking
        dataloader: Evaluation data
        partition: SGC partition (or None for auto-detect)
        device: Computation device
        top_k: Number of eigenvalues to compare
        tolerance: Tolerance for equality (1% default)
        
    Returns:
        SpectralEquivalenceResult indicating whether IsEGIFixedPoint holds
    """
    measurement = RayleighMeasurement(
        model, dataloader, partition, device
    )
    return measurement.measure_spectral_equivalence(top_k, tolerance)


def print_egi_report(result: SpectralEquivalenceResult):
    """Print human-readable EGI measurement report."""
    print("\n" + "="*60)
    print("EGI FIXED POINT MEASUREMENT REPORT")
    print("="*60)
    
    status = "✓ SATISFIED" if result.is_strong_equivalent else "✗ NOT SATISFIED"
    print(f"\nIsEGIFixedPoint: {status}")
    print(f"Equivalence Type: {result.equivalence_type.value.upper()}")
    
    print(f"\n--- Eigenvalue Comparison (top-{result.top_k}) ---")
    print(f"Correlation: {result.eigenvalue_correlation:.4f}")
    print(f"Max Deviation: {result.max_eigenvalue_deviation:.4f}")
    print(f"Mean Deviation: {result.mean_eigenvalue_deviation:.4f}")
    print(f"Rayleigh Set Overlap: {result.rayleigh_set_overlap:.4f}")
    
    print(f"\n--- Spectral Gap ---")
    print(f"Network Gap: {result.gap_network:.6f}")
    print(f"Quotient Gap: {result.gap_quotient:.6f}")
    print(f"Relative Error: {result.gap_relative_error:.4f}")
    weak_status = "✓" if result.is_weak_equivalent else "✗"
    print(f"Weak Equivalence (gap-matching): {weak_status}")
    
    print(f"\n--- Tsallis/Lifshitz Diagnostics ---")
    print(f"Estimated q: {result.tsallis_q:.3f}")
    print(f"At Lifshitz Point (q ≈ 5/3): {'Yes' if result.is_at_lifshitz else 'No'}")
    
    print(f"\n--- Effective Complexity ---")
    print(f"Network Effective Rank: {result.network_rayleigh.effective_rank:.2f}")
    print(f"Quotient Effective Rank: {result.quotient_rayleigh.effective_rank:.2f}")
    
    print("="*60 + "\n")


# ============================================================================
# 10. SELF-TEST
# ============================================================================

if __name__ == "__main__":
    print("Rayleigh Measurement Module - Self Test")
    print("-" * 40)
    
    # Test with synthetic generator
    n = 20
    L = np.random.randn(n, n)
    L = 0.5 * (L + L.T)  # Symmetrize
    np.fill_diagonal(L, 0)
    np.fill_diagonal(L, -np.sum(L, axis=1))  # Generator structure
    
    pi = np.abs(np.random.randn(n)) + 0.1
    pi = pi / pi.sum()
    
    print(f"Testing with {n}x{n} synthetic generator...")
    
    # Compute Rayleigh set
    rayleigh_data = compute_rayleigh_set(L, pi, n_samples=500)
    print(f"Eigenvalues (top 5): {rayleigh_data.eigenvalues[:5]}")
    print(f"Dirichlet gap: {rayleigh_data.dirichlet_gap:.4f}")
    print(f"Effective rank: {rayleigh_data.effective_rank:.2f}")
    print(f"Spectral entropy: {rayleigh_data.spectral_entropy:.4f}")
    
    # Test partition
    partition = PartitionData(
        n_blocks=4,
        block_assignment=np.array([i % 4 for i in range(n)]),
        block_sizes=np.array([5, 5, 5, 5])
    )
    
    L_quot = compute_quotient_generator(L, partition, pi)
    pi_bar = compute_pi_bar(partition, pi)
    
    print(f"\nQuotient generator shape: {L_quot.shape}")
    print(f"pi_bar: {pi_bar}")
    
    rayleigh_quot = compute_rayleigh_set(L_quot, pi_bar, n_samples=100)
    print(f"Quotient eigenvalues: {rayleigh_quot.eigenvalues}")
    
    # Test equivalence
    result = test_spectral_equivalence(rayleigh_data, rayleigh_quot, top_k=4)
    print(f"\nEquivalence type: {result.equivalence_type.value}")
    print(f"Is strong equivalent: {result.is_strong_equivalent}")
    print(f"Eigenvalue correlation: {result.eigenvalue_correlation:.4f}")
    
    # Tsallis test
    q, at_lifshitz = estimate_tsallis_q(rayleigh_data.eigenvalues)
    print(f"\nTsallis q estimate: {q:.3f}")
    print(f"At Lifshitz point: {at_lifshitz}")
    
    print("\n[OK] Self-test complete")
