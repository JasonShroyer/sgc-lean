# spectral.py
"""
Spectral analysis: spectral gap, timescales, Dirichlet decomposition, Schur correction.
"""
import numpy as np
from typing import Tuple


def compute_spectral_gap(L: np.ndarray, pi: np.ndarray) -> Tuple[float, np.ndarray]:
    """
    γ = min{-Re(λ) : λ eigenvalue of L, λ ≠ 0}.
    The Dirichlet spectral gap controls mixing time.
    [theorem: dirichlet_gap_non_decrease in Lumpability.lean]
    """
    eigenvalues = np.linalg.eigvals(L)
    real_parts = np.real(eigenvalues)
    # Filter out eigenvalues very close to zero (the stationary mode)
    nonzero_mask = np.abs(real_parts) > 1e-10
    nonzero = real_parts[nonzero_mask]
    
    if len(nonzero) > 0:
        # Spectral gap is the smallest magnitude of negative real parts
        # (eigenvalues of generator are ≤ 0)
        negative = nonzero[nonzero < 0]
        if len(negative) > 0:
            gamma = float(np.min(np.abs(negative)))
        else:
            gamma = 0.0
    else:
        gamma = 0.0
    
    return gamma, eigenvalues


def compute_timescales(eigenvalues: np.ndarray) -> np.ndarray:
    """
    T_k = -1/Re(λ_k). The characteristic timescales of each mode.
    [theorem: trajectory_closure_bound — timescales determine dynamics]
    """
    real_parts = np.real(eigenvalues)
    # Filter out zero eigenvalue
    nonzero_mask = np.abs(real_parts) > 1e-10
    nonzero = real_parts[nonzero_mask]
    
    if len(nonzero) == 0:
        return np.array([])
    
    # Timescales are -1/Re(λ) for negative eigenvalues
    negative = nonzero[nonzero < 0]
    if len(negative) == 0:
        return np.array([])
    
    timescales = -1.0 / negative
    return np.sort(timescales)[::-1]  # sorted slowest to fastest


def count_timescale_gaps(timescales: np.ndarray, gap_ratio: float = 2.0) -> int:
    """
    Count the number of well-separated timescale clusters.
    A gap exists where T_k / T_{k+1} > gap_ratio.
    This is the autopoietic depth d(L, pi).
    [theorem: rg_tower_terminates — tower levels = timescale separations]
    
    Default gap_ratio=2.0 detects moderate timescale separation (factor of 2).
    For stricter separation, use gap_ratio=5.0 or higher.
    """
    if len(timescales) < 2:
        return 0
    
    # Ensure timescales are sorted in descending order (slowest first)
    ts = np.sort(timescales)[::-1]
    
    # Compute ratios between consecutive timescales
    ratios = ts[:-1] / np.clip(ts[1:], 1e-15, None)
    return int(np.sum(ratios > gap_ratio))


def compute_dirichlet_form(L: np.ndarray, pi: np.ndarray, f: np.ndarray) -> float:
    """
    ℰ(f) = -⟨f, Lf⟩_π = -Σ_v π(v) f(v) (Lf)(v).
    Note: For generators, this is non-negative (Lf has opposite sign convention).
    [theorem: DirichletForm_nonneg in Lumpability.lean]
    """
    Lf = L @ f
    return -float(np.sum(pi * f * Lf))


def decompose_dirichlet(
    L: np.ndarray, pi: np.ndarray, Pi: np.ndarray, f: np.ndarray
) -> Tuple[float, float]:
    """
    Decompose ℰ(f) = ⟨f, -L̄f⟩_π + ⟨f, -Df⟩_π
    Returns (coarse_component, leakage_component).
    [theorem: dirichlet_form_defect_decomposition in EmergenceCapacity.lean]
    """
    from .partition import compute_defect_operator
    
    I = np.eye(len(L))
    D = compute_defect_operator(L, Pi)
    
    # L̄ = Π L (the coarse generator component)
    L_bar = Pi @ L
    
    # Coarse component: -⟨f, L̄f⟩_π
    coarse = -float(np.sum(pi * f * (L_bar @ f)))
    
    # Leakage component: -⟨f, Df⟩_π  
    leakage = -float(np.sum(pi * f * (D @ f)))
    
    return coarse, leakage


def compute_schur_correction(
    L: np.ndarray, pi: np.ndarray, assignment: np.ndarray
) -> np.ndarray:
    """
    Δ = D_upper · L_fine⁻¹ · D_lower (Wilsonian self-energy correction).
    The difference between the Schur complement and the quotient generator.
    L_eff = L̄ + Δ is the second-order effective coarse generator.
    [Discovery: Continent 4 — not yet in Lean formalization]
    """
    from .partition import compute_projector, compute_defect_operator
    
    n = len(L)
    Pi = compute_projector(pi, assignment)
    I = np.eye(n)
    
    # Block decomposition
    # D_upper: coarse→fine = Π L (I-Π)
    # D_lower: fine→coarse = (I-Π) L Π  
    # L_fine: fine→fine = (I-Π) L (I-Π)
    
    D_upper = Pi @ L @ (I - Pi)
    D_lower = (I - Pi) @ L @ Pi
    L_fine = (I - Pi) @ L @ (I - Pi)
    
    # Pseudoinverse of L_fine (on the fine subspace)
    try:
        # Use pseudoinverse since L_fine is singular on coarse subspace
        L_fine_pinv = np.linalg.pinv(L_fine, rcond=1e-10)
        Sigma = D_upper @ L_fine_pinv @ D_lower
    except np.linalg.LinAlgError:
        Sigma = np.zeros_like(L)
    
    return Sigma


def rayleigh_quotient(L: np.ndarray, pi: np.ndarray, f: np.ndarray) -> float:
    """
    R(f) = ℰ(f) / ‖f‖²_π = -⟨f, Lf⟩_π / ⟨f, f⟩_π.
    [theorem: RayleighQuotient definition in Lumpability.lean]
    """
    norm_sq = np.sum(pi * f * f)
    if norm_sq < 1e-15:
        return 0.0
    return compute_dirichlet_form(L, pi, f) / norm_sq


def compute_mixing_time(gamma: float, epsilon: float = 0.01) -> float:
    """
    t_mix(ε) ≈ (1/γ) log(1/ε).
    The time to reach ε-close to stationarity.
    """
    if gamma < 1e-15:
        return float('inf')
    return (1.0 / gamma) * np.log(1.0 / epsilon)
