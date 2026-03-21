# tsallis.py
"""
Tsallis index estimation and related statistics.
"""
import numpy as np
from scipy.optimize import minimize_scalar
from typing import Tuple, Dict, Any


def estimate_tsallis_q(pi: np.ndarray) -> Tuple[float, Dict[str, Any]]:
    """
    Estimate q from the stationary distribution π using the escort distribution fit.
    
    Method: Maximum likelihood fit of π(v) ∝ [1 - (1-q)·E(v)/T]^{1/(1-q)}
    to the empirical distribution, where E(v) are effective energies = -log π(v).
    
    For q=1 (Boltzmann): π(v) ∝ exp(-E(v))
    For q≠1 (Tsallis):   π(v) ∝ [1-(1-q)E(v)]^{1/(1-q)}
    
    The q value where the fit is best is the system's Tsallis index.
    
    [theorem: TsallisStatistics.lean — D_q ≥ 0 for q ∈ (1,2)]
    [Note: q estimation from data is EMPIRICAL — not a Lean theorem]
    """
    # Ensure valid probability distribution
    pi_safe = np.clip(pi, 1e-15, 1.0)
    pi_safe = pi_safe / pi_safe.sum()
    
    # Effective energies (up to temperature factor)
    energies = -np.log(pi_safe)
    # Normalize energies to have mean 0 for numerical stability
    energies = energies - energies.mean()
    
    def neg_log_likelihood(q: float) -> float:
        """Negative log-likelihood of π under Tsallis distribution with index q."""
        if abs(q - 1.0) < 1e-6:
            # q→1 limit: Boltzmann distribution
            # π(v) ∝ exp(-E(v)), so log π(v) = -E(v) - log(Z)
            log_Z = np.log(np.sum(np.exp(-energies)))
            return float(np.sum(pi_safe * (energies + log_Z)))
        
        # Tsallis: π_q(v) ∝ [1-(1-q)E]^{1/(1-q)} = exp_q(-E)
        # log π_q(v) = (1/(1-q)) log[1-(1-q)E] - log(Z_q)
        base = 1.0 - (1.0 - q) * energies
        
        # Check if base is valid (must be positive for real power)
        if np.any(base <= 0):
            return 1e10  # Invalid: return large penalty
        
        log_unnorm = np.log(base) / (1.0 - q)
        log_Z = np.log(np.sum(np.exp(log_unnorm - log_unnorm.max()))) + log_unnorm.max()
        log_pq_normalized = log_unnorm - log_Z
        
        # NLL = -Σ π(v) log π_q(v)
        return -float(np.sum(pi_safe * log_pq_normalized))
    
    # Search over q ∈ (1.0, 2.0) — the physically relevant range
    # q < 1: compact support distributions (less common)
    # q > 2: very heavy tails (pathological)
    try:
        result = minimize_scalar(
            neg_log_likelihood, 
            bounds=(1.001, 1.999), 
            method='bounded',
            options={'xatol': 1e-4}
        )
        q_star = float(result.x)
        nll_tsallis = float(result.fun)
    except Exception:
        q_star = 1.0
        nll_tsallis = neg_log_likelihood(1.0)
    
    # Compute q=1 likelihood for comparison
    nll_boltzmann = neg_log_likelihood(1.0)
    
    # Determine regime
    if abs(q_star - 1.0) < 0.05:
        regime = "near_boltzmann"
    elif abs(q_star - 1.5) < 0.15:
        regime = "near_attractor"  # q=3/2 is the Umarov-Tsallis attractor
    elif q_star > 1.7:
        regime = "heavy_tail"
    else:
        regime = "intermediate"
    
    diagnostics = {
        "q_star": q_star,
        "nll_boltzmann": nll_boltzmann,
        "nll_tsallis": nll_tsallis,
        "improvement": nll_boltzmann - nll_tsallis,
        "regime": regime,
        "citation": "EMPIRICAL — q estimated from π, not derived from theorem"
    }
    
    return q_star, diagnostics


def compute_tsallis_entropy(pi: np.ndarray, q: float) -> float:
    """
    S_q(π) = (1 - Σ π^q) / (q-1).
    For q→1, this reduces to Shannon entropy S_1 = -Σ π log π.
    [theorem: TsallisStatistics.lean, S_q ≥ 0]
    """
    pi_safe = np.clip(pi, 1e-15, 1.0)
    pi_safe = pi_safe / pi_safe.sum()
    
    if abs(q - 1.0) < 1e-6:
        # Shannon entropy limit
        return -float(np.sum(pi_safe * np.log(pi_safe)))
    
    return float((1.0 - np.sum(pi_safe ** q)) / (q - 1.0))


def compute_escort_distribution(pi: np.ndarray, q: float) -> np.ndarray:
    """
    P_q(v) = π(v)^q / Σ_w π(w)^q.
    The escort distribution reweights by the q-th power.
    [theorem: escort_is_distribution in TsallisStatistics.lean]
    """
    pi_safe = np.clip(pi, 1e-15, 1.0)
    pi_q = pi_safe ** q
    return pi_q / pi_q.sum()


def compute_tsallis_divergence(p: np.ndarray, q_dist: np.ndarray, q: float) -> float:
    """
    D_q(p || q) = (1/(q-1)) * (1 - Σ p^q / q^{q-1}).
    The Tsallis divergence (q-divergence).
    [theorem: tsallis_dpi — D_q satisfies DPI for q ∈ (1,2)]
    """
    p_safe = np.clip(p, 1e-15, 1.0)
    q_safe = np.clip(q_dist, 1e-15, 1.0)
    
    if abs(q - 1.0) < 1e-6:
        # KL divergence limit
        return float(np.sum(p_safe * np.log(p_safe / q_safe)))
    
    ratio = (p_safe ** q) / (q_safe ** (q - 1))
    return float((1.0 - np.sum(ratio)) / (q - 1.0))


def q_exponential(x: np.ndarray, q: float) -> np.ndarray:
    """
    exp_q(x) = [1 + (1-q)x]^{1/(1-q)} if 1+(1-q)x > 0, else 0.
    The q-exponential function.
    """
    if abs(q - 1.0) < 1e-6:
        return np.exp(x)
    
    base = 1.0 + (1.0 - q) * x
    result = np.zeros_like(x)
    valid = base > 0
    result[valid] = base[valid] ** (1.0 / (1.0 - q))
    return result


def q_logarithm(x: np.ndarray, q: float) -> np.ndarray:
    """
    ln_q(x) = (x^{1-q} - 1) / (1-q) for x > 0.
    The q-logarithm function.
    """
    x_safe = np.clip(x, 1e-15, None)
    
    if abs(q - 1.0) < 1e-6:
        return np.log(x_safe)
    
    return (x_safe ** (1.0 - q) - 1.0) / (1.0 - q)
