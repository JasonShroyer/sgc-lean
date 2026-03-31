#!/usr/bin/env python3
"""
PERIHELION Sprint 3 - Fix C: Analytical Ground Truth for NOISE_CORRELATION

For approximate equality (|a-b| < ε) on iid Gaussian noise N(0, σ²):

The trans_rate for the relation "approximately equal" is:
    trans_rate = P(|A-C| < ε | |A-B| < ε AND |B-C| < ε)

For iid Gaussians A, B, C ~ N(0, σ²):
    P(|A-B| < ε) = P(|X| < ε) where X = A-B ~ N(0, 2σ²)
                 = erf(ε / (σ√4)) = erf(ε / (2σ))

The conditional probability P(|A-C| < ε | |A-B| < ε, |B-C| < ε) requires
computing the probability over the constrained region. This is non-trivial
for the general case, but can be computed via Monte Carlo or numerical integration.

For INDEPENDENT edges (the null model):
    P(|A-C| < ε) = erf(ε / (2σ))
    
The deviation from independence reveals the transitivity structure.
"""

import numpy as np
from scipy.special import erf
from scipy.stats import norm
from typing import Tuple


def probability_within_tolerance(epsilon: float, sigma: float) -> float:
    """
    Compute P(|A-B| < ε) for A, B ~ iid N(0, σ²).
    
    A - B ~ N(0, 2σ²), so |A-B| follows a folded normal distribution.
    P(|A-B| < ε) = P(-ε < A-B < ε) = erf(ε / (σ√2 · √2)) = erf(ε / (2σ))
    """
    return float(erf(epsilon / (2 * sigma)))


def compute_trans_rate_monte_carlo(
    epsilon: float,
    sigma: float,
    n_samples: int = 100000,
    seed: int = 42
) -> Tuple[float, float]:
    """
    Compute trans_rate via Monte Carlo simulation.
    
    Generate iid triplets (A, B, C) ~ N(0, σ²).
    Filter to chains where |A-B| < ε AND |B-C| < ε.
    Compute fraction where |A-C| < ε (closure).
    
    Returns:
        (trans_rate, standard_error)
    """
    np.random.seed(seed)
    
    # Generate triplets
    A = np.random.normal(0, sigma, n_samples)
    B = np.random.normal(0, sigma, n_samples)
    C = np.random.normal(0, sigma, n_samples)
    
    # Find chains: |A-B| < ε AND |B-C| < ε
    chain_mask = (np.abs(A - B) < epsilon) & (np.abs(B - C) < epsilon)
    n_chains = np.sum(chain_mask)
    
    if n_chains < 10:
        return 0.0, 1.0  # Not enough chains
    
    # Find closures: |A-C| < ε among chains
    A_chains = A[chain_mask]
    C_chains = C[chain_mask]
    n_closures = np.sum(np.abs(A_chains - C_chains) < epsilon)
    
    trans_rate = n_closures / n_chains
    
    # Standard error (binomial)
    se = np.sqrt(trans_rate * (1 - trans_rate) / n_chains)
    
    return trans_rate, se


def compute_theoretical_delta(
    epsilon: float,
    sigma: float,
    n_samples: int = 1000000
) -> dict:
    """
    Compute theoretical δ for NOISE_CORRELATION with approximate equality.
    
    δ = 1 - trans_rate
    
    Returns detailed statistics.
    """
    # Edge probability
    p_edge = probability_within_tolerance(epsilon, sigma)
    
    # Monte Carlo trans_rate
    trans_rate, se = compute_trans_rate_monte_carlo(epsilon, sigma, n_samples)
    
    # Delta
    delta = 1 - trans_rate
    delta_se = se  # Same standard error
    
    # Independent edge model prediction (null hypothesis)
    # If edges were independent: trans_rate = p_edge
    trans_rate_independent = p_edge
    
    return {
        'epsilon': epsilon,
        'sigma': sigma,
        'p_edge': p_edge,
        'trans_rate': trans_rate,
        'trans_rate_se': se,
        'delta': delta,
        'delta_se': delta_se,
        'trans_rate_independent': trans_rate_independent,
        'delta_independent': 1 - trans_rate_independent,
        'excess_transitivity': trans_rate - trans_rate_independent
    }


def analyze_noise_correlation_ground_truth():
    """
    Analyze theoretical ground truth for NOISE_CORRELATION.
    
    Sweep over σ and ε to map the transitivity landscape.
    """
    print("=" * 70)
    print("  PERIHELION Sprint 3 - Fix C: Noise Correlation Ground Truth")
    print("  Analytical derivation for approximate equality on Gaussian noise")
    print("=" * 70)
    
    # Standard wavelet cD coefficient sigma (from Sprint 1 experiments)
    sigma_values = [0.5, 1.0, 2.0]
    epsilon_values = [0.25, 0.5, 1.0, 2.0]
    
    print(f"\n[1] Edge probability P(|A-B| < eps) for A,B ~ iid N(0, sigma^2):")
    print(f"  {'eps\\sig':>8}", end="")
    for sigma in sigma_values:
        print(f"  {sigma:>8.2f}", end="")
    print()
    print(f"  {'-'*8}", end="")
    for _ in sigma_values:
        print(f"  {'-'*8}", end="")
    print()
    
    for epsilon in epsilon_values:
        print(f"  {epsilon:>8.2f}", end="")
        for sigma in sigma_values:
            p = probability_within_tolerance(epsilon, sigma)
            print(f"  {p:>8.4f}", end="")
        print()
    
    print(f"\n[2] Trans_rate (Monte Carlo, n=1M samples):")
    print(f"  {'eps\\sig':>8}", end="")
    for sigma in sigma_values:
        print(f"  {sigma:>8.2f}", end="")
    print()
    print(f"  {'-'*8}", end="")
    for _ in sigma_values:
        print(f"  {'-'*8}", end="")
    print()
    
    results = {}
    for epsilon in epsilon_values:
        print(f"  {epsilon:>8.2f}", end="")
        for sigma in sigma_values:
            r = compute_theoretical_delta(epsilon, sigma, n_samples=1000000)
            results[(epsilon, sigma)] = r
            print(f"  {r['trans_rate']:>8.4f}", end="")
        print()
    
    print(f"\n[3] Delta = 1 - trans_rate:")
    print(f"  {'eps\\sig':>8}", end="")
    for sigma in sigma_values:
        print(f"  {sigma:>8.2f}", end="")
    print()
    print(f"  {'-'*8}", end="")
    for _ in sigma_values:
        print(f"  {'-'*8}", end="")
    print()
    
    for epsilon in epsilon_values:
        print(f"  {epsilon:>8.2f}", end="")
        for sigma in sigma_values:
            r = results[(epsilon, sigma)]
            print(f"  {r['delta']:>8.4f}", end="")
        print()
    
    print(f"\n[4] Excess transitivity (trans_rate - p_edge):")
    print(f"  {'eps\\sig':>8}", end="")
    for sigma in sigma_values:
        print(f"  {sigma:>8.2f}", end="")
    print()
    print(f"  {'-'*8}", end="")
    for _ in sigma_values:
        print(f"  {'-'*8}", end="")
    print()
    
    for epsilon in epsilon_values:
        print(f"  {epsilon:>8.2f}", end="")
        for sigma in sigma_values:
            r = results[(epsilon, sigma)]
            print(f"  {r['excess_transitivity']:>+8.4f}", end="")
        print()
    
    # Key insight
    print(f"\n[5] Key theoretical insight:")
    print(f"  For iid Gaussian noise, approximate equality IS transitive!")
    print(f"  If |A-B| < eps and |B-C| < eps, then |A-C| < 2*eps by triangle inequality.")
    print(f"  But |A-C| < eps is STRONGER than the triangle bound.")
    print(f"")
    print(f"  The excess transitivity (trans_rate > p_edge) occurs because:")
    print(f"  - Conditioning on |A-B| < eps and |B-C| < eps constrains A and C")
    print(f"  - This makes |A-C| < eps MORE likely than under independence")
    print(f"")
    print(f"  For NOISE_CORRELATION, we expect:")
    print(f"  - delta < 0.5 (trans_rate > 0.5) because of this excess transitivity")
    print(f"  - The exact value depends on eps/sigma ratio")
    
    # Recommended test case
    print(f"\n[6] Recommended test configuration:")
    # Pick eps/sigma = 1 as a reasonable middle ground
    epsilon_test = 1.0
    sigma_test = 1.0
    r_test = results[(epsilon_test, sigma_test)]
    
    print(f"  sigma = {sigma_test}, eps = {epsilon_test}")
    print(f"  P(|A-B| < eps) = {r_test['p_edge']:.4f}")
    print(f"  Theoretical trans_rate = {r_test['trans_rate']:.4f} +/- {r_test['trans_rate_se']:.4f}")
    print(f"  Theoretical delta = {r_test['delta']:.4f} +/- {r_test['delta_se']:.4f}")
    print(f"  Excess transitivity = {r_test['excess_transitivity']:+.4f}")
    
    print("\n" + "=" * 70)
    
    return results


if __name__ == "__main__":
    results = analyze_noise_correlation_ground_truth()
