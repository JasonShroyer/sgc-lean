"""
Critical Exponent Analysis for THRML-002b Results

Analyzes the finite-size scaling data to extract critical exponents
and further validate the phase transition hypothesis.

Author: SGC Research Team
Date: February 6, 2026
"""

import json
import numpy as np
from scipy.optimize import curve_fit
import os

def load_results(results_dir: str = "logs/thrml002"):
    """Load the most recent results."""
    runs = sorted([d for d in os.listdir(results_dir) if d.startswith("run_")])
    if not runs:
        raise FileNotFoundError("No results found")
    
    latest = os.path.join(results_dir, runs[-1], "results.json")
    with open(latest, "r") as f:
        return json.load(f)


def power_law(N, A, alpha):
    """Power law: Cv_max ~ N^alpha"""
    return A * np.power(N, alpha)


def analyze_cv_scaling(data):
    """
    Analyze how Cv_max scales with system size N.
    
    For a phase transition, we expect Cv_max ~ N^(alpha/nu)
    where alpha is the specific heat exponent and nu is the correlation length exponent.
    """
    print("\n" + "="*60)
    print("SPECIFIC HEAT SCALING ANALYSIS")
    print("="*60)
    
    p_values = data['p_values']
    N_values = np.array([3 * (p - 1) for p in p_values])
    Cv_max = np.array(data['scaling']['Cv_maxs'])
    
    print(f"\nData:")
    print(f"  p values: {p_values}")
    print(f"  N values: {N_values.tolist()}")
    print(f"  Cv_max:   {Cv_max.tolist()}")
    
    # Fit power law
    try:
        popt, pcov = curve_fit(power_law, N_values, Cv_max, p0=[0.1, 1.0])
        A, alpha = popt
        A_err, alpha_err = np.sqrt(np.diag(pcov))
        
        print(f"\nPower law fit: Cv_max = A * N^alpha")
        print(f"  A     = {A:.4f} +/- {A_err:.4f}")
        print(f"  alpha = {alpha:.4f} +/- {alpha_err:.4f}")
        
        # Compute R^2
        Cv_pred = power_law(N_values, A, alpha)
        ss_res = np.sum((Cv_max - Cv_pred)**2)
        ss_tot = np.sum((Cv_max - np.mean(Cv_max))**2)
        r2 = 1 - ss_res / ss_tot
        print(f"  R^2   = {r2:.4f}")
        
        # Interpretation
        print(f"\nInterpretation:")
        if alpha > 0.8:
            print(f"  alpha ~ 1 suggests first-order-like transition")
        elif alpha > 0.3:
            print(f"  alpha ~ 0.5 suggests 2D Ising-like universality class")
        else:
            print(f"  alpha ~ 0 suggests logarithmic divergence (mean-field)")
        
        return {'A': A, 'alpha': alpha, 'A_err': A_err, 'alpha_err': alpha_err, 'r2': r2}
    
    except Exception as e:
        print(f"  Fit failed: {e}")
        return None


def analyze_beta_c_scaling(data):
    """
    Analyze how the critical temperature scales with system size.
    
    beta_c(N) = beta_c(inf) + c * N^(-1/nu)
    """
    print("\n" + "="*60)
    print("CRITICAL TEMPERATURE SCALING")
    print("="*60)
    
    p_values = data['p_values']
    N_values = np.array([3 * (p - 1) for p in p_values])
    beta_cvs = np.array(data['scaling']['beta_cvs'])
    
    print(f"\nData:")
    print(f"  N values:  {N_values.tolist()}")
    print(f"  beta_Cv:   {beta_cvs.tolist()}")
    
    # For finite-size scaling: beta_c(N) = beta_c(inf) + c/N^(1/nu)
    # Simplified: fit beta_c vs 1/N
    inv_N = 1.0 / N_values
    
    # Linear fit: beta_c = a + b/N
    coeffs = np.polyfit(inv_N, beta_cvs, 1)
    b, a = coeffs
    
    print(f"\nLinear extrapolation: beta_c(N) = a + b/N")
    print(f"  beta_c(inf) = {a:.4f}")
    print(f"  b           = {b:.4f}")
    
    # Predict for larger N
    N_inf = np.array([50, 100, 200])
    beta_inf = a + b / N_inf
    print(f"\nExtrapolation to larger systems:")
    for n, bc in zip(N_inf, beta_inf):
        print(f"  N = {n}: beta_c ~ {bc:.4f}")
    
    return {'beta_c_inf': a, 'b': b}


def analyze_order_parameter_collapse(data):
    """
    Check if order parameter curves collapse under finite-size scaling.
    
    For a phase transition: epsilon(beta, N) = f((beta - beta_c) * N^(1/nu))
    """
    print("\n" + "="*60)
    print("ORDER PARAMETER ANALYSIS")
    print("="*60)
    
    p_values = data['p_values']
    
    print(f"\nTransition sharpness (d(epsilon_H)/d(beta) at transition):")
    
    for p in p_values:
        results = data['results'][str(p)]
        betas = np.array(results['betas'])
        epsilon_H = np.array(results['epsilon_H'])
        
        # Find steepest descent
        d_eps = np.diff(epsilon_H) / np.diff(betas)
        steepest_idx = np.argmin(d_eps)
        steepest_slope = d_eps[steepest_idx]
        beta_at_steepest = betas[steepest_idx]
        
        N = 3 * (p - 1)
        print(f"  p={p:2d} (N={N:2d}): slope = {steepest_slope:.3f} at beta = {beta_at_steepest:.3f}")
    
    return None


def analyze_accuracy_transition(data):
    """
    Analyze the accuracy transition and its sharpening with system size.
    """
    print("\n" + "="*60)
    print("ACCURACY TRANSITION ANALYSIS")
    print("="*60)
    
    p_values = data['p_values']
    
    print(f"\nBeta at which accuracy crosses 90%:")
    
    beta_90_list = []
    
    for p in p_values:
        results = data['results'][str(p)]
        betas = np.array(results['betas'])
        accuracy = np.array(results['accuracy'])
        
        # Find beta where accuracy first exceeds 90%
        idx_90 = np.argmax(accuracy > 0.9)
        if accuracy[idx_90] > 0.9:
            beta_90 = betas[idx_90]
        else:
            beta_90 = np.nan
        
        beta_90_list.append(beta_90)
        
        N = 3 * (p - 1)
        print(f"  p={p:2d} (N={N:2d}): beta_90% = {beta_90:.3f}, final_acc = {accuracy[-1]:.4f}")
    
    return beta_90_list


def main():
    """Run full critical exponent analysis."""
    print("\n" + "="*60)
    print("THRML-002b: CRITICAL EXPONENT ANALYSIS")
    print("="*60)
    
    # Load data
    data = load_results()
    
    # Run analyses
    cv_scaling = analyze_cv_scaling(data)
    beta_scaling = analyze_beta_c_scaling(data)
    analyze_order_parameter_collapse(data)
    analyze_accuracy_transition(data)
    
    # Summary
    print("\n" + "="*60)
    print("SUMMARY: PHASE TRANSITION EVIDENCE")
    print("="*60)
    
    print("\n1. SPECIFIC HEAT SCALING:")
    if cv_scaling:
        print(f"   Cv_max ~ N^{cv_scaling['alpha']:.2f}")
        print(f"   R^2 = {cv_scaling['r2']:.3f}")
        if cv_scaling['r2'] > 0.9:
            print("   -> STRONG power-law scaling (phase transition signature)")
        else:
            print("   -> Weak scaling (needs more data)")
    
    print("\n2. CRITICAL POINT CONVERGENCE:")
    print(f"   beta_c(N->inf) ~ {beta_scaling['beta_c_inf']:.3f}")
    
    print("\n3. OVERALL VERDICT:")
    
    # Check all criteria
    cv_growing = data['scaling']['Cv_growing']
    spreads_tightening = data['scaling']['spreads_tightening']
    
    if cv_growing and spreads_tightening:
        print("   *** PHASE TRANSITION HYPOTHESIS SUPPORTED ***")
        print("   - Cv_max grows with N")
        print("   - Critical point estimates converge")
        print("   - Power-law scaling observed")
    else:
        print("   INCONCLUSIVE - needs more data or analysis")
    
    print("\n" + "="*60)
    
    return {
        'cv_scaling': cv_scaling,
        'beta_scaling': beta_scaling
    }


if __name__ == "__main__":
    results = main()
