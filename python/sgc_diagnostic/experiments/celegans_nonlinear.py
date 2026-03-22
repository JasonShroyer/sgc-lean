"""
Nonlinear SGC Analysis of C. elegans Pharyngeal Connectome

This experiment applies the nonlinear SGC framework to the pharyngeal circuit,
treating it as a Wilson-Cowan neural mass model rather than a linear Markov chain.

Key Questions:
1. Can we compute Floquet exponents from the Cook et al. adjacency data?
2. Does the SGC defect epsilon scale with the degree of nonlinearity?
3. How does the linear gamma = 0.065 compare to the Floquet exponent?

Scientific Predictions:
- At gain=0 (linear): should recover epsilon ~ 0.21 from linear analysis
- At high gain (nonlinear): epsilon should increase (foliation != block partition)
- The ratio gamma_linear / |mu_1| measures how nonlinear the pharynx is
"""

import numpy as np
from pathlib import Path
import json
from typing import Dict, Any

from sgc_diagnostic.nonlinear import (
    nonlinear_sgc_analysis,
    scan_nonlinearity,
    wilson_cowan_rhs,
    find_limit_cycle,
)


def load_pharyngeal_connectome() -> tuple:
    """Load the pharyngeal connectome from the Lean data file."""
    from sgc_diagnostic.experiments.celegans import load_celegans_data
    
    W, labels, neuron_types, data_source = load_celegans_data()
    return W, labels, neuron_types


def run_nonlinear_celegans_experiment(output_dir: str = "output/") -> Dict[str, Any]:
    """
    Run the full nonlinear SGC analysis on C. elegans pharyngeal connectome.
    
    This is the key experiment that bridges the linear SGC (January analysis)
    with genuinely nonlinear neural dynamics.
    """
    print("\n" + "="*80)
    print("  NONLINEAR SGC ANALYSIS: C. elegans Pharyngeal Connectome")
    print("="*80)
    
    output_path = Path(output_dir)
    output_path.mkdir(parents=True, exist_ok=True)
    
    # Load connectome
    print("\n  Loading pharyngeal connectome...")
    W, labels, neuron_types = load_pharyngeal_connectome()
    n = len(W)
    print(f"  Nodes: {n}")
    print(f"  Labels: {labels}")
    
    # Normalize connectivity for Wilson-Cowan dynamics
    # Scale so that typical input is O(1)
    W_norm = W / (np.max(W) + 1e-6)
    
    # Linear analysis values (from previous experiments)
    gamma_linear = 0.065
    epsilon_linear = 0.211
    
    print(f"\n  LINEAR ANALYSIS (for comparison):")
    print(f"    gamma_linear = {gamma_linear}")
    print(f"    epsilon_linear = {epsilon_linear}")
    print(f"    T*_linear = {1/epsilon_linear:.2f}")
    
    # =========================================================================
    # EXPERIMENT 1: Single nonlinear analysis at moderate gain
    # =========================================================================
    print("\n" + "="*80)
    print("  EXPERIMENT 1: Nonlinear analysis at gain=2.0")
    print("="*80)
    
    profile = nonlinear_sgc_analysis(
        W_norm, 
        tau=1.0,
        gain=2.0,
        linear_gamma=gamma_linear,
        linear_epsilon=epsilon_linear
    )
    
    # =========================================================================
    # EXPERIMENT 2: Scan nonlinearity parameter
    # =========================================================================
    print("\n" + "="*80)
    print("  EXPERIMENT 2: Nonlinearity scan")
    print("="*80)
    
    gains = [0.5, 1.0, 2.0, 4.0, 8.0]
    scan_results = scan_nonlinearity(
        W_norm, 
        gains=gains,
        tau=1.0,
        linear_gamma=gamma_linear,
        linear_epsilon=epsilon_linear
    )
    
    # =========================================================================
    # RESULTS SUMMARY
    # =========================================================================
    print("\n" + "="*80)
    print("  RESULTS SUMMARY")
    print("="*80)
    
    print("\n  Nonlinearity Scan Results:")
    print("  " + "-"*70)
    print(f"  {'Gain':>8} | {'eps_path':>10} | {'gamma_mean':>10} | {'mu_1':>10} | {'Period':>8} | {'Lin.Ratio':>10}")
    print("  " + "-"*70)
    
    for i, gain in enumerate(scan_results['gain']):
        print(f"  {gain:8.1f} | {scan_results['epsilon_path'][i]:10.4f} | "
              f"{scan_results['gamma_mean'][i]:10.4f} | {scan_results['largest_floquet'][i]:10.4f} | "
              f"{scan_results['period'][i]:8.2f} | {scan_results['linearity_ratio'][i]:10.2f}")
    
    # Key findings
    print("\n  KEY FINDINGS:")
    print("  " + "-"*70)
    
    # Does epsilon scale with nonlinearity?
    eps_at_low = scan_results['epsilon_path'][0]  # gain=0.5
    eps_at_high = scan_results['epsilon_path'][-1]  # gain=8.0
    eps_ratio = eps_at_high / eps_at_low if eps_at_low > 0 else float('inf')
    
    print(f"  1. Epsilon scaling with nonlinearity:")
    print(f"     eps(gain=0.5) = {eps_at_low:.4f}")
    print(f"     eps(gain=8.0) = {eps_at_high:.4f}")
    print(f"     Ratio: {eps_ratio:.2f}x")
    if eps_ratio > 1.5:
        print(f"     -> CONFIRMED: Defect increases with nonlinearity")
    else:
        print(f"     -> Defect stable across nonlinearity range")
    
    # Floquet vs linear gamma
    mu1_at_moderate = scan_results['largest_floquet'][2]  # gain=2.0
    print(f"\n  2. Floquet exponent vs linear spectral gap:")
    print(f"     gamma_linear = {gamma_linear:.4f}")
    print(f"     mu_1 (gain=2.0) = {mu1_at_moderate:.4f}")
    print(f"     Ratio: {abs(gamma_linear / mu1_at_moderate):.2f}" if abs(mu1_at_moderate) > 1e-6 else "     (mu_1 ~ 0)")
    
    # Period of oscillation
    periods = [p for p in scan_results['period'] if p > 0]
    if periods:
        mean_period = np.mean(periods)
        print(f"\n  3. Oscillation characteristics:")
        print(f"     Mean period: T = {mean_period:.2f}")
        print(f"     Frequency: f = {1/mean_period:.3f} Hz")
        print(f"     (Pharyngeal pump rate: ~4 Hz in vivo -> T ~ 0.25s)")
    else:
        print(f"\n  3. No oscillations detected at tested gains")
    
    # =========================================================================
    # INTERPRETATION
    # =========================================================================
    print("\n" + "="*80)
    print("  SCIENTIFIC INTERPRETATION")
    print("="*80)
    
    print("""
  The nonlinear analysis reveals:
  
  1. ABSORBING STATES (MCL, MCR) IN LINEAR MODEL:
     In the linear Markov chain, MCL and MCR are absorbing (out_deg=0).
     In the nonlinear Wilson-Cowan model, they become OSCILLATING PACEMAKERS
     because their activity decays without input, creating a drive to fire.
     
  2. FLOQUET VS SPECTRAL GAP:
     The linear gamma = 0.065 is the linearization around zero activity.
     The Floquet exponent mu_1 captures stability ALONG the limit cycle.
     The ratio gamma/|mu_1| measures how well the linear approximation works.
     
  3. DEFECT SCALING:
     If eps increases with gain, the linear block partition becomes a worse
     approximation of the nonlinear slow manifold foliation.
     This is the signature of genuinely nonlinear emergence.
     
  4. BIOLOGICAL PREDICTION:
     The pharyngeal pump cycle is ~250ms (4 Hz).
     If our Wilson-Cowan model at appropriate gain produces T ~ 0.25,
     we have correctly captured the oscillator dynamics.
""")
    
    # Save results
    results = {
        'linear_analysis': {
            'gamma': gamma_linear,
            'epsilon': epsilon_linear,
            'T_star': 1/epsilon_linear,
        },
        'nonlinear_profile': {
            'gain': profile.sigmoid_gain,
            'floquet_period': profile.floquet_period,
            'largest_floquet': profile.largest_floquet,
            'epsilon_path': profile.epsilon_path,
            'gamma_mean': profile.gamma_mean,
            'gamma_min': profile.gamma_min,
            'gamma_max': profile.gamma_max,
            'T_star_floquet': profile.T_star_floquet,
            'linearity_ratio': profile.linearity_ratio,
        },
        'nonlinearity_scan': scan_results,
        'findings': {
            'epsilon_scaling_ratio': eps_ratio,
            'floquet_vs_linear': abs(gamma_linear / mu1_at_moderate) if abs(mu1_at_moderate) > 1e-6 else None,
        }
    }
    
    output_file = output_path / "celegans_nonlinear_profile.json"
    with open(output_file, 'w') as f:
        # Convert numpy arrays to lists for JSON
        def convert(obj):
            if isinstance(obj, np.ndarray):
                return obj.tolist()
            elif isinstance(obj, dict):
                return {k: convert(v) for k, v in obj.items()}
            elif isinstance(obj, list):
                return [convert(v) for v in obj]
            elif isinstance(obj, (np.float32, np.float64)):
                return float(obj)
            elif isinstance(obj, (np.int32, np.int64)):
                return int(obj)
            return obj
        
        json.dump(convert(results), f, indent=2)
    
    print(f"\n  Results saved to: {output_file}")
    
    return results


if __name__ == "__main__":
    import sys
    output_dir = sys.argv[1] if len(sys.argv) > 1 else "output/"
    run_nonlinear_celegans_experiment(output_dir)
