#!/usr/bin/env python3
"""
PERIHELION Sprint 2 - Controlled Grokking Test

Design a synthetic system with KNOWN transition point T*.
Before T*: random data (trans_rate ~ 0.5, disordered)
After T*: structured data (trans_rate → 1.0, ordered)

This directly tests the SGC phase transition detection without
physical simulation complexities.

The test:
1. Generate data that transitions from random to structured at T*_true
2. Stream through SGC engine
3. Measure T*_observed when trans_rate crosses 0.83
4. Compare T*_observed to T*_true

This validates whether the architecture can detect phase transitions
when we KNOW the ground truth.
"""

import numpy as np
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from core.triplet_extractor import Triplet, TripletCorpus
from core.sgc_engine import SGCEngine


def generate_transitioning_data(
    n_samples: int = 500,
    t_star_true: int = 200,
    transition_width: int = 50,
    value_range: float = 10.0,
    seed: int = 42
) -> tuple:
    """
    Generate CONTINUOUS synthetic data that transitions from random to clustered.
    
    Before T*: Values spread uniformly over [0, value_range] (low transitivity)
    After T*: Values cluster tightly around a central value (high transitivity)
    Transition: Smooth reduction in variance
    
    Key insight: We use APPROXIMATE EQUALITY (|a-b| < tolerance) as the relation.
    This is NOT inherently transitive:
    - a ≈ b and b ≈ c does NOT imply a ≈ c
    - But when values cluster, transitivity emerges
    
    Args:
        n_samples: Total number of samples
        t_star_true: True transition timestep
        transition_width: Width of transition region
        value_range: Initial range of random values
        seed: Random seed
        
    Returns:
        (values, cluster_std) where cluster_std is the effective std at each t
    """
    np.random.seed(seed)
    
    # Variance reduction: high before T*, low after T*
    t = np.arange(n_samples)
    # Sigmoid transition in log-variance
    log_var_high = np.log(value_range / 4)  # High variance = spread over range
    log_var_low = np.log(0.1)  # Low variance = tight cluster
    
    transition_factor = 1 / (1 + np.exp(-(t - t_star_true) / (transition_width / 4)))
    log_var = log_var_high * (1 - transition_factor) + log_var_low * transition_factor
    cluster_std = np.exp(log_var / 2)
    
    # Generate values: Gaussian centered at value_range/2 with time-varying std
    center = value_range / 2
    values = center + cluster_std * np.random.randn(n_samples)
    
    return values, cluster_std


def extract_approximate_equality_triplets(
    values: np.ndarray,
    window_start: int,
    window_end: int,
    tolerance: float = 1.0
) -> TripletCorpus:
    """
    Extract triplets based on APPROXIMATE equality (|a-b| < tolerance).
    
    KEY INSIGHT: Approximate equality is NOT inherently transitive!
    - a ≈ b means |a-b| < tolerance
    - a ≈ b and b ≈ c does NOT imply a ≈ c
    - Example: a=0, b=0.9*tol, c=1.8*tol → a≈b, b≈c, but NOT a≈c
    
    For spread data: chains often fail (trans_rate < 1)
    For clustered data: all values within tolerance (trans_rate → 1)
    
    This creates a genuine phase transition in transitivity!
    """
    corpus = TripletCorpus()
    
    window_values = values[window_start:window_end]
    n = len(window_values)
    
    if n < 2:
        return corpus
    
    # Create edges between approximately equal values
    for i in range(n):
        for j in range(i + 1, n):
            if abs(window_values[i] - window_values[j]) < tolerance:
                corpus.add(Triplet(
                    subject=f"t_{window_start + i}",
                    relation="APPROX_EQUAL",
                    obj=f"t_{window_start + j}",
                    subject_value=float(window_values[i]),
                    object_value=float(window_values[j]),
                    timestep=window_start + i
                ))
    
    return corpus


def run_synthetic_grokking_test(
    n_samples: int = 500,
    t_star_true: int = 200,
    transition_width: int = 50,
    value_range: float = 10.0,
    tolerance: float = 1.0,
    window_size: int = 30,
    step_size: int = 10,
    k_sustained: int = 3,
    seed: int = 42
):
    """
    Run controlled grokking test on synthetic data.
    
    Uses APPROXIMATE EQUALITY which is NOT inherently transitive.
    As data clusters, transitivity emerges → phase transition.
    
    Args:
        n_samples: Total samples
        t_star_true: True transition point
        transition_width: Width of transition
        value_range: Range of values
        tolerance: Tolerance for approximate equality
        window_size: Lookback window for measurement
        step_size: Measurement interval
        seed: Random seed
    """
    print("=" * 70)
    print("  PERIHELION Sprint 2 - Controlled Grokking Test")
    print("  Approximate Equality Phase Transition")
    print("=" * 70)
    
    # Generate data with known transition
    print(f"\n[1] Generating synthetic data...")
    values, cluster_std = generate_transitioning_data(
        n_samples=n_samples,
        t_star_true=t_star_true,
        transition_width=transition_width,
        value_range=value_range,
        seed=seed
    )
    
    print(f"  Total samples: {n_samples}")
    print(f"  True T* (transition): {t_star_true}")
    print(f"  Transition width: {transition_width}")
    print(f"  Value range: {value_range}")
    print(f"  Tolerance (epsilon): {tolerance}")
    print(f"  Std at t=0: {cluster_std[0]:.3f}")
    print(f"  Std at T*: {cluster_std[t_star_true]:.3f}")
    print(f"  Std at end: {cluster_std[-1]:.3f}")
    
    # Streaming measurement - FRESH SGC engine per window
    # This measures transitivity WITHIN each window, giving a time series
    print(f"\n[2] Streaming SGC measurement (per-window)...")
    print(f"  Sustained threshold: k={k_sustained} consecutive windows above 0.83")
    
    PERCOLATION_THRESHOLD = 0.83
    trans_rate_history = []
    grokking_timestep = None
    consecutive_above = 0  # Track consecutive windows above threshold
    
    for t in range(window_size, n_samples, step_size):
        # FRESH SGC engine for each window - measure transitivity within window only
        sgc = SGCEngine(min_chains=5)
        
        # Extract triplets for current window using APPROXIMATE equality
        corpus = extract_approximate_equality_triplets(
            values, t - window_size, t, tolerance=tolerance
        )
        
        # Add to SGC engine
        for relation in corpus.relations():
            for triplet in corpus.get_relation(relation):
                sgc.add_triplet(triplet.subject, triplet.relation, triplet.obj)
        
        # Measure trans_rate for THIS window
        measurements = sgc.measure_all_relations()
        
        if "APPROX_EQUAL" in measurements:
            m = measurements["APPROX_EQUAL"]
            trans_rate_history.append({
                'timestep': t,
                'trans_rate': m.trans_rate,
                'delta': m.delta,
                'phase': m.phase,
                'chains': m.n_chains_tested,
                'cluster_std': cluster_std[t]
            })
            
            # Check for sustained grokking (Fix B)
            if m.trans_rate >= PERCOLATION_THRESHOLD:
                consecutive_above += 1
                if grokking_timestep is None and consecutive_above >= k_sustained:
                    grokking_timestep = t
                    print(f"  ** GROKKING at timestep {t} (sustained {k_sustained} windows)")
                    print(f"     trans_rate = {m.trans_rate:.4f}")
                    print(f"     delta = {m.delta:.4f}")
                    print(f"     cluster_std = {cluster_std[t]:.3f}")
            else:
                consecutive_above = 0  # Reset counter
    
    # Print trajectory
    print(f"\n[3] Trans_rate trajectory:")
    print(f"  {'t':>5}  {'trans':>6}  {'std':>6}  {'graph'}")
    print(f"  {'-'*5}  {'-'*6}  {'-'*6}  {'-'*30}")
    
    for entry in trans_rate_history[::max(1, len(trans_rate_history)//15)]:
        bar = "#" * int(entry['trans_rate'] * 30)
        marker = " <-- T*_obs" if entry['timestep'] == grokking_timestep else ""
        t_star_marker = " <-- T*_true" if abs(entry['timestep'] - t_star_true) < step_size else ""
        print(f"  {entry['timestep']:5d}  {entry['trans_rate']:.4f}  {entry['cluster_std']:.4f}  {bar}{marker}{t_star_marker}")
    
    # Analysis
    print(f"\n[4] Grokking analysis...")
    print(f"  True T* (transition point): {t_star_true}")
    
    if grokking_timestep is not None:
        error = abs(grokking_timestep - t_star_true)
        error_pct = error / t_star_true * 100
        print(f"  Observed T*: {grokking_timestep}")
        print(f"  Absolute error: {error} timesteps")
        print(f"  Relative error: {error_pct:.1f}%")
        
        passed = error_pct < 30  # 30% error threshold
        status = "[PASS]" if passed else "[FAIL]"
        print(f"\n  {status}: T* detection error < 30%")
    else:
        print(f"  Observed T*: NOT DETECTED")
        print(f"  Grokking did not occur")
        passed = False
    
    # Final state
    if trans_rate_history:
        final = trans_rate_history[-1]
        print(f"\n[5] Final state:")
        print(f"  trans_rate = {final['trans_rate']:.4f}")
        print(f"  delta = {final['delta']:.4f}")
        print(f"  phase = {final['phase']}")
        print(f"  chains tested = {final['chains']}")
    
    print("\n" + "=" * 70)
    
    return {
        't_star_true': t_star_true,
        't_star_observed': grokking_timestep,
        'trans_rate_history': trans_rate_history,
        'passed': passed
    }


if __name__ == "__main__":
    # Fix B: Find optimal k for sustained threshold criterion
    print("\n" + "=" * 70)
    print("  Fix B: Finding optimal k for sustained threshold")
    print("=" * 70)
    
    # Test all k values
    results_by_k = {}
    
    for k in [1, 2, 3, 4]:
        print(f"\n{'='*70}")
        print(f"  Testing k_sustained = {k}")
        print(f"{'='*70}")
        
        results = []
        for test_num, (t_star, width) in enumerate([(200, 30), (200, 100), (350, 50)], 1):
            result = run_synthetic_grokking_test(
                n_samples=500,
                t_star_true=t_star,
                transition_width=width,
                value_range=10.0,
                tolerance=0.5,
                k_sustained=k,
                seed=42
            )
            results.append(result)
        
        results_by_k[k] = results
    
    # Summary table
    print("\n" + "=" * 70)
    print("  FIX B SUMMARY: Optimal k analysis")
    print("=" * 70)
    print(f"  {'k':>3}  {'Test1 (T*=200)':>18}  {'Test2 (T*=200)':>18}  {'Test3 (T*=350)':>18}")
    print(f"  {'-'*3}  {'-'*18}  {'-'*18}  {'-'*18}")
    
    for k, results in results_by_k.items():
        row = [f"  {k:>3}"]
        for r in results:
            if r['t_star_observed']:
                err = abs(r['t_star_observed'] - r['t_star_true']) / r['t_star_true'] * 100
                row.append(f"{r['t_star_observed']:>4} ({err:>5.1f}%)")
            else:
                row.append("  N/A")
        print("  ".join(row))
    
    print(f"\n  Target: Eliminate Test 3 spurious detection (was t=190 with k=1)")
    print(f"  While minimizing detection delay for Test 1 and Test 2")
