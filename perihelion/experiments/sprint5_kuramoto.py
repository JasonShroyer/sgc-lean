#!/usr/bin/env python3
"""
PERIHELION Sprint 5 — Kuramoto Phase Transition Test

First genuine physical phase transition test with pre-registered predictions.

System: Kuramoto oscillators
Relation: FREQUENCY_ENTRAINMENT (time-averaged frequency convergence)

Pre-registered predictions (from SPRINT5_PREDICTIONS.md):
  K=0.5: delta = 0.45 +/- 0.10 (disordered)
  K=2.0: delta = 0.20 +/- 0.10 (critical), T* = 220 steps
  K=5.0: delta = 0.05 +/- 0.05 (ordered)
"""

import numpy as np
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from core.sgc_engine import SGCEngine


class KuramotoModel:
    """
    Kuramoto model of coupled oscillators.
    
    d(theta_i)/dt = omega_i + (K/N) * sum_j sin(theta_j - theta_i)
    
    Parameters:
        N: Number of oscillators
        K: Coupling strength
        omega: Natural frequencies (drawn from N(0,1))
    """
    
    def __init__(self, N: int, K: float, seed: int = 42):
        self.N = N
        self.K = K
        np.random.seed(seed)
        self.omega = np.random.randn(N)  # Natural frequencies ~ N(0,1)
        self.theta = np.random.uniform(0, 2*np.pi, N)  # Initial phases
        self.t = 0
        
        # K_critical for N(0,1) distribution: 2/(pi * g(0)) where g(0) = 1/sqrt(2*pi)
        self.K_critical = np.sqrt(2 * np.pi) / np.pi  # ≈ 1.596
    
    def step(self, dt: float = 0.1):
        """Euler step for Kuramoto dynamics."""
        # Compute coupling term
        sin_diff = np.sin(self.theta[:, None] - self.theta[None, :])
        coupling = (self.K / self.N) * np.sum(sin_diff, axis=1)
        
        # Update phases
        d_theta = self.omega - coupling
        self.theta += dt * d_theta
        self.theta = np.mod(self.theta, 2 * np.pi)
        self.t += dt
        
        return d_theta  # Instantaneous frequencies
    
    def compute_order_parameter(self) -> complex:
        """Compute Kuramoto order parameter r*exp(i*psi)."""
        z = np.mean(np.exp(1j * self.theta))
        return z
    
    def simulate(self, n_steps: int, dt: float = 0.1) -> np.ndarray:
        """
        Simulate for n_steps, returning instantaneous frequencies at each step.
        
        Returns:
            frequencies: (n_steps, N) array of instantaneous frequencies
        """
        frequencies = np.zeros((n_steps, self.N))
        for i in range(n_steps):
            freq = self.step(dt)
            frequencies[i] = freq
        return frequencies


def compute_entrainment_triplets(
    frequencies: np.ndarray,
    window_size: int = 20,
    epsilon: float = 0.3
) -> list:
    """
    Extract FREQUENCY_ENTRAINMENT triplets.
    
    Oscillator i entrains to oscillator j if:
    |<omega_i>_T - <omega_j>_T| < epsilon
    
    where <omega>_T is time-averaged frequency over window.
    """
    n_steps, N = frequencies.shape
    
    if n_steps < window_size:
        return []
    
    # Compute time-averaged frequencies over recent window
    avg_freq = np.mean(frequencies[-window_size:], axis=0)
    
    # Find entrainment pairs
    triplets = []
    for i in range(N):
        for j in range(N):
            if i != j:
                if abs(avg_freq[i] - avg_freq[j]) < epsilon:
                    triplets.append((f"osc_{i}", "ENTRAINED", f"osc_{j}"))
    
    return triplets


def run_kuramoto_test(
    K: float,
    N: int = 50,
    n_steps: int = 500,
    window_size: int = 20,
    epsilon: float = 0.3,
    dt: float = 0.1,
    seed: int = 42,
    k_sustained: int = 2
):
    """
    Run Kuramoto test for a given coupling strength K.
    
    Returns measured delta and T* (if applicable).
    """
    print(f"\n{'='*60}")
    print(f"  Kuramoto Test: K = {K}")
    print(f"{'='*60}")
    
    # Initialize model
    model = KuramotoModel(N, K, seed)
    print(f"\n[1] Model parameters:")
    print(f"  N = {N} oscillators")
    print(f"  K = {K} (K_critical = {model.K_critical:.3f})")
    print(f"  K/K_c = {K/model.K_critical:.3f}")
    print(f"  Window size = {window_size}, epsilon = {epsilon}")
    
    # Simulate
    print(f"\n[2] Simulating {n_steps} steps...")
    frequencies = np.zeros((n_steps, N))
    order_params = []
    
    for i in range(n_steps):
        freq = model.step(dt)
        frequencies[i] = freq
        r = abs(model.compute_order_parameter())
        order_params.append(r)
    
    print(f"  Initial order parameter: {order_params[0]:.4f}")
    print(f"  Final order parameter: {order_params[-1]:.4f}")
    
    # Streaming measurement
    print(f"\n[3] Streaming SGC measurement...")
    
    GROKKING_THRESHOLD = 0.83
    trans_rate_history = []
    observed_t_star = None
    consecutive_above = 0
    
    step_size = 10
    
    for t in range(window_size, n_steps, step_size):
        # Extract triplets from frequencies up to time t
        triplets = compute_entrainment_triplets(
            frequencies[:t], 
            window_size=window_size, 
            epsilon=epsilon
        )
        
        if len(triplets) < 10:
            trans_rate_history.append({
                't': t, 
                'trans_rate': 0.0, 
                'n_triplets': len(triplets),
                'order_param': order_params[t-1]
            })
            continue
        
        # Measure with SGC
        sgc = SGCEngine(min_chains=20)
        for s, r, o in triplets:
            sgc.add_triplet(s, r, o)
        
        measurements = sgc.measure_all_relations()
        
        if "ENTRAINED" in measurements:
            m = measurements["ENTRAINED"]
            trans_rate_history.append({
                't': t,
                'trans_rate': m.trans_rate,
                'delta': m.delta,
                'phase': m.phase,
                'n_triplets': len(triplets),
                'order_param': order_params[t-1]
            })
            
            # Check for sustained grokking
            if m.trans_rate >= GROKKING_THRESHOLD:
                consecutive_above += 1
                if consecutive_above >= k_sustained and observed_t_star is None:
                    observed_t_star = t
            else:
                consecutive_above = 0
    
    # Print trajectory
    print(f"\n[4] Trans_rate trajectory:")
    print(f"  {'t':>5}  {'trans':>6}  {'delta':>6}  {'r':>6}  {'trips':>6}  {'graph'}")
    print(f"  {'-'*5}  {'-'*6}  {'-'*6}  {'-'*6}  {'-'*6}  {'-'*25}")
    
    for entry in trans_rate_history[::max(1, len(trans_rate_history)//12)]:
        if 'delta' in entry:
            bar = "#" * int(entry['trans_rate'] * 25)
            marker = " <-- T*" if entry['t'] == observed_t_star else ""
            print(f"  {entry['t']:5d}  {entry['trans_rate']:.4f}  {entry['delta']:.4f}  "
                  f"{entry['order_param']:.4f}  {entry['n_triplets']:6d}  {bar}{marker}")
    
    # Final measurement
    if trans_rate_history and 'delta' in trans_rate_history[-1]:
        final = trans_rate_history[-1]
        measured_delta = final['delta']
        measured_trans_rate = final['trans_rate']
        measured_phase = final['phase']
    else:
        measured_delta = 1.0
        measured_trans_rate = 0.0
        measured_phase = "disordered"
    
    print(f"\n[5] Final state:")
    print(f"  Measured delta = {measured_delta:.4f}")
    print(f"  Measured trans_rate = {measured_trans_rate:.4f}")
    print(f"  Measured phase = {measured_phase}")
    print(f"  Observed T* = {observed_t_star if observed_t_star else 'NOT DETECTED'}")
    
    return {
        'K': K,
        'measured_delta': measured_delta,
        'measured_trans_rate': measured_trans_rate,
        'measured_phase': measured_phase,
        'observed_t_star': observed_t_star,
        'final_order_param': order_params[-1],
        'trans_rate_history': trans_rate_history
    }


def validate_predictions(results: dict) -> dict:
    """
    Validate results against pre-registered predictions.
    """
    print("\n" + "=" * 70)
    print("  SPRINT 5 VALIDATION")
    print("=" * 70)
    
    # Pre-registered predictions
    predictions = {
        0.5: {'delta': 0.45, 'tolerance': 0.10, 'phase': 'disordered'},
        2.0: {'delta': 0.20, 'tolerance': 0.10, 'phase': 'critical', 't_star': 220},
        5.0: {'delta': 0.05, 'tolerance': 0.05, 'phase': 'ordered'}
    }
    
    validation = {}
    
    for K, pred in predictions.items():
        if K not in results:
            continue
            
        r = results[K]
        delta_error = abs(r['measured_delta'] - pred['delta'])
        delta_pass = delta_error <= pred['tolerance']
        
        print(f"\n  K = {K}:")
        print(f"    Predicted delta = {pred['delta']} +/- {pred['tolerance']}")
        print(f"    Measured delta = {r['measured_delta']:.4f}")
        print(f"    Error = {delta_error:.4f}")
        print(f"    Delta test: {'PASS' if delta_pass else 'FAIL'}")
        
        validation[K] = {'delta_pass': delta_pass, 'delta_error': delta_error}
        
        # T* validation for K=2.0
        if K == 2.0 and 't_star' in pred:
            t_star_pred = pred['t_star']
            t_star_obs = r['observed_t_star']
            
            if t_star_obs:
                t_star_error = abs(t_star_obs - t_star_pred) / t_star_pred
                t_star_pass = t_star_error <= 0.25
                print(f"    Predicted T* = {t_star_pred}")
                print(f"    Observed T* = {t_star_obs}")
                print(f"    T* error = {t_star_error*100:.1f}%")
                print(f"    T* test: {'PASS' if t_star_pass else 'FAIL'}")
                validation[K]['t_star_pass'] = t_star_pass
                validation[K]['t_star_error'] = t_star_error
            else:
                print(f"    T* not detected (predicted {t_star_pred})")
                validation[K]['t_star_pass'] = False
    
    # Delta ordering test
    print(f"\n  Delta ordering test:")
    if 0.5 in results and 2.0 in results and 5.0 in results:
        d05 = results[0.5]['measured_delta']
        d20 = results[2.0]['measured_delta']
        d50 = results[5.0]['measured_delta']
        
        order_1 = d05 > d20
        order_2 = d20 > d50
        ordering_pass = order_1 and order_2
        
        print(f"    delta(0.5) = {d05:.4f}")
        print(f"    delta(2.0) = {d20:.4f}")
        print(f"    delta(5.0) = {d50:.4f}")
        print(f"    delta(0.5) > delta(2.0)? {order_1}")
        print(f"    delta(2.0) > delta(5.0)? {order_2}")
        print(f"    Ordering test: {'PASS' if ordering_pass else 'FAIL'}")
        
        validation['ordering'] = ordering_pass
    
    return validation


if __name__ == "__main__":
    print("\n" + "=" * 70)
    print("  PERIHELION Sprint 5 — Kuramoto Phase Transition Test")
    print("  First genuine physical phase transition with pre-registered predictions")
    print("=" * 70)
    
    # Run tests for three K values
    # Using tighter epsilon=0.05 to avoid saturation at K>=2.0
    EPSILON = 0.05  # Tighter tolerance (was 0.3)
    
    results = {}
    
    for K in [0.5, 2.0, 5.0]:
        result = run_kuramoto_test(K, N=50, n_steps=500, epsilon=EPSILON, seed=42)
        results[K] = result
    
    # Validate against predictions
    validation = validate_predictions(results)
    
    # Overall summary
    print("\n" + "=" * 70)
    print("  SPRINT 5 SUMMARY")
    print("=" * 70)
    
    all_pass = True
    
    for K in [0.5, 2.0, 5.0]:
        if K in validation:
            v = validation[K]
            status = "PASS" if v['delta_pass'] else "FAIL"
            print(f"\n  K={K}: delta test {status} (error={v['delta_error']:.4f})")
            if not v['delta_pass']:
                all_pass = False
            
            if K == 2.0 and 't_star_pass' in v:
                t_status = "PASS" if v['t_star_pass'] else "FAIL"
                print(f"         T* test {t_status}")
                if not v['t_star_pass']:
                    all_pass = False
    
    if 'ordering' in validation:
        order_status = "PASS" if validation['ordering'] else "FAIL"
        print(f"\n  Delta ordering: {order_status}")
        if not validation['ordering']:
            all_pass = False
    
    print(f"\n  {'='*50}")
    print(f"  OVERALL: {'ALL TESTS PASS' if all_pass else 'SOME TESTS FAILED'}")
    print(f"  {'='*50}")
