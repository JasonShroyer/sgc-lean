#!/usr/bin/env python3
"""
PERIHELION Sprint 3 - Fix A: Damped Pendulum Amplitude Ratio Test

The CORRECT observable for damped pendulum phase transition:
- Extract local maxima of |θ(t)| (amplitude of each swing)
- Compute ratio amplitude[n] / amplitude[n-1]
- Early: ratios vary (transient behavior, disordered phase)
- Late: ratios converge to exp(-b*T) (exponential decay, ordered phase)

Uses entity-resolved accumulation:
- Nodes = value-bins (ratio values)
- Edges accumulate across all swings
- Trans_rate measured on entity-resolved graph

Prediction: This relation transitions from disordered to ordered as the
exponential decay pattern establishes. T* should follow finite-size scaling.
"""

import numpy as np
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from core.entity_resolved_triplets import (
    AmplitudeRatioExtractor,
    create_entity_resolved_corpus,
    EntityResolvedCorpus
)
from core.sgc_engine import SGCEngine


class DampedPendulumSimulator:
    """Simulate damped pendulum for amplitude extraction."""
    
    def __init__(self, mass: float = 1.0, length: float = 1.0, g: float = 9.81):
        self.mass = mass
        self.length = length
        self.g = g
        self.omega0 = np.sqrt(g / length)  # Natural frequency
    
    def simulate(
        self,
        theta0: float,
        omega0: float,
        damping: float,
        dt: float,
        n_steps: int
    ) -> tuple:
        """
        Simulate damped pendulum using RK4.
        
        Returns:
            (time, theta, omega) arrays
        """
        t = np.zeros(n_steps)
        theta = np.zeros(n_steps)
        omega = np.zeros(n_steps)
        
        theta[0] = theta0
        omega[0] = omega0
        
        def derivatives(th, om):
            dtheta = om
            domega = -self.omega0**2 * np.sin(th) - 2 * damping * om
            return dtheta, domega
        
        for i in range(n_steps - 1):
            th, om = theta[i], omega[i]
            
            # RK4
            k1_th, k1_om = derivatives(th, om)
            k2_th, k2_om = derivatives(th + 0.5*dt*k1_th, om + 0.5*dt*k1_om)
            k3_th, k3_om = derivatives(th + 0.5*dt*k2_th, om + 0.5*dt*k2_om)
            k4_th, k4_om = derivatives(th + dt*k3_th, om + dt*k3_om)
            
            theta[i+1] = th + (dt/6) * (k1_th + 2*k2_th + 2*k3_th + k4_th)
            omega[i+1] = om + (dt/6) * (k1_om + 2*k2_om + 2*k3_om + k4_om)
            t[i+1] = t[i] + dt
        
        return t, theta, omega


def run_amplitude_ratio_test(
    damping: float = 0.1,
    theta0: float = 1.0,
    n_steps: int = 5000,
    dt: float = 0.01,
    n_bins: int = 10,
    k_sustained: int = 3
):
    """
    Run amplitude ratio grokking test with entity-resolved accumulation.
    
    Args:
        damping: Damping coefficient
        theta0: Initial angle (radians)
        n_steps: Simulation timesteps
        dt: Time step
        n_bins: Bins for ratio discretization
        tolerance_factor: Tolerance = factor * bin_width
        k_sustained: Required consecutive windows above threshold
    """
    print("=" * 70)
    print("  PERIHELION Sprint 3 - Amplitude Ratio Grokking Test")
    print("  Entity-Resolved Accumulation")
    print("=" * 70)
    
    # Simulate pendulum
    print(f"\n[1] Simulating damped pendulum...")
    sim = DampedPendulumSimulator()
    t, theta, omega = sim.simulate(theta0, 0.0, damping, dt, n_steps)
    
    print(f"  Damping coefficient b = {damping}")
    print(f"  Initial angle = {theta0:.2f} rad")
    print(f"  Simulation time = {t[-1]:.1f} s")
    print(f"  Natural period T0 = {2*np.pi/sim.omega0:.3f} s")
    
    # Theoretical decay rate per period
    T0 = 2 * np.pi / sim.omega0
    theoretical_ratio = np.exp(-damping * T0)
    print(f"  Theoretical amplitude ratio = exp(-b*T0) = {theoretical_ratio:.4f}")
    
    # Extract amplitudes
    print(f"\n[2] Extracting swing amplitudes...")
    extractor = AmplitudeRatioExtractor(min_peak_distance=int(T0 / dt / 2))
    amplitudes, ratios = extractor.extract_from_trajectory(theta)
    
    print(f"  Detected {len(amplitudes)} amplitude peaks")
    print(f"  Computed {len(ratios)} amplitude ratios")
    
    if len(ratios) < 5:
        print("  ERROR: Not enough swings detected")
        return None
    
    print(f"  Ratio range: [{ratios.min():.4f}, {ratios.max():.4f}]")
    print(f"  Early ratios (first 5): {ratios[:5]}")
    print(f"  Late ratios (last 5): {ratios[-5:]}")
    
    # Streaming entity-resolved measurement
    print(f"\n[3] Streaming entity-resolved SGC measurement...")
    
    PERCOLATION_THRESHOLD = 0.83
    trans_rate_history = []
    grokking_swing = None
    consecutive_above = 0
    
    # Process ratios in batches (accumulating)
    batch_size = 3  # Add 3 ratios at a time
    
    for batch_end in range(batch_size, len(ratios) + 1, batch_size):
        # Create entity-resolved corpus from ratios seen so far
        ratios_so_far = ratios[:batch_end]
        corpus = create_entity_resolved_corpus(
            ratios_so_far,
            n_bins=n_bins,
            relation="AMPLITUDE_RATIO"
        )
        
        # Get triplets and measure with SGC
        triplets = corpus.get_triplets_for_sgc()
        
        if len(triplets) < 3:
            continue
        
        sgc = SGCEngine(min_chains=5)
        for s, r, o in triplets:
            sgc.add_triplet(s, r, o)
        
        measurements = sgc.measure_all_relations()
        
        if "AMPLITUDE_RATIO" in measurements:
            m = measurements["AMPLITUDE_RATIO"]
            
            stats = corpus.get_graph_stats()
            trans_rate_history.append({
                'swing': batch_end,
                'trans_rate': m.trans_rate,
                'delta': m.delta,
                'phase': m.phase,
                'n_entities': stats['n_entities'],
                'n_edges': stats['n_edges'],
                'chains': m.n_chains_tested
            })
            
            # Check sustained threshold (Fix B)
            if m.trans_rate >= PERCOLATION_THRESHOLD:
                consecutive_above += 1
                if consecutive_above >= k_sustained and grokking_swing is None:
                    grokking_swing = batch_end
                    print(f"  ** GROKKING at swing {batch_end} (sustained {k_sustained} windows)")
                    print(f"     trans_rate = {m.trans_rate:.4f}")
                    print(f"     delta = {m.delta:.4f}")
            else:
                consecutive_above = 0
    
    # Print trajectory
    print(f"\n[4] Trans_rate trajectory:")
    print(f"  {'swing':>6}  {'trans':>6}  {'delta':>6}  {'ent':>4}  {'edg':>4}  {'graph'}")
    print(f"  {'-'*6}  {'-'*6}  {'-'*6}  {'-'*4}  {'-'*4}  {'-'*25}")
    
    for entry in trans_rate_history[::max(1, len(trans_rate_history)//12)]:
        bar = "#" * int(entry['trans_rate'] * 25)
        marker = " <-- T*" if entry['swing'] == grokking_swing else ""
        print(f"  {entry['swing']:6d}  {entry['trans_rate']:.4f}  {entry['delta']:.4f}  "
              f"{entry['n_entities']:4d}  {entry['n_edges']:4d}  {bar}{marker}")
    
    # Analysis
    print(f"\n[5] Analysis...")
    print(f"  Total swings: {len(ratios)}")
    print(f"  Theoretical ratio (exponential decay): {theoretical_ratio:.4f}")
    
    if grokking_swing is not None:
        # Compute actual ratio std at grokking point
        ratios_at_grok = ratios[:grokking_swing]
        ratio_std = np.std(ratios_at_grok[-10:]) if len(ratios_at_grok) >= 10 else np.std(ratios_at_grok)
        print(f"  Grokking at swing: {grokking_swing}")
        print(f"  Ratio std at grokking: {ratio_std:.6f}")
        print(f"  [PASS]: Phase transition detected")
    else:
        print(f"  Grokking: NOT DETECTED")
        if trans_rate_history:
            final = trans_rate_history[-1]
            print(f"  Final trans_rate: {final['trans_rate']:.4f}")
            print(f"  Final delta: {final['delta']:.4f}")
        print(f"  [FAIL]: No phase transition detected")
    
    # Final state
    if trans_rate_history:
        final = trans_rate_history[-1]
        print(f"\n[6] Final state:")
        print(f"  trans_rate = {final['trans_rate']:.4f}")
        print(f"  delta = {final['delta']:.4f}")
        print(f"  phase = {final['phase']}")
        print(f"  entities = {final['n_entities']}")
        print(f"  edges = {final['n_edges']}")
    
    print("\n" + "=" * 70)
    
    return {
        'damping': damping,
        'theoretical_ratio': theoretical_ratio,
        'n_swings': len(ratios),
        'grokking_swing': grokking_swing,
        'trans_rate_history': trans_rate_history,
        'ratios': ratios
    }


if __name__ == "__main__":
    # Test with different damping values
    print("\n*** Test 1: Light damping (b=0.05) ***")
    result1 = run_amplitude_ratio_test(damping=0.05, n_steps=10000)
    
    print("\n*** Test 2: Moderate damping (b=0.1) ***")
    result2 = run_amplitude_ratio_test(damping=0.1, n_steps=8000)
    
    print("\n*** Test 3: Heavy damping (b=0.2) ***")
    result3 = run_amplitude_ratio_test(damping=0.2, n_steps=5000)
    
    # Summary
    print("\n" + "=" * 70)
    print("  SUMMARY")
    print("=" * 70)
    for i, r in enumerate([result1, result2, result3], 1):
        if r is None:
            print(f"  Test {i}: FAILED (not enough swings)")
            continue
        status = "PASS" if r['grokking_swing'] else "FAIL"
        grok = r['grokking_swing'] if r['grokking_swing'] else "N/A"
        print(f"  Test {i}: damping={r['damping']}, swings={r['n_swings']}, "
              f"T*={grok}, [{status}]")
