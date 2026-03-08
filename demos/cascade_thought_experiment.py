#!/usr/bin/env python3
"""
Phase 5: Tracking the Cascading Thought Exhaust

This experiment tests the prediction from FRONTIER_PHYSICS_SYNTHESIS.md Section 1:
    "Multi-step reasoning manifests as a CASCADE of Lifshitz transitions,
     each opening a Yamabe neck connecting two crystallized rule domains."

PREDICTION: When the engine composes two rules (e.g., reflect + color_map),
we should observe:
    1. Multiple distinct Cv peaks at successively lower temperatures
    2. b1 increasing monotonically (each step adds cycles)
    3. Specific heat signature: Cv(t) shows separated peaks, not one blob

SETUP: Synthetic ARC puzzles requiring exactly 2 composed operations:
    Puzzle A: Reflect vertically + change color (2-step)
    Puzzle B: Translate + fill interior (2-step)
    Control:  Single reflection (1-step)

TELEMETRY: Per-iteration measurement of:
    - Cv = beta^2 * Var(E)  (specific heat from energy variance)
    - M_eff (accumulated exploration mass)
    - b1 (first Betti number)
    - T (temperature)
    - sigma (quench strength)
    - eps_func (functional defect)
"""

import os
import sys
import numpy as np
from typing import Dict, List, Any

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from spiking_sheaf_engine import SpikingSheafEngine


def make_single_color_swap():
    """
    1-step puzzle: Two objects swap colors. 
    3 stalks (red block, blue block, background).
    Single rule: color_map(2->3, 3->2).
    """
    inp = np.zeros((5, 5), dtype=np.float32)
    # Red block top-left
    inp[0, 0] = 2; inp[0, 1] = 2
    inp[1, 0] = 2; inp[1, 1] = 2
    # Blue block bottom-right
    inp[3, 3] = 3; inp[3, 4] = 3
    inp[4, 3] = 3; inp[4, 4] = 3

    # Output: colors swapped
    out = np.zeros((5, 5), dtype=np.float32)
    out[0, 0] = 3; out[0, 1] = 3
    out[1, 0] = 3; out[1, 1] = 3
    out[3, 3] = 2; out[3, 4] = 2
    out[4, 3] = 2; out[4, 4] = 2

    return inp, out, "color_swap_only"


def make_swap_and_move():
    """
    2-step puzzle: Two objects swap colors AND move toward each other.
    3 stalks. Requires: color_map + translation (composition).
    """
    inp = np.zeros((5, 5), dtype=np.float32)
    # Red block top-left
    inp[0, 0] = 2; inp[0, 1] = 2
    inp[1, 0] = 2; inp[1, 1] = 2
    # Blue block bottom-right
    inp[3, 3] = 3; inp[3, 4] = 3
    inp[4, 3] = 3; inp[4, 4] = 3

    # Output: colors swapped AND moved toward center
    out = np.zeros((5, 5), dtype=np.float32)
    out[1, 1] = 3; out[1, 2] = 3
    out[2, 1] = 3; out[2, 2] = 3
    out[2, 2] = 2; out[2, 3] = 2
    out[3, 2] = 2; out[3, 3] = 2

    return inp, out, "swap+move"


def make_three_object_chain():
    """
    2-step puzzle: Three colored objects, each takes the color of its neighbor.
    4 stalks (3 objects + background). Requires chained color propagation.
    """
    inp = np.zeros((5, 7), dtype=np.float32)
    # Red block left
    inp[1, 0] = 1; inp[1, 1] = 1
    inp[2, 0] = 1; inp[2, 1] = 1
    # Green block middle
    inp[1, 3] = 3; inp[1, 4] = 3
    inp[2, 3] = 3; inp[2, 4] = 3
    # Blue block right
    inp[1, 5] = 2; inp[1, 6] = 2
    inp[2, 5] = 2; inp[2, 6] = 2

    # Output: each takes color of right neighbor (chain propagation)
    # Red -> Green, Green -> Blue, Blue -> Red
    out = np.zeros((5, 7), dtype=np.float32)
    out[1, 0] = 3; out[1, 1] = 3
    out[2, 0] = 3; out[2, 1] = 3
    out[1, 3] = 2; out[1, 4] = 2
    out[2, 3] = 2; out[2, 4] = 2
    out[1, 5] = 1; out[1, 6] = 1
    out[2, 5] = 1; out[2, 6] = 1

    return inp, out, "three_object_chain"


def make_four_object_grid():
    """
    Control: 4 objects in a grid, simple independent color maps.
    5 stalks (4 objects + background). Single rule applied to each.
    """
    inp = np.zeros((6, 6), dtype=np.float32)
    # 4 colored blocks in corners
    inp[0, 0] = 1; inp[0, 1] = 1; inp[1, 0] = 1; inp[1, 1] = 1  # TL: blue
    inp[0, 4] = 2; inp[0, 5] = 2; inp[1, 4] = 2; inp[1, 5] = 2  # TR: red
    inp[4, 0] = 3; inp[4, 1] = 3; inp[5, 0] = 3; inp[5, 1] = 3  # BL: green
    inp[4, 4] = 4; inp[4, 5] = 4; inp[5, 4] = 4; inp[5, 5] = 4  # BR: yellow

    # Output: all become same color (convergence)
    out = np.zeros((6, 6), dtype=np.float32)
    out[0, 0] = 5; out[0, 1] = 5; out[1, 0] = 5; out[1, 1] = 5
    out[0, 4] = 5; out[0, 5] = 5; out[1, 4] = 5; out[1, 5] = 5
    out[4, 0] = 5; out[4, 1] = 5; out[5, 0] = 5; out[5, 1] = 5
    out[4, 4] = 5; out[4, 5] = 5; out[5, 4] = 5; out[5, 5] = 5

    return inp, out, "four_objects_converge"


def compute_specific_heat(energies: List[float], beta: float) -> float:
    """
    Compute specific heat from energy time series.
    Cv = beta^2 * Var(E) using a sliding window.
    """
    if len(energies) < 3:
        return 0.0
    window = energies[-min(5, len(energies)):]
    return beta ** 2 * np.var(window)


def run_instrumented_crystallization(inp, out, name, max_iter=80):
    """
    Run crystallization with full per-iteration telemetry.
    
    Returns the telemetry time series for cascade analysis.
    """
    engine = SpikingSheafEngine(
        input_grid=inp,
        target_grid=out,
        spike_threshold=0.75,
        learning_rate=0.15
    )
    
    stalks = engine.decompose_to_stalks(inp)
    n_stalks = len(stalks)
    
    if n_stalks < 2 or engine.N > 225:
        print(f"  [{name}] Skipped: {n_stalks} stalks, N={engine.N}")
        return None
    
    # Run crystallization and capture the result
    result = engine.crystallize_logical_laplacian(
        stalks, out,
        max_iterations=max_iter,
        initial_temperature=1.0,
        sparsity_lambda=0.1
    )
    
    # Extract telemetry
    telemetry = result.get('telemetry', {})
    accuracy_hist = telemetry.get('accuracy', [])
    defect_hist = telemetry.get('functional_defect', [])
    complexity_hist = telemetry.get('complexity', [])
    energy_hist = telemetry.get('hamiltonian_energy', [])
    b1_hist = telemetry.get('b1', [])
    temp_hist = telemetry.get('temperature', [])
    
    # Compute Cv from HAMILTONIAN energy variance (the correct thermodynamic observable)
    # Cv = beta^2 * Var(E) where beta = 1/T
    cv_hist = []
    for t in range(len(energy_hist)):
        window = energy_hist[max(0, t-4):t+1]
        T_current = temp_hist[t] if t < len(temp_hist) else 1.0
        beta = 1.0 / max(T_current, 0.001)
        cv = beta ** 2 * np.var(window) if len(window) > 1 else 0.0
        cv_hist.append(cv)
    
    print(f"\n  [{name}] Result: grokked={result['grokked']}, "
          f"b1={result.get('b1', '?')}, "
          f"accuracy={result['final_accuracy']:.1%}, "
          f"defect={result['functional_defect']:.3f}")
    print(f"  [{name}] Iterations: {len(accuracy_hist)}")
    
    return {
        'name': name,
        'grokked': result['grokked'],
        'b1': result.get('b1', 0),
        'accuracy': result['final_accuracy'],
        'defect': result['functional_defect'],
        'n_stalks': n_stalks,
        'accuracy_hist': accuracy_hist,
        'defect_hist': defect_hist,
        'complexity_hist': complexity_hist,
        'energy_hist': energy_hist,
        'cv_hist': cv_hist,
    }


def find_cv_peaks(cv_hist, min_prominence=0.001):
    """Find peaks in the specific heat time series."""
    peaks = []
    for i in range(1, len(cv_hist) - 1):
        if cv_hist[i] > cv_hist[i-1] and cv_hist[i] > cv_hist[i+1]:
            # Check prominence
            left_min = min(cv_hist[max(0, i-5):i])
            right_min = min(cv_hist[i+1:min(len(cv_hist), i+6)])
            prominence = cv_hist[i] - max(left_min, right_min)
            if prominence > min_prominence:
                peaks.append({
                    'iteration': i,
                    'cv_value': cv_hist[i],
                    'prominence': prominence
                })
    return peaks


def analyze_cascade(result):
    """Analyze the thermodynamic cascade signature."""
    if result is None:
        return
    
    name = result['name']
    cv_hist = result['cv_hist']
    energy_hist = result['energy_hist']
    defect_hist = result['defect_hist']
    
    peaks = find_cv_peaks(cv_hist)
    
    print(f"\n  --- CASCADE ANALYSIS: {name} ---")
    print(f"  Total iterations: {len(cv_hist)}")
    print(f"  Cv peaks found: {len(peaks)}")
    
    if peaks:
        for i, p in enumerate(peaks):
            print(f"    Peak {i+1}: iter={p['iteration']}, "
                  f"Cv={p['cv_value']:.6f}, prominence={p['prominence']:.6f}")
    
    # Check for the cascade signature: multiple distinct peaks
    if len(peaks) >= 2:
        print(f"  ** YAMABE NECK SIGNATURE DETECTED: {len(peaks)} distinct Cv peaks **")
        print(f"  This suggests {len(peaks)} Lifshitz transitions (rule composition)")
    elif len(peaks) == 1:
        print(f"  Single Cv peak: consistent with single-step grokking")
    else:
        print(f"  No clear Cv peaks detected")
    
    # Print energy trajectory (sampled)
    n = len(energy_hist)
    if n > 0:
        sample_points = [0, n//4, n//2, 3*n//4, n-1]
        sample_points = [p for p in sample_points if p < n]
        print(f"\n  Energy trajectory (sampled):")
        for p in sample_points:
            cv_val = cv_hist[p] if p < len(cv_hist) else 0
            def_val = defect_hist[p] if p < len(defect_hist) else 0
            print(f"    iter={p:>3}: E={energy_hist[p]:.4f}, "
                  f"Cv={cv_val:.6f}, eps={def_val:.4f}")


def run_experiment():
    """Run the full Phase 5 cascade thought experiment."""
    print("=" * 70)
    print("PHASE 5: CASCADING THOUGHT EXHAUST EXPERIMENT")
    print("Testing prediction: multi-step reasoning = cascading Cv peaks")
    print("=" * 70)
    
    puzzles = [
        make_single_color_swap,      # Control: 1-step (simple color swap, 3 stalks)
        make_swap_and_move,          # Test: 2-step (swap + translate, 3 stalks)
        make_three_object_chain,     # Test: 2-step (chained color propagation, 4 stalks)
        make_four_object_grid,       # Control: many stalks, single rule (5 stalks)
    ]
    
    results = []
    
    for make_puzzle in puzzles:
        inp, out, name = make_puzzle()
        print(f"\n{'='*50}")
        print(f"Puzzle: {name}")
        print(f"Input shape: {inp.shape}, Output shape: {out.shape}")
        
        result = run_instrumented_crystallization(inp, out, name, max_iter=80)
        if result is not None:
            results.append(result)
            analyze_cascade(result)
    
    # Comparative analysis
    print("\n" + "=" * 70)
    print("COMPARATIVE CASCADE ANALYSIS")
    print("=" * 70)
    
    print(f"\n{'Puzzle':<25} {'Grokked':>8} {'b1':>4} {'Acc':>6} "
          f"{'Cv_peaks':>9} {'Cascade':>10}")
    print("-" * 70)
    
    for r in results:
        peaks = find_cv_peaks(r['cv_hist'])
        cascade = "YES" if len(peaks) >= 2 else "no"
        grok_str = "YES" if r['grokked'] else "no"
        print(f"{r['name']:<25} {grok_str:>8} {r['b1']:>4} "
              f"{r['accuracy']:>5.1%} {len(peaks):>9} {cascade:>10}")
    
    # The prediction
    print("\n" + "-" * 70)
    print("FRONTIER PREDICTION (Section 1.4):")
    print("  1-step puzzles should show 1 Cv peak (single Lifshitz transition)")
    print("  2-step puzzles should show 2+ Cv peaks (cascading transitions)")
    print("  Each successive peak should be at lower effective temperature")
    print("-" * 70)
    
    # Check prediction
    single_step = [r for r in results if '+' not in r['name']]
    multi_step = [r for r in results if '+' in r['name']]
    
    single_peaks = [len(find_cv_peaks(r['cv_hist'])) for r in single_step]
    multi_peaks = [len(find_cv_peaks(r['cv_hist'])) for r in multi_step]
    
    if single_peaks and multi_peaks:
        avg_single = np.mean(single_peaks)
        avg_multi = np.mean(multi_peaks)
        print(f"\n  Avg Cv peaks (1-step): {avg_single:.1f}")
        print(f"  Avg Cv peaks (2-step): {avg_multi:.1f}")
        
        if avg_multi > avg_single:
            print("\n  ** PREDICTION SUPPORTED: Multi-step tasks produce more Cv peaks **")
        else:
            print("\n  Prediction not yet supported. May need more iterations or")
            print("  stronger composition signal. The cascade may be sub-resolution.")
    
    return results


if __name__ == '__main__':
    results = run_experiment()
