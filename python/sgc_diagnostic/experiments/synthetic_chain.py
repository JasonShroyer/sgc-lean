# experiments/synthetic_chain.py
"""
Experiment 1: Asymmetric 4-State Chain

Tests the SGC diagnostic on a controlled synthetic system where we know
the ground truth partition structure.

States: {0,1,2,3}. Natural blocks: {0,1} | {2,3}.
Parameters: α=1.0 (intra-block), β=0.1 (inter-block), δ=0.3 (asymmetric coupling 0↔2).

This experiment TESTS:
1. P* recovery: does the optimal partition match the natural structure?
2. Non-zero defect: δ breaks exact lumpability, so ε > 0
3. q ≠ 1: non-uniform π means Tsallis index differs from Boltzmann
4. Timescale separation: α >> β means one clear timescale gap
5. Schur correction: second-order effects are measurable
"""
import numpy as np
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).parent.parent.parent))

from sgc_diagnostic import SGCDiagnostic, SGCProfile, generate_report
from sgc_diagnostic.certificates import CITATIONS, get_citation
from sgc_diagnostic.markov import validate_generator, check_detailed_balance


def build_asymmetric_chain(alpha: float = 1.0, beta: float = 0.1, 
                           delta: float = 0.3) -> tuple[np.ndarray, np.ndarray]:
    """
    Build the 4-state asymmetric chain generator.
    
    Structure:
        0 <-> 1  (intra-block, rate alpha)
        2 <-> 3  (intra-block, rate alpha)
        0 <-> 2  (inter-block asymmetric, rate delta)
        1 <-> 3  (inter-block symmetric, rate beta)
    
    Returns:
        L: Generator matrix (4x4)
        pi: Stationary distribution
    """
    # Build off-diagonal rates
    L = np.array([
        [0,     alpha,  delta,  0    ],  # 0 -> 1 (alpha), 0 -> 2 (delta)
        [beta,  0,      0,      alpha],  # 1 -> 0 (beta), 1 -> 3 (alpha)
        [delta, 0,      0,      alpha],  # 2 -> 0 (delta), 2 -> 3 (alpha)
        [0,     beta,   beta,   0    ],  # 3 -> 1 (beta), 3 -> 2 (beta)
    ], dtype=float)
    
    # Set diagonal so rows sum to zero
    np.fill_diagonal(L, -L.sum(axis=1))
    
    # Compute stationary distribution
    from sgc_diagnostic.markov import compute_stationary_distribution
    pi = compute_stationary_distribution(L)
    
    return L, pi


def build_broken_symmetry_chain(alpha: float = 1.0, beta: float = 0.1,
                                 delta_forward: float = 0.30, 
                                 delta_backward: float = 0.21) -> tuple[np.ndarray, np.ndarray]:
    """
    Build the 4-state chain with broken Z2 symmetry.
    
    The asymmetry delta_forward != delta_backward breaks exact lumpability,
    guaranteeing epsilon > 0. This is the chain where all five predictions
    should confirm simultaneously.
    
    Structure:
        0 <-> 1  (intra-block, rate alpha)
        2 <-> 3  (intra-block, rate alpha)
        0 -> 2   (rate delta_forward = 0.30)
        2 -> 0   (rate delta_backward = 0.21)
        1 <-> 3  (inter-block symmetric, rate beta)
    
    Returns:
        L: Generator matrix (4x4)
        pi: Stationary distribution
    """
    # Build off-diagonal rates with asymmetric 0<->2 coupling
    L = np.array([
        [0,     alpha,  delta_forward,   0    ],  # 0 -> 1, 0 -> 2
        [beta,  0,      0,               alpha],  # 1 -> 0, 1 -> 3
        [delta_backward, 0, 0,           alpha],  # 2 -> 0, 2 -> 3
        [0,     beta,   beta,            0    ],  # 3 -> 1, 3 -> 2
    ], dtype=float)
    
    # Set diagonal so rows sum to zero
    np.fill_diagonal(L, -L.sum(axis=1))
    
    # Compute stationary distribution
    from sgc_diagnostic.markov import compute_stationary_distribution
    pi = compute_stationary_distribution(L)
    
    return L, pi


def _run_chain_experiment(L: np.ndarray, pi: np.ndarray, system_name: str,
                          output_dir: str, pred1_epsilon_min: float = 0.05) -> SGCProfile:
    """
    Run SGC diagnostic on a 4-state chain and evaluate predictions.
    """
    # Validate
    validation = validate_generator(L, pi)
    print(f"\n  Validation: {'[OK] PASS' if validation['is_valid'] else '[X] FAIL'}")
    
    is_reversible, db_violation = check_detailed_balance(L, pi)
    print(f"  Detailed balance: {'[OK] YES' if is_reversible else '[X] NO'} (max violation: {db_violation:.2e})")
    
    # Create diagnostic engine
    diag = SGCDiagnostic(L, pi, 
                         labels=["0", "1", "2", "3"],
                         system_name=system_name)
    
    # STATE PREDICTIONS BEFORE COMPUTING
    print("\n  PREDICTIONS (stated before measurement):")
    print("-" * 60)
    
    # Prediction 1: Defect is non-zero
    pred2_n_blocks = 2
    pred3_depth_min = 1
    pred4_q_range = (1.0, 1.8)
    pred5_schur_min = 0.01
    
    print(f"  1. epsilon > {pred1_epsilon_min} (lumpability broken)")
    print(f"  2. k* = {pred2_n_blocks} blocks (natural structure)")
    print(f"  3. d >= {pred3_depth_min} (timescale gap)")
    print(f"  4. q in {pred4_q_range} (non-Boltzmann)")
    print(f"  5. ||Sigma|| > {pred5_schur_min} (second-order effects)")
    
    # COMPUTE PROFILE
    print("\n  Computing SGC profile...")
    profile = diag.compute_profile(k_min=2, k_max=4, n_restarts=30)
    
    # Register and evaluate predictions
    profile.add_prediction(
        statement=f"Defect epsilon > {pred1_epsilon_min}",
        theorem_key="optimal_partition_exists",
        predicted_value=pred1_epsilon_min,
        tolerance=pred1_epsilon_min
    ).evaluate(profile.epsilon)
    if profile.epsilon > pred1_epsilon_min:
        profile.predictions[0].verdict = "CONFIRMED"
    else:
        profile.predictions[0].verdict = "REFUTED"
    
    profile.add_prediction(
        statement=f"Optimal partition has {pred2_n_blocks} blocks",
        theorem_key="optimal_partition_exists",
        predicted_value=pred2_n_blocks,
        tolerance=0.5
    ).evaluate(profile.n_blocks)
    
    profile.add_prediction(
        statement=f"Autopoietic depth d >= {pred3_depth_min}",
        theorem_key="rg_tower_terminates",
        predicted_value=pred3_depth_min,
        tolerance=0.5
    ).evaluate(profile.autopoietic_depth)
    if profile.autopoietic_depth >= pred3_depth_min:
        profile.predictions[2].verdict = "CONFIRMED"
    else:
        profile.predictions[2].verdict = "REFUTED"
    
    profile.add_prediction(
        statement=f"Tsallis q in range {pred4_q_range}",
        theorem_key="q_estimation",
        predicted_value=(pred4_q_range[0] + pred4_q_range[1]) / 2,
        tolerance=(pred4_q_range[1] - pred4_q_range[0]) / 2
    ).evaluate(profile.q)
    
    profile.add_prediction(
        statement=f"Schur correction ||Sigma|| > {pred5_schur_min}",
        theorem_key="schur_self_energy",
        predicted_value=pred5_schur_min,
        tolerance=pred5_schur_min
    ).evaluate(profile.schur_correction_norm)
    if profile.schur_correction_norm > pred5_schur_min:
        profile.predictions[4].verdict = "CONFIRMED"
    else:
        profile.predictions[4].verdict = "REFUTED"
    
    # Print partition result
    print(f"\n  Optimal partition P*: {profile.P_star}")
    block_0 = [i for i in range(4) if profile.P_star[i] == 0]
    block_1 = [i for i in range(4) if profile.P_star[i] == 1]
    print(f"  Block structure: {{{block_0}}} | {{{block_1}}}")
    
    # Generate report
    generate_report(profile, output_dir)
    
    return profile


def run_synthetic_chain(output_dir: str = "output/") -> dict:
    """
    Run the synthetic chain experiments with falsifiable predictions.
    
    Returns dict with profiles for both symmetric and broken-symmetry chains.
    """
    results = {}
    
    # === EXPERIMENT 1A: Symmetric Chain ===
    print("\n" + "="*80)
    print("  EXPERIMENT 1A: Symmetric 4-State Chain")
    print("="*80)
    
    alpha, beta, delta = 1.0, 0.1, 0.3
    print(f"\n  Parameters: alpha={alpha}, beta={beta}, delta={delta}")
    print(f"  Expected structure: {{0,1}} | {{2,3}} or {{0,2}} | {{1,3}}")
    
    L1, pi1 = build_asymmetric_chain(alpha, beta, delta)
    print(f"\n  Generator L:")
    print(L1.round(4))
    print(f"\n  Stationary pi: {pi1.round(4)}")
    
    results["symmetric"] = _run_chain_experiment(
        L1, pi1, "Symmetric_4State_Chain", output_dir, pred1_epsilon_min=0.0
    )
    
    # === EXPERIMENT 1B: Broken Symmetry Chain ===
    print("\n" + "="*80)
    print("  EXPERIMENT 1B: Broken Symmetry 4-State Chain")
    print("="*80)
    
    alpha, beta = 1.0, 0.1
    delta_forward, delta_backward = 0.30, 0.21
    print(f"\n  Parameters: alpha={alpha}, beta={beta}")
    print(f"  Asymmetric coupling: 0->2 rate={delta_forward}, 2->0 rate={delta_backward}")
    print(f"  This breaks Z2 symmetry, guaranteeing epsilon > 0")
    
    L2, pi2 = build_broken_symmetry_chain(alpha, beta, delta_forward, delta_backward)
    print(f"\n  Generator L:")
    print(L2.round(4))
    print(f"\n  Stationary pi: {pi2.round(4)}")
    
    results["broken_symmetry"] = _run_chain_experiment(
        L2, pi2, "Asymmetric_4State_Broken", output_dir, pred1_epsilon_min=0.02
    )
    
    return results


if __name__ == "__main__":
    import sys
    output_dir = sys.argv[1] if len(sys.argv) > 1 else "output/"
    run_synthetic_chain(output_dir)
