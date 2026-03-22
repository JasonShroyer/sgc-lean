#!/usr/bin/env python3
"""
SGC Universal Runner
====================
Top-level script: load any data file, run the SGC engine, produce a physics report.

Usage:
    python run_universal.py <datafile> [--columns col1,col2,...] [--output report.txt]
    python run_universal.py --selftest
"""
import numpy as np
import argparse, sys, os, json

sys.path.insert(0, os.path.dirname(__file__))
from sgc_universal_loader import load_data
from sgc_relational_engine import SGCRelationalEngine, RelationalRule
from sgc_physics_report import generate_report, generate_json_summary


def state_vectors_to_trajectories(data: np.ndarray):
    """Convert (T, D) state array to list of (states_before, states_after) pairs.
    Each pair has shape (1, D) — single object dynamics."""
    T, D = data.shape
    trajectories = []
    for t in range(T - 1):
        sb = data[t].reshape(1, D)
        sa = data[t + 1].reshape(1, D)
        trajectories.append((sb, sa))
    return trajectories


def run_pipeline(data: np.ndarray, meta=None, max_iterations=200,
                 noise_test=True, verbose=True):
    """Run the full SGC pipeline: dynamics mode + manifold mode, report best."""
    T, D = data.shape

    # ================================================================
    # MODE 1: DYNAMICS (linear transition matrix R)
    # Discovers linear conservation laws from state transitions
    # ================================================================
    if verbose:
        print(f"\n{'='*60}")
        print(f"MODE 1: DYNAMICS (linear R matrix, {T} steps x {D}D)")
        print(f"{'='*60}")

    trajectories = state_vectors_to_trajectories(data)
    engine = SGCRelationalEngine(state_dim=D, max_objects=1, eta=0.01)
    rule_dynamics = engine.crystallize(trajectories, max_iterations=max_iterations,
                                        residual_threshold=1e-10)

    # ================================================================
    # MODE 2: MANIFOLD (quadratic lift, variance minimization)
    # Discovers quadratic conservation laws: E, L², mass shell, etc.
    # Uses crystallize_manifold_multi from the engine
    # ================================================================
    manifold_results = None
    if T >= 50 and D <= 10:  # manifold mode is O(D^4), limit to small D
        if verbose:
            print(f"\n{'='*60}")
            print(f"MODE 2: MANIFOLD (quadratic lift, k=2 constraints)")
            print(f"{'='*60}")
        try:
            constraints, mtel = SGCRelationalEngine.crystallize_manifold_multi(
                data, k=min(2, D), max_iterations=600, lr=0.01
            )
            # Compute variance for each constraint
            X_outer = np.einsum('ni,nj->nij', data, data)
            manifold_vars = []
            for C in constraints:
                q = np.einsum('ij,nij->n', C, X_outer)
                manifold_vars.append(float(np.var(q)))

            manifold_results = {
                'constraints': constraints,
                'variances': manifold_vars,
                'telemetry': mtel,
            }
            if verbose:
                for i, (C, v) in enumerate(zip(constraints, manifold_vars)):
                    print(f"\n  Manifold C_{i+1}: variance={v:.6e}")
                    print(f"    Diagonal: [{', '.join(f'{x:+.4f}' for x in np.diag(C))}]")
        except Exception as e:
            if verbose:
                print(f"  Manifold mode failed: {e}")

    # ================================================================
    # CHOOSE BEST MODE
    # Dynamics mode: defect measures linear fit quality
    # Manifold mode: variance measures quadratic invariant quality
    # If manifold mode found low-variance constraints, it wins
    # ================================================================
    manifold_wins = False
    if manifold_results and manifold_results['variances']:
        best_manifold_var = min(manifold_results['variances'])
        # Manifold wins if it found a genuine low-variance invariant
        # and dynamics mode has significant defect
        if best_manifold_var < 0.01 and rule_dynamics.functional_defect > 1e-6:
            manifold_wins = True
        # Also wins if variance is extremely low (near-exact conservation)
        if best_manifold_var < 1e-6:
            manifold_wins = True

    # Noise sensitivity test (on dynamics mode)
    noise_rule = None
    if noise_test and T >= 50:
        noise_data = data + np.random.randn(*data.shape) * 0.1
        noise_trajs = state_vectors_to_trajectories(noise_data)
        noise_engine = SGCRelationalEngine(state_dim=D, max_objects=1, eta=0.01)
        noise_rule = noise_engine.crystallize(noise_trajs, max_iterations=max_iterations,
                                               residual_threshold=1e-10)

    # Generate report
    report = generate_report(rule_dynamics, meta, noise_rule)
    summary = generate_json_summary(rule_dynamics, meta)

    # Append manifold results to report if available
    if manifold_results:
        manifold_lines = []
        manifold_lines.append(f"\n{'='*70}")
        manifold_lines.append("MANIFOLD MODE: QUADRATIC CONSERVATION LAWS")
        manifold_lines.append(f"{'='*70}")

        col_names = meta.columns if meta else [f'x{i}' for i in range(D)]

        for i, (C, v) in enumerate(zip(manifold_results['constraints'],
                                        manifold_results['variances'])):
            manifold_lines.append(f"\n  Constraint Q_{i+1}(x) = x^T C_{i+1} x:")
            manifold_lines.append(f"    Variance: {v:.6e}")
            diag = np.diag(C)
            manifold_lines.append(f"    C diagonal: [{', '.join(f'{x:+.4f}' for x in diag)}]")

            # Interpret: which variables dominate?
            top_idx = np.argsort(np.abs(diag))[::-1]
            terms = []
            for idx in top_idx[:D]:
                if abs(diag[idx]) > 0.01:
                    sign = '+' if diag[idx] > 0 else '-'
                    terms.append(f"{sign}{abs(diag[idx]):.4f}*{col_names[idx]}^2")
            if terms:
                manifold_lines.append(f"    Dominant terms: {' '.join(terms)}")

            # Check for Minkowski-like signature
            if abs(diag[0]) > 0.01 and D >= 2:
                ratios = diag[1:] / diag[0] if abs(diag[0]) > 0.01 else np.zeros(D-1)
                manifold_lines.append(f"    Ratios to {col_names[0]}^2: "
                                       f"[{', '.join(f'{r:+.4f}' for r in ratios)}]")

        if manifold_wins:
            manifold_lines.append(f"\n  *** MANIFOLD MODE WINS: quadratic invariants are stronger ***")
            manifold_lines.append(f"  The system has nonlinear conservation laws not visible to")
            manifold_lines.append(f"  the linear dynamics engine (Option C).")
        else:
            manifold_lines.append(f"\n  Linear dynamics mode is the primary result.")

        report += '\n' + '\n'.join(manifold_lines)
        summary['manifold'] = {
            'variances': manifold_results['variances'],
            'manifold_wins': manifold_wins,
        }

    return rule_dynamics, report, summary


def run_selftest():
    """Run the coupled oscillator benchmark and verify results."""
    print("=" * 70)
    print("SGC SELF-TEST: Coupled Harmonic Oscillator")
    print("=" * 70)

    # Generate coupled oscillator data
    # Two masses connected by spring: x'' = -k(x-y), y'' = -k(y-x)
    # State: [x, vx, y, vy]
    np.random.seed(42)
    dt = 0.01
    k = 1.0
    T = 500

    state = np.array([1.0, 0.0, -0.5, 0.3])  # initial: [x, vx, y, vy]
    trajectory = [state.copy()]

    for _ in range(T - 1):
        x, vx, y, vy = state
        # Euler integration
        ax = -k * (x - y)
        ay = -k * (y - x)
        state[0] += vx * dt
        state[1] += ax * dt
        state[2] += vy * dt
        state[3] += ay * dt
        trajectory.append(state.copy())

    data = np.array(trajectory)
    # Normalize
    means = data.mean(0)
    stds = data.std(0)
    stds[stds < 1e-12] = 1.0
    data_norm = (data - means) / stds

    from sgc_universal_loader import DataMetadata
    meta = DataMetadata(
        source_path='<selftest: coupled oscillator>',
        source_format='generated',
        columns=['x', 'vx', 'y', 'vy'],
        means=means.tolist(),
        stds=stds.tolist(),
        T=T, D=4,
    )

    rule, report, summary = run_pipeline(data_norm, meta, noise_test=False, verbose=True)

    print(report)

    # Verification
    passed = True
    if rule.b1 < 1:
        print(f"\nFAIL: b1 = {rule.b1}, expected >= 1")
        passed = False
    else:
        print(f"\nPASS: b1 = {rule.b1} >= 1 (conservation law detected)")

    # Check for coupling between x and y (Newton's Third Law)
    R = rule.R_self
    if abs(R[0, 2]) > 0.001 or abs(R[2, 0]) > 0.001:
        if abs(R[0, 2]) > 1e-6 and abs(R[2, 0]) > 1e-6:
            ratio = abs(R[0, 2] / R[2, 0])
            print(f"  Coupling ratio |R[x,y]/R[y,x]| = {ratio:.4f}")
        print("PASS: x-y coupling detected")
    else:
        print("INFO: Direct x-y coupling below threshold (may couple through velocities)")

    if passed:
        print("\n*** SELF-TEST PASSED ***")
        return 0
    else:
        print("\n*** SELF-TEST FAILED ***")
        return 1


def generate_test_data():
    """Generate test CSV files for validation."""
    demo_dir = os.path.dirname(__file__)

    # Test B: Kepler circular orbit
    print("Generating test_kepler.csv...")
    np.random.seed(42)
    T = 500
    dt = 0.01
    # Circular orbit: r=1, v=1, period=2pi
    theta = np.linspace(0, 4 * np.pi, T)
    x1 = np.cos(theta)
    y1 = np.sin(theta)
    vx1 = -np.sin(theta)
    vy1 = np.cos(theta)
    # Second body at origin (stationary, heavy)
    x2 = np.zeros(T)
    y2 = np.zeros(T)
    vx2 = np.zeros(T)
    vy2 = np.zeros(T)
    kepler_path = os.path.join(demo_dir, 'test_kepler.csv')
    with open(kepler_path, 'w') as f:
        f.write("x1,y1,vx1,vy1,x2,y2,vx2,vy2\n")
        for t in range(T):
            f.write(f"{x1[t]},{y1[t]},{vx1[t]},{vy1[t]},"
                    f"{x2[t]},{y2[t]},{vx2[t]},{vy2[t]}\n")
    print(f"  Written to {kepler_path}")

    # Test D: Lorenz attractor
    print("Generating test_lorenz.csv...")
    sigma, rho, beta = 10.0, 28.0, 8.0/3.0
    dt_l = 0.01
    T_l = 500
    state = np.array([1.0, 1.0, 1.0])
    lorenz_data = [state.copy()]
    for _ in range(T_l - 1):
        x, y, z = state
        dx = sigma * (y - x)
        dy = x * (rho - z) - y
        dz = x * y - beta * z
        state += np.array([dx, dy, dz]) * dt_l
        lorenz_data.append(state.copy())
    lorenz_arr = np.array(lorenz_data)
    lorenz_path = os.path.join(demo_dir, 'test_lorenz.csv')
    with open(lorenz_path, 'w') as f:
        f.write("x,y,z\n")
        for t in range(T_l):
            f.write(f"{lorenz_arr[t,0]},{lorenz_arr[t,1]},{lorenz_arr[t,2]}\n")
    print(f"  Written to {lorenz_path}")

    return kepler_path, lorenz_path


def main():
    parser = argparse.ArgumentParser(description='SGC Universal Physics Discovery')
    parser.add_argument('datafile', nargs='?', help='Path to data file')
    parser.add_argument('--columns', type=str, default=None,
                        help='Comma-separated column names to use')
    parser.add_argument('--output', type=str, default=None,
                        help='Output file for report')
    parser.add_argument('--json', type=str, default=None,
                        help='Output file for JSON summary')
    parser.add_argument('--selftest', action='store_true',
                        help='Run self-test on coupled oscillator')
    parser.add_argument('--generate-test-data', action='store_true',
                        help='Generate test CSV files for validation')
    args = parser.parse_args()

    if args.selftest:
        sys.exit(run_selftest())

    if args.generate_test_data:
        generate_test_data()
        return

    if not args.datafile:
        parser.print_help()
        sys.exit(1)

    columns = args.columns.split(',') if args.columns else None
    data, meta = load_data(args.datafile, columns=columns)

    rule, report, summary = run_pipeline(data, meta)

    print(report)

    if args.output:
        with open(args.output, 'w') as f:
            f.write(report)
        print(f"\nReport saved to {args.output}")

    if args.json:
        with open(args.json, 'w') as f:
            json.dump(summary, f, indent=2)
        print(f"JSON summary saved to {args.json}")


if __name__ == '__main__':
    main()
