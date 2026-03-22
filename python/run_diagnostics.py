#!/usr/bin/env python3
"""
SGC Emergence Diagnostic — Single Entry Point

Run SGC diagnostic experiments from the command line.

Usage:
    python run_diagnostics.py --experiment all
    python run_diagnostics.py --experiment synthetic
    python run_diagnostics.py --experiment grokking
    python run_diagnostics.py --experiment celegans
    
Output goes to python/output/ by default.
"""
import argparse
import sys
from pathlib import Path

# Add package to path
sys.path.insert(0, str(Path(__file__).parent))


def main():
    parser = argparse.ArgumentParser(
        description="SGC Emergence Diagnostic Engine",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
    python run_diagnostics.py --experiment all
    python run_diagnostics.py --experiment synthetic --output results/
    python run_diagnostics.py --experiment grokking
    python run_diagnostics.py --experiment celegans

Each experiment produces:
    - Console output with SGC profile and prediction evaluation
    - PNG figure with 6-panel diagnostic visualization  
    - Markdown certificate with theorem citations
        """
    )
    
    parser.add_argument(
        "--experiment", "-e",
        choices=["all", "synthetic", "grokking", "celegans"],
        default="all",
        help="Which experiment to run (default: all)"
    )
    
    parser.add_argument(
        "--output", "-o",
        type=str,
        default="output/",
        help="Output directory for figures and certificates (default: output/)"
    )
    
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Enable verbose output"
    )
    
    args = parser.parse_args()
    
    # Ensure output directory exists
    output_path = Path(args.output)
    output_path.mkdir(parents=True, exist_ok=True)
    
    print("=" * 80)
    print("  SGC EMERGENCE DIAGNOSTIC ENGINE")
    print("  A scientific instrument grounded in machine-verified mathematics")
    print("=" * 80)
    print(f"\n  Repository: https://github.com/JasonShroyer/sgc-lean")
    print(f"  Output directory: {output_path.absolute()}")
    print(f"  Experiment(s): {args.experiment}")
    
    results = {}
    
    # Run requested experiments
    if args.experiment in ("synthetic", "all"):
        try:
            from sgc_diagnostic.experiments.synthetic_chain import run_synthetic_chain
            results["synthetic"] = run_synthetic_chain(str(output_path))
        except Exception as e:
            print(f"\n  [X] Synthetic chain experiment failed: {e}")
            if args.verbose:
                import traceback
                traceback.print_exc()
    
    if args.experiment in ("grokking", "all"):
        try:
            from sgc_diagnostic.experiments.grokking import run_grokking_experiment
            results["grokking"] = run_grokking_experiment(str(output_path))
        except Exception as e:
            print(f"\n  [X] Grokking experiment failed: {e}")
            if args.verbose:
                import traceback
                traceback.print_exc()
    
    if args.experiment in ("celegans", "all"):
        try:
            from sgc_diagnostic.experiments.celegans import run_celegans_experiment
            results["celegans"] = run_celegans_experiment(str(output_path))
        except Exception as e:
            print(f"\n  [X] C. elegans experiment failed: {e}")
            if args.verbose:
                import traceback
                traceback.print_exc()
    
    # Part E: Final Summary Table
    print("\n" + "=" * 100)
    print("  FINAL SUMMARY TABLE")
    print("=" * 100)
    
    # Header with DATA column for REAL/SYNTHETIC label
    print(f"\n{'EXPERIMENT':<22} {'DATA':<8} {'eps':>10} {'gamma':>10} {'T*':>10} {'q':>8} {'N_E':>10} {'d':>4} {'ARI/beta':>10} {'PRED':<6}")
    print("-" * 100)
    
    # Collect all profiles for summary
    all_profiles = []
    
    for name, result in results.items():
        if isinstance(result, dict):
            # Handle synthetic chain which returns dict of profiles
            if 'symmetric' in result or 'broken_symmetry' in result:
                for subname, profile in result.items():
                    if hasattr(profile, 'epsilon'):
                        all_profiles.append((f"{name}_{subname}", profile, "SYNTH", None))
            # Handle grokking/celegans with is_real flag
            elif 'profile' in result:
                profile = result['profile']
                is_real = result.get('is_real', False)
                data_label = "REAL" if is_real else "SYNTH"
                extra = result.get('decay_beta') or result.get('ari')
                all_profiles.append((name, profile, data_label, extra))
            elif 'is_real' in result:
                # Grokking without profile object
                is_real = result.get('is_real', False)
                data_label = "REAL" if is_real else "SYNTH"
                decay_beta = result.get('decay_beta')
                # Create a mini profile dict for grokking
                if 'checkpoints' in result and len(result['checkpoints']) > 0:
                    last_cp = result['checkpoints'][-1]
                    sgc = last_cp.get('sgc', {})
                    all_profiles.append((name, {
                        'epsilon': sgc.get('epsilon', 0),
                        'gamma': sgc.get('gamma', 0),
                        'T_star': sgc.get('T_star', 0),
                        'q': sgc.get('q', 1),
                        'N_E': sgc.get('N_E', 0),
                        'autopoietic_depth': 0,
                        'predictions': result.get('predictions', {}),
                    }, data_label, decay_beta))
        elif hasattr(result, 'epsilon'):
            all_profiles.append((name, result, "SYNTH", None))
    
    total_confirmed = 0
    total_predictions = 0
    
    for exp_name, profile, data_label, extra_val in all_profiles:
        # Handle both SGCProfile objects and dicts
        if hasattr(profile, 'epsilon'):
            eps = profile.epsilon
            gamma = profile.gamma
            T_star = profile.T_star
            q = profile.q
            N_E = profile.N_E
            d = profile.autopoietic_depth
            preds = profile.predictions
            confirmed = sum(1 for p in preds if p.verdict == "CONFIRMED")
            total = len(preds)
        else:
            eps = profile.get('epsilon', 0)
            gamma = profile.get('gamma', 0)
            T_star = profile.get('T_star', 0)
            q = profile.get('q', 1)
            N_E = profile.get('N_E', 0)
            d = profile.get('autopoietic_depth', 0)
            preds = profile.get('predictions', {})
            if isinstance(preds, dict):
                confirmed = sum(1 for v in preds.values() if '[OK]' in str(v))
                total = len(preds)
            else:
                confirmed = sum(1 for p in preds if getattr(p, 'verdict', '') == "CONFIRMED")
                total = len(preds)
        
        total_confirmed += confirmed
        total_predictions += total
        
        # Format values
        eps_str = f"{eps:.6f}" if eps < 1 else f"{eps:.2e}"
        gamma_str = f"{gamma:.6f}" if gamma < 10 else f"{gamma:.2e}"
        T_str = f"{T_star:.2f}" if T_star < 1e6 else "inf"
        q_str = f"{q:.4f}"
        NE_str = f"{N_E:.2f}" if N_E < 1e6 else "inf"
        d_str = f"{d}"
        pred_str = f"{confirmed}/{total}"
        
        # Extra column: ARI for celegans, beta for grokking
        if extra_val is not None:
            if 'celegans' in exp_name.lower():
                extra_str = f"ARI={extra_val:.3f}"
            else:
                extra_str = f"b={extra_val:.3f}"
        else:
            extra_str = "n/a"
        
        # Truncate experiment name if needed
        exp_display = exp_name[:20] if len(exp_name) > 20 else exp_name
        
        print(f"  {exp_display:<20} {data_label:<8} {eps_str:>10} {gamma_str:>10} {T_str:>10} {q_str:>8} {NE_str:>10} {d_str:>4} {extra_str:>10} {pred_str:>6}")
    
    print("-" * 100)
    
    print(f"\n  Total predictions: {total_confirmed}/{total_predictions} confirmed")
    
    print("\n" + "=" * 100)
    print("  Output files saved to:", output_path.absolute())
    print("=" * 100)
    
    return results


if __name__ == "__main__":
    main()
