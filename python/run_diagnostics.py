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
    
    # Summary
    print("\n" + "=" * 80)
    print("  EXPERIMENT SUMMARY")
    print("=" * 80)
    
    for name, result in results.items():
        print(f"\n  {name.upper()}:")
        if isinstance(result, dict):
            if 'predictions' in result:
                preds = result['predictions']
                confirmed = sum(1 for v in preds.values() if '✓' in str(v) or v == 'CONFIRMED')
                total = len(preds)
                print(f"    Predictions: {confirmed}/{total} confirmed")
            if 'profile' in result:
                profile = result['profile']
                print(f"    ε={profile.epsilon:.4f}, γ={profile.gamma:.4f}, T*={profile.T_star:.2f}")
        elif hasattr(result, 'epsilon'):
            print(f"    ε={result.epsilon:.4f}, γ={result.gamma:.4f}, T*={result.T_star:.2f}")
    
    print("\n" + "=" * 80)
    print("  Output files saved to:", output_path.absolute())
    print("=" * 80)
    
    return results


if __name__ == "__main__":
    main()
