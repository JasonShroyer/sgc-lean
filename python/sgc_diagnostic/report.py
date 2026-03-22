# report.py
"""
Report generator: console output, 6-panel figure, JSON profile, and Markdown certificate.
"""
import json
import numpy as np
from datetime import datetime
from pathlib import Path
from typing import Optional
from .certificates import REPO, COMMIT

# Lazy import for matplotlib (may not be available or compatible)
plt = None
gridspec = None
_matplotlib_checked = False
_matplotlib_available = False

def _ensure_matplotlib():
    """Lazy import matplotlib with safety checks."""
    global plt, gridspec, _matplotlib_checked, _matplotlib_available
    
    # Skip if already checked and failed
    if _matplotlib_checked:
        return _matplotlib_available
    
    _matplotlib_checked = True
    
    # Check for explicit disable
    import os
    if os.environ.get('SGC_NO_MATPLOTLIB', '').lower() in ('1', 'true', 'yes'):
        print("  Warning: matplotlib disabled via SGC_NO_MATPLOTLIB")
        print("  Figures will not be generated.")
        return False
    
    # Try to import with Agg backend (non-interactive, avoids some crashes)
    os.environ.setdefault('MPLBACKEND', 'Agg')
    
    try:
        import matplotlib
        matplotlib.use('Agg')
        import matplotlib.pyplot as _plt
        import matplotlib.gridspec as _gridspec
        plt = _plt
        gridspec = _gridspec
        _matplotlib_available = True
        return True
    except Exception as e:
        # Catch all exceptions including numpy binary compatibility errors
        print(f"  Warning: matplotlib not available ({type(e).__name__})")
        print("  Figures will not be generated.")
        _matplotlib_available = False
        return False


def generate_report(profile, output_dir: str = "output/"):
    """
    Generate the full SGC emergence diagnostic report:
    1. Console summary with all five numbers
    2. JSON profile (always saved, no matplotlib dependency)
    3. 6-panel figure (if matplotlib available)
    4. Markdown certificate file
    """
    output_path = Path(output_dir)
    output_path.mkdir(parents=True, exist_ok=True)
    
    _print_console_report(profile)
    _save_json_profile(profile, output_path)  # Always save JSON (no matplotlib needed)
    
    # Try to generate figure, but don't abort on failure
    try:
        if _ensure_matplotlib():
            _generate_figure(profile, output_path)
    except Exception as e:
        print(f"  Warning: Figure generation failed ({e})")
        print("  Continuing without figure...")
    
    _write_certificate(profile, output_path)


def _save_json_profile(profile, output_path: Path):
    """Save complete profile as JSON (no matplotlib dependency)."""
    data = {
        "system_name": profile.system_name,
        "timestamp": datetime.now().isoformat(),
        "commit": COMMIT,
        "repository": REPO,
        
        # The five SGC numbers
        "epsilon": float(profile.epsilon),
        "gamma": float(profile.gamma),
        "T_star": float(profile.T_star),
        "q": float(profile.q),
        "N_E": float(profile.N_E) if profile.N_E < 1e10 else None,
        "autopoietic_depth": int(profile.autopoietic_depth),
        "schur_correction_norm": float(profile.schur_correction_norm),
        
        # System properties
        "n_states": int(profile.n),
        "n_blocks": int(profile.n_blocks),
        "regime": profile.regime,
        "validity_horizon_label": profile.validity_horizon_label,
        
        # Partition assignment
        "partition": profile.P_star.tolist() if hasattr(profile.P_star, 'tolist') else list(profile.P_star),
        
        # Defect curve
        "defect_curve": {str(k): float(v) for k, v in profile.defect_by_k.items()},
        
        # Eigenvalues (as list of [real, imag] pairs)
        "eigenvalues": [[float(np.real(e)), float(np.imag(e))] for e in profile.eigenvalues],
        
        # Dirichlet decomposition
        "dirichlet_decomposition": {
            "coarse": float(profile.dirichlet_coarse),
            "leakage": float(profile.dirichlet_leakage),
        },
        
        # q diagnostics
        "q_diagnostics": profile.q_diagnostics,
        
        # Stationary distribution
        "pi": profile.pi.tolist() if hasattr(profile.pi, 'tolist') else list(profile.pi),
        
        # Predictions
        "predictions": [
            {
                "statement": pred.statement,
                "theorem": pred.theorem.name if pred.theorem else None,
                "predicted_value": float(pred.predicted_value) if pred.predicted_value is not None else None,
                "tolerance": float(pred.tolerance) if pred.tolerance is not None else None,
                "actual_value": float(pred.actual_value) if pred.actual_value is not None else None,
                "verdict": pred.verdict,
            }
            for pred in profile.predictions
        ],
    }
    
    filename = output_path / f"{profile.system_name.replace(' ', '_')}_profile.json"
    with open(filename, 'w', encoding='utf-8') as f:
        json.dump(data, f, indent=2, ensure_ascii=False)
    print(f"  JSON profile saved: {filename}")


def _print_console_report(profile):
    """Print the console summary (ASCII-safe for Windows)."""
    print("=" * 80)
    print(f"  SGC EMERGENCE DIAGNOSTIC -- {profile.system_name}")
    print(f"  Commit: {REPO}/commit/{COMMIT}")
    print(f"  Timestamp: {datetime.now().isoformat()}")
    print("=" * 80)
    
    print(f"\n{'NUMBER':<30} {'VALUE':>12}  {'THEOREM':<35} {'STATUS'}")
    print("-" * 95)
    
    rows = [
        ("eps (defect norm)", f"{profile.epsilon:.6f}",
         "optimal_partition_exists", "PROVED"),
        ("gamma (spectral gap)", f"{profile.gamma:.6f}",
         "dirichlet_gap_non_decrease", "PROVED"),
        ("T* (validity horizon)", f"{profile.T_star:.2f}",
         "trajectory_closure_bound", "PROVED"),
        ("q (Tsallis index)", f"{profile.q:.4f}",
         "tsallis_dpi", "PROVED"),
        ("N_E (emergence capacity)", f"{profile.N_E:.4f}" if profile.N_E < 1e6 else "inf",
         "emergence_ceiling", "AXIOM"),
        ("d (autopoietic depth)", f"{profile.autopoietic_depth}",
         "rg_tower_terminates", "PROVED"),
        ("||Sigma|| (Schur self-energy)", f"{profile.schur_correction_norm:.6f}",
         "schur_self_energy", "CONJECTURE"),
    ]
    
    for name, val, thm, status in rows:
        status_marker = "[OK]" if status == "PROVED" else "[A]" if status == "AXIOM" else "[?]"
        print(f"  {name:<28} {val:>12}  {thm:<35} {status_marker} {status}")
    
    print(f"\n  SYSTEM PROPERTIES")
    print(f"  |-- States (n):     {profile.n}")
    print(f"  |-- Blocks (P*):    {profile.n_blocks}")
    print(f"  |-- Regime:         {profile.regime}")
    print(f"  +-- Validity:       {profile.validity_horizon_label}")
    
    # Dirichlet decomposition
    total = abs(profile.dirichlet_coarse) + abs(profile.dirichlet_leakage)
    if total > 1e-12:
        coarse_pct = 100 * abs(profile.dirichlet_coarse) / total
        leak_pct = 100 * abs(profile.dirichlet_leakage) / total
        print(f"\n  DIRICHLET DECOMPOSITION [theorem: dirichlet_form_defect_decomposition]")
        print(f"  E(f) = <f, -L_bar f>_pi + <f, -Df>_pi")
        print(f"       = {profile.dirichlet_coarse:+.6f} + {profile.dirichlet_leakage:+.6f}")
        print(f"       (coarse {coarse_pct:.1f}% / leakage {leak_pct:.1f}%)")
    
    # Predictions
    if profile.predictions:
        print(f"\n  FALSIFIABLE PREDICTIONS")
        print("-" * 70)
        for pred in profile.predictions:
            if pred.verdict == "CONFIRMED":
                marker = "[OK] CONFIRMED"
            elif pred.verdict == "REFUTED":
                marker = "[X] REFUTED"
            elif pred.verdict == "INCONCLUSIVE":
                marker = "[~] INCONCLUSIVE"
            else:
                marker = "[.] PENDING"
            print(f"  [{marker}] {pred.statement}")
            if pred.actual_value is not None:
                print(f"      Predicted: {pred.predicted_value:.4f} +/- {pred.tolerance:.4f}")
                print(f"      Actual:    {pred.actual_value:.4f}")
    
    print("=" * 80)


def _generate_figure(profile, output_path: Path):
    """Generate the 6-panel diagnostic figure."""
    fig = plt.figure(figsize=(16, 10))
    gs = gridspec.GridSpec(2, 3, figure=fig, hspace=0.3, wspace=0.3)
    
    # Panel 1: Defect curve ε(k) vs k
    ax1 = fig.add_subplot(gs[0, 0])
    _plot_defect_curve(ax1, profile)
    
    # Panel 2: Eigenvalue spectrum with timescale gaps
    ax2 = fig.add_subplot(gs[0, 1])
    _plot_spectrum(ax2, profile)
    
    # Panel 3: Dirichlet decomposition bar chart
    ax3 = fig.add_subplot(gs[0, 2])
    _plot_dirichlet_decomposition(ax3, profile)
    
    # Panel 4: Schur self-energy vs defect
    ax4 = fig.add_subplot(gs[1, 0])
    _plot_schur_vs_defect(ax4, profile)
    
    # Panel 5: Stationary distribution (q-colored)
    ax5 = fig.add_subplot(gs[1, 1])
    _plot_distribution(ax5, profile)
    
    # Panel 6: Prediction scoreboard
    ax6 = fig.add_subplot(gs[1, 2])
    _plot_scoreboard(ax6, profile)
    
    # Title
    fig.suptitle(f"SGC Emergence Diagnostic: {profile.system_name}", 
                 fontsize=14, fontweight='bold', y=0.98)
    
    # Save
    filename = output_path / f"{profile.system_name.replace(' ', '_')}_profile.png"
    plt.savefig(filename, dpi=150, bbox_inches='tight', facecolor='white')
    plt.close(fig)
    print(f"  Figure saved: {filename}")


def _plot_defect_curve(ax, profile):
    """Plot defect curve ε(k) vs number of blocks k."""
    if not profile.defect_by_k:
        ax.text(0.5, 0.5, "No defect data", ha='center', va='center', transform=ax.transAxes)
        ax.set_title("Defect Curve ε(k)")
        return
    
    ks = sorted(profile.defect_by_k.keys())
    epsilons = [profile.defect_by_k[k] for k in ks]
    
    ax.plot(ks, epsilons, 'b.-', linewidth=2, markersize=10)
    ax.axhline(y=profile.epsilon, color='r', linestyle='--', alpha=0.7, 
               label=f'ε* = {profile.epsilon:.4f}')
    ax.axvline(x=profile.n_blocks, color='g', linestyle=':', alpha=0.7,
               label=f'k* = {profile.n_blocks}')
    
    ax.set_xlabel('Number of blocks (k)')
    ax.set_ylabel('Defect norm ‖D_P‖_π')
    ax.set_title('Defect Curve [optimal_partition_exists]')
    ax.legend(loc='upper right', fontsize=8)
    ax.grid(True, alpha=0.3)
    ax.set_yscale('log')


def _plot_spectrum(ax, profile):
    """Plot eigenvalue spectrum with timescale gaps marked."""
    if len(profile.eigenvalues) == 0:
        ax.text(0.5, 0.5, "No spectral data", ha='center', va='center', transform=ax.transAxes)
        ax.set_title("Eigenvalue Spectrum")
        return
    
    # Plot eigenvalues in complex plane
    real = np.real(profile.eigenvalues)
    imag = np.imag(profile.eigenvalues)
    
    ax.scatter(real, imag, c='blue', s=50, alpha=0.7)
    ax.axhline(y=0, color='k', linewidth=0.5)
    ax.axvline(x=0, color='k', linewidth=0.5)
    ax.axvline(x=-profile.gamma, color='r', linestyle='--', alpha=0.7,
               label=f'γ = {profile.gamma:.4f}')
    
    ax.set_xlabel('Re(λ)')
    ax.set_ylabel('Im(λ)')
    ax.set_title(f'Spectrum [d = {profile.autopoietic_depth} gaps]')
    ax.legend(loc='lower left', fontsize=8)
    ax.grid(True, alpha=0.3)


def _plot_dirichlet_decomposition(ax, profile):
    """Plot Dirichlet form decomposition as bar chart."""
    labels = ['Coarse ⟨f,-L̄f⟩', 'Leakage ⟨f,-Df⟩']
    values = [profile.dirichlet_coarse, profile.dirichlet_leakage]
    colors = ['steelblue', 'coral']
    
    bars = ax.bar(labels, values, color=colors, edgecolor='black', linewidth=1.5)
    
    # Add value labels
    for bar, val in zip(bars, values):
        height = bar.get_height()
        ax.text(bar.get_x() + bar.get_width()/2., height,
                f'{val:.4f}', ha='center', va='bottom' if height >= 0 else 'top',
                fontsize=10)
    
    ax.axhline(y=0, color='k', linewidth=0.5)
    ax.set_ylabel('Dirichlet form component')
    ax.set_title('Dirichlet Decomposition\n[dirichlet_form_defect_decomposition]')
    ax.grid(True, alpha=0.3, axis='y')


def _plot_schur_vs_defect(ax, profile):
    """Plot Schur correction norm vs defect."""
    # Single point for this system
    ax.scatter([profile.epsilon], [profile.schur_correction_norm], 
               c='purple', s=100, marker='*', zorder=5)
    
    # Reference line: Σ = ε (equal magnitudes)
    max_val = max(profile.epsilon, profile.schur_correction_norm) * 1.5
    if max_val > 0:
        ax.plot([0, max_val], [0, max_val], 'k--', alpha=0.5, label='‖Σ‖ = ε')
    
    ax.set_xlabel('Defect norm ε')
    ax.set_ylabel('Schur correction ‖Σ‖')
    ax.set_title('Second-Order Correction\n[schur_self_energy: CONJECTURE]')
    ax.legend(loc='upper left', fontsize=8)
    ax.grid(True, alpha=0.3)
    
    # Annotate
    ax.annotate(f'ε={profile.epsilon:.4f}\n‖Σ‖={profile.schur_correction_norm:.4f}',
                xy=(profile.epsilon, profile.schur_correction_norm),
                xytext=(10, 10), textcoords='offset points', fontsize=9,
                bbox=dict(boxstyle='round,pad=0.3', facecolor='yellow', alpha=0.7))


def _plot_distribution(ax, profile):
    """Plot stationary distribution colored by q-escort."""
    from .tsallis import compute_escort_distribution
    
    n = len(profile.pi)
    x = np.arange(n)
    
    # Original distribution
    ax.bar(x, profile.pi, alpha=0.6, color='steelblue', label=f'π (q=1)')
    
    # Escort distribution if q ≠ 1
    if abs(profile.q - 1.0) > 0.05:
        pi_q = compute_escort_distribution(profile.pi, profile.q)
        ax.step(x, pi_q, where='mid', color='red', linewidth=2, 
                label=f'P_q (q={profile.q:.2f})')
    
    ax.set_xlabel('State')
    ax.set_ylabel('Probability')
    ax.set_title(f'Stationary Distribution\n[q={profile.q:.3f}, {profile.q_diagnostics.get("regime", "unknown")}]')
    ax.legend(loc='upper right', fontsize=8)
    ax.grid(True, alpha=0.3, axis='y')


def _plot_scoreboard(ax, profile):
    """Plot prediction scoreboard."""
    ax.axis('off')
    
    if not profile.predictions:
        ax.text(0.5, 0.5, "No predictions registered", 
                ha='center', va='center', fontsize=12)
        ax.set_title('Prediction Scoreboard')
        return
    
    # Build scoreboard text
    lines = ["PREDICTION SCOREBOARD\n" + "="*40 + "\n"]
    
    confirmed = sum(1 for p in profile.predictions if p.verdict == "CONFIRMED")
    refuted = sum(1 for p in profile.predictions if p.verdict == "REFUTED")
    pending = sum(1 for p in profile.predictions if p.verdict == "PENDING")
    inconclusive = sum(1 for p in profile.predictions if p.verdict == "INCONCLUSIVE")
    
    lines.append(f"✓ Confirmed:    {confirmed}")
    lines.append(f"✗ Refuted:      {refuted}")
    lines.append(f"~ Inconclusive: {inconclusive}")
    lines.append(f"⋯ Pending:      {pending}")
    lines.append("-" * 40)
    
    for i, pred in enumerate(profile.predictions):
        status = {"CONFIRMED": "✓", "REFUTED": "✗", 
                  "INCONCLUSIVE": "~", "PENDING": "⋯"}[pred.verdict]
        # Truncate statement if too long
        stmt = pred.statement[:50] + "..." if len(pred.statement) > 50 else pred.statement
        lines.append(f"{status} {stmt}")
    
    text = "\n".join(lines)
    ax.text(0.05, 0.95, text, transform=ax.transAxes, fontsize=9,
            verticalalignment='top', fontfamily='monospace',
            bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.8))
    ax.set_title('Prediction Scoreboard')


def _write_certificate(profile, output_path: Path):
    """Write Markdown certificate file."""
    filename = output_path / f"{profile.system_name.replace(' ', '_')}_certificate.md"
    
    with open(filename, 'w', encoding='utf-8') as f:
        f.write(f"# SGC Emergence Certificate: {profile.system_name}\n\n")
        f.write(f"**Generated:** {datetime.now().isoformat()}\n\n")
        f.write(f"**Repository:** [{REPO}]({REPO})\n\n")
        f.write(f"**Commit:** `{COMMIT}`\n\n")
        
        f.write("## The Five SGC Numbers\n\n")
        f.write("| Number | Value | Theorem | Status |\n")
        f.write("|--------|-------|---------|--------|\n")
        
        rows = [
            ("ε (defect)", f"{profile.epsilon:.6f}", "optimal_partition_exists", "PROVED"),
            ("γ (spectral gap)", f"{profile.gamma:.6f}", "dirichlet_gap_non_decrease", "PROVED"),
            ("T* (validity)", f"{profile.T_star:.2f}", "trajectory_closure_bound", "PROVED"),
            ("q (Tsallis)", f"{profile.q:.4f}", "tsallis_dpi", "PROVED"),
            ("N_E (capacity)", f"{profile.N_E:.4f}" if profile.N_E < 1e6 else "∞", "emergence_ceiling", "AXIOM"),
        ]
        
        for name, val, thm, status in rows:
            citation = profile.citations.get(thm)
            if citation:
                thm_link = f"[{thm}]({citation.url})"
            else:
                thm_link = thm
            f.write(f"| {name} | {val} | {thm_link} | {status} |\n")
        
        f.write("\n## System Properties\n\n")
        f.write(f"- **States:** {profile.n}\n")
        f.write(f"- **Optimal blocks:** {profile.n_blocks}\n")
        f.write(f"- **Autopoietic depth:** {profile.autopoietic_depth}\n")
        f.write(f"- **Regime:** {profile.regime}\n")
        f.write(f"- **Validity:** {profile.validity_horizon_label}\n")
        
        f.write("\n## Dirichlet Decomposition\n\n")
        f.write("```\n")
        f.write(f"ℰ(f) = ⟨f, -L̄f⟩_π + ⟨f, -Df⟩_π\n")
        f.write(f"     = {profile.dirichlet_coarse:+.6f} + {profile.dirichlet_leakage:+.6f}\n")
        f.write("```\n")
        f.write(f"\n*Theorem: dirichlet_form_defect_decomposition*\n")
        
        if profile.predictions:
            f.write("\n## Falsifiable Predictions\n\n")
            for pred in profile.predictions:
                status_emoji = {"CONFIRMED": "✅", "REFUTED": "❌", 
                               "INCONCLUSIVE": "⚠️", "PENDING": "⏳"}[pred.verdict]
                f.write(f"### {status_emoji} {pred.statement}\n\n")
                f.write(f"- **Theorem:** {pred.theorem.name} ({pred.theorem.status})\n")
                f.write(f"- **Predicted:** {pred.predicted_value:.4f} ± {pred.tolerance:.4f}\n")
                if pred.actual_value is not None:
                    f.write(f"- **Actual:** {pred.actual_value:.4f}\n")
                f.write(f"- **Verdict:** {pred.verdict}\n\n")
        
        f.write("\n## Citation\n\n")
        f.write("```bibtex\n")
        f.write("@software{sgc_diagnostic,\n")
        f.write("  title = {Spectral Geometry of Consolidation},\n")
        f.write(f"  url = {{{REPO}}},\n")
        f.write(f"  commit = {{{COMMIT}}},\n")
        f.write(f"  date = {{{datetime.now().strftime('%Y-%m-%d')}}}\n")
        f.write("}\n")
        f.write("```\n")
    
    print(f"  Certificate saved: {filename}")
