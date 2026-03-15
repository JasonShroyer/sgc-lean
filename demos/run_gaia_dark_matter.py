#!/usr/bin/env python3
"""
Gaia DR3 Dark Matter Analysis with SGC Zero-Parameter Engine
=============================================================

The dark matter hypothesis predicts that the Milky Way is embedded in a
massive dark matter halo that dominates the gravitational potential at
large galactocentric radii. This produces a FLAT rotation curve:
orbital velocity v(R) ≈ const for R >> R_disk, rather than the
Keplerian v(R) ~ 1/sqrt(R) expected from visible matter alone.

SGC PREDICTIONS:
- If the galaxy is an isolated Newtonian system with visible matter only,
  the engine should find conservation laws (E, L_z) that are consistent
  with a Keplerian potential at all radii.
- If a dark matter halo exists, the conservation laws should CHANGE
  between the inner disk (visible-dominated) and outer halo (DM-dominated).
  Specifically:
  * L_z conservation should be STRONGER at large R (circular orbits in halo)
  * Energy conservation should show DIFFERENT structure at large R
    (flat rotation curve = different potential shape)
  * The T* (validity horizon) should vary with radius — revealing where
    the effective potential changes character.

METHODOLOGY:
1. Load Gaia DR3, compute galactocentric coordinates
2. Split stars into radial bins (inner, solar, outer)
3. Run the full Cartan-Killing lift tournament on each bin
4. Compare conservation law structure across bins
5. Look for anomalies that signal non-standard gravitational physics
"""
import numpy as np
import csv, sys, os
from datetime import datetime

sys.path.insert(0, os.path.dirname(__file__))
from sgc_zero_param import discover, compute_spectral_profile
from sgc_universal import crystallize_universal, LIFT_LIBRARY, score_lift, _lift_degree


def load_gaia_galactocentric(csv_path: str, max_stars: int = 50000):
    """Load Gaia DR3 and compute galactocentric phase space coordinates."""
    records = []
    with open(csv_path, 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            try:
                rec = {k: float(row[k]) for k in
                       ['parallax', 'pmra', 'pmdec', 'radial_velocity', 'l', 'b']}
                if rec['parallax'] > 0.1:  # distance < 10 kpc
                    records.append(rec)
            except (ValueError, KeyError):
                continue
            if len(records) >= max_stars:
                break

    print(f"  Loaded {len(records)} stars with full 6D phase space")

    # Galactocentric transformation (manual, no astropy dependency)
    R_sun = 8.122  # kpc
    Z_sun = 0.0208  # kpc
    v_sun = np.array([12.9, 245.6, 7.78])  # km/s (U, V, W solar motion)
    k = 4.74047  # km/s per (mas/yr * kpc)

    l = np.array([r['l'] for r in records]) * np.pi / 180
    b = np.array([r['b'] for r in records]) * np.pi / 180
    plx = np.array([r['parallax'] for r in records])
    d = 1.0 / plx  # distance in kpc

    # Galactocentric Cartesian
    X_gc = R_sun - d * np.cos(b) * np.cos(l)
    Y_gc = -d * np.cos(b) * np.sin(l)
    Z_gc = d * np.sin(b) - Z_sun

    # Velocities
    vl = k * np.array([r['pmra'] for r in records]) * d
    vb = k * np.array([r['pmdec'] for r in records]) * d
    rv = np.array([r['radial_velocity'] for r in records])

    # Heliocentric Cartesian velocities
    U = rv * np.cos(l) * np.cos(b) - vl * np.sin(l) - vb * np.cos(l) * np.sin(b)
    V = rv * np.sin(l) * np.cos(b) + vl * np.cos(l) - vb * np.sin(l) * np.sin(b)
    W = rv * np.sin(b) + vb * np.cos(b)

    # Galactocentric velocities (subtract solar motion)
    vX = -(U + v_sun[0])
    vY = V + v_sun[1]
    vZ = W + v_sun[2]

    # Cylindrical radius
    R_cyl = np.sqrt(X_gc**2 + Y_gc**2)

    # Azimuthal velocity (rotation curve diagnostic)
    v_phi = (X_gc * vY - Y_gc * vX) / R_cyl

    # Angular momentum L_z = R * v_phi
    L_z = R_cyl * v_phi

    return {
        'X': X_gc, 'Y': Y_gc, 'Z': Z_gc,
        'vX': vX, 'vY': vY, 'vZ': vZ,
        'R': R_cyl, 'v_phi': v_phi, 'L_z': L_z,
        'd': d, 'n_stars': len(records),
    }


def analyze_radial_bin(data, mask, bin_name, col_names):
    """Run SGC analysis on a radial bin of stars."""
    X = np.column_stack([data['X'][mask], data['Y'][mask], data['Z'][mask],
                          data['vX'][mask], data['vY'][mask], data['vZ'][mask]])

    # Normalize
    X_norm = (X - X.mean(0)) / X.std(0)
    n = len(X_norm)

    if n < 50:
        print(f"    Too few stars ({n}), skipping")
        return None

    print(f"\n    {bin_name}: {n} stars")

    # Zero-param engine
    result = discover(X_norm, col_names, verbose=False)

    # Full Cartan-Killing lift tournament on COMPLETE 6D state (X,Y,Z,vX,vY,vZ).
    # NO subsetting — the engine must see the full phase space to discover
    # position-velocity cross terms (angular momentum L_z = X*vY - Y*vX)
    # and any higher-degree invariants autonomously.
    # The LIFT_LIBRARY already covers degrees 1-8, which includes all
    # polynomial forms relevant to MOND (v^4), DM halo (quadratic), and
    # standard Newtonian (quadratic + symplectic) without hardcoding anything.
    r_univ = crystallize_universal(X_norm, k=1, lambda_mdl=0.01)

    # Compute physical diagnostics
    R_bin = data['R'][mask]
    v_phi_bin = data['v_phi'][mask]
    L_z_bin = data['L_z'][mask]

    # L_z conservation: how constant is angular momentum?
    L_z_var = np.var(L_z_bin) / (np.mean(L_z_bin)**2 + 1e-10)  # coefficient of variation²

    # Rotation curve: mean and spread of v_phi
    v_phi_mean = np.mean(v_phi_bin)
    v_phi_std = np.std(v_phi_bin)

    print(f"    T* = {result.validity_horizon:.2f}")
    print(f"    Tsallis q = {result.spectral_profile.tsallis_q:.3f}")
    print(f"    Manifold wins: {result.manifold_wins}")
    if result.constraint_variances:
        print(f"    Manifold variances: {[f'{v:.4e}' for v in result.constraint_variances]}")
    print(f"    MDL winner (velocity): {r_univ.winning_lift}")
    print(f"    R range: {R_bin.min():.1f} - {R_bin.max():.1f} kpc")
    print(f"    <v_phi> = {v_phi_mean:.1f} ± {v_phi_std:.1f} km/s")
    print(f"    <L_z> = {np.mean(L_z_bin):.0f} ± {np.std(L_z_bin):.0f} kpc·km/s")
    print(f"    L_z CoV² = {L_z_var:.4f}")

    return {
        'name': bin_name,
        'n_stars': n,
        'T_star': result.validity_horizon,
        'b1': result.b1,
        'q': result.spectral_profile.tsallis_q,
        'manifold_wins': result.manifold_wins,
        'manifold_vars': result.constraint_variances,
        'mdl_winner': r_univ.winning_lift,
        'R_mean': np.mean(R_bin),
        'v_phi_mean': v_phi_mean,
        'v_phi_std': v_phi_std,
        'L_z_mean': np.mean(L_z_bin),
        'L_z_std': np.std(L_z_bin),
        'L_z_cov2': L_z_var,
        'mdl_scores': r_univ.mdl_scores,
        'mdl_variances': {name: score_lift(X_norm, LIFT_LIBRARY[name], k=1,
                           lambda_mdl=0.01, lift_name=name)[2][0]
                          for name in LIFT_LIBRARY if name in r_univ.mdl_scores},
    }


def main():
    csv_path = os.path.normpath(os.path.join(os.path.dirname(__file__),
                                               '..', 'data', 'gaia_dr3_raw.csv'))

    print("#" * 70)
    print("# GAIA DR3 DARK MATTER ANALYSIS")
    print(f"# SGC Zero-Parameter Engine + Cartan-Killing Lift Tournament")
    print(f"# Date: {datetime.now().strftime('%Y-%m-%d %H:%M')}")
    print("#" * 70)

    # Load data
    print("\n  Loading Gaia DR3...")
    data = load_gaia_galactocentric(csv_path)
    print(f"  Total stars: {data['n_stars']}")
    print(f"  R range: {data['R'].min():.1f} - {data['R'].max():.1f} kpc")
    print(f"  <v_phi> = {np.mean(data['v_phi']):.1f} km/s (expect ~220)")

    col_names = ['X', 'Y', 'Z', 'vX', 'vY', 'vZ']

    # Define radial bins
    R = data['R']
    bins = [
        ('Inner disk (R < 7 kpc)', R < 7),
        ('Solar neighborhood (7-9 kpc)', (R >= 7) & (R < 9)),
        ('Outer disk (9-12 kpc)', (R >= 9) & (R < 12)),
        ('Far outer (R > 12 kpc)', R >= 12),
    ]

    # Also: full sample
    bins.insert(0, ('Full sample', np.ones(len(R), dtype=bool)))

    # Run analysis on each bin
    results = []
    for bin_name, mask in bins:
        print(f"\n{'='*60}")
        print(f"  ANALYZING: {bin_name}")
        print(f"{'='*60}")
        r = analyze_radial_bin(data, mask, bin_name, col_names)
        if r:
            results.append(r)

    # ================================================================
    # DARK MATTER DIAGNOSTIC: Rotation Curve Profile
    # ================================================================
    print(f"\n{'#'*70}")
    print("# ROTATION CURVE PROFILE")
    print(f"{'#'*70}")
    print(f"\n  {'Bin':<30s} {'<R>':>6s}  {'<v_phi>':>8s}  {'std_vphi':>8s}  {'T*':>8s}  {'q':>6s}  {'Lz_CoV2':>10s}")
    print(f"  {'-'*30} {'-'*6}  {'-'*8}  {'-'*8}  {'-'*8}  {'-'*6}  {'-'*10}")
    for r in results:
        print(f"  {r['name']:<30s} {r['R_mean']:>6.1f}  {r['v_phi_mean']:>8.1f}  {r['v_phi_std']:>8.1f}  {r['T_star']:>8.2f}  {r['q']:>6.3f}  {r['L_z_cov2']:>10.4f}")

    # ================================================================
    # DARK MATTER DIAGNOSTIC: Conservation Law Structure
    # ================================================================
    print(f"\n{'#'*70}")
    print("# CONSERVATION LAW STRUCTURE BY RADIUS")
    print(f"{'#'*70}")
    for r in results:
        print(f"\n  {r['name']}:")
        print(f"    MDL winner: {r['mdl_winner']}")
        if r['manifold_vars']:
            print(f"    Manifold variances: {[f'{v:.4e}' for v in r['manifold_vars']]}")
        # Show top 3 lifts by MDL
        if r['mdl_scores']:
            sorted_scores = sorted(r['mdl_scores'].items(), key=lambda x: x[1])[:3]
            print(f"    Top lifts: {', '.join(f'{n}({s:.3f})' for n, s in sorted_scores)}")

    # ================================================================
    # INTERPRETATION
    # ================================================================
    print(f"\n{'#'*70}")
    print("# DARK MATTER INTERPRETATION")
    print(f"{'#'*70}")

    # Key diagnostic: does v_phi flatten or decline with R?
    if len(results) >= 4:
        inner_vphi = [r['v_phi_mean'] for r in results if r['R_mean'] < 8]
        outer_vphi = [r['v_phi_mean'] for r in results if r['R_mean'] > 10]

        if inner_vphi and outer_vphi:
            inner_mean = np.mean(inner_vphi)
            outer_mean = np.mean(outer_vphi)
            ratio = outer_mean / inner_mean if inner_mean > 0 else 0

            print(f"\n  Rotation curve diagnostic:")
            print(f"    Inner <v_phi> = {inner_mean:.1f} km/s")
            print(f"    Outer <v_phi> = {outer_mean:.1f} km/s")
            print(f"    Ratio (outer/inner) = {ratio:.3f}")

            if ratio > 0.85:
                print(f"\n  ** FLAT ROTATION CURVE DETECTED (ratio > 0.85) **")
                print(f"  This is consistent with a dark matter halo.")
                print(f"  Keplerian prediction (visible matter only): ratio ~ 0.7-0.8")
                print(f"  Observed: {ratio:.3f}")
            elif ratio > 0.7:
                print(f"\n  Moderately flat rotation curve (ratio {ratio:.3f})")
                print(f"  Consistent with some DM or modified gravity.")
            else:
                print(f"\n  Declining rotation curve (ratio {ratio:.3f})")
                print(f"  Closer to Keplerian (visible matter dominated).")

    # Key diagnostic: does L_z conservation CHANGE with radius?
    if len(results) >= 3:
        inner_lz = [r for r in results if r['R_mean'] < 8]
        outer_lz = [r for r in results if r['R_mean'] > 10]

        if inner_lz and outer_lz:
            print(f"\n  Angular momentum conservation diagnostic:")
            print(f"    Inner L_z CoV² = {inner_lz[0]['L_z_cov2']:.4f}")
            print(f"    Outer L_z CoV² = {outer_lz[0]['L_z_cov2']:.4f}")

            if outer_lz[0]['L_z_cov2'] < inner_lz[0]['L_z_cov2']:
                print(f"    L_z is MORE conserved at large R — consistent with DM halo")
                print(f"    (circular orbits in a smooth potential)")
            else:
                print(f"    L_z is LESS conserved at large R — may indicate perturbations")

    # Key diagnostic: does the Tsallis q change with radius?
    if len(results) >= 3:
        q_values = [(r['R_mean'], r['q']) for r in results if r['R_mean'] > 0]
        q_values.sort()
        print(f"\n  Tsallis q profile (heavy-tail structure):")
        for R_mean, q in q_values:
            print(f"    R = {R_mean:.1f} kpc: q = {q:.3f}")

    # Key diagnostic: do the winning lifts change with radius?
    print(f"\n  Lift tournament winners by radius:")
    for r in results:
        print(f"    R = {r['R_mean']:.1f} kpc: {r['mdl_winner']}")
    print(f"\n  If the winning lift CHANGES between inner and outer disk,")
    print(f"  this indicates the symmetry group of the potential changes —")
    print(f"  the signature of a transition between visible-dominated and")
    print(f"  DM-dominated regimes.")


if __name__ == '__main__':
    main()
