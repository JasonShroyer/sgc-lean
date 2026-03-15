#!/usr/bin/env python3
"""
Gaia DR3 Definitive Analysis
==============================
Addresses three issues from the assessment:
1. Report the Tsallis q values (are they in the formally safe range?)
2. Run dynamics-mode on a volume-complete subsample (d < 300pc)
3. Compare manifold-mode (selection-contaminated) vs dynamics-mode (clean)
"""
import numpy as np
import csv, sys, os

sys.path.insert(0, os.path.dirname(__file__))
from sgc_zero_param import discover
from sgc_relational_engine import SGCRelationalEngine

# ================================================================
# LOAD GAIA DATA
# ================================================================
R_sun = 8.122
k_conv = 4.74047
v_sun = np.array([12.9, 245.6, 7.78])

records = []
csv_path = os.path.normpath(os.path.join(os.path.dirname(__file__),
                                          '..', 'data', 'gaia_dr3_raw.csv'))
with open(csv_path, 'r') as f:
    reader = csv.DictReader(f)
    for row in reader:
        try:
            rec = {k: float(row[k]) for k in
                   ['parallax', 'pmra', 'pmdec', 'radial_velocity', 'l', 'b']}
            if rec['parallax'] > 0.1:
                records.append(rec)
        except (ValueError, KeyError):
            continue
        if len(records) >= 50000:
            break

l = np.array([r['l'] for r in records]) * np.pi / 180
b = np.array([r['b'] for r in records]) * np.pi / 180
plx = np.array([r['parallax'] for r in records])
d_kpc = 1.0 / plx

X_gc = R_sun - d_kpc * np.cos(b) * np.cos(l)
Y_gc = -d_kpc * np.cos(b) * np.sin(l)
Z_gc = d_kpc * np.sin(b)
vl = k_conv * np.array([r['pmra'] for r in records]) * d_kpc
vb = k_conv * np.array([r['pmdec'] for r in records]) * d_kpc
rv = np.array([r['radial_velocity'] for r in records])
U = rv*np.cos(l)*np.cos(b) - vl*np.sin(l) - vb*np.cos(l)*np.sin(b)
V = rv*np.sin(l)*np.cos(b) + vl*np.cos(l) - vb*np.sin(l)*np.sin(b)
W = rv*np.sin(b) + vb*np.cos(b)
vX = -(U + v_sun[0])
vY = V + v_sun[1]
vZ = W + v_sun[2]
R_cyl = np.sqrt(X_gc**2 + Y_gc**2)

print("#" * 70)
print("# GAIA DR3 DEFINITIVE ANALYSIS")
print("#" * 70)
print(f"  Total stars with 6D phase space: {len(records)}")

# ================================================================
# ISSUE 1: TSALLIS q VALUES
# ================================================================
print("\n" + "=" * 60)
print("ISSUE 1: TSALLIS q VALUES")
print("Formally safe range: q in (1, 2) [TsallisStatistics.lean]")
print("Empirically active but uncovered: q > 2 [GrokkingQParameter = 2.5]")
print("=" * 60)

# Run on several radial bins and report q
for bin_name, mask in [
    ("Solar (7-9 kpc)", (R_cyl >= 7) & (R_cyl < 9)),
    ("Outer (9-12 kpc)", (R_cyl >= 9) & (R_cyl < 12)),
    ("Far outer (>12 kpc)", R_cyl >= 12),
]:
    X = np.column_stack([X_gc[mask], Y_gc[mask], Z_gc[mask],
                          vX[mask], vY[mask], vZ[mask]])
    X_norm = (X - X.mean(0)) / X.std(0)
    X_sub = X_norm[:3000]
    if len(X_sub) < 50:
        continue
    r = discover(X_sub, ['X','Y','Z','vX','vY','vZ'], verbose=False)
    q = r.spectral_profile.tsallis_q
    in_safe = 1.0 < q < 2.0
    print(f"  {bin_name:25s}: q = {q:.4f}  {'SAFE (1,2)' if in_safe else 'OUTSIDE formal range'}")

# ================================================================
# ISSUE 2: DYNAMICS-MODE ON VOLUME-COMPLETE SUBSAMPLE
# ================================================================
print("\n" + "=" * 60)
print("ISSUE 2: DYNAMICS-MODE (volume-complete, d < 300pc)")
print("This removes selection contamination by using only nearby stars")
print("where Gaia is essentially complete (magnitude limit irrelevant).")
print("=" * 60)

# Volume-complete subsample: d < 0.3 kpc (300 pc)
d_limit = 0.3  # kpc
vol_mask = d_kpc < d_limit
n_vol = np.sum(vol_mask)
print(f"\n  Stars within {d_limit*1000:.0f} pc: {n_vol}")

if n_vol >= 100:
    X_vol = np.column_stack([X_gc[vol_mask], Y_gc[vol_mask], Z_gc[vol_mask],
                              vX[vol_mask], vY[vol_mask], vZ[vol_mask]])
    X_vol_norm = (X_vol - X_vol.mean(0)) / X_vol.std(0)

    # Use up to 3000 stars
    X_vol_sub = X_vol_norm[:3000]
    print(f"  Using {len(X_vol_sub)} stars for dynamics-mode test")

    # Run zero-param engine (includes both dynamics and manifold mode)
    r_vol = discover(X_vol_sub, ['X','Y','Z','vX','vY','vZ'], verbose=True)

    print(f"\n  DYNAMICS MODE RESULTS (volume-complete):")
    print(f"    T* = {r_vol.validity_horizon:.2f}")
    print(f"    b1 = {r_vol.b1}")
    print(f"    Tsallis q = {r_vol.spectral_profile.tsallis_q:.4f}")
    print(f"    Manifold wins: {r_vol.manifold_wins}")
    if r_vol.constraint_variances:
        print(f"    Manifold variances: {[f'{v:.4e}' for v in r_vol.constraint_variances]}")

    # Physical diagnostics on this subsample
    Lz_vol = X_gc[vol_mask][:len(X_vol_sub)] * vY[vol_mask][:len(X_vol_sub)] - \
             Y_gc[vol_mask][:len(X_vol_sub)] * vX[vol_mask][:len(X_vol_sub)]
    v_phi_vol = (X_gc[vol_mask][:len(X_vol_sub)] * vY[vol_mask][:len(X_vol_sub)] - \
                 Y_gc[vol_mask][:len(X_vol_sub)] * vX[vol_mask][:len(X_vol_sub)]) / \
                R_cyl[vol_mask][:len(X_vol_sub)]

    print(f"\n  Physical diagnostics (volume-complete):")
    print(f"    <L_z> = {np.mean(Lz_vol):.0f} +/- {np.std(Lz_vol):.0f} kpc*km/s")
    print(f"    <v_phi> = {np.mean(v_phi_vol):.1f} +/- {np.std(v_phi_vol):.1f} km/s")
    print(f"    L_z CoV = {np.std(Lz_vol)/abs(np.mean(Lz_vol)):.4f}")

    # Now run the lift tournament on this clean subsample
    from sgc_universal import crystallize_universal, LIFT_LIBRARY, score_lift, \
        find_min_variance_direction, lift_symmetric
    print(f"\n  MDL LIFT TOURNAMENT (volume-complete, 6D):")
    r_vol_univ = crystallize_universal(X_vol_sub, k=1, lambda_mdl=0.01)

    # Extract the degree-2 invariant on clean data
    Z2, n2 = lift_symmetric(X_vol_sub)
    Z2c = Z2 - Z2.mean(0)
    d2, v2 = find_min_variance_direction(Z2c, k=2)
    print(f"\n  Degree-2 invariant (CLEAN, no selection contamination):")
    print(f"    C1 variance: {v2[0]:.6e}")
    idx = np.argsort(np.abs(d2[0]))[::-1][:6]
    for j in idx:
        if abs(d2[0][j]) > 0.05:
            print(f"      {n2[j]:>12s}: {d2[0][j]:+.4f}")

    # Correlation with L_z on clean data
    q2 = Z2c @ d2[0]
    Lz_norm = (Lz_vol - np.mean(Lz_vol)) / (np.std(Lz_vol) + 1e-12)
    q2_norm = (q2 - np.mean(q2)) / (np.std(q2) + 1e-12)
    corr_clean = np.abs(np.corrcoef(Lz_norm[:len(q2_norm)], q2_norm)[0, 1])
    print(f"\n    Correlation with L_z (clean): {corr_clean:.4f}")
    print(f"    (Compare to contaminated: 0.1039)")

else:
    print(f"  Not enough nearby stars ({n_vol}). Expanding to d < 500 pc...")
    d_limit = 0.5
    vol_mask = d_kpc < d_limit
    n_vol = np.sum(vol_mask)
    print(f"  Stars within {d_limit*1000:.0f} pc: {n_vol}")
    if n_vol < 50:
        print("  Still not enough. Volume-complete test requires more data.")

# ================================================================
# ISSUE 3: COMPARISON TABLE
# ================================================================
print("\n" + "=" * 60)
print("COMPARISON: CONTAMINATED vs CLEAN")
print("=" * 60)
print(f"  {'Metric':<35s} {'Contaminated (7-12 kpc)':<25s} {'Clean (d<300pc)':<25s}")
print(f"  {'-'*35} {'-'*25} {'-'*25}")
if n_vol >= 100:
    print(f"  {'Degree-2 C1 corr with L_z':<35s} {'0.1039':<25s} {f'{corr_clean:.4f}':<25s}")
    print(f"  {'Tsallis q':<35s} {'1.50-1.64':<25s} {f'{r_vol.spectral_profile.tsallis_q:.4f}':<25s}")
    print(f"  {'Dynamics T*':<35s} {'0.17-0.19':<25s} {f'{r_vol.validity_horizon:.2f}':<25s}")
