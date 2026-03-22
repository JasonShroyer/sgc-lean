#!/usr/bin/env python3
"""
Gaia DR3 re-run with universal lift selector (Phase 13).
Key insight: L1 symmetric lift captures L_z via off-diagonal entries.
No Hessian pump — Stage 1 variance gradient only.
"""
import numpy as np
import csv, os, sys

sys.path.insert(0, os.path.dirname(__file__))
from sgc_universal import crystallize_universal, LIFT_LIBRARY

# Load Gaia data
csv_path = os.path.normpath(os.path.join(os.path.dirname(__file__),
                                          '..', 'data', 'gaia_dr3_raw.csv'))
records = []
with open(csv_path, 'r') as f:
    reader = csv.DictReader(f)
    for row in reader:
        try:
            records.append({
                'plx': float(row['parallax']),
                'pmra': float(row['pmra']),
                'pmdec': float(row['pmdec']),
                'rv': float(row['radial_velocity']),
                'l': float(row['l']),
                'b': float(row['b']),
            })
        except (ValueError, KeyError):
            pass

print(f"Loaded {len(records)} stars")

# Manual galactocentric transformation
R_sun = 8.122
Z_sun = 0.0208
v_sun = np.array([12.9, 245.6, 7.78])

l_rad = np.array([r['l'] for r in records]) * np.pi / 180
b_rad = np.array([r['b'] for r in records]) * np.pi / 180
plx = np.array([r['plx'] for r in records])
pmra = np.array([r['pmra'] for r in records])
pmdec = np.array([r['pmdec'] for r in records])
rv_arr = np.array([r['rv'] for r in records])
dist_kpc = 1.0 / plx

x_hc = dist_kpc * np.cos(b_rad) * np.cos(l_rad)
y_hc = dist_kpc * np.cos(b_rad) * np.sin(l_rad)
z_hc = dist_kpc * np.sin(b_rad)
X_gc = R_sun - x_hc
Y_gc = -y_hc
Z_gc = z_hc + Z_sun

k = 4.74047
vl = k * pmra * dist_kpc
vb = k * pmdec * dist_kpc
U_hc = rv_arr * np.cos(l_rad) * np.cos(b_rad) - vl * np.sin(l_rad) - vb * np.cos(l_rad) * np.sin(b_rad)
V_hc = rv_arr * np.sin(l_rad) * np.cos(b_rad) + vl * np.cos(l_rad) - vb * np.sin(l_rad) * np.sin(b_rad)
W_hc = rv_arr * np.sin(b_rad) + vb * np.cos(b_rad)
vX_gc = -(U_hc + v_sun[0])
vY_gc = V_hc + v_sun[1]
vZ_gc = W_hc + v_sun[2]
R_gc = np.sqrt(X_gc**2 + Y_gc**2)

# Ground truth L_z
Lz_true = X_gc * vY_gc - Y_gc * vX_gc

print("=" * 70)
print("GAIA DR3 RE-RUN WITH UNIVERSAL LIFT SELECTOR")
print("Stage 1 only (no Hessian pump)")
print("=" * 70)

bins = [
    ("Solar neighborhood (8-11 kpc)", 8, 11),
    ("Outer disk (11-16 kpc)", 11, 16),
]

for bin_name, rmin, rmax in bins:
    mask = (R_gc >= rmin) & (R_gc < rmax)
    n = int(np.sum(mask))
    print(f"\n{'=' * 70}")
    print(f"{bin_name}: {n} stars")
    print(f"{'=' * 70}")

    if n < 500:
        print("  SKIP: too few stars")
        continue

    state = np.column_stack([
        X_gc[mask], Y_gc[mask], Z_gc[mask],
        vX_gc[mask], vY_gc[mask], vZ_gc[mask]
    ])

    # Normalize: zero mean, unit variance
    state_mean = np.mean(state, axis=0)
    state_std = np.std(state, axis=0)
    state_std[state_std < 1e-10] = 1.0
    state_norm = (state - state_mean) / state_std

    # Run universal lift selector
    result = crystallize_universal(state_norm, k=2, lambda_mdl=0.01)

    print(f"\n  Winner: {result.winning_lift}")
    print(f"  Variances: {result.variances}")
    print(f"  Confidence: {result.confidence}")
    print(f"  Dominant features: {result.dominant_features}")

    # Interpret the winning constraint
    if 'symmetric' in result.winning_lift or 'mixed' in result.winning_lift:
        # Map feature names back to physical meaning
        labels = ['X', 'Y', 'Z', 'vX', 'vY', 'vZ']
        for cidx, c_vec in enumerate(result.constraints):
            top5 = np.argsort(np.abs(c_vec))[::-1][:5]
            print(f"\n  Constraint C_{cidx+1} top features:")
            for idx in top5:
                if abs(c_vec[idx]) > 0.05:
                    fname = result.feature_names[idx]
                    # Parse feature name to get physical labels
                    if '*' in fname:
                        parts = fname.replace('S:', '').replace('A:', '').split('*')
                        i, j = int(parts[0][1:]), int(parts[1][1:])
                        phys = f"{labels[i]}*{labels[j]}"
                    else:
                        phys = fname
                    print(f"    {fname:>15s} ({phys:>8s}): {c_vec[idx]:+.4f}")

    # L_z check: compute L_z for this bin and check variance
    Lz_bin = Lz_true[mask]
    Lz_norm = (Lz_bin - np.mean(Lz_bin)) / np.std(Lz_bin)
    print(f"\n  Ground truth L_z: mean={np.mean(Lz_bin):.1f} kpc*km/s, "
          f"std={np.std(Lz_bin):.1f}")

    # Shuffle control
    state_shuf = state_norm.copy()
    rng = np.random.RandomState(42)
    for dim in range(6):
        rng.shuffle(state_shuf[:, dim])
    result_shuf = crystallize_universal(state_shuf, k=1, lambda_mdl=0.01)
    print(f"\n  Shuffle: winner={result_shuf.winning_lift} "
          f"var={result_shuf.variances[0]:.4e}")
    if result.variances[0] > 0:
        ratio = result_shuf.variances[0] / result.variances[0]
        print(f"  Shuffle/Real ratio: {ratio:.1f}x "
              f"({'PASS' if ratio > 2 else 'FAIL'})")

print(f"\n{'=' * 70}")
print("GAIA UNIVERSAL BENCHMARK COMPLETE")
print(f"{'=' * 70}")
