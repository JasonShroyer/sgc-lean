#!/usr/bin/env python3
"""
BENCHMARK 1: GAIA DR3 — GALACTIC KINEMATICS (DARK MATTER TEST)

Discovers conserved integrals of motion from 6D stellar phase-space vectors
using SGC manifold mode. No parametric potential model assumed.

PRIOR PREDICTION (stated before running):
  P1: b_1 = 2 for inner disk (6-12 kpc): energy E and angular momentum L_z
  P2: b_1 < 2 or T* degradation for outer disk (12-25 kpc)
  P3: The discovered C matrices encode E and L_z without being told the
      functional form of the gravitational potential
"""
import numpy as np
import csv, os, sys

sys.path.insert(0, os.path.dirname(__file__))
from sgc_relational_engine import SGCRelationalEngine

# ====================================================================
# DATA LOADING AND GALACTOCENTRIC TRANSFORMATION
# ====================================================================
csv_path = os.path.join(os.path.dirname(__file__), '..', 'data', 'gaia_dr3_raw.csv')
csv_path = os.path.normpath(csv_path)

print("=" * 70)
print("BENCHMARK 1: GAIA DR3 — GALACTIC KINEMATICS")
print("Discovering integrals of motion from stellar phase space")
print("=" * 70)

# Load
records = []
with open(csv_path, 'r') as f:
    reader = csv.DictReader(f)
    for row in reader:
        try:
            records.append({
                'ra': float(row['ra']),
                'dec': float(row['dec']),
                'plx': float(row['parallax']),
                'pmra': float(row['pmra']),
                'pmdec': float(row['pmdec']),
                'rv': float(row['radial_velocity']),
                'l': float(row['l']),
                'b': float(row['b']),
            })
        except (ValueError, KeyError):
            pass

print(f"Loaded {len(records)} stars with full 6D kinematics")

# Manual galactocentric transformation (no astropy dependency)
# Solar parameters (IAU recommended, Gravity Collab. 2021):
R_sun = 8.122   # kpc, Sun's distance from GC
Z_sun = 0.0208  # kpc, Sun's height above plane
# Solar motion (Schoenrich+ 2010 + V_LSR=232.8 km/s):
v_sun = np.array([12.9, 245.6, 7.78])  # (U, V, W) in km/s

l_rad = np.array([r['l'] for r in records]) * np.pi / 180
b_rad = np.array([r['b'] for r in records]) * np.pi / 180
ra_rad = np.array([r['ra'] for r in records]) * np.pi / 180
dec_rad = np.array([r['dec'] for r in records]) * np.pi / 180
plx = np.array([r['plx'] for r in records])
pmra = np.array([r['pmra'] for r in records])
pmdec = np.array([r['pmdec'] for r in records])
rv_arr = np.array([r['rv'] for r in records])

dist_kpc = 1.0 / plx

# Heliocentric galactic cartesian (x toward GC, y toward l=90, z toward NGP)
x_hc = dist_kpc * np.cos(b_rad) * np.cos(l_rad)
y_hc = dist_kpc * np.cos(b_rad) * np.sin(l_rad)
z_hc = dist_kpc * np.sin(b_rad)

# Galactocentric position (GC at origin, Sun at negative X)
X_gc = R_sun - x_hc
Y_gc = -y_hc  # flip to right-handed
Z_gc = z_hc + Z_sun

# Heliocentric velocity in galactic (l, b, r) -> (U, V, W)
# U toward GC, V toward l=90 (rotation), W toward NGP
k = 4.74047  # km/s per (mas/yr * kpc)
vl = k * pmra * dist_kpc   # approximate: pm_l*cos(b) ~ pmra for |b| small
vb = k * pmdec * dist_kpc

# Project to galactic UVW (simplified: valid for |b| < 30 deg)
U_hc = rv_arr * np.cos(l_rad) * np.cos(b_rad) - vl * np.sin(l_rad) - vb * np.cos(l_rad) * np.sin(b_rad)
V_hc = rv_arr * np.sin(l_rad) * np.cos(b_rad) + vl * np.cos(l_rad) - vb * np.sin(l_rad) * np.sin(b_rad)
W_hc = rv_arr * np.sin(b_rad) + vb * np.cos(b_rad)

# Galactocentric velocity: add solar motion
vX_gc = -(U_hc + v_sun[0])  # flip sign: helio U is toward GC, galactocentric X is from GC
vY_gc = V_hc + v_sun[1]
vZ_gc = W_hc + v_sun[2]

R_gc = np.sqrt(X_gc**2 + Y_gc**2)

print(f"Galactocentric R range: {R_gc.min():.2f} - {R_gc.max():.2f} kpc")
print(f"Median R: {np.median(R_gc):.2f} kpc")

# ====================================================================
# PRIOR PREDICTIONS (stated before seeing results)
# ====================================================================
print(f"\n{'=' * 70}")
print("PRIOR PREDICTIONS")
print(f"{'=' * 70}")
print("  P1: k_eff = 2 for inner disk (6-12 kpc): E and L_z conserved")
print("  P2: k_eff < 2 or higher variance for outer disk (12-25 kpc)")
print("  P3: C matrices encode energy + angular momentum structure")
print("      without parametric potential model")

# ====================================================================
# GROUND TRUTH: Compute E and L_z directly
# ====================================================================
# Approximate energy: E = 0.5*v^2 (kinetic only, potential unknown)
v_tot = np.sqrt(vX_gc**2 + vY_gc**2 + vZ_gc**2)
# Angular momentum about z-axis: L_z = X*vY - Y*vX
Lz = X_gc * vY_gc - Y_gc * vX_gc

print(f"\n  Ground truth diagnostics:")
print(f"    v_tot range: {v_tot.min():.1f} - {v_tot.max():.1f} km/s")
print(f"    L_z range: {Lz.min():.1f} - {Lz.max():.1f} kpc*km/s")

# ====================================================================
# BINNED ANALYSIS
# ====================================================================
bins = [
    ("Inner disk (6-9 kpc)", 6, 9),
    ("Solar neighborhood (9-12 kpc)", 9, 12),
    ("Outer disk (12-16 kpc)", 12, 16),
    ("Far outer (16-25 kpc)", 16, 25),
]

results_table = []

for bin_name, rmin, rmax in bins:
    mask = (R_gc >= rmin) & (R_gc < rmax)
    n_stars = int(np.sum(mask))

    print(f"\n{'=' * 70}")
    print(f"RADIAL BIN: {bin_name} — {n_stars} stars")
    print(f"{'=' * 70}")

    if n_stars < 200:
        print(f"  SKIP: insufficient stars ({n_stars} < 200)")
        results_table.append({
            'bin': bin_name, 'n': n_stars, 'k_eff': 'N/A',
            'var1': 'N/A', 'var2': 'N/A', 'status': 'SKIP'
        })
        continue

    # Build 6D state vectors for this bin
    state = np.column_stack([
        X_gc[mask], Y_gc[mask], Z_gc[mask],
        vX_gc[mask], vY_gc[mask], vZ_gc[mask]
    ])

    # Normalize: zero mean, unit std per dimension
    state_mean = np.mean(state, axis=0)
    state_std = np.std(state, axis=0)
    state_std[state_std < 1e-10] = 1.0
    state_norm = (state - state_mean) / state_std

    print(f"  State shape: {state_norm.shape}")
    print(f"  Position std (kpc): {state_std[:3]}")
    print(f"  Velocity std (km/s): {state_std[3:]}")

    # Run manifold multi with k=3
    print(f"\n  Running crystallize_manifold_multi(k=3)...")
    constraints, telemetry = SGCRelationalEngine.crystallize_manifold_multi(
        state_norm, k=3, max_iterations=800, lr=0.01
    )

    # Analyze results
    X_outer = np.einsum('ni,nj->nij', state_norm, state_norm)
    variances = []
    for cidx, C in enumerate(constraints):
        q = np.einsum('ij,nij->n', C, X_outer)
        v = float(np.var(q))
        variances.append(v)

    # k_effective: count constraints where variance < 10% of a random C
    np.random.seed(42)
    C_rand = np.random.randn(6, 6)
    C_rand = (C_rand + C_rand.T) / 2
    C_rand /= np.linalg.norm(C_rand)
    q_rand = np.einsum('ij,nij->n', C_rand, X_outer)
    var_rand = float(np.var(q_rand))

    k_eff = sum(1 for v in variances if v < 0.1 * var_rand)

    print(f"\n  RESULTS:")
    print(f"    Random C variance: {var_rand:.4e}")
    for cidx, v in enumerate(variances):
        ratio = v / var_rand
        print(f"    C_{cidx+1} variance: {v:.4e} "
              f"(ratio to random: {ratio:.4f})")
    print(f"    k_effective = {k_eff}")

    # Analyze C matrix structure: position-velocity coupling
    for cidx, C in enumerate(constraints):
        pos_block = C[:3, :3]
        vel_block = C[3:, 3:]
        cross_block = C[:3, 3:]
        print(f"\n    C_{cidx+1} structure:")
        print(f"      Position block norm: {np.linalg.norm(pos_block):.4f}")
        print(f"      Velocity block norm: {np.linalg.norm(vel_block):.4f}")
        print(f"      Cross block norm:    {np.linalg.norm(cross_block):.4f}")
        print(f"      Diagonal: [{', '.join(f'{v:+.4f}' for v in np.diag(C))}]")

    # Shuffle control
    print(f"\n  SHUFFLE CONTROL:")
    state_shuffled = state_norm.copy()
    np.random.seed(123)
    for dim in range(6):
        np.random.shuffle(state_shuffled[:, dim])
    constraints_shuf, _ = SGCRelationalEngine.crystallize_manifold_multi(
        state_shuffled, k=2, max_iterations=400, lr=0.01
    )
    X_outer_shuf = np.einsum('ni,nj->nij', state_shuffled, state_shuffled)
    for cidx, C in enumerate(constraints_shuf):
        q = np.einsum('ij,nij->n', C, X_outer_shuf)
        v = float(np.var(q))
        print(f"    Shuffled C_{cidx+1} variance: {v:.4e}")

    results_table.append({
        'bin': bin_name, 'n': n_stars, 'k_eff': k_eff,
        'var1': f'{variances[0]:.2e}' if len(variances) > 0 else 'N/A',
        'var2': f'{variances[1]:.2e}' if len(variances) > 1 else 'N/A',
        'var_rand': f'{var_rand:.2e}',
        'status': 'OK'
    })

# ====================================================================
# SUMMARY
# ====================================================================
print(f"\n{'=' * 70}")
print("RESULTS SUMMARY")
print(f"{'=' * 70}")
print(f"\n  {'Bin':<30s} {'N':>7s} {'k_eff':>6s} {'Var(C1)':>12s} "
      f"{'Var(C2)':>12s} {'Var(rand)':>12s}")
print(f"  {'-'*80}")
for r in results_table:
    if r['status'] == 'SKIP':
        print(f"  {r['bin']:<30s} {r['n']:>7d}  SKIP (too few stars)")
    else:
        print(f"  {r['bin']:<30s} {r['n']:>7d} {r['k_eff']:>6d} "
              f"{r['var1']:>12s} {r['var2']:>12s} {r['var_rand']:>12s}")

print(f"\n{'=' * 70}")
print("BENCHMARK 1 COMPLETE")
print(f"{'=' * 70}")
