#!/usr/bin/env python3
"""
Gaia DR3 Propagation Diagnostic
================================
Determines whether the degree-5 winner is genuine new physics
or algebraic propagation of degree-2 invariants.

The test: extract the dominant monomials from the L7 winner.
If they are products of the degree-2 winners (e.g. E*L_z, E^2, L_z^2*E),
it's propagation. If new independent radial or velocity powers appear
that are NOT expressible as products of the quadratic invariants,
that would be genuine higher-order physics.
"""
import numpy as np
import csv, sys, os

sys.path.insert(0, os.path.dirname(__file__))
from sgc_universal import (find_min_variance_direction, lift_symmetric,
                            lift_cubic, lift_quartic, lift_quintic,
                            lift_identity, LIFT_LIBRARY, score_lift)

# Load and transform Gaia data
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
        if len(records) >= 30000:
            break

l = np.array([r['l'] for r in records]) * np.pi / 180
b = np.array([r['b'] for r in records]) * np.pi / 180
plx = np.array([r['parallax'] for r in records])
d = 1.0 / plx

X_gc = R_sun - d * np.cos(b) * np.cos(l)
Y_gc = -d * np.cos(b) * np.sin(l)
Z_gc = d * np.sin(b)
vl = k_conv * np.array([r['pmra'] for r in records]) * d
vb = k_conv * np.array([r['pmdec'] for r in records]) * d
rv = np.array([r['radial_velocity'] for r in records])
U = rv*np.cos(l)*np.cos(b) - vl*np.sin(l) - vb*np.cos(l)*np.sin(b)
V = rv*np.sin(l)*np.cos(b) + vl*np.cos(l) - vb*np.sin(l)*np.sin(b)
W = rv*np.sin(b) + vb*np.cos(b)
vX = -(U + v_sun[0])
vY = V + v_sun[1]
vZ = W + v_sun[2]
R_cyl = np.sqrt(X_gc**2 + Y_gc**2)

# Solar neighborhood sample
mask = (R_cyl >= 7) & (R_cyl < 12)
X = np.column_stack([X_gc[mask], Y_gc[mask], Z_gc[mask],
                      vX[mask], vY[mask], vZ[mask]])
X = (X - X.mean(0)) / X.std(0)
X = X[:5000]
names = ['X', 'Y', 'Z', 'vX', 'vY', 'vZ']
print(f"Data: {X.shape}")

print("\n" + "=" * 60)
print("DEGREE-2 INVARIANTS (L1_symmetric)")
print("=" * 60)
Z2, n2 = lift_symmetric(X)
Z2c = Z2 - Z2.mean(0)
d2, v2 = find_min_variance_direction(Z2c, k=3)
for i in range(min(3, len(v2))):
    print(f"\n  C_{i+1}: variance = {v2[i]:.6e}")
    idx = np.argsort(np.abs(d2[i]))[::-1][:6]
    for j in idx:
        if abs(d2[i][j]) > 0.05:
            print(f"    {n2[j]:>12s}: {d2[i][j]:+.4f}")

print("\n" + "=" * 60)
print("DEGREE-3 INVARIANTS (L3_cubic)")
print("=" * 60)
Z3, n3 = lift_cubic(X)
Z3c = Z3 - Z3.mean(0)
d3, v3 = find_min_variance_direction(Z3c, k=2)
for i in range(min(2, len(v3))):
    print(f"\n  C_{i+1}: variance = {v3[i]:.6e}")
    idx = np.argsort(np.abs(d3[i]))[::-1][:6]
    for j in idx:
        if abs(d3[i][j]) > 0.05:
            print(f"    {n3[j]:>18s}: {d3[i][j]:+.4f}")

print("\n" + "=" * 60)
print("DEGREE-4 INVARIANTS (L6_quartic)")
print("=" * 60)
Z4, n4 = lift_quartic(X)
Z4c = Z4 - Z4.mean(0)
d4, v4 = find_min_variance_direction(Z4c, k=2)
for i in range(min(2, len(v4))):
    print(f"\n  C_{i+1}: variance = {v4[i]:.6e}")
    idx = np.argsort(np.abs(d4[i]))[::-1][:6]
    for j in idx:
        if abs(d4[i][j]) > 0.05:
            print(f"    {n4[j]:>18s}: {d4[i][j]:+.4f}")

print("\n" + "=" * 60)
print("DEGREE-5 INVARIANTS (L7_quintic)")
print("=" * 60)
Z5, n5 = lift_quintic(X)
Z5c = Z5 - Z5.mean(0)
d5, v5 = find_min_variance_direction(Z5c, k=2)
for i in range(min(2, len(v5))):
    print(f"\n  C_{i+1}: variance = {v5[i]:.6e}")
    idx = np.argsort(np.abs(d5[i]))[::-1][:6]
    for j in idx:
        if abs(d5[i][j]) > 0.05:
            print(f"    {n5[j]:>18s}: {d5[i][j]:+.4f}")

print("\n" + "=" * 60)
print("PROPAGATION DIAGNOSTIC")
print("=" * 60)
print(f"  Degree 1 variance: {find_min_variance_direction(X - X.mean(0), k=1)[1][0]:.6e}")
print(f"  Degree 2 variance: {v2[0]:.6e}")
print(f"  Degree 3 variance: {v3[0]:.6e}")
print(f"  Degree 4 variance: {v4[0]:.6e}")
print(f"  Degree 5 variance: {v5[0]:.6e}")

# The key test: if deg-5 variance ~ (deg-2 variance)^(5/2), it's pure propagation
# If deg-5 variance << (deg-2 variance)^(5/2), there's genuine new structure
ratio_expected = v2[0] ** 2.5  # propagation prediction
ratio_actual = v5[0]
print(f"\n  Propagation prediction (deg2^2.5): {ratio_expected:.6e}")
print(f"  Actual deg-5 variance:             {ratio_actual:.6e}")
print(f"  Ratio actual/predicted:            {ratio_actual / ratio_expected:.4f}")

if ratio_actual < ratio_expected * 0.01:
    print(f"\n  ** GENUINE NEW PHYSICS AT DEGREE 5 **")
    print(f"  The degree-5 invariant is NOT a product of degree-2 invariants.")
elif ratio_actual < ratio_expected * 0.1:
    print(f"\n  POSSIBLE NEW STRUCTURE at degree 5 (10x better than propagation)")
else:
    print(f"\n  PROPAGATION CONFIRMED: degree-5 variance consistent with")
    print(f"  algebraic consequences of degree-2 invariants.")
    print(f"  The fundamental conservation laws live at degree 2.")

# Also: compute the ACTUAL angular momentum and energy to verify
print("\n" + "=" * 60)
print("PHYSICAL INVARIANT CHECK")
print("=" * 60)
Xr = X_gc[mask][:5000]
Yr = Y_gc[mask][:5000]
vXr = vX[mask][:5000]
vYr = vY[mask][:5000]
vZr = vZ[mask][:5000]
Lz = Xr * vYr - Yr * vXr
v_sq = vXr**2 + vYr**2 + vZr**2
R_r = R_cyl[mask][:5000]

print(f"  L_z: mean={np.mean(Lz):.0f}, std={np.std(Lz):.0f}, CoV={np.std(Lz)/abs(np.mean(Lz)):.4f}")
print(f"  v^2: mean={np.mean(v_sq):.0f}, std={np.std(v_sq):.0f}, CoV={np.std(v_sq)/abs(np.mean(v_sq)):.4f}")
print(f"  R:   mean={np.mean(R_r):.2f}, std={np.std(R_r):.2f}")

# Test if L_z is the degree-2 invariant the engine found
Lz_norm = (Lz - np.mean(Lz)) / np.std(Lz)
# Reconstruct the degree-2 invariant from the engine's coefficients
q2 = Z2c @ d2[0]
q2_norm = (q2 - np.mean(q2)) / (np.std(q2) + 1e-12)
corr = np.abs(np.corrcoef(Lz_norm, q2_norm)[0, 1])
print(f"\n  Correlation between engine's C1 and L_z: {corr:.4f}")
print(f"  (1.0 = engine found exactly L_z; 0.0 = unrelated)")
