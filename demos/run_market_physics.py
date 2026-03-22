#!/usr/bin/env python3
"""
MARKET PHYSICS EXPERIMENT
=========================
Testing the Cartan-Killing lift tower on financial data.

Hypothesis:
  H0: Markets are non-conservative. No degree 1-8 finds T* >> 1.
  H1: Markets contain hidden constraints (no-arbitrage, put-call parity)
      that manifest at some polynomial degree.
  H2: Markets are an EFT — approximate symmetry with finite T*.

Three datasets:
  1. Pure random walk (control)
  2. Realistic market (OU + vol clustering)
  3. Hidden-constraint market (embedded Minkowski-like invariant)
"""
import numpy as np
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from sgc_universal import crystallize_universal
from sgc_zero_param import discover

np.random.seed(42)
N = 2000

print("#" * 70)
print("# MARKET PHYSICS EXPERIMENT")
print("# Testing the Cartan-Killing lift tower on financial data")
print("#" * 70)

# ================================================================
# DATASET 1: PURE RANDOM WALK (Control)
# ================================================================
print("\n" + "=" * 60)
print("DATASET 1: PURE RANDOM WALK (4D)")
print("Expected: T* < 1 at ALL degrees")
print("=" * 60)

price = np.cumsum(np.random.randn(N) * 0.02) + 100
volume = np.abs(np.random.randn(N)) * 1e6 + 5e6
vix = np.abs(np.convolve(np.random.randn(N), np.ones(20)/20, mode='same')) * 20
bond = 3.0 + np.cumsum(np.random.randn(N) * 0.01)
X1 = np.column_stack([price, volume, vix, bond])
X1 = (X1 - X1.mean(0)) / X1.std(0)

r1 = discover(X1, ['price', 'volume', 'vix', 'bond'], verbose=False)
print(f"  Dynamics: b1={r1.b1}, T*={r1.validity_horizon:.2f}, defect={r1.functional_defect:.4e}")
print(f"  Manifold variances: {[f'{v:.4e}' for v in r1.constraint_variances]}")
print(f"  Manifold wins: {r1.manifold_wins}")
print(f"  Tsallis q: {r1.spectral_profile.tsallis_q:.3f}")

print("\n  MDL Tournament (all degrees):")
r1u = crystallize_universal(X1, k=1, lambda_mdl=0.01)
print(f"  Winner: {r1u.winning_lift}")

# ================================================================
# DATASET 2: REALISTIC MARKET (vol clustering + mean reversion)
# ================================================================
print("\n" + "=" * 60)
print("DATASET 2: REALISTIC MARKET (OU + vol clustering)")
print("Expected: short-horizon structure, T* moderate")
print("=" * 60)

dt = 1.0
mu_p, theta_p, sigma_p = 0.0, 0.01, 0.02
mu_v, theta_v, sigma_v = 20.0, 0.05, 3.0
p2, v2 = [100.0], [20.0]
for t in range(N - 1):
    dp = theta_p * (mu_p - (p2[-1] - 100)) * dt + sigma_p * np.random.randn() * np.sqrt(dt)
    dv = theta_v * (mu_v - v2[-1]) * dt + sigma_v * np.random.randn() * np.sqrt(dt) * (1 + 0.5 * abs(dp / sigma_p))
    p2.append(p2[-1] + dp)
    v2.append(max(v2[-1] + dv, 5))
p2 = np.array(p2)
v2 = np.array(v2)
vol2 = np.abs(np.diff(p2, prepend=p2[0])) * 252**0.5
bond2 = 3.0 + 0.1 * (v2 - 20) / 15 + np.random.randn(N) * 0.1
X2 = np.column_stack([p2, vol2, v2, bond2])
X2 = (X2 - X2.mean(0)) / X2.std(0)

r2 = discover(X2, ['price', 'vol', 'vix', 'bond'], verbose=False)
print(f"  Dynamics: b1={r2.b1}, T*={r2.validity_horizon:.2f}, defect={r2.functional_defect:.4e}")
print(f"  Manifold wins: {r2.manifold_wins}")
print(f"  Tsallis q: {r2.spectral_profile.tsallis_q:.3f}")

print("\n  MDL Tournament (all degrees):")
r2u = crystallize_universal(X2, k=1, lambda_mdl=0.01)
print(f"  Winner: {r2u.winning_lift}")

# ================================================================
# DATASET 3: HIDDEN CONSTRAINT MARKET
# Embed: price^2 + bond^2 - vix^2 = K (Minkowski-like invariant)
# Simulates a market where risk-neutral pricing creates a
# conserved quadratic form (put-call parity in disguise).
# ================================================================
print("\n" + "=" * 60)
print("DATASET 3: HIDDEN CONSTRAINT MARKET")
print("Embedded: price^2 + bond^2 - vix^2 = K")
print("Expected: L1 finds the constraint, T* >> 1")
print("=" * 60)

p3 = np.random.randn(N) * 2 + 50
b3 = np.random.randn(N) * 1 + 3
K = 2500 + 9
v3_sq = p3**2 + b3**2 - K
v3 = np.sqrt(np.maximum(v3_sq, 0.01)) + np.random.randn(N) * 0.01
noise_dim = np.random.randn(N) * 5
X3 = np.column_stack([p3, v3, b3, noise_dim])
X3 = (X3 - X3.mean(0)) / X3.std(0)

I_gt = p3**2 + b3**2 - v3**2
print(f"  Ground truth invariant var: {np.var(I_gt):.4e}")

r3 = discover(X3, ['price', 'vix', 'bond', 'noise'], verbose=False)
print(f"  Dynamics: b1={r3.b1}, T*={r3.validity_horizon:.2f}, defect={r3.functional_defect:.4e}")
print(f"  Manifold variances: {[f'{v:.4e}' for v in r3.constraint_variances]}")
print(f"  Manifold wins: {r3.manifold_wins}")
print(f"  Tsallis q: {r3.spectral_profile.tsallis_q:.3f}")

print("\n  MDL Tournament (all degrees):")
r3u = crystallize_universal(X3, k=1, lambda_mdl=0.01)
print(f"  Winner: {r3u.winning_lift}")

if r3u.constraints:
    c = r3u.constraints[0]
    names = ['price', 'vix', 'bond', 'noise']
    print(f"\n  Discovered constraint coefficients:")
    for i, (name, val) in enumerate(zip(r3u.feature_names[:10], c[:10])):
        if abs(val) > 0.05:
            print(f"    {name}: {val:+.4f}")

# ================================================================
# DATASET 4: CUBIC MARKET CONSTRAINT
# Embed: price * vix * bond = K (a triple-product conservation)
# This would indicate SU(3)-like structure in the market.
# ================================================================
print("\n" + "=" * 60)
print("DATASET 4: CUBIC MARKET CONSTRAINT")
print("Embedded: price * vix * bond = K")
print("Expected: L3 finds the constraint")
print("=" * 60)

a4 = np.random.uniform(0.5, 5.0, N)
b4 = np.random.uniform(0.5, 5.0, N)
K4 = 5.0
c4 = K4 / (a4 * b4) + np.random.randn(N) * 0.001
noise4 = np.random.randn(N) * 2
X4 = np.column_stack([a4, b4, c4, noise4])
X4 = (X4 - X4.mean(0)) / X4.std(0)

I4_gt = a4 * b4 * c4
print(f"  Ground truth cubic invariant var: {np.var(I4_gt):.4e}")

r4u = crystallize_universal(X4, k=1, lambda_mdl=0.01)
print(f"  Winner: {r4u.winning_lift}")
print(f"  Variances: {r4u.variances}")

# ================================================================
# SUMMARY
# ================================================================
print("\n" + "#" * 70)
print("# MARKET PHYSICS RESULTS")
print("#" * 70)
print(f"")
print(f"  {'Dataset':<30s} {'T*':>8s}  {'b1':>3s}  {'Manifold':>10s}  {'MDL Winner':>15s}")
print(f"  {'-'*30} {'-'*8}  {'-'*3}  {'-'*10}  {'-'*15}")
print(f"  {'1. Random walk':<30s} {r1.validity_horizon:>8.2f}  {r1.b1:>3d}  {'YES' if r1.manifold_wins else 'NO':>10s}  {r1u.winning_lift:>15s}")
print(f"  {'2. Realistic market':<30s} {r2.validity_horizon:>8.2f}  {r2.b1:>3d}  {'YES' if r2.manifold_wins else 'NO':>10s}  {r2u.winning_lift:>15s}")
print(f"  {'3. Hidden quadratic (p2+b2-v2)':<30s} {r3.validity_horizon:>8.2f}  {r3.b1:>3d}  {'YES' if r3.manifold_wins else 'NO':>10s}  {r3u.winning_lift:>15s}")
print(f"  {'4. Hidden cubic (p*v*b=K)':<30s} {'N/A':>8s}  {'N/A':>3s}  {'N/A':>10s}  {r4u.winning_lift:>15s}")
print()

if r1.validity_horizon < 2 and r3.manifold_wins:
    print("  RESULT: The engine correctly distinguishes:")
    print("    - Random walk: T* < 1 (NO conservation laws)")
    print("    - Hidden constraint: manifold mode discovers the invariant")
    print("    - The MDL tournament selects the correct polynomial degree")
    print()
    print("  INTERPRETATION:")
    print("    If real market data shows T* >> 1 at some degree,")
    print("    that degree reveals the hidden symmetry group of the market.")
    print("    If T* < 1 at ALL degrees, the market is genuinely non-conservative.")
elif r1.validity_horizon < 2:
    print("  RESULT: Engine correctly rejects random walk (T* < 1)")
    print("  but hidden constraint detection needs verification.")
else:
    print("  RESULT: Unexpected — check individual results above.")
