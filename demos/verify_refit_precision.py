#!/usr/bin/env python3
"""
Final precision test: Are the refit coefficients bx, by, bz equal?

Two tests:
1. Print the 2-parameter refit (a, b) coefficients to 8 sig figs
   for both muon blocks. Since the refit uses Cov([E^2, |p|^2]),
   it forces bx=by=bz=b by construction. Report this constraint.

2. Run the UNCONSTRAINED 4-parameter refit: diag(a, bx, by, bz)
   minimizing Var[a*E^2 + bx*px^2 + by*py^2 + bz*pz^2].
   This is the minimum eigenvector of the 4x4 covariance matrix
   Cov([E^2, px^2, py^2, pz^2]). If bx != bz, the detector
   geometry is visible. Report |bx-bz|/|bx| for the isotropy test.

3. Run on simulated isotropic muons to confirm the engine finds
   exact eta when the data is isotropic.
"""
import numpy as np
import sys, os, csv
sys.path.insert(0, os.path.dirname(__file__))
from sgc_relational_engine import load_cern_dimuon

csv_path = os.path.join(os.path.dirname(__file__), '..', 'data', 'MuRun2010B.csv')
csv_path = os.path.normpath(csv_path)
X_raw, M_oracle = load_cern_dimuon(csv_path)
global_scale = np.std(X_raw)
X = X_raw / global_scale

print("=" * 70)
print("REFIT PRECISION DIAGNOSTIC")
print("=" * 70)

for muon_name, sl in [("Muon 1", slice(0, 4)), ("Muon 2", slice(4, 8))]:
    x = X[:, sl]  # (N, 4)
    E_sq = x[:, 0] ** 2
    px_sq = x[:, 1] ** 2
    py_sq = x[:, 2] ** 2
    pz_sq = x[:, 3] ** 2
    p_sq = px_sq + py_sq + pz_sq

    print(f"\n{'=' * 70}")
    print(f"{muon_name}")
    print(f"{'=' * 70}")

    # ============================================================
    # TEST 1: 2-parameter refit (a, b) — forces bx=by=bz
    # ============================================================
    features_2 = np.column_stack([E_sq, p_sq])
    Sigma_2 = np.cov(features_2, rowvar=False)
    evals_2, evecs_2 = np.linalg.eigh(Sigma_2)
    min_dir_2 = evecs_2[:, 0]
    a_2, b_2 = min_dir_2
    # Ensure a > 0 (energy positive convention)
    if a_2 < 0:
        a_2, b_2 = -a_2, -b_2

    # Variance achieved
    q_2 = a_2 * E_sq + b_2 * p_sq
    var_2 = np.var(q_2)
    # Normalize
    norm_2 = np.sqrt(a_2**2 + 3*b_2**2)

    print(f"\n  2-parameter refit (a, b) [forces bx=by=bz=b]:")
    print(f"    a  = {a_2:+.10f}")
    print(f"    b  = {b_2:+.10f}")
    print(f"    b/a = {b_2/a_2:+.10f}  (exact Minkowski: -1.0)")
    print(f"    |b/a - (-1)| = {abs(b_2/a_2 - (-1)):.2e}")
    print(f"    Variance: {var_2:.6e}")

    # ============================================================
    # TEST 2: 4-parameter refit (a, bx, by, bz) — unconstrained
    # ============================================================
    features_4 = np.column_stack([E_sq, px_sq, py_sq, pz_sq])
    Sigma_4 = np.cov(features_4, rowvar=False)
    evals_4, evecs_4 = np.linalg.eigh(Sigma_4)
    min_dir_4 = evecs_4[:, 0]
    a_4, bx_4, by_4, bz_4 = min_dir_4
    if a_4 < 0:
        a_4, bx_4, by_4, bz_4 = -a_4, -bx_4, -by_4, -bz_4

    q_4 = a_4 * E_sq + bx_4 * px_sq + by_4 * py_sq + bz_4 * pz_sq
    var_4 = np.var(q_4)

    print(f"\n  4-parameter refit (a, bx, by, bz) [unconstrained]:")
    print(f"    a  = {a_4:+.10f}")
    print(f"    bx = {bx_4:+.10f}")
    print(f"    by = {by_4:+.10f}")
    print(f"    bz = {bz_4:+.10f}")
    print(f"    bx/a = {bx_4/a_4:+.10f}")
    print(f"    by/a = {by_4/a_4:+.10f}")
    print(f"    bz/a = {bz_4/a_4:+.10f}")
    print(f"    Exact Minkowski: all ratios = -1.0")
    print(f"    Variance: {var_4:.6e}")
    print(f"    Variance improvement over 2-param: "
          f"{var_2/var_4:.4f}x")

    # Isotropy test
    b_mean = (bx_4 + by_4 + bz_4) / 3
    print(f"\n  ISOTROPY TEST:")
    print(f"    |bx - by| / |bx| = {abs(bx_4 - by_4) / abs(bx_4):.6e}")
    print(f"    |bx - bz| / |bx| = {abs(bx_4 - bz_4) / abs(bx_4):.6e}")
    print(f"    |by - bz| / |by| = {abs(by_4 - bz_4) / abs(by_4):.6e}")
    max_aniso = max(abs(bx_4 - by_4), abs(bx_4 - bz_4), abs(by_4 - bz_4)) / abs(b_mean)
    print(f"    Max anisotropy: {max_aniso:.6e}")
    if max_aniso < 1e-4:
        print(f"    VERDICT: ISOTROPIC to < 0.01% — exact Lorentz invariance")
    elif max_aniso < 0.01:
        print(f"    VERDICT: NEAR-ISOTROPIC ({max_aniso*100:.2f}%) — "
              f"Lorentz-like, minor detector effect")
    else:
        print(f"    VERDICT: ANISOTROPIC ({max_aniso*100:.1f}%) — "
              f"detector beam-axis geometry visible")

    # Physical meaning
    print(f"\n  Physical interpretation:")
    print(f"    The 4-param constraint is: "
          f"{a_4:.6f}*E^2 + {bx_4:.6f}*px^2 + {by_4:.6f}*py^2 + {bz_4:.6f}*pz^2 = const")
    m_sq_eff = np.mean(a_4 * E_sq + bx_4 * px_sq + by_4 * py_sq + bz_4 * pz_sq) * global_scale**2
    print(f"    Effective mass^2: {m_sq_eff:.6f} GeV^2 (m_mu^2 = 0.0112)")

    # Report the 4x4 Sigma matrix structure
    print(f"\n  Cov([E^2, px^2, py^2, pz^2]):")
    print(f"    {np.array2string(Sigma_4, precision=6, suppress_small=True)}")
    print(f"    Eigenvalues: {evals_4}")

# ============================================================
# TEST 3: Simulated isotropic muons
# ============================================================
print(f"\n{'=' * 70}")
print("TEST 3: SIMULATED ISOTROPIC MUONS")
print("=" * 70)

np.random.seed(42)
N_sim = 100000
m_mu = 0.10566  # muon mass in GeV

# Generate isotropic muon 4-vectors
# Random |p| from exponential distribution (rough approximation)
p_mag = np.random.exponential(5.0, size=N_sim)  # mean 5 GeV
# Isotropic direction
cos_theta = 2 * np.random.rand(N_sim) - 1
sin_theta = np.sqrt(1 - cos_theta**2)
phi = 2 * np.pi * np.random.rand(N_sim)

px_sim = p_mag * sin_theta * np.cos(phi)
py_sim = p_mag * sin_theta * np.sin(phi)
pz_sim = p_mag * cos_theta
E_sim = np.sqrt(px_sim**2 + py_sim**2 + pz_sim**2 + m_mu**2)

# Scale
sim_scale = np.std(np.column_stack([E_sim, px_sim, py_sim, pz_sim]))
x_sim = np.column_stack([E_sim, px_sim, py_sim, pz_sim]) / sim_scale

# Verify mass shell
eta = np.diag([1, -1, -1, -1])
m_sq_check = np.var(np.einsum('ni,ij,nj->n', x_sim, eta/2, x_sim))
print(f"  Simulated mass shell var (eta/2): {m_sq_check:.6e}")

# 4-parameter refit on isotropic data
E_sq_s = x_sim[:, 0] ** 2
px_sq_s = x_sim[:, 1] ** 2
py_sq_s = x_sim[:, 2] ** 2
pz_sq_s = x_sim[:, 3] ** 2

features_sim = np.column_stack([E_sq_s, px_sq_s, py_sq_s, pz_sq_s])
Sigma_sim = np.cov(features_sim, rowvar=False)
evals_sim, evecs_sim = np.linalg.eigh(Sigma_sim)
min_dir_sim = evecs_sim[:, 0]
a_s, bx_s, by_s, bz_s = min_dir_sim
if a_s < 0:
    a_s, bx_s, by_s, bz_s = -a_s, -bx_s, -by_s, -bz_s

print(f"\n  4-parameter refit on ISOTROPIC simulated muons:")
print(f"    a  = {a_s:+.10f}")
print(f"    bx = {bx_s:+.10f}")
print(f"    by = {by_s:+.10f}")
print(f"    bz = {bz_s:+.10f}")
print(f"    bx/a = {bx_s/a_s:+.10f}")
print(f"    by/a = {by_s/a_s:+.10f}")
print(f"    bz/a = {bz_s/a_s:+.10f}")

b_mean_s = (bx_s + by_s + bz_s) / 3
max_aniso_s = max(abs(bx_s-by_s), abs(bx_s-bz_s), abs(by_s-bz_s)) / abs(b_mean_s)
print(f"\n  ISOTROPY TEST (simulated):")
print(f"    Max anisotropy: {max_aniso_s:.6e}")
if max_aniso_s < 1e-2:
    print(f"    VERDICT: ISOTROPIC — engine recovers exact eta from isotropic data")
else:
    print(f"    VERDICT: Anisotropic even on isotropic data — engine issue")

q_sim = a_s * E_sq_s + bx_s * px_sq_s + by_s * py_sq_s + bz_s * pz_sq_s
print(f"    Achieved variance: {np.var(q_sim):.6e}")

print(f"\n{'=' * 70}")
print("DIAGNOSTIC COMPLETE")
print("=" * 70)
