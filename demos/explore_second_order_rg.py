#!/usr/bin/env python3
"""
THE NEW CONTINENT: Second-Order Coarse-Graining Theory
========================================================

Tests the Wilsonian effective action L_eff = L_bar + D*L_fine^-1*D
on an ASYMMETRIC 4-state chain with non-uniform pi and approximate
(not exact) lumpability.

THREE QUESTIONS:
Q1: Does L_eff give a better trajectory bound than L_bar? (O(eps^2*t) vs O(eps*t))
Q2: Does autopoietic depth d equal the number of spectral gap separations?
Q3: Does gamma_q vary with q when pi is non-uniform?
"""
import numpy as np
from scipy.linalg import expm

np.set_printoptions(precision=8, suppress=True)


def inner_pi(pi, f, g):
    return np.sum(pi * f * g)

def norm_pi(pi, f):
    return np.sqrt(inner_pi(pi, f, f))

def coarse_proj(pi, partition, f):
    n = len(pi)
    blocks = {}
    for i, b in enumerate(partition):
        blocks.setdefault(b, []).append(i)
    result = np.zeros(n)
    for block_id, members in blocks.items():
        pi_block = sum(pi[m] for m in members)
        if pi_block > 0:
            avg = sum(pi[m] * f[m] for m in members) / pi_block
            for m in members:
                result[m] = avg
    return result

def quotient_system(L, pi, partition):
    blocks = {}
    for i, b in enumerate(partition):
        blocks.setdefault(b, []).append(i)
    block_ids = sorted(blocks.keys())
    nb = len(block_ids)
    pi_bar = np.zeros(nb)
    L_bar = np.zeros((nb, nb))
    for a, a_id in enumerate(block_ids):
        pi_bar[a] = sum(pi[m] for m in blocks[a_id])
        for b, b_id in enumerate(block_ids):
            if pi_bar[a] > 0:
                L_bar[a, b] = sum(pi[x]*L[x,y] for x in blocks[a_id] for y in blocks[b_id]) / pi_bar[a]
    return L_bar, pi_bar


print("#" * 70)
print("# THE NEW CONTINENT: Second-Order Coarse-Graining")
print("#" * 70)

# ============================================================
# THE ASYMMETRIC CHAIN
# States: {0, 1, 2, 3}
# Partition: {0,1} | {2,3}
# ASYMMETRIC: different intra-block rates, different inter-block rates
# This breaks Z2 symmetry and makes pi non-uniform.
# ============================================================

# Block 0: fast coupling between 0 and 1
a01 = 2.0  # rate 0->1
a10 = 1.0  # rate 1->0 (asymmetric!)

# Block 1: slower coupling between 2 and 3
a23 = 0.8
a32 = 1.5

# Inter-block: weak and asymmetric
b02 = 0.15  # 0->2
b13 = 0.10  # 1->3
b20 = 0.05  # 2->0
b31 = 0.08  # 3->1

L = np.array([
    [-(a01+b02), a01, b02, 0],
    [a10, -(a10+b13), 0, b13],
    [b20, 0, -(a23+b20), a23],
    [0, b31, a32, -(a32+b31)],
])

# Compute stationary distribution: pi @ L = 0, sum(pi) = 1
eigvals, eigvecs = np.linalg.eig(L.T)
idx = np.argmin(np.abs(eigvals))
pi = np.real(eigvecs[:, idx])
pi = pi / np.sum(pi)
pi = np.abs(pi)

print(f"\nAsymmetric generator L:")
print(L)
print(f"\nStationary pi = {pi}")
print(f"pi is uniform? {np.allclose(pi, pi[0])}")
assert not np.allclose(pi, pi[0]), "pi should be non-uniform!"
print(f"Verify pi@L = 0: {np.allclose(pi @ L, 0, atol=1e-8)}")

partition = [0, 0, 1, 1]

# Eigenvalues of L
L_eigs = np.sort(np.linalg.eigvals(L).real)
print(f"\nEigenvalues of L: {L_eigs}")
print(f"Spectral gap (2nd smallest |lambda|): {-L_eigs[-2]:.6f}")

# ============================================================
# Q1: SECOND-ORDER TRAJECTORY BOUND
# Compare L_bar (tree-level) vs L_eff (one-loop) as predictors
# ============================================================
print(f"\n{'='*60}")
print("Q1: SECOND-ORDER TRAJECTORY BOUND")
print("Does L_eff = L_bar + D*L_fine^-1*D give O(eps^2*t)?")
print(f"{'='*60}")

# Quotient generator (tree-level)
L_bar, pi_bar = quotient_system(L, pi, partition)
print(f"\nQuotient generator L_bar:\n{L_bar}")

# Block decomposition
blocks = {0: [0,1], 1: [2,3]}
# Build the block matrices
L_AA = L[np.ix_([0,1],[0,1])]  # intra-block 0
L_BB = L[np.ix_([2,3],[2,3])]  # intra-block 1
D_AB = L[np.ix_([0,1],[2,3])]  # block 0 -> block 1
D_BA = L[np.ix_([2,3],[0,1])]  # block 1 -> block 0

print(f"\nL_AA (intra-block 0): {L_AA}")
print(f"L_BB (intra-block 1): {L_BB}")
print(f"D_AB (0->1): {D_AB}")
print(f"D_BA (1->0): {D_BA}")

# Schur complement: L_eff = L_AA - D_AB @ L_BB^{-1} @ D_BA (for block 0)
# But L_BB is singular. Use pseudoinverse.
L_BB_pinv = np.linalg.pinv(L_BB)
self_energy = D_AB @ L_BB_pinv @ D_BA
L_eff_block0 = L_AA - self_energy

print(f"\nSelf-energy (one-loop correction):\n{self_energy}")
print(f"L_eff (block 0, Schur complement):\n{L_eff_block0}")

# Now: compare trajectory errors
# Pick a test function that is block-constant
f0 = np.array([1.0, 1.0, 0.0, 0.0])  # indicator of block 0
f0 = f0 - inner_pi(pi, f0, np.ones(4)) / inner_pi(pi, np.ones(4), np.ones(4))  # mean-zero

# Compute the defect
pf0 = coarse_proj(pi, partition, f0)
Lpf0 = L @ pf0
Df0 = Lpf0 - coarse_proj(pi, partition, Lpf0)
eps = norm_pi(pi, Df0) / norm_pi(pi, f0) if norm_pi(pi, f0) > 1e-12 else 0

print(f"\nDefect epsilon = ||Df||/||f|| = {eps:.8f}")

# Trajectory comparison at various times
print(f"\n  {'t':>6s}  {'||exact - L_bar||':>18s}  {'||exact - L_eff||':>18s}  {'eps*t*C':>12s}  {'eps^2*t*C':>12s}")
print(f"  {'-'*6}  {'-'*18}  {'-'*18}  {'-'*12}  {'-'*12}")

# Build the LIFTED L_bar as a 4x4 matrix for trajectory comparison
# L_bar acts on block-constant functions via the quotient
def lift_quotient_evolution(L_bar_2x2, pi_bar_2x2, partition_4, t):
    """Compute e^{t*L_bar} lifted to the full 4-state space."""
    exp_Lbar = expm(t * L_bar_2x2)
    # Lift: block-constant evolution
    result = np.zeros((4, 4))
    blocks_local = {0: [0,1], 1: [2,3]}
    for i in range(4):
        bi = partition_4[i]
        for bj_idx, bj_id in enumerate(sorted(blocks_local.keys())):
            for j in blocks_local[bj_id]:
                result[i, j] = exp_Lbar[bi, bj_idx] * pi[j] / pi_bar_2x2[bj_idx]
    return result

C = norm_pi(pi, f0)
for t in [0.1, 0.5, 1.0, 2.0, 5.0, 10.0, 20.0]:
    # Exact evolution
    exact = expm(t * L) @ f0

    # Tree-level (L_bar) evolution: project, evolve on quotient, lift back
    pf = coarse_proj(pi, partition, f0)
    # Evolve the block averages
    f_bar = np.array([inner_pi(pi, pf, np.array([1,1,0,0])) / pi_bar[0],
                       inner_pi(pi, pf, np.array([0,0,1,1])) / pi_bar[1]])
    evolved_bar = expm(t * L_bar) @ f_bar
    # Lift back
    tree_level = np.zeros(4)
    for i in range(4):
        bi = partition[i]
        tree_level[i] = evolved_bar[bi]

    err_tree = norm_pi(pi, exact - tree_level)
    err_bound1 = eps * t * C

    # One-loop (L_eff) evolution: use the full Schur complement
    # This is harder because L_eff is 2x2 (block 0 Schur complement)
    # For a fair comparison, compute the FULL 4x4 effective evolution
    # using the Schur complement for BOTH blocks
    L_AA_pinv = np.linalg.pinv(L_AA)
    self_energy_B = D_BA @ L_AA_pinv @ D_AB
    L_eff_block1 = L_BB - self_energy_B

    # Build full 4x4 effective generator
    L_eff_full = np.zeros((4, 4))
    L_eff_full[np.ix_([0,1],[0,1])] = L_eff_block0
    L_eff_full[np.ix_([2,3],[2,3])] = L_eff_block1
    # Keep inter-block coupling
    L_eff_full[np.ix_([0,1],[2,3])] = D_AB
    L_eff_full[np.ix_([2,3],[0,1])] = D_BA

    one_loop = expm(t * L_eff_full) @ f0
    err_loop = norm_pi(pi, exact - one_loop)
    err_bound2 = eps**2 * t * C

    print(f"  {t:>6.1f}  {err_tree:>18.8f}  {err_loop:>18.8f}  {err_bound1:>12.6f}  {err_bound2:>12.8f}")

# ============================================================
# Q2: AUTOPOIETIC DEPTH vs SPECTRAL GAPS
# ============================================================
print(f"\n{'='*60}")
print("Q2: AUTOPOIETIC DEPTH vs SPECTRAL GAP SEPARATIONS")
print(f"{'='*60}")

eigs = np.sort(-np.linalg.eigvals(L).real)  # positive eigenvalues of -L
print(f"\nEigenvalues of -L (sorted): {eigs}")

# Count spectral gap separations: ratio > 3 between consecutive eigenvalues
gaps = []
for i in range(len(eigs)-1):
    if eigs[i] > 1e-10 and eigs[i+1] > 1e-10:
        ratio = eigs[i+1] / eigs[i]
        gaps.append((i, eigs[i], eigs[i+1], ratio))
        print(f"  Gap {i}: {eigs[i]:.4f} -> {eigs[i+1]:.4f}, ratio = {ratio:.2f}")

n_separations = sum(1 for _, _, _, r in gaps if r > 3)
print(f"\nSpectral gap separations (ratio > 3): {n_separations}")
print(f"Autopoietic depth d: need to compute RG tower...")

# Run RG tower
from itertools import product as iprod
def find_optimal_partition_brute(L_loc, pi_loc, n):
    best_defect = float('inf')
    best_partition = list(range(n))
    partitions_seen = set()
    for labels in iprod(range(n), repeat=n):
        mapping = {}; counter = 0; canonical = []
        for l in labels:
            if l not in mapping: mapping[l] = counter; counter += 1
            canonical.append(mapping[l])
        canonical = tuple(canonical)
        if canonical in partitions_seen: continue
        partitions_seen.add(canonical)
        n_blocks = len(set(canonical))
        if n_blocks == 1 or n_blocks == n: continue
        # Compute defect for this partition
        proj = lambda f: coarse_proj(pi_loc, list(canonical), f)
        total_defect = 0
        for trial in range(200):
            f = np.random.randn(n)
            f -= inner_pi(pi_loc, f, np.ones(n)) / inner_pi(pi_loc, np.ones(n), np.ones(n))
            nf = norm_pi(pi_loc, f)
            if nf > 1e-10:
                pf_loc = proj(f)
                Lpf = L_loc @ pf_loc
                Df = Lpf - proj(Lpf)
                total_defect = max(total_defect, norm_pi(pi_loc, Df) / nf)
        if total_defect < best_defect:
            best_defect = total_defect
            best_partition = list(canonical)
    return best_partition, best_defect

L_cur, pi_cur, n_cur = L.copy(), pi.copy(), 4
depth = 0
for level in range(5):
    if n_cur <= 1: break
    P_opt, eps_opt = find_optimal_partition_brute(L_cur, pi_cur, n_cur)
    n_blocks = len(set(P_opt))
    print(f"  Level {level}: |V|={n_cur}, P={P_opt}, eps={eps_opt:.6e}")
    if n_blocks == n_cur or n_blocks <= 1:
        print(f"  Terminal at level {level}")
        break
    depth += 1
    L_cur, pi_cur = quotient_system(L_cur, pi_cur, P_opt)
    n_cur = n_blocks

print(f"\nAutopoietic depth d = {depth}")
print(f"Spectral gap separations = {n_separations}")
print(f"d == n_separations? {depth == n_separations}")

# ============================================================
# Q3: GAMMA_Q vs Q ON NON-UNIFORM PI
# ============================================================
print(f"\n{'='*60}")
print("Q3: ESCORT-WEIGHTED SPECTRAL GAP ON NON-UNIFORM PI")
print(f"{'='*60}")

def escort_spectral_gap(L_loc, pi_loc, q, n_samples=20000):
    n = len(pi_loc)
    Z_q = np.sum(pi_loc**q)
    best = float('inf')
    for _ in range(n_samples):
        f = np.random.randn(n)
        mean_q = np.sum(pi_loc**q * f) / Z_q
        f -= mean_q
        var_q = np.sum(pi_loc**q * f**2) / Z_q
        if var_q > 1e-12:
            E_q = 0
            for x in range(n):
                for y in range(n):
                    if x != y and L_loc[x,y] > 0:
                        E_q += pi_loc[x]**q * L_loc[x,y] * (f[y]-f[x])**2
            E_q = 0.5 * E_q / Z_q
            ratio = E_q / var_q
            if ratio < best:
                best = ratio
    return best

gamma_1 = escort_spectral_gap(L, pi, 1.0)
print(f"\nStandard gamma_1 = {gamma_1:.6f}")
print(f"pi = {pi} (NON-UNIFORM)")

q_vals = [1.0, 1.1, 1.2, 1.3, 1.4, 1.5, 1.6, 1.7, 1.8, 1.9]
print(f"\n  {'q':>5s}  {'gamma_q':>10s}  {'gamma_q/g1':>12s}  {'g1^(2-q)':>12s}  {'ratio':>8s}")
print(f"  {'-'*5}  {'-'*10}  {'-'*12}  {'-'*12}  {'-'*8}")
for q in q_vals:
    gq = escort_spectral_gap(L, pi, q)
    pred = gamma_1 ** (2-q)
    r = gq / pred if pred > 1e-12 else 0
    print(f"  {q:>5.1f}  {gq:>10.6f}  {gq/gamma_1:>12.6f}  {pred:>12.6f}  {r:>8.4f}")

print(f"\n{'#'*70}")
print("# EXPLORATION COMPLETE")
print(f"{'#'*70}")
