#!/usr/bin/env python3
"""
VOYAGE OF EXPLORATION: The Five Continents
=============================================

Three numerical experiments on the simplest non-trivial Markov chain
to test three theoretical predictions before formalizing anything.

Experiment 1: Defect-Dirichlet Duality
  Is E(f_block) = ||D_P f_block||^2 / ||f_block||^2 ?
  If yes: fluctuation-dissipation theorem for finite Markov chains.

Experiment 2: RG Tower Termination
  Apply optimal partition -> quotient -> optimal partition -> ...
  Does it terminate? In how many steps? What is the terminal defect?

Experiment 3: gamma_q vs q Scaling
  Compute the escort-weighted Dirichlet form at multiple q values.
  Does gamma_q ~ gamma^{2-q} hold? Or is the scaling different?

Plus two deeper investigations:
  Schur complement connection (Continent 4)
  Coarse-graining criticality threshold (Continent 5)
"""
import numpy as np
from itertools import product as cartprod

np.set_printoptions(precision=6, suppress=True)


def inner_pi(pi, f, g):
    """Weighted inner product <f, g>_pi = sum pi(v) f(v) g(v)."""
    return np.sum(pi * f * g)


def norm_sq_pi(pi, f):
    return inner_pi(pi, f, f)


def norm_pi(pi, f):
    return np.sqrt(norm_sq_pi(pi, f))


def coarse_projector(pi, partition):
    """Coarse projector Pi: f -> block-constant conditional expectation."""
    n = len(pi)
    blocks = {}
    for i, b in enumerate(partition):
        blocks.setdefault(b, []).append(i)

    def project(f):
        result = np.zeros(n)
        for block_id, members in blocks.items():
            pi_block = sum(pi[m] for m in members)
            if pi_block > 0:
                avg = sum(pi[m] * f[m] for m in members) / pi_block
                for m in members:
                    result[m] = avg
        return result
    return project


def defect_operator(L, pi, partition):
    """D_P f = (I - Pi)(L @ Pi f)."""
    proj = coarse_projector(pi, partition)

    def D(f):
        pf = proj(f)
        Lpf = L @ pf
        return Lpf - proj(Lpf)
    return D


def dirichlet_form(L, pi, f):
    """E(f) = <f, Lf>_pi."""
    Lf = L @ f
    return inner_pi(pi, f, Lf)


def op_norm_pi(pi, linear_op, n_samples=10000):
    """Estimate operator norm ||T||_pi = sup ||Tf||_pi / ||f||_pi."""
    d = len(pi)
    best = 0.0
    for _ in range(n_samples):
        f = np.random.randn(d)
        f -= inner_pi(pi, f, np.ones(d)) / inner_pi(pi, np.ones(d), np.ones(d)) * np.ones(d)
        nf = norm_pi(pi, f)
        if nf > 1e-12:
            Tf = linear_op(f)
            best = max(best, norm_pi(pi, Tf) / nf)
    return best


print("#" * 70)
print("# VOYAGE OF EXPLORATION: THE FIVE CONTINENTS")
print("#" * 70)

# ============================================================
# THE SPECIMEN: A 4-state chain with 2 blocks
# ============================================================
# States: {0, 1, 2, 3}
# Partition: P = {0,1} | {2,3}  (two blocks of size 2)
#
# Generator L (continuous-time Markov):
#   - Strong intra-block coupling (fast mixing within blocks)
#   - Weak inter-block coupling (slow mixing between blocks)
#   - Row sums = 0 (generator property)
#   - Off-diagonal >= 0

alpha = 1.0   # intra-block rate
beta = 0.1    # inter-block rate (the "leak")

L = np.array([
    [-(alpha + beta),  alpha,           beta,             0           ],
    [ alpha,          -(alpha + beta),   0,               beta        ],
    [ beta,            0,              -(alpha + beta),   alpha       ],
    [ 0,               beta,            alpha,           -(alpha + beta)],
])

# Stationary distribution: uniform (by symmetry)
pi = np.array([0.25, 0.25, 0.25, 0.25])

# Verify: pi @ L = 0
assert np.allclose(pi @ L, 0, atol=1e-10), f"Not stationary: {pi @ L}"

partition = [0, 0, 1, 1]  # block 0 = {0,1}, block 1 = {2,3}

print(f"\nGenerator L (alpha={alpha}, beta={beta}):")
print(L)
print(f"Stationary pi = {pi}")
print(f"Partition: {partition}")

# ============================================================
# CONTINENT 1: DEFECT-DIRICHLET DUALITY
# ============================================================
print(f"\n{'='*60}")
print("CONTINENT 1: DEFECT-DIRICHLET DUALITY")
print(f"{'='*60}")
print("Question: Is E(f_block) = ||D f_block||^2_pi / ||f_block||^2_pi ?")

D = defect_operator(L, pi, partition)
proj = coarse_projector(pi, partition)

# Block indicator function: f = [1, 1, -1, -1] (mean-zero block indicator)
f_block = np.array([1.0, 1.0, -1.0, -1.0])
f_block -= inner_pi(pi, f_block, np.ones(4))  # ensure mean-zero

# Compute both sides
E_f = dirichlet_form(L, pi, f_block)
Df = D(f_block)
defect_ratio = norm_sq_pi(pi, Df) / norm_sq_pi(pi, f_block)

print(f"\n  f_block = {f_block}")
print(f"  E(f_block) = <f, Lf>_pi = {E_f:.8f}")
print(f"  ||D f_block||^2_pi / ||f_block||^2_pi = {defect_ratio:.8f}")
print(f"  Ratio E / defect_ratio = {E_f / defect_ratio:.8f}")

if abs(E_f - defect_ratio) < 1e-8:
    print(f"\n  *** EXACT DUALITY: E(f) = ||Df||^2/||f||^2 ***")
elif abs(E_f - defect_ratio) / abs(E_f) < 0.01:
    print(f"\n  ** Approximate duality (< 1% error) **")
else:
    print(f"\n  Duality does NOT hold exactly.")
    print(f"  Difference: {abs(E_f - defect_ratio):.8e}")
    print(f"  Relative: {abs(E_f - defect_ratio) / abs(E_f):.4f}")

# Also check: what IS D f_block?
print(f"\n  D(f_block) = {Df}")
print(f"  L @ f_block = {L @ f_block}")
print(f"  Pi(L @ f_block) = {proj(L @ f_block)}")

# Decompose: E(f) = <f, L_bar f> + <f, Df>
L_bar_f = proj(L @ proj(f_block))  # coarse generator applied to f
inner_coarse = inner_pi(pi, f_block, L_bar_f)
inner_defect = inner_pi(pi, f_block, Df)
print(f"\n  Decomposition: E(f) = <f, L_bar f> + <f, Df>")
print(f"    <f, L_bar f>_pi = {inner_coarse:.8f}")
print(f"    <f, Df>_pi      = {inner_defect:.8f}")
print(f"    Sum             = {inner_coarse + inner_defect:.8f}")
print(f"    E(f)            = {E_f:.8f}")
print(f"    Match: {abs(E_f - (inner_coarse + inner_defect)) < 1e-10}")

# The key question: is <f, Df> = ||Df||^2 / ||f||^2 * ||f||^2 = ||Df||^2 ?
print(f"\n  <f, Df>_pi         = {inner_defect:.8f}")
print(f"  ||Df||^2_pi        = {norm_sq_pi(pi, Df):.8f}")
print(f"  Are they equal?    {abs(inner_defect - norm_sq_pi(pi, Df)) < 1e-10}")

# Try multiple block-constant functions
print(f"\n  Testing on multiple block-constant functions:")
for a, b in [(1, -1), (2, -1), (1, -3), (0.5, -2)]:
    f = np.array([a, a, b, b], dtype=float)
    f -= inner_pi(pi, f, np.ones(4))
    if norm_pi(pi, f) < 1e-10:
        continue
    Ef = dirichlet_form(L, pi, f)
    Df_val = D(f)
    defect_sq = norm_sq_pi(pi, Df_val)
    inner_fDf = inner_pi(pi, f, Df_val)
    print(f"    f=[{a},{a},{b},{b}]: E={Ef:.6f}  <f,Df>={inner_fDf:.6f}  "
          f"||Df||^2={defect_sq:.6f}  E=<f,Lbar_f>+<f,Df>: "
          f"{abs(Ef - (inner_pi(pi, f, proj(L @ proj(f))) + inner_fDf)) < 1e-10}")

# ============================================================
# CONTINENT 2: RG TOWER TERMINATION
# ============================================================
print(f"\n{'='*60}")
print("CONTINENT 2: RG TOWER TERMINATION")
print(f"{'='*60}")

def find_optimal_partition(L, pi, n):
    """Brute-force find the partition minimizing defect norm."""
    best_defect = float('inf')
    best_partition = list(range(n))  # trivial (discrete)

    # Generate all partitions of n elements (Bell number grows fast)
    # For n=4, Bell(4) = 15 — tractable
    from itertools import product as iprod
    # Generate partitions as equivalence classes
    partitions_seen = set()
    for labels in iprod(range(n), repeat=n):
        # Normalize: relabel to canonical form
        mapping = {}
        counter = 0
        canonical = []
        for l in labels:
            if l not in mapping:
                mapping[l] = counter
                counter += 1
            canonical.append(mapping[l])
        canonical = tuple(canonical)
        if canonical in partitions_seen:
            continue
        partitions_seen.add(canonical)

        # Skip trivial partitions (all same block or all different)
        n_blocks = len(set(canonical))
        if n_blocks == 1 or n_blocks == n:
            continue

        D_p = defect_operator(L, pi, list(canonical))
        eps = op_norm_pi(pi, D_p, n_samples=5000)
        if eps < best_defect:
            best_defect = eps
            best_partition = list(canonical)

    return best_partition, best_defect


def quotient_system(L, pi, partition):
    """Compute the quotient generator L_bar and pi_bar."""
    blocks = {}
    for i, b in enumerate(partition):
        blocks.setdefault(b, []).append(i)
    block_ids = sorted(blocks.keys())
    n_blocks = len(block_ids)

    pi_bar = np.zeros(n_blocks)
    L_bar = np.zeros((n_blocks, n_blocks))

    for a_idx, a_id in enumerate(block_ids):
        pi_bar[a_idx] = sum(pi[m] for m in blocks[a_id])
        for b_idx, b_id in enumerate(block_ids):
            if pi_bar[a_idx] > 0:
                L_bar[a_idx, b_idx] = sum(
                    pi[x] * L[x, y]
                    for x in blocks[a_id]
                    for y in blocks[b_id]
                ) / pi_bar[a_idx]

    return L_bar, pi_bar


print(f"\nLevel 0: |V| = 4, L = generator")
L_current = L.copy()
pi_current = pi.copy()
n_current = 4

for level in range(5):
    if n_current <= 1:
        print(f"  Terminal: single state reached at level {level}")
        break

    P_opt, eps_opt = find_optimal_partition(L_current, pi_current, n_current)
    n_blocks = len(set(P_opt))

    print(f"\n  Level {level}: |V|={n_current}, optimal P={P_opt}, "
          f"n_blocks={n_blocks}, defect={eps_opt:.6e}")

    if n_blocks == n_current or n_blocks <= 1:
        print(f"  Terminal: optimal partition is trivial")
        break

    L_current, pi_current = quotient_system(L_current, pi_current, P_opt)
    n_current = n_blocks
    print(f"  Quotient: L_bar =\n{L_current}")
    print(f"  pi_bar = {pi_current}")

# ============================================================
# CONTINENT 3: GAMMA_Q VS Q SCALING
# ============================================================
print(f"\n{'='*60}")
print("CONTINENT 3: ESCORT-WEIGHTED SPECTRAL GAP vs q")
print(f"{'='*60}")


def escort_dirichlet_form(L, pi, f, q):
    """E_q(f) = (1/2) * (1/Z_q) * sum pi(x)^q L(x,y) (f(y)-f(x))^2."""
    n = len(pi)
    Z_q = np.sum(pi**q)
    if Z_q < 1e-30:
        return 0.0
    total = 0.0
    for x in range(n):
        for y in range(n):
            if x != y and L[x, y] > 0:
                total += pi[x]**q * L[x, y] * (f[y] - f[x])**2
    return 0.5 * total / Z_q


def escort_variance(pi, f, q):
    """Var_q(f) under escort distribution."""
    Z_q = np.sum(pi**q)
    if Z_q < 1e-30:
        return 0.0
    mean_q = np.sum(pi**q * f) / Z_q
    return np.sum(pi**q * (f - mean_q)**2) / Z_q


def escort_spectral_gap(L, pi, q, n_samples=10000):
    """Estimate gamma_q = inf E_q(f) / Var_q(f) over f orthogonal to q-constants."""
    n = len(pi)
    best_ratio = float('inf')
    for _ in range(n_samples):
        f = np.random.randn(n)
        # Make mean-zero under escort
        Z_q = np.sum(pi**q)
        mean_q = np.sum(pi**q * f) / Z_q
        f -= mean_q
        var_q = escort_variance(pi, f, q)
        if var_q > 1e-12:
            E_q = escort_dirichlet_form(L, pi, f, q)
            ratio = E_q / var_q
            if ratio < best_ratio:
                best_ratio = ratio
    return best_ratio


# Standard spectral gap (q=1)
gamma_1 = escort_spectral_gap(L, pi, 1.0)
print(f"\n  Standard spectral gap gamma_1 = {gamma_1:.6f}")

q_values = [1.0, 1.1, 1.2, 1.3, 1.4, 1.5, 1.6, 1.7, 1.8, 1.9]
gamma_q_values = []

print(f"\n  {'q':>5s}  {'gamma_q':>10s}  {'gamma_q/gamma_1':>15s}  {'gamma^{2-q} pred':>16s}  {'ratio':>8s}")
print(f"  {'-'*5}  {'-'*10}  {'-'*15}  {'-'*16}  {'-'*8}")

for q in q_values:
    gamma_q = escort_spectral_gap(L, pi, q)
    gamma_q_values.append(gamma_q)
    pred = gamma_1 ** (2 - q)
    ratio = gamma_q / pred if pred > 1e-12 else float('inf')
    print(f"  {q:>5.1f}  {gamma_q:>10.6f}  {gamma_q/gamma_1:>15.6f}  {pred:>16.6f}  {ratio:>8.4f}")

# ============================================================
# CONTINENT 4: SCHUR COMPLEMENT
# ============================================================
print(f"\n{'='*60}")
print("CONTINENT 4: SCHUR COMPLEMENT / WILSONIAN EFFECTIVE ACTION")
print(f"{'='*60}")

# Decompose L into blocks relative to partition {0,1} | {2,3}
L_coarse = L[:2, :2]  # L restricted to block 0
L_fine = L[2:, 2:]    # L restricted to block 1
D_lower = L[2:, :2]   # inter-block: fine -> coarse
D_upper = L[:2, 2:]   # inter-block: coarse -> fine

print(f"\n  Block decomposition of L:")
print(f"  L_coarse (block 0->0):\n{L_coarse}")
print(f"  L_fine (block 1->1):\n{L_fine}")
print(f"  D_upper (block 0->1):\n{D_upper}")
print(f"  D_lower (block 1->0):\n{D_lower}")

# Schur complement: L/L_fine = L_coarse - D_upper @ L_fine^{-1} @ D_lower
# But L_fine is singular (rows sum to 0), so we use pseudoinverse
L_fine_pinv = np.linalg.pinv(L_fine)
schur = L_coarse - D_upper @ L_fine_pinv @ D_lower

print(f"\n  L_fine pseudoinverse:\n{L_fine_pinv}")
print(f"  Schur complement L/L_fine:\n{schur}")
print(f"  Self-energy D_upper @ L_fine^-1 @ D_lower:\n{D_upper @ L_fine_pinv @ D_lower}")

# Compare to the quotient generator
L_bar, pi_bar = quotient_system(L, pi, partition)
print(f"\n  Quotient generator L_bar:\n{L_bar}")
print(f"  Schur complement:\n{schur}")
print(f"  Are they equal? {np.allclose(schur, L_bar, atol=1e-6)}")

# ============================================================
# CONTINENT 5: COARSE-GRAINING CRITICALITY
# ============================================================
print(f"\n{'='*60}")
print("CONTINENT 5: COARSE-GRAINING CRITICALITY (gamma_c = epsilon)")
print(f"{'='*60}")

# Vary beta (inter-block coupling) and track gamma vs epsilon
betas = np.logspace(-3, 0, 20)
print(f"\n  {'beta':>8s}  {'gamma':>10s}  {'epsilon':>10s}  {'gamma/eps':>10s}  {'regime':>15s}")
print(f"  {'-'*8}  {'-'*10}  {'-'*10}  {'-'*10}  {'-'*15}")

for b in betas:
    L_b = np.array([
        [-(alpha + b), alpha, b, 0],
        [alpha, -(alpha + b), 0, b],
        [b, 0, -(alpha + b), alpha],
        [0, b, alpha, -(alpha + b)],
    ])

    # Spectral gap: second smallest eigenvalue of -L
    eigvals = np.sort(np.linalg.eigvalsh(-L_b))
    gamma_b = eigvals[1]  # smallest nonzero

    # Defect
    D_b = defect_operator(L_b, pi, partition)
    eps_b = op_norm_pi(pi, D_b, n_samples=3000)

    ratio = gamma_b / eps_b if eps_b > 1e-12 else float('inf')
    regime = "NCD (gamma>eps)" if gamma_b > eps_b else "LINEAR (gamma<eps)"

    print(f"  {b:>8.4f}  {gamma_b:>10.6f}  {eps_b:>10.6f}  {ratio:>10.4f}  {regime:>15s}")

print(f"\n  The criticality threshold gamma_c = epsilon occurs when the ratio = 1.")
print(f"  Below this: linear error growth (T* = 1/eps).")
print(f"  Above this: NCD uniform error bound (infinite T*).")

# ============================================================
# SUMMARY
# ============================================================
print(f"\n{'#'*70}")
print("# EXPLORATION SUMMARY")
print(f"{'#'*70}")
print(f"\nAll five continents explored on a 4-state chain.")
print(f"The numerical evidence will reveal which theoretical predictions hold.")
