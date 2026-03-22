#!/usr/bin/env python3
"""
CERN Dimuon Verification Protocol: Three Tests Before the Record

Test 1: Seed stability — does the engine consistently pick Muon 2, or
        does it rotate randomly between blocks? (artifact vs discovery)

Test 2: Mass shell variance — does the discovered C* achieve variance
        near 3.5e-7 (mass shell), or is it still ~1.0? (eigenvector vs
        actual conservation law)

Test 3: Hessian isotropy — are the px/py/pz Hessian eigenvalues
        degenerate due to detector cylindrical symmetry? (detector
        geometry artifact vs genuine Minkowski structure)
"""

import numpy as np
import sys, os, csv

sys.path.insert(0, os.path.dirname(__file__))
from sgc_relational_engine import SGCRelationalEngine, load_cern_dimuon


def run_verification():
    print("=" * 70)
    print("CERN DIMUON VERIFICATION PROTOCOL")
    print("Three tests before the result goes in the record")
    print("=" * 70)

    # Load data
    csv_path = os.path.join(os.path.dirname(__file__), '..', 'data',
                             'MuRun2010B.csv')
    csv_path = os.path.normpath(csv_path)
    X_raw, M_oracle = load_cern_dimuon(csv_path)
    N = len(X_raw)
    d = 8

    global_scale = np.std(X_raw)
    X = X_raw / global_scale

    eta = np.diag([1, -1, -1, -1])

    # Ground truth mass shell variances (normalized)
    m1_norm = np.einsum('ni,ij,nj->n', X[:, :4], eta, X[:, :4])
    m2_norm = np.einsum('ni,ij,nj->n', X[:, 4:], eta, X[:, 4:])
    gt_var_m1 = float(np.var(m1_norm))
    gt_var_m2 = float(np.var(m2_norm))
    print(f"\nGround truth mass shell variance (normalized):")
    print(f"  Muon 1: {gt_var_m1:.6e}")
    print(f"  Muon 2: {gt_var_m2:.6e}")

    # ==================================================================
    # TEST 1: SEED STABILITY
    # ==================================================================
    print(f"\n{'=' * 70}")
    print("TEST 1: SEED STABILITY (5 runs, different random seeds)")
    print("Question: Does the engine consistently pick Muon 2, or rotate?")
    print(f"{'=' * 70}")

    seeds = [42, 123, 456, 789, 1337]
    block_winners = []
    discovered_ratios = []
    discovered_variances = []

    for seed in seeds:
        np.random.seed(seed)
        # Perturb the initial C slightly with seed-dependent noise
        # (The engine starts from C=I, but the gradient has no randomness
        # unless the data order changes. So we add tiny perturbation.)
        X_shuffled = X.copy()
        perm = np.random.permutation(N)
        X_shuffled = X_shuffled[perm]

        C, tel = SGCRelationalEngine.crystallize_manifold(
            X_shuffled, max_iterations=1000, lr=0.01
        )

        # Check which block has Minkowski structure
        block_11 = C[:4, :4]
        block_22 = C[4:, 4:]

        best_name = None
        best_error = float('inf')
        best_ratios = None
        for bname, block in [("Muon1", block_11), ("Muon2", block_22)]:
            bd = np.diag(block)
            if abs(bd[0]) > 0.01:
                ratios = bd[1:] / bd[0]
                err = np.max(np.abs(ratios - (-1.0)))
                if err < best_error:
                    best_error = err
                    best_name = bname
                    best_ratios = ratios

        block_winners.append(best_name)
        discovered_ratios.append(best_ratios)
        discovered_variances.append(tel['final_variance'])

        if best_ratios is not None:
            print(f"  Seed {seed:5d}: winner={best_name} "
                  f"ratios=[{', '.join(f'{r:+.4f}' for r in best_ratios)}] "
                  f"error={best_error:.4f} var={tel['final_variance']:.4e}")
        else:
            print(f"  Seed {seed:5d}: winner=NONE (no block passed)")

    # Verdict
    unique_winners = set(w for w in block_winners if w is not None)
    print(f"\n  Winners across seeds: {block_winners}")
    if len(unique_winners) == 1:
        print(f"  VERDICT: Consistently {list(unique_winners)[0]} — "
              f"NOT random rotation. Likely physics-driven asymmetry.")
    elif len(unique_winners) == 2:
        n1 = sum(1 for w in block_winners if w == "Muon1")
        n2 = sum(1 for w in block_winners if w == "Muon2")
        print(f"  VERDICT: Muon1={n1}, Muon2={n2} — "
              f"{'ROTATES (normalization artifact)' if min(n1,n2) >= 2 else 'Mostly one block'}")
    else:
        print(f"  VERDICT: No block consistently passes — artifact")

    # ==================================================================
    # TEST 2: MASS SHELL VARIANCE ON DISCOVERED C*
    # ==================================================================
    print(f"\n{'=' * 70}")
    print("TEST 2: MASS SHELL VARIANCE")
    print("Question: Does C* achieve variance ~3.5e-7 or still ~1.0?")
    print(f"{'=' * 70}")

    # Use the C from the first (seed=42) run
    np.random.seed(42)
    C_full, tel_full = SGCRelationalEngine.crystallize_manifold(
        X, max_iterations=1000, lr=0.01
    )

    # Extract the winning 4x4 block
    block_11 = C_full[:4, :4]
    block_22 = C_full[4:, 4:]

    # Determine which block is the winner
    for bname, block, x_slice in [("Muon1", block_11, X[:, :4]),
                                    ("Muon2", block_22, X[:, 4:])]:
        bd = np.diag(block)
        if abs(bd[0]) < 0.01:
            print(f"\n  {bname}: block collapsed (E diagonal < 0.01)")
            continue

        # Compute q_i = x_i^T C_block x_i for each event
        q_block = np.einsum('ni,ij,nj->n', x_slice, block, x_slice)
        var_block = float(np.var(q_block))
        mean_block = float(np.mean(q_block))

        # Physical units
        q_phys = q_block * (global_scale ** 2)
        var_phys = float(np.var(q_phys))
        mean_phys = float(np.mean(q_phys))

        # Compare to ground truth
        gt_var = gt_var_m1 if bname == "Muon1" else gt_var_m2
        ratios = bd[1:] / bd[0]

        print(f"\n  {bname} block:")
        print(f"    Block diagonal: [{', '.join(f'{v:+.6f}' for v in bd)}]")
        print(f"    Ratios to E:    [{', '.join(f'{r:+.4f}' for r in ratios)}]")
        print(f"    Achieved var (normalized): {var_block:.6e}")
        print(f"    Target var (mass shell):   {gt_var:.6e}")
        print(f"    Ratio achieved/target:     {var_block/gt_var:.1f}x")
        print(f"    Mean q (GeV^2):            {mean_phys:.6f}")
        print(f"    Expected (m_mu^2):         0.0112")
        if abs(mean_phys) > 0:
            print(f"    sqrt(|mean q|):            {np.sqrt(abs(mean_phys)):.4f} GeV")

    # Also compute variance using the exact Minkowski metric for comparison
    print(f"\n  Reference: EXACT Minkowski metric on each muon:")
    for bname, x_slice in [("Muon1", X[:, :4]), ("Muon2", X[:, 4:])]:
        q_exact = np.einsum('ni,ij,nj->n', x_slice, eta, x_slice)
        var_exact = float(np.var(q_exact))
        # Normalize eta to ||eta||_F = 1 for fair comparison
        eta_norm = eta / np.linalg.norm(eta)
        q_exact_norm = np.einsum('ni,ij,nj->n', x_slice, eta_norm, x_slice)
        var_exact_norm = float(np.var(q_exact_norm))
        print(f"    {bname} with eta/||eta||: var = {var_exact_norm:.6e}")

    # ==================================================================
    # TEST 3: HESSIAN ISOTROPY CHECK
    # ==================================================================
    print(f"\n{'=' * 70}")
    print("TEST 3: HESSIAN ISOTROPY")
    print("Question: Are px/py/pz eigenvalues degenerate (detector symmetry)?")
    print(f"{'=' * 70}")

    # Compute variance Hessian
    X_outer = np.einsum('ni,nj->nij', X, X)
    triu_idx = np.triu_indices(d)
    n_sym = len(triu_idx[0])
    Z = X_outer[:, triu_idx[0], triu_idx[1]]
    diag_mask = triu_idx[0] == triu_idx[1]
    Z[:, ~diag_mask] *= np.sqrt(2.0)
    Z_mean = np.mean(Z, axis=0)
    Z_centered = Z - Z_mean
    H = 2.0 * (Z_centered.T @ Z_centered) / N

    H_eigvals, H_eigvecs = np.linalg.eigh(H)

    print(f"\n  Hessian shape: {H.shape}")
    print(f"  Eigenvalue range: [{H_eigvals[0]:.6e}, {H_eigvals[-1]:.6e}]")

    # Report the bottom 10 eigenvalues
    print(f"\n  Bottom 10 Hessian eigenvalues:")
    for i in range(min(10, len(H_eigvals))):
        # Reconstruct the eigenvector as a d×d matrix to inspect
        sv = H_eigvecs[:, i]
        sd = np.zeros((d, d))
        sd[triu_idx[0], triu_idx[1]] = sv
        sd[triu_idx[1], triu_idx[0]] = sv
        for k in range(n_sym):
            ii, jj = triu_idx[0][k], triu_idx[1][k]
            if ii != jj:
                sd[ii, jj] /= np.sqrt(2.0)
                sd[jj, ii] /= np.sqrt(2.0)
        sd_diag = np.diag(sd)
        sd_eigs = np.sort(np.linalg.eigvalsh(sd))[::-1]
        print(f"    [{i}] lambda={H_eigvals[i]:.6e}  "
              f"diag=[{', '.join(f'{v:+.3f}' for v in sd_diag)}]  "
              f"eigs=[{', '.join(f'{v:+.3f}' for v in sd_eigs[:4])}...]")

    # Specifically check: are the bottom 3 eigenvalues degenerate?
    bottom3 = H_eigvals[:3]
    spread = (np.max(bottom3) - np.min(bottom3)) / (np.abs(np.mean(bottom3)) + 1e-12)
    print(f"\n  Bottom 3 eigenvalues: {bottom3}")
    print(f"  Relative spread: {spread:.6f}")
    if spread < 0.01:
        print(f"  VERDICT: Bottom 3 ARE degenerate (spread < 1%) — "
              f"detector symmetry artifact")
    elif spread < 0.10:
        print(f"  VERDICT: Bottom 3 are NEAR-degenerate (spread < 10%) — "
              f"partial detector symmetry")
    else:
        print(f"  VERDICT: Bottom 3 are NOT degenerate (spread {spread*100:.1f}%) — "
              f"structure is NOT from detector symmetry alone")

    # Check px vs py vs pz separately in the data
    print(f"\n  Data moment diagnostics (detector symmetry check):")
    labels = ['E1', 'px1', 'py1', 'pz1', 'E2', 'px2', 'py2', 'pz2']
    for i in range(d):
        x2_mean = float(np.mean(X[:, i]**2))
        x4_mean = float(np.mean(X[:, i]**4))
        print(f"    {labels[i]:>4s}: <x^2>={x2_mean:.6e}  <x^4>={x4_mean:.6e}  "
              f"kurtosis={x4_mean/(x2_mean**2):.2f}")

    print(f"\n  If px1,py1 have similar kurtosis but pz1 is different,")
    print(f"  the Hessian structure partially reflects detector geometry.")
    print(f"  If all three spatial components differ, the Hessian is not")
    print(f"  dominated by detector cylindrical symmetry.")

    print(f"\n{'=' * 70}")
    print("VERIFICATION COMPLETE")
    print(f"{'=' * 70}")


if __name__ == '__main__':
    run_verification()
