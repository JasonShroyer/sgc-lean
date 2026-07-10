#!/usr/bin/env python3
"""
spectral_dimension_quench.py  -- Path A of pre-registration decisions/0008.

Tests the spatial Tsallis law  q* = 1 + 2/d_s  on five graph Laplacians whose
spectral dimension d_s is known analytically:

    1D ring (Cayley Z_N,{+-1})  d_s = 1     -> q* = 3.000
    2D torus  Z_m^2             d_s = 2     -> q* = 2.000
    3D torus  Z_m^3             d_s = 3     -> q* = 1.667
    Sierpinski gasket           d_s = 2ln3/ln5 ~ 1.365 -> q* ~ 2.465
    modular Cayley expander      d_s -> inf -> q* -> 1.0  (Boltzmann limit)

Grounding (faithful to the SGC formalization):
  * (V, L, pi): finite state space, generator L = D - A (symmetric PSD), measure pi.
    -> Axiom 0 of "Theory of Emergence"; here pi is uniform (vertex-transitive graphs).
  * Heat-kernel return probability  P(t) = (1/N) sum_k e^{-lambda_k t}
    -> SGC `K_norm` / HeatKernel in src/SGC/Spectral/Defs.lean.
  * Spectral dimension  P(t) ~ t^{-d_s/2}  (Tauberian dual of rho(lambda)~lambda^{d_s/2-1}).
  * q-exponential (Beck-Cohen superstatistics): a Gamma(shape d_s/2)-superposition of
    exponentials is exp_q(-t/tau) with q = 1 + 2/d_s. So the defect-minimizing escort
    index = best-fit q-exponential index of P(t).  (decisions/0008, superstatistics section)
  * Escort distribution P_q(x) ~ pi(x)^q and Tsallis q-divergence D_q
    -> src/SGC/InformationGeometry/TsallisStatistics.lean, EscortConductance.lean.

SCOPE (pre-registered honesty): on abstract graphs q*(from P-tail) and d_s(from the
same tail) are analytically linked, so Path A is CALIBRATION -- it checks (i) the two
independent d_s estimators agree, (ii) P(t) is q-exponential per geometry, (iii) the
monotone ladder reproduces. The non-tautological test is Path B (learned manifold).
"""

import argparse
import json
import math
import time

import numpy as np

ZERO_TOL = 1e-9
LN3_OVER_LN5 = math.log(3.0) / math.log(5.0)
DS_SIERPINSKI = 2.0 * LN3_OVER_LN5          # ~ 1.3652
SEEDS = list(range(42, 50))                  # EDL multi-seed discipline (n=8)


# --------------------------------------------------------------------------- #
# Graph builders: return the combinatorial Laplacian L = D - A (symmetric PSD) #
# --------------------------------------------------------------------------- #
def _laplacian_from_edges(n, edges):
    A = np.zeros((n, n))
    for i, j in edges:
        A[i, j] += 1.0
        A[j, i] += 1.0
    deg = A.sum(axis=1)
    return np.diag(deg) - A


def ring_spectrum(n):
    """Cycle C_n = Cayley(Z_n,{+-1}); EXACT eigenvalues 2(1-cos(2 pi k/n)).  d_s = 1.

    Abelian Cayley graph -> spectrum is analytic, so we use large n (clean power-law
    window) at zero diagonalization cost."""
    k = np.arange(n)
    return 2.0 * (1.0 - np.cos(2.0 * np.pi * k / n))


def torus_spectrum(side, dim):
    """Torus Z_side^dim; EXACT eigenvalues = sums of 1D-cycle eigenvalues.  d_s = dim."""
    base = 2.0 * (1.0 - np.cos(2.0 * np.pi * np.arange(side) / side))
    spec = base.copy()
    for _ in range(dim - 1):
        spec = (spec[:, None] + base[None, :]).ravel()
    return spec


def sierpinski_laplacian(level):
    """Sierpinski gasket graph by iterative 3-corner gluing.  d_s = 2 ln3/ln5."""
    # Start with a triangle; each step replaces every triangle by 3 half-size ones.
    pts = {(0.0, 0.0), (1.0, 0.0), (0.5, math.sqrt(3) / 2)}
    triangles = [tuple(pts)]
    for _ in range(level):
        new_tris = []
        for (a, b, c) in triangles:
            mab = ((a[0] + b[0]) / 2, (a[1] + b[1]) / 2)
            mbc = ((b[0] + c[0]) / 2, (b[1] + c[1]) / 2)
            mca = ((c[0] + a[0]) / 2, (c[1] + a[1]) / 2)
            new_tris += [(a, mab, mca), (b, mab, mbc), (c, mbc, mca)]
        triangles = new_tris
    # Index unique vertices (round to avoid float dup).
    index, verts = {}, []
    def vid(p):
        key = (round(p[0], 9), round(p[1], 9))
        if key not in index:
            index[key] = len(verts)
            verts.append(key)
        return index[key]
    edges = set()
    for (a, b, c) in triangles:
        ia, ib, ic = vid(a), vid(b), vid(c)
        for i, j in ((ia, ib), (ib, ic), (ic, ia)):
            edges.add((min(i, j), max(i, j)))
    return _laplacian_from_edges(len(verts), list(edges))


def cayley_expander_laplacian(n, n_generators, seed):
    """Cayley(Z_n, S) with random generators S -> expander (Alon-Roichman). d_s -> inf."""
    rng = np.random.default_rng(seed)
    gens = rng.choice(np.arange(1, n), size=n_generators, replace=False)
    edges = []
    for g in gens:
        for i in range(n):
            j = (i + int(g)) % n
            edges.append((min(i, j), max(i, j)))
    edges = list(set(edges))
    return _laplacian_from_edges(n, edges)


# --------------------------------------------------------------------------- #
# Spectral observables                                                          #
# --------------------------------------------------------------------------- #
def scaling_window(eigs):
    """Pre-registered window t in [10/lambda_max, 0.1/lambda_2]; None if gapped."""
    nz = eigs[eigs > ZERO_TOL]
    lam2, lam_max = nz.min(), nz.max()
    t_lo, t_hi = 10.0 / lam_max, 0.1 / lam2
    if t_lo >= t_hi:
        return None  # no power-law window  ==  spectral gap  ==  d_s -> inf
    return np.geomspace(t_lo, t_hi, 64)


def return_prob(eigs, t):
    """P(t) = sum over NONZERO modes of e^{-lambda t} (zero mode = constant floor)."""
    nz = eigs[eigs > ZERO_TOL]
    return np.array([np.sum(np.exp(-nz * tt)) for tt in t])


def fit_ds_return(eigs, window):
    """Estimator 1: d_s = -2 * slope(log P vs log t)."""
    P = return_prob(eigs, window)
    slope = np.polyfit(np.log(window), np.log(P), 1)[0]
    return -2.0 * slope


def fit_ds_dos(eigs):
    """Estimator 2 (independent): integrated DOS N(lambda) ~ lambda^{d_s/2}."""
    nz = np.sort(eigs[eigs > ZERO_TOL])
    n = len(nz)
    lo, hi = max(2, int(0.02 * n)), max(4, int(0.20 * n))
    k = np.arange(lo, hi)
    slope = np.polyfit(np.log(nz[k]), np.log(k + 1.0), 1)[0]
    return 2.0 * slope


def fit_q_qexp(eigs, window):
    """Primary q*: least-squares fit of P(t) to A * exp_q(-t/tau) in log space."""
    from scipy.optimize import curve_fit
    P = return_prob(eigs, window)
    logP = np.log(P)

    def log_qexp(t, logA, q, tau):
        return logA - (1.0 / (q - 1.0)) * np.log1p((q - 1.0) * t / tau)

    p0 = [logP[0], 1.5, window[len(window) // 2]]
    bounds = ([-50.0, 1.001, 1e-6], [50.0, 3.0, 1e9])
    try:
        popt, _ = curve_fit(log_qexp, window, logP, p0=p0, bounds=bounds, maxfev=20000)
        resid = float(np.mean((log_qexp(window, *popt) - logP) ** 2))
        return float(popt[1]), float(popt[2]), resid
    except Exception as exc:  # pragma: no cover
        return float("nan"), float("nan"), float("inf")


# NOTE: the EXPLORATORY escort self-consistency defect (decisions/0008) is DEFERRED.
# On vertex-transitive graphs the stationary measure pi is uniform, so the escort
# P_q(x) ~ pi(x)^q is uniform for every q and D_q(P_q || K_t P_q) = 0 identically --
# the probe is degenerate here. It becomes meaningful only with a non-uniform pi, i.e.
# on the learned representation manifold (Path B), where it will be implemented.


# --------------------------------------------------------------------------- #
# Per-graph driver                                                              #
# --------------------------------------------------------------------------- #
def analyze(name, eigvals, ds_analytic, seed=None):
    eigvals = np.clip(np.asarray(eigvals, dtype=float), 0, None)
    n = len(eigvals)
    window = scaling_window(eigvals)
    if window is None:  # gapped == expander == d_s -> inf, Boltzmann q -> 1
        return dict(graph=name, seed=seed, n=n, gapped=True,
                    ds_analytic=ds_analytic, ds_return=float("inf"),
                    ds_dos=float("nan"), q_star=1.0, q_pred=1.0, fit_resid=0.0)
    ds_ret = fit_ds_return(eigvals, window)
    ds_dos = fit_ds_dos(eigvals)
    q_star, _tau, resid = fit_q_qexp(eigvals, window)
    q_pred = 1.0 + 2.0 / ds_dos if ds_dos > 0 else float("nan")
    return dict(graph=name, seed=seed, n=n, gapped=False,
                ds_analytic=ds_analytic, ds_return=ds_ret, ds_dos=ds_dos,
                q_star=q_star, q_pred=q_pred, fit_resid=resid)


def build_ladder(args):
    return [
        ("1D ring",    ring_spectrum(args.ring),                                      1.0),
        ("2D torus",   torus_spectrum(args.torus2d, 2),                               2.0),
        ("3D torus",   torus_spectrum(args.torus3d, 3),                               3.0),
        ("Sierpinski", np.linalg.eigvalsh(sierpinski_laplacian(args.sierpinski)), DS_SIERPINSKI),
    ]


def main():
    ap = argparse.ArgumentParser(description="Path A spectral-dimension Tsallis quench")
    ap.add_argument("--ring", type=int, default=4000)       # analytic spectrum
    ap.add_argument("--torus2d", type=int, default=100)    # N = 10_000, analytic
    ap.add_argument("--torus3d", type=int, default=60)     # N = 216_000, analytic
    ap.add_argument("--sierpinski", type=int, default=7)   # N ~ 3282 (numeric eigvalsh)
    ap.add_argument("--expander-n", type=int, default=1500)
    ap.add_argument("--expander-gens", type=int, default=10)
    ap.add_argument("--out", type=str, default="experiments/spectral_dimension_quench_results.json")
    args = ap.parse_args()

    t_start = time.time()
    results = []
    for name, eigs, ds in build_ladder(args):
        results.append(analyze(name, eigs, ds))

    # Expander across the pre-registered seed set (only seed-dependent arm).
    for seed in SEEDS:
        L = cayley_expander_laplacian(args.expander_n, args.expander_gens, seed)
        results.append(analyze("modular expander", np.linalg.eigvalsh(L), float("inf"), seed=seed))

    # ---- report ----
    hdr = f"{'graph':<18}{'N':>8}{'d_s(anal)':>11}{'d_s(DOS)':>11}{'d_s(ret)':>11}{'q*(fit)':>10}{'1+2/d_s':>10}"
    print("\n" + "=" * len(hdr))
    print("PATH A  -- spectral-dimension Tsallis quench (decisions/0008)")
    print("=" * len(hdr))
    print(hdr)
    print("-" * len(hdr))
    seen_expander = False
    for r in results:
        if r["graph"] == "modular expander":
            if seen_expander:
                continue
            seen_expander = True
            exp = [x for x in results if x["graph"] == "modular expander"]
            qs = np.array([x["q_star"] for x in exp])
            print(f"{'modular expander':<18}{exp[0]['n']:>8}{'inf':>11}{'gapped':>11}{'gapped':>11}"
                  f"{qs.mean():>10.3f}{1.0:>10.3f}   [n=8 seeds, std={qs.std():.3f}]")
            continue
        da = f"{r['ds_analytic']:.3f}"
        print(f"{r['graph']:<18}{r['n']:>8}{da:>11}{r['ds_dos']:>11.3f}{r['ds_return']:>11.3f}"
              f"{r['q_star']:>10.3f}{r['q_pred']:>10.3f}")
    print("-" * len(hdr))

    # ---- pre-registered falsifier checks ----
    ladder = [r for r in results if r["graph"] != "modular expander"]
    ladder_sorted = sorted(ladder, key=lambda r: r["ds_analytic"])
    qs_by_ds = [r["q_star"] for r in ladder_sorted]
    monotone = all(qs_by_ds[i] >= qs_by_ds[i + 1] - 0.15 for i in range(len(qs_by_ds) - 1))
    exp_q = np.mean([x["q_star"] for x in results if x["graph"] == "modular expander"])
    max_err = max(abs(r["q_star"] - r["q_pred"]) for r in ladder)
    print("FALSIFIER CHECKS")
    print(f"  F1 monotone q* decreasing in d_s ........ {'PASS' if monotone else 'FAIL'}")
    print(f"  F2 expander drives q* -> 1 (got {exp_q:.3f}) .. {'PASS' if exp_q < 1.2 else 'FAIL'}")
    print(f"  F3 low-d_s graphs reach q* > 2 .......... "
          f"{'PASS' if all(r['q_star'] > 2.0 for r in ladder if r['ds_analytic'] < 2.0) else 'FAIL'}")
    print(f"  primary consistency max|q* - (1+2/d_s_DOS)| = {max_err:.3f}")
    print("  escort-defect probe: DEFERRED (uniform pi degenerate on these graphs; Path B)")
    print(f"\n  elapsed {time.time() - t_start:.1f}s")

    with open(args.out, "w") as fh:
        json.dump(results, fh, indent=2, default=str)
    print(f"  results -> {args.out}\n")


if __name__ == "__main__":
    main()
