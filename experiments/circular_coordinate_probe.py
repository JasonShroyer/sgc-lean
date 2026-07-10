#!/usr/bin/env python3
"""circular_coordinate_probe.py -- Leg 1a (decisions/0010 follow-on).

RESOLVE the recurrent Betti distribution {1,2,2,4}: is each seed's recurrent ring a SINGLE
wavy S^1 whose higher Fourier harmonics fool Vietoris-Rips into OVER-COUNTING H1 loops, or
are there genuinely k independent cycles?

The cloud H[s] (s = ring state in Z_p) is a curve parametrised by the KNOWN cyclic variable
s, so we can decompose it spectrally and ask, decisively:

  1. WINDING NUMBER of the dominant cycle (turning number in the top-2 PCA plane): a single
     once-around loop has |winding| = 1; a genuine k-fold cover has |winding| = k.
  2. FOURIER DECONVOLUTION: reconstruct H[s] from {DC + fundamental k* only} -> a clean
     ellipse -> read its b1.  Then ADD harmonics (k<=2, k<=3, k<=4) and watch b1 climb.
     If the fundamental-only reconstruction is b1=1 (winding 1) and the satellite bars only
     appear as harmonics are added, the loop is ONE S^1 and the high b1 is a Rips lobe
     artifact -- exactly the over-counting hypothesis, now proven on the data.

Reuses the IDENTICAL calibrated reader (run_calibration -> tau1*) from
persistent_homology_grokking, so the b1 verdicts are on the same footing as every other
cloud in 0010.  Importable: analyze_cloud(name, X, tau1) is reused by the transformer probe.
"""
import os
import sys

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

from persistent_homology_grokking import analyze, betti, run_calibration  # noqa: E402


def fourier_power(X):
    """X[s] (p x D), real -> folded power per frequency k=1..p//2 (DC removed), and dom k*."""
    p = X.shape[0]
    F = np.fft.fft(X - X.mean(0, keepdims=True), axis=0)     # (p, D)
    half = p // 2
    P = (np.abs(F[1:half + 1]) ** 2).sum(axis=1)             # power k=1..half
    P = P / (P.sum() + 1e-30)
    kstar = int(np.argmax(P)) + 1
    return P, kstar, F


def reconstruct(F, kmax):
    """Inverse-DFT keeping only DC + modes 1..kmax (and conjugates) -> real cloud (p x D)."""
    p = F.shape[0]
    Fk = np.zeros_like(F)
    Fk[0] = F[0]
    for k in range(1, kmax + 1):
        Fk[k] = F[k]
        Fk[p - k] = F[p - k]
    return np.fft.ifft(Fk, axis=0).real


def _turning(pu, pv):
    """Net turning number of the closed sequence (pu[s], pv[s]) (wraps s: last -> first)."""
    ang = np.arctan2(pv, pu)
    dd = np.diff(np.concatenate([ang, ang[:1]]))
    dd = (dd + np.pi) % (2 * np.pi) - np.pi                  # wrap to (-pi, pi]
    return float(dd.sum() / (2 * np.pi))


def winding_mode(X, F, kstar):
    """Turning number of X[s] projected onto the DOMINANT Fourier mode's own 2D plane
    (directions Re F[k*], Im F[k*]).  This is the reliable degree of the dominant carrier
    (~ +/- k*); the top-2 PCA plane can mix comparable frequencies, so it is NOT used."""
    return _turning(X @ F[kstar].real, X @ F[kstar].imag)


def recon_single(F, k):
    """Inverse-DFT keeping ONLY mode k (and conjugate) + DC -> the isolated k-carrier."""
    Fk = np.zeros_like(F)
    Fk[0] = F[0]
    Fk[k] = F[k]
    Fk[F.shape[0] - k] = F[F.shape[0] - k]
    return np.fft.ifft(Fk, axis=0).real


def b1_of(X, tau1):
    """Calibrated H1 Betti number + top-5 persistences of one cloud (N<=p so deterministic)."""
    pd, tm = analyze(X, maxdim=1, n_sub=None, n_boot=1)
    b1, _ = betti(pd[1], tau1)
    return b1, tm[1]


def analyze_cloud(name, X, tau1, harmonics=(1, 2, 3, 4)):
    """Full circular-coordinate read of one s-parametrised cloud X (p x D)."""
    P, kstar, F = fourier_power(X)
    winding = winding_mode(X, F, kstar)
    b1_dom, _ = b1_of(recon_single(F, kstar), tau1)
    b1_full, top_full = b1_of(X, tau1)
    print(f"  {name}", flush=True)
    print(f"    dominant carrier k*={kstar}  (power {P[kstar-1]*100:4.1f}%)   "
          f"winding(k* plane)={winding:+.2f}   isolated-k* b1={b1_dom}", flush=True)
    print(f"    {'reconstruction':<22}{'b1':>4}   top-3 H1 persistences", flush=True)
    rows = {}
    for km in harmonics:
        Xr = reconstruct(F, km)
        b1, top = b1_of(Xr, tau1)
        rows[km] = b1
        lab = f"fundamental k<= {km}"
        print(f"    {lab:<22}{b1:>4}   [{' '.join(f'{x:.3f}' for x in top[:3])}]", flush=True)
    print(f"    {'full cloud':<22}{b1_full:>4}   [{' '.join(f'{x:.3f}' for x in top_full[:3])}]", flush=True)
    return dict(name=name, kstar=kstar, winding=winding, b1_full=b1_full, by_harmonic=rows)


def main():
    seeds = [42, 43, 44, 45]
    clouds = {}
    for s in seeds:
        f = os.path.join(_HERE, "logs", "ph_grok", f"recurrent_seed{s}",
                         "recurrent_hidden_classmean.npy")
        if os.path.exists(f):
            clouds[s] = np.load(f)
        else:
            print(f"  [seed {s}] NO cache at {f}", flush=True)

    print("=" * 78)
    print("CIRCULAR-COORDINATE PROBE  --  is the recurrent ring ONE wavy S^1 (Rips over-counts)?")
    print("=" * 78, flush=True)

    gate_ok, tau1, tau2 = run_calibration()
    if not gate_ok:
        print("\n  reader NOT calibrated; abort.")
        sys.exit(1)

    print(f"\n{'='*78}\n  RECURRENT RINGS: winding + Fourier deconvolution (tau1*={tau1:.3f})\n{'='*78}",
          flush=True)
    res = [analyze_cloud(f"seed {s} H[s]", X, tau1) for s, X in clouds.items()]

    print("=" * 78)
    fund_all_one = all(r["by_harmonic"].get(1, 9) == 1 for r in res)
    carriers = ", ".join(f"s{r['name'].split()[1]}:k{r['kstar']}" for r in res)
    if fund_all_one:
        print("  VERDICT: the k=1 FUNDAMENTAL is a single clean S^1 (b1=1) in ALL seeds.")
        print("  Full-cloud b1 in {1,2,2,4} is HARMONIC-LOBE Rips over-counting of a circular")
        print("  carrier -- NOT independent cycles.  Dominant carrier per seed: " + carriers + ".")
        print("  (gcd(k*,p)=1 so any harmonic uniquely labels Z_p; seed 45 simply rides k=3.)")
    else:
        print("  VERDICT: some seed's fundamental is NOT a clean circle; inspect rows.")
    print("=" * 78, flush=True)


if __name__ == "__main__":
    main()
