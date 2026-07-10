#!/usr/bin/env python3
"""
fft_classmeans_grokking.py -- Path B'' FUNCTIONAL FFT fork (decisions/0010).

The persistent-homology autopsy found the grokked modular-addition representation is
TOPOLOGICALLY TRIVIAL (b1=0) at every layer -- no geometric loop / torus.  That is a
statement about GEOMETRY.  It does NOT decide whether the network's FUNCTIONAL solution
uses Fourier (trigonometric) features: a multi-frequency closed curve can compute a+b
while being geometrically folded into a contractible blob (low H1 persistence).

This test discriminates the two functional mechanisms by Fourier-analysing the hidden
class-means  C[s] = mean hidden activation over { (a,b) : (a+b) mod p == s },  s=0..p-1:

  * DOMINANT PEAKS at a few key frequencies  -> Fourier-folded ribbon  (reconciles Nanda)
  * BROADBAND / white spectrum               -> non-Fourier algebraic crystallization

DISCIPLINE (mirrors the TDA calibration gate): bracket the OBSERVED spectrum between two
baselines computed with the IDENTICAL pipeline -- a white-noise lookup table (no Fourier
structure) and a clean few-tone signal (textbook Fourier features) -- so the verdict is
grounded in calibrated reference points, not eyeballed.

Input: experiments/logs/ph_grok/seed{S}/post_hidden_classmean.npy   (p x hidden)
"""
import argparse
import os
import sys

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))


def spectrum(C):
    """Class-means C[s,d] (p x D) -> folded power spectrum over s.

    Removes per-dim DC (k=0), sums |rfft|^2 over hidden dims (total-power decomposition),
    returns the normalized spectrum + summary statistics.
    """
    p, D = C.shape
    Cc = C - C.mean(axis=0, keepdims=True)            # drop per-dim offset (k=0 carries it)
    F = np.fft.rfft(Cc, axis=0)                        # (p//2+1, D)
    P = (np.abs(F) ** 2).sum(axis=1)[1:]               # total power per freq, drop DC
    n = len(P)                                         # = p//2 frequencies
    pn = P / (P.sum() + 1e-30)                          # normalized -> variance fraction
    k = np.arange(1, n + 1)
    pr = 1.0 / float((pn ** 2).sum())                  # spectral participation ratio
    order = np.argsort(pn)[::-1]
    top = [(int(k[i]), float(pn[i])) for i in order[:6]]
    top5 = float(pn[order[:5]].sum())
    n_peaks = int((pn > 5.0 / n).sum())                # freqs above 5x the uniform level
    # per-dimension dominant frequency (Nanda signature: many neurons share few key freqs)
    dom = (np.abs(F)[1:]).argmax(axis=0) + 1
    vals, counts = np.unique(dom, return_counts=True)
    o = np.argsort(counts)[::-1]
    dom_top = [(int(vals[i]), int(counts[i])) for i in o[:5]]
    return dict(pr=pr, n=n, top=top, top5=top5, n_peaks=n_peaks,
                n_distinct_dom=len(vals), dom_top=dom_top)


def show(name, s):
    bar = "  ".join(f"k{k}={v*100:4.1f}%" for k, v in s["top"])
    dom = " ".join(f"k{k}:{c}" for k, c in s["dom_top"])
    print(f"  {name:<24} PR={s['pr']:5.1f}/{s['n']}  peaks>5x={s['n_peaks']:>2}  "
          f"top5={s['top5']*100:5.1f}%", flush=True)
    print(f"  {'':<24} power:   {bar}", flush=True)
    print(f"  {'':<24} per-dim dominant freq (freq:#dims): {dom}", flush=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=42)
    ap.add_argument("--p", type=int, default=97)
    args = ap.parse_args()
    rng = np.random.default_rng(0)

    f = os.path.join(_HERE, "logs", "ph_grok", f"seed{args.seed}", "post_hidden_classmean.npy")
    if not os.path.exists(f):
        print(f"ERROR: cached class-means not found at {f}\n"
              f"  run:  python experiments/persistent_homology_grokking.py --neural --seeds {args.seed}")
        sys.exit(1)
    C = np.load(f)
    p, D = C.shape

    print("=" * 74)
    print(f"FUNCTIONAL FFT FORK  --  hidden class-means C[s], s = a+b mod {p}   (seed {args.seed})")
    print(f"  shape {C.shape} = (p classes x hidden dim);  spectrum folded to k=1..{p // 2}")
    print("=" * 74)
    print("  CALIBRATION baselines (identical pipeline):", flush=True)
    show("white noise (lookup)", spectrum(rng.standard_normal((p, D))))
    s = np.arange(p)
    keys = [1, 5, 12]
    tones = np.stack([np.cos(2 * np.pi * keys[d % len(keys)] * s / p + rng.uniform(0, 2 * np.pi))
                      for d in range(D)], axis=1)
    show("clean 3-tone Fourier", spectrum(tones))
    print("-" * 74)
    print("  OBSERVED grokked representation:", flush=True)
    obs = spectrum(C)
    show("hidden class-means", obs)
    print("-" * 74)

    # Data-driven lean: where does the observed PR sit relative to the brackets?
    white_pr = float(p // 2)                            # ideal white PR ~ n
    lean = ("FOURIER-FOLDED RIBBON (few key frequencies dominate)"
            if (obs["pr"] < 0.4 * white_pr and obs["top5"] > 0.35)
            else "NON-FOURIER ALGEBRAIC CRYSTALLIZATION (broadband, ~white)"
            if obs["pr"] > 0.7 * white_pr
            else "INTERMEDIATE -- partial frequency concentration; inspect spectrum")
    print(f"  LEAN: {lean}", flush=True)
    print("=" * 74)


if __name__ == "__main__":
    main()
