#!/usr/bin/env python3
"""torus_h2_control.py -- Waypoint B control: validate the H2 protocol on KNOWN shapes.

The learned 2-torus reads b2=1 (H2 gap 8.4x) under the FULL p^2 skeleton but b2=0 (gap 1.1x) under
the calibrated 100-pt subsample.  Which protocol is right at N=289?  Settle it on synthetic clouds
with KNOWN topology, sampled IDENTICALLY to the learned torus (17x17 grid, R^256, matched noise):

  * genuine torus  T^2          (b1=2, b2=1) -- full-skeleton H2 gap should be HIGH; the 100-pt
                                                subsample may FALSE-NEGATIVE (under-resolved void)
  * figure-8 / wedge of 2 circles (b1=2, b2=0) -- NO 2-void: gap ~1x under BOTH protocols

If full-skeleton gives torus gap >> 1 and wedge gap ~1, then the learned net's full-skeleton gap
8.4x DECISIVELY means a genuine 2-torus, and the subsampled b2=0 is an under-sampling false negative
(not an over-count).  Uses the IDENTICAL calibrated reader (tau2*) and analyze/betti.
"""
import os
import sys

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

from persistent_homology_grokking import analyze, betti, run_calibration, N_H2, NB_H2  # noqa: E402

LOGDIR = os.path.join(_HERE, "logs", "ph_grok")
_lines = []


def out(s=""):
    print(s, flush=True)
    _lines.append(s)


def _write():
    os.makedirs(LOGDIR, exist_ok=True)
    path = os.path.join(LOGDIR, "torus_h2_control.txt")
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(_lines) + "\n")
    return path


def torus_grid(p=17, D=256, noise=0.03, seed=0):
    """Genuine flat torus, sampled on the SAME 17x17 grid as the learned code. b1=2, b2=1."""
    rng = np.random.default_rng(seed)
    s1, s2 = np.meshgrid(np.arange(p), np.arange(p))
    t, s = 2 * np.pi * s1.ravel() / p, 2 * np.pi * s2.ravel() / p
    base = np.stack([np.cos(t), np.sin(t), np.cos(s), np.sin(s)], 1)
    X = np.concatenate([base, np.zeros((len(base), D - 4))], 1)
    return X + noise * rng.standard_normal(X.shape)


def wedge_grid(p=17, D=256, noise=0.03, seed=0):
    """Figure-8: two unit circles tangent at the origin (share ONE point). b1=2, b2=0."""
    rng = np.random.default_rng(seed)
    n = p * p
    n1 = n // 2
    a = 2 * np.pi * np.arange(n1) / n1
    b = 2 * np.pi * np.arange(n - n1) / (n - n1)
    c1 = np.stack([-1 + np.cos(a), np.sin(a)], 1)          # circle centred (-1,0)
    c2 = np.stack([1 - np.cos(b), np.sin(b)], 1)           # circle centred (+1,0); both touch (0,0)
    base = np.concatenate([c1, c2], 0)
    X = np.concatenate([base, np.zeros((len(base), D - 2))], 1)
    return X + noise * rng.standard_normal(X.shape)


def read_h2(name, X, tau2, protocol):
    if protocol == "full":
        pd, tm = analyze(X, maxdim=2, n_sub=None, n_boot=1)
    else:
        pd, tm = analyze(X, maxdim=2, n_sub=N_H2, n_boot=NB_H2, base_seed=42)
    b2, _ = betti(pd[2], tau2)
    top = tm[2]
    gap = top[0] / (top[1] + 1e-9)
    out(f"    {name:<22} {protocol:<5}  b2={b2}  topH2=[{' '.join(f'{x:.3f}' for x in top[:5])}]  "
        f"gap={gap:.1f}x")
    _write()
    return b2, gap


def main():
    out("=" * 80)
    out("TORUS H2 PROTOCOL CONTROL  --  full-skeleton vs 100-pt subsample on KNOWN shapes (N=289)")
    out("  learned torus: full b2=1 gap 8.4x  |  subsample b2=0 gap 1.1x  -- which is right?")
    out("=" * 80)
    gate_ok, tau1, tau2 = run_calibration()
    if not gate_ok:
        out("  reader NOT calibrated; abort."); _write(); sys.exit(1)
    out(f"\n  reader tau2*={tau2:.3f}   clouds: 17x17 grid in R^256, noise 0.03\n")

    torus = torus_grid()
    wedge = wedge_grid()

    out("  FAST subsample reads (100x4) first:")
    t_sub = read_h2("torus T^2 (b2=1)", torus, tau2, "sub")
    w_sub = read_h2("wedge fig-8 (b2=0)", wedge, tau2, "sub")

    out("\n  SLOW full-skeleton reads (289 pts, ~13 min each):")
    t_full = read_h2("torus T^2 (b2=1)", torus, tau2, "full")
    w_full = read_h2("wedge fig-8 (b2=0)", wedge, tau2, "full")

    out("\n" + "=" * 80)
    out(f"  full-skeleton:  torus gap={t_full[1]:.1f}x (b2={t_full[0]})   "
        f"wedge gap={w_full[1]:.1f}x (b2={w_full[0]})")
    out(f"  subsample100 :  torus gap={t_sub[1]:.1f}x (b2={t_sub[0]})   "
        f"wedge gap={w_sub[1]:.1f}x (b2={w_sub[0]})")
    if t_full[1] >= 3.0 and w_full[1] < 2.0:
        out("  VERDICT: full-skeleton DISCRIMINATES (torus gap high, wedge gap ~1). The learned net's")
        out("  full-skeleton gap 8.4x therefore certifies a GENUINE 2-TORUS; the subsampled b2=0 is an")
        out(f"  under-sampling FALSE NEGATIVE{' (synthetic torus subsample also fails)' if t_sub[0]==0 else ''}.")
    else:
        out("  VERDICT: full-skeleton does NOT cleanly discriminate here -- inspect; the learned b2 claim")
        out("  must be hedged. (torus gap not high enough or wedge gap too high.)")
    out("=" * 80)
    print(f"\n[summary -> {_write()}]", flush=True)


if __name__ == "__main__":
    main()
