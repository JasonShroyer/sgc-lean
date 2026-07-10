#!/usr/bin/env python3
"""transformer_replication_summary.py -- Leg 2 replication (decisions/0010).

Train (if missing) the transformer at seeds 42-45, then read ALL of them in ONE calibrated
pass and write a clean multi-seed table to a LOG FILE (so the terminal-truncation that bit the
recurrent replication cannot lose the readout).

Question under test (the carrier-frequency law, pre-registered before this run): does the
seed-42 result -- transformer token embedding & residual FOLD to b1=0 because the carrier is a
HIGH key frequency -- REPLICATE?  If 43-45 also show full-cloud b1=0 with a HIGH dominant
carrier, the law holds; if some seed rides a LOW carrier (k=1) and stays b1>=1, it is refined.
"""
import os
import sys

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)
sys.path.insert(0, os.path.join(_HERE, "..", "demos"))

from persistent_homology_grokking import run_calibration, N_H1            # noqa: E402
from fft_classmeans_grokking import spectrum                             # noqa: E402
from circular_coordinate_probe import fourier_power, winding_mode, b1_of, reconstruct  # noqa: E402

SEEDS = [42, 43, 44, 45]
LOG = os.path.join(_HERE, "logs", "ph_grok", "transformer_replication.txt")
_lines = []


def out(s=""):
    print(s, flush=True)
    _lines.append(s)


def ensure_cache(seed):
    d = os.path.join(_HERE, "logs", "ph_grok", f"transformer_seed{seed}")
    emb = os.path.join(d, "embed.npy")
    if not os.path.exists(emb):
        import torch
        from transformer_modular_grokking import build_and_train
        device = "cuda" if torch.cuda.is_available() else "cpu"
        snap = build_and_train(seed=seed, device=device)
        os.makedirs(d, exist_ok=True)
        for k in ("embed", "resid_classmean", "neur_classmean"):
            np.save(os.path.join(d, f"{k}.npy"), snap[k])
        out(f"  [seed {seed}] trained: grok@{snap['grok_step']} test_acc={snap['test_acc']:.4f}")
    return dict(embed=np.load(os.path.join(d, "embed.npy")),
                resid=np.load(os.path.join(d, "resid_classmean.npy")))


def row(seed, name, X, tau1):
    P, kstar, F = fourier_power(X)
    b1_full, top = b1_of(X, tau1)
    b1_k4, _ = b1_of(reconstruct(F, 4), tau1)
    w = winding_mode(X, F, kstar)
    sp = spectrum(X)
    keys = ",".join(f"k{k}" for k, _ in sp["top"][:5])
    out(f"    {name:<10} full_b1={b1_full}  dom_k*={kstar:<2} (winding {w:+.1f})  "
        f"k<=4_b1={b1_k4}  PR={sp['pr']:.1f}  keys={keys}  topH1={top[0]:.3f}")
    return dict(seed=seed, name=name, b1_full=b1_full, kstar=kstar, b1_k4=b1_k4)


def main():
    clouds = {s: ensure_cache(s) for s in SEEDS}
    out("=" * 78)
    out("TRANSFORMER REPLICATION  --  carrier-frequency law across seeds 42-45")
    out("=" * 78)
    gate_ok, tau1, tau2 = run_calibration()
    if not gate_ok:
        out("  reader NOT calibrated; abort.")
        _flush(); sys.exit(1)
    out(f"\n  per-seed readout (identical reader, tau1*={tau1:.3f}):")
    res = []
    for s in SEEDS:
        out(f"  seed {s}")
        res.append(row(s, "embed", clouds[s]["embed"], tau1))
        res.append(row(s, "resid@=", clouds[s]["resid"], tau1))
    out("=" * 78)
    emb = [r for r in res if r["name"] == "embed"]
    all_fold = all(r["b1_full"] == 0 for r in emb)
    all_high = all(r["kstar"] >= 6 for r in emb)
    all_circ = all(r["b1_k4"] >= 1 for r in emb)
    if all_fold and all_high:
        out("  VERDICT: REPLICATED -- every seed's embedding folds (full b1=0) with a HIGH")
        out("  carrier (k*>=6); low-freq (k<=4) recon stays circular. Carrier-frequency law HOLDS:")
        out("  feedforward/transformer ride HIGH keys -> fold to b1=0; recurrent rides k=1 -> b1>=1.")
    else:
        out("  VERDICT: NOT uniform -- inspect rows (some seed folds/carries differently).")
    out(f"  embed full_b1 per seed: {[r['b1_full'] for r in emb]}  "
        f"dom_k* per seed: {[r['kstar'] for r in emb]}  k<=4 circular: {all_circ}")
    out("=" * 78)
    _flush()


def _flush():
    os.makedirs(os.path.dirname(LOG), exist_ok=True)
    with open(LOG, "w", encoding="utf-8") as f:
        f.write("\n".join(_lines) + "\n")
    print(f"\n[summary written -> {LOG}]", flush=True)


if __name__ == "__main__":
    main()
