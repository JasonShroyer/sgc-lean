#!/usr/bin/env python3
"""recurrent_phase_hardening.py -- Leg 3c (decisions/0010 follow-on): armour the singularity.

Leg 3b located the topological switch in alpha in (0, 0.01] at L=12, seed 42: the FIRST nonzero
gate (0.01) already carries a full k=1 ring (b1>=1, topH1 > tau1*) at only 15% accuracy.  Two open
questions remain before we can call it a seed-invariant first-order step at the alpha=0 singularity:

  1. SUB-0.01 STRUCTURE -- is the ring still ON a DECADE lower (alpha=0.001), or is there a knee
     between 1e-3 and 1e-2?  A log-spaced grid {0, 0.001, 0.002, 0.005, 0.01} resolves it.
  2. SEED-INVARIANCE -- does the step land at the same place for seeds 43, 44, 45 (not just 42)?

Reuses the IDENTICAL model / train_one / metrics from recurrent_phase_transition and the SAME
calibrated reader (run_calibration -> tau1*), so every number is on the footing of all of 0010.
"""
import argparse
import os
import sys

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

from persistent_homology_grokking import run_calibration                 # noqa: E402
from recurrent_phase_transition import train_one, metrics                # noqa: E402

import torch                                                             # noqa: E402

LOGDIR = os.path.join(_HERE, "logs", "ph_grok")
_lines = []


def out(s=""):
    print(s, flush=True)
    _lines.append(s)


def _write(path):
    os.makedirs(LOGDIR, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(_lines) + "\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seeds", default="43,44,45")
    ap.add_argument("--alphas", default="0.0,0.001,0.002,0.005,0.01")
    ap.add_argument("--L", type=int, default=12)
    ap.add_argument("--iters", type=int, default=2500)
    args = ap.parse_args()
    seeds = [int(s) for s in args.seeds.split(",")]
    alphas = [float(a) for a in args.alphas.split(",")]
    device = "cuda" if torch.cuda.is_available() else "cpu"
    path = os.path.join(LOGDIR, f"phase_hardening_loggrid_L{args.L}_seeds{seeds[0]}-{seeds[-1]}.txt")

    out("=" * 80)
    out(f"RECURRENT PHASE HARDENING (Leg 3c)  --  log-grid alpha={alphas}")
    out(f"  L={args.L}  seeds={seeds}  iters={args.iters}")
    out("  Q1: is the ring ON a decade below 0.01 (alpha=0.001)?  Q2: seed-invariant switch?")
    out("=" * 80)
    gate_ok, tau1, tau2 = run_calibration()
    if not gate_ok:
        out("  reader NOT calibrated; abort."); _write(path); sys.exit(1)
    out(f"\n  device={device}  reader tau1*={tau1:.3f}")
    out(f"\n  {'seed':>5} {'alpha':>7} {'testacc':>8} {'k*':>4} {'k*pwr%':>7} {'b1full':>7} "
        f"{'b1dom':>6} {'topH1':>6}")

    switch = {}    # seed -> first alpha with b1>=1 AND k*<=3 (ring on)
    for seed in seeds:
        for a in alphas:
            acc, Hmean, cover = train_one(a, args.L, args.iters, seed, device=device)
            m = metrics(Hmean, tau1)
            ring_on = (m["b1_full"] >= 1 and m["kstar"] <= 3 and m["top"] >= tau1)
            if ring_on and seed not in switch:
                switch[seed] = a
            flag = "  <- ring ON" if ring_on else ""
            out(f"  {seed:>5d} {a:>7.3f} {acc:>8.3f} {m['kstar']:>4d} {m['pwr']*100:>7.1f} "
                f"{m['b1_full']:>7d} {m['b1_dom']:>6d} {m['top']:>6.3f}{flag}")
            _write(path)
        out("")

    out("=" * 80)
    nonzero = [a for a in alphas if a > 0]
    amin = min(nonzero) if nonzero else None
    on_at_min = [s for s in seeds if switch.get(s) == amin]
    out(f"  switch location (first alpha with k=low ring above tau1*) per seed: "
        f"{ {s: switch.get(s, 'never') for s in seeds} }")
    if amin is not None and len(on_at_min) == len(seeds):
        out(f"  VERDICT: ring is ON at the SMALLEST nonzero gate alpha={amin:g} for ALL "
            f"{len(seeds)} seeds -> switch bounded to (0, {amin:g}]; seed-invariant step at the "
            f"alpha=0 singularity CONFIRMED a decade tighter than Leg 3b.")
    elif on_at_min:
        out(f"  VERDICT: ring ON at alpha={amin:g} for {len(on_at_min)}/{len(seeds)} seeds; "
            f"others switch higher -> mild seed-dependence, inspect rows.")
    else:
        out(f"  VERDICT: ring NOT on at alpha={amin:g} -> there IS a knee between {amin:g} and the "
            f"higher gates; the switch is not at the pure singularity. Inspect rows.")
    out("=" * 80)
    print(f"\n[summary written -> {path}]", flush=True)
    _write(path)


if __name__ == "__main__":
    main()
