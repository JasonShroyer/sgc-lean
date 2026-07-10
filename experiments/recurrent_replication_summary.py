#!/usr/bin/env python3
"""recurrent_replication_summary.py -- read cached recurrent H[s] across seeds in ONE
calibrated pass, so the multi-seed b1 distribution is reported cleanly (no per-run
re-calibration, no terminal-truncation loss).  Caches written by recurrent_modular_grokking.py.
"""
import os
import sys

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

from persistent_homology_grokking import run_calibration, read_layer   # noqa: E402
from fft_classmeans_grokking import spectrum, show                     # noqa: E402

SEEDS = [42, 43, 44, 45]

clouds = {}
for s in SEEDS:
    f = os.path.join(_HERE, "logs", "ph_grok", f"recurrent_seed{s}", "recurrent_hidden_classmean.npy")
    if os.path.exists(f):
        clouds[s] = np.load(f)
    else:
        print(f"  [seed {s}] NO cache at {f}", flush=True)

print("=" * 78)
print("RECURRENT REPLICATION  --  cached H[s] (wd=1e-3, L=32); function then topology")
print("=" * 78)
print("  -- FFT (dominant ring harmonics):", flush=True)
for s, C in clouds.items():
    show(f"seed {s}", spectrum(C))

gate_ok, tau1, tau2 = run_calibration()
if not gate_ok:
    print("\n  >>> reader NOT calibrated; aborting (honest gate stop).")
    sys.exit(1)

print(f"\n{'='*78}\n  RECURRENT b1 ACROSS SEEDS  (identical reader, tau1*={tau1:.3f})\n{'='*78}", flush=True)
for s, C in clouds.items():
    read_layer(f"seed {s} H[s]", C, tau1, tau2, "ring b1>=1")
print("=" * 78, flush=True)
