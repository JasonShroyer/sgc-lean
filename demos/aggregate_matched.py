#!/usr/bin/env python3
"""
Aggregate the amplitude-matched A/B across seeds -> error-barred verdict.
========================================================================

Reads every  logs/matched_ab/matched_<mode>_seed<seed>.csv  produced by
wavelet_gauge_matched_ab.py and answers the two open questions with error bars:

    Q1  ENVELOPE NULL?   wavelet  vs  matched_svd_flat
    Q2  GAUGE WIN REAL?  matched_svd_flat  vs  matched_weight_scaled

Grok epochs are read at the CSV's tomography resolution (every 50 ep) -- the first
logged epoch whose test_acc crosses the threshold. That coarse grid is fine for an
effect of hundreds of epochs.

The decisive statistic is PAIRED BY SEED: the same seed fixes the data split and
init, so per-seed differences cancel the (large) seed-to-seed grok jitter. We
report, over seeds where BOTH arms grokked, the mean +/- std of the per-seed
difference (and ratio). If the paired difference's error bar straddles 0, the
effect is not resolved at this n.

Run:
    python aggregate_matched.py
    python aggregate_matched.py --grok 0.95
"""

import argparse
import csv
import math
import re
from collections import defaultdict
from pathlib import Path

_DEMOS = Path(__file__).resolve().parent
_PAT = re.compile(r"matched_(?P<mode>.+)_seed(?P<seed>\d+)\.csv$")


def grok_epoch(csv_path: Path, thresh: float) -> int:
    """First logged epoch with test_acc >= thresh, or -1 if never."""
    with open(csv_path, newline="") as f:
        for row in csv.DictReader(f):
            try:
                if float(row["test_acc"]) >= thresh:
                    return int(row["epoch"])
            except (KeyError, ValueError):
                continue
    return -1


def mean_std(xs):
    if not xs:
        return float("nan"), float("nan")
    m = sum(xs) / len(xs)
    if len(xs) == 1:
        return m, 0.0
    v = sum((x - m) ** 2 for x in xs) / (len(xs) - 1)
    return m, math.sqrt(v)


def fmt(m, s):
    return "nan" if m != m else (f"{m:6.0f} +/- {s:4.0f}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", type=str, default=str(_DEMOS / "logs" / "matched_ab"))
    ap.add_argument("--grok", type=float, default=0.95)
    args = ap.parse_args()

    d = Path(args.dir)
    # mode -> {seed: grok_epoch}
    table = defaultdict(dict)
    results_csv = d / "grok_results.csv"
    col = "grok95" if args.grok >= 0.925 else "grok90"
    if results_csv.exists():
        # Preferred: exact per-epoch grok epochs written by the experiment.
        with open(results_csv, newline="") as f:
            for row in csv.DictReader(f):
                try:
                    seed, g = int(row["seed"]), int(row[col])
                except (KeyError, ValueError):
                    continue
                if g > 0:            # later rows (re-runs) overwrite earlier
                    table[row["mode"]][seed] = g
        src = f"grok_results.csv  (EXACT per-epoch, col={col})"
    else:
        # Fallback: scan per-arm CSVs (coarse 50-ep grid -- can miss the crossing).
        for p in sorted(d.glob("matched_*_seed*.csv")):
            m = _PAT.search(p.name)
            if not m:
                continue
            mode, seed = m.group("mode"), int(m.group("seed"))
            g = grok_epoch(p, args.grok)
            if g > 0:
                table[mode][seed] = g
        src = "per-arm CSV scan  (coarse 50-ep grid; UNRELIABLE)"

    print("#" * 84)
    print(f"AMPLITUDE-MATCHED A/B  --  grok threshold = {args.grok:.0%}")
    print(f"  dir: {d}")
    print(f"  source: {src}")
    print("#" * 84)

    order = ["wavelet", "matched_svd_flat", "matched_band",
             "matched_weight_scaled", "isotropic"]
    present = [m for m in order if m in table] + \
              [m for m in table if m not in order]

    print(f"\n{'mode':24s} | {'n':>2} | {'grok mean+/-std':>16} | seeds (epoch)")
    print("-" * 84)
    for mode in present:
        seeds = table[mode]
        m, s = mean_std(list(seeds.values()))
        detail = " ".join(f"{sd}:{ep}" for sd, ep in sorted(seeds.items()))
        print(f"{mode:24s} | {len(seeds):>2} | {fmt(m, s):>16} | {detail}")

    def paired(a, b, label):
        common = sorted(set(table.get(a, {})) & set(table.get(b, {})))
        if not common:
            print(f"\n{label}: no common seeds for {a} vs {b}")
            return
        diffs = [table[b][sd] - table[a][sd] for sd in common]  # b - a (epochs)
        ratios = [table[b][sd] / table[a][sd] for sd in common]
        dm, ds = mean_std(diffs)
        rm, rs = mean_std(ratios)
        print(f"\n{label}  ({a} -> {b}, paired over seeds {common})")
        print(f"    per-seed delta (b-a): {[f'{x:+d}' for x in diffs]}  "
              f"=> {dm:+.0f} +/- {ds:.0f} epochs")
        print(f"    per-seed ratio (b/a): {[f'{x:.2f}' for x in ratios]}  "
              f"=> {rm:.3f} +/- {rs:.3f}x")
        resolved = (abs(dm) > ds) and len(common) >= 2
        print(f"    -> {'RESOLVED' if resolved else 'NOT resolved'} at n={len(common)} "
              f"(|mean| {'>' if resolved else '<='} 1 std)")

    print("\n" + "=" * 84)
    print("Q1  ENVELOPE NULL?   (expect ~1.00x, delta ~0)")
    paired("wavelet", "matched_svd_flat", "Q1 envelope")
    print("\n" + "=" * 84)
    print("Q2  GAUGE / FRAME-ALIGNMENT WIN?   (Artemis predicts weight_scaled SLOWER)")
    paired("matched_svd_flat", "matched_weight_scaled", "Q2 gauge")
    paired("wavelet", "matched_weight_scaled", "Q2 gauge (vs wavelet)")
    print("=" * 84)


if __name__ == "__main__":
    main()
