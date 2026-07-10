"""
aggregate_perihelion.py
=======================
Paired-by-seed factorial analysis of perihelion_factorial_ablation.py output.

Reads logs/perihelion_ablation/grok_results.csv (one row per (seed, arm)) and
reports, for a chosen dependent variable (default grok95 = first epoch test>=0.95):

  1. Per-arm summary: mean +/- std grok epoch, grok-fraction (n_grokked / n_seeds).
  2. The 3 MAIN EFFECTS (LR, Noise, Quench) and all 2-way + 3-way INTERACTIONS,
     computed as standard 2^3 +/-1 contrasts, paired within each seed, then
     averaged over seeds with sem and a paired t-statistic.
  3. The PER-SEED SIGN VECTOR for every effect (the EDL-0007 discipline: never
     grade a sub-1.5x effect on the mean alone; report whether the seeds agree).

Sign convention: the DV is a grok EPOCH, so a NEGATIVE effect = FEWER epochs =
the factor ACCELERATES grokking. Censored runs (never grokked, grok95=-1) are
right-censored at the run's max_epochs cap; effects involving heavily-censored
cells are LOWER BOUNDS on the true acceleration (flagged).

Usage:
  python aggregate_perihelion.py                 # grok95
  python aggregate_perihelion.py --dv grok90
  python aggregate_perihelion.py --dv mem2grok95 # the memorize->grok gap
"""

import argparse
import csv
import math
import os
from collections import defaultdict

CSV_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "logs", "perihelion_ablation", "grok_results.csv")

FACTORS = ["LR", "Noise", "Quench"]
EFFECTS = ["LR", "Noise", "Quench",
           "LRxNoise", "LRxQuench", "NoisexQuench", "LRxNoisexQuench"]


def signs(row):
    """(+1/-1) coding: LR=+1 for 3e-3, Noise=+1 for ON, Quench=+1 for ON."""
    a = +1 if float(row["lr"]) >= 2e-3 else -1
    b = +1 if row["noise_on"] == "1" else -1
    c = +1 if row["quench_on"] == "1" else -1
    return a, b, c


def contrast(name):
    return {
        "LR": lambda a, b, c: a,
        "Noise": lambda a, b, c: b,
        "Quench": lambda a, b, c: c,
        "LRxNoise": lambda a, b, c: a * b,
        "LRxQuench": lambda a, b, c: a * c,
        "NoisexQuench": lambda a, b, c: b * c,
        "LRxNoisexQuench": lambda a, b, c: a * b * c,
    }[name]


def mean(xs):
    return sum(xs) / len(xs) if xs else float("nan")


def std(xs):
    if len(xs) < 2:
        return float("nan")
    m = mean(xs)
    return math.sqrt(sum((x - m) ** 2 for x in xs) / (len(xs) - 1))


def fmt_signs(vals, tol=1e-9):
    return "[" + "".join("+" if v > tol else ("-" if v < -tol else "0")
                         for v in vals) + "]"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--csv", default=CSV_PATH)
    ap.add_argument("--dv", default="grok95",
                    choices=["grok95", "grok90", "mem2grok95"])
    ap.add_argument("--cap", type=int, default=0,
                    help="censoring cap; 0 => use each row's max_epochs")
    args = ap.parse_args()

    if not os.path.exists(args.csv):
        print(f"[aggregate] no results yet at {args.csv}")
        return

    rows = []
    with open(args.csv, newline="", encoding="utf-8") as f:
        for row in csv.DictReader(f):
            rows.append(row)
    if not rows:
        print("[aggregate] results file is empty")
        return

    # by_seed[seed][arm] = row ; by_arm[arm] = [rows]
    by_seed = defaultdict(dict)
    by_arm = defaultdict(list)
    for row in rows:
        by_seed[row["seed"]][row["arm"]] = row
        by_arm[row["arm"]].append(row)

    def capof(row):
        if args.cap > 0:
            return args.cap
        try:
            return int(row.get("max_epochs", 4000) or 4000)
        except ValueError:
            return 4000

    def dv_value(row):
        v = int(row[args.dv])
        return capof(row) if v < 0 else v

    print(f"\n{'='*74}\nPERIHELION FACTORIAL  --  DV = {args.dv}  "
          f"(lower epoch = faster grok)\n{'='*74}")
    print(f"source: {args.csv}")
    print(f"rows: {len(rows)}  seeds: {len(by_seed)}  arms: {len(by_arm)}")

    # ── 1. per-arm summary ──────────────────────────────────────────────────
    print(f"\n{'arm':<18}{'grok95 mean+/-std':>22}{'grok-frac':>12}"
          f"{'grok90':>10}{'mem2grok':>10}")
    print("-" * 74)
    for arm in sorted(by_arm):
        rs = by_arm[arm]
        g95 = [int(r["grok95"]) for r in rs if int(r["grok95"]) >= 0]
        g90 = [int(r["grok90"]) for r in rs if int(r["grok90"]) >= 0]
        m2g = [int(r["mem2grok95"]) for r in rs if int(r["mem2grok95"]) >= 0]
        frac = f"{len(g95)}/{len(rs)}"
        gm = f"{mean(g95):.0f}+/-{std(g95):.0f}" if g95 else "never"
        print(f"{arm:<18}{gm:>22}{frac:>12}"
              f"{(f'{mean(g90):.0f}' if g90 else '-'):>10}"
              f"{(f'{mean(m2g):.0f}' if m2g else '-'):>10}")

    # ── 2/3. paired factorial effects ───────────────────────────────────────
    complete_seeds = [s for s, d in by_seed.items() if len(d) >= 8]
    incomplete = [s for s, d in by_seed.items() if len(d) < 8]
    if incomplete:
        print(f"\n[note] {len(incomplete)} seed(s) incomplete (<8 arms), "
              f"excluded from paired effects: {sorted(incomplete)}")
    if not complete_seeds:
        print("\n[aggregate] no complete seeds yet (need all 8 arms). "
              "Effects will appear once seeds finish.")
        return

    # censoring exposure
    n_cells = 0
    n_cens = 0
    for s in complete_seeds:
        for row in by_seed[s].values():
            n_cells += 1
            if int(row[args.dv]) < 0:
                n_cens += 1
    print(f"\nPaired over {len(complete_seeds)} complete seed(s): "
          f"{sorted(complete_seeds)}")
    if n_cens:
        print(f"[warn] {n_cens}/{n_cells} cells censored (never grokked, "
              f"capped at max_epochs) -> effects are LOWER BOUNDS.")

    eff_by_seed = defaultdict(list)
    for s in complete_seeds:
        Y = {}
        for row in by_seed[s].values():
            Y[signs(row)] = dv_value(row)
        if len(Y) < 8:
            continue
        for name in EFFECTS:
            fn = contrast(name)
            eff_by_seed[name].append(sum(fn(*k) * Y[k] for k in Y) / 4.0)

    print(f"\n{'effect':<18}{'mean(ep)':>10}{'sem':>9}{'t':>7}"
          f"{'n':>4}   per-seed-signs")
    print("-" * 74)
    for name in EFFECTS:
        vals = eff_by_seed[name]
        m, sd, n = mean(vals), std(vals), len(vals)
        sem = sd / math.sqrt(n) if n > 1 else float("nan")
        t = m / sem if sem and not math.isnan(sem) and sem != 0 else float("nan")
        marker = ""
        if name in FACTORS and n > 1 and not math.isnan(t):
            if abs(t) >= 2.0:
                marker = "  <== significant"
        print(f"{name:<18}{m:>10.1f}{sem:>9.1f}{t:>7.2f}{n:>4}   "
              f"{fmt_signs(vals)}{marker}")

    # ── interpretation crib ─────────────────────────────────────────────────
    print(f"\n{'-'*74}\nReading guide:")
    print("  - NEGATIVE mean => factor REDUCES grok epoch => ACCELERATES.")
    print("  - Quench main effect ~ 0 (and sign vector mixed) => the dynamic")
    print("    transition is CONSOLIDATION-ONLY (consistent with adiabatic_freeze:")
    print("    protection does not cause collapse).")
    print("  - LR strongly negative + Noise ~ 0 => grokking is RATE-limited here,")
    print("    not exploration-limited (the one improvable lever is LR).")
    print(f"{'='*74}\n")


if __name__ == "__main__":
    main()
