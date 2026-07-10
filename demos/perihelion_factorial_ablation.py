"""
perihelion_factorial_ablation.py
================================
Definitive full-factorial (2^3) overnight ablation of the "Perihelion"
parameter-free controller's claimed grokking mechanisms, grounded against the
actual controller code (perihelion/core/sgc_autonomous_controller.py, tag
sgc-autonomous-controller-v1) and the SGC Lean kernel.

WHY (ground-truthing, this session):
  Artemis described three mechanisms. Cross-checking the code + kernel:
    (1) "Fisher-Rao LR = 1/sqrt(N)" -> NOT in the code (real LR control is a
        +/-20% homeostasis nudge). We test it anyway as a free hyperparameter:
        LR 1e-3 (standard) vs 3e-3 (the muP/Fisher-Rao-adjacent "hot" rate).
    (2) "Dynamic WD excavation = lambda*.eps^2" -> real, but ~= a constant WD~1.
    (3) "Zero-lag chi_g quench cuts the plateau" -> MISLABELED. The real trigger
        is train_acc>=0.99 (memorization onset), and
        src/SGC/ContinualLearning/AdiabaticInvariant.lean : `adiabatic_freeze`
        PROVES (adiabatic protection) =/=> (defect collapse). Conservation is
        not collapse: the quench cannot CREATE a grok, it can only PRESERVE the
        state it fires into. Quench too early => the dumb memorized state is
        frozen forever.

THE TWO FALSIFIABLE QUESTIONS:
  (A) QUENCH CAUSALITY. Does the dynamic transition (ramp WD 0.1->2.0 + freeze
      noise on onset) ACCELERATE grok95, or is it consolidation-only? The
      Noise x Quench interaction separates "accelerates the existing route" from
      "merely supplies the compression the noise-off arms lacked."
  (B) RATE- vs EXPLORATION-LIMITED. Does 3x LR speed grok, and how much does
      exploration noise actually contribute?

DESIGN (per 2026-06-17 spec + smoke-test correction):
  The spec proposed baseline WD=1.0 so quench-OFF still groks, isolating the
  quench as a pure *transition*. But the smoke showed AdamW wd=1.0 is ABOVE the
  memorization ceiling at lr=1e-3 (net stuck ~35% train) -> the low-LR cells
  never even memorize. So we use the VALIDATED exploration WD = 0.1 (memorizes;
  groks-with-noise ~1534) and recover the original intent via the Noise x Quench
  INTERACTION: if quench helps only when noise is OFF, it is a WD-compression
  substitute, not an accelerator of the noise route (quantifies "is it magic?").

  Baseline exploration WD = 0.1 for ALL arms.
    - Quench OFF: WD pinned at 0.1 the ENTIRE run; noise (if ON) active throughout.
    - Quench ON : on sustained train_acc>=0.99 (5 epochs) -> WD ramps linearly
      0.1 -> 2.0 over 200 epochs AND noise (if ON) is frozen to 0.0.

  Factors (2^3 = 8 arms), paired over 8 seeds (42-49) => 64 runs:
    A  LR     : 1e-3  vs 3e-3
    B  Noise  : OFF   vs ON  (SVD-diagonal, matched Frobenius ||dW||_F ~ 0.1/matrix)
    C  Quench : OFF   vs ON

  Same seed => identical 30/70 data split AND model init across all 8 arms, so
  the only difference between arms is the factor settings (clean paired deltas).

Reuses validated GrokMLP / ModularAdditionDataset from sgc_grokking_phase6_1.py.
Non-destructive: writes only to logs/perihelion_ablation/.

Usage:
  python perihelion_factorial_ablation.py --smoke           # 1 seed, sanity+timing
  python perihelion_factorial_ablation.py --seeds 42-49     # full n=8 overnight
"""

import argparse
import csv
import os
import time
from dataclasses import dataclass
from typing import List, Optional

import numpy as np
import torch
import torch.nn as nn

from sgc_grokking_phase6_1 import GrokMLP, ModularAdditionDataset

LOG_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       "logs", "perihelion_ablation")
RESULTS_CSV = os.path.join(LOG_DIR, "grok_results.csv")


# ─────────────────────────────────────────────────────────────────────────────
# SVD-diagonal noise at matched Frobenius norm (||dW||_F = noise_scale per matrix)
# ─────────────────────────────────────────────────────────────────────────────

def inject_svd_noise(model: nn.Module, device: str, noise_scale: float) -> float:
    """Flat SVD-diagonal perturbation, amplitude-matched per 2D weight.

    dW = U diag(Z) Vh with Z ~ N(0,I) renormalized so ||Z||_2 = noise_scale.
    Since U,Vh have orthonormal columns/rows, ||dW||_F = ||Z||_2 = noise_scale
    EXACTLY -> a clean, frame-preserving, matched-amplitude pump (no envelope;
    today's A/B showed the Hermite envelope is null at matched amplitude).
    1D params (biases) are skipped to keep amplitude controlled. Returns total
    ||dW||_F injected (diagnostic).
    """
    total = 0.0
    with torch.no_grad():
        for _name, param in model.named_parameters():
            if param.dim() != 2:
                continue
            U, S, Vh = torch.linalg.svd(param.data, full_matrices=False)
            Z = torch.randn(S.shape[0], device=device)
            nz = torch.linalg.norm(Z)
            if nz > 1e-12:
                Z = Z / nz * noise_scale
            dW = (U * Z.unsqueeze(0)) @ Vh
            param.add_(dW)
            total += float(torch.linalg.norm(dW).item())
    return total


# ─────────────────────────────────────────────────────────────────────────────
# Data -> GPU-resident tensors (fast full-batch eval each epoch)
# ─────────────────────────────────────────────────────────────────────────────

def build_tensors(p: int, train_fraction: float, seed: int, device: str):
    tr = ModularAdditionDataset(p=p, train=True, train_fraction=train_fraction, seed=seed)
    te = ModularAdditionDataset(p=p, train=False, train_fraction=train_fraction, seed=seed)

    def to_xy(ds):
        xs = torch.stack([ds[i][0] for i in range(len(ds))]).to(device)
        ys = torch.tensor([ds[i][1] for i in range(len(ds))], dtype=torch.long).to(device)
        return xs, ys

    Xtr, Ytr = to_xy(tr)
    Xte, Yte = to_xy(te)
    return Xtr, Ytr, Xte, Yte


# ─────────────────────────────────────────────────────────────────────────────
# Arms / results
# ─────────────────────────────────────────────────────────────────────────────

@dataclass
class Arm:
    name: str
    lr: float
    noise_on: bool
    quench_on: bool


@dataclass
class RunResult:
    seed: int
    arm: str
    lr: float
    noise_on: bool
    quench_on: bool
    onset_epoch: int = -1
    grok90: int = -1
    grok95: int = -1
    mem2grok95: int = -1          # grok95 - onset_epoch (memorize->grok gap)
    final_test_acc: float = 0.0
    peak_test_acc: float = 0.0
    epochs_run: int = 0
    wall_sec: float = 0.0
    status: str = ""


def run_arm(arm: Arm, seed: int, *, p: int = 97, hidden: int = 128,
            train_fraction: float = 0.3, batch_size: int = 32,
            wd_explore: float = 0.1, wd_quench: float = 2.0,
            noise_scale: float = 0.1, onset_acc: float = 0.99,
            onset_patience: int = 5, anneal_epochs: int = 200,
            max_epochs: int = 4000, post_grok_epochs: int = 200,
            device: str = "cuda") -> RunResult:
    """Train one (arm, seed) and return grok timing + diagnostics."""
    t0 = time.time()

    # Seed BEFORE init so data split + model init are seed-determined and
    # arm-independent (paired design). Data split uses its own RandomState(seed).
    torch.manual_seed(seed)
    np.random.seed(seed)
    Xtr, Ytr, Xte, Yte = build_tensors(p, train_fraction, seed, device)
    n_train = Xtr.shape[0]

    torch.manual_seed(seed)
    model = GrokMLP(p=p, hidden_dim=hidden).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=arm.lr, weight_decay=wd_explore)
    ce = nn.CrossEntropyLoss()

    res = RunResult(seed=seed, arm=arm.name, lr=arm.lr,
                    noise_on=arm.noise_on, quench_on=arm.quench_on)

    onset_epoch = -1
    onset_streak = 0
    stop_at: Optional[int] = None

    for epoch in range(1, max_epochs + 1):
        # ── train (mini-batch) ──────────────────────────────────────────────
        model.train()
        perm = torch.randperm(n_train, device=device)
        for i in range(0, n_train, batch_size):
            idx = perm[i:i + batch_size]
            opt.zero_grad()
            loss = ce(model(Xtr[idx]), Ytr[idx])
            loss.backward()
            opt.step()

        # ── quench schedule (the controller's REAL mechanism) ───────────────
        # WD pinned at wd_explore until onset; if quench_on, ramp 1.0->2.0 over
        # anneal_epochs after onset, and freeze exploration noise.
        in_quench = arm.quench_on and onset_epoch >= 0
        if in_quench:
            prog = min(1.0, (epoch - onset_epoch) / max(1, anneal_epochs))
            wd_now = wd_explore + prog * (wd_quench - wd_explore)
        else:
            wd_now = wd_explore
        for g in opt.param_groups:
            g["weight_decay"] = wd_now

        # ── exploration noise (frozen once quench fires) ────────────────────
        noise_active = arm.noise_on and not in_quench
        if noise_active:
            inject_svd_noise(model, device, noise_scale)

        # ── eval (full-batch, cheap) ────────────────────────────────────────
        model.eval()
        with torch.no_grad():
            tr_acc = (model(Xtr).argmax(1) == Ytr).float().mean().item()
            te_acc = (model(Xte).argmax(1) == Yte).float().mean().item()

        res.peak_test_acc = max(res.peak_test_acc, te_acc)
        res.final_test_acc = te_acc

        # ── onset detection (memorization complete) ─────────────────────────
        if onset_epoch < 0:
            onset_streak = onset_streak + 1 if tr_acc >= onset_acc else 0
            if onset_streak >= onset_patience:
                onset_epoch = epoch - onset_patience + 1
                res.onset_epoch = onset_epoch

        # ── grok milestones ─────────────────────────────────────────────────
        if res.grok90 < 0 and te_acc >= 0.90:
            res.grok90 = epoch
        if res.grok95 < 0 and te_acc >= 0.95:
            res.grok95 = epoch
            if res.onset_epoch >= 0:
                res.mem2grok95 = epoch - res.onset_epoch
            stop_at = epoch + post_grok_epochs  # watch consolidation then stop

        if epoch % 200 == 0 or epoch == 1:
            print(f"  [{arm.name} s{seed}] ep{epoch:5d} tr={tr_acc*100:5.1f}% "
                  f"te={te_acc*100:5.1f}% wd={wd_now:.2f} noise={int(noise_active)} "
                  f"onset={onset_epoch}", flush=True)

        if stop_at is not None and epoch >= stop_at:
            res.status = "grokked"
            res.epochs_run = epoch
            break
    else:
        res.epochs_run = max_epochs
        res.status = "grokked" if res.grok95 >= 0 else "censored"

    res.wall_sec = time.time() - t0
    print(f"  => [{arm.name} s{seed}] grok95={res.grok95} grok90={res.grok90} "
          f"onset={res.onset_epoch} mem2grok={res.mem2grok95} "
          f"peak_te={res.peak_test_acc*100:.1f}% [{res.status}] "
          f"({res.wall_sec:.0f}s)", flush=True)
    return res


# ─────────────────────────────────────────────────────────────────────────────
# Driver
# ─────────────────────────────────────────────────────────────────────────────

def build_arms() -> List[Arm]:
    arms = []
    for lr in (1e-3, 3e-3):
        for noise_on in (False, True):
            for quench_on in (False, True):
                arms.append(Arm(
                    name=f"lr{lr:g}_n{int(noise_on)}_q{int(quench_on)}",
                    lr=lr, noise_on=noise_on, quench_on=quench_on))
    return arms


def parse_seeds(spec: str) -> List[int]:
    if "-" in spec:
        a, b = spec.split("-")
        return list(range(int(a), int(b) + 1))
    return [int(s) for s in spec.split(",")]


CSV_FIELDS = ["timestamp", "seed", "arm", "lr", "noise_on", "quench_on",
              "onset_epoch", "grok90", "grok95", "mem2grok95",
              "final_test_acc", "peak_test_acc", "epochs_run", "wall_sec",
              "max_epochs", "status"]


def append_result(res: RunResult, max_epochs: int):
    os.makedirs(LOG_DIR, exist_ok=True)
    new = not os.path.exists(RESULTS_CSV)
    with open(RESULTS_CSV, "a", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        if new:
            w.writerow(CSV_FIELDS)
        w.writerow([
            time.strftime("%Y-%m-%dT%H:%M:%S"), res.seed, res.arm, res.lr,
            int(res.noise_on), int(res.quench_on), res.onset_epoch, res.grok90,
            res.grok95, res.mem2grok95, f"{res.final_test_acc:.4f}",
            f"{res.peak_test_acc:.4f}", res.epochs_run, f"{res.wall_sec:.1f}",
            max_epochs, res.status])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seeds", type=str, default="42-49")
    ap.add_argument("--max_epochs", type=int, default=4000)
    ap.add_argument("--batch_size", type=int, default=32)
    ap.add_argument("--noise_scale", type=float, default=0.1)
    ap.add_argument("--smoke", action="store_true",
                    help="1 seed (42), max_epochs=2500, timing/sanity only")
    args = ap.parse_args()

    device = "cuda" if torch.cuda.is_available() else "cpu"
    seeds = [42] if args.smoke else parse_seeds(args.seeds)
    max_epochs = 2500 if args.smoke else args.max_epochs
    arms = build_arms()

    print(f"[factorial] device={device} seeds={seeds} arms={len(arms)} "
          f"max_epochs={max_epochs} batch={args.batch_size} "
          f"noise_scale={args.noise_scale} wd_explore=0.1->2.0")
    print(f"[factorial] arms: {[a.name for a in arms]}")
    print(f"[factorial] results -> {RESULTS_CSV}")

    grand_t0 = time.time()
    n_done = 0
    for seed in seeds:
        for arm in arms:
            res = run_arm(arm, seed, batch_size=args.batch_size,
                          noise_scale=args.noise_scale, max_epochs=max_epochs,
                          device=device)
            append_result(res, max_epochs)
            n_done += 1
            print(f"[factorial] progress {n_done}/{len(seeds)*len(arms)} "
                  f"({time.time()-grand_t0:.0f}s elapsed)", flush=True)
    print(f"[factorial] DONE {n_done} runs in {time.time()-grand_t0:.0f}s "
          f"-> {RESULTS_CSV}")


if __name__ == "__main__":
    main()
