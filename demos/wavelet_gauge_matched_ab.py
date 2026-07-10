#!/usr/bin/env python3
"""
Wavelet Gauge-Coupling — AMPLITUDE-MATCHED A/B (the decisive, honest run)
========================================================================

WHY THIS EXISTS
---------------
The original Phase-6.1 demo (sgc_grokking_phase6_1.py) shows a dramatic
"wavelet >> isotropic" result in the low-WD heat regime: wavelet-shaped SVD
noise lets the one-hot MLP memorise then grok (~epoch 1600 at 95%), while
`--noise_mode isotropic` cannot even memorise (train stuck ~3%).

BUT that comparison is amplitude-confounded. In the original:
    * wavelet   : unit-energy envelope in SVD space  -> ||dW||_F ~ noise_scale (=0.1)
    * isotropic : randn_like(W) * noise_scale         -> ||dW||_F ~ noise_scale*sqrt(numel)
For a 128x128 layer that is 0.1 vs 0.1*128 = 12.8  -> isotropic injects ~128x
MORE total perturbation every epoch. So the isotropic arm fails partly (mostly?)
because it is blasted with ~128x more noise, NOT necessarily because it is
"poorly gauge-coupled".

THE DECISIVE DESIGN (Artemis's plan, Option A + B)
--------------------------------------------------
Reproduce the EXACT Phase-6.1 setup (one-hot GrokMLP, modular addition mod 97,
30/70 split, CorrectedWaveletController: heat WD=0.1, kappa_contract trigger,
per-epoch injection) and vary ONLY the 2-D weight-matrix noise distribution.
Biases (dim<2) always get randn*noise_scale (identical across every arm), so the
single variable is the matrix envelope. Arms:

    wavelet               Hermite-Gaussian unit-energy SVD   (Phase-6.1 standard)   ||dW||_F~eta
    matched_svd_flat      FLAT unit-energy SVD envelope                              ||dW||_F~eta   <-- matches wavelet EXACTLY, only shape differs
    matched_band          FLAT over the central band the wavelet occupies, unit E   ||dW||_F~eta   <-- matched norm AND matched band (Option B)
    matched_weight_scaled randn in weight space, scaled by 1/sqrt(numel)            ||dW||_F~eta   <-- matched norm, weight-space (is the SVD basis special?)
    isotropic             randn_like(W) * noise_scale  (THE ORIGINAL)               ||dW||_F~eta*sqrt(numel)  <-- UNMATCHED reference (the ~128x blast)

WHAT EACH NUMBER MEANS (publish both, per Artemis)
--------------------------------------------------
    wavelet vs isotropic            = the massive PRACTICAL win of SVD-space
                                      self-normalisation (don't blast the net).
    wavelet vs matched_svd_flat     = the TRUE spectral gauge-coupling effect at
                                      matched amplitude (the discovery predicts
                                      wavelet still faster, ~2x). If they tie, the
                                      "gauge" win was really just amplitude.
    matched_band vs matched_svd_flat= does CONCENTRATING in the wavelet's band
                                      (the soft/mid singular modes) matter, vs
                                      spreading flat over all modes?
    matched_weight_scaled           = control: is the SVD frame itself special, or
                                      is matched amplitude enough?

DIAGNOSTICS per arm: grok@90% / grok@95% epoch (headline), plus kappa_grad =
<dW, ghat>^2 / ||dW||^2 (fraction of injected-noise energy along the loss
gradient -- a direct gauge-coupling-to-loss probe; the gauge claim predicts
wavelet/band > flat here) and the controller's kappa_tail for context.

Everything is reported as-is, single seed unless --seeds given. Non-destructive:
imports the validated Phase-6.1 components, never modifies them.

Run:
    python wavelet_gauge_matched_ab.py
    python wavelet_gauge_matched_ab.py --modes wavelet matched_svd_flat --max_epochs 2500
    python wavelet_gauge_matched_ab.py --seeds 42 43 44
"""

import argparse
import csv
import math
import os
import sys
import time
from pathlib import Path

import numpy as np
import torch
import torch.nn as nn
from torch.utils.data import DataLoader

# Import the validated Phase-6.1 components directly (non-destructive reuse).
_DEMOS = Path(__file__).resolve().parent
if str(_DEMOS) not in sys.path:
    sys.path.insert(0, str(_DEMOS))
from sgc_grokking_phase6_1 import (  # noqa: E402
    GrokMLP,
    ModularAdditionDataset,
    CorrectedWaveletController,
    analyze_layer_spectrum,
    hermite_gaussian_weight,
)

ALL_MODES = [
    "wavelet",
    "matched_svd_flat",
    "matched_band",
    "matched_weight_scaled",
    "isotropic",
]


def _flat_unit(n_sv: int) -> np.ndarray:
    w = np.ones(n_sv, dtype=np.float64)
    return w / np.sqrt((w ** 2).sum())


def _band_unit(n_sv: int, lo: float, hi: float) -> np.ndarray:
    u = np.linspace(0.0, 1.0, n_sv)
    w = ((u >= lo) & (u <= hi)).astype(np.float64)
    if w.sum() < 1e-9:
        w = np.ones(n_sv, dtype=np.float64)
    return w / np.sqrt((w ** 2).sum())


def inject_matched(model: GrokMLP, noise_scale: float, mode: str, device: str,
                   wavelet_a: float = 1.0, wavelet_b: float = 2.0,
                   band=(0.25, 0.75)):
    """
    Inject weight noise with the chosen 2-D matrix envelope at MATCHED Frobenius
    norm (except `isotropic`, the deliberately UNMATCHED reference).

    1-D params (biases) always get randn*noise_scale -> identical across arms.

    Returns (kappa_tail, kappa_grad) averaged over the 2-D layers:
        kappa_tail = ||C[tail-half]||^2 / ||C||^2,  C = U^T dW V  (controller's proxy)
        kappa_grad = <dW, ghat>^2 / ||dW||^2        (coupling to the loss gradient)
    """
    tot_tail, tot_grad, n_layers = 0.0, 0.0, 0
    with torch.no_grad():
        for _name, p in model.named_parameters():
            if p.dim() != 2:
                p.add_(torch.randn_like(p) * noise_scale)
                continue

            # Pre-injection SVD basis (used for SVD injection AND kappa_tail probe).
            try:
                U, S, Vh = torch.linalg.svd(p.data, full_matrices=False)
            except Exception:
                p.add_(torch.randn_like(p) * noise_scale)
                continue
            n_sv = len(S)
            if n_sv < 2:
                p.add_(torch.randn_like(p) * noise_scale)
                continue

            if mode == "isotropic":
                # UNMATCHED reference: ||dW||_F ~ noise_scale * sqrt(numel).
                dW = torch.randn_like(p) * noise_scale
            elif mode == "matched_weight_scaled":
                # Matched Frobenius, weight space: scale so ||dW||_F ~ noise_scale.
                dW = torch.randn_like(p) * (noise_scale / math.sqrt(p.numel()))
            else:
                if mode == "wavelet":
                    w = hermite_gaussian_weight(np.linspace(0, 1, n_sv),
                                                wavelet_a, wavelet_b)
                elif mode == "matched_svd_flat":
                    w = _flat_unit(n_sv)
                elif mode == "matched_band":
                    w = _band_unit(n_sv, band[0], band[1])
                else:
                    raise ValueError(f"unknown mode {mode}")
                w_t = torch.from_numpy(w).float().to(device)
                Z = torch.randn(n_sv, device=device) * w_t * noise_scale
                dW = (U * Z.unsqueeze(0)) @ Vh  # ||dW||_F = ||Z|| ~ noise_scale

            # Gauge coupling to the loss gradient (uses last training-batch grad).
            if p.grad is not None:
                g = p.grad.data
                gn = g.norm()
                if gn > 1e-12:
                    proj = (dW * (g / gn)).sum()
                    e = dW.pow(2).sum() + 1e-12
                    tot_grad += float((proj * proj / e).item())

            p.add_(dW)

            # kappa_tail in the pre-injection SVD basis: C = U^T dW V (V = Vh^T).
            C = U.t() @ dW @ Vh.t()
            tail = int(n_sv * 0.5)
            e_tot = float((C ** 2).sum().item()) + 1e-12
            e_tail = float((C[tail:, :] ** 2).sum().item())
            tot_tail += e_tail / e_tot
            n_layers += 1

    if n_layers == 0:
        return 0.5, 0.0
    return tot_tail / n_layers, tot_grad / n_layers


def evaluate(model: GrokMLP, loader: DataLoader, device: str) -> float:
    model.eval()
    correct, total = 0, 0
    with torch.no_grad():
        for x, y in loader:
            x, y = x.to(device), y.to(device)
            out = model(x)
            correct += (out.argmax(dim=1) == y).sum().item()
            total += x.size(0)
    return correct / max(1, total)


def run_arm(mode: str, p: int, hidden_dim: int, max_epochs: int, batch_size: int,
            lr: float, weight_decay: float, noise_scale: float,
            tomography_interval: int, seed: int, grok_lo: float, grok_hi: float,
            post_grok_epochs: int, out_dir: Path) -> dict:
    torch.manual_seed(seed)
    np.random.seed(seed)
    device = "cuda" if torch.cuda.is_available() else "cpu"

    print("=" * 92)
    print(f"ARM: {mode.upper():22s}  (seed {seed}, add mod {p}, 70/30 split, "
          f"heat WD=0.1, noise_scale={noise_scale}, device={device})")
    print("=" * 92)

    train_ds = ModularAdditionDataset(p, train=True, seed=seed)
    test_ds = ModularAdditionDataset(p, train=False, seed=seed)
    train_loader = DataLoader(train_ds, batch_size=batch_size, shuffle=True)
    test_loader = DataLoader(test_ds, batch_size=256)

    model = GrokMLP(p, hidden_dim).to(device)
    criterion = nn.CrossEntropyLoss()
    optimizer = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=weight_decay)

    # The real Phase-6.1 controller drives WD/phase/trigger. We inject ourselves
    # (inject_matched) and feed the controller the same bookkeeping inject_noise
    # would, so the heat/anneal/quench logic is byte-for-byte the original's.
    controller = CorrectedWaveletController(
        delta=0.1, initial_distance=1.0, wd_heat=0.1, wd_quench=2.0,
        wd_baseline=weight_decay, noise_scale=noise_scale, noise_mode="wavelet",
        trigger_mode="effective_contract", train_size=len(train_ds),
        batch_size=batch_size, lr=lr,
    )

    out_dir.mkdir(parents=True, exist_ok=True)
    csv_path = out_dir / f"matched_{mode}_seed{seed}.csv"
    cf = open(csv_path, "w", newline="")
    cw = csv.DictWriter(cf, fieldnames=[
        "epoch", "train_acc", "test_acc", "epsilon", "hidden_eff_rank",
        "kappa_tail", "kappa_grad", "M_eff_contract", "phase", "weight_decay",
    ])
    cw.writeheader()

    grok90, grok95 = -1, -1
    last_kt, last_kg = 0.5, 0.0
    t0 = time.time()

    for epoch in range(1, max_epochs + 1):
        model.train()
        train_correct, train_total = 0, 0
        for x, y in train_loader:
            x, y = x.to(device), y.to(device)
            optimizer.zero_grad()
            out = model(x)
            loss = criterion(out, y)
            loss.backward()
            optimizer.step()
            train_correct += (out.argmax(dim=1) == y).sum().item()
            train_total += x.size(0)
        train_acc = train_correct / max(1, train_total)

        # Per-epoch injection during heat/anneal (the single experimental variable).
        if controller.current_phase in ("heat", "anneal"):
            if controller.current_phase == "anneal":
                scale = controller._get_anneal_noise_scale(epoch)
            else:
                scale = controller.noise_scale
            last_kt, last_kg = inject_matched(model, scale, mode, device)
            # Replicate CorrectedWaveletController.inject_noise bookkeeping exactly.
            controller.injection_count += 1
            controller.kappa_tail = last_kt
            controller.M_nominal += scale
            controller.M_effective_tail += last_kt * scale
            controller.eta_mass_since_tomo += scale
            controller.kappa_tail_history.append(last_kt)

        test_acc = evaluate(model, test_loader, device)

        if epoch % tomography_interval == 0 or epoch == 1:
            spec = analyze_layer_spectrum("hidden_1", model.hidden_layer.weight.data)
            if controller.current_phase in ("heat", "anneal"):
                controller.update_kappa_contract(spec.defect.epsilon)
            new_wd, phase = controller.update(epoch, spec.defect.epsilon,
                                              spec.effective_rank)
            for pg in optimizer.param_groups:
                pg["weight_decay"] = new_wd
            cw.writerow({
                "epoch": epoch, "train_acc": round(train_acc, 6),
                "test_acc": round(test_acc, 6),
                "epsilon": round(spec.defect.epsilon, 6),
                "hidden_eff_rank": round(spec.effective_rank, 4),
                "kappa_tail": round(last_kt, 6), "kappa_grad": round(last_kg, 8),
                "M_eff_contract": round(controller.M_effective_contract, 6),
                "phase": phase, "weight_decay": round(new_wd, 4),
            })
            cf.flush()
            print(f"  ep {epoch:5d} | train {train_acc*100:5.1f}% | "
                  f"test {test_acc*100:5.1f}% | eps {spec.defect.epsilon:.4f} | "
                  f"effrank {spec.effective_rank:5.1f} | k_grad {last_kg:.5f} | "
                  f"{phase}")

        if grok90 < 0 and test_acc >= grok_lo:
            grok90 = epoch
        if grok95 < 0 and test_acc >= grok_hi:
            grok95 = epoch
            controller.signal_grokking(epoch, test_acc)
            print(f"  *** {mode}: grok@{int(grok_hi*100)}% at epoch {epoch} "
                  f"({time.time()-t0:.1f}s) ***")
        # Efficiency: once grokked, confirm briefly then stop.
        if grok95 > 0 and epoch >= grok95 + post_grok_epochs:
            break

    cf.close()
    elapsed = time.time() - t0
    print(f"{mode}: grok90={grok90 if grok90>0 else 'NONE':>6} "
          f"grok95={grok95 if grok95>0 else 'NONE':>6} "
          f"kappa_grad~{last_kg:.5f} | {elapsed:.1f}s -> {csv_path}")
    return {"mode": mode, "seed": seed, "grok90": grok90, "grok95": grok95,
            "kappa_grad": last_kg, "elapsed": elapsed}


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--modes", nargs="+", default=ALL_MODES, choices=ALL_MODES)
    ap.add_argument("--seeds", nargs="+", type=int, default=[42])
    ap.add_argument("--p", type=int, default=97)
    ap.add_argument("--hidden_dim", type=int, default=128)
    ap.add_argument("--max_epochs", type=int, default=3000)
    ap.add_argument("--batch_size", type=int, default=32)
    ap.add_argument("--lr", type=float, default=1e-3)
    ap.add_argument("--weight_decay", type=float, default=1.0)
    ap.add_argument("--noise_scale", type=float, default=0.1)
    ap.add_argument("--tomography_interval", type=int, default=50)
    ap.add_argument("--grok_lo", type=float, default=0.90)
    ap.add_argument("--grok_hi", type=float, default=0.95)
    ap.add_argument("--post_grok_epochs", type=int, default=200)
    ap.add_argument("--out_dir", type=str,
                    default=str(_DEMOS / "logs" / "matched_ab"))
    args = ap.parse_args()

    out_dir = Path(args.out_dir)
    print("#" * 92)
    print("WAVELET GAUGE-COUPLING — AMPLITUDE-MATCHED A/B")
    print(f"  modes: {args.modes}")
    print(f"  seeds: {args.seeds}   max_epochs: {args.max_epochs}   "
          f"out: {out_dir}")
    print("#" * 92)

    results = []
    # Persist EXACT per-epoch grok results as each arm finishes (append-mode, so a
    # killed run keeps every completed arm). This is the ground truth for
    # aggregate_matched.py -- the per-arm CSVs only log every tomography_interval
    # and stop post_grok_epochs after grok, so their 50-ep grid can miss the
    # threshold crossing entirely.
    out_dir.mkdir(parents=True, exist_ok=True)
    results_path = out_dir / "grok_results.csv"
    _new = not results_path.exists()
    rf = open(results_path, "a", newline="")
    rw = csv.writer(rf)
    if _new:
        rw.writerow(["mode", "seed", "grok90", "grok95", "kappa_grad", "elapsed"])
        rf.flush()
    for seed in args.seeds:
        for mode in args.modes:
            r = run_arm(
                mode=mode, p=args.p, hidden_dim=args.hidden_dim,
                max_epochs=args.max_epochs, batch_size=args.batch_size,
                lr=args.lr, weight_decay=args.weight_decay,
                noise_scale=args.noise_scale,
                tomography_interval=args.tomography_interval, seed=seed,
                grok_lo=args.grok_lo, grok_hi=args.grok_hi,
                post_grok_epochs=args.post_grok_epochs, out_dir=out_dir)
            results.append(r)
            rw.writerow([r["mode"], r["seed"], r["grok90"], r["grok95"],
                         round(r["kappa_grad"], 8), round(r["elapsed"], 1)])
            rf.flush()
    rf.close()

    print("\n" + "#" * 92)
    print("SUMMARY  (grok epoch; lower = faster; NONE = never reached threshold)")
    print("#" * 92)
    print(f"{'mode':22s} | {'seed':>4} | {'grok@90%':>9} | {'grok@95%':>9} | "
          f"{'kappa_grad':>10}")
    print("-" * 92)
    for r in results:
        print(f"{r['mode']:22s} | {r['seed']:>4} | "
              f"{(r['grok90'] if r['grok90']>0 else '—'):>9} | "
              f"{(r['grok95'] if r['grok95']>0 else '—'):>9} | "
              f"{r['kappa_grad']:>10.5f}")

    # Headline deltas (averaged over seeds where both arms grokked).
    def avg_grok(mode):
        vals = [r["grok95"] for r in results
                if r["mode"] == mode and r["grok95"] > 0]
        return sum(vals) / len(vals) if vals else None

    wav = avg_grok("wavelet")
    flat = avg_grok("matched_svd_flat")
    band = avg_grok("matched_band")
    iso = avg_grok("isotropic")
    print("-" * 92)
    if wav and flat:
        print(f"  GAUGE-COUPLING (matched amplitude): matched_svd_flat {flat:.0f} "
              f"-> wavelet {wav:.0f}  = {flat/wav:.2f}x")
    if wav and band:
        print(f"  BAND vs HERMITE (matched amplitude): matched_band {band:.0f} "
              f"vs wavelet {wav:.0f}  = {band/wav:.2f}x")
    if wav and iso:
        print(f"  SELF-NORMALISATION (vs naive blast): isotropic {iso:.0f} "
              f"-> wavelet {wav:.0f}  = {iso/wav:.2f}x")
    elif iso is None:
        print("  SELF-NORMALISATION: isotropic NEVER grokked (the ~128x blast) "
              "-> wavelet wins by infinity (practical win).")
    print("#" * 92)


if __name__ == "__main__":
    main()
