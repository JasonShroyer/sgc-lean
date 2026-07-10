#!/usr/bin/env python3
"""
SVD-Frame Gauge Probe — does SVD-space noise really preserve the singular frame?
===============================================================================

WHY THIS EXISTS
---------------
The amplitude-matched A/B (wavelet_gauge_matched_ab.py) showed, at MATCHED
Frobenius norm:
    * spectral envelope (Hermite vs flat vs band)  -> NULL effect  (grok ~1534)
    * SVD-diagonal injection vs full weight-space   -> ~1.2x faster (1534 vs 1819)

Artemis's proposed MECHANISM for that ~1.2x ("the gauge win") is exact algebra:

    W  = U S V^T                          (the layer's current SVD)
    dW = U diag(Z) V^T                    (SVD-DIAGONAL injection)
    => W + dW = U (S + diag(Z)) V^T       <-- SAME U, V. Only singular VALUES move.

So SVD-diagonal noise is GAUGE-PRESERVING (zero rotation of the singular vectors)
by construction, whereas a full random matrix (weight-space noise) has OFF-DIAGONAL
components in the SVD basis (C = U^T dW V) that rotate the singular vectors -- most
violently where singular-value gaps are smallest (the near-degenerate tail).

This script does not assert that -- it MEASURES it. For a realistic, memorised
GrokMLP weight matrix it injects each noise type at matched amplitude and reports:

    ||dW||_F              total perturbation energy (sanity: matched ~ noise_scale,
                          naive isotropic ~ noise_scale*sqrt(numel)).
    offdiag_frac          (||C||^2 - ||diag C||^2) / ||C||^2, C = U^T dW V.
                          0  => purely diagonal (gauge-preserving by construction).
                          ~1 => energy lives off-diagonal (rotates the frame).
    rot_head / rot_tail   principal angle (deg) between the top-k (head) and
                          bottom-k (tail) left-singular subspaces BEFORE vs AFTER
                          injection. Artemis predicts ~0 for SVD-diagonal arms,
                          and tail >> head for weight-space arms.

Non-destructive: imports the validated Phase-6.1 components, never modifies them,
and perturbs COPIES of the weights (the trained model is left untouched).

Run:
    python svd_gauge_probe.py
    python svd_gauge_probe.py --memorize_epochs 300 --n_draws 16 --subspace_k 32
"""

import argparse
import csv
import math
import sys
from pathlib import Path

import numpy as np
import torch
import torch.nn as nn
from torch.utils.data import DataLoader

_DEMOS = Path(__file__).resolve().parent
if str(_DEMOS) not in sys.path:
    sys.path.insert(0, str(_DEMOS))
from sgc_grokking_phase6_1 import (  # noqa: E402
    GrokMLP,
    ModularAdditionDataset,
    hermite_gaussian_weight,
)

MODES = ["wavelet", "matched_svd_flat", "matched_band",
         "matched_weight_scaled", "isotropic"]


def _flat_unit(n_sv: int) -> np.ndarray:
    w = np.ones(n_sv, dtype=np.float64)
    return w / np.sqrt((w ** 2).sum())


def _band_unit(n_sv: int, lo: float, hi: float) -> np.ndarray:
    u = np.linspace(0.0, 1.0, n_sv)
    w = ((u >= lo) & (u <= hi)).astype(np.float64)
    if w.sum() < 1e-9:
        w = np.ones(n_sv, dtype=np.float64)
    return w / np.sqrt((w ** 2).sum())


def make_delta(W: torch.Tensor, U: torch.Tensor, S: torch.Tensor, Vh: torch.Tensor,
               mode: str, noise_scale: float, device: str,
               wavelet_a: float = 1.0, wavelet_b: float = 2.0,
               band=(0.25, 0.75)) -> torch.Tensor:
    """Build dW for `mode` at matched Frobenius (except `isotropic`). Identical
    rule to wavelet_gauge_matched_ab.inject_matched, but returns dW (no in-place)."""
    n_sv = len(S)
    if mode == "isotropic":
        return torch.randn_like(W) * noise_scale
    if mode == "matched_weight_scaled":
        return torch.randn_like(W) * (noise_scale / math.sqrt(W.numel()))
    if mode == "wavelet":
        w = hermite_gaussian_weight(np.linspace(0, 1, n_sv), wavelet_a, wavelet_b)
    elif mode == "matched_svd_flat":
        w = _flat_unit(n_sv)
    elif mode == "matched_band":
        w = _band_unit(n_sv, band[0], band[1])
    else:
        raise ValueError(mode)
    w_t = torch.from_numpy(w).float().to(device)
    Z = torch.randn(n_sv, device=device) * w_t * noise_scale
    return (U * Z.unsqueeze(0)) @ Vh  # ||dW||_F = ||Z|| ~ noise_scale


def subspace_angle_deg(A: torch.Tensor, B: torch.Tensor) -> float:
    """Largest principal angle (deg) between the column spaces of A and B.
    A, B have orthonormal columns (singular-vector subsets). cos(theta_i) are the
    singular values of A^T B; the largest angle = the worst-aligned direction."""
    M = A.t() @ B
    s = torch.linalg.svdvals(M).clamp(-1.0, 1.0)
    cos_min = float(s.min().item())
    return math.degrees(math.acos(max(-1.0, min(1.0, cos_min))))


def probe_layer(W: torch.Tensor, mode: str, noise_scale: float, n_draws: int,
                k: int, device: str) -> dict:
    """Average gauge diagnostics over n_draws random injections of `mode`."""
    U, S, Vh = torch.linalg.svd(W, full_matrices=False)
    V = Vh.t()
    n_sv = len(S)
    k = min(k, n_sv // 2)
    head_idx = slice(0, k)             # top-k singular directions (largest sigma)
    tail_idx = slice(n_sv - k, n_sv)   # bottom-k (smallest sigma, near-degenerate)

    fro, offd, rh, rt = [], [], [], []
    for _ in range(n_draws):
        dW = make_delta(W, U, S, Vh, mode, noise_scale, device)
        fro.append(float(dW.norm().item()))

        C = U.t() @ dW @ V                              # noise in the SVD basis
        e_tot = float((C ** 2).sum().item()) + 1e-12
        e_diag = float((torch.diagonal(C) ** 2).sum().item())
        offd.append((e_tot - e_diag) / e_tot)

        Up, _Sp, _Vhp = torch.linalg.svd(W + dW, full_matrices=False)
        rh.append(subspace_angle_deg(U[:, head_idx], Up[:, head_idx]))
        rt.append(subspace_angle_deg(U[:, tail_idx], Up[:, tail_idx]))

    return {
        "fro": float(np.mean(fro)),
        "offdiag_frac": float(np.mean(offd)),
        "rot_head_deg": float(np.mean(rh)),
        "rot_tail_deg": float(np.mean(rt)),
    }


def memorize_model(p: int, hidden_dim: int, epochs: int, lr: float, wd: float,
                   batch_size: int, seed: int, device: str) -> GrokMLP:
    """Train a GrokMLP to the memorised (pre-grok) state -- the regime in which the
    experiment injects noise -- so the probed matrix has a realistic spectrum."""
    torch.manual_seed(seed)
    np.random.seed(seed)
    ds = ModularAdditionDataset(p, train=True, seed=seed)
    loader = DataLoader(ds, batch_size=batch_size, shuffle=True)
    model = GrokMLP(p, hidden_dim).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=wd)
    crit = nn.CrossEntropyLoss()
    for ep in range(1, epochs + 1):
        model.train()
        correct = total = 0
        for x, y in loader:
            x, y = x.to(device), y.to(device)
            opt.zero_grad()
            out = model(x)
            loss = crit(out, y)
            loss.backward()
            opt.step()
            correct += (out.argmax(1) == y).sum().item()
            total += x.size(0)
    print(f"  memorised GrokMLP @ epoch {epochs}: train_acc={correct/max(1,total)*100:.1f}%")
    return model


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--p", type=int, default=97)
    ap.add_argument("--hidden_dim", type=int, default=128)
    ap.add_argument("--memorize_epochs", type=int, default=300)
    ap.add_argument("--lr", type=float, default=1e-3)
    ap.add_argument("--wd", type=float, default=0.1)        # heat regime
    ap.add_argument("--batch_size", type=int, default=32)
    ap.add_argument("--noise_scale", type=float, default=0.1)
    ap.add_argument("--n_draws", type=int, default=16)
    ap.add_argument("--subspace_k", type=int, default=32)
    ap.add_argument("--seed", type=int, default=42)
    ap.add_argument("--out_dir", type=str, default=str(_DEMOS / "logs" / "matched_ab"))
    args = ap.parse_args()

    device = "cuda" if torch.cuda.is_available() else "cpu"
    print("#" * 92)
    print("SVD-FRAME GAUGE PROBE  (does SVD-diagonal noise preserve the frame?)")
    print(f"  noise_scale={args.noise_scale}  n_draws={args.n_draws}  "
          f"subspace_k={args.subspace_k}  device={device}")
    print("#" * 92)

    model = memorize_model(args.p, args.hidden_dim, args.memorize_epochs, args.lr,
                           args.wd, args.batch_size, args.seed, device)

    # Probe every 2-D weight matrix (the objects the experiment actually perturbs).
    layers = [(n, p.data.clone()) for n, p in model.named_parameters() if p.dim() == 2]

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    csv_path = out_dir / "svd_gauge_probe.csv"
    cf = open(csv_path, "w", newline="")
    cw = csv.DictWriter(cf, fieldnames=["layer", "shape", "mode", "fro",
                                        "offdiag_frac", "rot_head_deg", "rot_tail_deg"])
    cw.writeheader()

    for lname, W in layers:
        W = W.to(device)
        print(f"\nLAYER {lname}  shape={tuple(W.shape)}  ||W||_F={W.norm().item():.3f}")
        print(f"  {'mode':22s} | {'||dW||_F':>9} | {'offdiag':>8} | "
              f"{'rot_head':>9} | {'rot_tail':>9}")
        print("  " + "-" * 70)
        for mode in MODES:
            r = probe_layer(W, mode, args.noise_scale, args.n_draws,
                            args.subspace_k, device)
            print(f"  {mode:22s} | {r['fro']:9.4f} | {r['offdiag_frac']:8.4f} | "
                  f"{r['rot_head_deg']:8.3f}d | {r['rot_tail_deg']:8.3f}d")
            cw.writerow({"layer": lname, "shape": str(tuple(W.shape)), "mode": mode,
                         "fro": round(r["fro"], 6),
                         "offdiag_frac": round(r["offdiag_frac"], 6),
                         "rot_head_deg": round(r["rot_head_deg"], 6),
                         "rot_tail_deg": round(r["rot_tail_deg"], 6)})
        cf.flush()
    cf.close()

    print("\n" + "#" * 92)
    print("EXPECTATION (Artemis's gauge mechanism):")
    print("  SVD arms (wavelet/flat/band): offdiag~0, rot_head~rot_tail~0  -> GAUGE-PRESERVING")
    print("  matched_weight_scaled:        offdiag~1, rot_tail >> rot_head  -> rotates the frame")
    print("  isotropic:                    ||dW||_F ~128x, rot ~ 90deg      -> frame scrambled")
    print(f"  -> {csv_path}")
    print("#" * 92)


if __name__ == "__main__":
    main()
