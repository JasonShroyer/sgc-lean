#!/usr/bin/env python3
"""transformer_modular_grokking.py -- Leg 2 (decisions/0010): DRIVE THE WEDGE.

The MLP folds the cyclic structure flat (b1=0 at EVERY layer).  But the mechanistic-
interpretability literature reports that a TRANSFORMER trained on a+b mod p arranges its
token embeddings on a CIRCLE (Nanda et al. 2023, the "clock").  If that survives our
calibrated reader it means "feedforward -> b1=0" is MLP-specific, not feedforward-generic --
the architecture decides WHERE (if anywhere) topology is allowed to live.

PRE-REGISTERED predictions (locked in decisions/0010 before this run; reader pre-calibrated):
  P1  token embedding W_E[0..p-1] reads b1>=1 (the clock); likely Rips over-counts the
      multi-key-frequency lobes (b1 in {2,3,4}) but the circular-coordinate deconvolution
      shows a single dominant S^1 carrier (winding +/- k*), exactly as the recurrent ring did.
  P2  => "feedforward -> b1=0" is MLP-specific: the transformer parks the circle in the
      EMBEDDING where our MLP had b1=0 everywhere.
  P3  residual @ '=' (the computation that emits the answer): if b1>=1, topology lives in the
      computation; if b1=0, the circle is only the input ENCODING (folded once a,b combine).
FALSIFIERS: embedding reads b1=0 (clock does not survive our reader -> investigate pipeline);
  residual reads robust b1>=1 (would EXTEND the law into the computation).

Same task family (a+b mod 97), same hidden width (d_model=128 == the reader's R^128 calibration
ambient), IDENTICAL calibrated barcode reader + circular-coordinate tool as every other 0010 cloud.
"""
import argparse
import os
import sys

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)
sys.path.insert(0, os.path.join(_HERE, "..", "demos"))


def build_and_train(p=97, frac=0.4, d_model=128, n_heads=4, d_mlp=512,
                    lr=1e-3, wd=1.0, max_steps=30000, eval_every=200,
                    post_grok=1500, seed=42, device="cuda"):
    import torch
    import torch.nn as nn
    from analog_modular_arithmetic import EmbeddingModularDataset

    torch.manual_seed(seed)
    np.random.seed(seed)
    vocab, n_ctx, eq = p + 1, 3, p          # token p == '='

    class Transformer(nn.Module):
        def __init__(self):
            super().__init__()
            self.W_E = nn.Embedding(vocab, d_model)
            self.W_pos = nn.Embedding(n_ctx, d_model)
            self.attn = nn.MultiheadAttention(d_model, n_heads, batch_first=True)
            self.fc1 = nn.Linear(d_model, d_mlp)
            self.act = nn.GELU()
            self.fc2 = nn.Linear(d_mlp, d_model)
            self.W_U = nn.Linear(d_model, p, bias=False)
            self._resid = None
            self._neur = None

        def forward(self, x):
            pos = torch.arange(x.shape[1], device=x.device)
            h = self.W_E(x) + self.W_pos(pos)[None]
            h = h + self.attn(h, h, h, need_weights=False)[0]
            n = self.act(self.fc1(h))
            h = h + self.fc2(n)
            self._resid = h[:, -1]                       # residual @ '=' (B, d_model)
            self._neur = n[:, -1]                        # MLP neurons @ '=' (B, d_mlp)
            return self.W_U(h[:, -1])

    model = Transformer().to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=wd, betas=(0.9, 0.98))
    crit = nn.CrossEntropyLoss()

    def pairs_to_tensors(ds):
        a = torch.tensor([pr[0] for pr in ds.pairs], device=device)
        b = torch.tensor([pr[1] for pr in ds.pairs], device=device)
        y = torch.tensor(ds.targets, device=device)
        x = torch.stack([a, b, torch.full_like(a, eq)], dim=1)   # (N, 3)
        return x, y

    tr = EmbeddingModularDataset(p, "add", frac, "train", seed)
    te = EmbeddingModularDataset(p, "add", frac, "test", seed)
    x_tr, y_tr = pairs_to_tensors(tr)
    x_te, y_te = pairs_to_tensors(te)

    @torch.no_grad()
    def acc(x, y):
        model.eval()
        return (model(x).argmax(-1) == y).float().mean().item()

    print(f"[TRAIN transformer] p={p} d_model={d_model} heads={n_heads} d_mlp={d_mlp} "
          f"wd={wd} frac={frac} seed={seed} (full-batch, N_tr={len(y_tr)})", flush=True)
    print(f"{'step':>6} {'loss':>8} {'train':>6} {'test':>6}  event", flush=True)
    grok = -1
    for step in range(1, max_steps + 1):
        model.train()
        opt.zero_grad()
        crit(model(x_tr), y_tr).backward()
        opt.step()
        if step % eval_every == 0 or step == 1:
            tra, tea = acc(x_tr, y_tr), acc(x_te, y_te)
            tag = ""
            if grok < 0 and tea > 0.95:
                grok = step
                tag = "<- GROK"
            print(f"{step:>6} {crit(model(x_tr), y_tr).item():>8.4f} {tra:>6.3f} {tea:>6.3f}  {tag}",
                  flush=True)
            if grok > 0 and step >= grok + post_grok:
                break

    # ---- capture clouds (full grid) ----
    allp = np.array([(a, b) for a in range(p) for b in range(p)])
    xa = torch.tensor(allp[:, 0], device=device)
    xb = torch.tensor(allp[:, 1], device=device)
    xg = torch.stack([xa, xb, torch.full_like(xa, eq)], dim=1)
    model.eval()
    with torch.no_grad():
        _ = model(xg)
        resid = model._resid.cpu().numpy()              # (p^2, d_model)
        neur = model._neur.cpu().numpy()                # (p^2, d_mlp)
        W_E = model.W_E.weight.detach().cpu().numpy()[:p]   # (p, d_model) number tokens
    sums = (allp[:, 0] + allp[:, 1]) % p
    resid_cm = np.stack([resid[sums == s].mean(0) for s in range(p)])   # (p, d_model)
    neur_cm = np.stack([neur[sums == s].mean(0) for s in range(p)])     # (p, d_mlp)
    return dict(embed=W_E, resid_full=resid, resid_classmean=resid_cm,
                neur_classmean=neur_cm, grok_step=grok,
                test_acc=acc(x_te, y_te))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=42)
    ap.add_argument("--p", type=int, default=97)
    ap.add_argument("--frac", type=float, default=0.4)
    ap.add_argument("--wd", type=float, default=1.0)
    ap.add_argument("--lr", type=float, default=1e-3)
    ap.add_argument("--max-steps", type=int, default=30000)
    args = ap.parse_args()

    import torch
    device = "cuda" if torch.cuda.is_available() else "cpu"

    from persistent_homology_grokking import run_calibration, read_layer, N_H1
    from fft_classmeans_grokking import spectrum, show
    from circular_coordinate_probe import analyze_cloud

    print("=" * 78)
    print("DRIVE THE WEDGE  --  transformer on a+b mod p  (does the clock survive our reader?)")
    print("=" * 78, flush=True)
    snap = build_and_train(p=args.p, frac=args.frac, wd=args.wd, lr=args.lr,
                           max_steps=args.max_steps, seed=args.seed, device=device)
    outdir = os.path.join(_HERE, "logs", "ph_grok", f"transformer_seed{args.seed}")
    os.makedirs(outdir, exist_ok=True)
    for k in ("embed", "resid_classmean", "neur_classmean"):
        np.save(os.path.join(outdir, f"{k}.npy"), snap[k])
    print(f"  grok@{snap['grok_step']}  final test acc={snap['test_acc']:.4f}  "
          f"[saved -> {outdir}]", flush=True)

    print("\n" + "=" * 78)
    print("FUNCTIONAL FFT  --  transformer embedding & residual")
    print("=" * 78, flush=True)
    show("token embedding W_E[s]", spectrum(snap["embed"]))
    show("residual @ '=' [s]", spectrum(snap["resid_classmean"]))

    gate_ok, tau1, tau2 = run_calibration()
    if not gate_ok:
        print("\n  reader NOT calibrated; abort.")
        sys.exit(1)

    print(f"\n{'='*78}\n  TRANSFORMER BARCODE READOUT  seed={args.seed}  (tau1*={tau1:.3f})\n{'='*78}",
          flush=True)
    print("  -- prior P1: token EMBEDDING is the 'clock' -> b1>=1 (vs MLP embed_a b1=0)", flush=True)
    read_layer("token embedding", snap["embed"], tau1, tau2, "CLOCK b1>=1")
    print("  -- prior P3: residual @ '=' (the computation) -> b1>=1 (topology) or b1=0 (folded)", flush=True)
    read_layer("residual @ '='", snap["resid_classmean"], tau1, tau2, "? b1")
    read_layer("residual full", snap["resid_full"], tau1, tau2, "? b1 + scatter", n_sub=N_H1)

    print(f"\n{'='*78}\n  CIRCULAR-COORDINATE DECONVOLUTION (single S^1 carrier?)\n{'='*78}", flush=True)
    analyze_cloud("token embedding", snap["embed"], tau1)
    analyze_cloud("residual @ '='", snap["resid_classmean"], tau1)
    print("=" * 78, flush=True)


if __name__ == "__main__":
    main()
