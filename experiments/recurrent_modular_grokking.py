#!/usr/bin/env python3
"""
recurrent_modular_grokking.py -- the REMEMBER-vs-COMPUTE test (decisions/0010 follow-on).

Path B'' proved the FEEDFORWARD modular-addition MLP is a Fourier-FOLDED RIBBON:
functionally ~4 Fourier frequencies (99.2% power, k in {8,15,25,26}) but topologically
TRIVIAL (b1=0) -- the periodic code is folded flat into a contractible blob.

Pre-registered prediction (stated before running; reader gates are pre-calibrated, so the
b1 readout cannot be fudged post-hoc):

    A network that must REMEMBER the cyclic state over time -- rather than COMPUTE it in one
    feedforward pass -- is forced to carry the topology of the stimulus.  A recurrent solver
    of modular PATH INTEGRATION (track s_t = (s_{t-1} + v_t) mod p from velocities v in
    {-1,0,+1}) must build a continuous RING attractor over Z_p, so its hidden manifold should
    read b1 = 1 (one dominant Fourier mode, k=1), where the feedforward MLP read b1 = 0.

This is the toy analogue of head-direction ring attractors (Kim et al., Science 2017) and of
grid cells emerging in path-integrating RNNs (Cueva & Wei 2018; Banino et al. 2018).

CONTROL DISCIPLINE: identical hidden_dim=128 and identical wd=0.5 as the feedforward MLP, and
the recurrent H[s] cloud is read by the SAME calibrated Vietoris-Rips reader (same tau1*/tau2*)
that gave the feedforward b1=0.  Only the architecture (recurrent vs feedforward) differs.
If b1=0, that REFUTES the prediction and is reported as such.
"""
import argparse
import os
import sys

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

from persistent_homology_grokking import run_calibration, read_layer, N_H1  # noqa: E402
from fft_classmeans_grokking import spectrum, show                          # noqa: E402

import torch                                                                # noqa: E402
import torch.nn as nn                                                       # noqa: E402


class RecurrentModularSolver(nn.Module):
    """GRU that path-integrates velocities v in {-1,0,+1} into s_t = (sum v) mod p."""

    def __init__(self, p, n_actions=3, emb_dim=32, hidden_dim=128):
        super().__init__()
        self.p = p
        self.hidden_dim = hidden_dim
        self.act_emb = nn.Embedding(n_actions, emb_dim)
        self.cell = nn.GRUCell(emb_dim, hidden_dim)
        self.readout = nn.Linear(hidden_dim, p)
        self.h0 = nn.Parameter(torch.zeros(hidden_dim))

    def forward(self, actions, noise=0.0, return_hidden=False):
        B, L = actions.shape
        h = self.h0.unsqueeze(0).expand(B, -1).contiguous()
        logits, hs = [], []
        for t in range(L):
            h = self.cell(self.act_emb(actions[:, t]), h)
            if noise > 0:
                h = h + noise * torch.randn_like(h)
            logits.append(self.readout(h))
            if return_hidden:
                hs.append(h)
        logits = torch.stack(logits, 1)
        return (logits, torch.stack(hs, 1)) if return_hidden else logits


def gen_batch(B, L, p, rng, device):
    """Uniform-random start s0 (absolute-set token at t=0) + {-1,0,+1} velocity walk.
    Random start guarantees UNIFORM coverage of all p ring states: a pure +-1 walk from a
    fixed origin diffuses too slowly (std ~ sqrt(2L/3)) to visit far states, leaving H[s]
    rows empty.  Tokens 0..p-1 = 'set heading to value'; tokens p..p+2 = velocity -1,0,+1."""
    s0 = rng.integers(0, p, size=(B, 1))
    v = rng.integers(-1, 2, size=(B, L - 1))
    s = np.concatenate([s0, (s0 + np.cumsum(v, axis=1)) % p], axis=1)
    actions = np.concatenate([s0, (v + 1) + p], axis=1)
    return (torch.tensor(actions, dtype=torch.long, device=device),
            torch.tensor(s, dtype=torch.long, device=device))


def train(p=97, hidden_dim=128, wd=0.5, lr=1e-3, L=64, batch=256, iters=4000,
          noise=0.0, seed=42, device="cpu"):
    torch.manual_seed(seed)
    rng = np.random.default_rng(seed)
    model = RecurrentModularSolver(p, n_actions=p + 3, hidden_dim=hidden_dim).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=wd)
    crit = nn.CrossEntropyLoss()
    print(f"[TRAIN recurrent] p={p} hidden={hidden_dim} wd={wd} L={L} noise={noise} "
          f"iters={iters} device={device}", flush=True)
    print(f"{'iter':>6} {'loss':>8} {'lastacc':>8}", flush=True)
    model.train()
    for it in range(1, iters + 1):
        acts, tgts = gen_batch(batch, L, p, rng, device)
        logits = model(acts, noise=noise)
        loss = crit(logits.reshape(-1, p), tgts.reshape(-1))
        opt.zero_grad(); loss.backward()
        torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)   # standard RNN stabiliser
        opt.step()
        if it == 1 or it % 500 == 0:
            with torch.no_grad():
                last = (logits[:, -1].argmax(-1) == tgts[:, -1]).float().mean().item()
            print(f"{it:>6} {loss.item():>8.4f} {last:>8.3f}", flush=True)
    # held-out generalization: fresh random walks the model has never seen
    model.eval()
    with torch.no_grad():
        acts, tgts = gen_batch(512, L, p, rng, device)
        logits, hs = model(acts, return_hidden=True)
        burn = 4
        acc = (logits[:, burn:].argmax(-1) == tgts[:, burn:]).float().mean().item()
    print(f"  held-out per-step accuracy (fresh walks, t>={burn}) = {acc:.4f}", flush=True)
    H = hs[:, burn:, :].reshape(-1, hidden_dim).cpu().numpy()
    S = tgts[:, burn:].reshape(-1).cpu().numpy()
    counts = np.array([(S == s).sum() for s in range(p)])
    print(f"  state coverage: {(counts > 0).sum()}/{p} ring states visited "
          f"(min={int(counts.min())}, median={int(np.median(counts))} samples/state)", flush=True)
    Hmean = np.stack([H[S == s].mean(0) if counts[s] > 0 else np.zeros(hidden_dim)
                      for s in range(p)])
    return Hmean, H, S, acc


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=42)
    ap.add_argument("--p", type=int, default=97)
    ap.add_argument("--wd", type=float, default=0.5)
    ap.add_argument("--noise", type=float, default=0.0)
    ap.add_argument("--iters", type=int, default=4000)
    ap.add_argument("--L", type=int, default=64)
    args = ap.parse_args()
    device = "cuda" if torch.cuda.is_available() else "cpu"

    print("=" * 78)
    print("REMEMBER-vs-COMPUTE  --  recurrent modular path-integrator (Z_p ring)")
    print("=" * 78)
    Hmean, Hraw, S, acc = train(p=args.p, wd=args.wd, noise=args.noise, L=args.L,
                                iters=args.iters, seed=args.seed, device=device)
    outdir = os.path.join(_HERE, "logs", "ph_grok", f"recurrent_seed{args.seed}")
    os.makedirs(outdir, exist_ok=True)
    np.save(os.path.join(outdir, "recurrent_hidden_classmean.npy"), Hmean)
    print(f"  [saved H[s] -> {outdir}]", flush=True)

    # ---- FFT: recurrent ring (expect k=1) vs feedforward folded ribbon (k=8,15,25,26) ----
    print("\n" + "=" * 78)
    print("FUNCTIONAL FFT  --  recurrent H[s] vs cached feedforward class-means")
    print("=" * 78, flush=True)
    show("recurrent H[s]", spectrum(Hmean))
    ff = os.path.join(_HERE, "logs", "ph_grok", f"seed{args.seed}", "post_hidden_classmean.npy")
    if os.path.exists(ff):
        show("feedforward (cached)", spectrum(np.load(ff)))

    # ---- topology: SAME calibrated reader that gave the feedforward b1=0 ----
    print("\n" + "=" * 78, flush=True)
    gate_ok, tau1, tau2 = run_calibration()
    if not gate_ok:
        print("\n  >>> reader NOT calibrated; aborting topology readout (honest gate stop).")
        return
    print(f"\n{'='*78}\n  RECURRENT BARCODE READOUT  seed={args.seed}  "
          f"(held-out acc={acc:.3f})\n{'='*78}", flush=True)
    print("  -- prior: ring attractor over Z_p  ->  b1=1 (vs feedforward b1=0)", flush=True)
    read_layer("recurrent H[s]",    Hmean, tau1, tau2, "RING b1=1")
    read_layer("recurrent full",    Hraw,  tau1, tau2, "RING b1=1 + scatter", n_sub=N_H1)
    print("=" * 78, flush=True)


if __name__ == "__main__":
    main()
