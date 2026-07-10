#!/usr/bin/env python3
"""torus_integrator_grokking.py -- Waypoint B (decisions/0010): the 2-torus integrator.

Scale the recurrent path-integrator to TWO independent running sums on Z_p:
    s1_t = (s1_{t-1} + v1_t) mod p ,   s2_t = (s2_{t-1} + v2_t) mod p ,   v in {-1,0,+1}.
Two readout heads must recover BOTH sums, so a competent net CANNOT collapse to a 1D code -- it
must carry two independent circular variables.  The decisive question is the SHAPE of their join:

  * GENUINE FLAT TORUS  T^2 = S^1 x S^1  ->  b0=1, b1=2, b2=1   (two cycles + an enclosed 2-void)
  * DEGENERATE WEDGE / figure-8         ->  b0=1, b1=2, b2=0   (two cycles glued at a point, NO void)

(NB: two independent rings in orthogonal subspaces ARE a torus with b2=1 -- the b2=0 alternative is
the degenerate case where the join carries no 2-cell.)  Since b1>=2 is forced by competence, the
experiment is entirely a test of b2 -- which is exactly the H2 reading that is the NOISIEST part of
the calibrated pipeline (synthetic-torus margin was only ~0.29 vs tau2*=0.18).  Mitigations
(per the lab's guidance): SMALL modulus p so the p^2 class-mean skeleton is DENSE, letting the
calibrated reader's H2 subsample (N_H2 of p^2) cover the torus far more densely than the synthetic
calibration (100-of-1200) -- we keep the IDENTICAL calibrated subsampling (maxdim=2 Rips explodes
with concentration of measure if fed all N, and tau2* was calibrated at N_H2); and report the H2
BARCODE GAP (top bar vs 2nd bar) -- a distinct isolated top H2 bar is a positive 2-void signature
even if it falls under the conservative gate.

Reuses the IDENTICAL calibrated reader (run_calibration -> tau1*, tau2*) and analyze/betti.
"""
import argparse
import os
import sys

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

from persistent_homology_grokking import (analyze, betti, run_calibration,    # noqa: E402
                                          N_H1, NB_H1, N_H2, NB_H2)
from circular_coordinate_probe import b1_of                                # noqa: E402

import torch                                                              # noqa: E402
import torch.nn as nn                                                     # noqa: E402

LOGDIR = os.path.join(_HERE, "logs", "ph_grok")
_lines = []


def out(s=""):
    print(s, flush=True)
    _lines.append(s)


def _write():
    os.makedirs(LOGDIR, exist_ok=True)
    path = os.path.join(LOGDIR, f"torus_integrator_p{_P}_seed{_SEED}.txt")
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(_lines) + "\n")
    return path


class TorusRecurrentSolver(nn.Module):
    """GRU integrator with two action channels (one per running sum) and two readout heads.
    Per channel: tokens 0,1,2 -> velocity -1,0,+1; tokens 3..3+p-1 -> absolute set s at t=0."""

    def __init__(self, p, hidden_dim=256, emb_dim=32):
        super().__init__()
        self.p, self.hidden_dim = p, hidden_dim
        self.emb1 = nn.Embedding(p + 3, emb_dim)
        self.emb2 = nn.Embedding(p + 3, emb_dim)
        self.cell = nn.GRUCell(2 * emb_dim, hidden_dim)
        self.head1 = nn.Linear(hidden_dim, p)
        self.head2 = nn.Linear(hidden_dim, p)
        self.h0 = nn.Parameter(torch.zeros(hidden_dim))

    def forward(self, a1, a2, return_hidden=False):
        B, L = a1.shape
        h = self.h0.unsqueeze(0).expand(B, -1).contiguous()
        l1, l2, hs = [], [], []
        for t in range(L):
            x = torch.cat([self.emb1(a1[:, t]), self.emb2(a2[:, t])], dim=-1)
            h = self.cell(x, h)
            l1.append(self.head1(h)); l2.append(self.head2(h))
            if return_hidden:
                hs.append(h)
        L1, L2 = torch.stack(l1, 1), torch.stack(l2, 1)
        return (L1, L2, torch.stack(hs, 1)) if return_hidden else (L1, L2)


def gen_batch_torus(B, L, p, rng, device):
    s1 = rng.integers(0, p, B); s2 = rng.integers(0, p, B)
    a1 = np.zeros((B, L), int); a2 = np.zeros((B, L), int)
    t1 = np.zeros((B, L), int); t2 = np.zeros((B, L), int)
    a1[:, 0] = 3 + s1; a2[:, 0] = 3 + s2
    t1[:, 0] = s1; t2[:, 0] = s2
    for t in range(1, L):
        v1 = rng.integers(0, 3, B); v2 = rng.integers(0, 3, B)
        a1[:, t] = v1; a2[:, t] = v2
        s1 = (s1 + (v1 - 1)) % p; s2 = (s2 + (v2 - 1)) % p
        t1[:, t] = s1; t2[:, t] = s2
    tt = lambda z: torch.tensor(z, device=device)
    return tt(a1), tt(a2), tt(t1), tt(t2)


def train(p, L, iters, seed, hidden=256, wd=0.5, lr=1e-3, batch=512, device="cpu"):
    torch.manual_seed(seed)
    rng = np.random.default_rng(seed)
    model = TorusRecurrentSolver(p, hidden_dim=hidden).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=wd)
    crit = nn.CrossEntropyLoss()
    model.train()
    for it in range(1, iters + 1):
        a1, a2, t1, t2 = gen_batch_torus(batch, L, p, rng, device)
        L1, L2 = model(a1, a2)
        loss = crit(L1.reshape(-1, p), t1.reshape(-1)) + crit(L2.reshape(-1, p), t2.reshape(-1))
        opt.zero_grad(); loss.backward()
        torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
        opt.step()
        if it % max(1, iters // 6) == 0 or it == 1:
            with torch.no_grad():
                a = (L1.argmax(-1) == t1).float().mean().item()
                b = (L2.argmax(-1) == t2).float().mean().item()
            out(f"    iter {it:>5d}  loss {loss.item():.3f}  trainacc s1={a:.3f} s2={b:.3f}")
    model.eval()
    burn = max(3, L // 4)
    with torch.no_grad():
        a1, a2, t1, t2 = gen_batch_torus(4096, L, p, rng, device)
        L1, L2, hs = model(a1, a2, return_hidden=True)
        acc1 = (L1[:, burn:].argmax(-1) == t1[:, burn:]).float().mean().item()
        acc2 = (L2[:, burn:].argmax(-1) == t2[:, burn:]).float().mean().item()
    H = hs[:, burn:, :].reshape(-1, hidden).cpu().numpy()
    S1 = t1[:, burn:].reshape(-1).cpu().numpy()
    S2 = t2[:, burn:].reshape(-1).cpu().numpy()
    # joint class-means on the full p x p grid (no subsampling)
    grid = np.zeros((p, p, hidden)); cnt = np.zeros((p, p), int)
    np.add.at(grid, (S1, S2), H)
    np.add.at(cnt, (S1, S2), 1)
    grid = grid / np.maximum(cnt, 1)[:, :, None]
    return acc1, acc2, grid, int((cnt > 0).sum())


def fft2_carriers(grid, topn=6):
    """Dominant 2D Fourier modes of the (s1,s2)->R^D grid (DC removed).  A clean PRODUCT torus
    concentrates power on the axes (k1,0) and (0,k2); cross-terms (k1,k2) signal entanglement."""
    p = grid.shape[0]
    F = np.fft.fft2(grid - grid.mean((0, 1), keepdims=True), axes=(0, 1))
    P = (np.abs(F) ** 2).sum(-1)
    P[0, 0] = 0.0
    Pn = P / (P.sum() + 1e-30)
    idx = np.dstack(np.unravel_index(np.argsort(-Pn.ravel()), P.shape))[0][:topn]
    fold = lambda k: k if k <= p // 2 else k - p
    return [((fold(int(i)), fold(int(j))), float(Pn[i, j])) for i, j in idx]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--p", type=int, default=17)
    ap.add_argument("--L", type=int, default=20)
    ap.add_argument("--iters", type=int, default=6000)
    ap.add_argument("--seed", type=int, default=42)
    ap.add_argument("--hidden", type=int, default=256)
    args = ap.parse_args()
    device = "cuda" if torch.cuda.is_available() else "cpu"

    out("=" * 80)
    out(f"2-TORUS INTEGRATOR (Waypoint B)  --  two running sums on Z_{args.p}  "
        f"L={args.L} seed={args.seed}")
    out("  competent net forces b1>=2; the test is b2:  TORUS b2=1 (2-void)  vs  WEDGE b2=0")
    out("=" * 80)
    gate_ok, tau1, tau2 = run_calibration()
    if not gate_ok:
        out("  reader NOT calibrated; abort."); _write(); sys.exit(1)
    out(f"\n  device={device}  reader tau1*={tau1:.3f}  tau2*={tau2:.3f}")

    out(f"\n  training 2-torus integrator (p={args.p}, hidden={args.hidden}, iters={args.iters}):")
    acc1, acc2, grid, cover = train(args.p, args.L, args.iters, args.seed,
                                    hidden=args.hidden, device=device)
    out(f"  -> test acc  s1={acc1:.3f}  s2={acc2:.3f}   grid coverage {cover}/{args.p**2}")
    _write()   # bank the trained-model result before the (slow) maxdim=2 H2 step

    p = args.p
    Hmean = grid.reshape(p * p, -1)
    out(f"\n  {'='*76}\n  TOPOLOGY of joint code H[s1,s2]  (grid N={p*p}; calibrated reader "
        f"subsamples H1:{N_H1}x{NB_H1} H2:{N_H2}x{NB_H2})\n  {'='*76}")
    pdH1, tmH1 = analyze(Hmean, maxdim=1, n_sub=N_H1, n_boot=NB_H1, base_seed=args.seed)
    pdH2, tmH2 = analyze(Hmean, maxdim=2, n_sub=N_H2, n_boot=NB_H2, base_seed=args.seed)
    b1, _ = betti(pdH1[1], tau1)
    b2, _ = betti(pdH2[2], tau2)
    topH1, topH2 = tmH1[1], tmH2[2]
    gap1 = topH1[0] / (topH1[1] + 1e-9)
    gap2 = topH2[0] / (topH2[1] + 1e-9)
    out(f"    b1 = {b1}   (tau1*={tau1:.3f})   top-5 H1 = [{' '.join(f'{x:.3f}' for x in topH1[:5])}]"
        f"   gap(top/2nd)={gap1:.1f}x")
    out(f"    b2 = {b2}   (tau2*={tau2:.3f})   top-5 H2 = [{' '.join(f'{x:.3f}' for x in topH2[:5])}]"
        f"   gap(top/2nd)={gap2:.1f}x")

    # marginals: each running sum, averaged over the other, must be a clean single ring (b1=1)
    G = grid
    b1_m1, _ = b1_of(G.mean(axis=1), tau1)
    b1_m2, _ = b1_of(G.mean(axis=0), tau1)
    out(f"\n    marginal rings: s1-circle b1={b1_m1}   s2-circle b1={b1_m2}  (each should be 1)")

    car = fft2_carriers(grid)
    out(f"    2D carriers (k1,k2):power  " +
        "  ".join(f"({k[0]:+d},{k[1]:+d}):{pw*100:.0f}%" for k, pw in car))
    on_axis = sum(pw for (k1, k2), pw in car[:4] if k1 == 0 or k2 == 0)
    cross = sum(pw for (k1, k2), pw in car[:4] if k1 != 0 and k2 != 0)
    out(f"    axis-power(top4)={on_axis*100:.0f}%  cross-power(top4)={cross*100:.0f}%  "
        f"(axis-dominant => clean PRODUCT torus; cross-heavy => entangled)")

    out("\n" + "=" * 80)
    competent = acc1 > 0.8 and acc2 > 0.8
    if not competent:
        out(f"  net not yet competent (acc s1={acc1:.2f} s2={acc2:.2f}); topology may be partial "
            f"-- raise --iters before trusting b2.")
    if b2 >= 1:
        out(f"  VERDICT: GENUINE 2-TORUS confirmed -- b1={b1}>=2 and b2={b2}>=1 clears tau2*. "
            f"The net builds a 2D toroidal coordinate system, not a wedge.")
    elif gap2 >= 2.0:
        out(f"  VERDICT: BORDERLINE torus -- b2 reads 0 under the conservative gate, BUT the top H2 "
            f"bar ({topH2[0]:.3f}) stands {gap2:.1f}x above the H2 noise floor ({topH2[1]:.3f}): a "
            f"real but faint 2-void. Consistent with a torus the reader cannot crisply certify.")
    else:
        out(f"  VERDICT: NO 2-void (b2=0, top H2 bar {topH2[0]:.3f} not isolated, gap {gap2:.1f}x). "
            f"With b1={b1}, the join is a WEDGE/figure-8 of circles, not a product torus.")
    out("=" * 80)
    print(f"\n[summary written -> {_write()}]", flush=True)


if __name__ == "__main__":
    import sys as _sys
    _P, _SEED = 17, 42
    for i, a in enumerate(_sys.argv):
        if a == "--p":
            _P = int(_sys.argv[i + 1])
        if a == "--seed":
            _SEED = int(_sys.argv[i + 1])
    main()
