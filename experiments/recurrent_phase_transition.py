#!/usr/bin/env python3
"""recurrent_phase_transition.py -- Leg 3 (decisions/0010 follow-on): the alpha-gate sweep.

Sweep the recurrence gate alpha in  h_t = cell(x_t, alpha * h_{t-1})  from 0 (feedforward,
no memory) to 1 (full recurrence) on the modular path-integration task, and watch the
representational topology turn on.  Pre-registered question: as alpha rises, does the carrier
frequency k* / the loop b1 change SMOOTHLY (crossover) or DISCONTINUOUSLY (first-order snap)?

PRE-REGISTERED RIVAL HYPOTHESES (stated before running; reader gate is pre-calibrated):
  H_snap   (ghost-parity / Floquet, Bateman-Turok analogy as the collaborators frame it):
           k* HOLDS at a HIGH feedforward-like carrier while acc is low, then DISCONTINUOUSLY
           snaps to the fundamental (k=1/3) at a critical alpha*; b1 jumps 0 -> >=1 at the SAME
           alpha*.  A sharp, possibly hysteretic, first-order transition.
  H_smooth (null / crossover): k* drifts down and b1 creeps up through tau1* gradually; no
           discontinuity.
  H_cap    (DEFLATIONARY -- the mundane confound I must rule out): there is no exotic resonance;
           the gate is just a memory horizon (state retained ~ alpha^L).  Then the onset alpha*
           is set by alpha*^(L-1) ~ const, so alpha* must INCREASE with sequence length L.
           DISCRIMINATOR: run two L; if alpha* moves as 1 - c/L it is capacity, not a universal
           critical point.

DEVIN'S OWN PREDICTION (differs from the collaborators', logged so I cannot retro-fit):
  BELOW alpha* the net cannot integrate, so its hidden cloud is INCOHERENT (no clean carrier:
  low dominant-mode power, noisy k*), NOT a coherent high-frequency 'ghost sector'.  The ring
  (k=low, b1>=1) appears together with task competence.  So I expect H_snap's 'holds high then
  snaps' to be FALSIFIED in favour of 'incoherent blob -> coherent ring', and the onset to track
  H_cap (capacity), unless the two-L control shows an L-invariant alpha*.

Reuses the IDENTICAL calibrated reader (run_calibration -> tau1*), the FFT, and the
circular-coordinate winding probe, so every number is on the same footing as the rest of 0010.
"""
import argparse
import os
import sys

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

from persistent_homology_grokking import run_calibration                         # noqa: E402
from fft_classmeans_grokking import spectrum                                     # noqa: E402
from circular_coordinate_probe import fourier_power, winding_mode, b1_of, recon_single  # noqa: E402
from recurrent_modular_grokking import gen_batch                                 # noqa: E402

import torch                                                                     # noqa: E402
import torch.nn as nn                                                            # noqa: E402

LOGDIR = os.path.join(_HERE, "logs", "ph_grok")
_lines = []


def out(s=""):
    print(s, flush=True)
    _lines.append(s)


class AlphaRecurrentSolver(nn.Module):
    """GRU path-integrator whose recurrent feedback is scaled by a FIXED gate alpha.
    alpha=0 -> h_t depends only on the current token (no memory, pure feedforward per step);
    alpha=1 -> ordinary GRU recurrence."""

    def __init__(self, p, n_actions, alpha, emb_dim=32, hidden_dim=128):
        super().__init__()
        self.p, self.hidden_dim = p, hidden_dim
        self.register_buffer("alpha", torch.tensor(float(alpha)))
        self.act_emb = nn.Embedding(n_actions, emb_dim)
        self.cell = nn.GRUCell(emb_dim, hidden_dim)
        self.readout = nn.Linear(hidden_dim, p)
        self.h0 = nn.Parameter(torch.zeros(hidden_dim))

    def forward(self, actions, return_hidden=False):
        B, L = actions.shape
        h = self.h0.unsqueeze(0).expand(B, -1).contiguous()
        logits, hs = [], []
        for t in range(L):
            h = self.cell(self.act_emb(actions[:, t]), self.alpha * h)
            logits.append(self.readout(h))
            if return_hidden:
                hs.append(h)
        logits = torch.stack(logits, 1)
        return (logits, torch.stack(hs, 1)) if return_hidden else logits


def train_one(alpha, L, iters, seed, p=97, hidden=128, wd=0.5, lr=1e-3, batch=256, device="cpu"):
    torch.manual_seed(seed)
    rng = np.random.default_rng(seed)
    model = AlphaRecurrentSolver(p, n_actions=p + 3, alpha=alpha, hidden_dim=hidden).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=wd)
    crit = nn.CrossEntropyLoss()
    model.train()
    for it in range(1, iters + 1):
        acts, tgts = gen_batch(batch, L, p, rng, device)
        loss = crit(model(acts).reshape(-1, p), tgts.reshape(-1))
        opt.zero_grad(); loss.backward()
        torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
        opt.step()
    model.eval()
    burn = max(2, L // 4)
    with torch.no_grad():
        acts, tgts = gen_batch(512, L, p, rng, device)
        logits, hs = model(acts, return_hidden=True)
        acc = (logits[:, burn:].argmax(-1) == tgts[:, burn:]).float().mean().item()
    H = hs[:, burn:, :].reshape(-1, hidden).cpu().numpy()
    S = tgts[:, burn:].reshape(-1).cpu().numpy()
    counts = np.array([(S == s).sum() for s in range(p)])
    Hmean = np.stack([H[S == s].mean(0) if counts[s] > 0 else np.zeros(hidden) for s in range(p)])
    return acc, Hmean, int((counts > 0).sum())


def metrics(Hmean, tau1):
    P, kstar, F = fourier_power(Hmean)
    pwr = float(P[kstar - 1])                       # dominant-mode power fraction (coherence)
    b1_full, top = b1_of(Hmean, tau1)
    b1_dom, _ = b1_of(recon_single(F, kstar), tau1)  # isolated dominant carrier
    wind = winding_mode(Hmean, F, kstar)
    sp = spectrum(Hmean)
    return dict(kstar=kstar, pwr=pwr, b1_full=b1_full, b1_dom=b1_dom,
                wind=wind, top=float(top[0]), pr=sp["pr"])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=42)
    ap.add_argument("--L", type=int, default=12)
    ap.add_argument("--iters", type=int, default=2500)
    ap.add_argument("--n-alpha", type=int, default=11)
    ap.add_argument("--alpha-max", type=float, default=1.0,
                    help="sweep [0, alpha_max]; use 0.1 for the Leg-3b fine sub-0.1 grid")
    args = ap.parse_args()
    device = "cuda" if torch.cuda.is_available() else "cpu"
    alphas = np.linspace(0.0, args.alpha_max, args.n_alpha)

    out("=" * 80)
    out(f"RECURRENT PHASE TRANSITION (Leg 3)  --  alpha in [0, {args.alpha_max:g}] "
        f"({args.n_alpha} pts)  L={args.L} seed={args.seed}")
    out("  H_snap: k* holds high then SNAPS to fundamental; b1 jumps 0->1 at same alpha* (sharp)")
    out("  H_smooth: k* drifts, b1 creeps up (crossover)   |   H_cap: alpha* set by memory ~alpha^L")
    out("=" * 80)
    gate_ok, tau1, tau2 = run_calibration()
    if not gate_ok:
        out("  reader NOT calibrated; abort."); _flush(); sys.exit(1)

    out(f"\n  device={device}  iters={args.iters}  reader tau1*={tau1:.3f}")
    out(f"\n  {'alpha':>6} {'testacc':>8} {'k*':>4} {'k*pwr%':>7} {'b1full':>7} {'b1dom':>6} "
        f"{'wind':>6} {'topH1':>6} {'cover':>6}")
    rows = []
    for a in alphas:
        acc, Hmean, cover = train_one(a, args.L, args.iters, args.seed, device=device)
        m = metrics(Hmean, tau1)
        rows.append(dict(alpha=float(a), acc=acc, cover=cover, **m))
        out(f"  {a:>6.2f} {acc:>8.3f} {m['kstar']:>4d} {m['pwr']*100:>7.1f} {m['b1_full']:>7d} "
            f"{m['b1_dom']:>6d} {m['wind']:>+6.1f} {m['top']:>6.3f} {cover:>4d}/97")
        _write()   # incremental flush so progress is readable mid-run

    # ---- transition diagnostics ----
    out("\n" + "=" * 80)
    accs = np.array([r["acc"] for r in rows])
    b1s = np.array([r["b1_full"] for r in rows])
    # alpha*: first alpha whose acc crosses 0.5
    above = np.where(accs >= 0.5)[0]
    astar = alphas[above[0]] if len(above) else None
    dacc = np.diff(accs)
    jmp = int(np.argmax(dacc)) if len(dacc) else -1
    out(f"  onset alpha* (acc>=0.5): {astar if astar is not None else 'never reached'}")
    if jmp >= 0:
        out(f"  largest single-step acc jump: {dacc[jmp]:+.2f} between alpha={alphas[jmp]:.2f}"
            f" -> {alphas[jmp+1]:.2f}  (sharp if one step carries most of the rise)")
    # coherence below onset: do failing nets carry a coherent HIGH carrier (H_snap) or noise (Devin)?
    if astar is not None and above[0] > 0:
        below = rows[:above[0]]
        hi = [r for r in below if r["kstar"] >= 6 and r["pwr"] >= 0.30]
        out(f"  sub-onset regime: {len(hi)}/{len(below)} alphas show a COHERENT high carrier "
            f"(k*>=6 & power>=30%). dom-mode power below onset = "
            f"{[round(r['pwr'],2) for r in below]}")
        out("    -> many coherent-high => supports H_snap 'ghost sector'; near-zero/noisy => "
            "supports Devin 'incoherent blob below onset'.")
    # does b1 turn on with acc?
    on = np.where(b1s >= 1)[0]
    if len(on):
        out(f"  b1>=1 first at alpha={alphas[on[0]]:.2f} (acc there={accs[on[0]]:.2f}); "
            f"k* there={rows[on[0]]['kstar']}  -> ring appears "
            f"{'WITH' if astar is not None and abs(alphas[on[0]]-astar)<=0.11 else 'OFFSET FROM'} "
            f"task competence")
    else:
        out("  b1>=1 never reached in this sweep")
    out("  CAPACITY CONTROL: rerun with a different --L; if alpha* tracks 1-c/L it is a memory")
    out("  horizon (H_cap), not a universal critical point. (sharp vs smooth is read off the table)")
    out("=" * 80)
    _flush()


def _write():
    os.makedirs(LOGDIR, exist_ok=True)
    tag = "" if abs(_AMAX - 1.0) < 1e-9 else f"_amax{_AMAX:g}"
    path = os.path.join(LOGDIR, f"phase_transition_L{_L}_seed{_SEED}{tag}.txt")
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(_lines) + "\n")
    return path


def _flush():
    print(f"\n[summary written -> {_write()}]", flush=True)


if __name__ == "__main__":
    # capture L/seed for the log filename without re-parsing
    import sys as _sys
    _L = 12
    _SEED = 42
    _AMAX = 1.0
    for i, a in enumerate(_sys.argv):
        if a == "--L":
            _L = int(_sys.argv[i + 1])
        if a == "--seed":
            _SEED = int(_sys.argv[i + 1])
        if a == "--alpha-max":
            _AMAX = float(_sys.argv[i + 1])
    main()
