#!/usr/bin/env python3
"""
representation_manifold_grokking.py  --  Path B of pre-registration decisions/0009.

The non-tautological test of the spatial Tsallis law q* = 1 + 2/d_s.  Path A (0008)
confirmed the law on graphs whose d_s is KNOWN; here d_s is EMERGENT -- it is whatever
geometry a network crystallizes when it groks a + b (mod p).  We track, across the
memorize -> grok transition, the representation manifold's

    * spectral dimension d_s   (two independent estimators, reused from Path A), and
    * Tsallis index q*         (q-exponential fit of the heat-kernel return prob),

and ask whether (d_s, q*) ride the curve q* = 1 + 2/d_s  [H1 spatial/fractal]  or whether
q* pins near 3/2 independent of d_s  [H2 algebraic attractor].

CRUCIAL SCOPE NOTE (correctness): a EUCLIDEAN point-cloud affinity graph recovers the
manifold's intrinsic (Hausdorff) dimension as seen by ordinary diffusion -- circle -> 1,
2-torus -> 2, Gaussian R^k -> k.  This differs from Path A's INTRINSIC-GRAPH d_s (where a
Sierpinski *graph* gives the spectral 2ln3/ln5 ~ 1.365).  So a chaos-game Sierpinski *cloud*
calibrates to its Hausdorff value ln3/ln2 ~ 1.585.  Phase 0 calibrates the cloud pipeline on
manifolds with unambiguous Euclidean dimension BEFORE any activation readout is trusted.

Reuses (no reinvention):
  * estimators            experiments/spectral_dimension_quench.py
  * grok model + data     demos/analog_modular_arithmetic.py (EmbeddingGrokMLP, dataset)
  * escort Dirichlet form demos/explore_defect_duality.py (here computed EXACTLY)
"""

import argparse
import json
import math
import os
import sys
import time

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)
sys.path.insert(0, os.path.join(_HERE, "..", "demos"))

# Path A estimators -- identical functions, so Path B inherits the validated calibration.
from spectral_dimension_quench import (  # noqa: E402
    scaling_window, fit_ds_return, fit_ds_dos, fit_q_qexp,
)

ZERO_TOL = 1e-9
SEEDS = [42, 43, 44, 45]


# --------------------------------------------------------------------------- #
# Point cloud  ->  symmetric normalized graph Laplacian spectrum               #
# --------------------------------------------------------------------------- #
def affinity_laplacian(X, mode="knn", k=12, sigma_scale=1.0):
    """Center+unit-RMS the cloud, build a symmetric affinity, return
    (eigs of L_sym = I - D^-1/2 A D^-1/2, affinity A, degree vector)."""
    X = np.asarray(X, dtype=float)
    X = X - X.mean(axis=0, keepdims=True)
    rms = math.sqrt(float((X ** 2).sum(axis=1).mean())) + 1e-12
    X = X / rms
    N = len(X)
    sq = (X ** 2).sum(1)[:, None] + (X ** 2).sum(1)[None, :] - 2.0 * (X @ X.T)
    sq = np.maximum(sq, 0.0)
    if mode == "knn":
        kk = min(k, N - 1)
        order = np.argsort(sq, axis=1)[:, 1:kk + 1]          # exclude self
        kept = np.sqrt(sq[np.arange(N)[:, None], order])
        sigma = sigma_scale * (float(np.median(kept)) + 1e-12)
        A = np.zeros((N, N))
        rows = np.repeat(np.arange(N), kk)
        A[rows, order.ravel()] = np.exp(-(kept.ravel() ** 2) / (2.0 * sigma ** 2))
        A = np.maximum(A, A.T)                                # symmetrize union
    else:  # full Gaussian
        sigma = sigma_scale * (float(np.median(np.sqrt(sq[sq > 1e-18]))) + 1e-12)
        A = np.exp(-sq / (2.0 * sigma ** 2))
        np.fill_diagonal(A, 0.0)
    deg = A.sum(1)
    inv_sqrt = 1.0 / np.sqrt(np.where(deg > 1e-12, deg, 1.0))
    L = np.eye(N) - (A * inv_sqrt[:, None]) * inv_sqrt[None, :]
    L = 0.5 * (L + L.T)
    eigs = np.clip(np.linalg.eigvalsh(L), 0.0, None)
    return eigs, A, deg


def escort_gap(A, deg, q):
    """Exact escort spectral gap gamma_q = min_{f indep of escort-const}
    E_q(f)/Var_q(f), with E_q the escort Dirichlet form (pi^q weights) and Var_q
    the escort variance.  Solved as the smallest positive generalized eigenvalue of
    (L_q, diag(pi^q)); the Z_q normalization cancels.  pi = stationary deg measure."""
    from scipy.linalg import eigh
    pi = deg / deg.sum()
    pq = np.power(np.clip(pi, 1e-30, None), q)
    Wt = 0.5 * (pq[:, None] + pq[None, :]) * A                # symmetric escort weights
    Lq = np.diag(Wt.sum(1)) - Wt
    try:
        w = eigh(Lq, np.diag(pq), eigvals_only=True)
    except Exception:
        return float("nan")
    w = np.sort(w)
    thresh = 1e-9 * max(1.0, float(w[-1]))
    pos = w[w > thresh]
    return float(pos[0]) if len(pos) else 0.0


def window_norm(eigs, min_decades=0.8):
    """Power-law return window for a NORMALIZED Laplacian (spectrum in [0,2]).

    Distinct from Path A's scaling_window (tuned for combinatorial Laplacians with a
    ~10^6 dynamic range): here the principled window runs between the fastest- and
    slowest-mode timescales t in [1/lam_max, 1/lam2].  Fewer than min_decades of range
    == spectral gap == high-d / gapped -> q* -> 1."""
    nz = eigs[eigs > ZERO_TOL]
    if len(nz) < 8:
        return None
    lam2, lam_max = float(nz.min()), float(nz.max())
    t_lo, t_hi = 1.0 / lam_max, 1.0 / lam2
    if t_hi <= t_lo or math.log10(t_hi / t_lo) < min_decades:
        return None
    return np.geomspace(t_lo, t_hi, 64)


def analyze_manifold(X, mode="knn", k=12, escort_qs=None):
    """Point cloud -> {d_s (return primary + DOS cross-check), q* (q-exp fit), escort}."""
    eigs, A, deg = affinity_laplacian(X, mode=mode, k=k)
    window = window_norm(eigs)
    out = dict(n=int(len(X)))
    if window is None:                                        # gapped == high-d / expander
        out.update(gapped=True, ds_ret=float("inf"), ds_dos=float("nan"),
                   q_star=1.0, q_pred=1.0, resid=0.0)
    else:
        ds_ret = float(fit_ds_return(eigs, window))           # PRIMARY on point clouds
        ds_dos = float(fit_ds_dos(eigs))                      # independent cross-check
        q_star, _tau, resid = fit_q_qexp(eigs, window)
        out.update(gapped=False, ds_ret=ds_ret, ds_dos=ds_dos, q_star=float(q_star),
                   q_pred=(1.0 + 2.0 / ds_ret if ds_ret > 0 else float("nan")),
                   resid=float(resid))
    if escort_qs is not None and len(deg) <= 256:             # cheap only on small graphs
        out["escort"] = {f"{q:.2f}": escort_gap(A, deg, q) for q in escort_qs}
    return out


# --------------------------------------------------------------------------- #
# Phase 0  --  synthetic calibration of the CLOUD pipeline                      #
# --------------------------------------------------------------------------- #
def _circle(n, rng, dim=8, noise=0.004):
    t = rng.uniform(0, 2 * np.pi, n)
    base = np.stack([np.cos(t), np.sin(t)], 1)
    pad = np.zeros((n, dim - 2))
    return np.concatenate([base, pad], 1) + noise * rng.standard_normal((n, dim))


def _torus(n, rng, dim=8, noise=0.02):
    t, s = rng.uniform(0, 2 * np.pi, n), rng.uniform(0, 2 * np.pi, n)
    base = np.stack([np.cos(t), np.sin(t), np.cos(s), np.sin(s)], 1)
    pad = np.zeros((n, dim - 4))
    return np.concatenate([base, pad], 1) + noise * rng.standard_normal((n, dim))


def _gaussian(n, rng, k=3, dim=8):
    X = np.zeros((n, dim))
    X[:, :k] = rng.standard_normal((n, k))
    return X


def _sierpinski_cloud(n, rng, dim=8, noise=0.0):
    verts = np.array([[0.0, 0.0], [1.0, 0.0], [0.5, math.sqrt(3) / 2]])
    p = rng.standard_normal(2) * 0.1
    pts = []
    for i in range(n + 200):
        p = (p + verts[rng.integers(3)]) / 2.0
        if i >= 200:
            pts.append(p.copy())
    base = np.array(pts)
    pad = np.zeros((len(base), dim - 2))
    return np.concatenate([base, pad], 1) + noise * rng.standard_normal((len(base), dim))


def _highd(n, rng, dim=50):
    return rng.standard_normal((n, dim))


def run_calibration(mode, k, n=800, seed=42):
    rng = np.random.default_rng(seed)
    # (name, cloud, Euclidean d_s truth)  -- Sierpinski cloud truth = Hausdorff ln3/ln2.
    clouds = [
        ("circle",        _circle(n, rng),                  1.000),
        ("Sierpinski2D",  _sierpinski_cloud(n, rng),        math.log(3) / math.log(2)),
        ("2-torus",       _torus(n, rng),                   2.000),
        ("Gaussian R^3",  _gaussian(n, rng, 3),             3.000),
        ("high-d R^50",   _highd(n, rng),                   float("inf")),
    ]
    hdr = f"{'cloud':<14}{'d_s truth':>11}{'d_s(ret)':>11}{'d_s(DOS)':>11}{'q*(fit)':>10}{'1+2/d_s':>10}"
    print("\n" + "=" * len(hdr))
    print(f"PHASE 0  CLOUD CALIBRATION  (affinity={mode}, k={k}, N={n})")
    print("=" * len(hdr))
    print(hdr)
    print("-" * len(hdr))
    rows, gate_ok = [], True
    for name, X, truth in clouds:
        r = analyze_manifold(X, mode=mode, k=k)
        r["cloud"], r["truth"] = name, truth
        rows.append(r)
        if r["gapped"]:
            ok = math.isinf(truth)
            print(f"{name:<14}{'inf':>11}{'gapped':>11}{'gapped':>11}{1.0:>10.3f}{1.0:>10.3f}"
                  f"   {'OK' if ok else 'FAIL'}")
            gate_ok &= ok
            continue
        rel = abs(r["ds_ret"] - truth) / truth if truth > 0 else 1.0
        ok = (rel <= 0.25)
        gate_ok &= ok
        print(f"{name:<14}{truth:>11.3f}{r['ds_ret']:>11.3f}{r['ds_dos']:>11.3f}"
              f"{r['q_star']:>10.3f}{r['q_pred']:>10.3f}   {'OK' if ok else 'FAIL'}")
    qs = [r["q_star"] for r in rows if not r["gapped"]]
    truths = [r["truth"] for r in rows if not r["gapped"]]
    qs_sorted = [q for _, q in sorted(zip(truths, qs))]       # ascending in d_s truth
    monotone = all(qs_sorted[i] >= qs_sorted[i + 1] - 0.2
                   for i in range(len(qs_sorted) - 1))
    print("-" * len(hdr))
    print(f"  monotone q* decreasing in d_s ... {'PASS' if monotone else 'FAIL'}")
    print(f"  CALIBRATION GATE ............... {'PASS' if (gate_ok and monotone) else 'FAIL'}")
    return gate_ok and monotone, rows


# --------------------------------------------------------------------------- #
# Phase 1  --  train, probe the learned manifold across the grok transition     #
# --------------------------------------------------------------------------- #
def train_and_probe(p, op, seed, args, device):
    import torch
    import torch.nn as nn
    from torch.utils.data import DataLoader
    from analog_modular_arithmetic import EmbeddingGrokMLP, EmbeddingModularDataset

    torch.manual_seed(seed)
    np.random.seed(seed)

    train_ds = EmbeddingModularDataset(p, op, args.train_fraction, "train", seed)
    test_ds = EmbeddingModularDataset(p, op, args.train_fraction, "test", seed)
    train_loader = DataLoader(train_ds, batch_size=args.batch, shuffle=True)
    test_loader = DataLoader(test_ds, batch_size=args.batch, shuffle=False)

    model = EmbeddingGrokMLP(vocab_size=p, embed_dim=args.embed_dim,
                             hidden_dim=args.hidden_dim, output_dim=p,
                             num_layers=args.layers).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=args.lr, weight_decay=args.wd)
    crit = nn.CrossEntropyLoss()

    # fixed sample of input pairs for the hidden-activation manifold (reused each probe)
    all_pairs = np.array([(a, b) for a in range(p) for b in range(p)])
    rng = np.random.default_rng(seed)
    sample = all_pairs[rng.choice(len(all_pairs), min(args.hidden_sample, len(all_pairs)),
                                  replace=False)]
    sa = torch.tensor(sample[:, 0], dtype=torch.long, device=device)
    sb = torch.tensor(sample[:, 1], dtype=torch.long, device=device)
    escort_qs = [1.0, 1.25, 1.5, 1.75, 2.0, 2.25, 2.5]

    def evaluate(loader):
        model.eval(); correct = total = 0
        with torch.no_grad():
            for a, b, y in loader:
                a, b, y = a.to(device), b.to(device), y.to(device)
                correct += (model(a, b).argmax(-1) == y).sum().item(); total += y.numel()
        return correct / max(1, total)

    def probe():
        model.eval()
        with torch.no_grad():
            emb = model.embed_a.weight.detach().cpu().numpy()
            _ = model(sa, sb)
            hid = model._hidden_activations.detach().cpu().numpy()
        m_emb = analyze_manifold(emb, mode=args.affinity, k=args.k, escort_qs=escort_qs)
        m_hid = analyze_manifold(hid, mode=args.affinity, k=args.k)
        return m_emb, m_hid

    history, grok_ep = [], -1
    print(f"\n[seed {seed}] p={p} op={op} lr={args.lr} wd={args.wd} "
          f"frac={args.train_fraction} affinity={args.affinity}")
    print(f"{'ep':>5} {'train':>6} {'test':>6} | "
          f"{'emb:d_s':>8}{'emb:q*':>7} | {'hid:d_s':>8}{'hid:q*':>7}")
    for ep in range(1, args.epochs + 1):
        model.train()
        for a, b, y in train_loader:
            a, b, y = a.to(device), b.to(device), y.to(device)
            opt.zero_grad(); loss = crit(model(a, b), y); loss.backward(); opt.step()

        if ep == 1 or ep % args.probe_interval == 0:
            tr, te = evaluate(train_loader), evaluate(test_loader)
            m_emb, m_hid = probe()
            history.append(dict(epoch=ep, train_acc=tr, test_acc=te, emb=m_emb, hid=m_hid))
            if grok_ep < 0 and te > 0.95:
                grok_ep = ep
            ed = "gap" if m_emb["gapped"] else f"{m_emb['ds_dos']:.2f}"
            hd = "gap" if m_hid["gapped"] else f"{m_hid['ds_dos']:.2f}"
            print(f"{ep:>5} {tr:>6.3f} {te:>6.3f} | "
                  f"{ed:>8}{m_emb['q_star']:>7.3f} | {hd:>8}{m_hid['q_star']:>7.3f}"
                  + ("   <-- GROK" if ep == grok_ep else ""))
        if grok_ep > 0 and ep > grok_ep + args.post_grok:
            break

    return dict(seed=seed, p=p, op=op, grok_epoch=grok_ep, history=history)


def summarize(run):
    h = run["history"]
    if not h:
        return
    grok = run["grok_epoch"]
    pre = next((m for m in reversed(h) if m["test_acc"] < 0.5), h[0])
    post = h[-1]
    grow = next((m for m in h if m["epoch"] == grok), post)
    print(f"\n  [seed {run['seed']}] grok@{grok}")
    for tag, m in [("pre-grok ", pre), ("at-grok  ", grow), ("final    ", post)]:
        for man in ("emb", "hid"):
            d = m[man]
            ds = "gap" if d["gapped"] else f"{d['ds_dos']:.2f}"
            print(f"    {tag} {man}: test={m['test_acc']:.3f}  d_s={ds:>5}  "
                  f"q*={d['q_star']:.3f}  1+2/d_s={d['q_pred']:.3f}")


# --------------------------------------------------------------------------- #
def main():
    ap = argparse.ArgumentParser(description="Path B representation-manifold Tsallis test")
    ap.add_argument("--calibrate-only", action="store_true")
    ap.add_argument("--affinity", choices=["knn", "gaussian"], default="knn")
    ap.add_argument("--k", type=int, default=12)
    ap.add_argument("--p", type=int, default=97)
    ap.add_argument("--op", type=str, default="add")
    ap.add_argument("--epochs", type=int, default=8000)
    ap.add_argument("--probe-interval", type=int, default=100)
    ap.add_argument("--post-grok", type=int, default=1200)
    ap.add_argument("--train-fraction", type=float, default=0.4)
    ap.add_argument("--lr", type=float, default=1e-3)
    ap.add_argument("--wd", type=float, default=1.0)
    ap.add_argument("--batch", type=int, default=512)
    ap.add_argument("--embed-dim", type=int, default=128)
    ap.add_argument("--hidden-dim", type=int, default=128)
    ap.add_argument("--layers", type=int, default=2)
    ap.add_argument("--hidden-sample", type=int, default=1024)
    ap.add_argument("--seeds", type=int, nargs="*", default=SEEDS)
    ap.add_argument("--out", type=str,
                    default="experiments/representation_manifold_results.json")
    args = ap.parse_args()

    t0 = time.time()
    gate_ok, calib = run_calibration(args.affinity, args.k)
    if args.calibrate_only:
        json.dump(dict(calibration=calib, gate=gate_ok),
                  open("experiments/representation_manifold_calibration.json", "w"),
                  indent=2, default=str)
        print(f"\n  elapsed {time.time() - t0:.1f}s  (calibration only)")
        return
    if not gate_ok:
        print("\n  ABORT: calibration gate FAILED -- fix affinity before trusting Phase 1.")
        return

    import torch
    device = "cuda" if torch.cuda.is_available() else "cpu"
    runs = [train_and_probe(args.p, args.op, s, args, device) for s in args.seeds]
    print("\n" + "=" * 72)
    print("PATH B SUMMARY  (decisions/0009)")
    print("=" * 72)
    for run in runs:
        summarize(run)
    json.dump(dict(calibration=calib, runs=runs), open(args.out, "w"),
              indent=2, default=str)
    print(f"\n  elapsed {time.time() - t0:.1f}s   results -> {args.out}")


if __name__ == "__main__":
    main()
