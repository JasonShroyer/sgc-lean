#!/usr/bin/env python3
"""
persistent_homology_grokking.py  --  Path B'' (follow-on to decisions/0009).

DEFINITIVE topological test of the grokked modular-addition representation via
persistent homology (Vietoris-Rips, ripser).  Resolves Artemis's three-way fork:

    H1 (b1=2, b2=1)  TRUE FLAT TORUS   T^2 = S^1 x S^1   (independent a,b periodicities)
    H2 (b1=1, b2=0)  FOURIER RIBBON    diagonal circle S^1  (only a+b survives)
    H3 (b1=0)        TOPOLOGICAL ILLUSION  contractible memorization blob

KEY DESIGN INSIGHT -- why we read the barcode of MULTIPLE LAYERS, not one cloud:
the functional-defect collapse (within-class variance -> 0) IS the statement that the
HIDDEN layer keeps only (a+b).  A function of a single periodic variable traces ONE
loop, so the hidden manifold is EXPECTED to be the (a+b) circle (b1=1) *by design* --
NOT a capacity-degenerated torus.  The genuine b1=2 torus, if it lives anywhere, is in
the INPUT EMBEDDINGS [e_a(a) (+) e_b(b)], which retain a and b independently (product of
two circles = torus, Kunneth).  So the answer to the fork is LAYER-DEPENDENT, and that
layer-dependence is the actual physics.  We therefore probe:
    (1) embed_a(a)            (97 pts)   prior: circle  b1=1
    (2) embed_b(b)            (97 pts)   prior: circle  b1=1
    (3) joint [e_a (+) e_b]   (grid)     prior: TORUS   b1=2, b2=1
    (4) hidden class-means    (97 pts)   prior: circle  b1=1   (the a+b loop)
    (5) hidden full cloud     (grid)     the d_corr~1.6-1.7 object; prior b1=1 + scatter

CALIBRATION-GATE-FIRST DISCIPLINE (the lesson of Path B / B'):
finite point clouds FAKE H1 loops.  PHASE 0 calibrates the ripser barcode reader on
KNOWN objects -- circle (b1=1), flat Clifford torus (b1=2,b2=1), 2-sphere (b1=0,b2=1),
Gaussian blob (b1=0).  It DERIVES persistence thresholds tau1*, tau2* from the b1=0 / b2=0
NULL clouds (the false-positive floor) that the b>=1 controls must clear.  Only a reader
that recovers ALL FOUR known Betti numbers is trusted on the neural manifold.  Every raw
top-persistence is PRINTED so the gap (signal vs noise) is auditable, not asserted.

Reuses representation_manifold_grokking cloud generators + analog_modular_arithmetic
EmbeddingGrokMLP/EmbeddingModularDataset (the identical wd=0.5 cloud Path B' calibrated).
"""

import argparse
import math
import os
import sys
import time

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

from representation_manifold_grokking import _circle, _torus, _gaussian   # noqa: E402

try:
    import gudhi
except ImportError:
    print("ERROR: gudhi not installed.  Run:  python -m pip install --no-deps gudhi")
    sys.exit(1)

# Shared reader settings -- calibration and neural readout MUST use identical values
# so the calibrated persistence thresholds tau1*/tau2* transfer across clouds.
# Vietoris-Rips cost is ~O(N^{k+1}); on HIGH-DIM blob clouds (concentration of measure
# -> near-complete graph) it explodes, so N MUST stay small.  Low-dim manifolds resolve
# fine at these sizes; H1 margins are large so N=250 is ample.
N_H1, NB_H1, MEL_H1 = 250, 8, 2.5      # H1 (triangles):  subsample, bootstraps, max edge length
N_H2, NB_H2, MEL_H2 = 100, 4, 2.8      # H2 (tetrahedra):  smaller N, fewer bootstraps
SPARSE, SPARSE_H2 = 0.3, 0.5            # gudhi sparse-Rips (1+eps); H2 sparser (costlier simplices)


# --------------------------------------------------------------------------- #
# Extra calibration cloud: 2-sphere S^2  (b0=1, b1=0, b2=1) -- the H1 null     #
# --------------------------------------------------------------------------- #
def _sphere(n, rng, dim=8, noise=0.01):
    v = rng.standard_normal((n, 3))
    v /= (np.linalg.norm(v, axis=1, keepdims=True) + 1e-12)
    pad = np.zeros((n, dim - 3))
    return np.concatenate([v, pad], 1) + noise * rng.standard_normal((n, dim))


# --------------------------------------------------------------------------- #
# Barcode reader                                                              #
# --------------------------------------------------------------------------- #
def _normalize(X):
    """Center + scale to unit RMS radius so a persistence threshold transfers
    across clouds of different raw scale (same convention as corr_logperiodic)."""
    X = np.asarray(X, dtype=float)
    X = X - X.mean(axis=0, keepdims=True)
    rms = math.sqrt(float((X ** 2).sum(axis=1).mean())) + 1e-12
    return X / rms


def _persistences(dgm):
    """Sorted (desc) finite bar lifetimes (death - birth) of one H_k diagram."""
    if dgm is None or len(dgm) == 0:
        return np.array([])
    pers = dgm[:, 1] - dgm[:, 0]
    pers = pers[np.isfinite(pers)]
    return np.sort(pers)[::-1]


def _diagram(X, maxdim, thresh, n_sub, seed):
    X = _normalize(X)
    if n_sub is not None and len(X) > n_sub:
        rng = np.random.default_rng(seed)
        X = X[rng.choice(len(X), n_sub, replace=False)]
    mel = float(thresh) if thresh is not None else (MEL_H1 if maxdim <= 1 else MEL_H2)
    sp = SPARSE if maxdim <= 1 else SPARSE_H2
    rc = gudhi.RipsComplex(points=np.ascontiguousarray(X, dtype=float),
                           max_edge_length=mel, sparse=sp)
    st = rc.create_simplex_tree(max_dimension=maxdim + 1)
    st.compute_persistence(homology_coeff_field=2)
    return [np.asarray(st.persistence_intervals_in_dimension(d)).reshape(-1, 2)
            for d in range(maxdim + 1)]


def analyze(X, maxdim=2, n_sub=None, n_boot=8, thresh=None, base_seed=0, topk=5):
    """Bootstrap-subsample the cloud and return, per homology dim, the per-bootstrap
    sorted persistence arrays plus the median of the top-k persistences (for printing)."""
    do_boot = n_sub is not None and len(X) > n_sub
    nb = n_boot if do_boot else 1
    per_dim = {d: [] for d in range(maxdim + 1)}
    for bsi in range(nb):
        dgms = _diagram(X, maxdim, thresh, n_sub if do_boot else None, base_seed + bsi)
        for d in range(maxdim + 1):
            per_dim[d].append(_persistences(dgms[d]))
    topmed = {}
    for d, lst in per_dim.items():
        rows = np.zeros((len(lst), topk))
        for i, p in enumerate(lst):
            rows[i, :min(topk, len(p))] = p[:topk]
        topmed[d] = np.median(rows, axis=0)
    return per_dim, topmed


def betti(per_dim_lst, tau):
    """Median count (and per-bootstrap counts) of bars with persistence > tau."""
    counts = [int((p > tau).sum()) for p in per_dim_lst]
    return int(np.median(counts)) if counts else 0, counts


def _fmt(v, k=5):
    return " ".join(f"{x:6.3f}" for x in v[:k])


# --------------------------------------------------------------------------- #
# Phase 0  --  calibrate the reader; derive tau1* (H1) and tau2* (H2)         #
# --------------------------------------------------------------------------- #
def run_calibration(n1=1200, n_sub1=N_H1, n_boot1=NB_H1,
                    n2=900, n_sub2=N_H2, n_boot2=NB_H2, margin1=1.5, margin2=2.0, seed=42):
    rng = np.random.default_rng(seed)
    # Calibrate at the NEURAL ambient dimension: concentration of measure in high-d can
    # suppress loop persistence, so an 8-d calibration could over-state the probe's power.
    # The FUZZY circle is the key false-negative control -- if the probe still recovers a
    # loop buried under substantial high-d noise, then a neural b1=0 is a genuine absence.
    D = 128
    clouds = [
        ("circle  R^128",      _circle(n1, rng, dim=D, noise=0.02),  1, 0),
        ("fuzzy circle R^128", _circle(n1, rng, dim=D, noise=0.06),  1, 0),
        ("flat torus R^128",   _torus(n1, rng, dim=D, noise=0.03),   2, 1),
        ("sphere  R^128",      _sphere(n1, rng, dim=D, noise=0.02),  0, 1),
        ("gaussian R^3->128",  _gaussian(n1, rng, 3, D),             0, 0),
    ]
    print("=" * 78)
    print(f"PHASE 0  PERSISTENT-HOMOLOGY READER CALIBRATION  "
          f"(H1: N={n_sub1}x{n_boot1} boots | H2: N={n_sub2}x{n_boot2} boots)")
    print("=" * 78)
    print("  clouds normalized to unit RMS radius; persistence = bar lifetime (death-birth)")
    print("  top-5 H1 / H2 persistences (median over bootstraps) -- gap = signal vs noise floor")
    print("-" * 78)
    print(f"{'cloud':<15}{'truth b1,b2':>12}   {'top-5 H1 persistences':<38}")
    rec = {}
    for name, X, tb1, tb2 in clouds:
        pdH1, tmH1 = analyze(X, maxdim=1, n_sub=n_sub1, n_boot=n_boot1, base_seed=seed)
        pdH2, tmH2 = analyze(X, maxdim=2, n_sub=n_sub2, n_boot=n_boot2, base_seed=seed)
        rec[name] = dict(tb1=tb1, tb2=tb2, H1=pdH1[1], H2=pdH2[2],
                         topH1=tmH1[1], topH2=tmH2[2])
        print(f"{name:<15}{f'{tb1},{tb2}':>12}   H1[{_fmt(tmH1[1])}]")
        print(f"{'':<15}{'':>12}   H2[{_fmt(tmH2[2])}]")
    print("-" * 78)

    # NULL floors: b1=0 clouds set the H1 false-positive floor; b2=0 clouds set H2 floor.
    null_h1 = [rec[n]["topH1"][0] for n in rec if rec[n]["tb1"] == 0]
    null_h2 = [rec[n]["topH2"][0] for n in rec if rec[n]["tb2"] == 0]
    tau1 = margin1 * max(null_h1) if null_h1 else float("inf")
    tau2 = margin2 * max(null_h2) if null_h2 else float("inf")
    print(f"  H1 null floor (max top-1 over b1=0 clouds) = {max(null_h1):.3f}"
          f"  ->  tau1* = {margin1}x = {tau1:.3f}")
    print(f"  H2 null floor (max top-1 over b2=0 clouds) = {max(null_h2):.3f}"
          f"  ->  tau2* = {margin2}x = {tau2:.3f}  (H2 noisier -> larger margin)")
    print("-" * 78)

    gate_ok = True
    print(f"{'cloud':<15}{'b1 (read/true)':>16}{'b2 (read/true)':>16}{'verdict':>10}")
    for name, X, tb1, tb2 in clouds:
        b1, _ = betti(rec[name]["H1"], tau1)
        b2, _ = betti(rec[name]["H2"], tau2)
        ok = (b1 == tb1) and (b2 == tb2)
        gate_ok &= ok
        print(f"{name:<15}{f'{b1}/{tb1}':>16}{f'{b2}/{tb2}':>16}{('OK' if ok else 'FAIL'):>10}")
    print("-" * 78)
    print(f"  READER CALIBRATED ... {'YES -- all 4 Betti numbers recovered' if gate_ok else 'NO -- DO NOT trust neural readout'}")
    print("=" * 78)
    return gate_ok, tau1, tau2


# --------------------------------------------------------------------------- #
# Phase 1  --  train wd=0.5 model, read the barcode of every layer            #
# --------------------------------------------------------------------------- #
def train_capture(seed=42, p=97, op="add", wd=0.5, lr=1e-3, frac=0.4, epochs=6000,
                  probe_interval=100, post_grok=600, embed_dim=128, hidden_dim=128,
                  layers=2, batch=512):
    import torch
    import torch.nn as nn
    from torch.utils.data import DataLoader
    sys.path.insert(0, os.path.join(_HERE, "..", "demos"))
    from analog_modular_arithmetic import EmbeddingGrokMLP, EmbeddingModularDataset

    device = "cuda" if torch.cuda.is_available() else "cpu"
    torch.manual_seed(seed); np.random.seed(seed)
    train_ds = EmbeddingModularDataset(p, op, frac, "train", seed)
    test_ds = EmbeddingModularDataset(p, op, frac, "test", seed)
    train_loader = DataLoader(train_ds, batch_size=batch, shuffle=True)
    test_loader = DataLoader(test_ds, batch_size=batch, shuffle=False)
    model = EmbeddingGrokMLP(vocab_size=p, embed_dim=embed_dim, hidden_dim=hidden_dim,
                             output_dim=p, num_layers=layers).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=wd)
    crit = nn.CrossEntropyLoss()
    allp = np.array([(a, b) for a in range(p) for b in range(p)])
    Aa = torch.tensor(allp[:, 0], dtype=torch.long, device=device)
    Bb = torch.tensor(allp[:, 1], dtype=torch.long, device=device)
    sums = (allp[:, 0] + allp[:, 1]) % p

    def evaluate(loader):
        model.eval(); c = t = 0
        with torch.no_grad():
            for a, b, y in loader:
                a, b, y = a.to(device), b.to(device), y.to(device)
                c += (model(a, b).argmax(-1) == y).sum().item(); t += y.numel()
        return c / max(1, t)

    def snapshot():
        model.eval()
        with torch.no_grad():
            _ = model(Aa, Bb)
            H = model._hidden_activations.detach().cpu().numpy()        # (p^2, hidden)
            ea = model.embed_a.weight.detach().cpu().numpy()            # (p, embed)
            eb = model.embed_b.weight.detach().cpu().numpy()            # (p, embed)
        cmean = np.stack([H[sums == s].mean(0) for s in range(p)])      # (p, hidden) by a+b
        ej = np.concatenate([ea[allp[:, 0]], eb[allp[:, 1]]], axis=1)   # (p^2, 2*embed) joint
        return dict(hidden_full=H, embed_a=ea, embed_b=eb,
                    hidden_classmean=cmean, embed_joint=ej)

    print(f"\n[TRAIN seed {seed}] p={p} op={op} wd={wd} lr={lr} frac={frac} "
          f"(full manifold N={len(allp)})", flush=True)
    print(f"{'ep':>5} {'train':>6} {'test':>6}   event", flush=True)
    grok_ep, caps = -1, {}
    for ep in range(1, epochs + 1):
        model.train()
        for a, b, y in train_loader:
            a, b, y = a.to(device), b.to(device), y.to(device)
            opt.zero_grad(); crit(model(a, b), y).backward(); opt.step()
        if ep == 1 or ep % probe_interval == 0:
            tr, te = evaluate(train_loader), evaluate(test_loader)
            tag = ""
            if "pre" not in caps and tr > 0.95 and te < 0.30:
                caps["pre"] = (ep, tr, te, snapshot()); tag = "<- PRE-grok (memorized)"
            if grok_ep < 0 and te > 0.95:
                grok_ep = ep; caps["at"] = (ep, tr, te, snapshot()); tag = "<- AT-grok"
            print(f"{ep:>5} {tr:>6.3f} {te:>6.3f}   {tag}", flush=True)
        if grok_ep > 0 and ep >= grok_ep + post_grok:
            caps["post"] = (ep, evaluate(train_loader), evaluate(test_loader), snapshot())
            print(f"{ep:>5} {caps['post'][1]:>6.3f} {caps['post'][2]:>6.3f}   <- POST-grok", flush=True)
            break
    return caps


def read_layer(name, X, tau1, tau2, prior, n_sub=None, n_boot=NB_H1):
    """Read b1,b2 of one neural cloud and print the auditable top persistences."""
    pdH1, tmH1 = analyze(X, maxdim=1, n_sub=n_sub, n_boot=n_boot)
    pdH2, tmH2 = analyze(X, maxdim=2, n_sub=(n_sub if n_sub is None else min(n_sub, N_H2)),
                         n_boot=max(2, n_boot // 2))
    b1, c1 = betti(pdH1[1], tau1)
    b2, c2 = betti(pdH2[2], tau2)
    print(f"  {name:<22} N={len(X):>5}  b1={b1} b2={b2}   (prior: {prior})", flush=True)
    print(f"  {'':<22} H1[{_fmt(tmH1[1])}]  (tau1*={tau1:.3f})", flush=True)
    print(f"  {'':<22} H2[{_fmt(tmH2[2])}]  (tau2*={tau2:.3f})", flush=True)
    return dict(name=name, b1=b1, b2=b2, c1=c1, c2=c2)


def _cache_dir(seed):
    return os.path.join(_HERE, "logs", "ph_grok", f"seed{seed}")


def _readout(snap, pre_at, tau1, tau2, seed, header):
    print(f"\n{'='*78}\n  BARCODE READOUT  seed={seed}  {header}\n{'='*78}", flush=True)
    print("  -- INPUT EMBEDDINGS (retain a,b independently; prior = two circles -> torus)", flush=True)
    read_layer("embed_a(a)",      snap["embed_a"],       tau1, tau2, "circle b1=1")
    read_layer("embed_b(b)",      snap["embed_b"],       tau1, tau2, "circle b1=1")
    read_layer("joint [ea(+)eb]", snap["embed_joint"],   tau1, tau2, "TORUS b1=2,b2=1", n_sub=N_H1)
    print("  -- HIDDEN MANIFOLD (functional collapse to a+b; prior = single circle)", flush=True)
    read_layer("hidden class-means",   snap["hidden_classmean"], tau1, tau2, "circle b1=1")
    read_layer("hidden full (d_corr)", snap["hidden_full"],      tau1, tau2, "b1=1 + scatter", n_sub=N_H1)
    for tag in ("pre", "at"):
        if tag in pre_at:
            pd, tm = analyze(pre_at[tag], maxdim=1, n_sub=N_H1, n_boot=6)
            b1, _ = betti(pd[1], tau1)
            print(f"  [emergence] hidden full @ {tag}-grok: b1={b1}  H1[{_fmt(tm[1])}]", flush=True)


def run_neural(tau1, tau2, seeds=(42,), wd=0.5):
    for s in seeds:
        caps = train_capture(seed=s, wd=wd)
        if "post" not in caps:
            print(f"  [seed {s}] never grokked -- skipping topology readout", flush=True)
            continue
        ep, tr, te, snap = caps["post"]
        outdir = _cache_dir(s)
        os.makedirs(outdir, exist_ok=True)
        for key, arr in snap.items():
            np.save(os.path.join(outdir, f"post_{key}.npy"), arr)
        pre_at = {}
        for tag in ("pre", "at"):
            if tag in caps:
                pre_at[tag] = caps[tag][3]["hidden_full"]
                np.save(os.path.join(outdir, f"{tag}_hidden_full.npy"), pre_at[tag])
        print(f"  [saved snapshots -> {outdir}]", flush=True)
        _readout(snap, pre_at, tau1, tau2, s, f"POST-grok ep{ep} (train={tr:.3f} test={te:.3f})")


def run_from_cache(tau1, tau2, seeds=(42,)):
    for s in seeds:
        outdir = _cache_dir(s)
        if not os.path.isdir(outdir):
            print(f"  [seed {s}] no cached snapshots at {outdir}", flush=True)
            continue
        snap = {f[5:-4]: np.load(os.path.join(outdir, f))
                for f in os.listdir(outdir) if f.startswith("post_")}
        pre_at = {tag: np.load(os.path.join(outdir, f"{tag}_hidden_full.npy"))
                  for tag in ("pre", "at")
                  if os.path.exists(os.path.join(outdir, f"{tag}_hidden_full.npy"))}
        _readout(snap, pre_at, tau1, tau2, s, "(cached snapshots)")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--calibrate-only", action="store_true")
    ap.add_argument("--neural", action="store_true")
    ap.add_argument("--from-cache", action="store_true", help="re-read saved snapshots, no training")
    ap.add_argument("--seeds", type=int, nargs="*", default=[42])
    ap.add_argument("--wd", type=float, default=0.5)
    ap.add_argument("--margin1", type=float, default=1.5)
    ap.add_argument("--margin2", type=float, default=2.0)
    args = ap.parse_args()
    t0 = time.time()
    gate_ok, tau1, tau2 = run_calibration(margin1=args.margin1, margin2=args.margin2)
    if not gate_ok:
        print("\n  >>> Reader NOT calibrated; aborting neural readout (honest gate stop).")
        return
    if args.from_cache:
        run_from_cache(tau1, tau2, seeds=tuple(args.seeds))
    elif args.neural and not args.calibrate_only:
        run_neural(tau1, tau2, seeds=tuple(args.seeds), wd=args.wd)
    print(f"\n  elapsed {time.time() - t0:.1f}s", flush=True)


if __name__ == "__main__":
    main()
