#!/usr/bin/env python3
"""
cantor_representation_probe.py  --  Path B' of decisions/0009.

Tests whether the grokked representation manifold is a DISCRETE-SCALE-INVARIANT
(Cantor / hierarchical) set rather than a smooth low-d manifold.  The signature is
log-periodic modulation of the heat-kernel return probability:

    P(t) = t^{-d_s/2} * Phi(ln t),    Phi periodic in ln t   (DSI fractal)
    P(t) = t^{-d_s/2}                  (smooth d_s-manifold: flat local slope)

so the LOCAL spectral dimension  d_s(t) = -2 d ln P / d ln t  is a flat plateau for a
smooth manifold and an OSCILLATING wave for a DSI fractal.

CRITICAL DISCIPLINE (the lesson of Path B's Phase-0 gate, applied recursively):
log-periodic oscillations are trivially faked by finite-size / noise.  So PHASE 0 here
CALIBRATES the oscillation probe on KNOWN objects -- it must light up on a Sierpinski
cloud (genuine DSI) and stay dark on circle / torus / Gaussian (smooth) BEFORE any
neural readout is trusted.  Three honest outcomes:
  (a) Sierpinski oscillates, smooth ones don't  -> probe has power -> proceed to neural.
  (b) nothing (incl. Sierpinski) oscillates      -> probe UNDERPOWERED at this N -> say so.
  (c) everything oscillates                       -> probe picks up noise -> NOT trustworthy.

Reuses the validated Path B machinery (affinity graph, return_prob, cloud generators).
"""

import argparse
import math
import os
import sys

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

from spectral_dimension_quench import return_prob                       # noqa: E402
from representation_manifold_grokking import (                          # noqa: E402
    affinity_laplacian, _circle, _torus, _sierpinski_cloud, _gaussian,
)

ZERO_TOL = 1e-9


# --------------------------------------------------------------------------- #
# Scale-resolved spectral dimension and log-periodicity detection             #
# --------------------------------------------------------------------------- #
def wide_window(eigs, n=160, pad_lo=0.5, pad_hi=2.0):
    """Power-law scaling window of a normalized Laplacian, slightly widened to expose
    several ln-t cycles.  Uniform in u = ln t (geomspace)."""
    nz = eigs[eigs > ZERO_TOL]
    if len(nz) < 16:
        return None
    lam2, lam_max = float(nz.min()), float(nz.max())
    t_lo, t_hi = pad_lo / lam_max, pad_hi / lam2
    if t_hi <= t_lo or math.log10(t_hi / t_lo) < 1.0:
        return None
    return np.geomspace(t_lo, t_hi, n)


def ds_of_t(eigs, window):
    """Local d_s(t) = -2 d ln P / d ln t via centered differences on the uniform
    u = ln t grid.  Returns (u_mid, ds_local)."""
    P = return_prob(eigs, window)
    u = np.log(window)
    lnP = np.log(np.maximum(P, 1e-300))
    ds = -2.0 * np.gradient(lnP, u)
    return u, ds


def corr_logperiodic(X, n_r=240, p_lo=0.3, p_hi=65.0):
    """Grassberger-Procaccia correlation-integral DSI probe -- the RIGHT instrument.

    C(r) = fraction of point pairs closer than r.  For a d-set C(r) ~ r^d, so
    d_corr(r) = d ln C / d ln r is the correlation dimension; r spans MANY decades
    (min pairwise distance -> diameter), giving many ln-r cycles -- enough to actually
    resolve the log-periodic modulation of a discrete-scale-invariant fractal
    (period_b = spatial scaling ratio; ~2 for Sierpinski's halving) from a smooth
    manifold's flat power law.  Returns None if the scaling band is too short."""
    X = np.asarray(X, dtype=float)
    X = X - X.mean(axis=0, keepdims=True)
    rms = math.sqrt(float((X ** 2).sum(axis=1).mean())) + 1e-12
    X = X / rms
    from scipy.spatial.distance import pdist
    d = np.sort(pdist(X))
    npairs = len(d)
    r_lo, r_hi = float(np.percentile(d, p_lo)), float(np.percentile(d, p_hi))
    if r_hi <= r_lo or math.log10(r_hi / r_lo) < 0.8:
        return None
    r = np.geomspace(r_lo, r_hi, n_r)
    C = np.searchsorted(d, r, side="right") / npairs
    good = C > 0
    r, C = r[good], C[good]
    if len(r) < 32:
        return None
    lnr, lnC = np.log(r), np.log(C)
    c1, c0 = np.polyfit(lnr, lnC, 1)                     # c1 = correlation dimension
    resid = lnC - (c1 * lnr + c0)
    resid_rms = float(np.sqrt(np.mean(resid ** 2)))
    du = float(lnr[1] - lnr[0])
    w = np.hanning(len(resid))
    rr = (resid - resid.mean()) * w
    spec = np.abs(np.fft.rfft(rr)) ** 2
    freqs = np.fft.rfftfreq(len(resid), d=du)
    lo = 2
    band = spec[lo:]
    kpk = int(np.argmax(band)) + lo
    f_pk = float(freqs[kpk])
    period_u = 1.0 / f_pk if f_pk > 0 else float("inf")
    total = float(spec[lo:].sum()) + 1e-30
    peak_frac = float(spec[kpk] / total)
    sig = float(spec[kpk] / (np.median(band) + 1e-30))     # peak SNR vs off-peak floor
    amp = 2.0 * math.sqrt(max(spec[kpk], 0.0)) / (0.5 * len(resid))
    span_u = float(lnr[-1] - lnr[0])
    return dict(d_corr=float(c1), resid_rms=resid_rms * 1e3, amp=amp * 1e3,
                period_b=math.exp(period_u) if math.isfinite(period_u) else float("nan"),
                peak_frac=peak_frac, sig=sig,
                n_cycles=span_u / period_u if period_u > 0 else 0.0,
                decades=span_u / math.log(10.0))


def detect_logperiodic(eigs, window):
    """Detrend ln P(u) by its best power law, then look for a single dominant
    log-periodic component via a Hann-windowed periodogram on the uniform u-grid.

    Returns dict with: ds_mean (window power-law slope), resid_rms (RMS of detrended
    ln P, x1e3), amp (peak oscillation amplitude in ln P units, x1e3), period_b
    (scaling ratio exp(period_u) of the dominant mode), peak_frac (peak power / total
    detrended power -- spectral concentration in [0,1]), n_cycles (decades*ln10/period_u)."""
    P = return_prob(eigs, window)
    u = np.log(window)
    lnP = np.log(np.maximum(P, 1e-300))
    # power-law detrend
    c1, c0 = np.polyfit(u, lnP, 1)
    resid = lnP - (c1 * u + c0)
    resid_rms = float(np.sqrt(np.mean(resid ** 2)))
    # Hann-windowed periodogram (uniform du); drop DC + first bin (residual trend)
    du = float(u[1] - u[0])
    w = np.hanning(len(resid))
    r = (resid - resid.mean()) * w
    spec = np.abs(np.fft.rfft(r)) ** 2
    freqs = np.fft.rfftfreq(len(resid), d=du)            # cycles per unit u
    lo = 2                                               # skip DC and slowest bin
    if len(spec) <= lo + 1:
        return dict(ds_mean=-2.0 * c1, resid_rms=resid_rms * 1e3, amp=0.0,
                    period_b=float("nan"), peak_frac=0.0, n_cycles=0.0)
    band = spec[lo:]
    kpk = int(np.argmax(band)) + lo
    f_pk = float(freqs[kpk])
    period_u = 1.0 / f_pk if f_pk > 0 else float("inf")
    total = float(spec[lo:].sum()) + 1e-30
    peak_frac = float(spec[kpk] / total)
    # amplitude of a cosine with this periodogram power (Hann coherent gain ~0.5)
    amp = 2.0 * math.sqrt(max(spec[kpk], 0.0)) / (0.5 * len(resid))
    span_u = float(u[-1] - u[0])
    return dict(ds_mean=-2.0 * c1, resid_rms=resid_rms * 1e3, amp=amp * 1e3,
                period_b=math.exp(period_u) if math.isfinite(period_u) else float("nan"),
                peak_frac=peak_frac, n_cycles=span_u / period_u if period_u > 0 else 0.0)


# --------------------------------------------------------------------------- #
# Phase 0  --  calibrate the oscillation probe on KNOWN smooth vs DSI clouds   #
# --------------------------------------------------------------------------- #
def run_calibration(n=1500, k=12, seeds=(42, 43, 44)):
    clouds = [
        ("circle (smooth d=1)", _circle, 1.000, False),
        ("2-torus (smooth d=2)", _torus, 2.000, False),
        ("Gaussian R^3 (smooth)", lambda nn, rng: _gaussian(nn, rng, 3), 3.000, False),
        ("Sierpinski (DSI frac)", _sierpinski_cloud, math.log(3) / math.log(2), True),
    ]
    hdr = (f"{'cloud':<24}{'d_s(t)mean':>11}{'resid_rms':>11}{'osc_amp':>9}"
           f"{'period_b':>10}{'peak_frac':>11}{'cycles':>8}")
    print("=" * len(hdr))
    print(f"PHASE 0  LOG-PERIODICITY PROBE CALIBRATION  (N={n}, k={k}, seeds={list(seeds)})")
    print("=" * len(hdr))
    print("  resid_rms, osc_amp in 1e-3 ln-P units; DSI fractal should show HIGH amp &")
    print("  peak_frac vs smooth manifolds.  GATE: Sierpinski separates from all smooth.")
    print("-" * len(hdr))
    print(hdr)
    print("-" * len(hdr))
    stats = {}
    for name, gen, truth, is_frac in clouds:
        rows = []
        for s in seeds:
            rng = np.random.default_rng(s)
            X = gen(n, rng)
            eigs, _A, _deg = affinity_laplacian(X, mode="knn", k=k)
            window = wide_window(eigs)
            if window is None:
                continue
            rows.append(detect_logperiodic(eigs, window))
        if not rows:
            print(f"{name:<24}{'gapped/insufficient window':>50}")
            continue
        agg = {key: float(np.mean([r[key] for r in rows])) for key in rows[0]}
        stats[name] = (agg, is_frac)
        print(f"{name:<24}{agg['ds_mean']:>11.3f}{agg['resid_rms']:>11.2f}"
              f"{agg['amp']:>9.2f}{agg['period_b']:>10.3f}{agg['peak_frac']:>11.3f}"
              f"{agg['n_cycles']:>8.2f}")
    print("-" * len(hdr))
    # GATE: the fractal's oscillation amplitude AND spectral concentration must exceed
    # the worst (largest) smooth-manifold baseline by a clear margin.
    smooth_amp = [a['amp'] for (a, f) in stats.values() if not f]
    smooth_pk = [a['peak_frac'] for (a, f) in stats.values() if not f]
    frac = [(a, nm) for nm, (a, f) in stats.items() if f]
    if smooth_amp and frac:
        fa = frac[0][0]
        amp_ratio = fa['amp'] / (max(smooth_amp) + 1e-9)
        pk_ratio = fa['peak_frac'] / (max(smooth_pk) + 1e-9)
        has_power = (amp_ratio >= 1.8 and pk_ratio >= 1.3)
        print(f"  fractal/smooth  osc_amp ratio = {amp_ratio:.2f}   "
              f"peak_frac ratio = {pk_ratio:.2f}")
        print(f"  PROBE HAS DISCRIMINATING POWER ... {'YES' if has_power else 'NO -- underpowered/noisy'}")
        return has_power, stats
    print("  PROBE CALIBRATION INCONCLUSIVE (missing fractal or smooth baseline)")
    return False, stats


def run_corr_calibration(n=4000, seeds=(42, 43, 44, 45, 46, 47)):
    """Primary gate: the correlation-integral DSI probe on KNOWN smooth vs fractal clouds.
    Answer-agnostic DSI discriminator = a STABLE scaling ratio across independent samples
    (a true fractal has a fixed period_b; noise gives scattered period_b) plus a clear
    spectral peak (sig) and excess amplitude over the smooth baselines."""
    clouds = [
        ("circle (smooth d=1)", _circle, 1.000, False),
        ("2-torus (smooth d=2)", _torus, 2.000, False),
        ("Gaussian R^3 (smooth)", lambda nn, rng: _gaussian(nn, rng, 3), 3.000, False),
        ("Sierpinski (DSI frac)", _sierpinski_cloud, math.log(3) / math.log(2), True),
    ]
    hdr = (f"{'cloud':<24}{'d_corr':>9}{'decades':>9}{'cycles':>8}{'osc_amp':>9}"
           f"{'sig':>7}{'period_b':>14}")
    print("\n" + "=" * len(hdr))
    print(f"PHASE 0b  CORRELATION-INTEGRAL DSI PROBE  (Grassberger-Procaccia, N={n})")
    print("=" * len(hdr))
    print("  DSI fractal (Sierpinski) should show HIGH osc_amp/peak_frac with MANY cycles")
    print("  and period_b ~ 2 (halving); smooth manifolds -> flat (low amp). ")
    print("-" * len(hdr))
    print(hdr)
    print("-" * len(hdr))
    stats = {}
    for name, gen, truth, is_frac in clouds:
        rows = []
        for s in seeds:
            rng = np.random.default_rng(s)
            r = corr_logperiodic(gen(n, rng))
            if r is not None:
                rows.append(r)
        if not rows:
            print(f"{name:<24}{'insufficient scaling band':>50}")
            continue
        agg = {key: float(np.mean([r[key] for r in rows])) for key in rows[0]}
        pb = [r['period_b'] for r in rows if math.isfinite(r['period_b'])]
        agg['period_b_std'] = float(np.std(pb)) if pb else float('nan')
        agg['period_b_cv'] = (agg['period_b_std'] / agg['period_b']
                              if agg.get('period_b', 0) else float('nan'))
        stats[name] = (agg, is_frac)
        print(f"{name:<24}{agg['d_corr']:>9.3f}{agg['decades']:>9.2f}{agg['n_cycles']:>8.2f}"
              f"{agg['amp']:>9.2f}{agg['sig']:>7.1f}"
              f"{agg['period_b']:>9.2f}+-{agg['period_b_std']:<4.2f}")
    print("-" * len(hdr))
    smooth_sig = [a['sig'] for (a, f) in stats.values() if not f]
    smooth_cyc = [a['n_cycles'] for (a, f) in stats.values() if not f]
    frac = [a for nm, (a, f) in stats.items() if f]
    if smooth_sig and frac:
        fa = frac[0]
        # The ONE robust discriminator (the others fail: smooth curvature can have large
        # amplitude AND a sharp 'sig' peak): WHERE the dominant log-periodogram peak sits.
        # A DSI fractal has a real short-log-period harmonic (peak well ABOVE the 2-cycle
        # whole-window curvature floor); every smooth manifold pins AT that ~2-cycle floor.
        frac_above_floor = fa['n_cycles'] >= 3.5
        smooth_at_floor = all(c < 3.0 for c in smooth_cyc)
        has_power = (frac_above_floor and smooth_at_floor and 1.6 <= fa['period_b'] <= 2.6)
        print(f"  fractal peak @ {fa['n_cycles']:.1f} cycles (period_b={fa['period_b']:.2f}); "
              f"smooth peaks @ {min(smooth_cyc):.1f}-{max(smooth_cyc):.1f} cycles "
              f"(curvature floor: {'yes' if smooth_at_floor else 'NO'})")
        print(f"  PROBE HAS DISCRIMINATING POWER ... {'YES' if has_power else 'NO -- underpowered/noisy'}")
        return has_power, stats
    print("  CALIBRATION INCONCLUSIVE")
    return False, stats


def dsi_verdict(r):
    """Classify a corr_logperiodic result against the calibrated discriminator."""
    if r is None:
        return "no scaling band (gapped/degenerate)"
    above = r['n_cycles'] >= 3.5
    band = 1.6 <= r['period_b'] <= 6.0
    if above and band:
        return (f"DSI-LIKE: peak @ {r['n_cycles']:.1f} cyc, period_b={r['period_b']:.2f} "
                f"(ABOVE curvature floor)")
    return (f"smooth-like: peak @ {r['n_cycles']:.1f} cyc "
            f"(at ~2-cycle curvature floor -> NOT discrete-scale-invariant)")


def run_neural(seed=42, p=97, op="add", wd=0.5, lr=1e-3, frac=0.4, epochs=6000,
               probe_interval=100, post_grok=600, embed_dim=128, hidden_dim=128,
               layers=2, batch=512):
    """Train one seed at LOWER weight decay (avoids post-grok over-compression) and run
    the CALIBRATED correlation-integral DSI probe on the FULL p^2-point hidden manifold at
    pre-grok / at-grok / well-post-grok.  Answers: is the grokked manifold a smooth low-d
    set or a discrete-scale-invariant (Cantor-like) one?"""
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

    def evaluate(loader):
        model.eval(); c = t = 0
        with torch.no_grad():
            for a, b, y in loader:
                a, b, y = a.to(device), b.to(device), y.to(device)
                c += (model(a, b).argmax(-1) == y).sum().item(); t += y.numel()
        return c / max(1, t)

    def hidden_full():
        model.eval()
        with torch.no_grad():
            _ = model(Aa, Bb)
            return model._hidden_activations.detach().cpu().numpy()

    print(f"\n[NEURAL seed {seed}] p={p} op={op} wd={wd} lr={lr} frac={frac} "
          f"(full manifold N={len(allp)})")
    print(f"{'ep':>5} {'train':>6} {'test':>6}   event")
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
                caps["pre"] = (ep, tr, te, hidden_full()); tag = "<- captured PRE-grok (memorized)"
            if grok_ep < 0 and te > 0.95:
                grok_ep = ep; caps["at"] = (ep, tr, te, hidden_full()); tag = "<- captured AT-grok"
            print(f"{ep:>5} {tr:>6.3f} {te:>6.3f}   {tag}")
        if grok_ep > 0 and ep >= grok_ep + post_grok:
            caps["post"] = (ep, evaluate(train_loader), evaluate(test_loader), hidden_full())
            print(f"{ep:>5} {caps['post'][1]:>6.3f} {caps['post'][2]:>6.3f}   <- captured POST-grok")
            break

    print(f"\n  DSI PROBE on the learned hidden manifold (calibrated: Sierpinski->DSI, "
          f"smooth->floor):")
    for tag in ("pre", "at", "post"):
        if tag not in caps:
            continue
        ep, tr, te, H = caps[tag]
        r = corr_logperiodic(H)
        dc = f"d_corr={r['d_corr']:.2f}" if r else "d_corr=NA"
        print(f"    {tag:<4} ep{ep:<5} test={te:.3f}  {dc:<14}  {dsi_verdict(r)}")
    return caps


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=1500)
    ap.add_argument("--n-corr", type=int, default=5000)
    ap.add_argument("--k", type=int, default=12)
    ap.add_argument("--calibrate-only", action="store_true")
    ap.add_argument("--neural", action="store_true", help="run the neural DSI phase")
    ap.add_argument("--seeds", type=int, nargs="*", default=[42, 43])
    ap.add_argument("--wd", type=float, default=0.5)
    args = ap.parse_args()
    import time
    t0 = time.time()
    hk_power, _ = run_calibration(n=args.n, k=args.k)
    corr_power, _ = run_corr_calibration(n=args.n_corr)
    print(f"\n  PROBE VERDICT:")
    print(f"    heat-kernel d_s(t) log-periodicity ... {'usable' if hk_power else 'UNDERPOWERED'}")
    print(f"    correlation-integral DSI           ... {'usable' if corr_power else 'UNDERPOWERED'}")
    if not corr_power:
        print("\n  >>> The DSI probe is NOT calibrated-usable at this N; aborting neural phase.")
        print("  >>> The Cantor/DSI hypothesis is not testable this way -- honest negative.")
        return
    if args.neural:
        for s in args.seeds:
            run_neural(seed=s, wd=args.wd)
    print(f"\n  elapsed {time.time() - t0:.1f}s")


if __name__ == "__main__":
    main()
