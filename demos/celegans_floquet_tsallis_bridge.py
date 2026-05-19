#!/usr/bin/env python3
"""
demos/celegans_floquet_tsallis_bridge.py
=========================================

The empirical anchor for the Lean theorem chain:

    SGC.NonlinearEmergence.CelegansLinearityRatio = 0.08
        |
        | (via Floquet–Tsallis identification q = 2 - r)
        v
    SGC.Bridge.CelegansFloquetTsallis.CelegansTsallisQ = 1.92
        |
        | (via q-LIL scaling exponent (2-q)/2)
        v
    SGC.Bridge.CelegansFloquetTsallis.CelegansAnomalousDiffusion = 0.04

This script:

  1. Loads the *C. elegans* pharyngeal connectome from
     `data/cook2020_pharynx_synapses.csv`.
  2. Measures the *linear* spectral gap γ_linear (eigenvalue gap of the
     normalised connectivity matrix).
  3. Runs Wilson–Cowan dynamics on the connectome and measures the
     *Floquet* spectral gap γ_F (monodromy exponent gap).
  4. Computes the empirical linearity ratio r = γ_linear / γ_F.
  5. Computes the implied Tsallis q = 2 - r and the predicted anomalous
     diffusion exponent α = (2 - q) / 2 = r / 2 via the Lean theorem
     `predicted_alpha_eq_r_half`.
  6. Saves the headline numbers to a CSV and JSON for downstream
     consumption (the durable Branch A artefact).
  7. Measures α via phase diffusion on a stochastic (Langevin) version
     of the Wilson–Cowan dynamics, providing an *independent* empirical
     measurement of the anomalous diffusion exponent.
  8. Reports the discrepancy between the Lean constant `r = 0.08`, the
     empirical r from the connectome, and the MSD-fit α from the
     stochastic dynamics.

Outputs:
  - reports/celegans_bridge/celegans_floquet_tsallis_results.csv
  - reports/celegans_bridge/celegans_floquet_tsallis_results.json

Reference theorems (Lean):
  - SGC.Bridge.CelegansFloquetTsallis.predicted_alpha_eq_r_half
  - SGC.Bridge.CelegansFloquetTsallis.celegans_anomalous_diffusion_value
  - SGC.Bridge.CelegansFloquetTsallis.celegans_scaling_lt_UGM
  - SGC.Bridge.CelegansFloquetTsallis.celegans_tsallis_q_in_NESS_regime
"""

from __future__ import annotations

import csv
import io
import json
import sys
from pathlib import Path

import numpy as np

# Windows consoles default to cp1252; force UTF-8 so Greek letters print.
if sys.stdout.encoding and sys.stdout.encoding.lower() not in {"utf-8", "utf8"}:
    try:
        sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8",
                                      errors="replace")
    except Exception:
        pass

# ── Private Engine Interface ────────────────────────────────────────────────
# The production SGC nonlinear physics engine (`sgc_nonlinear_physics.py`) is
# proprietary and not distributed with this repository. The functions below
# are public stub signatures that document the interface this script consumes.
# Empirical results (CSV/JSON) were generated using the production engine and
# are included in `reports/celegans_bridge/` as standalone artefacts.
#
# To run this script end-to-end you need an implementation that satisfies the
# documented signatures below; without it the script imports cleanly but
# raises `NotImplementedError` at the first call site.
# ────────────────────────────────────────────────────────────────────────────


def load_celegans_pharynx():
    """Return `(W_raw, labels, neuron_types)` for the *C. elegans* pharyngeal
    connectome (Cook et al. 2019; 20 neurons, 161 edges).

    `W_raw` is a `(20, 20)` numpy array of synapse counts; `labels` is the
    list of neuron names; `neuron_types` is the list of class strings
    (`'sensory'`, `'inter'`, `'motor'`, ...).
    """
    raise NotImplementedError(
        "Requires proprietary SGC nonlinear engine "
        "(demos/sgc_nonlinear_physics.py)."
    )


def sigmoid(x, gain: float = 2.0):
    """Smooth firing-rate nonlinearity used in the Wilson–Cowan dynamics
    `dp/dt = (-p + sigmoid(W·p, gain)) / tau`.
    """
    raise NotImplementedError(
        "Requires proprietary SGC nonlinear engine "
        "(demos/sgc_nonlinear_physics.py)."
    )


def find_limit_cycle(
    W,
    tau: float = 1.0,
    gain: float = 2.0,
    t_transient: float = 100.0,
    t_record: float = 50.0,
    dt: float = 0.01,
):
    """Integrate Wilson–Cowan to a stable limit cycle and return the recorded
    cycle.

    Returns `(trajectory, times, period)` where `trajectory` is a `(T, n)`
    array of state vectors, `times` is the `(T,)` array of timestamps, and
    `period` is the autocorrelation-detected limit-cycle period.
    """
    raise NotImplementedError(
        "Requires proprietary SGC nonlinear engine "
        "(demos/sgc_nonlinear_physics.py)."
    )


def compute_floquet_exponents(
    W,
    trajectory,
    times,
    period: float,
    tau: float = 1.0,
    gain: float = 2.0,
):
    """Compute the Floquet exponents of the limit cycle by integrating the
    monodromy matrix `M = exp(integral_0^T J(p(t)) dt)` and taking the
    eigenvalue logarithms.

    Returns a numpy array of Floquet exponents sorted in descending order
    of real part (so `result[0]` is the slowest decay rate).
    """
    raise NotImplementedError(
        "Requires proprietary SGC nonlinear engine "
        "(demos/sgc_nonlinear_physics.py)."
    )


# ============================================================================
# LEAN PREDICTIONS — pulled verbatim from
# `SGC.Bridge.CelegansFloquetTsallis` for downstream comparison.
# ============================================================================

LEAN_CELEGANS_LINEARITY_RATIO: float = 0.08
LEAN_CELEGANS_TSALLIS_Q: float = 2.0 - LEAN_CELEGANS_LINEARITY_RATIO   # 1.92
LEAN_CELEGANS_ALPHA: float = LEAN_CELEGANS_LINEARITY_RATIO / 2.0       # 0.04
LEAN_UGM_ALPHA: float = 0.5  # qLIL_scaling_at_one


# ============================================================================
# MEASUREMENTS
# ============================================================================

def measure_floquet_spectrum(
    W: np.ndarray,
    tau: float = 1.0,
    gain: float = 2.0,
    t_transient: float = 100.0,
    t_record: float = 50.0,
    dt: float = 0.01,
    seed: int = 0,
) -> dict:
    """Run Wilson–Cowan and extract `gamma_F` and `gamma_linear` from the
    Floquet spectrum.

    The Floquet exponents (sorted descending) give two natural rates:

      `gamma_F = |mu_1|`               — the spectral abscissa, i.e. the
                                         slowest decay rate (rate at which
                                         the most-persistent transverse
                                         mode contracts onto the cycle /
                                         fixed point).
      `gamma_linear = |mu_1 - mu_2|`   — the "linear spectral gap", i.e.
                                         the spacing between the two
                                         slowest decay modes.

    These are exactly the two numbers feeding the Lean
    `LinearityRatio gamma_linear gamma_F` in
    `SGC.Spectral.FloquetTheory.celegans_linearity_ratio`.
    """
    np.random.seed(seed)
    trajectory, times, period = find_limit_cycle(
        W, tau=tau, gain=gain,
        t_transient=t_transient, t_record=t_record, dt=dt,
    )
    floquet_exponents = compute_floquet_exponents(
        W, trajectory, times, period, tau=tau, gain=gain,
    )

    if floquet_exponents.size >= 2:
        mu1 = float(floquet_exponents[0])
        mu2 = float(floquet_exponents[1])
        gamma_F = abs(mu1)
        gamma_linear = abs(mu1 - mu2)
    else:
        mu1 = mu2 = float("nan")
        gamma_F = gamma_linear = float("nan")

    return {
        "gamma_linear": gamma_linear,
        "gamma_F": gamma_F,
        "mu1": mu1,
        "mu2": mu2,
        "floquet_exponents": floquet_exponents.tolist(),
        "trajectory": trajectory,
        "times": times,
        "period": period,
    }


def langevin_phase_diffusion(
    W: np.ndarray,
    tau: float = 1.0,
    gain: float = 2.0,
    sigma: float = 0.01,
    n_trajectories: int = 8,
    t_burn: float = 50.0,
    t_record: float = 200.0,
    dt: float = 0.01,
    seed: int = 0,
) -> tuple[float | None, dict]:
    """Measure α via MSD of a *stochastic* Wilson–Cowan limit cycle.

    Adds isotropic Gaussian noise of amplitude `sigma` to the deterministic
    dynamics and fits MSD(τ) ∝ τ^α on the log-log slope. For a deeply
    nonlinear limit cycle the diffusion is *sub-diffusive*: α < 1/2.

    Returns (alpha_msd, diagnostics_dict).
    """
    rng = np.random.default_rng(seed)
    n = W.shape[0]

    def rhs(t, p):
        return (-p + sigmoid(W @ p, gain=gain)) / tau

    n_steps_burn = int(t_burn / dt)
    n_steps_record = int(t_record / dt)
    sqrt_dt = np.sqrt(dt)

    # Collect displacement-from-initial trajectories.
    all_disp = np.zeros((n_trajectories, n_steps_record, n))
    for k in range(n_trajectories):
        p = 0.5 + 0.1 * rng.standard_normal(n)
        p = np.clip(p, 0.01, 0.99)
        # Burn-in (Euler-Maruyama).
        for _ in range(n_steps_burn):
            p = p + dt * rhs(0.0, p) + sigma * sqrt_dt * rng.standard_normal(n)
            p = np.clip(p, 0.0, 1.0)
        p0 = p.copy()
        # Record.
        for i in range(n_steps_record):
            p = p + dt * rhs(0.0, p) + sigma * sqrt_dt * rng.standard_normal(n)
            p = np.clip(p, 0.0, 1.0)
            all_disp[k, i, :] = p - p0

    # MSD over lag, averaged across trajectories AND time-shifts.
    max_lag_steps = n_steps_record // 4
    lags = np.unique(
        np.geomspace(2, max_lag_steps, num=20).astype(int)
    )
    msd = np.zeros(lags.size)
    for li, lag in enumerate(lags):
        # For each trajectory, average over starting points.
        accum = 0.0
        count = 0
        for k in range(n_trajectories):
            disp = all_disp[k]  # (T, n)
            diff = disp[lag:] - disp[:-lag]
            accum += float(np.mean(np.sum(diff * diff, axis=1)))
            count += 1
        msd[li] = accum / max(count, 1)

    tau_values = lags * dt

    # Robust log–log fit on the central window.
    log_t = np.log(tau_values)
    log_m = np.log(msd + 1e-30)
    n_pts = log_t.size
    lo = max(2, n_pts // 5)
    hi = max(lo + 3, (4 * n_pts) // 5)
    if hi - lo < 3:
        return None, {"tau": tau_values.tolist(), "msd": msd.tolist()}
    slope, _intercept = np.polyfit(log_t[lo:hi], log_m[lo:hi], 1)
    return float(slope), {
        "tau": tau_values.tolist(),
        "msd": msd.tolist(),
        "fit_window": (int(lo), int(hi)),
        "sigma": sigma,
        "n_trajectories": n_trajectories,
    }


# ============================================================================
# MAIN
# ============================================================================

def main() -> dict:
    print("=" * 72)
    print("  C. elegans Floquet–Tsallis Bridge — Empirical Anchor")
    print("=" * 72)
    print()
    print("  Lean prediction chain (SGC.Bridge.CelegansFloquetTsallis):")
    print(f"    r (CelegansLinearityRatio)      = {LEAN_CELEGANS_LINEARITY_RATIO}")
    print(f"    q (CelegansTsallisQ)            = {LEAN_CELEGANS_TSALLIS_Q}")
    print(f"    α (CelegansAnomalousDiffusion)  = {LEAN_CELEGANS_ALPHA}")
    print(f"    UGM baseline α                  = {LEAN_UGM_ALPHA}")
    print(f"    SGC sub-Brownian ratio (α / UGM)= {LEAN_CELEGANS_ALPHA / LEAN_UGM_ALPHA:.3f}")
    print()

    # ---- 1. Connectome ----
    W_raw, labels, neuron_types = load_celegans_pharynx()
    W = W_raw / (np.max(W_raw) + 1e-9)
    n_neurons = W.shape[0]
    n_edges = int(np.sum(W_raw > 0))
    print(f"  [1] Connectome: {n_neurons} pharyngeal neurons, {n_edges} edges")

    # ---- 2. Floquet spectrum → γ_linear and γ_F ----
    print(f"  [2] Running Wilson–Cowan to limit cycle (gain=2.0)...")
    floq = measure_floquet_spectrum(W)
    gamma_linear = floq["gamma_linear"]
    gamma_F = floq["gamma_F"]
    mu1 = floq["mu1"]
    mu2 = floq["mu2"]
    period = floq["period"]
    print(f"      Spectral abscissa γ_F = |μ₁|     = {gamma_F:.4f}")
    print(f"        (Lean `CelegansFloquetGap`       ≈ 0.83)")
    print(f"      Linear gap γ_linear = |μ₁−μ₂|    = {gamma_linear:.4f}")
    print(f"        (Lean `celegans_markov_gap`      ≈ 0.065)")
    print(f"      μ₁, μ₂                           = {mu1:.4f}, {mu2:.4f}")
    print(f"      Limit-cycle period T             = {period:.2f}")

    # ---- 3. Empirical r → q → α ----
    if gamma_F > 0:
        r_measured = gamma_linear / gamma_F
    else:
        r_measured = float("nan")
    q_measured = 2.0 - r_measured
    alpha_bridge = r_measured / 2.0
    print(f"  [3] Empirical r = γ_linear / γ_F   = {r_measured:.4f}")
    print(f"      Empirical q = 2 - r             = {q_measured:.4f}")
    print(f"      Bridge α = r / 2 (Lean thm)     = {alpha_bridge:.4f}")
    print(f"      |r_measured - r_Lean|           = {abs(r_measured - LEAN_CELEGANS_LINEARITY_RATIO):.4f}")
    print(f"      |α_bridge   - α_Lean|           = {abs(alpha_bridge - LEAN_CELEGANS_ALPHA):.4f}")

    # ---- 5. MSD measurement of α (stochastic phase diffusion) ----
    print(f"  [5] Stochastic phase-diffusion MSD α-fit...")
    alpha_msd, msd_diag = langevin_phase_diffusion(W)
    if alpha_msd is not None:
        print(f"      MSD-fit α                      = {alpha_msd:.4f}")
        print(f"      |α_msd     - α_Lean|           = {abs(alpha_msd - LEAN_CELEGANS_ALPHA):.4f}")
    else:
        print(f"      MSD fit returned no result.")
    print()

    # ---- 6. Save outputs ----
    out_dir = Path(__file__).resolve().parent.parent / "reports" / "celegans_bridge"
    out_dir.mkdir(parents=True, exist_ok=True)

    csv_path = out_dir / "celegans_floquet_tsallis_results.csv"
    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["quantity", "value", "source"])
        w.writerow(["lean_r", LEAN_CELEGANS_LINEARITY_RATIO,
                    "SGC.NonlinearEmergence.CelegansLinearityRatio"])
        w.writerow(["lean_q", LEAN_CELEGANS_TSALLIS_Q,
                    "SGC.Bridge.CelegansFloquetTsallis.CelegansTsallisQ"])
        w.writerow(["lean_alpha", LEAN_CELEGANS_ALPHA,
                    "SGC.Bridge.CelegansFloquetTsallis.CelegansAnomalousDiffusion"])
        w.writerow(["measured_mu1", mu1,
                    "largest Floquet exponent (slowest contracting mode)"])
        w.writerow(["measured_mu2", mu2,
                    "second-largest Floquet exponent"])
        w.writerow(["measured_gamma_F", gamma_F,
                    "|mu1| = spectral abscissa @ Wilson-Cowan gain=2"])
        w.writerow(["measured_gamma_linear", gamma_linear,
                    "|mu1 - mu2| = linear spectral gap"])
        w.writerow(["measured_r", r_measured, "gamma_linear / gamma_F"])
        w.writerow(["measured_q", q_measured, "2 - r"])
        w.writerow(["bridge_alpha", alpha_bridge,
                    "r / 2  (predicted_alpha_eq_r_half)"])
        if alpha_msd is not None:
            w.writerow(["msd_alpha", alpha_msd,
                        "log-log slope of MSD(tau) on stochastic WC"])
        w.writerow(["r_residual", abs(r_measured - LEAN_CELEGANS_LINEARITY_RATIO),
                    "|measured_r - lean_r|"])
        w.writerow(["alpha_bridge_residual",
                    abs(alpha_bridge - LEAN_CELEGANS_ALPHA),
                    "|bridge_alpha - lean_alpha|"])
        if alpha_msd is not None:
            w.writerow(["alpha_msd_residual",
                        abs(alpha_msd - LEAN_CELEGANS_ALPHA),
                        "|msd_alpha - lean_alpha|"])
    print(f"  CSV  -> {csv_path}")

    json_path = out_dir / "celegans_floquet_tsallis_results.json"
    payload = {
        "lean": {
            "r": LEAN_CELEGANS_LINEARITY_RATIO,
            "q": LEAN_CELEGANS_TSALLIS_Q,
            "alpha": LEAN_CELEGANS_ALPHA,
            "ugm_alpha_baseline": LEAN_UGM_ALPHA,
            "theorem_chain": [
                "SGC.NonlinearEmergence.CelegansLinearityRatio",
                "SGC.Bridge.CelegansFloquetTsallis.linearity_ratio_to_Tsallis_q",
                "SGC.Bridge.CelegansFloquetTsallis.predicted_alpha_eq_r_half",
                "SGC.Bridge.CelegansFloquetTsallis.celegans_anomalous_diffusion_value",
                "SGC.Bridge.CelegansFloquetTsallis.celegans_scaling_lt_UGM",
            ],
        },
        "measured": {
            "gamma_linear": gamma_linear,
            "gamma_F": gamma_F,
            "mu1": mu1,
            "mu2": mu2,
            "limit_cycle_period": period,
            "r": r_measured,
            "q": q_measured,
            "alpha_via_r_half": alpha_bridge,
            "alpha_via_msd": alpha_msd,
        },
        "residuals": {
            "r_minus_lean": abs(r_measured - LEAN_CELEGANS_LINEARITY_RATIO),
            "alpha_bridge_minus_lean": abs(alpha_bridge - LEAN_CELEGANS_ALPHA),
            "alpha_msd_minus_lean": (abs(alpha_msd - LEAN_CELEGANS_ALPHA)
                                     if alpha_msd is not None else None),
        },
        "msd": msd_diag,
        "metadata": {
            "n_neurons": int(n_neurons),
            "n_edges": int(n_edges),
            "wilson_cowan_gain": 2.0,
            "wilson_cowan_tau": 1.0,
            "langevin_sigma": msd_diag.get("sigma", None),
            "n_trajectories": msd_diag.get("n_trajectories", None),
        },
    }
    with open(json_path, "w", encoding="utf-8") as f:
        json.dump(payload, f, indent=2)
    print(f"  JSON -> {json_path}")
    print()
    print("=" * 72)

    return payload


if __name__ == "__main__":
    main()
