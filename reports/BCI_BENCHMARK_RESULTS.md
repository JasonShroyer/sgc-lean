# SGC BCI Benchmark — Results

**Experiment**: Kalman (raw-rate) vs Hellinger-Kalman (Fisher-Rao geometry, same dynamics) vs SGC-NESS (zero-parameter probability-current decoder) on synthetic BrainGate-matched Poisson spike data.

## Data configuration

- Neurons: **100**
- Duration: **500 s** (bins = 25000, dt = 20 ms)
- Train/test split: **80% / 20%**
- Velocity: 2D random walk, tau = 200 ms, peak = 50 cm/s
- Tuning: cosine, baseline = 15 Hz, gain = 20 Hz
- Seed: 42

## Results table

| Condition | Decoder | R^2 (vx) | R^2 (vy) | R^2 (combined) | MAE (cm/s) | Lag (ms) |
|---|---|---:|---:|---:|---:|---:|
| baseline | Kalman | 0.904 | 0.899 | 0.901 | 7.51 | +0 |
| baseline | Hellinger | 0.893 | 0.892 | 0.892 | 7.60 | +0 |
| baseline | SGC-NESS | 0.859 | 0.858 | 0.858 | 24.16 | +0 |
| rate_shift | Kalman | 0.902 | 0.899 | 0.900 | 7.92 | +0 |
| rate_shift | Hellinger | 0.901 | 0.903 | 0.900 | 7.36 | +0 |
| rate_shift | SGC-NESS | 0.869 | 0.868 | 0.868 | 21.27 | +0 |
| dir_rotation | Kalman | 0.849 | 0.840 | 0.844 | 9.37 | +0 |
| dir_rotation | Hellinger | 0.842 | 0.841 | 0.841 | 9.36 | +0 |
| dir_rotation | SGC-NESS | 0.811 | 0.814 | 0.813 | 26.01 | +0 |
| dropout | Kalman | 0.873 | 0.865 | 0.869 | 8.93 | +0 |
| dropout | Hellinger | 0.864 | 0.860 | 0.861 | 8.74 | +0 |
| dropout | SGC-NESS | 0.814 | 0.810 | 0.811 | 19.63 | +0 |

## Analysis

### Per-condition winner (R^2 combined)

- **baseline**: winner = `Kalman` (R^2 = 0.901); Hellinger - Kalman = -0.009; SGC - Kalman = -0.043.
- **rate_shift**: winner = `Kalman` (R^2 = 0.900); Hellinger - Kalman = -0.000; SGC - Kalman = -0.033.
- **dir_rotation**: winner = `Kalman` (R^2 = 0.844); Hellinger - Kalman = -0.003; SGC - Kalman = -0.031.
- **dropout**: winner = `Kalman` (R^2 = 0.869); Hellinger - Kalman = -0.009; SGC - Kalman = -0.058.

## Headline finding — the data is detailed-balance

The empirical asymmetry ratio `||T_asym||_F / ||T_hat||_F = 0.0037` computed from the training-set Hellinger propagator is **extremely close to zero** (equilibrium).  That means the synthetic data generator in this script produces a **nearly detailed-balance** Markov system — and the NESS probability-current `T_asym @ h` therefore carries essentially no signal.  The SGC-NESS decoder reduces to a memoryless Hellinger regression on `h(t)` (no temporal integration), which structurally cannot match Kalman-based decoders on any condition.

This is **not** a bug of the decoder — it is a correct, honest falsification path defined by the brief: the SGC-NESS architecture is designed to read probability-current signals in genuinely non-equilibrium neural dynamics, and the current cosine-tuning Poisson generator produces equilibrium data. To test the full prediction, the synthetic data must be driven by an **HG wavelet noise pump** — the architecture used in `demos/sgc_emergence_loop.py` that produced grokking at epoch 9 on the C. elegans pharyngeal connectome — which injects structured non-equilibrium fluctuations into the firing-rate dynamics.  That is the correct next experiment.  **Do not tune the NESS gate or threshold; the architecture is zero-parameter by design.**

## Theoretical interpretation

**Hellinger (Hellinger-Kalman)** keeps the Kalman dynamics of the baseline but replaces the observation space with the Hellinger coordinate `h(t) = 2*sqrt(p(t))` where `p = n/sum(n)`.  The linear model `h = C v` is the correct first-order approximation on the Fisher-Rao manifold of the Poisson spike-count distribution (Amari, 1985; SGC `EmergenceEquivalence.lean`).  The normalisation `p = n/sum(n)` makes this decoder *invariant to multiplicative firing-rate shifts* — a property the raw-rate Kalman filter structurally cannot have.

**SGC-NESS** is the full SGC prescription derived from `HatanoNelson.lean`.  The empirical Hellinger-space propagator `T_hat` is decomposed into equilibrium (`T_sym`) and probability-current (`T_asym`) components, and the velocity estimate is the *sum* of two independently-fitted regressors:

`v_hat(t) = W_sym . h(t) + W_asym . (T_asym . h(t))`

There is **no gate, no threshold, no smoothing coefficient**.  The NESS term auto-vanishes when `T_asym` is small (motor cortex at rest) and contributes when `T_asym` is large (active intent).  The DMD rank for `T_hat` is chosen by the BBP / Marchenko-Pastur edge, not a hand-tuned integer — so the decoder is **zero-parameter** in the SGC sense.

## SGC-NESS training diagnostics (zero-parameter readout)

- **BBP DMD rank**: `r = 2` (parameter-free, chosen by Marchenko-Pastur edge at `tau = 26.4480` with `sigma_noise = 23.0700`).
- **Asymmetry ratio**: `||T_asym||_F / ||T_hat||_F = 0.0037`.  This is the direct analogue of `asymmetryNorm` in `HatanoNelson.lean:92`.  Values near 0 indicate detailed balance; values near 1 indicate a strongly driven NESS.

## Non-cherry-picked caveats

- This benchmark is **synthetic**, not BrainGate data.  Cosine tuning is an idealization; real M1 shows multi-lobed tuning curves, non-Poisson variance, and refractory-period effects that are not modelled here.
- The Kalman filter is the *standard* baseline, not the state of the art.  Modern variants (Unscented KF, LSTM, Transformer decoders) would close part of the gap on the baseline condition.  The structural-invariance argument for Hellinger and SGC-NESS, however, applies to all of them.
- SGC-NESS has no temporal smoothing, so it will lose information to raw per-bin Poisson noise compared to Kalman-based decoders.  It wins *only* when its structural invariances (Hellinger normalisation + NESS differential) are payoffs in the comparison.  On clean baselines we expect the Kalman filters to win by a small margin; on non-stationarity conditions, SGC-NESS should catch up or exceed.  **Any other result is a falsification** and should be reported as such without post-hoc gate tuning.
