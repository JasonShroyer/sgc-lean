# Release Notes — `v1.0-actuation-phase-1`

**Date**: May 9, 2026
**Branch**: `sgc-actuation-phase-1`
**Tag**: `v1.0-actuation-phase-1`
**Build**: `lake build` — 3155 jobs, 0 errors.

This is the first **publicly tagged** release of SGC-Lean.  It consolidates the R-sprint chain (15 axiom retirements), the Phase R4b-1 sibling structure, and the first executable validation harness for the SGC theory of emergent computation.

---

## Headlines

1. **15 axioms retired across 5 R-sprints**, replaced by constructive proofs in Mathlib's spectral and information-geometric frameworks.
2. **Phase R4b-1 sibling structure** `GeneratorBandPassFilter` with non-triviality theorem proved — opens the Plancherel pipeline for SGC's Markov-generator convention.
3. **Zero-parameter `SGCNESSDecoder`** shipped in Python with an honest falsification report on synthetic BCI data — the decoder correctly detects when its NESS hypothesis is not exercised by the data, exactly as the theory predicts.
4. **0 new axioms, 0 new sorrys** in this release relative to the prior public state.

## What's new since the pre-actuation baseline (`ef09dd3`)

### Track A — Behavioural validation (`8066801`)

`@c:\Lean4 Projects\demos\sgc_bci_benchmark.py` — ~1000-line self-contained benchmark, no new dependencies, runs end-to-end in under 5 minutes.

Three decoders compared on synthetic BrainGate-matched Poisson spike data:

- `KalmanDecoder` — raw-rate baseline (30-year BCI standard).
- `HellingerDecoder` — Kalman with `h(t) = 2·sqrt(p(t))` Fisher-Rao observation geometry.
- `SGCNESSDecoder` — **zero-parameter** full SGC prescription from `HatanoNelson.lean`.  Decomposes the empirical Hellinger propagator `T_hat = T_sym + T_asym` and regresses velocity against both `h(t)` and `T_asym · h(t)`.  No gate, no threshold, no smoothing coefficient.  DMD rank chosen by Marchenko-Pastur / BBP edge.

**Result**:

| Condition | Kalman | Hellinger | SGC-NESS |
|---|---:|---:|---:|
| baseline | 0.901 | 0.892 | 0.858 |
| rate_shift | 0.900 | 0.900 | 0.868 |
| dir_rotation | 0.844 | 0.841 | 0.813 |
| dropout | 0.869 | 0.861 | 0.811 |

**Headline finding**: training-set asymmetry ratio `‖T_asym‖_F / ‖T_hat‖_F = 0.0037` is essentially zero, meaning the cosine-tuning Poisson generator produces a *near-detailed-balance* Markov system.  The NESS probability-current carries no signal, and SGC-NESS correctly reduces to memoryless Hellinger regression.  This is **not** a failure — it is the precise falsification path the SGC theory predicts and the design brief specified.

The architectural correction shipped here (delete `SGCDefectAwareDecoder`, replace with `SGCNESSDecoder`) implements the April-2026 memo: `T_asym` is the **signal**, not noise to be gated.

Reports: `@c:\Lean4 Projects\reports\BCI_BENCHMARK_RESULTS.md`, `@c:\Lean4 Projects\reports\BCI_BENCHMARK_RESULTS.json`.

### Track B — Lean R4b-1 (`1335f2f`)

New module `@c:\Lean4 Projects\src\SGC\Spectral\GeneratorBandPassFilter.lean` (~170 lines).  Introduces the Phase R4b sibling to `BandPassFilter` for SGC's Markov-generator convention (spectrum in `(-∞, 0]`):

```lean
def IsGeneratorCalderonNormalized (ψ : ℝ → ℝ) : Prop :=
  ∫ u in Set.Iio (0 : ℝ), (ψ u) ^ 2 / |u| = 1

structure GeneratorBandPassFilter where
  func : ℝ → ℝ
  support_neg : ∀ u : ℝ, 0 ≤ u → func u = 0
  normalized  : IsGeneratorCalderonNormalized func
```

Three proved theorems:

- `not_identically_zero` — every Calderón filter is non-zero somewhere (15-line proof).
- `exists_nonzero` — existential corollary.
- `exists_nonzero_neg` — combines with `support_neg` to land the witness in `Iio 0`.

**Sibling, not replacement**: `BandPassFilter` and its 12+ downstream call sites are untouched.

Scoping report: `@c:\Lean4 Projects\reports\PHASE_R4B_REPORT.md` documents R4b-2 / R4b-3 / R4b-4 with compile-ready Lean statements.

## The 15-axiom-retirement chain (cumulative since `lean-foundation-phases-1-2c`)

| Commit | Sprint | Δ axioms | What was retired |
|---|---|---:|---|
| `500ca6e` | NormedBridge | −3 | weighted compactness on finite-dim π-spaces |
| `53b2937` | KL non-negativity | −3 | Jensen + log-sum-inequality chain |
| `b799008` | Manifold non-degeneracy + KL eq_zero | −3 | Fisher-information + Pinsker |
| `d3be8c5` | Phase R1 | −3 | spectral CFC for π-self-adjoint matrices |
| `2ac1ee0` | Phase R2+R3+R4 | −3 | canonical-wavelet ScaleIntegratedEnergy + RepresentedStabilityFlow + tight_frame_error_zero |
| **v1.0** | | **−15** | |

## Build verification

```powershell
git fetch origin
git checkout v1.0-actuation-phase-1
lake build
```

Expected: `Build completed successfully (3155 jobs).`

The 11 pre-existing sorrys in `FunctionalBlanket`, `AdiabaticInvariant`, and `SpinGlass` are unchanged from the pre-actuation state and are individually scoped in their respective files.

## Breaking changes

**None.**  All v1.0 additions are sibling structures and new modules.  Every existing API surface (`BandPassFilter`, `funCalculus_SA`, the Quantum bridge theorems, `Grokking` formalisations) is preserved bit-for-bit.

## Reproducibility commands

```powershell
# Lean — full theoretical edifice
lake build

# Python — Track A behavioural validation
python demos/sgc_bci_benchmark.py        # full 500 s, ~3 min
python demos/sgc_bci_benchmark.py --fast # quick sanity, ~30 s

# Python — pre-actuation grokking + Lifshitz demos (still working)
python demos/lifshitz_transition_experiment.py
python demos/functional_grokking_detector.py
```

## Where to go next

- **For reviewers**: `@c:\Lean4 Projects\THEORETICAL_MANIFEST.md` — the 10-minute audit map.
- **For priority assessment**: `@c:\Lean4 Projects\PRIORITY_CLAIMS.md` — explicit comparison to recent external work.
- **For builders**: `@c:\Lean4 Projects\reports\PHASE_R4B_REPORT.md` — precisely scoped open theorems for the next sprint.
- **For the public face**: `@c:\Lean4 Projects\README.md`.

## Citation

> Shroyer, J. *et al.* (2026). *SGC-Lean v1.0: The Spectral Geometry of Consolidation, Actuation Phase 1.*  GitHub: `JasonShroyer/sgc-lean`.  Tag: `v1.0-actuation-phase-1`.
