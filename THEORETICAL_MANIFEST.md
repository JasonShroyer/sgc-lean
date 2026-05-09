# SGC Theoretical Manifest — v1.0

**Tag**: `v1.0-actuation-phase-1`
**Branch**: `sgc-actuation-phase-1`
**Build status**: `lake build` — 3155 jobs, 0 errors, 11 pre-existing sorrys (unchanged), 0 axioms added in v1.0.

This manifest is the single source of truth mapping each SGC concept to its **machine-verified** Lean theorem with `@path:line` citations.  It is intended for reviewers who want to verify the edifice in 10 minutes without reading every file.

---

## 1. Foundational structures

| Concept | Lean structure / def | Citation |
|---|---|---|
| π-weighted self-adjoint matrix | `IsSymmPi` | `@c:\Lean4 Projects\src\SGC\Spectral\WeightedHermitian.lean` |
| Constructive π-CFC | `funCalculus_SA` | `@c:\Lean4 Projects\src\SGC\Spectral\WeightedHermitian.lean` |
| Sectorial operator | `IsSectorial` | `@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean:89` |
| Calderón normalisation (positive ray) | `IsCalderonNormalized` | `@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean:75` |
| Calderón normalisation (negative ray) | `IsGeneratorCalderonNormalized` | `@c:\Lean4 Projects\src\SGC\Spectral\GeneratorBandPassFilter.lean:88` |
| Band-pass filter (positive support) | `BandPassFilter` | `@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean:108` |
| Band-pass filter (negative support, **R4b-1**) | `GeneratorBandPassFilter` | `@c:\Lean4 Projects\src\SGC\Spectral\GeneratorBandPassFilter.lean:104` |
| Sectorial functional calculus | `SectorialFunctionalCalculus` | `@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean:135` |
| Hatano-Nelson asymmetry diagnostic | `asymmetryNorm` | `@c:\Lean4 Projects\src\SGC\Quantum\HatanoNelson.lean:92` |
| Heat-kernel semigroup | `HeatKernel` | `@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean` |

## 2. Theorem index by topic

### 2.1 Spectral functional calculus (Phase R1, commit `d3be8c5`)

| Theorem | Statement (informal) | Citation |
|---|---|---|
| `funCalculus_SA_commute_HeatKernel` | `ψ(sL)` commutes with `e^{tL}` | `@c:\Lean4 Projects\src\SGC\Spectral\WeightedHermitian.lean` |
| `funCalculus_SA_scaling` | `ψ(csL) = (cψ)(sL)` for scalar `c > 0` | `@c:\Lean4 Projects\src\SGC\Spectral\WeightedHermitian.lean` |
| `functional_calculus_commutes_semigroup` | Bridge form: now a theorem (was axiom) | `@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean:145` |
| `functional_calculus_scaling` | Bridge form: now a theorem (was axiom) | `@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean:163` |

### 2.2 Canonical wavelet spine (Phase R2+R3+R4, commit `2ac1ee0`)

| Theorem / def | Content | Citation |
|---|---|---|
| `ScaleIntegratedEnergy` | Bochner integral `∫ ‖ψ(sL)f‖² ds/s` | `@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean` |
| `RepresentedStabilityFlow` | `calderonConstant · IntrinsicFlow` | `@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean` |
| `tight_frame_error_zero` | Tight-frame error vanishes when `A = B` (4-tactic proof) | `@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean` |
| `hermiteGaussianFilterNormalized_isCalderonNormalized` | Concrete HG witness for `IsCalderonNormalized` | `@c:\Lean4 Projects\src\SGC\Bridge\HermiteGaussianCanonical.lean:487` |

### 2.3 Generator-convention sibling (Phase R4b-1, commit `1335f2f`)

| Theorem | Statement | Citation |
|---|---|---|
| `GeneratorBandPassFilter.normalized_eq_one` | API restatement of `normalized` field | `@c:\Lean4 Projects\src\SGC\Spectral\GeneratorBandPassFilter.lean:118` |
| `GeneratorBandPassFilter.not_identically_zero` | Every Calderón filter is non-zero somewhere | `@c:\Lean4 Projects\src\SGC\Spectral\GeneratorBandPassFilter.lean:137` |
| `GeneratorBandPassFilter.exists_nonzero` | Existential corollary | `@c:\Lean4 Projects\src\SGC\Spectral\GeneratorBandPassFilter.lean:155` |
| `GeneratorBandPassFilter.exists_nonzero_neg` | Witness lies in `Iio 0` | `@c:\Lean4 Projects\src\SGC\Spectral\GeneratorBandPassFilter.lean:163` |

### 2.4 Quantum error correction bridge (pre-actuation, retained)

| Theorem | Citation |
|---|---|
| `knill_laflamme_forces_zero_defect` | `@c:\Lean4 Projects\src\SGC\Bridge\Quantum.lean` |
| `all_ones_in_code` | `@c:\Lean4 Projects\src\SGC\Bridge\Quantum.lean` |
| `defect_kills_all_ones` | `@c:\Lean4 Projects\src\SGC\Bridge\Quantum.lean` |
| `partition_forces_alpha_zero` | `@c:\Lean4 Projects\src\SGC\Bridge\Quantum.lean` |
| `operator_zero_iff_norm_sq_zero` | `@c:\Lean4 Projects\src\SGC\Bridge\Quantum.lean` |

### 2.5 Grokking + functional blanket (pre-actuation, retained)

| Concept | Citation |
|---|---|
| Functional blanket — algebraic symmetry classes | `@c:\Lean4 Projects\src\SGC\FunctionalBlanket.lean` |
| Kramers escape — barrier-crossing model | `@c:\Lean4 Projects\src\SGC\Grokking.lean` |
| Information gradient law `‖∇I‖ > ‖∇E‖` | `@c:\Lean4 Projects\src\SGC\Grokking.lean` |
| Adiabatic invariant for blanket freezing | `@c:\Lean4 Projects\src\SGC\ContinualLearning.lean` |

## 3. Empirical demonstrations (reproducible)

### 3.1 BCI benchmark (Track A, commit `8066801`)

```powershell
python demos/sgc_bci_benchmark.py        # full 500 s run, ~3 minutes
python demos/sgc_bci_benchmark.py --fast # fast sanity run
```

Three decoders compared: `Kalman`, `HellingerDecoder` (Fisher-Rao geometry), `SGCNESSDecoder` (zero-parameter probability-current decoder).  Output:

- `@c:\Lean4 Projects\reports\BCI_BENCHMARK_RESULTS.md` — table + headline finding
- `@c:\Lean4 Projects\reports\BCI_BENCHMARK_RESULTS.json` — raw numerical results

**Headline**: training-set asymmetry ratio `‖T_asym‖_F / ‖T_hat‖_F = 0.0037` shows the synthetic data is near-equilibrium.  The SGC-NESS decoder correctly detects this and reduces to memoryless Hellinger regression — exactly the falsification path the brief specified.

### 3.2 Lifshitz / grokking experiments (pre-actuation, retained)

```powershell
python demos/lifshitz_transition_experiment.py
python demos/functional_grokking_detector.py
```

Empirical validation of: functional defect 1.01 → 0.13 → 0.003 across grokking, class separation 0.01 → 6.45 → 346, geometric defect bounded.

## 4. Retired axioms (cumulative −15 across the R-sprint chain)

| Commit | Sprint | Axioms retired | Replacement theorems |
|---|---|---:|---|
| `500ca6e` | NormedBridge weighted compactness | −3 | constructive Mathlib-backed proofs |
| `53b2937` | KL non-negativity trio | −3 | Jensen + log-sum-inequality chain |
| `b799008` | Manifold non-degeneracy + KL eq_zero_iff | −3 | Fisher-information + Pinsker |
| `d3be8c5` | Phase R1 spectral CFC | −3 | `funCalculus_SA` + commute + scaling |
| `2ac1ee0` | Phase R2+R3+R4 canonical-wavelet spine | −3 | `ScaleIntegratedEnergy`, `RepresentedStabilityFlow`, `tight_frame_error_zero` |
| **Total** | | **−15 axioms** | **18+ new theorems** |

This sprint (`8066801` Track A + `1335f2f` Track B): 0 axioms removed, 0 axioms added, 4 new theorems in `GeneratorBandPassFilter`, 1 new structure, 1 new Python benchmark module.

## 5. Open work (scoped, not yet proved)

Each item below has a precise compile-ready Lean statement in its respective scoping report.

| Item | Statement location | Estimated effort |
|---|---|---|
| **R4b-2** Plancherel for generator convention | `@c:\Lean4 Projects\reports\PHASE_R4B_REPORT.md` §3 | ~1 week |
| **R4b-3** Frame lower bound = eigenvalue infimum | `@c:\Lean4 Projects\reports\PHASE_R4B_REPORT.md` §3 | 2–3 days after R4b-2 |
| **R4b-4** Grokking ↔ frame-bound collapse | `@c:\Lean4 Projects\reports\PHASE_R4B_REPORT.md` §3 | 1–2 weeks |
| Pre-actuation residual sorrys | `FunctionalBlanket.lean`, `AdiabaticInvariant.lean`, `SpinGlass.lean` | 11 sorrys, individually scoped |

## 6. How to verify

```powershell
git fetch origin
git checkout v1.0-actuation-phase-1
lake build                                        # full tree, 3155 jobs
lake build SGC.Spectral.GeneratorBandPassFilter   # just the new module
python demos/sgc_bci_benchmark.py --fast          # Track A sanity run
```

The git tag is the citable artefact.  Every theorem above resolves to a specific commit hash in the linear history `…→ ef09dd3 → 8066801 → 1335f2f → <release>`.

## 7. License + citation

Apache 2.0.  Cite as:

> Shroyer, J. *et al.* (2026). *SGC-Lean: The Spectral Geometry of Consolidation, v1.0-actuation-phase-1*.  GitHub: `JasonShroyer/sgc-lean`.  Tag: `v1.0-actuation-phase-1`.
