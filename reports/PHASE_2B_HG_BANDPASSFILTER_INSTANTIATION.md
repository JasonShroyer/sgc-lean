# Phase 2B — HG `BandPassFilter` Instantiation

**Date:** April 25, 2026
**Sprint:** post-Phase-2A, structural completion of the SGC Canonical Wavelet proof chain
**Status:** delivered, zero new `sorry`, builds clean under `lake build`

Phase 2B closes the structural gap between `@c:\Lean4 Projects\src\SGC\InformationGeometry\HermiteGaussianExtremal.lean` (Phase 2A, the variational-extremal identity) and `@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean` (the frame-theoretic theorems). It does so by providing the concrete `BandPassFilter` instance that `CanonicalWavelet.lean` has been leaving abstract.

## Deliverable summary

| Artifact | Status |
|---|---|
| `@c:\Lean4 Projects\src\SGC\Bridge\HermiteGaussianCanonical.lean` (new, ~280 lines) | Compiles clean under `lake build`, **zero `sorry`**, zero new warnings |
| `@c:\Lean4 Projects\reports\PHASE_2B_HG_BANDPASSFILTER_INSTANTIATION.md` | This file |

Verification command:

```bash
lake build SGC.Bridge.HermiteGaussianCanonical
# ✔ [3084/3084] Built SGC.Bridge.HermiteGaussianCanonical (8.5s)
# Build completed successfully (3084 jobs).
```

## The headline definition

Located at `@c:\Lean4 Projects\src\SGC\Bridge\HermiteGaussianCanonical.lean:90-92`:

```lean
def hermiteGaussianFilter (α β : ℝ) (u : ℝ) : ℝ :=
  if 0 < u then Real.rpow u α * Real.exp (-(β * u^2)) else 0
```

This is the filter identified by the **SGC Canonical Wavelet Theorem** (paper §4.1, Theorem 1) as the unique variational extremal on constant-curvature model spaces. Extended to all of ℝ by zero on the non-positive reals so that it fits the `BandPassFilter` abstraction.

The `BandPassFilter` instance itself at `@c:\Lean4 Projects\src\SGC\Bridge\HermiteGaussianCanonical.lean:150-153`:

```lean
def HGBandPassFilter (α β : ℝ) : BandPassFilter :=
  { func := hermiteGaussianFilter α β,
    support_pos := hermiteGaussianFilter_support_pos α β,
    normalized := trivial }
```

With this definition, **every universally-quantified theorem in `CanonicalWavelet.lean` now has a concrete specialisation to the canonical HG filter**.

## Supporting lemmas proved along the way

| Lemma | Content |
|---|---|
| `hermiteGaussianFilter_zero_of_nonpos` | Filter vanishes for `u ≤ 0` |
| `hermiteGaussianFilter_pos_of_pos` | Filter is strictly positive for `u > 0` |
| `hermiteGaussianFilter_support_pos` | Discharges `BandPassFilter.support_pos` |
| `hermiteGaussianFilter_eq_rpow_mul_gaussAmpl` | Bridge to Phase 2A: `ψ_{α,β}(u) = u^α · gaussAmpl(2β)(u)` for `u > 0` |
| `HGBandPassFilter_func` | `@[simp]` unfolding lemma |

## Specialisations of `CanonicalWavelet.lean` theorems

All five become concrete theorems about the canonical Hermite-Gaussian frame:

| Concrete theorem | Specialises | Paper statement |
|---|---|---|
| `HG_representation_error_bound` | `representation_error_bound` | Paper inequality `\|β_rep - β_intrinsic\| ≤ C(B/A - 1)` |
| `HG_tight_frame_zero_error` | `tight_frame_zero_error` | Paper: tight frame ⇒ zero artifact flow |
| `HG_tight_frame_exists_on_constant_ricci` | `constant_ricci_tight_frame_exists` | **Paper Theorem 1 existence form** |
| `HG_geometric_error_bound` | `geometric_error_bound` | Paper Theorem 1.A: Fisher-Rao penalty bound |
| `HG_frame_condition_ge_one` | `frame_condition_ge_one` | Paper frame-bound inequality `B/A ≥ 1` |

Each specialisation is a one-line direct instantiation — zero new proof obligations, zero new axioms, zero new `sorry`s.

## The completed canonical-wavelet chain

With Phase 2B in place, the structural chain is now complete:

```
           Paper Theorem 1 (continuous uniqueness on model spaces)
                                │
                                ▼   Phase 2A (critical-point kernel via Euler-Lagrange)
               `gaussAmpl_is_harmonic_oscillator_ground_state`
                                │
                                ▼   Phase 2B (extend to u^α · exp(-β u²); vanish on u ≤ 0)
                     `hermiteGaussianFilter`
                                │
                                ▼   Phase 2B (BandPassFilter instantiation)
                     `HGBandPassFilter`  ←──(structural hand-off)──┐
                                                                  │
                    `SGC.Bridge.CanonicalWavelet`                  │
                    abstract frame theorems (5)                   │
                                │                                 │
                                ▼  (direct instantiation)         │
           `HG_representation_error_bound`,                       │
           `HG_tight_frame_zero_error`,                           │
           `HG_tight_frame_exists_on_constant_ricci`,   ──────────┘
           `HG_geometric_error_bound`,
           `HG_frame_condition_ge_one`.
```

The result: the **SGC Canonical Wavelet theorem chain has a concrete canonical filter in the repo** — no more abstract `psi : BandPassFilter` hand-waving.

## Honest scope — what still remains open

Three leverage points are explicitly documented as future work, not claimed as done:

1. **The `normalized` field is still `True`** in `@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean:74`. Strengthening it to carry the Calderón condition `∫₀^∞ |ψ(u)|² du/u = 1` and proving it for the HG filter with normalisation constant `C_{α,β} = √(2·(2β)^α / Γ(α))` requires `Mathlib.Analysis.SpecialFunctions.Gamma` and `Mathlib.MeasureTheory.Integral` — heavy but tractable. Phase 2E-candidate.
2. **Excited Hermite-Gaussian states `ψ_n` for `n ≥ 1`** are not yet formalised at the EL level. They follow by repeated application of the raising operator `a^† = -∂_u + √β · u` to the ground state proved in Phase 2A. Phase 2D-candidate.
3. **`geometric_commutator_constraint` and `constant_ricci_tight_frame_exists`** in `CanonicalWavelet.lean` remain axioms. Discharging them would require pseudospectral machinery (paper §4.2, via the Kreiss Matrix Theorem referenced in the paper). Phase 2E-candidate.

None of these openness items blocks the use of the canonical wavelet tower at the critical-point level.

## What explicitly is NOT introduced

Same discipline as Phase 2A. The full chain `HellingerLift → HermiteGaussianExtremal → HGBandPassFilter → CanonicalWavelet frame theorems` is a **scalar** chain. The paper's Theorems 1, 1.A, 2, and Lemma 3.2 are all scalar results; their formalisation across these four Lean files introduces no spinor machinery and requires none.

The non-normality appearing in paper Theorem 1.A and Theorem 2 is handled by the **commutator `[L, Γ₂]`** used in `CanonicalWavelet.lean`'s `geometric_commutator_constraint` — which is the paper's own device (paper §4.2, §2.3). It is **not** a "chirality operator" `Γ = (L - L^*)/\|L - L^*\|`; that framing is an overlay proposed by an earlier synthesis, rejected in Phase 2A for reasons documented at `@c:\Lean4 Projects\reports\PHASE_2A_CANONICAL_WAVELET_FOUNDATION.md`.

## Current tower status

| Layer | Theorem | File | Status |
|---|---|---|---|
| **0** | Chentsov metric uniqueness | `RenormalizationDynamics.lean` | axiomatised |
| **1** | Hellinger tangent isometry (Phase 1A) | `HellingerLift.lean` | **zero `sorry` proved** |
| **2–3** | Fisher geometry + spectral consolidation | `FisherKL.lean`, `RenormalizationDynamics.lean` | axiomatised + proved |
| **4** | HG ground-state EL identity (Phase 2A) | `HermiteGaussianExtremal.lean` | **zero `sorry` proved** |
| **4b** | Canonical wavelet frame stability (abstract) | `CanonicalWavelet.lean` | axiomatised framework + proved theorems |
| **4c** | HG `BandPassFilter` instantiation + concrete specialisations (Phase 2B) | `HermiteGaussianCanonical.lean` | **zero `sorry` proved** |
| **5** | HG completeness / orthonormality | `HGCompleteness.lean` | skeleton, 10+ `sorry`s |

## Technical note for the next session

For Phase 2C (closing `hg_orthonormal` and `hg_momentum_recurrence` in `HGCompleteness.lean`), the `hasDerivAt_gaussAmpl` and `hasDerivAt_gaussAmpl_firstDeriv` derivatives from Phase 2A are directly reusable. The momentum-recurrence identity `d/dx ψ_n = √n · ψ_{n-1} − √(n+1) · ψ_{n+1}` follows from the harmonic-oscillator ladder operators `a`, `a^†` acting on the raw Gaussian, which is exactly the structure of Phase 2A's derivative identities.

For any derivative proof inside `HGCompleteness.lean`, remember the Mathlib API gotcha from Phase 2A: use **explicit** `HasDerivAt.neg`, `HasDerivAt.exp`, `HasDerivAt.mul` qualification (not dot notation, which resolves to `HasFDerivAtFilter.*` via definitional unfolding), and import:

```lean
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
```

## Artefacts

```
src/SGC/Bridge/HermiteGaussianCanonical.lean              (NEW, ~280 lines, zero sorry)
reports/PHASE_2B_HG_BANDPASSFILTER_INSTANTIATION.md       (this file)
```

## Closing posture

The structural proof chain for the SGC Canonical Wavelet theorem is now complete in Lean at the critical-point level. Three bricks — Phase 1A (Hellinger), Phase 2A (EL identity), Phase 2B (BandPassFilter instantiation) — all dry, all zero `sorry`. The paper's Theorem 1 has a concrete filter identification in the repo; the paper's Theorem 2 frame-stability results now specialise directly to the canonical HG family.

Nothing committed today contradicts anything already in the repo. No new axioms, no phantom files, no overreach. Ready for Phase 2C, 2D, or 3 on the user's priority.
