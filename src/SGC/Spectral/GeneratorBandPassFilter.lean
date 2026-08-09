/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# GeneratorBandPassFilter: Calderón wavelets on the negative half-line

This module opens **Phase R4b** of the SGC spectral-wavelet programme
(design doc: `@c:\Lean4 Projects\reports\DESIGN_REPRESENTED_STABILITY_FLOW.md`).

## Problem (Phase R4b scope)

The existing `BandPassFilter` in
`@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean:108` carries the
classical continuous-wavelet support and normalisation conventions:

* `support_pos : ∀ s, func s ≠ 0 → s > 0`  — support on `(0, ∞)`.
* `normalized : ∫ u in Set.Ioi 0, func u ^ 2 / u = 1`  — Calderón reproducing.

These conventions are correct for **Laplacian-type** operators whose
spectra lie in `[0, ∞)`.  In the SGC codebase, however, `L` is a Markov
**generator** (rate matrix) whose spectrum lies in `(-∞, 0]`.  Applying
a `BandPassFilter`-built functional calculus to an SGC generator `L`
yields `ψ(s·λᵢ) = 0` for every eigenvalue `λᵢ ≤ 0` — so the
`funCalculus_SA` of Phase R1 is identically zero on the SGC convention,
and the Plancherel / scale-integrated-energy identity becomes vacuous.

This module introduces a **sibling structure**, `GeneratorBandPassFilter`,
whose support and normalisation live on the negative half-line with the
mirror-image Haar measure `du / |u|`.  Both sibling structures coexist;
neither is modified.  Downstream theorems of Phase R4b (the Plancherel
identity and the grokking-frame-bound collapse) will be stated in terms
of the new structure.

## Deliverable of this file (Phase R4b-1)

1. The definition `IsGeneratorCalderonNormalized` — Calderón condition
   on `Set.Iio 0`.
2. The structure `GeneratorBandPassFilter` with three fields.
3. The non-triviality theorem `GeneratorBandPassFilter.not_identically_zero`:
   every `GeneratorBandPassFilter` has its scalar profile non-zero on at
   least one point, because the normalisation integral is `1 ≠ 0`.
4. A forward-compatibility helper `GeneratorBandPassFilter.normalized_eq_one`
   that is `rfl`-equal to `.normalized` but hides the unfolded integral
   behind a named lemma so downstream proofs read cleanly.

## Deferred to subsequent Phase R4b-2/3/4 sprints

* **R4b-2** `scaleIntegratedEnergy_calderon_generator` — the Plancherel
  identity for `funCalculus_SA` against a `GeneratorBandPassFilter`,
  giving `ScaleIntegratedEnergy = ‖f‖²_π` in this convention.  Requires
  a change-of-variables lemma on the multiplicative group `(0, ∞)`
  applied inside Mathlib's `cfc` framework.
* **R4b-3** `frame_bound_lower_eigenvalue` — the frame lower bound
  `A := inf_i ∫ s, ψ(s·λᵢ)² / s ds` expressed purely in terms of the
  spectrum of `L`.  Direct corollary of R4b-2.
* **R4b-4** `grokking_iff_frame_bound_collapse` — in `Grokking.lean`,
  the statement that the grokking phase transition of a learning
  dynamics corresponds exactly to the frame lower bound `A` crossing
  zero.  This would subsume the April-2026 *Spectral Edge Thesis* and
  *Grokking as Dimensional Phase Transition* results.

A running report of open goals and progress lives at
`@c:\Lean4 Projects\reports\PHASE_R4B_REPORT.md`.
-/

namespace SGC.Spectral.GeneratorBandPass

open MeasureTheory Set

/-- **Calderón normalisation for generator-convention filters**:

    `∫ u in (-∞, 0), ψ(u)² / |u| du = 1`.

    The measure `du / |u|` on the negative half-line is the multiplicative
    Haar measure in the `u ↦ -u` coordinate (so that `|u|` replaces `u`
    in the denominator).  It is the mirror image of
    `IsCalderonNormalized` in
    `@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean:75`,
    applied to filters supported on `Set.Iio 0`. -/
def IsGeneratorCalderonNormalized (ψ : ℝ → ℝ) : Prop :=
  ∫ u in Set.Iio (0 : ℝ), (ψ u) ^ 2 / |u| = 1

/-- **Band-pass filter on the negative half-line** — the Phase R4b sibling
    of `BandPassFilter`.

    Fields:
    * `func`       — the scalar filter profile.
    * `support_neg`— `ψ` vanishes on `[0, ∞)`, i.e., is supported on
                     the open negative ray `(-∞, 0)`.
    * `normalized` — `IsGeneratorCalderonNormalized func`.

    **Design note**: smoothness (`ContDiff ℝ ⊤ func`) is intentionally
    *not* a field here, because the non-triviality theorem `R4b-1` does
    not require it.  When the Plancherel identity `R4b-2` is proved, a
    smoothness or measurability hypothesis will be added separately at
    the theorem level — following the pattern of `funCalculus_SA`'s
    `Continuous` side condition. -/
structure GeneratorBandPassFilter where
  /-- Scalar filter profile. -/
  func : ℝ → ℝ
  /-- Support on the open negative half-line: `func` vanishes on `[0, ∞)`. -/
  support_neg : ∀ u : ℝ, 0 ≤ u → func u = 0
  /-- Calderón reproducing condition on the negative half-line. -/
  normalized : IsGeneratorCalderonNormalized func

namespace GeneratorBandPassFilter

/-- The Calderón integral of a `GeneratorBandPassFilter` equals `1`.

    A thin restatement of the `normalized` field under the full name of
    the integral.  Makes downstream `rw` / `simp` calls more readable. -/
theorem normalized_eq_one (ψ : GeneratorBandPassFilter) :
    ∫ u in Set.Iio (0 : ℝ), (ψ.func u) ^ 2 / |u| = 1 :=
  ψ.normalized

/-- **Non-triviality theorem (Phase R4b-1)**:

    Every `GeneratorBandPassFilter` has a non-zero scalar profile at some
    point.  This is the bare minimum sanity check on the structure, and
    is a direct consequence of the normalisation integral being `1 ≠ 0`.

    The proof is short: if `ψ.func ≡ 0` on all of `ℝ`, the integrand of
    `normalized` is zero everywhere, so the integral is zero — contradicting
    `normalized = 1`.  This uses `MeasureTheory.integral_zero` for the
    Bochner integral of the constant zero function.

    **Why this matters for R4b**: every subsequent theorem in Phase R4b
    (Plancherel identity, frame-bound eigenvalue expression, grokking
    phase transition) implicitly depends on the filter being non-zero
    on the spectrum of `L`.  This theorem is the formal hook that makes
    such arguments structurally available. -/
theorem not_identically_zero (ψ : GeneratorBandPassFilter) :
    ¬ (∀ x : ℝ, ψ.func x = 0) := by
  intro h_all_zero
  -- Unfold the Calderón normalisation to its underlying equality.
  have h_norm :
      ∫ u in Set.Iio (0 : ℝ), (ψ.func u) ^ 2 / |u| = 1 :=
    ψ.normalized
  have h_int_zero : ∫ u in Set.Iio (0 : ℝ), (ψ.func u) ^ 2 / |u| = 0 := by
    have h_integrand_zero :
        (fun u => (ψ.func u) ^ 2 / |u|) = (fun _ => (0 : ℝ)) := by
      funext u
      rw [h_all_zero u]
      simp
    rw [h_integrand_zero]
    simp
  have h_one_zero : (1 : ℝ) = 0 := h_norm.symm.trans h_int_zero
  exact one_ne_zero h_one_zero

/-- **Corollary**: there exists a point where `ψ.func` is non-zero. -/
theorem exists_nonzero (ψ : GeneratorBandPassFilter) :
    ∃ x : ℝ, ψ.func x ≠ 0 := by
  by_contra h
  push_neg at h
  exact ψ.not_identically_zero h

/-- **Corollary**: the non-zero point from `exists_nonzero` lies in
    `Set.Iio 0`.

    Combines `exists_nonzero` with the `support_neg` field: if `ψ.func x ≠ 0`
    then `¬ (0 ≤ x)`, i.e., `x < 0`. -/
theorem exists_nonzero_neg (ψ : GeneratorBandPassFilter) :
    ∃ x : ℝ, x < 0 ∧ ψ.func x ≠ 0 := by
  obtain ⟨x, hx⟩ := ψ.exists_nonzero
  refine ⟨x, ?_, hx⟩
  by_contra h_nonneg
  push_neg at h_nonneg
  exact hx (ψ.support_neg x h_nonneg)

end GeneratorBandPassFilter

end SGC.Spectral.GeneratorBandPass
