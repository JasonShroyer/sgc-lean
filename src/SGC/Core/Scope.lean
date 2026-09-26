/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.InformationGeometry.MarkovPathFisher

/-!
# `SGC.Scope`: a certified evaluation scope

A scope is a fine discrete-time kernel, a partition (the coarse projection),
and a strictly positive stationary law. The defect is computed, never stored:
it is the canonical measure-reentry defect `MeasureReentry.defectSq`. Exactness
is a derived proposition, equivalent to zero defect.

## What is proved and what is not

* `defectSq_eq_zero_iff` — zero defect iff exact strong lumpability.
* `fisherLoss_le` — for a block-pair tilt with row energy at most `Bmax`, the
  path Fisher information lost by the macro-observer over `T` steps is at most
  `T² · Bmax · 𝔇_π²` (proved, `MarkovPathFisher`).
* `informationHorizon` / `fisherLoss_le_of_le_horizon` — the proved horizon:
  for `T ≤ √(ε / (Bmax · 𝔇_π²))` the loss is at most `ε`.
* `mixingLossRate` — the linear-in-`T` rate `Bmax · 𝔇_π² · (1+σ)/(1-σ)` is a
  DEFINITION ONLY. It is supported numerically (960/960 cases,
  `closure_sufficiency_v3`) but not proved; no theorem here depends on it.

These horizons bound information about a parameter direction lost by coarse
observation. They are not prediction-error horizons; those are
`KernelHorizon` / `PhysicalHorizon` statements about `‖Tⁿ K − K Qⁿ‖`.
-/

noncomputable section

namespace SGC.Core

open Matrix SGC.InformationGeometry

/-- A certified evaluation scope. -/
structure Scope (V : Type*) [Fintype V] [DecidableEq V] where
  kernel : Matrix V V ℝ
  partition : Partition V
  pi : V → ℝ
  kernel_pos : ∀ x y, 0 < kernel x y
  kernel_row : ∀ x, ∑ y, kernel x y = 1
  pi_pos : ∀ x, 0 < pi x
  pi_stationary : pi ᵥ* kernel = pi

namespace Scope

variable {V : Type*} [Fintype V] [DecidableEq V] (S : Scope V)

/-- The canonical measure-reentry defect `𝔇_π²` of the scope. -/
def defectSq : ℝ := SGC.Renormalization.MeasureReentry.defectSq S.kernel S.partition S.pi

/-- The scope is exact when the partition is strongly lumpable for the kernel. -/
def IsExact : Prop := IsStronglyLumpable S.kernel S.partition

theorem defectSq_nonneg : 0 ≤ S.defectSq :=
  SGC.Renormalization.MeasureReentry.defectSq_nonneg _ _ (fun x => (S.pi_pos x).le)

theorem defectSq_eq_zero_iff : S.defectSq = 0 ↔ S.IsExact :=
  SGC.Renormalization.MeasureReentry.defectSq_eq_zero_iff_stronglyLumpable _ _ S.pi_pos

/-- Fisher information lost over `T` steps by the macro-observer, for a
block-pair tilt `b`. -/
def fisherLoss (b : S.partition.Quot → S.partition.Quot → ℝ) (T : ℕ) : ℝ :=
  ScoreProjection.fineFisher (MarkovPathFisher.pathProb S.kernel S.pi T)
      (MarkovPathFisher.pathDeriv S.kernel S.partition.quot_map S.pi b T)
    - ScoreProjection.coarseFisher (MarkovPathFisher.macroPath S.partition.quot_map T)
      (MarkovPathFisher.pathProb S.kernel S.pi T)
      (MarkovPathFisher.pathDeriv S.kernel S.partition.quot_map S.pi b T)

theorem fisherLoss_le (b : S.partition.Quot → S.partition.Quot → ℝ) {Bmax : ℝ}
    (hB : ∀ A, ∑ C, b A C ^ 2 ≤ Bmax) (T : ℕ) :
    S.fisherLoss b T ≤ (T : ℝ) ^ 2 * (Bmax * S.defectSq) :=
  MarkovPathFisher.fisherLoss_markov_path_le_measureReentry S.kernel S.pi T S.partition
    S.kernel_pos S.kernel_row S.pi_pos S.pi_stationary b hB

/-- An exact scope loses no information about any block-pair tilt. -/
theorem fisherLoss_eq_zero_of_exact (hex : S.IsExact)
    (b : S.partition.Quot → S.partition.Quot → ℝ) (T : ℕ) : S.fisherLoss b T ≤ 0 := by
  have hB : ∀ A, ∑ C, b A C ^ 2 ≤ ∑ A', ∑ C, b A' C ^ 2 := fun A =>
    Finset.single_le_sum (f := fun A => ∑ C, b A C ^ 2)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ A)
  have h := S.fisherLoss_le b hB T
  rwa [(S.defectSq_eq_zero_iff).mpr hex, mul_zero, mul_zero] at h

/-- The proved information horizon `√(ε / (Bmax · 𝔇_π²))`. -/
def informationHorizon (ε Bmax : ℝ) : ℝ := Real.sqrt (ε / (Bmax * S.defectSq))

theorem fisherLoss_le_of_le_horizon (b : S.partition.Quot → S.partition.Quot → ℝ)
    {Bmax ε : ℝ} (hB : ∀ A, ∑ C, b A C ^ 2 ≤ Bmax) (hBpos : 0 < Bmax)
    (hD : 0 < S.defectSq) (hε : 0 ≤ ε) (T : ℕ)
    (hT : (T : ℝ) ≤ S.informationHorizon ε Bmax) : S.fisherLoss b T ≤ ε := by
  have hc : 0 < Bmax * S.defectSq := mul_pos hBpos hD
  have hsq : (T : ℝ) ^ 2 ≤ ε / (Bmax * S.defectSq) := by
    have := pow_le_pow_left₀ (Nat.cast_nonneg T) hT 2
    rwa [informationHorizon, Real.sq_sqrt (div_nonneg hε hc.le)] at this
  have h2 : (T : ℝ) ^ 2 * (Bmax * S.defectSq) ≤ ε := by
    rwa [le_div_iff₀ hc] at hsq
  exact (S.fisherLoss_le b hB T).trans h2

/-- Conjectural linear-in-`T` loss rate under mixing with contraction `σ`.
Definition only: numerically supported, not proved; no theorem uses it. -/
def mixingLossRate (Bmax σ : ℝ) : ℝ := Bmax * S.defectSq * (1 + σ) / (1 - σ)

end Scope

end SGC.Core
