/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# The Statistical Horizon theorem

The Kernel Horizon mechanism (`SGC.Renormalization.KernelHorizon.kernel_closure_error_le`:
contraction plus telescoping) transported to an abstract operator setting that covers the
Koopman operator of a measure-preserving dynamical system.

## Setting

A normed space `E` (in the intended application, `E = L^2(μ)` for an invariant measure
`μ`), a **non-expansive** operator `U` (`‖U‖ ≤ 1`; the Koopman operator `φ ↦ φ ∘ S` of a
measure-preserving map is an isometry), and a **projection** `Π` with `Π * Π = Π` and
`‖Π‖ ≤ 1` (conditional expectation onto a finite partition is an orthogonal projection).
The **coarse predictor** is `A = Π * U * Π` and the **closure defect** is

    δ = ‖(1 - Π) * U * Π‖ ,

the part of one step that leaves the coarse subspace when started inside it.

## Results

* `statistical_horizon`: `‖U^m * Π - A^m * Π‖ ≤ m * δ`.
* `statistical_forecast_horizon`: `‖Π * U^m * Π - A^m * Π‖ ≤ m * δ` - conditional
  `m`-step predictions differ from iterating the one-step coarse predictor by at most
  `m δ` on unit observables. With sampling time `τ` the physical horizon for tolerance
  `η` is `m τ` with `m δ ≤ η`.
* `exact_forecast_of_defect_zero`: `δ = 0` forces exact agreement for all `m`.

## The obstruction this quantifies (regression test)

Averaging one-step transitions of a measure-preserving system over a partition gives a
row-stochastic matrix with the right stationary law, but **not** an autonomous coarse
Markov law: the `m`-step statistics need not be the `m`-th power of the one-step matrix.
`fourCycle_K2_ne_K1_sq` records the smallest counterexample (external review,
2026-09-12): the deterministic four-cycle `0 → 1 → 2 → 3 → 0` with uniform invariant
measure and cells `{0,1}`, `{2,3}` has `K₁ = [[1/2,1/2],[1/2,1/2]]` but
`K₂ = [[0,1],[1,0]] ≠ K₁²`. The statistical horizon theorem is exactly the statement
that such failures are bounded by `m δ`; the four-cycle has `δ > 0`.

## What is and is not claimed

PROVEN: the operator inequalities above for any normed space and any `U`, `Π` with the
stated norm and idempotence hypotheses; the four-cycle matrix inequality.

NOT CLAIMED: anything about fluids. Instantiating `E = L^2(μ)` for an invariant measure
of Galerkin Navier-Stokes, choosing the partition, and estimating `δ` is the statistical
bridge programme; this module supplies its horizon theorem and its first regression test,
not the bridge. `δ = 0` is a strong condition: for a deterministic evolution and a finite
partition it forces the next cell to be a deterministic function of the current cell
(external review), so positive `δ` is the generic case.

Attribution: the theorem statement and the four-cycle counterexample were supplied in an
external adversarial review (2026-09-12); the formalization is this project's.
-/

noncomputable section

namespace SGC.Bridge.StatisticalHorizon

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The coarse one-step predictor `P U P`. -/
def coarsePredictor (U P : E →L[ℝ] E) : E →L[ℝ] E := P * U * P

/-- The closure defect `‖(1 - P) U P‖`. -/
def closureDefect (U P : E →L[ℝ] E) : ℝ := ‖(1 - P) * U * P‖

section Lemmas

variable {U P : E →L[ℝ] E}

/-- `P` absorbs on the left of `A^m P`. -/
lemma proj_mul_pow_predictor_mul_proj (hPP : P * P = P) (m : ℕ) :
    P * ((coarsePredictor U P) ^ m * P) = (coarsePredictor U P) ^ m * P := by
  induction m with
  | zero => simp [hPP]
  | succ m _ =>
    rw [pow_succ']
    simp only [coarsePredictor, mul_assoc]
    rw [← mul_assoc P P, hPP]

/-- `‖A‖ ≤ 1`. -/
lemma norm_coarsePredictor_le_one (hU : ‖U‖ ≤ 1) (hP : ‖P‖ ≤ 1) :
    ‖coarsePredictor U P‖ ≤ 1 := by
  unfold coarsePredictor
  calc ‖P * U * P‖ ≤ ‖P * U‖ * ‖P‖ := norm_mul_le _ _
    _ ≤ (‖P‖ * ‖U‖) * ‖P‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ (1 * 1) * 1 := by gcongr
    _ = 1 := by ring

/-- `‖A^m P‖ ≤ 1`. -/
lemma norm_pow_predictor_mul_proj_le_one (hU : ‖U‖ ≤ 1) (hP : ‖P‖ ≤ 1) (m : ℕ) :
    ‖(coarsePredictor U P) ^ m * P‖ ≤ 1 := by
  have hA := norm_coarsePredictor_le_one hU hP
  have hAm : ‖(coarsePredictor U P) ^ m‖ ≤ 1 := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simpa [ContinuousLinearMap.one_def] using (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E))
    · calc ‖(coarsePredictor U P) ^ m‖ ≤ ‖coarsePredictor U P‖ ^ m := norm_pow_le' _ hm
        _ ≤ 1 ^ m := by gcongr
        _ = 1 := one_pow m
  calc ‖(coarsePredictor U P) ^ m * P‖ ≤ ‖(coarsePredictor U P) ^ m‖ * ‖P‖ := norm_mul_le _ _
    _ ≤ 1 * 1 := by gcongr
    _ = 1 := by ring

end Lemmas

section Main

variable {U P : E →L[ℝ] E}

/-- The `m`-step error operator `U^m P - A^m P`. -/
def errorOp (U P : E →L[ℝ] E) (m : ℕ) : E →L[ℝ] E :=
  U ^ m * P - (coarsePredictor U P) ^ m * P

/-- Exact one-step recursion: `E_{m+1} = U E_m + (U - A) A^m P`. -/
lemma errorOp_succ (m : ℕ) :
    errorOp U P (m + 1) =
      U * errorOp U P m + (U - coarsePredictor U P) * ((coarsePredictor U P) ^ m * P) := by
  simp only [errorOp, pow_succ', mul_sub, sub_mul, mul_assoc]
  abel

/-- The inhomogeneous term is a defect: `(U - A) A^m P = ((1 - P) U P) (A^m P)`. -/
lemma sub_predictor_mul (hPP : P * P = P) (m : ℕ) :
    (U - coarsePredictor U P) * ((coarsePredictor U P) ^ m * P) =
      ((1 - P) * U * P) * ((coarsePredictor U P) ^ m * P) := by
  conv_lhs => rw [← proj_mul_pow_predictor_mul_proj hPP m]
  simp only [coarsePredictor, sub_mul, one_mul, mul_assoc]
  rw [← mul_assoc P P, hPP]

/-- **Statistical Horizon theorem.** `‖U^m P - A^m P‖ ≤ m δ`. -/
theorem statistical_horizon (hU : ‖U‖ ≤ 1) (hP : ‖P‖ ≤ 1) (hPP : P * P = P) (m : ℕ) :
    ‖errorOp U P m‖ ≤ m * closureDefect U P := by
  induction m with
  | zero => simp [errorOp]
  | succ m ih =>
    rw [errorOp_succ, sub_predictor_mul hPP]
    have hδ : ‖((1 - P) * U * P) * ((coarsePredictor U P) ^ m * P)‖ ≤ closureDefect U P := by
      calc ‖((1 - P) * U * P) * ((coarsePredictor U P) ^ m * P)‖
          ≤ ‖(1 - P) * U * P‖ * ‖(coarsePredictor U P) ^ m * P‖ := norm_mul_le _ _
        _ ≤ ‖(1 - P) * U * P‖ * 1 := by
            gcongr; exact norm_pow_predictor_mul_proj_le_one hU hP m
        _ = closureDefect U P := by rw [mul_one]; rfl
    have hUE : ‖U * errorOp U P m‖ ≤ ‖errorOp U P m‖ := by
      calc ‖U * errorOp U P m‖ ≤ ‖U‖ * ‖errorOp U P m‖ := norm_mul_le _ _
        _ ≤ 1 * ‖errorOp U P m‖ := by gcongr
        _ = ‖errorOp U P m‖ := one_mul _
    calc ‖U * errorOp U P m + ((1 - P) * U * P) * ((coarsePredictor U P) ^ m * P)‖
        ≤ ‖U * errorOp U P m‖ + ‖((1 - P) * U * P) * ((coarsePredictor U P) ^ m * P)‖ :=
          norm_add_le _ _
      _ ≤ ‖errorOp U P m‖ + closureDefect U P := add_le_add hUE hδ
      _ ≤ m * closureDefect U P + closureDefect U P := by gcongr
      _ = (m + 1 : ℕ) * closureDefect U P := by push_cast; ring

/-- **Forecast form.** Conditional `m`-step prediction vs iterated coarse predictor:
`‖P U^m P - A^m P‖ ≤ m δ`. -/
theorem statistical_forecast_horizon (hU : ‖U‖ ≤ 1) (hP : ‖P‖ ≤ 1) (hPP : P * P = P)
    (m : ℕ) :
    ‖P * (U ^ m * P) - (coarsePredictor U P) ^ m * P‖ ≤ m * closureDefect U P := by
  have h : P * (U ^ m * P) - (coarsePredictor U P) ^ m * P = P * errorOp U P m := by
    simp only [errorOp, mul_sub, proj_mul_pow_predictor_mul_proj hPP]
  rw [h]
  calc ‖P * errorOp U P m‖ ≤ ‖P‖ * ‖errorOp U P m‖ := norm_mul_le _ _
    _ ≤ 1 * (m * closureDefect U P) := by gcongr; exact statistical_horizon hU hP hPP m
    _ = m * closureDefect U P := one_mul _

/-- Zero closure defect forces exact statistical forecasting at every horizon. -/
theorem exact_forecast_of_defect_zero (hU : ‖U‖ ≤ 1) (hP : ‖P‖ ≤ 1) (hPP : P * P = P)
    (hδ : closureDefect U P = 0) (m : ℕ) :
    P * (U ^ m * P) = (coarsePredictor U P) ^ m * P := by
  have h := statistical_forecast_horizon hU hP hPP m
  rw [hδ, mul_zero] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

end Main

/-! ## Regression test: averaged one-step statistics do not compose

The deterministic four-cycle on `Fin 4` with cells `{0,1}` and `{2,3}`. -/

section FourCycle

/-- One-step averaged transition matrix of the four-cycle over the two cells. -/
def K₁ : Matrix (Fin 2) (Fin 2) ℚ := !![1/2, 1/2; 1/2, 1/2]

/-- Two-step averaged transition matrix of the four-cycle over the two cells. -/
def K₂ : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 1, 0]

/-- `K₂ ≠ K₁ * K₁`: the coarse one-step law is not autonomous. -/
theorem fourCycle_K2_ne_K1_sq : K₂ ≠ K₁ * K₁ := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp [K₁, K₂, Matrix.mul_apply, Fin.sum_univ_two] at this
  norm_num at this

/-- The one-step matrix is what averaging the four-cycle over the cells produces:
each cell sends half its mass to itself and half to the other cell. -/
theorem fourCycle_K1_rows : ∀ i, K₁ i 0 + K₁ i 1 = 1 := by
  intro i; fin_cases i <;> simp [K₁] <;> norm_num

end FourCycle

end SGC.Bridge.StatisticalHorizon

end
