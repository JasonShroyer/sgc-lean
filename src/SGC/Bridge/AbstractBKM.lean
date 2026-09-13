/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Abstract BKM: the L0 budget-continuation theorem

Level L0 of the BKM ladder (`docs/bkm-formalization-design.md`, 2026-08-26, revised
2026-09-12). Everything here is finite-dimensional-agnostic real analysis in a normed
space: a trajectory `x : ℝ → E` whose right derivative is controlled by a scalar
*budget density* `W` times its own norm,

    ‖x'(t)‖ ≤ W(t) ‖x(t)‖,

satisfies the Gronwall-with-time-dependent-rate bound

    ‖x(t)‖ ≤ exp (∫₀ᵗ W) ‖x(0)‖.

Consequently a *finite accumulated budget* `∫₀ᵀ W ≤ M` forces `‖x‖ ≤ e^M ‖x 0‖` on
`[0, T]`, and any norm excursion beyond that ceiling forces the budget past `M`. This is
the abstract shape shared by

* the SGC Kernel-Horizon bounds (`error ≤ n ‖C‖`, `≤ ‖C‖ / (1 − α)`): a validity
  horizon is a finite budget;
* the Beale–Kato–Majda continuation criterion for 3D Euler, where the budget density is
  `‖curl u(t)‖_L∞` and the controlled quantity is a Sobolev norm of `u`.

## What is and is not claimed

* PROVEN (kernel, no axioms beyond the classical three): the theorems below, for an
  arbitrary real normed space `E`, arbitrary continuous `W : ℝ → ℝ`, and any `x` with a
  right derivative on `[0, T)` satisfying the pointwise bound.
* NOT CLAIMED: any statement about the Euler or Navier–Stokes equations. Instantiating
  `x`, `W` with a Galerkin-truncated fluid and a vorticity budget, with the constant `1`
  in `‖x'‖ ≤ W ‖x‖` replaced by the BKM log-interpolation, is level L1–L3 of the ladder
  and is not done here. The resemblance to BKM is the reason for the module name, not a
  theorem in it.
* NOT CLAIMED: any relation between this `W` and the SGC defect `‖PL − QP‖`. That
  identification is the L1 obligation `𝔇_{π,N} ≥ c ‖ω_N‖_∞ − r_N` and is open.

The external self-assessed Lean artifact `openai/NavierStokesAndEuler` (2026-09-08)
proves BKM-shaped budget divergence for a concrete Euler datum; nothing from it is
imported or assumed here.
-/

noncomputable section

namespace SGC.Bridge.AbstractBKM

open Set Real intervalIntegral MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The accumulated budget `∫₀ᵗ W` of a budget density `W`. -/
def budget (W : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, W s

@[simp] lemma budget_zero (W : ℝ → ℝ) : budget W 0 = 0 := by
  simp [budget]

/-- The accumulated budget of a continuous density is differentiable with derivative the
density. -/
lemma hasDerivAt_budget {W : ℝ → ℝ} (hW : Continuous W) (t : ℝ) :
    HasDerivAt (budget W) (W t) t :=
  integral_hasDerivAt_right (hW.intervalIntegrable 0 t)
    (hW.stronglyMeasurableAtFilter volume _) hW.continuousAt

/-- Strictly fenced Gronwall step: for every `ε > 0`, the trajectory stays under the
barrier `exp (budget W t) * (‖x 0‖ + ε * exp t)`. The `ε * exp t` term makes the barrier
strictly outrun the trajectory at contact, which is what the fencing lemma requires. -/
theorem norm_le_barrier_of_budget_control
    {x x' : ℝ → E} {W : ℝ → ℝ} {T : ℝ} (hW : Continuous W)
    (hx : ContinuousOn x (Icc 0 T))
    (hx' : ∀ t ∈ Ico 0 T, HasDerivWithinAt x (x' t) (Ici t) t)
    (bound : ∀ t ∈ Ico 0 T, ‖x' t‖ ≤ W t * ‖x t‖)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ t ∈ Icc 0 T, ‖x t‖ ≤ exp (budget W t) * (‖x 0‖ + ε * exp t) := by
  set B : ℝ → ℝ := fun t => exp (budget W t) * (‖x 0‖ + ε * exp t) with hBdef
  set B' : ℝ → ℝ := fun t =>
    exp (budget W t) * W t * (‖x 0‖ + ε * exp t) + exp (budget W t) * (ε * exp t) with hB'def
  have hB : ∀ t, HasDerivAt B (B' t) t := by
    intro t
    have h1 : HasDerivAt (fun u => exp (budget W u)) (exp (budget W t) * W t) t :=
      (hasDerivAt_budget hW t).exp
    have h2 : HasDerivAt (fun u => ‖x 0‖ + ε * exp u) (ε * exp t) t :=
      ((hasDerivAt_exp t).const_mul ε).const_add ‖x 0‖
    simpa [hBdef, hB'def] using h1.mul h2
  have ha : ‖x 0‖ ≤ B 0 := by
    simp only [hBdef, budget_zero, exp_zero, one_mul, mul_one]
    linarith
  have hbound : ∀ t ∈ Ico 0 T, ‖x t‖ = B t → ‖x' t‖ < B' t := by
    intro t ht hxB
    calc ‖x' t‖ ≤ W t * ‖x t‖ := bound t ht
      _ = exp (budget W t) * W t * (‖x 0‖ + ε * exp t) := by rw [hxB, hBdef]; ring
      _ < B' t := by
        simp only [hB'def]
        exact lt_add_of_pos_right _ (by positivity)
  intro t ht
  exact image_norm_le_of_norm_deriv_right_lt_deriv_boundary hx hx' ha hB hbound ht

/-- **L0 budget–Gronwall theorem.** If the right derivative of `x` is controlled by the
budget density times the norm, then the norm is controlled by the exponential of the
accumulated budget. -/
theorem norm_le_exp_budget
    {x x' : ℝ → E} {W : ℝ → ℝ} {T : ℝ} (hW : Continuous W)
    (hx : ContinuousOn x (Icc 0 T))
    (hx' : ∀ t ∈ Ico 0 T, HasDerivWithinAt x (x' t) (Ici t) t)
    (bound : ∀ t ∈ Ico 0 T, ‖x' t‖ ≤ W t * ‖x t‖) :
    ∀ t ∈ Icc 0 T, ‖x t‖ ≤ exp (budget W t) * ‖x 0‖ := by
  intro t ht
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hpos : 0 < exp (budget W t) * exp t := by positivity
  have h := norm_le_barrier_of_budget_control hW hx hx' bound
    (ε := δ / (exp (budget W t) * exp t)) (div_pos hδ hpos) t ht
  have hne : exp (budget W t) * exp t ≠ 0 := hpos.ne'
  calc ‖x t‖ ≤ exp (budget W t) * (‖x 0‖ + δ / (exp (budget W t) * exp t) * exp t) := h
    _ = exp (budget W t) * ‖x 0‖ + δ := by field_simp

/-- **Finite budget ⇒ bounded evolution.** A budget ceiling `M` on `[0, T]` yields the
uniform bound `‖x t‖ ≤ e^M ‖x 0‖`. This is the continuation half of a BKM-type
criterion in abstract form. -/
theorem bounded_of_budget_le
    {x x' : ℝ → E} {W : ℝ → ℝ} {T M : ℝ} (hW : Continuous W)
    (hx : ContinuousOn x (Icc 0 T))
    (hx' : ∀ t ∈ Ico 0 T, HasDerivWithinAt x (x' t) (Ici t) t)
    (bound : ∀ t ∈ Ico 0 T, ‖x' t‖ ≤ W t * ‖x t‖)
    (hM : ∀ t ∈ Icc 0 T, budget W t ≤ M) :
    ∀ t ∈ Icc 0 T, ‖x t‖ ≤ exp M * ‖x 0‖ := by
  intro t ht
  calc ‖x t‖ ≤ exp (budget W t) * ‖x 0‖ := norm_le_exp_budget hW hx hx' bound t ht
    _ ≤ exp M * ‖x 0‖ := by gcongr; exact hM t ht

/-- **Excursion ⇒ budget spent.** Contrapositive of `bounded_of_budget_le`: if the norm
ever exceeds `e^M ‖x 0‖` on `[0, T]`, the accumulated budget exceeds `M` somewhere on
`[0, T]`. This is the abstract form of "blowup requires budget divergence". -/
theorem exists_budget_gt_of_norm_gt
    {x x' : ℝ → E} {W : ℝ → ℝ} {T M : ℝ} (hW : Continuous W)
    (hx : ContinuousOn x (Icc 0 T))
    (hx' : ∀ t ∈ Ico 0 T, HasDerivWithinAt x (x' t) (Ici t) t)
    (bound : ∀ t ∈ Ico 0 T, ‖x' t‖ ≤ W t * ‖x t‖)
    (hexc : ∃ t ∈ Icc 0 T, exp M * ‖x 0‖ < ‖x t‖) :
    ∃ t ∈ Icc 0 T, M < budget W t := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨t, ht, hlt⟩ := hexc
  exact absurd (bounded_of_budget_le hW hx hx' bound hcon t ht) (not_le.mpr hlt)

end SGC.Bridge.AbstractBKM

end
