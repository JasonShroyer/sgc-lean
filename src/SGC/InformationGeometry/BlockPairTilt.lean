/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Directional closure defect of a block-pair tilt

Finite state space `V`, partition `q : V → β`, stationary weights `π > 0`,
block exit rates `R x C`. The stationary block average is
`Rbar A C = (Σ_{x ∈ A} π x R x C) / π(A)`, the residual is `res = R - Rbar`,
and for a block-pair tilt `b : β → β → ℝ` the directional closure defect is

  `δ x = Σ_C res x C * b (q x) C`.

## Main results

* `surrogate_error_eq` — replacing exit rates by their block averages in a
  block-pair-tilt step score changes it by exactly `-δ x`.
* `delta_mean_zero` — `Σ_x π x δ x = 0`.
* `delta_sq_le` — `δ x ² ≤ (Σ_C b (q x) C ²) · Σ_C res x C ²` (Cauchy–Schwarz).
* `delta_energy_le` — `Σ π δ² ≤ Bmax · D_π²` whenever every block row of `b`
  has squared norm at most `Bmax`, where `D_π² = Σ_x π x Σ_C res x C ²`.

Together with `ScoreProjection.fisherLoss_eq_condVar`, these are the
algebraic ingredients of the directional closure bound for Markov path
spaces; the path-space assembly itself is not in this file.
-/

noncomputable section

namespace SGC.InformationGeometry.BlockPairTilt

open Finset

set_option linter.unusedSectionVars false

variable {V β : Type*} [Fintype V] [Fintype β] [DecidableEq β]
variable (q : V → β) (π : V → ℝ) (R : V → β → ℝ) (b : β → β → ℝ)

/-- Stationary mass of a block. -/
def blockMass (A : β) : ℝ := ∑ x ∈ univ.filter (fun x => q x = A), π x

/-- Stationary block average of exit rates. -/
def Rbar (A C : β) : ℝ := (∑ x ∈ univ.filter (fun x => q x = A), π x * R x C) / blockMass q π A

/-- Residual exit rates. -/
def res (x : V) (C : β) : ℝ := R x C - Rbar q π R (q x) C

/-- Directional closure defect. -/
def delta (x : V) : ℝ := ∑ C, res q π R x C * b (q x) C

/-- Closure defect `D_π²`. -/
def defectSq : ℝ := ∑ x, π x * ∑ C, res q π R x C ^ 2

/-- Step score of a block-pair tilt given exit rates `R'` (with `R = R'` this
is the softmax score; with `R' = Rbar` it is the block-measurable surrogate). -/
def stepScore (R' : V → β → ℝ) (x : V) (C₁ : β) : ℝ :=
  b (q x) C₁ - ∑ C, R' x C * b (q x) C

theorem surrogate_error_eq (x : V) (C₁ : β) :
    stepScore q b R x C₁ - stepScore q b (fun x C => Rbar q π R (q x) C) x C₁
      = - delta q π R b x := by
  unfold stepScore delta res
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

theorem res_block_mean_zero (hπ : ∀ x, 0 < π x) (A C : β) :
    ∑ x ∈ univ.filter (fun x => q x = A), π x * res q π R x C = 0 := by
  have hmem : ∀ x ∈ univ.filter (fun x => q x = A),
      π x * res q π R x C = π x * R x C - π x * Rbar q π R A C := by
    intro x hx
    unfold res
    rw [(Finset.mem_filter.mp hx).2]
    ring
  rw [Finset.sum_congr rfl hmem, Finset.sum_sub_distrib, ← Finset.sum_mul]
  change _ - blockMass q π A * Rbar q π R A C = 0
  rcases eq_or_ne (blockMass q π A) 0 with h0 | h0
  · have hempty : univ.filter (fun x => q x = A) = ∅ := by
      by_contra hne
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have : 0 < blockMass q π A := Finset.sum_pos (fun x _ => hπ x) ⟨x, hx⟩
      linarith
    simp [hempty, h0]
  · unfold Rbar
    field_simp
    ring

theorem delta_mean_zero (hπ : ∀ x, 0 < π x) : ∑ x, π x * delta q π R b x = 0 := by
  unfold delta
  have hswap : ∑ x, π x * ∑ C, res q π R x C * b (q x) C
      = ∑ A, ∑ C, b A C * ∑ x ∈ univ.filter (fun x => q x = A), π x * res q π R x C := by
    rw [← Finset.sum_fiberwise univ q]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    have hin : ∀ x ∈ univ.filter (fun x => q x = A),
        π x * ∑ C, res q π R x C * b (q x) C = ∑ C, b A C * (π x * res q π R x C) := by
      intro x hx
      rw [(Finset.mem_filter.mp hx).2, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun C _ => by ring)
    rw [Finset.sum_congr rfl hin, Finset.sum_comm]
    exact Finset.sum_congr rfl (fun C _ => by rw [Finset.mul_sum])
  rw [hswap]
  refine Finset.sum_eq_zero (fun A _ => Finset.sum_eq_zero (fun C _ => ?_))
  rw [res_block_mean_zero q π R hπ A C, mul_zero]

theorem delta_sq_le (x : V) :
    delta q π R b x ^ 2 ≤ (∑ C, b (q x) C ^ 2) * ∑ C, res q π R x C ^ 2 := by
  unfold delta
  calc (∑ C, res q π R x C * b (q x) C) ^ 2
      ≤ (∑ C, res q π R x C ^ 2) * ∑ C, b (q x) C ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq univ _ _
    _ = _ := mul_comm _ _

theorem delta_energy_le (hπ : ∀ x, 0 < π x) {Bmax : ℝ}
    (hB : ∀ A, ∑ C, b A C ^ 2 ≤ Bmax) :
    ∑ x, π x * delta q π R b x ^ 2 ≤ Bmax * defectSq q π R := by
  unfold defectSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun x _ => ?_)
  have hr : 0 ≤ ∑ C, res q π R x C ^ 2 := Finset.sum_nonneg (fun C _ => sq_nonneg _)
  have h1 := delta_sq_le q π R b x
  have h2 : (∑ C, b (q x) C ^ 2) * ∑ C, res q π R x C ^ 2 ≤ Bmax * ∑ C, res q π R x C ^ 2 :=
    mul_le_mul_of_nonneg_right (hB (q x)) hr
  have := mul_le_mul_of_nonneg_left (h1.trans h2) (hπ x).le
  linarith

end SGC.InformationGeometry.BlockPairTilt
