/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The anchor certificate with partial witness coverage (P33)

The executable anchor certificate (0100, 0113–0115) scores an input with no training witness on its block as an error
of one. This file states that rule as a theorem: for a weight `w ≥ 0`, a predictor `f`, ground truth `y`, and a partial
witness map `A : α → Option α` along which `y` is invariant,

`Σ w·1[f ≠ y] ≤ Σ w·1[no witness] + Σ w·1[witness ∧ f x ≠ f (A x)] + Σ w·1[witness ∧ f (A x) ≠ y (A x)]`.

The unseen-orbit mass is the first term — explicit in the certificate, not discharged by assumption. When every input
has a witness the first term vanishes and the statement reduces to the anchor bound of `Adequacy` (P8).
-/

namespace SGC.Bridge.AnchorCoverage

open Finset

variable {α β : Type*} [Fintype α] [DecidableEq β]

/-- Indicator of error. -/
def err (f y : α → β) (x : α) : ℝ := if f x = y x then 0 else 1

/-- Indicator of "no witness". -/
def noWitness (A : α → Option α) (x : α) : ℝ := if (A x).isNone then 1 else 0

/-- Indicator of disagreement with the witness (zero when there is none). -/
def witnessDisagree (f : α → β) (A : α → Option α) (x : α) : ℝ :=
  match A x with
  | none => 0
  | some a => if f x = f a then 0 else 1

/-- Indicator of the witness being wrong (zero when there is none). -/
def witnessError (f y : α → β) (A : α → Option α) (x : α) : ℝ :=
  match A x with
  | none => 0
  | some a => if f a = y a then 0 else 1

theorem pointwise (f y : α → β) (A : α → Option α) (hinv : ∀ x a, A x = some a → y a = y x) (x : α) :
    err f y x ≤ noWitness A x + witnessDisagree f A x + witnessError f y A x := by
  unfold err noWitness witnessDisagree witnessError
  cases h : A x with
  | none =>
    simp only [h, Option.isNone_none, if_true]
    split_ifs <;> norm_num
  | some a =>
    have hy := hinv x a h
    simp only [h, Option.isNone_some, Bool.false_eq_true, if_false, zero_add]
    by_cases h1 : f x = y x
    · simp only [h1, if_true]
      split_ifs <;> norm_num
    · simp only [h1, if_false]
      by_cases h2 : f x = f a
      · have h3 : ¬ f a = y a := fun h3 => h1 (h2.trans (h3.trans hy))
        simp only [h2, h3, if_true, if_false]; norm_num
      · simp only [h2, if_false]
        split_ifs <;> norm_num

/-- **P33.** The weighted anchor certificate with the unseen-orbit mass explicit. -/
theorem anchor_bound_with_coverage (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) (f y : α → β) (A : α → Option α)
    (hinv : ∀ x a, A x = some a → y a = y x) :
    ∑ x, w x * err f y x ≤
      ∑ x, w x * noWitness A x + ∑ x, w x * witnessDisagree f A x + ∑ x, w x * witnessError f y A x := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  have := pointwise f y A hinv x
  calc w x * err f y x ≤ w x * (noWitness A x + witnessDisagree f A x + witnessError f y A x) :=
        mul_le_mul_of_nonneg_left this (hw x)
    _ = w x * noWitness A x + w x * witnessDisagree f A x + w x * witnessError f y A x := by ring

/-- With full coverage the first term vanishes. -/
theorem noWitness_eq_zero_of_total (A : α → Option α) (htot : ∀ x, (A x).isSome) (x : α) : noWitness A x = 0 := by
  unfold noWitness
  have : ¬ (A x).isNone := by
    have h := htot x
    cases hA : A x <;> simp_all
  simp [this]

end SGC.Bridge.AnchorCoverage
