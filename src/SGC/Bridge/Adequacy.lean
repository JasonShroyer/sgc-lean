/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Adequacy from relational consistency and anchors

A macro-description is *adequate* only relative to a task, a deployment distribution, and a budget.
This file proves the two elementary inequalities that turn a label-free consistency statistic into a
certificate, over a finite input type `X` with a weight (probability mass) `w : X → ℝ`:

* **Anchor bound** (`error_le_contradiction_add_anchor_error`). If every input `x` has an anchor
  `A x` with the same label (`y (A x) = y x`), then
  `P[f X ≠ y X] ≤ P[f X ≠ f (A X)] + P[f (A X) ≠ y (A X)]`:
  deployment error is at most the contradiction with the anchor plus the anchor's own error. The
  first term is label-free; the second is measured where labels exist (the training set). This is a
  usable upper bound on held-out error from training labels and unlabeled consistency.

* **Contradiction lower bound** (`contradiction_le_two_mul_error`). If `T` is a weight-preserving
  bijection and the label is `T`-invariant, then
  `P[f (T X) ≠ f X] ≤ 2 · P[f X ≠ y X]`:
  half the contradiction rate is a lower bound on the error. High contradiction certifies a problem;
  low contradiction does not certify correctness (the error can hide where `f` and `f ∘ T` agree).

* **Selector soundness** (`selector_sound`). Given a finite family of candidate repairs with valid
  per-candidate error bounds, a selector that returns a candidate whose bound is below tolerance
  returns a candidate whose true error is below tolerance. A modest, defensible first theorem about an
  actual selector; no optimality is claimed.

All sums are finite; `ind p` is the real indicator of a decidable proposition.
-/

noncomputable section

namespace SGC.Bridge.Adequacy

open Finset

variable {X Y : Type*} [Fintype X]

/-- Real indicator of a proposition. -/
def ind (p : Prop) [Decidable p] : ℝ := if p then 1 else 0

lemma ind_nonneg (p : Prop) [Decidable p] : 0 ≤ ind p := by
  unfold ind; split_ifs <;> norm_num

lemma ind_le_one (p : Prop) [Decidable p] : ind p ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

/-- Pointwise: an error at `x` is a contradiction with the anchor or an error shared with it. -/
lemma ind_err_le (f y : X → Y) (A : X → X) [DecidableEq Y] (hA : ∀ x, y (A x) = y x) (x : X) :
    ind (f x ≠ y x) ≤ ind (f x ≠ f (A x)) + ind (f (A x) ≠ y (A x)) := by
  unfold ind
  split_ifs with h0 h1 h3 <;> try norm_num
  all_goals (push_neg at *; exact absurd (by rw [‹f x = f (A x)›, ‹f (A x) = y (A x)›, hA]) h0)

/-- Weighted probability of a predicate. -/
def prob (w : X → ℝ) (p : X → Prop) [DecidablePred p] : ℝ := ∑ x, w x * ind (p x)

/-- **Anchor bound.** -/
theorem error_le_contradiction_add_anchor_error (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (f y : X → Y) (A : X → X) [DecidableEq Y] (hA : ∀ x, y (A x) = y x) :
    prob w (fun x => f x ≠ y x) ≤
      prob w (fun x => f x ≠ f (A x)) + prob w (fun x => f (A x) ≠ y (A x)) := by
  unfold prob
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (ind_err_le f y A hA x) (hw x)

/-- Pointwise: a contradiction between `x` and `T x` needs an error at one of them when the label is
`T`-invariant. -/
lemma ind_contra_le (f y : X → Y) (T : X → X) [DecidableEq Y] (hy : ∀ x, y (T x) = y x) (x : X) :
    ind (f (T x) ≠ f x) ≤ ind (f (T x) ≠ y (T x)) + ind (f x ≠ y x) := by
  unfold ind
  split_ifs with h0 h1 h2 <;> try norm_num
  all_goals (push_neg at *; exact absurd (by rw [‹f (T x) = y (T x)›, hy, ‹f x = y x›]) h0)

/-- **Contradiction lower bound.** For a weight-preserving bijection `T` and a `T`-invariant label,
the contradiction rate is at most twice the error rate. -/
theorem contradiction_le_two_mul_error (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (f y : X → Y)
    (T : X ≃ X) [DecidableEq Y] (hwT : ∀ x, w (T x) = w x) (hy : ∀ x, y (T x) = y x) :
    prob w (fun x => f (T x) ≠ f x) ≤ 2 * prob w (fun x => f x ≠ y x) := by
  unfold prob
  have hstep : ∑ x, w x * ind (f (T x) ≠ f x) ≤
      ∑ x, w x * ind (f (T x) ≠ y (T x)) + ∑ x, w x * ind (f x ≠ y x) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (ind_contra_le f y T hy x) (hw x)
  have hre : ∑ x, w x * ind (f (T x) ≠ y (T x)) = ∑ x, w x * ind (f x ≠ y x) := by
    calc ∑ x, w x * ind (f (T x) ≠ y (T x)) = ∑ x, w (T x) * ind (f (T x) ≠ y (T x)) := by
          apply Finset.sum_congr rfl; intro x _; rw [hwT]
      _ = ∑ x, w x * ind (f x ≠ y x) := T.sum_comp (fun x => w x * ind (f x ≠ y x))
  linarith

/-- **Selector soundness.** A finite family of candidates with valid error bounds: returning a
candidate whose bound is at most the tolerance returns a candidate whose true error is at most the
tolerance. -/
theorem selector_sound {ι : Type*} (err bound : ι → ℝ) (hvalid : ∀ i, err i ≤ bound i)
    (tol : ℝ) (i : ι) (hsel : bound i ≤ tol) : err i ≤ tol :=
  le_trans (hvalid i) hsel

end SGC.Bridge.Adequacy
