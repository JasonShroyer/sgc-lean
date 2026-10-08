/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# No-go: a level that erases a decision-relevant distinction cannot host an optimal agent

The negative clause of the emergent-intelligence hypothesis, in its finite exact form. A *coarse
policy* is one that acts on the level: it assigns the same action to micro-states in the same block.
If two micro-states `x ~ y` in one block have *different* strict optimal actions (with margins
`m x, m y > 0`), then every coarse policy has regret at least `m x` at `x` or at least `m y` at `y`
(`coarse_policy_regret`). Under any weighting that puts mass on both, the expected regret is at least
`min (w x * m x) (w y * m y)` (`coarse_policy_expected_regret`).

This is the formal content of "intelligence is not emergent at this level": no agent confined to the
level is near-optimal, however it computes. Near-optimality then requires a finer level — exactly the
"look" lever of `CoarseFloor`. It is the finite-state form of π*-irrelevance in state abstraction
(Li–Walsh–Littman 2006): a partition that is not π*-irrelevant has positive value loss for every
abstract policy.
-/

namespace SGC.Bridge.NoGo

variable {V α : Type*}

/-- Regret of a policy `σ` at micro-state `z`, relative to the optimal action `astar z`. -/
def regret (u : α → V → ℝ) (astar : V → α) (σ : V → α) (z : V) : ℝ :=
  u (astar z) z - u (σ z) z

/-- Strict optimality with margin: every non-optimal action loses at least `m z` at `z`. -/
def HasMargin (u : α → V → ℝ) (astar : V → α) (m : V → ℝ) : Prop :=
  ∀ z a, a ≠ astar z → m z ≤ u (astar z) z - u a z

lemma regret_nonneg (u : α → V → ℝ) (astar : V → α) (m : V → ℝ) (hm : ∀ z, 0 ≤ m z)
    (h : HasMargin u astar m) (σ : V → α) (z : V) : 0 ≤ regret u astar σ z := by
  unfold regret
  by_cases hz : σ z = astar z
  · rw [hz]; linarith
  · exact le_trans (hm z) (h z (σ z) hz)

/-- **No-go.** If `x` and `y` receive the same action under `σ` (they lie in one block of the level)
but have different optimal actions, then `σ` has regret at least `m x` at `x` or at least `m y` at `y`. -/
theorem coarse_policy_regret (u : α → V → ℝ) (astar : V → α) (m : V → ℝ) (h : HasMargin u astar m)
    (σ : V → α) (x y : V) (hblock : σ x = σ y) (hdiff : astar x ≠ astar y) :
    m x ≤ regret u astar σ x ∨ m y ≤ regret u astar σ y := by
  by_cases hx : σ x = astar x
  · right
    have hy : σ y ≠ astar y := by
      intro hy; apply hdiff; rw [← hx, hblock, hy]
    exact h y (σ y) hy
  · left
    exact h x (σ x) hx

/-- **Expected form.** For nonnegative weights on `x` and `y`, the weighted regret is at least
`min (w x * m x) (w y * m y)`. -/
theorem coarse_policy_expected_regret (u : α → V → ℝ) (astar : V → α) (m : V → ℝ)
    (hm : ∀ z, 0 ≤ m z) (h : HasMargin u astar m) (σ : V → α) (x y : V) (hblock : σ x = σ y)
    (hdiff : astar x ≠ astar y) (w : V → ℝ) (hw : ∀ z, 0 ≤ w z) :
    min (w x * m x) (w y * m y) ≤ w x * regret u astar σ x + w y * regret u astar σ y := by
  have hrx := regret_nonneg u astar m hm h σ x
  have hry := regret_nonneg u astar m hm h σ y
  rcases coarse_policy_regret u astar m h σ x y hblock hdiff with hx | hy
  · calc min (w x * m x) (w y * m y) ≤ w x * m x := min_le_left _ _
      _ ≤ w x * regret u astar σ x := mul_le_mul_of_nonneg_left hx (hw x)
      _ ≤ w x * regret u astar σ x + w y * regret u astar σ y := by
          have := mul_nonneg (hw y) hry; linarith
  · calc min (w x * m x) (w y * m y) ≤ w y * m y := min_le_right _ _
      _ ≤ w y * regret u astar σ y := mul_le_mul_of_nonneg_left hy (hw y)
      _ ≤ w x * regret u astar σ x + w y * regret u astar σ y := by
          have := mul_nonneg (hw x) hrx; linarith

end SGC.Bridge.NoGo
