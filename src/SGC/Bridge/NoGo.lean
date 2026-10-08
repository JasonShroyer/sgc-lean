/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Ring.Finset

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


/-!
## The representation-dependent regret floor (one-step, finite)

The two-state obstruction above is worst-case. The deployment-sensitive version: for a representation
`z : V → B`, weights `μ`, and utilities `u`, the best expected utility achievable by **any** policy that
acts through `z` — deterministic or randomized — is `∑ b, max_a U b a` where
`U b a = ∑_{x : z x = b} μ x · u x a` is the block utility. Hence the minimal regret of a `z`-policy is
`R*(z) = ∑ x, μ x · max_a u x a − ∑ b, max_a U b a`, exactly, and it is attained by the per-block
argmax. Randomization within a block cannot beat the best single action (a convex combination is at
most the maximum). History-dependent policies are *not* covered: they are a different information
structure and need the multi-step setting.
-/

section RegretFloor

open Finset

variable {B : Type*} [Fintype V] [Fintype B] [DecidableEq B] [Fintype α] [Nonempty α]

/-- Block utility of action `a` in block `b`: the `μ`-weighted utility over the fiber. -/
def blockU (z : V → B) (μ : V → ℝ) (u : V → α → ℝ) (b : B) (a : α) : ℝ :=
  ∑ x ∈ univ.filter (fun x => z x = b), μ x * u x a

/-- A policy acting through `z` decomposes fiberwise. -/
theorem utility_fiberwise (z : V → B) (μ : V → ℝ) (u : V → α → ℝ) (s : B → α) :
    ∑ x, μ x * u x (s (z x)) = ∑ b, blockU z μ u b (s b) := by
  unfold blockU
  rw [← Finset.sum_fiberwise (s := univ) (g := z) (f := fun x => μ x * u x (s (z x)))]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro x hx
  rw [(Finset.mem_filter.mp hx).2]

/-- The per-block argmax exists (finite, nonempty action set). -/
theorem exists_block_argmax (z : V → B) (μ : V → ℝ) (u : V → α → ℝ) :
    ∃ sopt : B → α, ∀ b a, blockU z μ u b a ≤ blockU z μ u b (sopt b) := by
  have h : ∀ b, ∃ aopt, ∀ a, blockU z μ u b a ≤ blockU z μ u b aopt := by
    intro b
    obtain ⟨aopt, -, hmax⟩ := Finset.exists_max_image univ (fun a => blockU z μ u b a) univ_nonempty
    exact ⟨aopt, fun a => hmax a (mem_univ a)⟩
  choose sopt hs using h
  exact ⟨sopt, hs⟩

/-- **Deterministic floor.** Every policy acting through `z` is dominated by the per-block argmax. -/
theorem coarse_policy_le_argmax (z : V → B) (μ : V → ℝ) (u : V → α → ℝ) (sopt : B → α)
    (hs : ∀ b a, blockU z μ u b a ≤ blockU z μ u b (sopt b)) (s : B → α) :
    ∑ x, μ x * u x (s (z x)) ≤ ∑ x, μ x * u x (sopt (z x)) := by
  rw [utility_fiberwise, utility_fiberwise]
  exact Finset.sum_le_sum (fun b _ => hs b (s b))

/-- **Randomized floor.** A randomized block policy `p b a` (nonnegative, summing to one in each block)
cannot beat the per-block argmax either. -/
theorem randomized_coarse_policy_le_argmax (z : V → B) (μ : V → ℝ) (u : V → α → ℝ) (sopt : B → α)
    (hs : ∀ b a, blockU z μ u b a ≤ blockU z μ u b (sopt b)) (p : B → α → ℝ)
    (hp0 : ∀ b a, 0 ≤ p b a) (hp1 : ∀ b, ∑ a, p b a = 1) :
    ∑ b, ∑ a, p b a * blockU z μ u b a ≤ ∑ b, blockU z μ u b (sopt b) := by
  apply Finset.sum_le_sum
  intro b _
  calc ∑ a, p b a * blockU z μ u b a ≤ ∑ a, p b a * blockU z μ u b (sopt b) :=
        Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hs b a) (hp0 b a))
    _ = (∑ a, p b a) * blockU z μ u b (sopt b) := by rw [Finset.sum_mul]
    _ = blockU z μ u b (sopt b) := by rw [hp1 b, one_mul]

/-- The regret floor of a representation: full-information optimum minus the best `z`-policy. -/
def regretFloor (z : V → B) (μ : V → ℝ) (u : V → α → ℝ) (astar : V → α) (sopt : B → α) : ℝ :=
  ∑ x, μ x * u x (astar x) - ∑ x, μ x * u x (sopt (z x))

/-- **Exact characterization.** Every policy acting through `z` has regret at least `regretFloor`,
and the per-block argmax attains it. -/
theorem regret_ge_floor (z : V → B) (μ : V → ℝ) (u : V → α → ℝ) (astar : V → α) (sopt : B → α)
    (hs : ∀ b a, blockU z μ u b a ≤ blockU z μ u b (sopt b)) (s : B → α) :
    regretFloor z μ u astar sopt ≤ ∑ x, μ x * u x (astar x) - ∑ x, μ x * u x (s (z x)) := by
  unfold regretFloor
  have := coarse_policy_le_argmax z μ u sopt hs s
  linarith

end RegretFloor

end SGC.Bridge.NoGo
