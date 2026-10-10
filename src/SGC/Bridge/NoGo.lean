/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
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


/-!
## History sufficiency and the task-directed planner bound

Two of the three propositions the Q2 review asked for, in their finite exact forms.

**History sufficiency.** Let `ℓ h b` be the probability of observing the coarse history `h` given
that the present micro-state lies in block `b` — i.e. the likelihood of the history is
**block-constant** (it depends on the present micro-state only through its block). Then no policy
acting on the history can beat the best policy acting on the present block
(`history_value_le_block_value`): the history gain is zero. For a *reversible* stationary chain with a
lumpable partition the likelihood of the past coarse trajectory is block-constant (the reversed chain
is the same chain and is lumpable), which is why the symmetry quotients of decision 0102 showed exactly
zero gain. For a forward-lumpable but *non-reversible* chain the likelihood need not be block-constant
and history can recover erased information (the shift-register counterexample) — the hypothesis of
this theorem is precisely what fails there.

**Task-directed planner bound.** If a planner's estimated values `v̂ a` are within `D` of the exact
coarse-information values `v a` for every action, then choosing the planner's argmax loses at most
`2 D` against the best action on the same information (`argmax_perturbation`). With
`v a = (P e^{tL} u_a)(b)` and `v̂ a = (e^{tPLP} P u_a)(b)` this bounds Gap 2 by twice the
task-directed predictive defect `D_U(P, t) = max_a ‖v_a − v̂_a‖_∞`.
-/

section HistoryAndPlanner

open Finset

variable {B Hs : Type*} [Fintype V] [Fintype B] [DecidableEq B] [Fintype α] [Fintype Hs]

/-- **History sufficiency.** With a block-constant history likelihood `ℓ` (nonnegative, summing to one
over histories for each block), every history-dependent policy `σ` is dominated by the per-block argmax. -/
theorem history_value_le_block_value (z : V → B) (μ : V → ℝ) (u : V → α → ℝ)
    (ℓ : Hs → B → ℝ) (hℓ0 : ∀ h b, 0 ≤ ℓ h b) (hℓ1 : ∀ b, ∑ h, ℓ h b = 1)
    (sopt : B → α) (hs : ∀ b a, blockU z μ u b a ≤ blockU z μ u b (sopt b)) (σ : Hs → α) :
    ∑ h, ∑ x, μ x * ℓ h (z x) * u x (σ h) ≤ ∑ b, blockU z μ u b (sopt b) := by
  have hfib : ∀ h : Hs, ∑ x, μ x * ℓ h (z x) * u x (σ h) = ∑ b, ℓ h b * blockU z μ u b (σ h) := by
    intro h
    unfold blockU
    rw [← Finset.sum_fiberwise (s := univ) (g := z) (f := fun x => μ x * ℓ h (z x) * u x (σ h))]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]; ring
  calc ∑ h, ∑ x, μ x * ℓ h (z x) * u x (σ h) = ∑ h, ∑ b, ℓ h b * blockU z μ u b (σ h) := by
        apply Finset.sum_congr rfl; intro h _; exact hfib h
    _ ≤ ∑ h, ∑ b, ℓ h b * blockU z μ u b (sopt b) := by
        apply Finset.sum_le_sum; intro h _
        apply Finset.sum_le_sum; intro b _
        exact mul_le_mul_of_nonneg_left (hs b (σ h)) (hℓ0 h b)
    _ = ∑ b, (∑ h, ℓ h b) * blockU z μ u b (sopt b) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro b _
        rw [Finset.sum_mul]
    _ = ∑ b, blockU z μ u b (sopt b) := by
        apply Finset.sum_congr rfl; intro b _
        rw [hℓ1 b, one_mul]

/-- **Argmax perturbation.** If every estimated value is within `D` of the true value, the estimated
argmax loses at most `2 D` against any action. -/
theorem argmax_perturbation (v vhat : α → ℝ) (D : ℝ) (hD : ∀ a, |v a - vhat a| ≤ D)
    (ahat : α) (hmax : ∀ a, vhat a ≤ vhat ahat) (a : α) : v a - v ahat ≤ 2 * D := by
  have h1 := abs_le.mp (hD a)
  have h2 := abs_le.mp (hD ahat)
  have h3 := hmax a
  linarith [h1.1, h1.2, h2.1, h2.2]

end HistoryAndPlanner


/-!
## Reusable valid certificates

Two certificates that a learner can hold for a whole task family after a one-time computation.

**Information certificate (P20).** For any block-level comparator `Ubar : B → α → ℝ` and any pointwise
deviation bound `dev x ≥ |U x a − Ubar (z x) a|`, the regret floor at the given utilities satisfies
`Σ_x μ x · U x (astar x) − Σ_b blockU b (sopt b) ≤ 2 Σ_x μ x · dev x`.
Taking `Ubar` to be the coarse model's prediction and `dev` the within-block deviation of the true
horizon-`n` utilities, bounded through the operator norms of `(1−P)K^n P` and `(1−P)K^n(1−P)`
(computed once), gives a valid, horizon-indexed information certificate at coarse cost per task.

**Estimated-margin certificate (P19).** If the *estimated* values have margin `m̂` at `â` and all contrast
errors are below `m̂`, then `â` is truly optimal: the planner's decision in that block costs nothing.
Blocks failing the test are charged the contrast bound (P16). This is the margin-aware planner
certificate, valid and computable from the coarse model's own values plus a reusable contrast bound.
-/

section Certificates

variable {B : Type*} [Fintype V] [Fintype B] [DecidableEq B] [Fintype α] [Nonempty α]

/-- **P20.** Regret floor ≤ twice the `μ`-weighted pointwise deviation from any block-level comparator. -/
theorem regret_floor_le_two_deviation (z : V → B) (μ : V → ℝ) (hμ : ∀ x, 0 ≤ μ x) (U : V → α → ℝ)
    (Ubar : B → α → ℝ) (dev : V → ℝ) (hdev : ∀ x a, |U x a - Ubar (z x) a| ≤ dev x)
    (astar : V → α) (hstar : ∀ x a, U x a ≤ U x (astar x))
    (sbar : B → α) (hbar : ∀ b a, Ubar b a ≤ Ubar b (sbar b))
    (sopt : B → α) (hs : ∀ b a, blockU z μ U b a ≤ blockU z μ U b (sopt b)) :
    ∑ x, μ x * U x (astar x) - ∑ b, blockU z μ U b (sopt b) ≤ 2 * ∑ x, μ x * dev x := by
  have h1 : ∑ x, μ x * U x (sbar (z x)) ≤ ∑ x, μ x * U x (sopt (z x)) :=
    coarse_policy_le_argmax z μ U sopt hs sbar
  have h2 : ∑ x, μ x * U x (sopt (z x)) = ∑ b, blockU z μ U b (sopt b) := utility_fiberwise z μ U sopt
  have hpt : ∀ x, U x (astar x) - U x (sbar (z x)) ≤ 2 * dev x := by
    intro x
    have ha := abs_le.mp (hdev x (astar x))
    have hb := abs_le.mp (hdev x (sbar (z x)))
    have hc := hbar (z x) (astar x)
    linarith [ha.1, ha.2, hb.1, hb.2]
  have h3 : ∑ x, μ x * U x (astar x) - ∑ x, μ x * U x (sbar (z x)) ≤ 2 * ∑ x, μ x * dev x := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    have := mul_le_mul_of_nonneg_left (hpt x) (hμ x)
    linarith [this]
  linarith

/-- **P19.** Estimated margin `m̂` at `â` plus contrast errors below `m̂` ⇒ `â` is truly optimal. -/
theorem argmax_preserved_of_estimated_margin (v vhat : α → ℝ) (ahat : α) (mhat : ℝ)
    (hm : ∀ a, a ≠ ahat → mhat ≤ vhat ahat - vhat a)
    (hc : ∀ a, |(vhat ahat - v ahat) - (vhat a - v a)| < mhat) :
    ∀ a, a ≠ ahat → v a < v ahat := by
  intro a ha
  have h1 := hm a ha
  have h2 := (abs_lt.mp (hc a)).2
  linarith

end Certificates


/-!
## Selector theorem and the contrast-based information certificate

**Selector theorem (P21).** If every resource `r` has a valid certified objective `Ĵ r` with
`J r ≤ Ĵ r ≤ J r + δ r`, then minimizing `Ĵ` returns a resource whose true objective is within
`δ r*` of the optimum: `J r̂ ≤ J r* + δ r*`. Loose certificates on the *best* resource are what make a
sound selector conservative; tightening must target `δ r*`. (Acquisition costs for inspecting several
candidates are not modelled here; they change the meta-level problem.)

**Contrast-based information certificate (P22).** If the *action contrasts* of the utilities deviate
from a block-level comparator's contrasts by at most `dΔ x` at each state, the regret floor is at most
`Σ_x μ x · dΔ x` — with factor one, and invariant to any action-independent (common-mode) variation
within blocks, which the absolute-deviation certificate P20 pays for and the decision never does.
No optimality hypothesis on the reference action is needed (the inequality holds for any `astar`).
-/

section SelectorAndContrast

variable {R : Type*}

/-- **P21 Selector theorem.** -/
theorem selector_le_opt_add_slack (J Jhat δ : R → ℝ) (hlo : ∀ r, J r ≤ Jhat r)
    (hhi : ∀ r, Jhat r ≤ J r + δ r) (rhat rstar : R) (hmin : ∀ r, Jhat rhat ≤ Jhat r) :
    J rhat ≤ J rstar + δ rstar :=
  le_trans (hlo rhat) (le_trans (hmin rstar) (hhi rstar))

variable {B : Type*} [Fintype V] [Fintype B] [DecidableEq B] [Fintype α] [Nonempty α]

/-- **P22 Contrast-based information certificate.** -/
theorem regret_floor_le_contrast_deviation (z : V → B) (μ : V → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (U : V → α → ℝ) (Ubar : B → α → ℝ) (dΔ : V → ℝ)
    (hdev : ∀ x a b, |(U x a - U x b) - (Ubar (z x) a - Ubar (z x) b)| ≤ dΔ x)
    (astar : V → α) (sbar : B → α) (hbar : ∀ b a, Ubar b a ≤ Ubar b (sbar b))
    (sopt : B → α) (hs : ∀ b a, blockU z μ U b a ≤ blockU z μ U b (sopt b)) :
    ∑ x, μ x * U x (astar x) - ∑ b, blockU z μ U b (sopt b) ≤ ∑ x, μ x * dΔ x := by
  have h1 : ∑ x, μ x * U x (sbar (z x)) ≤ ∑ x, μ x * U x (sopt (z x)) :=
    coarse_policy_le_argmax z μ U sopt hs sbar
  have h2 : ∑ x, μ x * U x (sopt (z x)) = ∑ b, blockU z μ U b (sopt b) := utility_fiberwise z μ U sopt
  have hpt : ∀ x, U x (astar x) - U x (sbar (z x)) ≤ dΔ x := by
    intro x
    have ha := (abs_le.mp (hdev x (astar x) (sbar (z x)))).2
    have hc := hbar (z x) (astar x)
    linarith
  have h3 : ∑ x, μ x * U x (astar x) - ∑ x, μ x * U x (sbar (z x)) ≤ ∑ x, μ x * dΔ x := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro x _
    have := mul_le_mul_of_nonneg_left (hpt x) (hμ x)
    linarith [this]
  linarith

end SelectorAndContrast

end SGC.Bridge.NoGo
