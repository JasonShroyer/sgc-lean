/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.InformationGeometry.TaskRelevantGain

/-!
# Value of information for finite typed decisions

A typed decision chooses an action `a : α` (a finite, nonempty option set — the
shape of a `choice` primitive) after observing a coarse variable. With weights
`w` on a finite outcome space `Ω` and utility `u a ω`, the *block utility* of
action `a` on block `b` of an observation `q` is the unnormalized sum

  `U_q(b, a) = Σ_{q ω = b} w ω · u a ω`,

and the *achievable value* under observation `q` is `V(q) = Σ_b max_a U_q(b, a)`
(choose the best action on each block). No division appears, so empty blocks
and zero weights are harmless.

## Results

* `value_le_of_refine` — **refinement never hurts:** `V(f ∘ q) ≤ V(q)`.
* `voi_nonneg`, `voi_eq_zero_iff` — the value of information
  `V(q) − V(f ∘ q)` is nonnegative and vanishes iff on every coarse block some
  action optimal for the coarse block is optimal on every fine block inside it.
* `voi_chain` — values of information telescope along nested refinements.
* `voi_eq_zero_of_constant_optimal` — if one action is optimal on every fine
  block, refining is worthless (the decision is already determined).

This is the decision-theoretic twin of `TaskRelevantGain`: that module measures
what a refinement does to the best squared-error *prediction*; this one measures
what it does to the best *action*. A refinement can be informative about the
state (positive `gain`, positive Fisher loss recovered) and still have zero value
of information for a given decision — the observation changed beliefs but not
the optimal act. Both quantities are needed by a controller deciding whether to
retrieve or refine.
-/

noncomputable section

namespace SGC.InformationGeometry.DecisionValue

open Finset

set_option linter.unusedSectionVars false

variable {Ω β γ δ α : Type*} [Fintype Ω] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ] [Fintype α] [Nonempty α]

variable (q : Ω → β) (f : β → γ) (w : Ω → ℝ) (u : α → Ω → ℝ)

/-- Unnormalized block utility of action `a` on block `b`. -/
def blockUtility (b : β) (a : α) : ℝ := ∑ ω ∈ univ.filter (fun ω => q ω = b), w ω * u a ω

/-- Best achievable block utility. -/
def blockValue (b : β) : ℝ := univ.sup' univ_nonempty (blockUtility q w u b)

/-- Achievable value under observation `q`. -/
def value : ℝ := ∑ b, blockValue q w u b

/-- Value of information of the refinement `q` over `f ∘ q`. -/
def voi : ℝ := value q w u - value (f ∘ q) w u

lemma blockUtility_le_blockValue (b : β) (a : α) : blockUtility q w u b a ≤ blockValue q w u b :=
  Finset.le_sup' (blockUtility q w u b) (Finset.mem_univ a)

lemma exists_optimal (b : β) : ∃ a, blockUtility q w u b a = blockValue q w u b := by
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup' univ_nonempty (blockUtility q w u b)
  exact ⟨a, ha.symm⟩

/-- Coarse block utility is the sum of fine block utilities over the fiber. -/
lemma blockUtility_comp (c : γ) (a : α) :
    blockUtility (f ∘ q) w u c a = ∑ b ∈ univ.filter (fun b => f b = c), blockUtility q w u b a := by
  unfold blockUtility
  exact ScoreProjection.sum_filter_comp q f c (fun ω => w ω * u a ω)

/-- The coarse block value is at most the sum of fine block values over the fiber. -/
lemma blockValue_comp_le (c : γ) :
    blockValue (f ∘ q) w u c ≤ ∑ b ∈ univ.filter (fun b => f b = c), blockValue q w u b := by
  unfold blockValue
  refine Finset.sup'_le _ _ (fun a _ => ?_)
  rw [blockUtility_comp q f w u c a]
  exact Finset.sum_le_sum (fun b _ => blockUtility_le_blockValue q w u b a)

/-- **Refinement never hurts.** -/
theorem value_le_of_refine : value (f ∘ q) w u ≤ value q w u := by
  unfold value
  rw [ScoreProjection.sum_fibers f (blockValue q w u)]
  exact Finset.sum_le_sum (fun c _ => blockValue_comp_le q f w u c)

theorem voi_nonneg : 0 ≤ voi q f w u := by
  unfold voi
  linarith [value_le_of_refine q f w u]

/-- **Value of information vanishes iff no coarse block would change its optimal action
on refinement:** on each coarse block some action is simultaneously optimal on every fine
block inside it. -/
theorem voi_eq_zero_iff :
    voi q f w u = 0 ↔ ∀ c, ∃ a, ∀ b, f b = c →
      blockUtility q w u b a = blockValue q w u b := by
  unfold voi value
  rw [ScoreProjection.sum_fibers f (blockValue q w u), sub_eq_zero, eq_comm]
  have hterm : ∀ c, blockValue (f ∘ q) w u c ≤ ∑ b ∈ univ.filter (fun b => f b = c),
      blockValue q w u b := blockValue_comp_le q f w u
  constructor
  · intro h c
    have hc := (Finset.sum_eq_sum_iff_of_le (fun c _ => hterm c)).mp h c (Finset.mem_univ c)
    obtain ⟨a, ha⟩ := exists_optimal (f ∘ q) w u c
    refine ⟨a, fun b hb => ?_⟩
    have hsum : ∑ b ∈ univ.filter (fun b => f b = c), blockUtility q w u b a
        = ∑ b ∈ univ.filter (fun b => f b = c), blockValue q w u b := by
      rw [← blockUtility_comp q f w u c a, ha, hc]
    have hb' := (Finset.sum_eq_sum_iff_of_le (fun b _ => blockUtility_le_blockValue q w u b a)).mp
      hsum b (by simpa using hb)
    exact hb'
  · intro h
    refine Finset.sum_congr rfl (fun c _ => ?_)
    obtain ⟨a, ha⟩ := h c
    refine le_antisymm (hterm c) ?_
    calc ∑ b ∈ univ.filter (fun b => f b = c), blockValue q w u b
        = ∑ b ∈ univ.filter (fun b => f b = c), blockUtility q w u b a :=
          Finset.sum_congr rfl (fun b hb => (ha b (Finset.mem_filter.mp hb).2).symm)
      _ = blockUtility (f ∘ q) w u c a := (blockUtility_comp q f w u c a).symm
      _ ≤ blockValue (f ∘ q) w u c := blockUtility_le_blockValue (f ∘ q) w u c a

/-- If a single action is optimal on every fine block, refinement has no value. -/
theorem voi_eq_zero_of_constant_optimal (a : α)
    (ha : ∀ b, blockUtility q w u b a = blockValue q w u b) : voi q f w u = 0 :=
  (voi_eq_zero_iff q f w u).mpr (fun _ => ⟨a, fun b _ => ha b⟩)

/-- **Telescoping** along `q ≥ f ∘ q ≥ g ∘ f ∘ q`. -/
theorem voi_chain (g : γ → δ) :
    voi q (g ∘ f) w u = voi q f w u + voi (f ∘ q) g w u := by
  unfold voi
  have h : (g ∘ f) ∘ q = g ∘ (f ∘ q) := rfl
  rw [h]
  ring

/-- Refining further can only increase the value of information relative to a fixed base. -/
theorem voi_mono (g : γ → δ) : voi q f w u ≤ voi q (g ∘ f) w u := by
  rw [voi_chain q f w u g]
  linarith [voi_nonneg (f ∘ q) g w u]

end SGC.InformationGeometry.DecisionValue
