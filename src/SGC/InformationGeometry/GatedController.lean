/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.InformationGeometry.DecisionValue

/-!
# A one-step refinement controller, and what it provably dominates

A controller holds a coarse observation `q₀` and a finite menu of candidate
refinements `qᵢ` (each with `q₀ = fᵢ ∘ qᵢ`) at acquisition cost `cᵢ ≥ 0`. It
may act now on `q₀`, or pay `cᵢ` and act on `qᵢ`. Its **net value** is

  `N = max (V(q₀), maxᵢ (V(qᵢ) − cᵢ))`.

## Results

* `net_ge_base` — the controller never does worse than acting now.
* `net_ge_refine` — it never does worse than any fixed always-refine-`i` policy.
* `refines_iff` — it refines iff some candidate has `voi > cost`; when no
  candidate pays for itself it acts now.
* `net_le_value_sup` — the controller cannot exceed the best refined value: the
  bound is `V(qᵢ*)` for the chosen candidate; information has a ceiling.

These are one-step statements about expected utility in the finite model, with
the utility taken as given. They provide the evaluation criterion for the
bounded gated-execution experiment: a controller is correct when its realized
decisions match the `voi − cost` rule, and the theorems say what that rule
guarantees. Nothing here models a "confidence-only" policy; such a policy has no
utility semantics to be dominated in.
-/

noncomputable section

namespace SGC.InformationGeometry.GatedController

open Finset DecisionValue

set_option linter.unusedSectionVars false

variable {Ω β γ α ι : Type*} [Fintype Ω] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ] [Fintype α] [Nonempty α] [Fintype ι] [Nonempty ι]

/-- A menu of refinements of a common coarse observation. -/
structure Menu (Ω β γ ι : Type*) where
  q₀ : Ω → γ
  q : ι → Ω → β
  f : ι → β → γ
  factor : ∀ i ω, f i (q i ω) = q₀ ω
  cost : ι → ℝ
  cost_nonneg : ∀ i, 0 ≤ cost i

variable (M : Menu Ω β γ ι) (w : Ω → ℝ) (u : α → Ω → ℝ)

/-- Net value of refining by candidate `i`. -/
def refineNet (i : ι) : ℝ := value (M.q i) w u - M.cost i

/-- Best net refinement. -/
def bestRefine : ℝ := univ.sup' univ_nonempty (refineNet M w u)

/-- Net value of the controller. -/
def net : ℝ := max (value M.q₀ w u) (bestRefine M w u)

lemma q₀_eq (i : ι) : M.q₀ = M.f i ∘ M.q i := by
  funext ω
  exact (M.factor i ω).symm

/-- **Never worse than acting now.** -/
theorem net_ge_base : value M.q₀ w u ≤ net M w u := le_max_left _ _

/-- **Never worse than any fixed refinement policy.** -/
theorem net_ge_refine (i : ι) : value (M.q i) w u - M.cost i ≤ net M w u :=
  (Finset.le_sup' (refineNet M w u) (mem_univ i)).trans (le_max_right _ _)

/-- The value of information of candidate `i` over the base. -/
def voiOf (i : ι) : ℝ := voi (M.q i) (M.f i) w u

theorem refineNet_eq (i : ι) : refineNet M w u i = value M.q₀ w u + (voiOf M w u i - M.cost i) := by
  unfold refineNet voiOf voi
  rw [← q₀_eq M i]
  ring

/-- **The controller refines iff some candidate's value of information exceeds its cost.** -/
theorem refines_iff : value M.q₀ w u < net M w u ↔ ∃ i, M.cost i < voiOf M w u i := by
  unfold net bestRefine
  constructor
  · intro h
    have h' : value M.q₀ w u < univ.sup' univ_nonempty (refineNet M w u) := by
      rcases lt_max_iff.mp h with h1 | h1
      · exact absurd h1 (lt_irrefl _)
      · exact h1
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' univ_nonempty (refineNet M w u)
    refine ⟨i, ?_⟩
    rw [hi, refineNet_eq] at h'
    linarith
  · rintro ⟨i, hi⟩
    refine lt_max_of_lt_right ?_
    refine lt_of_lt_of_le ?_ (Finset.le_sup' (refineNet M w u) (mem_univ i))
    rw [refineNet_eq]
    linarith

/-- When no candidate pays for itself, the controller acts now. -/
theorem net_eq_base_of_no_profit (h : ∀ i, voiOf M w u i ≤ M.cost i) :
    net M w u = value M.q₀ w u := by
  unfold net bestRefine
  refine max_eq_left (Finset.sup'_le _ _ (fun i _ => ?_))
  rw [refineNet_eq]
  linarith [h i]

/-- **Information has a ceiling:** the controller's net value never exceeds the best
refined value (costs only subtract). -/
theorem net_le_value_sup :
    net M w u ≤ max (value M.q₀ w u) (univ.sup' univ_nonempty (fun i => value (M.q i) w u)) := by
  unfold net bestRefine
  refine max_le_max le_rfl (Finset.sup'_le _ _ (fun i _ => ?_))
  refine (Finset.le_sup' (fun i => value (M.q i) w u) (mem_univ i)).trans' ?_
  unfold refineNet
  linarith [M.cost_nonneg i]

/-- The base value is itself at most every refined value (refinement never hurts). -/
theorem value_base_le (i : ι) : value M.q₀ w u ≤ value (M.q i) w u := by
  rw [q₀_eq M i]
  exact value_le_of_refine (M.q i) (M.f i) w u

end SGC.InformationGeometry.GatedController
