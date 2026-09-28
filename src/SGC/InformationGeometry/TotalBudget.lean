/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.InformationGeometry.MarkovPathFisher

/-!
# The closure defect is the total information budget over block-pair directions

A single task direction `b` sees only the projection `δ_b` of the closure
residual. Summing over the *indicator basis* of block-pair tilts
`1_{(A,C)}` recovers the whole residual:

  `Σ_{A,C} ‖δ_{1_{(A,C)}}‖²_π = 𝔇_π²`,

and therefore the total one-step information loss over every block-pair
direction is at most the closure defect:

  `Σ_{A,C} loss₁(1_{(A,C)}) ≤ 𝔇_π²`.

This is the precise relation between the direction-free closure quantities of
the spectral-partitioning literature (χ²-mutual information, normalized cut,
`k − tr P̄`) and the direction-specific relevance objective `J₁`: the closure
defect is a *sum over all directions*; a task consumes one of them. Minimizing
the sum says nothing about any one summand (decisions 0074, 0075).
-/

noncomputable section

namespace SGC.InformationGeometry.TotalBudget

open Finset Matrix SGC.InformationGeometry SGC.InformationGeometry.MarkovPathFisher

set_option linter.unusedSectionVars false

variable {V β : Type*} [Fintype V] [DecidableEq V] [Fintype β] [DecidableEq β]
variable (q : V → β) (π : V → ℝ) (R : V → β → ℝ)

/-- Indicator block-pair tilt. -/
def ind (A C : β) : β → β → ℝ := fun A' C' => if A' = A ∧ C' = C then 1 else 0

lemma delta_ind (A C : β) (x : V) :
    BlockPairTilt.delta q π R (ind A C) x = if q x = A then BlockPairTilt.res q π R x C else 0 := by
  unfold BlockPairTilt.delta ind
  by_cases hA : q x = A
  · simp only [hA, true_and]
    rw [Finset.sum_eq_single C]
    · simp
    · intro C' _ hC'
      simp [hC']
    · simp
  · simp [hA]

/-- **The indicator basis recovers the closure defect:**
`Σ_{A,C} ‖δ_{1_{(A,C)}}‖²_π = 𝔇_π²`. -/
theorem sum_ind_energy_eq_defectSq :
    ∑ A, ∑ C, ∑ x, π x * BlockPairTilt.delta q π R (ind A C) x ^ 2
      = BlockPairTilt.defectSq q π R := by
  unfold BlockPairTilt.defectSq
  simp only [delta_ind]
  have h : ∀ x, ∑ A, ∑ C, π x * (if q x = A then BlockPairTilt.res q π R x C else 0) ^ 2
      = π x * ∑ C, BlockPairTilt.res q π R x C ^ 2 := by
    intro x
    rw [Finset.sum_eq_single (q x)]
    · simp [Finset.mul_sum]
    · intro A _ hA
      simp [Ne.symm hA]
    · simp
  calc ∑ A, ∑ C, ∑ x, π x * (if q x = A then BlockPairTilt.res q π R x C else 0) ^ 2
      = ∑ A, ∑ x, ∑ C, π x * (if q x = A then BlockPairTilt.res q π R x C else 0) ^ 2 :=
        Finset.sum_congr rfl (fun A _ => Finset.sum_comm)
    _ = ∑ x, ∑ A, ∑ C, π x * (if q x = A then BlockPairTilt.res q π R x C else 0) ^ 2 :=
        Finset.sum_comm
    _ = ∑ x, π x * ∑ C, BlockPairTilt.res q π R x C ^ 2 := Finset.sum_congr rfl (fun x _ => h x)

lemma ind_sq_le (A C : β) : ∀ A', ∑ C', ind A C A' C' ^ 2 ≤ 1 := by
  intro A'
  unfold ind
  by_cases hA : A' = A
  · subst hA
    rw [Finset.sum_eq_single C]
    · simp
    · intro C' _ hC'
      simp [hC']
    · simp
  · simp [hA]

variable (P : Matrix V V ℝ)

/-- **Total one-step budget.** The Fisher information lost about *all* block-pair
directions together, in one step, is at most the closure defect. -/
theorem total_oneStep_loss_le_defectSq (hP : ∀ x y, 0 < P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (hπ : ∀ x, 0 < π x) (hstat : π ᵥ* P = π) :
    ∑ A, ∑ C, (ScoreProjection.fineFisher (pathProb P π 1) (pathDeriv P q π (ind A C) 1)
      - ScoreProjection.coarseFisher (macroPath q 1) (pathProb P π 1) (pathDeriv P q π (ind A C) 1))
      ≤ BlockPairTilt.defectSq q π (blockExit P q) := by
  rw [← sum_ind_energy_eq_defectSq q π (blockExit P q)]
  refine Finset.sum_le_sum (fun A _ => Finset.sum_le_sum (fun C _ => ?_))
  have := fisherLoss_markov_path_le_energy P q π (ind A C) 1 hP hrow hπ hstat
  simpa using this

end SGC.InformationGeometry.TotalBudget
