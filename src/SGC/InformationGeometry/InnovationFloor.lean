/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.InformationGeometry.GeneralPathBound

/-!
# The multi-step lower bound is the composition law

Two proposed multi-step floors were refuted numerically (decisions 0073, 0077):
`T ×` the one-step floor, and the sum of per-step conditional variances
`Σ_t E[Var(r_t | Y, X_{≤t})]`. Both fail because later blocks reveal earlier
states.

The correct statement is exact and hypothesis-free. Refine the macro-history
`Y` by any further observation `Z` of the path (for instance `X_0`, or
`X_{≤t}`). By the chain rule `fisherLoss_chain`,

  `loss(Y) = loss(Y, Z) + loss_{push}(Z → Y)`,

and both terms are nonnegative. Hence **every refinement gives a lower bound**
`loss(Y) ≥ loss_{push}(Z → Y)`, the *innovation* carried by `Z`; iterating
along `Y ≤ (Y, X_0) ≤ (Y, X_0, X_1) ≤ … ≤ full path` telescopes to the loss,
with each innovation `≥ 0`. This is the Doob decomposition of the exact
identity, and it is where a valid multi-step floor lives.
-/

noncomputable section

namespace SGC.InformationGeometry.InnovationFloor

open Finset Matrix SGC.InformationGeometry SGC.InformationGeometry.MarkovPathFisher
  SGC.InformationGeometry.GeneralPathBound

set_option linter.unusedSectionVars false

variable {V β γ : Type*} [Fintype V] [DecidableEq V] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]
variable (P : Matrix V V ℝ) (q : V → β) (π : V → ℝ) (s : V → V → ℝ) (T : ℕ)

/-- A refinement of the macro-history: an observation `ρ` of the path from which
the block path is recoverable via `f`. -/
structure Refinement where
  ρ : (Fin (T + 1) → V) → γ
  f : γ → (Fin (T + 1) → β)
  factor : ∀ ω, f (ρ ω) = macroPath q T ω

variable (R : Refinement q T (γ := γ))

/-- Loss of the pushed-forward family from the refinement down to the block path:
the innovation carried by `ρ` beyond `Y`. -/
def innovation : ℝ :=
  ScoreProjection.fineFisher (ScoreProjection.blockMass R.ρ (pathProb P π T))
      (ScoreProjection.blockDeriv R.ρ (pathDerivG P π s T))
    - ScoreProjection.coarseFisher R.f (ScoreProjection.blockMass R.ρ (pathProb P π T))
      (ScoreProjection.blockDeriv R.ρ (pathDerivG P π s T))

/-- Loss through the refined observation `ρ`. -/
def refinedLoss : ℝ :=
  ScoreProjection.fineFisher (pathProb P π T) (pathDerivG P π s T)
    - ScoreProjection.coarseFisher R.ρ (pathProb P π T) (pathDerivG P π s T)

/-- **Exact decomposition:** `loss(Y) = loss(ρ) + innovation(ρ → Y)`. -/
theorem lossG_eq_refined_add_innovation :
    lossG P q π s T = refinedLoss P q π s T R + innovation P q π s T R := by
  unfold lossG refinedLoss innovation
  have h := ScoreProjection.fisherLoss_chain R.ρ (pathDerivG P π s T) (p := pathProb P π T) R.f
  have hq : (fun ω => R.f (R.ρ ω)) = macroPath q T := funext R.factor
  rw [hq] at h
  exact h

/-- **The innovation floor:** every refinement of the macro-history lower-bounds the loss. -/
theorem innovation_le_lossG (hP : ∀ x y, 0 < P x y) (hπ : ∀ x, 0 < π x) :
    innovation P q π s T R ≤ lossG P q π s T := by
  rw [lossG_eq_refined_add_innovation P q π s T R]
  have h0 : 0 ≤ refinedLoss P q π s T R := by
    unfold refinedLoss
    have := ScoreProjection.coarseFisher_le R.ρ (pathDerivG P π s T) (pathProb_pos P hP hπ T)
    linarith
  linarith

/-- Innovations are nonnegative. -/
theorem innovation_nonneg (hP : ∀ x y, 0 < P x y) (hπ : ∀ x, 0 < π x)
    (hsurj : Function.Surjective R.ρ) : 0 ≤ innovation P q π s T R := by
  unfold innovation
  have := ScoreProjection.coarseFisher_le R.f
    (ScoreProjection.blockDeriv R.ρ (pathDerivG P π s T))
    (ScoreProjection.blockMass_pos R.ρ (pathProb_pos P hP hπ T) hsurj)
  linarith

/-- The refinement by the initial state: `(Y, X_0)`. -/
def initialRefinement : Refinement q T (γ := (Fin (T + 1) → β) × V) where
  ρ := fun ω => (macroPath q T ω, ω 0)
  f := Prod.fst
  factor := fun _ => rfl

/-- **Concrete floor:** the information about `s` carried by the initial state
beyond the block path lower-bounds the `T`-step loss. -/
theorem initial_innovation_le_lossG (hP : ∀ x y, 0 < P x y) (hπ : ∀ x, 0 < π x) :
    innovation P q π s T (initialRefinement q T) ≤ lossG P q π s T :=
  innovation_le_lossG P q π s T _ hP hπ

end SGC.InformationGeometry.InnovationFloor
