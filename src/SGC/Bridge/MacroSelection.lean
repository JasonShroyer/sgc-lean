/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Bridge.CoarseFloor
import SGC.Renormalization.OptimalPartition

/-!
# Selecting a macro-description: three failure modes along the refinement lattice

A system choosing its own coarse description faces three ways to be wrong — bad coarse dynamics,
missing task information, inadequate data — and the certified loss of acting on an **estimated**
coarse prediction splits into exactly these three terms:

  `loss ≤ ⟨Πf − g, Δu⟩  +  ⟨g − ĝ, Δu⟩  +  ⟨(I−Π)f, (I−Π)Δu⟩`
            (dynamics)        (data)           (task)

(`three_mode_bound`). The pigeonhole corollary `some_mode_exceeds` is the formal content of
"the diagnostic separates the modes": if the certified loss exceeds a tolerance, at least one
named term exceeds a third of it, and each term has its own repair lever (better coarse model /
more samples / finer or task-aligned partition).

Along the refinement order `P₁ ≤ P₂` (`P₁` finer) the three terms behave differently:
* the task term is **antitone** — refining never increases unrepresented content
  (`residual_sq_antitone_of_refinement`, Pythagoras with the tower property);
* the data term grows with the number of blocks (more parameters; not formalized here, it is
  the content of the row radii in `TwoRadii`);
* the dynamics term is **not** monotone: `QuotientGenerator.defect_not_antitone_under_refinement`
  exhibits a finer partition that leaks more than a coarser one.

So selection is a genuine trade-off with a non-monotone middle term, and a selector that walks the
lattice must use the attribution, not a single score.
-/

noncomputable section

namespace SGC.Bridge.MacroSelection

open Finset SGC.Approximate SGC.Renormalization SGC.Bridge.CoarseFloor

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)

/-- **Three-mode bound.** A coarse model with ideal coarse prediction `g` (block-constant) but
actual estimated prediction `ĝ`, acting with `a_ĝ` optimal for `ĝ`, loses at most a dynamics term,
a data term and a task term against the true optimum `a*`. -/
theorem three_mode_bound (P : Partition V) (f g ghat : V → ℝ) (ustar ug : V → ℝ)
    (hopt_hat : EU pi_dist ghat ustar ≤ EU pi_dist ghat ug) :
    EU pi_dist f ustar - EU pi_dist f ug ≤
      inner_pi pi_dist (CoarseProjector P pi_dist hπ f - g) (ustar - ug) +
      inner_pi pi_dist (g - ghat) (ustar - ug) +
      inner_pi pi_dist (f - CoarseProjector P pi_dist hπ f)
        ((ustar - ug) - CoarseProjector P pi_dist hπ (ustar - ug)) := by
  unfold EU at *
  have h1 : inner_pi pi_dist f ustar - inner_pi pi_dist f ug = inner_pi pi_dist f (ustar - ug) := by
    rw [inner_pi_sub_right]
  have hsplit : f = (CoarseProjector P pi_dist hπ f - g) + (g - ghat) + ghat +
      (f - CoarseProjector P pi_dist hπ f) := by abel
  have h2 : inner_pi pi_dist f (ustar - ug) =
      inner_pi pi_dist (CoarseProjector P pi_dist hπ f - g) (ustar - ug) +
      inner_pi pi_dist (g - ghat) (ustar - ug) + inner_pi pi_dist ghat (ustar - ug) +
      inner_pi pi_dist (f - CoarseProjector P pi_dist hπ f) (ustar - ug) := by
    conv_lhs => rw [hsplit]
    rw [inner_pi_add_left, inner_pi_add_left, inner_pi_add_left]
  have h3 : inner_pi pi_dist ghat (ustar - ug) ≤ 0 := by
    rw [inner_pi_sub_right]; linarith
  rw [h1, h2, inner_residual_eq_residual_residual pi_dist hπ P f (ustar - ug)]
  linarith

/-- **Attribution.** If the certified loss exceeds `3·τ`, at least one of the three named terms
exceeds `τ`. -/
theorem some_mode_exceeds {a b c τ loss : ℝ} (h : loss ≤ a + b + c) (hτ : 3 * τ < loss) :
    τ < a ∨ τ < b ∨ τ < c := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨ha, hb, hc⟩ := hcon
  linarith

/-- **The task term is antitone under refinement.** If `P₁` is finer than `P₂`, the unrepresented
content of any `u` is smaller under `P₁`:
`‖u − Π₁u‖² ≤ ‖u − Π₂u‖²`. -/
theorem residual_sq_antitone_of_refinement (P₁ P₂ : Partition V) (h : P₁ ≤ P₂) (u : V → ℝ) :
    norm_sq_pi pi_dist (u - CoarseProjector P₁ pi_dist hπ u) ≤
      norm_sq_pi pi_dist (u - CoarseProjector P₂ pi_dist hπ u) := by
  -- Π₂u is P₂-block-constant hence P₁-block-constant, so Π₁(Π₂u) = Π₂u; apply the prediction
  -- floor for P₁ with g := Π₂u.
  have hg : CoarseProjector P₁ pi_dist hπ (CoarseProjector P₂ pi_dist hπ u) =
      CoarseProjector P₂ pi_dist hπ u :=
    finer_proj_fixes_coarser P₁ P₂ pi_dist hπ h u
  exact prediction_floor pi_dist hπ P₁ u (CoarseProjector P₂ pi_dist hπ u) hg

/-- Corollary: refining a partition never increases the task term of the three-mode bound, for
any fixed utility difference. -/
theorem task_term_antitone_of_refinement (P₁ P₂ : Partition V) (h : P₁ ≤ P₂) (du : V → ℝ) :
    norm_pi pi_dist (du - CoarseProjector P₁ pi_dist hπ du) ≤
      norm_pi pi_dist (du - CoarseProjector P₂ pi_dist hπ du) := by
  unfold norm_pi
  exact Real.sqrt_le_sqrt (residual_sq_antitone_of_refinement pi_dist hπ P₁ P₂ h du)

end SGC.Bridge.MacroSelection
