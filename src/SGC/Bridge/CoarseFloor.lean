/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Bridge.DecisionHorizon

/-!
# The floor of a coarse view: what modelling cannot remove

Every certificate in `DecisionHorizon` and `TwoRadii` is an upper bound on what a coarse model can
lose. This file gives the other side, for the class of coarse models whose fine prediction is
**block-constant** in `L²(π)` (stationary re-expansion: the agent stores the macrostate and relies
on equilibrium within blocks).

Write `f` for the true density, `Π` for the coarse projector, `u a` for the utility of action `a`,
and `EU_f(a) = ⟨f, u a⟩_π` for expected utility under the law `π·f`.

* **Prediction floor** (Pythagoras): `min_{g block-constant} ‖f − g‖_π = ‖(I−Π)f‖_π`.
  No coarse model on `Π` — corrected, learned or exact — predicts closer than the unrepresented
  content.
* **Decision decomposition.** If a coarse model predicts `g` (block-constant) and acts with an
  action `a_g` optimal for `g`, then its loss against the true optimum `a*` satisfies

    `EU_f(a*) − EU_f(a_g) ≤ ⟨Πf − g, u a* − u a_g⟩_π + ⟨(I−Π)f, (I−Π)(u a* − u a_g)⟩_π`.

  The first term is the model's error on block masses — what better coarse modelling removes; it
  vanishes for the perfect coarse model `g = Πf`. The second is the unrepresented content paired
  with the task — what only finer information removes; it vanishes when the utility is
  block-constant. This is the exact "think or look" split.
* **Margin lower bound.** If the true optimum beats every other action by `m` and the coarse model
  picks a different action, it loses at least `m`.

All statements are finite-dimensional linear algebra; the only facts about `Π` used are
idempotence and self-adjointness in `⟨·,·⟩_π` (`CoarseProjector_idempotent`,
`CoarseProjector_self_adjoint`).
-/

noncomputable section

namespace SGC.Bridge.CoarseFloor

open Finset SGC.Approximate

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (P : Partition V)

/-- Expected utility of `a` under the law `π·f`. -/
def EU (f : V → ℝ) (u : V → ℝ) : ℝ := inner_pi pi_dist f u

/-- Local name for the coarse projector (the symbol `Π` is reserved by Lean). -/
abbrev Pj : (V → ℝ) →ₗ[ℝ] (V → ℝ) := CoarseProjector P pi_dist hπ

lemma proj_apply_proj (f : V → ℝ) : Pj pi_dist hπ P (Pj pi_dist hπ P f) = Pj pi_dist hπ P f := by
  have h := CoarseProjector_idempotent P pi_dist hπ
  exact congrFun (congrArg DFunLike.coe h) f

/-- The unrepresented part of `f` is orthogonal to every block-constant `g` (`Πg = g`). -/
lemma inner_residual_blockConstant (f g : V → ℝ) (hg : Pj pi_dist hπ P g = g) :
    inner_pi pi_dist (f - Pj pi_dist hπ P f) g = 0 := by
  rw [← hg, ← CoarseProjector_self_adjoint P pi_dist hπ]
  have : Pj pi_dist hπ P (f - Pj pi_dist hπ P f) = 0 := by
    rw [(Pj pi_dist hπ P).map_sub, proj_apply_proj]; simp
  rw [this, inner_pi_zero_left]

/-- Pairing the residual with any `h` only sees the residual of `h`. -/
lemma inner_residual_eq_residual_residual (f h : V → ℝ) :
    inner_pi pi_dist (f - Pj pi_dist hπ P f) h = inner_pi pi_dist (f - Pj pi_dist hπ P f) (h - Pj pi_dist hπ P h) := by
  have hz : inner_pi pi_dist (f - Pj pi_dist hπ P f) (Pj pi_dist hπ P h) = 0 :=
    inner_residual_blockConstant pi_dist hπ P f (Pj pi_dist hπ P h) (proj_apply_proj pi_dist hπ P h)
  rw [inner_pi_sub_right, hz, sub_zero]

/-- **Prediction floor.** For every block-constant `g`, `‖f − g‖² = ‖f − Πf‖² + ‖Πf − g‖²`, hence
`‖f − g‖_π ≥ ‖f − Πf‖_π`, with equality at `g = Πf`. -/
theorem norm_sq_sub_blockConstant (f g : V → ℝ) (hg : Pj pi_dist hπ P g = g) :
    norm_sq_pi pi_dist (f - g) = norm_sq_pi pi_dist (f - Pj pi_dist hπ P f) + norm_sq_pi pi_dist (Pj pi_dist hπ P f - g) := by
  have hsplit : f - g = (f - Pj pi_dist hπ P f) + (Pj pi_dist hπ P f - g) := by abel
  have hcross : inner_pi pi_dist (f - Pj pi_dist hπ P f) (Pj pi_dist hπ P f - g) = 0 := by
    apply inner_residual_blockConstant pi_dist hπ P
    rw [(Pj pi_dist hπ P).map_sub, proj_apply_proj, hg]
  unfold norm_sq_pi
  rw [hsplit, inner_pi_add_left, inner_pi_add_right, inner_pi_add_right, hcross,
    inner_pi_comm (Pj pi_dist hπ P f - g) (f - Pj pi_dist hπ P f), hcross]
  ring

theorem prediction_floor (f g : V → ℝ) (hg : Pj pi_dist hπ P g = g) :
    norm_sq_pi pi_dist (f - Pj pi_dist hπ P f) ≤ norm_sq_pi pi_dist (f - g) := by
  rw [norm_sq_sub_blockConstant pi_dist hπ P f g hg]
  have : 0 ≤ norm_sq_pi pi_dist (Pj pi_dist hπ P f - g) := by
    unfold norm_sq_pi inner_pi
    exact Finset.sum_nonneg fun x _ => by
      have := (hπ x).le; nlinarith [sq_nonneg ((Pj pi_dist hπ P f - g) x)]
  linarith

/-- **Decision decomposition.** A coarse model predicts the block-constant `g` and takes `a_g`,
optimal for `g`. Its loss against the true optimum `a*` is bounded by a model-error term plus an
unrepresented-content term. -/
theorem loss_le_model_plus_residual (f g : V → ℝ) (hg : Pj pi_dist hπ P g = g) (ustar ug : V → ℝ)
    (hopt_g : EU pi_dist g ustar ≤ EU pi_dist g ug) :
    EU pi_dist f ustar - EU pi_dist f ug ≤
      inner_pi pi_dist (Pj pi_dist hπ P f - g) (ustar - ug) +
      inner_pi pi_dist (f - Pj pi_dist hπ P f) ((ustar - ug) - Pj pi_dist hπ P (ustar - ug)) := by
  unfold EU at *
  have h1 : inner_pi pi_dist f ustar - inner_pi pi_dist f ug = inner_pi pi_dist f (ustar - ug) := by
    rw [inner_pi_sub_right]
  have hsplit : f = (Pj pi_dist hπ P f - g) + g + (f - Pj pi_dist hπ P f) := by abel
  have h2 : inner_pi pi_dist f (ustar - ug) =
      inner_pi pi_dist (Pj pi_dist hπ P f - g) (ustar - ug) + inner_pi pi_dist g (ustar - ug) +
      inner_pi pi_dist (f - Pj pi_dist hπ P f) (ustar - ug) := by
    conv_lhs => rw [hsplit]
    rw [inner_pi_add_left, inner_pi_add_left]
  have h3 : inner_pi pi_dist g (ustar - ug) ≤ 0 := by
    rw [inner_pi_sub_right]; linarith
  rw [h1, h2, inner_residual_eq_residual_residual pi_dist hπ P f (ustar - ug)]
  linarith

/-- **Perfect coarse model.** With `g = Πf` the model term vanishes: the irreducible loss is
bounded by the pairing of the unrepresented content of the state with that of the utility. -/
theorem perfect_coarse_loss_le (f : V → ℝ) (ustar uc : V → ℝ)
    (hopt_c : EU pi_dist (Pj pi_dist hπ P f) ustar ≤ EU pi_dist (Pj pi_dist hπ P f) uc) :
    EU pi_dist f ustar - EU pi_dist f uc ≤
      inner_pi pi_dist (f - Pj pi_dist hπ P f) ((ustar - uc) - Pj pi_dist hπ P (ustar - uc)) := by
  have h := loss_le_model_plus_residual pi_dist hπ P f (Pj pi_dist hπ P f) (proj_apply_proj pi_dist hπ P f) ustar uc hopt_c
  simp only [sub_self, inner_pi_zero_left, zero_add] at h
  exact h

/-- Cauchy–Schwarz form of the irreducible loss. -/
theorem perfect_coarse_loss_le_norms (f : V → ℝ) (ustar uc : V → ℝ)
    (hopt_c : EU pi_dist (Pj pi_dist hπ P f) ustar ≤ EU pi_dist (Pj pi_dist hπ P f) uc) :
    EU pi_dist f ustar - EU pi_dist f uc ≤
      norm_pi pi_dist (f - Pj pi_dist hπ P f) * norm_pi pi_dist ((ustar - uc) - Pj pi_dist hπ P (ustar - uc)) :=
  le_trans (perfect_coarse_loss_le pi_dist hπ P f ustar uc hopt_c)
    (le_trans (le_abs_self _) (cauchy_schwarz_pi pi_dist hπ _ _))

/-- **Task-invariant utilities have no irreducible loss**: if `u a* − u a_c` is block-constant, the
perfect coarse model loses nothing. -/
theorem perfect_coarse_loss_zero_of_blockConstant (f : V → ℝ) (ustar uc : V → ℝ)
    (hopt_c : EU pi_dist (Pj pi_dist hπ P f) ustar ≤ EU pi_dist (Pj pi_dist hπ P f) uc)
    (hopt_star : EU pi_dist f uc ≤ EU pi_dist f ustar)
    (hbc : Pj pi_dist hπ P (ustar - uc) = ustar - uc) :
    EU pi_dist f ustar - EU pi_dist f uc = 0 := by
  have h := perfect_coarse_loss_le pi_dist hπ P f ustar uc hopt_c
  rw [hbc, sub_self, inner_pi_zero_right] at h
  unfold EU at *
  linarith

/-- **Margin lower bound.** If `a*` beats every other action by at least `m` under the true law and
the coarse model's action differs from `a*`, the loss is at least `m`. -/
theorem loss_ge_margin {α : Type*} (f : V → ℝ) (u : α → V → ℝ) (astar ag : α) {m : ℝ}
    (hmargin : ∀ a, a ≠ astar → EU pi_dist f (u astar) - EU pi_dist f (u a) ≥ m)
    (hne : ag ≠ astar) :
    EU pi_dist f (u astar) - EU pi_dist f (u ag) ≥ m :=
  hmargin ag hne

end SGC.Bridge.CoarseFloor
