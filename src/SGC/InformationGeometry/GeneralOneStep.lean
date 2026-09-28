/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.InformationGeometry.ScoreProjection

/-!
# One-step loss for an arbitrary direction: the fiber-variance objective

For any step score `s : V → V → ℝ` (the derivative of `log P_θ(x,y)` in any
direction, not necessarily a block-pair tilt), the one-step Fisher loss through a
partition `q` is exactly the `π·P`-weighted within-fiber variance of `s` over the
block pairs `(q x, q y)`:

  `loss₁(q) = Σ_{x,y} π x P x y · (s x y − mean_{(q x, q y)} s)²  =: J₁(q)`.

It vanishes iff `s` is constant on every block pair. `J₁` is the objective that
ranks coarse-grainings by relevance to a task direction (decision 0074/0075): it
is computable from one transition, and an agglomerative merge under `J₁`
recovers the multi-step information optimum in almost all tested cases.
-/

noncomputable section

namespace SGC.InformationGeometry.GeneralOneStep

open Finset Matrix SGC.InformationGeometry

set_option linter.unusedSectionVars false

variable {V β : Type*} [Fintype V] [DecidableEq V] [Fintype β] [DecidableEq β]
variable (P : Matrix V V ℝ) (q : V → β) (π : V → ℝ) (s : V → V → ℝ)

/-- Coarse map on one transition. -/
def Q (ω : V × V) : β × β := (q ω.1, q ω.2)

/-- Law of one transition. -/
def w (ω : V × V) : ℝ := π ω.1 * P ω.1 ω.2

/-- Derivative data `w · s`. -/
def d (ω : V × V) : ℝ := w P π ω * s ω.1 ω.2

/-- Fiber mean of the step score on the block pair `f`. -/
def fiberMean (f : β × β) : ℝ :=
  ScoreProjection.blockAvg (Q q) (w P π) (fun ω => s ω.1 ω.2) f

/-- The fiber-variance objective `J₁`. -/
def J1 : ℝ := ∑ ω : V × V, w P π ω * (s ω.1 ω.2 - fiberMean P q π s (Q q ω)) ^ 2

/-- One-step Fisher loss. -/
def loss1 : ℝ :=
  ScoreProjection.fineFisher (w P π) (d P π s)
    - ScoreProjection.coarseFisher (Q q) (w P π) (d P π s)

lemma w_pos (hP : ∀ x y, 0 < P x y) (hπ : ∀ x, 0 < π x) (ω : V × V) : 0 < w P π ω :=
  mul_pos (hπ _) (hP _ _)

/-- **The one-step loss is the fiber-variance objective.** -/
theorem loss1_eq_J1 (hP : ∀ x y, 0 < P x y) (hπ : ∀ x, 0 < π x) :
    loss1 P q π s = J1 P q π s := by
  unfold loss1 J1
  have hs : ∀ ω : V × V, d P π s ω / w P π ω = (fun _ : V × V => (0 : ℝ)) ω - (-(s ω.1 ω.2)) := by
    intro ω
    unfold d
    rw [mul_div_cancel_left₀ _ (w_pos P π hP hπ ω).ne']
    ring
  rw [ScoreProjection.fisherLoss_eq_condVar (Q q) (d P π s) (w_pos P π hP hπ)
    (fun _ => 0) (fun ω => -(s ω.1 ω.2)) (fun _ => 0) (fun _ => rfl) hs]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  congr 1
  have hneg : ScoreProjection.blockAvg (Q q) (w P π) (fun ω : V × V => -(s ω.1 ω.2)) (Q q ω)
      = -fiberMean P q π s (Q q ω) := by
    unfold fiberMean ScoreProjection.blockAvg
    rw [← neg_div, ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [hneg]
  ring

/-- **Zero one-step loss iff the step score is constant on every block pair.** -/
theorem loss1_eq_zero_iff (hP : ∀ x y, 0 < P x y) (hπ : ∀ x, 0 < π x) :
    loss1 P q π s = 0 ↔
      ∀ x x' y y', q x = q x' → q y = q y' → s x y = s x' y' := by
  rw [loss1_eq_J1 P q π s hP hπ]
  unfold J1
  constructor
  · intro h0 x x' y y' hx hy
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun ω _ =>
      mul_nonneg (w_pos P π hP hπ ω).le (sq_nonneg _))).mp h0
    have hfix : ∀ ω : V × V, s ω.1 ω.2 = fiberMean P q π s (Q q ω) := by
      intro ω
      have := hterm ω (Finset.mem_univ ω)
      rcases mul_eq_zero.mp this with hw | hsq
      · exact absurd hw (w_pos P π hP hπ ω).ne'
      · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
        linarith
    have h1 := hfix (x, y)
    have h2 := hfix (x', y')
    have hQ : Q q (x, y) = Q q (x', y') := by
      simp only [Q, hx, hy]
    simp only at h1 h2
    rw [h1, h2, hQ]
  · intro hc
    refine Finset.sum_eq_zero (fun ω _ => ?_)
    have hmean : fiberMean P q π s (Q q ω) = s ω.1 ω.2 := by
      unfold fiberMean ScoreProjection.blockAvg
      have hconst : ∀ ω' ∈ univ.filter (fun ω' : V × V => Q q ω' = Q q ω),
          w P π ω' * s ω'.1 ω'.2 = w P π ω' * s ω.1 ω.2 := by
        intro ω' hω'
        have hQ := (Finset.mem_filter.mp hω').2
        simp only [Q, Prod.mk.injEq] at hQ
        rw [hc ω'.1 ω.1 ω'.2 ω.2 hQ.1 hQ.2]
      rw [Finset.sum_congr rfl hconst, ← Finset.sum_mul]
      have hM : 0 < ScoreProjection.blockMass (Q q) (w P π) (Q q ω) :=
        Finset.sum_pos (fun ω' _ => w_pos P π hP hπ ω') ⟨ω, by simp⟩
      unfold ScoreProjection.blockMass at hM ⊢
      field_simp
    rw [hmean, sub_self]
    ring

end SGC.InformationGeometry.GeneralOneStep
