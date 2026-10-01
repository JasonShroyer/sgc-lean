/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.InformationGeometry.DecisionValue
import SGC.InformationGeometry.EstimatedDecision

/-!
# Value of information is bounded by belief shift

Decision 0080 found that curiosity (belief change) selects a valueless observation a
third of the time when a valuable one exists — and never found value without belief
change. This module proves the second half and makes the first half precise.

For an observation `q` of a finite state with weights `w` (total `W > 0`), the
**belief shift** is the unnormalized `L¹` distance between the joint law
`w(x)·1[q x = b]` and the prior-proportional law `(M_b / W)·w(x)`:

  `shift(q) = Σ_b Σ_x | w x · 1[q x = b] − (M_b / W) · w x |`.

In normalized terms this is `2 · Σ_b P(b) · TV(P(· | b), P(·))`: twice the expected
total-variation change of belief on observing `q`.

## Results

* `voi_le_range_mul_shift` — for any utility with `|u a x − u a' x| ≤ R`,
  `V(q) − V(trivial) ≤ R · shift(q)`.
* `voi_eq_zero_of_shift_zero` — no belief change, no value.

So: **belief change upper-bounds decision value** (curiosity is a necessary screen);
decision 0078's witness shows it does not lower-bound it (curiosity is not sufficient).
Because `shift` needs no utilities, a controller can prune candidates with small shift
before computing `voi`. The Pinsker step from `shift` to mutual information is not
included here.
-/

noncomputable section

namespace SGC.InformationGeometry.BeliefShiftBound

open Finset DecisionValue

set_option linter.unusedSectionVars false

variable {Ω β α : Type*} [Fintype Ω] [Fintype β] [DecidableEq β] [Fintype α] [Nonempty α]

variable (q : Ω → β) (w : Ω → ℝ) (u : α → Ω → ℝ)

/-- Total weight. -/
def W : ℝ := ∑ x, w x

/-- Joint weight of `(x, b)`. -/
def joint (b : β) (x : Ω) : ℝ := if q x = b then w x else 0

/-- Prior-proportional weight of `(x, b)`. -/
def indep (b : β) (x : Ω) : ℝ := ScoreProjection.blockMass q w b / W w * w x

/-- Belief shift: `L¹` distance between the joint and the prior-proportional law. -/
def shift : ℝ := ∑ b, ∑ x, |joint q w b x - indep q w b x|

/-- The trivial observation. -/
def trivialObs : Ω → Unit := fun _ => ()

lemma blockUtility_eq_sum_joint (b : β) (a : α) :
    blockUtility q w u b a = ∑ x, joint q w b x * u a x := by
  unfold blockUtility joint
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl (fun x _ => by split_ifs <;> simp)

lemma blockUtility_trivial (a : α) :
    blockUtility (trivialObs (Ω := Ω)) w u () a = ∑ x, w x * u a x := by
  unfold blockUtility trivialObs
  simp

lemma sum_indep_mul (b : β) (a : α) :
    ∑ x, indep q w b x * u a x = ScoreProjection.blockMass q w b / W w * ∑ x, w x * u a x := by
  unfold indep
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun x _ => by ring)

lemma sum_blockUtility_fibers (a : α) :
    ∑ b, blockUtility q w u b a = ∑ x, w x * u a x := by
  unfold blockUtility
  exact (ScoreProjection.sum_fibers q (fun x => w x * u a x)).symm

/-- **Value of information is bounded by utility range times belief shift.** -/
theorem voi_le_range_mul_shift (hw : ∀ x, 0 ≤ w x) (hW : 0 < W w) {R : ℝ}
    (hR : ∀ a a' x, |u a x - u a' x| ≤ R) :
    value q w u - value (trivialObs (Ω := Ω)) w u ≤ R * shift q w := by
  -- optimal action for the prior
  obtain ⟨a₀, ha₀⟩ := exists_optimal (trivialObs (Ω := Ω)) w u ()
  have hV0 : value (trivialObs (Ω := Ω)) w u = ∑ x, w x * u a₀ x := by
    unfold value
    rw [Fintype.sum_unique, ← ha₀, blockUtility_trivial]
  have hmax : ∀ a, ∑ x, w x * u a x ≤ ∑ x, w x * u a₀ x := by
    intro a
    rw [← blockUtility_trivial w u a, ← blockUtility_trivial w u a₀, ha₀]
    exact blockUtility_le_blockValue _ w u () a
  -- write V(q) − V(trivial) as a sum over blocks of (blockValue − blockUtility at a₀)
  have hsplit : value q w u - value (trivialObs (Ω := Ω)) w u
      = ∑ b, (blockValue q w u b - blockUtility q w u b a₀) := by
    rw [Finset.sum_sub_distrib, sum_blockUtility_fibers, hV0]
    rfl
  rw [hsplit]
  unfold shift
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun b _ => ?_)
  -- per block: pick the block-optimal action
  obtain ⟨ab, hab⟩ := exists_optimal q w u b
  rw [← hab, blockUtility_eq_sum_joint, blockUtility_eq_sum_joint, ← Finset.sum_sub_distrib]
  have hM : 0 ≤ ScoreProjection.blockMass q w b / W w :=
    div_nonneg (Finset.sum_nonneg (fun x _ => hw x)) hW.le
  -- the prior-proportional part is ≤ 0
  have hind : ∑ x, indep q w b x * (u ab x - u a₀ x) ≤ 0 := by
    have : ∑ x, indep q w b x * (u ab x - u a₀ x)
        = ScoreProjection.blockMass q w b / W w * (∑ x, w x * u ab x - ∑ x, w x * u a₀ x) := by
      rw [← Finset.sum_sub_distrib]
      unfold indep
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [this]
    exact mul_nonpos_of_nonneg_of_nonpos hM (by linarith [hmax ab])
  calc ∑ x, (joint q w b x * u ab x - joint q w b x * u a₀ x)
      = ∑ x, (joint q w b x - indep q w b x) * (u ab x - u a₀ x)
          + ∑ x, indep q w b x * (u ab x - u a₀ x) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun x _ => by ring)
    _ ≤ ∑ x, (joint q w b x - indep q w b x) * (u ab x - u a₀ x) := by linarith
    _ ≤ ∑ x, |joint q w b x - indep q w b x| * R := by
        refine Finset.sum_le_sum (fun x _ => ?_)
        calc (joint q w b x - indep q w b x) * (u ab x - u a₀ x)
            ≤ |(joint q w b x - indep q w b x) * (u ab x - u a₀ x)| := le_abs_self _
          _ = |joint q w b x - indep q w b x| * |u ab x - u a₀ x| := abs_mul _ _
          _ ≤ |joint q w b x - indep q w b x| * R :=
              mul_le_mul_of_nonneg_left (hR ab a₀ x) (abs_nonneg _)
    _ = R * ∑ x, |joint q w b x - indep q w b x| := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun x _ => by ring)

theorem shift_nonneg : 0 ≤ shift q w :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))

/-- **No belief change, no value.** -/
theorem voi_eq_zero_of_shift_zero (hw : ∀ x, 0 ≤ w x) (hW : 0 < W w) {R : ℝ}
    (hR : ∀ a a' x, |u a x - u a' x| ≤ R) (hs : shift q w = 0) :
    value q w u - value (trivialObs (Ω := Ω)) w u = 0 := by
  have h1 := voi_le_range_mul_shift q w u hw hW hR
  rw [hs, mul_zero] at h1
  have h2 : value (trivialObs (Ω := Ω)) w u ≤ value q w u := by
    have := value_le_of_refine q (fun _ : β => ()) w u
    exact this
  linarith

theorem voi_le_estimated_shift (wHat : Ω → ℝ) (hwHat : ∀ x, 0 ≤ wHat x)
    (hW : 0 < W wHat) {R M : ℝ}
    (hR : ∀ a a' x, |u a x - u a' x| ≤ R) (hM : ∀ a x, |u a x| ≤ M) :
    value q w u - value (trivialObs (Ω := Ω)) w u ≤
      R * shift q wHat + 2 * (M * EstimatedDecision.l1Error w wHat) := by
  have hshift := voi_le_range_mul_shift q wHat u hwHat hW hR
  have herr := EstimatedDecision.voi_error_le q w wHat u (fun _ : β => ()) hM
  change |(value q w u - value (trivialObs (Ω := Ω)) w u) -
    (value q wHat u - value (trivialObs (Ω := Ω)) wHat u)| ≤ _ at herr
  have hupper := (abs_le.mp herr).2
  linarith

theorem prune_of_estimated_shift (wHat : Ω → ℝ) (hwHat : ∀ x, 0 ≤ wHat x)
    (hW : 0 < W wHat) {R M cost : ℝ}
    (hR : ∀ a a' x, |u a x - u a' x| ≤ R) (hM : ∀ a x, |u a x| ≤ M)
    (hcost : R * shift q wHat + 2 * (M * EstimatedDecision.l1Error w wHat) ≤ cost) :
    value q w u - cost ≤ value (trivialObs (Ω := Ω)) w u := by
  have h := voi_le_estimated_shift q w u wHat hwHat hW hR hM
  linarith

end SGC.InformationGeometry.BeliefShiftBound
