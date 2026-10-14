/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith

/-!
# The net benefit of projecting onto an approximate invariant subspace (P34)

Let `P` be an orthogonal projector on a real inner product space (idempotent and self-adjoint: the Reynolds
average over a discovered relation set when the data measure is invariant under it, or the projection onto the
complement of a proposed irrelevant subspace). For a target `y` and any predictor `f`,

`‖f − y‖² − ‖P f − y‖² = ‖(1 − P)(f − y)‖² − ‖(1 − P) y‖²`.

The left side is the net generalization benefit of repairing `f` to `P f`; the right side is the error removed
minus the *misspecification bias* `‖(1−P) y‖²` — zero when the target is invariant under the projected
relations (false negatives at the edge of discovery cost nothing), and second order in the principal angle
between the proposed and true subspaces when they tilt (`‖(1−P) y‖ ≤ ‖(1−P) P*‖ ‖y‖`). The operational form:
benefit `≥ ½ ‖(1−P) f‖² − 2 ‖(1−P) y‖²` — the learner's measurable defect against twice the bias — which is the
statement that acting on approximately correct relations (0115, arm R2) is justified exactly when the defect it
removes exceeds twice the bias it introduces.

This generalizes the strict-benefit theorem of Elesedy–Zaidi (2021) from a known group to any orthogonal
projector; it is an `L²` identity for squared loss, not a statement about 0–1 error.
-/

namespace SGC.Bridge.ApproxInvarianceBenefit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => @inner ℝ E _ x y

/-- Pythagoras for an orthogonal projector: `‖v‖² = ‖P v‖² + ‖v − P v‖²`. -/
theorem norm_sq_split (P : E →ₗ[ℝ] E) (hself : ∀ x z, ⟪P x, z - P z⟫ = 0) (v : E) :
    ‖v‖ ^ 2 = ‖P v‖ ^ 2 + ‖v - P v‖ ^ 2 := by
  have h : v = P v + (v - P v) := by abel
  have horth : ⟪P v, v - P v⟫ = 0 := hself v v
  calc ‖v‖ ^ 2 = ‖P v + (v - P v)‖ ^ 2 := by rw [← h]
    _ = ‖P v‖ ^ 2 + 2 * ⟪P v, v - P v⟫ + ‖v - P v‖ ^ 2 := norm_add_sq_real _ _
    _ = ‖P v‖ ^ 2 + ‖v - P v‖ ^ 2 := by rw [horth]; ring

/-- **P34 (identity).** `‖f − y‖² − ‖P f − y‖² = ‖(f − y) − P (f − y)‖² − ‖y − P y‖²`. -/
theorem approx_invariance_benefit (P : E →ₗ[ℝ] E) (hidem : ∀ x, P (P x) = P x)
    (hself : ∀ x z, ⟪P x, z - P z⟫ = 0) (f y : E) :
    ‖f - y‖ ^ 2 - ‖P f - y‖ ^ 2 = ‖(f - y) - P (f - y)‖ ^ 2 - ‖y - P y‖ ^ 2 := by
  have h1 := norm_sq_split P hself (f - y)
  -- P f − y = P (f − y) − (y − P y), and the two pieces are orthogonal
  have hdecomp : P f - y = P (f - y) - (y - P y) := by
    rw [map_sub]; abel
  have horth : ⟪P (f - y), y - P y⟫ = 0 := hself (f - y) y
  have h2 : ‖P f - y‖ ^ 2 = ‖P (f - y)‖ ^ 2 + ‖y - P y‖ ^ 2 := by
    rw [hdecomp, norm_sub_sq_real, horth]; ring
  linarith

/-- `‖a‖² ≤ 2 ‖a − b‖² + 2 ‖b‖²`. -/
theorem norm_sq_le_two (a b : E) : ‖a‖ ^ 2 ≤ 2 * ‖a - b‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h : a = (a - b) + b := by abel
  have hle : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
    calc ‖a‖ = ‖(a - b) + b‖ := by rw [← h]
      _ ≤ ‖a - b‖ + ‖b‖ := norm_add_le _ _
  have h0 : 0 ≤ ‖a‖ := norm_nonneg _
  have h3 : ‖a‖ ^ 2 ≤ (‖a - b‖ + ‖b‖) ^ 2 := by
    have hnn : 0 ≤ ‖a - b‖ + ‖b‖ := by positivity
    nlinarith [mul_le_mul hle hle h0 hnn]
  nlinarith [sq_nonneg (‖a - b‖ - ‖b‖)]

/-- **P34 (operational form).** Net benefit `≥ ½ ‖(1−P) f‖² − 2 ‖(1−P) y‖²`: the measurable defect of the
predictor against twice the misspecification bias. -/
theorem approx_invariance_benefit_lower (P : E →ₗ[ℝ] E) (hidem : ∀ x, P (P x) = P x)
    (hself : ∀ x z, ⟪P x, z - P z⟫ = 0) (f y : E) :
    ‖f - y‖ ^ 2 - ‖P f - y‖ ^ 2 ≥ (1 / 2) * ‖f - P f‖ ^ 2 - 2 * ‖y - P y‖ ^ 2 := by
  have hid := approx_invariance_benefit P hidem hself f y
  -- (f − y) − P(f − y) = (f − P f) − (y − P y)
  have hsplit : (f - y) - P (f - y) = (f - P f) - (y - P y) := by rw [map_sub]; abel
  have h2 := norm_sq_le_two (f - P f) (y - P y)
  rw [hsplit] at hid
  linarith

/-- False negatives at the edge cost nothing: if the target is already invariant (`P y = y`), the bias term
vanishes and the benefit equals the removed defect. -/
theorem benefit_of_invariant_target (P : E →ₗ[ℝ] E) (hidem : ∀ x, P (P x) = P x)
    (hself : ∀ x z, ⟪P x, z - P z⟫ = 0) (f y : E) (hy : P y = y) :
    ‖f - y‖ ^ 2 - ‖P f - y‖ ^ 2 = ‖(f - y) - P (f - y)‖ ^ 2 := by
  rw [approx_invariance_benefit P hidem hself f y, hy, sub_self, norm_zero]; ring

end SGC.Bridge.ApproxInvarianceBenefit
