import FHDT.Core.Projector
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section
open Matrix Real LinearMap Finset

namespace FHDT

variable {V : Type*} [Fintype V] [DecidableEq V] {pi_dist : V → ℝ}

/-- L²(pi)-unit coordinate at x. -/
def unit_coord_pi (pi_dist : V → ℝ) (hπ : ∀ x, 0 < pi_dist x) (x : V) : V → ℝ :=
  fun y => if y = x then (1 / Real.sqrt (pi_dist x)) else 0

lemma unit_coord_pi_norm_one (hπ : ∀ x, 0 < pi_dist x) (x : V) :
  norm_sq_pi pi_dist (unit_coord_pi pi_dist hπ x) = 1 := by
  sorry

lemma diag_as_rayleigh (hπ : ∀ x, 0 < pi_dist x) (A : (V → ℝ) →ₗ[ℝ] (V → ℝ)) (x : V) :
  (A (unit_coord_pi pi_dist hπ x)) x / (Real.sqrt (pi_dist x)) =
  inner_pi pi_dist (unit_coord_pi pi_dist hπ x) (A (unit_coord_pi pi_dist hπ x)) := by
  sorry

/-- Bounds the diagonal element by the operator norm. -/
lemma abs_diag_le_opNorm_pi (hπ : ∀ x, 0 < pi_dist x) (A_mat : Matrix V V ℝ) (x : V) :
  |A_mat x x| ≤ opNorm_pi pi_dist hπ (toLin' A_mat) := by
  sorry

/--
**Pillar 3: The Diagonal Bridge**
The sum of absolute diagonal elements is bounded by the cardinality times the operator norm.
-/
lemma sum_abs_diag_le_card_opNorm (hπ : ∀ x, 0 < pi_dist x) (A_mat : Matrix V V ℝ) :
  ∑ x, |A_mat x x| ≤ Fintype.card V * opNorm_pi pi_dist hπ (toLin' A_mat) := by
  sorry

end FHDT
