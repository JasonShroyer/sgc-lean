import FHDT.Core.Projector
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
open Matrix Real LinearMap Finset

namespace FHDT

variable {V : Type*} [Fintype V] [DecidableEq V] {pi_dist : V → ℝ}

/-- L²(pi)-unit coordinate at x. -/
def unit_coord_pi (pi_dist : V → ℝ) (hπ : ∀ x, 0 < pi_dist x) (x : V) : V → ℝ :=
  fun y => if y = x then (1 / Real.sqrt (pi_dist x)) else 0

lemma unit_coord_pi_norm_one (hπ : ∀ x, 0 < pi_dist x) (x : V) :
  norm_sq_pi pi_dist (unit_coord_pi pi_dist hπ x) = 1 := by
  unfold norm_sq_pi inner_pi unit_coord_pi
  -- The sum reduces to a single term where y = x
  have h_sum : ∑ y, pi_dist y * (if y = x then 1 / Real.sqrt (pi_dist x) else 0) * (if y = x then 1 / Real.sqrt (pi_dist x) else 0) = pi_dist x * (1 / Real.sqrt (pi_dist x)) * (1 / Real.sqrt (pi_dist x)) := by
    rw [Finset.sum_eq_single x]
    · simp
    · intros y _ hy
      simp [hy]
    · intro hx
      exfalso
      exact hx (Finset.mem_univ x)
  rw [h_sum]
  field_simp
  rw [Real.sq_sqrt (le_of_lt (hπ x))]
  exact div_self (ne_of_gt (hπ x))

lemma abs_diag_le_opNorm_pi (hπ : ∀ x, 0 < pi_dist x) (A_mat : Matrix V V ℝ) (x : V) :
  |A_mat x x| ≤ opNorm_pi pi_dist hπ (toLin' A_mat) := by
  let A := toLin' A_mat
  let u := unit_coord_pi pi_dist hπ x
  -- 1. Show that the diagonal element is the weighted inner product
  have h_diag : A_mat x x = inner_pi pi_dist u (A u) := by
    unfold inner_pi u unit_coord_pi A
    rw [Finset.sum_eq_single x]
    · simp only [ite_true, toLin'_apply]
      change A_mat x x = pi_dist x * (1 / Real.sqrt (pi_dist x)) * (∑ y, A_mat x y * (if y = x then 1 / Real.sqrt (pi_dist x) else 0))
      rw [Finset.sum_eq_single x]
      · simp only [ite_true]
        field_simp
        rw [Real.sq_sqrt (le_of_lt (hπ x))]
        rw [mul_div_assoc, div_self (ne_of_gt (hπ x)), mul_one]
      · intros y _ hy; simp [if_neg hy]
      · intro h; exact (h (Finset.mem_univ x)).elim
    · intros y _ hy; simp [if_neg hy]
    · intro h; exact (h (Finset.mem_univ x)).elim
  rw [h_diag]
  -- 2. Apply Cauchy-Schwarz from the clean API
  have h_cs := cauchy_schwarz_pi pi_dist hπ u (A u)
  apply le_trans h_cs
  -- 3. Apply Operator Norm Bound from the clean API
  have h_bound := opNorm_pi_bound pi_dist hπ A u
  have h_u_one : norm_pi pi_dist u = 1 := by
    rw [norm_pi, unit_coord_pi_norm_one hπ x, Real.sqrt_one]
  rw [h_u_one, mul_one] at h_bound
  rw [h_u_one, one_mul]
  exact h_bound

/--
**Pillar 3: The Diagonal Bridge**
The sum of absolute diagonal elements is bounded by the cardinality times the operator norm.
-/
lemma sum_abs_diag_le_card_opNorm (hπ : ∀ x, 0 < pi_dist x) (A_mat : Matrix V V ℝ) :
  ∑ x, |A_mat x x| ≤ Fintype.card V * opNorm_pi pi_dist hπ (toLin' A_mat) := by
  calc
    ∑ x, |A_mat x x| ≤ ∑ x, opNorm_pi pi_dist hπ (toLin' A_mat) := by
      apply Finset.sum_le_sum
      intro x _
      exact abs_diag_le_opNorm_pi hπ A_mat x
    _ = Fintype.card V * opNorm_pi pi_dist hπ (toLin' A_mat) := by
      simp [Finset.sum_const, Nat.card_eq_fintype_card]

end FHDT
