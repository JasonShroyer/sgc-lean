import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import FHDT.Core.Assumptions

noncomputable section
open Finset LinearMap Matrix Real ContinuousLinearMap

namespace FHDT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Isometry transporting L²(pi) to Euclidean space via diag(√pi).
    Renamed variable from π to pi_dist to resolve Windows encoding issues. -/
def iso_L2_to_std (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) : (V → ℝ) ≃ₗᵢ[ℝ] (V → ℝ) where
  toFun f v := f v * Real.sqrt (pi_dist v)
  invFun g v := g v / Real.sqrt (pi_dist v)
  left_inv f := by
    funext v
    have := Real.sqrt_ne_zero'.mpr (h_pos v)
    field_simp
  right_inv g := by
    funext v
    have := Real.sqrt_ne_zero'.mpr (h_pos v)
    field_simp
  map_add' f g := by
    funext v
    simp [Pi.add_apply]
    ring
  map_smul' r f := by
    funext v
    simp [smul_eq_mul]
    ring
  norm_map' := by
    intro f
    sorry

/-- The L²(pi) operator norm. -/
def opNorm_pi (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] (V → ℝ)) : ℝ :=
  sorry

lemma opNorm_pi_nonneg (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] (V → ℝ)) :
  0 ≤ opNorm_pi pi_dist h_pos A := by
  sorry

lemma opNorm_pi_comp (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) (A B : (V → ℝ) →ₗ[ℝ] (V → ℝ)) :
  opNorm_pi pi_dist h_pos (A ∘ₗ B) ≤ opNorm_pi pi_dist h_pos A * opNorm_pi pi_dist h_pos B := by
  sorry

/-- Canonical L²(pi) orthogonal projector onto 1^⊥. -/
def P_ortho_pi (pi_dist : V → ℝ) (h_sum : ∑ v, pi_dist v = 1) (h_pos : ∀ v, 0 < pi_dist v) :
  (V → ℝ) →ₗ[ℝ] (V → ℝ) :=
  sorry

end FHDT
