import FHDT.Core.Assumptions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.QuadraticForm.Isometry

noncomputable section
open Finset LinearMap Matrix Real

namespace FHDT

variable {V : Type*} [Fintype V]

/-- The isometry from L²(π) to standard Euclidean space. -/
def iso_L2_to_std (π : V → ℝ) (h_pos : ∀ v, 0 < π v) : (V → ℝ) ≃ₗᵢ[ℝ] (V → ℝ) :=
  LinearEquiv.ofIsometry
    (fun v => fun x => v x / sqrt (π x))
    (fun v => fun x => v x * sqrt (π x))
    sorry -- proof of isometry
    sorry -- proof of linear

/-- The L²(π) operator norm via the isometry. -/
def opNorm_pi (π : V → ℝ) (h_pos : ∀ v, 0 < π v) (A : (V → ℝ) →ₗ[ℝ] (V → ℝ)) : ℝ :=
  LinearMap.opNorm (iso_L2_to_std π h_pos ∘ A ∘ (iso_L2_to_std π h_pos).symm)

/-- The orthogonal projector onto 1^⊥ in L²(π). -/
def P_ortho_pi (π : V → ℝ) : (V → ℝ) →ₗ[ℝ] (V → ℝ) :=
  LinearMap.id - LinearMap.smulRight (inner_pi π · constant_vec_one) constant_vec_one

/-- Helper lemma: P_ortho_pi is self-adjoint. -/
lemma P_ortho_pi_is_selfAdj {π : V → ℝ} (h_pos : ∀ v, 0 < π v) :
    LinearMap.adjoint (P_ortho_pi π) = P_ortho_pi π := sorry

/-- Helper lemma: P_ortho_pi is idempotent. -/
lemma P_ortho_pi_is_idempotent {π : V → ℝ} :
    (P_ortho_pi π).comp (P_ortho_pi π) = P_ortho_pi π := sorry

end FHDT
