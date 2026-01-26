import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Real.Basic

noncomputable section

namespace SGC
namespace Axioms
namespace GeometryGeneral

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {𝕜 : Type*} [RCLike 𝕜]

abbrev constant_vec_one : V → 𝕜 := fun _ => 1

def inner_pi (pi_dist : V → ℝ) (u v : V → 𝕜) : 𝕜 :=
  ∑ x, (pi_dist x : 𝕜) * star (u x) * v x

def norm_sq_pi (pi_dist : V → ℝ) (v : V → 𝕜) : ℝ :=
  RCLike.re (inner_pi pi_dist v v)

def norm_pi (pi_dist : V → ℝ) (v : V → 𝕜) : ℝ :=
  Real.sqrt (norm_sq_pi pi_dist v)

lemma inner_pi_add_left (pi_dist : V → ℝ) (u v w : V → 𝕜) :
    inner_pi pi_dist (u + v) w = inner_pi pi_dist u w + inner_pi pi_dist v w := by
  simp [inner_pi, mul_add, add_mul, Finset.sum_add_distrib]

lemma inner_pi_add_right (pi_dist : V → ℝ) (u v w : V → 𝕜) :
    inner_pi pi_dist u (v + w) = inner_pi pi_dist u v + inner_pi pi_dist u w := by
  simp [inner_pi, mul_add, Finset.sum_add_distrib]

lemma inner_pi_smul_left (pi_dist : V → ℝ) (c : 𝕜) (u v : V → 𝕜) :
    inner_pi pi_dist (c • u) v = star c * inner_pi pi_dist u v := by
  classical
  unfold inner_pi
  -- Expand RHS to a sum, then compare termwise.
  rw [Finset.mul_sum]
  -- `star (c • u x) = star c * star (u x)` and reassociate.
  simp [Pi.smul_apply, mul_assoc, mul_left_comm, mul_comm]

lemma inner_pi_smul_right (pi_dist : V → ℝ) (c : 𝕜) (u v : V → 𝕜) :
    inner_pi pi_dist u (c • v) = c * inner_pi pi_dist u v := by
  classical
  unfold inner_pi
  rw [Finset.mul_sum]
  simp [Pi.smul_apply, mul_assoc, mul_left_comm, mul_comm]

lemma inner_pi_conj_symm (pi_dist : V → ℝ) (u v : V → 𝕜) :
    inner_pi pi_dist u v = star (inner_pi pi_dist v u) := by
  simp [inner_pi, mul_assoc, mul_left_comm, mul_comm]

/-! ## Hermitian Operators

For quantum applications, we need operators that are self-adjoint with respect to
the weighted Hermitian inner product. Over ℂ, this corresponds to Hermitian matrices;
over ℝ, this reduces to symmetric matrices.
-/

/-- An operator A is self-adjoint w.r.t. the weighted inner product if ⟨Au, v⟩ = ⟨u, Av⟩.
    For quantum Hamiltonians, this ensures real eigenvalues and orthogonal eigenvectors. -/
def IsSelfAdjoint_pi (pi_dist : V → ℝ) (A : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) : Prop :=
  ∀ u v, inner_pi pi_dist (A u) v = inner_pi pi_dist u (A v)

/-- An operator A is positive w.r.t. the weighted inner product if ⟨Au, u⟩ ≥ 0 for all u.
    Combined with self-adjointness, this gives a positive semidefinite operator. -/
def IsPositive_pi (pi_dist : V → ℝ) (A : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) : Prop :=
  ∀ u, 0 ≤ RCLike.re (inner_pi pi_dist (A u) u)

/-- For self-adjoint operators, ⟨Au, u⟩ is real-valued (imaginary part is zero).
    Proof: ⟨Au,u⟩ = star⟨u,Au⟩ = star⟨Au,u⟩ by self-adjointness, so z = star z. -/
axiom inner_self_adjoint_real (pi_dist : V → ℝ) (A : (V → 𝕜) →ₗ[𝕜] (V → 𝕜))
    (hA : IsSelfAdjoint_pi pi_dist A) (u : V → 𝕜) :
    RCLike.im (inner_pi pi_dist (A u) u) = 0

/-! ## Spectral Gap (Generalized)

The spectral gap is the infimum of the Rayleigh quotient ⟨Hu,u⟩/⟨u,u⟩ over
vectors orthogonal to the constant function. -/

/-- The spectral gap of a self-adjoint operator H, defined as the infimum of the
    Rayleigh quotient on vectors orthogonal to the constant function. -/
noncomputable def SpectralGap_pi (pi_dist : V → ℝ) (H : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) : ℝ :=
  sInf { r | ∃ v : V → 𝕜, v ≠ 0 ∧ inner_pi pi_dist v constant_vec_one = 0 ∧
    r = RCLike.re (inner_pi pi_dist (H v) v) / norm_sq_pi pi_dist v }

/-! ## Trace Operations

For density matrices, we need trace and trace norm. -/

/-- The weighted trace: Tr_π(A) = Σ_x π(x) A(x,x).
    For density matrices, this should equal 1. -/
def trace_pi (pi_dist : V → ℝ) (A : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) : 𝕜 :=
  ∑ x, (pi_dist x : 𝕜) * A (fun y => if y = x then 1 else 0) x

/-- A density matrix is a positive operator with trace 1. -/
structure IsDensityMatrix (pi_dist : V → ℝ) (ρ : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) : Prop where
  self_adjoint : IsSelfAdjoint_pi pi_dist ρ
  positive : IsPositive_pi pi_dist ρ
  trace_one : trace_pi pi_dist ρ = 1

end GeometryGeneral
end Axioms
end SGC
