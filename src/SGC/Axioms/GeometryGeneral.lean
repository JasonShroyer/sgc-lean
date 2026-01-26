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

/-! ## Trace Norm and Distance

The trace norm (nuclear norm) is the quantum analog of the L¹ norm.
The trace distance is the quantum analog of total variation distance.
-/

/-- The trace norm (nuclear norm): ||A||₁ = Tr(√(A†A)).
    This is axiomatized; computing it requires spectral decomposition. -/
axiom traceNorm_pi (pi_dist : V → ℝ) (A : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) : ℝ

/-- Trace norm is nonnegative. -/
axiom traceNorm_pi_nonneg (pi_dist : V → ℝ) (A : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) :
    0 ≤ traceNorm_pi pi_dist A

/-- Trace norm of zero is zero. -/
axiom traceNorm_pi_zero (pi_dist : V → ℝ) :
    traceNorm_pi pi_dist (0 : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) = 0

/-- Triangle inequality for trace norm. -/
axiom traceNorm_pi_add (pi_dist : V → ℝ) (A B : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) :
    traceNorm_pi pi_dist (A + B) ≤ traceNorm_pi pi_dist A + traceNorm_pi pi_dist B

/-- Trace norm is invariant under negation: ||−A||₁ = ||A||₁. -/
axiom traceNorm_pi_neg (pi_dist : V → ℝ) (A : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) :
    traceNorm_pi pi_dist (-A) = traceNorm_pi pi_dist A

/-- The trace distance between density matrices: D(ρ,σ) = ½||ρ - σ||₁.
    This is the quantum analog of total variation distance. -/
def traceDistance_pi (pi_dist : V → ℝ) (ρ σ : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) : ℝ :=
  (1/2) * traceNorm_pi pi_dist (ρ - σ)

/-- Trace distance is symmetric. -/
lemma traceDistance_pi_symm (pi_dist : V → ℝ) (ρ σ : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) :
    traceDistance_pi pi_dist ρ σ = traceDistance_pi pi_dist σ ρ := by
  simp only [traceDistance_pi]
  congr 1
  -- σ - ρ = -(ρ - σ), so ||σ - ρ||₁ = ||-(ρ - σ)||₁ = ||ρ - σ||₁
  have h : σ - ρ = -(ρ - σ) := by abel
  rw [h, traceNorm_pi_neg]

/-- Trace distance is nonnegative. -/
lemma traceDistance_pi_nonneg (pi_dist : V → ℝ) (ρ σ : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) :
    0 ≤ traceDistance_pi pi_dist ρ σ := by
  unfold traceDistance_pi
  apply mul_nonneg (by norm_num : (0:ℝ) ≤ 1/2)
  exact traceNorm_pi_nonneg pi_dist _

/-- Trace distance satisfies triangle inequality. -/
lemma traceDistance_pi_triangle (pi_dist : V → ℝ) (ρ σ τ : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) :
    traceDistance_pi pi_dist ρ τ ≤ traceDistance_pi pi_dist ρ σ + traceDistance_pi pi_dist σ τ := by
  unfold traceDistance_pi
  have h : ρ - τ = (ρ - σ) + (σ - τ) := by abel
  calc (1/2) * traceNorm_pi pi_dist (ρ - τ)
      = (1/2) * traceNorm_pi pi_dist ((ρ - σ) + (σ - τ)) := by rw [h]
    _ ≤ (1/2) * (traceNorm_pi pi_dist (ρ - σ) + traceNorm_pi pi_dist (σ - τ)) := by
        apply mul_le_mul_of_nonneg_left (traceNorm_pi_add _ _ _) (by norm_num : (0:ℝ) ≤ 1/2)
    _ = (1/2) * traceNorm_pi pi_dist (ρ - σ) + (1/2) * traceNorm_pi pi_dist (σ - τ) := by ring

/-- Trace distance is bounded by 1 for density matrices. -/
axiom traceDistance_pi_le_one (pi_dist : V → ℝ) (ρ σ : (V → 𝕜) →ₗ[𝕜] (V → 𝕜))
    (hρ : IsDensityMatrix pi_dist ρ) (hσ : IsDensityMatrix pi_dist σ) :
    traceDistance_pi pi_dist ρ σ ≤ 1

/-! ## Fidelity

Fidelity measures the closeness of quantum states. F(ρ,σ) = 1 iff ρ = σ.
-/

/-- The fidelity between density matrices: F(ρ,σ) = (Tr√(√ρ σ √ρ))².
    For pure states |ψ⟩⟨ψ| and |φ⟩⟨φ|, this equals |⟨ψ|φ⟩|². -/
axiom fidelity_pi (pi_dist : V → ℝ) (ρ σ : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) : ℝ

/-- Fidelity is between 0 and 1 for density matrices. -/
axiom fidelity_pi_bounds (pi_dist : V → ℝ) (ρ σ : (V → 𝕜) →ₗ[𝕜] (V → 𝕜))
    (hρ : IsDensityMatrix pi_dist ρ) (hσ : IsDensityMatrix pi_dist σ) :
    0 ≤ fidelity_pi pi_dist ρ σ ∧ fidelity_pi pi_dist ρ σ ≤ 1

/-- Fidelity is symmetric. -/
axiom fidelity_pi_symm (pi_dist : V → ℝ) (ρ σ : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) :
    fidelity_pi pi_dist ρ σ = fidelity_pi pi_dist σ ρ

/-- Fidelity equals 1 iff the states are equal. -/
axiom fidelity_pi_eq_one_iff (pi_dist : V → ℝ) (ρ σ : (V → 𝕜) →ₗ[𝕜] (V → 𝕜))
    (hρ : IsDensityMatrix pi_dist ρ) (hσ : IsDensityMatrix pi_dist σ) :
    fidelity_pi pi_dist ρ σ = 1 ↔ ρ = σ

/-- Fuchs-van de Graaf inequality: relates trace distance and fidelity.
    1 - √F(ρ,σ) ≤ D(ρ,σ) ≤ √(1 - F(ρ,σ)) -/
axiom fuchs_van_de_graaf (pi_dist : V → ℝ) (ρ σ : (V → 𝕜) →ₗ[𝕜] (V → 𝕜))
    (hρ : IsDensityMatrix pi_dist ρ) (hσ : IsDensityMatrix pi_dist σ) :
    1 - Real.sqrt (fidelity_pi pi_dist ρ σ) ≤ traceDistance_pi pi_dist ρ σ ∧
    traceDistance_pi pi_dist ρ σ ≤ Real.sqrt (1 - fidelity_pi pi_dist ρ σ)

/-! ## Classical-Quantum Bridge

These lemmas connect the quantum trace distance to classical total variation.
For diagonal (classical) density matrices, trace distance equals TV distance.
-/

/-- A density matrix is classical (diagonal) if it commutes with all projectors onto
    computational basis states. This corresponds to a classical probability distribution. -/
def IsClassical_pi (pi_dist : V → ℝ) (ρ : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) : Prop :=
  ∀ x : V, ∀ u : V → 𝕜, ρ (fun y => if y = x then u x else 0) =
    fun y => if y = x then ρ u x else 0

/-- For classical (diagonal) density matrices, trace distance equals total variation.
    This is the key bridge lemma connecting quantum and classical information theory. -/
axiom traceDistance_classical_eq_TV (pi_dist : V → ℝ) (ρ σ : (V → 𝕜) →ₗ[𝕜] (V → 𝕜))
    (hρ_dm : IsDensityMatrix pi_dist ρ) (hσ_dm : IsDensityMatrix pi_dist σ)
    (hρ_cl : IsClassical_pi pi_dist ρ) (hσ_cl : IsClassical_pi pi_dist σ) :
    traceDistance_pi pi_dist ρ σ =
      (1/2) * ∑ x, |RCLike.re (ρ (fun y => if y = x then 1 else 0) x) -
                   RCLike.re (σ (fun y => if y = x then 1 else 0) x)|

end GeometryGeneral
end Axioms
end SGC
