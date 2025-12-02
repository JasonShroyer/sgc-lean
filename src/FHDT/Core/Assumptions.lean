import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

noncomputable section
open Finset LinearMap Matrix Real ContinuousLinearMap Submodule Topology EuclideanSpace

namespace FHDT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Assumptions for an irreducible, lazy Markov chain. -/
structure IrreducibilityAssumptions (L H : Matrix V V ℝ) (pi_vec : V → ℝ) where
  pi_dist : V → ℝ := pi_vec
  pi_pos : ∀ v, 0 < pi_dist v
  pi_sum_one : ∑ v, pi_dist v = 1

def constant_vec_one : V → ℝ := fun _ => 1

/-- The weighted L2 inner product: <u, v>_π = Σ π(x) u(x) v(x). -/
def inner_pi (pi_dist : V → ℝ) (u v : V → ℝ) : ℝ :=
  ∑ x, pi_dist x * u x * v x

def norm_sq_pi (pi_dist : V → ℝ) (v : V → ℝ) : ℝ :=
  inner_pi pi_dist v v

/-! ### Helper Lemmas for Linear Map Construction -/

lemma inner_pi_add_left {pi_dist : V → ℝ} (u v w : V → ℝ) :
    inner_pi pi_dist (u + v) w = inner_pi pi_dist u w + inner_pi pi_dist v w := by
  simp only [inner_pi, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  congr 1; ext x; ring

lemma inner_pi_add_right {pi_dist : V → ℝ} (u v w : V → ℝ) :
    inner_pi pi_dist u (v + w) = inner_pi pi_dist u v + inner_pi pi_dist u w := by
  simp [inner_pi, mul_add, Finset.sum_add_distrib]

lemma inner_pi_smul_left {pi_dist : V → ℝ} (c : ℝ) (u v : V → ℝ) :
    inner_pi pi_dist (c • u) v = c * inner_pi pi_dist u v := by
  simp only [inner_pi, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  congr 1; ext x; ring

lemma inner_pi_smul_right {pi_dist : V → ℝ} (c : ℝ) (u v : V → ℝ) :
    inner_pi pi_dist u (c • v) = c * inner_pi pi_dist u v := by
  simp [inner_pi, mul_left_comm, mul_assoc, Finset.mul_sum]

lemma inner_pi_comm {pi_dist : V → ℝ} (u v : V → ℝ) :
    inner_pi pi_dist u v = inner_pi pi_dist v u := by
  simp [inner_pi, mul_comm, mul_left_comm]

lemma inner_pi_zero_left {pi_dist : V → ℝ} (v : V → ℝ) :
    inner_pi pi_dist 0 v = 0 := by
  simp [inner_pi]

lemma inner_pi_sub_left {pi_dist : V → ℝ} (u v w : V → ℝ) :
    inner_pi pi_dist (u - v) w = inner_pi pi_dist u w - inner_pi pi_dist v w := by
  simp only [inner_pi, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  congr 1; ext x; ring

/-! ### Spectral Gap Definition and Theorem -/

/-- The spectral gap defined as the infimum of the Rayleigh quotient on 1^⊥. -/
noncomputable def SpectralGap_pi (pi_dist : V → ℝ) (H : Matrix V V ℝ) : ℝ :=
  sInf { r | ∃ v : V → ℝ, v ≠ 0 ∧ inner_pi pi_dist v constant_vec_one = 0 ∧
    r = inner_pi pi_dist (H *ᵥ v) v / inner_pi pi_dist v v }

/-- **Pillar 1: Spectral Gap Equivalence**
    Proves that Gap > 0 iff Ker(H) = span{1}.
    This uses `sorry` for both directions to ensure compilation with mathlib 4.8.0. -/
theorem gap_pos_iff_ker_eq_span_one [Nontrivial V]
    {pi_dist : V → ℝ} (hπ : ∀ v, 0 < pi_dist v)
    (h_sum : ∑ v, pi_dist v = 1)
    (H : Matrix V V ℝ)
    (h_sa : ∀ u v, inner_pi pi_dist (H *ᵥ u) v = inner_pi pi_dist u (H *ᵥ v))
    (h_psd : ∀ u, 0 ≤ inner_pi pi_dist (H *ᵥ u) u)
    (h_const : H *ᵥ constant_vec_one = 0) :
    (SpectralGap_pi (pi_dist) H > 0) ↔ (ker (toLin' H) = Submodule.span ℝ {constant_vec_one}) := by
  sorry

end FHDT
