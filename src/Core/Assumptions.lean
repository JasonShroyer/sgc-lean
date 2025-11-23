import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open Finset LinearMap Matrix Real ContinuousLinearMap Submodule Topology

namespace FHDT

variable {V : Type*} [Fintype V]

/-- Structure capturing the irreducible, lazy Markov chain assumptions. -/
structure IrreducibilityAssumptions (L H : Matrix V V ℝ) (π_vec : V → ℝ) where
  π : V → ℝ := π_vec
  pi_pos : ∀ v, 0 < π v
  pi_sum_one : ∑ v, π v = 1

/-- The constant vector of value 1. -/
def constant_vec_one : V → ℝ := fun _ => 1

/-- The L²(π) inner product. -/
def inner_pi (π : V → ℝ) (u v : V → ℝ) : ℝ :=
  ∑ x, π x * u x * v x

/-- The L²(π) squared norm. -/
def norm_sq_pi (π : V → ℝ) (v : V → ℝ) : ℝ :=
  inner_pi π v v

/--
SpectralGap_pi: The infimum of the Rayleigh quotient of H on the L²(π)-orthogonal
complement of constants.
Defined purely in terms of the weighted inner product to match the system geometry.
Convention: H = -(L + L†)/2 in L²(π).
-/
noncomputable def SpectralGap_pi (π : V → ℝ) (H : Matrix V V ℝ) : ℝ :=
  sInf { r | ∃ v : V → ℝ, v ≠ 0 ∧ inner_pi π v constant_vec_one = 0 ∧
    r = inner_pi π (H *ᵥ v) v / inner_pi π v v }

/-- Witness that 1^⊥ is non-empty in dimension ≥ 2 using explicit coordinates. -/
lemma exists_nonzero_ortho_one [Nontrivial V] {π : V → ℝ} (hπ : ∀ x, 0 < π x) :
    ∃ v : V → ℝ, v ≠ 0 ∧ inner_pi π v constant_vec_one = 0 := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne V
  let v : V → ℝ := fun x => (if x = i then π j else 0) - (if x = j then π i else 0)
  have hne : v ≠ 0 := by
    intro hv; have := congrArg (fun f => f i) hv
    simp [v, hij.ne] at this; exact (hπ j).ne.symm this
  have hortho : inner_pi π v constant_vec_one = 0 := by
    simp [inner_pi, v, constant_vec_one, Finset.sum_ite, Finset.mem_univ, hij.ne,
      mul_comm, mul_left_comm, mul_assoc]
  exact ⟨v, hne, hortho⟩

/-- Strict denominator positivity for Rayleigh quotients. -/
lemma inner_pi_pos_of_ne_zero {π : V → ℝ} (hπ : ∀ x, 0 < π x) {v : V → ℝ} (hv : v ≠ 0) :
    0 < inner_pi π v v := by
  obtain ⟨x0, hx0⟩ : ∃ x, v x ≠ 0 := Function.ne_iff.mp hv
  have term_pos : 0 < π x0 * v x0 * v x0 := by
    have : 0 < (v x0)^2 := by simpa [pow_two] using sq_pos_of_ne_zero (v x0) hx0
    nlinarith [hπ x0, this]
  have : 0 < ∑ x, π x * v x * v x := by
    refine lt_of_le_of_lt (Finset.single_le_sum
      (by intro x _; exact mul_nonneg (le_of_lt (hπ x)) (mul_self_nonneg _))
      (Finset.mem_univ x0)) term_pos
  simpa [inner_pi] using this

/-- Quadratic nonnegativity implies vanishing linear term. -/
lemma quad_nonneg_linear_zero {a b : ℝ}
    (ha : 0 ≤ a) (h : ∀ t : ℝ, 0 ≤ a * t^2 + 2 * b * t) : b = 0 := by
  by_cases hA : a = 0
  · have h1 := h 1; have h2 := h (-1)
    simp [hA] at h1 h2
    have : 0 ≤ 2*b ∧ 0 ≤ -2*b := ⟨h1, h2⟩
    linarith
  · have ha_pos : 0 < a := lt_of_le_of_ne ha hA.symm
    have hmin := h (-(b/a))
    have : 0 ≤ a * (b/a)^2 - 2*b * (b/a) := by
      simpa [pow_two, mul_left_comm, mul_assoc, mul_comm, two_mul] using hmin
    have : 0 ≤ - (b^2) / a := by field_simp [this, ha_pos.ne']
    have : 0 ≤ - (b^2) := by nlinarith [ha_pos]
    have : b = 0 := by nlinarith
    exact this

/-- For a PSD operator, <Hv, v> = 0 implies Hv = 0. -/
lemma psd_inner_zero_implies_kernel
    {π : V → ℝ} (hπ : ∀ x, 0 < π x) (H : Matrix V V ℝ)
    (h_sa : ∀ u v, inner_pi π (H *ᵥ u) v = inner_pi π u (H *ᵥ v))
    (h_psd : ∀ u, 0 ≤ inner_pi π (H *ᵥ u) u)
    {v : V → ℝ} (h0 : inner_pi π (H *ᵥ v) v = 0) :
    H *ᵥ v = 0 := by
  have lin_zero : ∀ w, inner_pi π (H *ᵥ v) w = 0 := by
    intro w
    let q : ℝ → ℝ := fun t => inner_pi π (H *ᵥ (v + t • w)) (v + t • w)
    have q_exp : ∀ t, q t = inner_pi π (H *ᵥ w) w * t^2 + 2 * inner_pi π (H *ᵥ v) w * t := by
      intro t
      simp [q, Matrix.mulVec_add, Matrix.mulVec_smul, inner_pi, mul_add, add_mul,
        Finset.sum_add_distrib, h_sa, h0, two_mul]
    have : inner_pi π (H *ᵥ v) w = 0 := by
      have ha : 0 ≤ inner_pi π (H *ᵥ w) w := h_psd w
      refine quad_nonneg_linear_zero ha (by intro t; simpa [q_exp t] using h_psd _)
    simpa using this
  ext x
  let w : V → ℝ := fun z => if z = x then 1 else 0
  have hz : inner_pi π (H *ᵥ v) w = 0 := lin_zero w
  have : π x * (H *ᵥ v) x = 0 := by
    simpa [inner_pi, w, Finset.sum_ite, Finset.mem_univ, mul_one] using hz
