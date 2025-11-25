import os

content = """import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.NormedSpace.FiniteDimension

noncomputable section
open Finset LinearMap Matrix Real ContinuousLinearMap Submodule Topology EuclideanSpace

namespace FHDT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Structure capturing the irreducible, lazy Markov chain assumptions. -/
structure IrreducibilityAssumptions (L H : Matrix V V ℝ) (pi_vec : V → ℝ) where
  pi_dist : V → ℝ := pi_vec
  pi_pos : ∀ v, 0 < pi_dist v
  pi_sum_one : ∑ v, pi_dist v = 1

/-- The constant vector of value 1. -/
def constant_vec_one : V → ℝ := fun _ => 1

/-- The L²(pi) inner product. -/
def inner_pi (pi_dist : V → ℝ) (u v : V → ℝ) : ℝ :=
  ∑ x, pi_dist x * u x * v x

/-- The L²(pi) squared norm. -/
def norm_sq_pi (pi_dist : V → ℝ) (v : V → ℝ) : ℝ :=
  inner_pi pi_dist v v

/--
SpectralGap_pi: The infimum of the Rayleigh quotient of H on the L²(pi)-orthogonal
complement of constants.
-/
noncomputable def SpectralGap_pi (pi_dist : V → ℝ) (H : Matrix V V ℝ) : ℝ :=
  sInf { r |
    ∃ v : V → ℝ, v ≠ 0 ∧ inner_pi pi_dist v constant_vec_one = 0 ∧
    r = inner_pi pi_dist (H *ᵥ v) v / inner_pi pi_dist v v }

/-- Witness that 1^⊥ is non-empty in dimension ≥ 2 using explicit coordinates. -/
lemma exists_nonzero_ortho_one [Nontrivial V] {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x) :
    ∃ v : V → ℝ, v ≠ 0 ∧ inner_pi pi_dist v constant_vec_one = 0 := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne V
  let v : V → ℝ := fun x => (if x = i then pi_dist j else 0) - (if x = j then pi_dist i else 0)
  have hne : v ≠ 0 := by
    intro hv
    have h_at_i := congr_fun hv i
    simp [v, hij] at h_at_i
    apply (ne_of_gt (hπ j))
    exact h_at_i.symm
  have hortho : inner_pi pi_dist v constant_vec_one = 0 := by
    simp [inner_pi, v, constant_vec_one, Finset.sum_ite, Finset.mem_univ, hij,
      mul_comm, mul_left_comm, mul_assoc]
  exact ⟨v, hne, hortho⟩

/-- Strict denominator positivity for Rayleigh quotients. -/
lemma inner_pi_pos_of_ne_zero {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x) {v : V → ℝ} (hv : v ≠ 0) :
    0 < inner_pi pi_dist v v := by
  obtain ⟨x0, hx0⟩ : ∃ x, v x ≠ 0 := Function.ne_iff.mp hv
  have term_pos : 0 < pi_dist x0 * v x0 * v x0 := by
    have : 0 < (v x0)^2 := sq_pos_of_ne_zero hx0
    nlinarith [hπ x0, this]
  have : 0 < ∑ x, pi_dist x * v x * v x := by
    apply lt_of_lt_of_le term_pos
    -- Explicitly provide the set (univ) to avoid unification failure
    refine Finset.single_le_sum (fun x _ => ?_) (Finset.mem_univ x0)
    apply mul_nonneg (le_of_lt (hπ x)) (mul_self_nonneg _)
  simpa [inner_pi] using this

/-- Quadratic nonnegativity implies vanishing linear term. -/
lemma quad_nonneg_linear_zero {a b : ℝ}
    (ha : 0 ≤ a) (h : ∀ t : ℝ, 0 ≤ a * t^2 + 2 * b * t) : b = 0 := by
  by_cases hA : a = 0
  · have h1 := h 1
    have h2 := h (-1)
    simp [hA] at h1 h2
    linarith
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm hA)
    have hmin := h (-(b/a))
    have : 0 ≤ a * (-(b/a))^2 + 2 * b * (-(b/a)) := hmin
    field_simp [hA] at this
    have : 0 ≤ - (b^2) / a := by nlinarith
    -- Fix: Use ne_of_gt explicitly for division logic
    have : b^2 ≤ 0 := by
      rw [le_div_iff₀ (ne_of_gt ha_pos)] at this
      linarith
    have : b = 0 := by nlinarith
    exact this

/-- For a PSD operator, <Hv, v> = 0 implies Hv = 0. -/
lemma psd_inner_zero_implies_kernel
    {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x) (H : Matrix V V ℝ)
    (h_sa : ∀ u v, inner_pi pi_dist (H *ᵥ u) v = inner_pi pi_dist u (H *ᵥ v))
    (h_psd : ∀ u, 0 ≤ inner_pi pi_dist (H *ᵥ u) u)
    {v : V → ℝ} (h0 : inner_pi pi_dist (H *ᵥ v) v = 0) :
    H *ᵥ v = 0 := by
  have lin_zero : ∀ w, inner_pi pi_dist (H *ᵥ v) w = 0 := by
    intro w
    let q : ℝ → ℝ := fun t => inner_pi pi_dist (H *ᵥ (v + t • w)) (v + t • w)
    have q_exp : ∀ t, q t = inner_pi pi_dist (H *ᵥ w) w * t^2 + 2 * inner_pi pi_dist (H *ᵥ v) w * t := by
      intro t
      simp [q, Matrix.mulVec_add, Matrix.mulVec_smul, inner_pi, mul_add, add_mul,
        Finset.sum_add_distrib, h_sa, h0, two_mul]
    have : inner_pi pi_dist (H *ᵥ v) w = 0 := by
      have ha : 0 ≤ inner_pi pi_dist (H *ᵥ w) w := h_psd w
      refine quad_nonneg_linear_zero ha (by intro t; simpa [q_exp t] using h_psd _)
    simpa using this
  ext x
  let w : V → ℝ := fun z => if z = x then 1 else 0
  have hz : inner_pi pi_dist (H *ᵥ v) w = 0 := lin_zero w
  have : pi_dist x * (H *ᵥ v) x = 0 := by
    simpa [inner_pi, w, Finset.sum_ite, Finset.mem_univ, mul_one] using hz
  exact (mul_eq_zero.mp this).resolve_left (ne_of_gt (hπ x))

theorem gap_pos_iff_ker_eq_span_one [Nontrivial V] {pi_dist : V → ℝ} (hπ : ∀ v, 0 < pi_dist v)
    (h_sum : ∑ v, pi_dist v = 1)
    (H : Matrix V V ℝ)
    (h_sa : ∀ u v, inner_pi pi_dist (H *ᵥ u) v = inner_pi pi_dist u (H *ᵥ v))
    (h_psd : ∀ u, 0 ≤ inner_pi pi_dist (H *ᵥ u) u)
    (h_const : H *ᵥ constant_vec_one = 0) :
    (SpectralGap_pi (pi_dist) H > 0) ↔ (ker (toLin' H) = Submodule.span ℝ {constant_vec_one}) := by
  constructor
  · -- Forward: Gap > 0 implies kernel is exactly span {1}
    intro h_gap
    refine le_antisymm (Submodule.span_le.mpr ?_) ?_
    · rw [SetLike.mem_coe, LinearMap.mem_ker]
      exact h_const
    intro v hv
    have h11 : inner_pi pi_dist constant_vec_one constant_vec_one = 1 := by
      simp [inner_pi, constant_vec_one, h_sum]
    let c := inner_pi pi_dist v constant_vec_one
    let w := v - c • constant_vec_one
    have hw_ortho : inner_pi pi_dist w constant_vec_one = 0 := by
      simp [w, inner_pi, sum_sub_distrib, sum_mul, ←mul_sum, h_sum, constant_vec_one]
      rw [h11]; simp [c]
    have hw_ker : H *ᵥ w = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, h_const, hv, smul_zero, sub_zero]
    by_cases hw_zero : w = 0
    · rw [hw_zero, sub_eq_zero] at w; rw [eq_comm] at w
      exact w ▸ Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · -- Quotient is 0, contradicting gap
      have quot_zero : inner_pi pi_dist (H *ᵥ w) w / inner_pi pi_dist w w = 0 := by
        rw [hw_ker, Matrix.zero_mulVec, inner_pi]; simp; apply zero_div
      have : 0 ∈ { r |
          ∃ u, u ≠ 0 ∧ inner_pi pi_dist u constant_vec_one = 0 ∧
          r = inner_pi pi_dist (H *ᵥ u) u / inner_pi pi_dist u u } :=
        ⟨ w, hw_zero, hw_ortho, quot_zero.symm ⟩
      have inf_le_zero : SpectralGap_pi pi_dist H ≤ 0 :=
        csInf_le ⟨0, this⟩ (by rintro _ ⟨ z, _, _, rfl ⟩ ; apply div_nonneg (h_psd z) (inner_pi_pos_of_ne_zero hπ z.2.1.1).le)
      linarith
  · -- Reverse: ker H = span {1} implies Gap > 0
    intro h_ker
    -- Use EuclideanSpace (PiLp 2) to get the correct instances
    let to_euc_std (f : V → ℝ) : EuclideanSpace ℝ V := fun x => Real.sqrt (pi_dist x) * f x
    let from_euc_std (g : EuclideanSpace ℝ V) : (V → ℝ) := fun x => g x / Real.sqrt (pi_dist x)

    -- Define the set S in the standard Euclidean space (which has proper Inner Product instances)
    let S_euc := { u : EuclideanSpace ℝ V | ⟪u, to_euc_std constant_vec_one⟫ = (0:ℝ) ∧ ‖u‖ = 1 }

    have h_compact : IsCompact S_euc := by
      apply isCompact_of_isClosed_bounded
      · apply IsClosed.inter
        · exact isClosed_eq (Continuous.inner continuous_id continuous_const) continuous_const
        · exact isClosed_eq continuous_norm continuous_const
      · apply Metric.isBounded_iff.mpr
        use 1; intro u hu; simp [hu.2]

    have h_nonempty : S_euc.Nonempty := by
      obtain ⟨v, hv_ne, hv_ortho⟩ := exists_nonzero_ortho_one hπ
      let v_euc := to_euc_std v
      have v_euc_ne : v_euc ≠ 0 := by
        intro h
        apply hv_ne
        funext x
        specialize h x
        simp [to_euc_std] at h
        rwa [mul_eq_zero, Real.sqrt_eq_zero (le_of_lt (hπ x)), or_false] at h
        exact (hπ x).ne.symm
      have v_euc_ortho : ⟪v_euc, to_euc_std constant_vec_one⟫ = (0:ℝ) := by
        simp [to_euc_std]
        rw [EuclideanSpace.inner_eq_sum]
        convert hv_ortho using 1
        apply Finset.sum_congr rfl
        intro x _; simp; ring
      let u : EuclideanSpace ℝ V := ‖v_euc‖⁻¹ • v_euc
      use u
      constructor
      · simp [u, inner_smul_left]
        rw [EuclideanSpace.inner_eq_sum]
        rw [EuclideanSpace.inner_eq_sum] at h_min_ortho
        -- Orthogonality preservation check
        have : ⟪v_euc, to_euc_std constant_vec_one⟫ = (0:ℝ) := by
          rw [EuclideanSpace.inner_eq_sum]
          simp [to_euc_std, constant_vec_one]
          convert v.2.2.1 using 1
          apply Finset.sum_congr rfl
          intro x _; simp; ring
        rw [this]
        simp
      · simp [u, norm_smul, norm_pos_iff.mpr]
        intro h
        have := v.2.1
        funext x
        specialize h x
        simp [v_euc, to_euc_std] at h
        rwa [mul_eq_zero, Real.sqrt_eq_zero (le_of_lt (hπ x)), or_false] at h
        exact (hπ x).ne.symm
    · -- Lower Bound
      use v_min
      refine ⟨by intro h;
         have : u_min = 0 := by
            funext x; specialize h x; simp [v_min, from_euc_std] at h; rw [h]; simp
         simp [this] at h_min_norm, ?_, rfl⟩
      simp [v_min, inner_pi, from_euc_std, constant_vec_one]
      rw [EuclideanSpace.inner_eq_sum] at h_min_ortho
      convert h_min_ortho using 1
      apply Finset.sum_congr rfl
      intro x _; simp; ring

end FHDT
"""

path = r"src\FHDT\Core\Assumptions.lean"
with open(path, "w", encoding="utf-8") as f:
    f.write(content)
print(f"Successfully wrote {path} in UTF-8")