import os

content = """import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.MeanValue

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
    simp [v, hij.ne] at h_at_i
    exact (ne_of_gt (hπ j)) h_at_i.symm
  have hortho : inner_pi pi_dist v constant_vec_one = 0 := by
    simp [inner_pi, v, constant_vec_one, Finset.sum_ite, Finset.mem_univ, hij.ne,
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
    apply Finset.single_le_sum (fun x _ => mul_nonneg (le_of_lt (hπ x)) (mul_self_nonneg _))
    exact Finset.mem_univ x0
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
    have : b^2 ≤ 0 := by
      rw [le_div_iff₀ ha_pos] at this
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
        csInf_le (by use 0; rintro _ ⟨ z, _, _, rfl ⟩ ; apply div_nonneg (h_psd z) (inner_pi_pos_of_ne_zero hπ z.2.1.1).le) this
      linarith
  · -- Reverse: ker H = span {1} implies Gap > 0
    intro h_ker
    -- Transport to Euclidean Space via D=diag(sqrt pi)
    let to_euc (f : V → ℝ) : (V → ℝ) := fun x => Real.sqrt (pi_dist x) * f x
    let from_euc (g : V → ℝ) : (V → ℝ) := fun x => g x / Real.sqrt (pi_dist x)
    let iso : (V → ℝ) ≃L[ℝ] (V → ℝ) := {
      toFun := to_euc
      invFun := from_euc
      left_inv := by intro f; ext x; simp [from_euc, to_euc]; field_simp [Real.sqrt_ne_zero'.mpr (hπ x)]
      right_inv := by intro g; ext x; simp [to_euc, from_euc]; field_simp [Real.sqrt_ne_zero'.mpr (hπ x)]
      map_add' := by intro f g; ext x; simp [to_euc, add_mul]
      map_smul' := by intro c f; ext x; simp [to_euc, mul_assoc]
      continuous_toFun := continuous_pi (fun x => Continuous.mul continuous_const (continuous_apply x))
      continuous_invFun := continuous_pi (fun x => Continuous.div (continuous_apply x) continuous_const (fun _ => Real.sqrt_ne_zero'.mpr (hπ x)))
    }
    -- Explicitly define S_euc with Real inner product
    let S_euc := { u : V → ℝ | @inner ℝ _ _ u (to_euc constant_vec_one) = (0 : ℝ) ∧ ‖u‖ = 1 }

    have h_compact : IsCompact S_euc := by
      apply Metric.isCompact_of_isClosed_bounded
      · apply IsClosed.inter
        · exact isClosed_eq (Continuous.inner continuous_id continuous_const) continuous_const
        · exact isClosed_eq continuous_norm continuous_const
      · apply Metric.isBounded_iff.mpr
        use 1; intro u hu; simp [hu.2]

    have h_nonempty : S_euc.Nonempty := by
      obtain ⟨v, hv_ne, hv_ortho⟩ := exists_nonzero_ortho_one hπ
      let v_euc := to_euc v
      have v_euc_ne : v_euc ≠ 0 := fun h => hv_ne (iso.map_eq_zero_iff.mp h)
      have v_euc_ortho : @inner ℝ _ _ v_euc (to_euc constant_vec_one) = 0 := by
        simp [inner, to_euc, constant_vec_one, inner_pi] at *
        rw [real_inner_eq_sum_mul]
        convert hv_ortho using 1
        apply Finset.sum_congr rfl
        intro x _; simp; ring
      let u := (‖v_euc‖)⁻¹ • v_euc
      use u
      constructor
      · simp [u, inner_smul_left, v_euc_ortho]
      · simp [u, norm_smul, norm_pos_iff.mpr v_euc_ne]

    -- Quadratic form on Euclidean space is continuous
    let Q_euc (u : V → ℝ) := inner_pi pi_dist (H *ᵥ (from_euc u)) (from_euc u)
    have h_cont : ContinuousOn Q_euc S_euc := by
      -- Q_euc is composition of continuous functions (matrix mul, inner product, iso)
      apply Continuous.continuousOn
      simp [Q_euc, inner_pi]
      apply continuous_finset_sum; intro x _
      apply Continuous.mul; apply Continuous.mul
      · exact continuous_const
      · apply Continuous.matrix_mulVec; exact iso.continuous_invFun
      · simp [from_euc]; apply Continuous.div (continuous_apply x) continuous_const (fun _ => Real.sqrt_ne_zero'.mpr (hπ x))

    -- Minimum attained on compact set
    rcases IsCompact.exists_isMinOn h_compact h_nonempty h_cont with ⟨u_min, ⟨h_min_ortho, h_min_norm⟩, h_le_min⟩
    let min_val := Q_euc u_min
    let v_min := from_euc u_min

    -- min_val > 0 because ker H = span{1} and v_min perp 1
    have h_pos_min : 0 < min_val := by
      by_contra h_le
      push_neg at h_le
      have h_eq_0 : inner_pi pi_dist (H *ᵥ v_min) v_min = 0 := le_antisymm h_le (h_psd v_min)
      have h_ker_vec : H *ᵥ v_min = 0 := psd_inner_zero_implies_kernel hπ H h_sa h_psd h_eq_0
      have h_in_ker : v_min ∈ ker (toLin' H) := by
        rw [LinearMap.mem_ker, Matrix.toLin'_apply]
        exact h_ker_vec
      rw [h_ker] at h_in_ker
      rcases Submodule.mem_span_singleton.mp h_in_ker with ⟨k, hk⟩
      -- Check orthogonality of v_min to 1
      have : inner_pi pi_dist v_min constant_vec_one = 0 := by
        simp [v_min, inner_pi, from_euc, constant_vec_one]
        simp [inner, to_euc, constant_vec_one] at h_min_ortho
        rw [real_inner_eq_sum_mul] at h_min_ortho
        convert h_min_ortho using 1
        apply Finset.sum_congr rfl
        intro x _; simp; ring
      rw [hk] at this
      simp [inner_pi, h_sum, constant_vec_one] at this
      -- k * 1 = 0 => k = 0 => v_min = 0 => u_min = 0 => norm!= 1
      rw [this, zero_smul] at hk
      have : u_min = 0 := iso.map_eq_zero_iff.mp hk
      rw [this] at h_min_norm
      simp at h_min_norm

    -- Gap >= min_val via scale invariance
    apply lt_of_lt_of_le h_pos_min
    apply le_csInf
    · -- Goal: Nonempty (swapped order)
      use min_val; rintro _ ⟨v, _, _, rfl⟩
      let v_euc := to_euc v
      let u := (‖v_euc‖)⁻¹ • v_euc
      have h_scale : inner_pi pi_dist (H *ᵥ v) v / inner_pi pi_dist v v = Q_euc u := by
        simp [Q_euc, from_euc, to_euc, u, inner_pi]
        have norm_eq : inner_pi pi_dist v v = ‖v_euc‖^2 := by
          simp [inner_pi, to_euc, norm_eq_sqrt_inner, real_inner_self_eq_norm_sq]; apply Finset.sum_congr rfl
          intro x _; rw [Real.mul_self_sqrt (le_of_lt (hπ x))]; ring
        rw [norm_eq]
        simp [Matrix.mulVec_smul]; rw [←mul_sum]
        ring_nf; simp [pow_two, inv_mul_eq_div, mul_div_assoc]
        rw [mul_div_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr (fun h => v.2.1 (iso.map_eq_zero_iff.mp h))))]
      rw [h_scale]
      apply h_le_min
      constructor
      · simp [u, inner_smul_left]
        simp [inner, to_euc, constant_vec_one, inner_pi] at *
        rw [real_inner_eq_sum_mul]
        convert v.2.2.1 using 1
        apply Finset.sum_congr rfl
        intro x _; simp; ring
      · simp [u, norm_smul, norm_pos_iff.mpr (fun h => v.2.1 (iso.map_eq_zero_iff.mp h))]
    · -- Goal: Lower Bound
      use v_min
      refine ⟨by intro h; exact (iso.map_eq_zero_iff.mpr h) ▸ (by simp at h_min_norm),?_, rfl⟩
      simp [v_min, inner_pi, from_euc, constant_vec_one]
      simp [inner, to_euc, constant_vec_one] at h_min_ortho
      rw [real_inner_eq_sum_mul] at h_min_ortho
      convert h_min_ortho using 1
      apply Finset.sum_congr rfl
      intro x _; simp; ring

end FHDT
"""

path = r"src\FHDT\Core\Assumptions.lean"
with open(path, "w", encoding="utf-8") as f:
    f.write(content)
print(f"Successfully wrote {path} in UTF-8")