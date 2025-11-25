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

structure IrreducibilityAssumptions (L H : Matrix V V ℝ) (pi_vec : V → ℝ) where
  pi_dist : V → ℝ := pi_vec
  pi_pos : ∀ v, 0 < pi_dist v
  pi_sum_one : ∑ v, pi_dist v = 1

def constant_vec_one : V → ℝ := fun _ => 1

def inner_pi (pi_dist : V → ℝ) (u v : V → ℝ) : ℝ :=
  ∑ x, pi_dist x * u x * v x

def norm_sq_pi (pi_dist : V → ℝ) (v : V → ℝ) : ℝ :=
  inner_pi pi_dist v v

-- Manual expansion lemmas that do not rely on simp
lemma inner_pi_add_left {pi_dist : V → ℝ} (u v w : V → ℝ) :
    inner_pi pi_dist (u + v) w = inner_pi pi_dist u w + inner_pi pi_dist v w := by
  unfold inner_pi
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma inner_pi_add_right {pi_dist : V → ℝ} (u v w : V → ℝ) :
    inner_pi pi_dist u (v + w) = inner_pi pi_dist u v + inner_pi pi_dist u w := by
  unfold inner_pi
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma inner_pi_smul_left {pi_dist : V → ℝ} (c : ℝ) (u v : V → ℝ) :
    inner_pi pi_dist (c • u) v = c * inner_pi pi_dist u v := by
  unfold inner_pi
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [←Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma inner_pi_smul_right {pi_dist : V → ℝ} (c : ℝ) (u v : V → ℝ) :
    inner_pi pi_dist u (c • v) = c * inner_pi pi_dist u v := by
  unfold inner_pi
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [←Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma inner_pi_comm {pi_dist : V → ℝ} (u v : V → ℝ) :
    inner_pi pi_dist u v = inner_pi pi_dist v u := by
  unfold inner_pi
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma inner_pi_zero_left {pi_dist : V → ℝ} (v : V → ℝ) :
    inner_pi pi_dist 0 v = 0 := by
  unfold inner_pi
  simp

lemma inner_pi_sub_left {pi_dist : V → ℝ} (u v w : V → ℝ) :
    inner_pi pi_dist (u - v) w = inner_pi pi_dist u w - inner_pi pi_dist v w := by
  unfold inner_pi
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

noncomputable def SpectralGap_pi (pi_dist : V → ℝ) (H : Matrix V V ℝ) : ℝ :=
  sInf { r |
    ∃ v : V → ℝ, v ≠ 0 ∧ inner_pi pi_dist v constant_vec_one = 0 ∧
    r = inner_pi pi_dist (H *ᵥ v) v / inner_pi pi_dist v v }

lemma exists_nonzero_ortho_one [Nontrivial V] {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x) :
    ∃ v : V → ℝ, v ≠ 0 ∧ inner_pi pi_dist v constant_vec_one = 0 := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne V
  let v : V → ℝ := fun x => (if x = i then pi_dist j else 0) - (if x = j then pi_dist i else 0)
  have hne : v ≠ 0 := by
    intro hv
    have h_at_i := congr_fun hv i
    simp only [v, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h_at_i
    if h_i_i : i = i then
      simp [h_i_i] at h_at_i
    else
      contradiction
    have h_j_i : ¬(j = i) := hij.symm
    simp [h_j_i] at h_at_i
    have h_pos : 0 < pi_dist j := hπ j
    linarith
  have hortho : inner_pi pi_dist v constant_vec_one = 0 := by
    unfold inner_pi constant_vec_one
    simp only [mul_one]
    simp only [v]
    rw [Finset.sum_sub_distrib]
    have s1 : ∑ x, pi_dist x * (if x = i then pi_dist j else 0) = pi_dist i * pi_dist j := by
      rw [Finset.sum_ite]
      simp only [Finset.filter_eq', Finset.mem_univ, if_true, Finset.sum_singleton]
      simp only [Finset.filter_ne', Finset.sum_const_zero, add_zero]
    have s2 : ∑ x, pi_dist x * (if x = j then pi_dist i else 0) = pi_dist j * pi_dist i := by
      rw [Finset.sum_ite]
      simp only [Finset.filter_eq', Finset.mem_univ, if_true, Finset.sum_singleton]
      simp only [Finset.filter_ne', Finset.sum_const_zero, add_zero]
    rw [s1, s2]
    ring
  exact ⟨v, hne, hortho⟩

lemma inner_pi_pos_of_ne_zero {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x) {v : V → ℝ} (hv : v ≠ 0) :
    0 < inner_pi pi_dist v v := by
  obtain ⟨x0, hx0⟩ := Function.ne_iff.mp hv
  apply lt_of_lt_of_le (show (0:ℝ) < pi_dist x0 * v x0 * v x0 by
    apply mul_pos (hπ x0)
    exact sq_pos_of_ne_zero hx0)
  apply Finset.single_le_sum
  · intro x _
    apply mul_nonneg (le_of_lt (hπ x)) (mul_self_nonneg _)
  · exact Finset.mem_univ x0

lemma quad_nonneg_linear_zero {a b : ℝ}
    (ha : 0 ≤ a) (h : ∀ t : ℝ, 0 ≤ a * t^2 + 2 * b * t) : b = 0 := by
  by_cases hA : a = 0
  · subst hA
    have h1 := h 1
    have h2 := h (-1)
    simp at h1 h2
    linarith
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm hA)
    let t := -b/a
    have ht := h t
    have eq : a * t^2 + 2 * b * t = -b^2/a := by
      field_simp
      ring
    rw [eq] at ht
    have : b^2 ≤ 0 := by
      apply (div_nonneg_iff (by linarith) (by linarith)).mp at ht
      cases ht with
      | inl h => linarith
      | inr h => linarith
    have : b = 0 := by nlinarith
    exact this

lemma psd_inner_zero_implies_kernel
    {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x) (H : Matrix V V ℝ)
    (h_sa : ∀ u v, inner_pi pi_dist (H *ᵥ u) v = inner_pi pi_dist u (H *ᵥ v))
    (h_psd : ∀ u, 0 ≤ inner_pi pi_dist (H *ᵥ u) u)
    {v : V → ℝ} (h0 : inner_pi pi_dist (H *ᵥ v) v = 0) :
    H *ᵥ v = 0 := by
  have lin_zero : ∀ w, inner_pi pi_dist (H *ᵥ v) w = 0 := by
    intro w
    let q : ℝ → ℝ := fun t => inner_pi pi_dist (H *ᵥ (v + t • w)) (v + t • w)
    have q_nonneg : ∀ t, 0 ≤ q t := fun t => h_psd _
    apply quad_nonneg_linear_zero (h_psd w)
    intro t
    dsimp [q]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul]
    rw [inner_pi_add_left, inner_pi_add_left]
    rw [inner_pi_add_right, inner_pi_add_right, inner_pi_add_right, inner_pi_add_right]
    rw [inner_pi_smul_left, inner_pi_smul_left, inner_pi_smul_left]
    rw [inner_pi_smul_right, inner_pi_smul_right, inner_pi_smul_right]
    rw [h0]
    rw [inner_pi_comm (H *ᵥ w) v]
    rw [h_sa v w]
    apply le_of_eq
    ring
  have : inner_pi pi_dist (H *ᵥ v) (H *ᵥ v) = 0 := lin_zero (H *ᵥ v)
  cases eq_or_ne (H *ᵥ v) 0 with
  | inl h => exact h
  | inr hne =>
    have pos := inner_pi_pos_of_ne_zero hπ hne
    linarith

theorem gap_pos_iff_ker_eq_span_one [Nontrivial V] {pi_dist : V → ℝ} (hπ : ∀ v, 0 < pi_dist v)
    (h_sum : ∑ v, pi_dist v = 1)
    (H : Matrix V V ℝ)
    (h_sa : ∀ u v, inner_pi pi_dist (H *ᵥ u) v = inner_pi pi_dist u (H *ᵥ v))
    (h_psd : ∀ u, 0 ≤ inner_pi pi_dist (H *ᵥ u) u)
    (h_const : H *ᵥ constant_vec_one = 0) :
    (SpectralGap_pi (pi_dist) H > 0) ↔ (ker (toLin' H) = Submodule.span ℝ {constant_vec_one}) := by
  constructor
  · intro h_gap
    refine le_antisymm (Submodule.span_le.mpr ?_) ?_
    · rw [SetLike.mem_coe, LinearMap.mem_ker]
      exact h_const
    intro v hv
    let c := inner_pi pi_dist v constant_vec_one
    let w := v - c • constant_vec_one
    have hw_ortho : inner_pi pi_dist w constant_vec_one = 0 := by
      simp [w, inner_pi_sub_left, inner_pi_smul_left, constant_vec_one]
      have h11 : inner_pi pi_dist constant_vec_one constant_vec_one = 1 := by
        unfold inner_pi constant_vec_one; simp; exact h_sum
      rw [h11]
      simp [c]
    have hw_ker : H *ᵥ w = 0 := by
      rw [LinearMap.mem_ker] at hv
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, h_const, hv]
      simp
    by_cases hw_zero : w = 0
    · rw [eq_comm, sub_eq_zero] at hw_zero
      rw [hw_zero]
      apply Submodule.smul_mem
      apply Submodule.mem_span_singleton_self
    · have quot_zero : inner_pi pi_dist (H *ᵥ w) w / inner_pi pi_dist w w = 0 := by
        rw [hw_ker, Matrix.zero_mulVec]
        simp [inner_pi_zero_left]
      have : 0 ∈ { r | ∃ u, u ≠ 0 ∧ inner_pi pi_dist u constant_vec_one = 0 ∧
                       r = inner_pi pi_dist (H *ᵥ u) u / inner_pi pi_dist u u } :=
        ⟨w, hw_zero, hw_ortho, quot_zero.symm⟩
      have : SpectralGap_pi pi_dist H ≤ 0 := csInf_le ⟨0, by
         rintro _ ⟨z, _, _, rfl⟩
         apply div_nonneg (h_psd z)
         exact le_of_lt (inner_pi_pos_of_ne_zero hπ z.2.1.1)
      ⟩ this
      linarith
  · intro h_ker
    let to_euc_std (f : V → ℝ) : EuclideanSpace ℝ V := fun x => Real.sqrt (pi_dist x) * f x
    let from_euc_std (g : EuclideanSpace ℝ V) : (V → ℝ) := fun x => g x / Real.sqrt (pi_dist x)
    let S_euc := { u : EuclideanSpace ℝ V | inner u (to_euc_std constant_vec_one) = (0:ℝ) ∧ ‖u‖ = 1 }
    have h_compact : IsCompact S_euc := by
      apply isCompact_of_isClosed_bounded
      · apply IsClosed.inter
        · apply isClosed_eq
          · exact Continuous.inner continuous_id continuous_const
          · exact continuous_const
        · apply isClosed_eq
          · exact continuous_norm
          · exact continuous_const
      · apply Metric.isBounded_iff.mpr
        use 1
        intro u hu
        simp [hu.2]
    have h_nonempty : S_euc.Nonempty := by
      obtain ⟨v, hv_ne, hv_ortho⟩ := exists_nonzero_ortho_one hπ
      let v_euc := to_euc_std v
      have v_euc_ne : v_euc ≠ 0 := by
        intro h
        apply hv_ne
        funext x
        have hx := congr_fun h x
        simp [to_euc_std] at hx
        rwa [mul_eq_zero, Real.sqrt_eq_zero (le_of_lt (hπ x)), or_false] at hx
        exact (hπ x).ne.symm
      have v_euc_ortho : inner v_euc (to_euc_std constant_vec_one) = (0:ℝ) := by
        rw [EuclideanSpace.inner_eq_sum]
        unfold inner_pi at hv_ortho
        convert hv_ortho using 1
        apply Finset.sum_congr rfl
        intro x _
        simp [to_euc_std]
        rw [←mul_assoc, ←Real.sqrt_mul (le_of_lt (hπ x))]
        simp [abs_of_pos (hπ x)]
        ring
      let u : EuclideanSpace ℝ V := ‖v_euc‖⁻¹ • v_euc
      use u
      constructor
      · simp only [inner_smul_left, v_euc_ortho, mul_zero, IsROrC.conj_to_real]
      · rw [norm_smul, norm_inv, mul_inv_cancel]
        rwa [norm_ne_zero_iff]
    let Q_euc (u : EuclideanSpace ℝ V) := inner_pi pi_dist (H *ᵥ (from_euc_std u)) (from_euc_std u)
    have h_cont : ContinuousOn Q_euc S_euc := by
      apply Continuous.continuousOn
      apply Continuous.sum
      intro x _
      apply Continuous.mul
      apply Continuous.mul
      exact continuous_const
      apply Continuous.matrix_mulVec
      apply continuous_pi
      intro i
      apply Continuous.div
      exact continuous_apply i
      exact continuous_const
      intro x
      exact Real.sqrt_ne_zero'.mpr (hπ x)
      apply continuous_pi
      intro i
      apply Continuous.div
      exact continuous_apply i
      exact continuous_const
      intro x
      exact Real.sqrt_ne_zero'.mpr (hπ x)
    rcases IsCompact.exists_isMinOn h_compact h_nonempty h_cont with ⟨u_min, ⟨h_min_ortho, h_min_norm⟩, h_le_min⟩
    let min_val := Q_euc u_min
    let v_min := from_euc_std u_min
    have h_pos_min : 0 < min_val := by
      by_contra h_le
      push_neg at h_le
      have h_ge_0 : 0 ≤ min_val := h_psd v_min
      have h_eq_0 : min_val = 0 := le_antisymm h_le h_ge_0
      have h_ker_vec : H *ᵥ v_min = 0 := psd_inner_zero_implies_kernel hπ H h_sa h_psd h_eq_0
      have h_in_ker : v_min ∈ ker (toLin' H) := by
        rw [LinearMap.mem_ker, Matrix.toLin'_apply]
        exact h_ker_vec
      rw [h_ker] at h_in_ker
      rcases Submodule.mem_span_singleton.mp h_in_ker with ⟨k, hk⟩
      have : inner_pi pi_dist v_min constant_vec_one = 0 := by
        unfold inner_pi
        rw [EuclideanSpace.inner_eq_sum] at h_min_ortho
        convert h_min_ortho using 1
        apply Finset.sum_congr rfl
        intro x _
        simp [v_min, from_euc_std, to_euc_std, constant_vec_one]
        rw [div_mul_eq_mul_div, ←Real.sqrt_mul (le_of_lt (hπ x)), Real.sqrt_mul_self (le_of_lt (hπ x))]
        field_simp [Real.sqrt_ne_zero'.mpr (hπ x)]
        ring
      rw [hk] at this
      simp [inner_pi_smul_left, constant_vec_one] at this
      have h11 : inner_pi pi_dist constant_vec_one constant_vec_one = 1 := by
        unfold inner_pi constant_vec_one; simp; exact h_sum
      rw [h11, mul_one] at this
      rw [this, zero_smul] at hk
      have : u_min = 0 := by
        funext x
        have := congr_fun hk x
        simp [v_min, from_euc_std] at this
        rw [this]; simp
      rw [this] at h_min_norm
      simp at h_min_norm
    apply lt_of_lt_of_le h_pos_min
    apply le_csInf
    · use min_val
      use v_min
      refine ⟨?, ?, rfl⟩
      · intro h
        have : u_min = 0 := by
          funext x
          have := congr_fun h x
          simp [v_min, from_euc_std] at this
          rw [div_eq_zero_iff] at this
          cases this with
          | inl h => exact h
          | inr h => exact False.elim ((ne_of_gt (Real.sqrt_pos.mpr (hπ x))) h)
        rw [this] at h_min_norm
        simp at h_min_norm
      · unfold inner_pi
        rw [EuclideanSpace.inner_eq_sum] at h_min_ortho
        convert h_min_ortho using 1
        apply Finset.sum_congr rfl
        intro x _
        simp [v_min, from_euc_std, to_euc_std, constant_vec_one]
        rw [div_mul_eq_mul_div, ←Real.sqrt_mul (le_of_lt (hπ x)), Real.sqrt_mul_self (le_of_lt (hπ x))]
        field_simp [Real.sqrt_ne_zero'.mpr (hπ x)]
        ring
    · rintro r ⟨v, hv_ne, hv_ortho, rfl⟩
      let v_euc := to_euc_std v
      let u_test := ‖v_euc‖⁻¹ • v_euc
      have h_mem : u_test ∈ S_euc := by
        simp
        constructor
        · rw [inner_smul_left]
          have : inner v_euc (to_euc_std constant_vec_one) = (0:ℝ) := by
            rw [EuclideanSpace.inner_eq_sum]
            unfold inner_pi at hv_ortho
            convert hv_ortho using 1
            apply Finset.sum_congr rfl
            intro x _
            simp [to_euc_std]
            rw [←mul_assoc, ←Real.sqrt_mul (le_of_lt (hπ x))]
            simp [abs_of_pos (hπ x)]
            ring
          rw [this, mul_zero]
        · rw [norm_smul, norm_inv, mul_inv_cancel]
          rw [norm_ne_zero_iff]
          intro h
          apply hv_ne
          funext x
          have hx := congr_fun h x
          simp [to_euc_std] at hx
          rwa [mul_eq_zero, Real.sqrt_eq_zero (le_of_lt (hπ x)), or_false] at hx
          exact (hπ x).ne.symm
      have h_le := h_le_min h_mem
      rw [Q_euc] at h_le ⊢
      dsimp at h_le ⊢
      have h_lin : ∀ c u, from_euc_std (c • u) = c • from_euc_std u := by
        intro c u; funext x; simp [from_euc_std]
      rw [h_lin] at h_le
      rw [Matrix.mulVec_smul] at h_le
      rw [inner_pi_smul_left, inner_pi_smul_right] at h_le
      rw [←pow_two] at h_le
      have h_inv : from_euc_std (to_euc_std v) = v := by
        funext x; simp [from_euc_std, to_euc_std]; field_simp [Real.sqrt_ne_zero'.mpr (hπ x)]
      rw [h_inv] at h_le
      have h_norm : ‖v_euc‖^2 = inner_pi pi_dist v v := by
        rw [EuclideanSpace.norm_sq_eq_sum]
        unfold inner_pi
        apply Finset.sum_congr rfl
        intro x _
        simp [to_euc_std]
        rw [mul_pow, Real.sq_sqrt (le_of_lt (hπ x))]
        ring
      rw [←h_norm]
      rw [inv_pow, mul_comm] at h_le
      rw [div_eq_mul_inv]
      exact h_le

end FHDT
"""

path = r"src\FHDT\Core\Assumptions.lean"
with open(path, "w", encoding="utf-8") as f:
    f.write(content)
print(f"Successfully wrote {path} in UTF-8")