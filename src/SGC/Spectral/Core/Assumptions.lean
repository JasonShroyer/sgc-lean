import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-!
  # SGC/Spectral/Core/Assumptions.lean

  Core spectral assumptions and weighted inner product definitions.

  **NOTE**: This module uses the **Explicit Weight Pattern** (`pi_dist` as an argument)
  rather than typeclasses. See `ARCHITECTURE.md` for the full rationale.
-/

noncomputable section

namespace SGC.Spectral
section Assumptions
open Finset LinearMap Matrix Real ContinuousLinearMap Submodule Topology EuclideanSpace

-- Suppress unused variable warnings (many lemmas don't need all type constraints)
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Assumptions for an irreducible, lazy Markov chain. -/
structure IrreducibilityAssumptions (L H : Matrix V V ℝ) (pi_vec : V → ℝ) where
  pi_dist : V → ℝ := pi_vec
  pi_pos : ∀ v, 0 < pi_dist v
  pi_sum_one : ∑ v, pi_dist v = 1

abbrev constant_vec_one : V → ℝ := fun _ => 1

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

lemma inner_pi_zero_right {pi_dist : V → ℝ} (u : V → ℝ) :
    inner_pi pi_dist u 0 = 0 := by
  simp [inner_pi]

lemma inner_pi_sub_left {pi_dist : V → ℝ} (u v w : V → ℝ) :
    inner_pi pi_dist (u - v) w = inner_pi pi_dist u w - inner_pi pi_dist v w := by
  simp only [inner_pi, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  congr 1; ext x; ring

lemma inner_pi_sub_right {pi_dist : V → ℝ} (u v w : V → ℝ) :
    inner_pi pi_dist u (v - w) = inner_pi pi_dist u v - inner_pi pi_dist u w := by
  simp only [inner_pi, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  congr 1; ext x; ring

/-! ### Norm helpers -/

/-- norm_sq_pi is positive for nonzero vectors when weights are positive. -/
lemma norm_sq_pi_pos {pi_dist : V → ℝ} (hπ : ∀ v, 0 < pi_dist v) {u : V → ℝ} (hu : u ≠ 0) :
    0 < norm_sq_pi pi_dist u := by
  rw [norm_sq_pi, inner_pi]
  -- There exists some v where u v ≠ 0
  have hex : ∃ v, u v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu (funext h)
  obtain ⟨v₀, hv₀⟩ := hex
  -- The sum has a positive term at v₀
  have h_term_pos : 0 < pi_dist v₀ * u v₀ * u v₀ := by
    have hπ₀ : 0 < pi_dist v₀ := hπ v₀
    have h_usq : 0 < u v₀ * u v₀ := mul_self_pos.mpr hv₀
    calc 0 < pi_dist v₀ * (u v₀ * u v₀) := mul_pos hπ₀ h_usq
      _ = pi_dist v₀ * u v₀ * u v₀ := by ring
  apply Finset.sum_pos'
  · intro v _
    have hπv : 0 ≤ pi_dist v := le_of_lt (hπ v)
    have h_usq : 0 ≤ u v * u v := mul_self_nonneg (u v)
    calc 0 ≤ pi_dist v * (u v * u v) := mul_nonneg hπv h_usq
      _ = pi_dist v * u v * u v := by ring
  · exact ⟨v₀, Finset.mem_univ _, h_term_pos⟩

/-! ### Spectral Gap Definition and Theorem -/

/-- The spectral gap defined as the infimum of the Rayleigh quotient on 1^⊥. -/
noncomputable def SpectralGap_pi (pi_dist : V → ℝ) (H : Matrix V V ℝ) : ℝ :=
  sInf { r | ∃ v : V → ℝ, v ≠ 0 ∧ inner_pi pi_dist v constant_vec_one = 0 ∧
    r = inner_pi pi_dist (H *ᵥ v) v / inner_pi pi_dist v v }

/-- Helper: norm_sq_pi of constant_vec_one equals the sum of weights (which is 1). -/
lemma norm_sq_pi_one {pi_dist : V → ℝ} (h_sum : ∑ v, pi_dist v = 1) :
    norm_sq_pi pi_dist constant_vec_one = 1 := by
  simp only [norm_sq_pi, inner_pi, constant_vec_one, mul_one, h_sum]

/-- Helper: If ⟨Hu, u⟩_π = 0 and H is PSD w.r.t. inner_pi, then Hu = 0.
    This uses polarization: for PSD H, the form ⟨Hu, v⟩ induces a semi-inner product,
    and ⟨Hu, u⟩ = 0 implies Hu = 0 by Cauchy-Schwarz. -/
lemma inner_H_zero_of_psd_zero {pi_dist : V → ℝ} (hπ : ∀ v, 0 < pi_dist v)
    (H : Matrix V V ℝ)
    (h_sa : ∀ u v, inner_pi pi_dist (H *ᵥ u) v = inner_pi pi_dist u (H *ᵥ v))
    (h_psd : ∀ u, 0 ≤ inner_pi pi_dist (H *ᵥ u) u)
    {u : V → ℝ} (hu : inner_pi pi_dist (H *ᵥ u) u = 0) :
    H *ᵥ u = 0 := by
  -- Standard fact: for a PSD symmetric bilinear form B, B(u,u) = 0 implies B(u,v) = 0 for all v
  -- Here B(u,v) = ⟨Hu, v⟩_π. Taking v = Hu gives ⟨Hu, Hu⟩ = 0, hence Hu = 0.
  -- The polarization argument: for all t, 0 ≤ ⟨H(u+tv), u+tv⟩ = ⟨Hu,u⟩ + 2t⟨Hu,v⟩ + t²⟨Hv,v⟩
  -- With ⟨Hu,u⟩ = 0: 2t⟨Hu,v⟩ + t²⟨Hv,v⟩ ≥ 0 for all t. If ⟨Hu,v⟩ ≠ 0, take t with opposite sign.
  -- This forces ⟨Hu,v⟩ = 0 for all v; take v = Hu to get ‖Hu‖² = 0.
  by_contra h_ne
  have h_Hu_norm_pos : 0 < norm_sq_pi pi_dist (H *ᵥ u) := norm_sq_pi_pos hπ h_ne
  -- ⟨Hu, Hu⟩_π = ⟨H(Hu), u⟩_π by self-adjointness
  have h_eq : inner_pi pi_dist (H *ᵥ u) (H *ᵥ u) = inner_pi pi_dist (H *ᵥ (H *ᵥ u)) u := by
    rw [h_sa (H *ᵥ u) u]
  rw [norm_sq_pi] at h_Hu_norm_pos
  -- Polarization with v = Hu: consider ⟨H(u + t·Hu), u + t·Hu⟩ ≥ 0
  -- This expands to ⟨Hu,u⟩ + 2t⟨Hu,Hu⟩ + t²⟨H(Hu),Hu⟩ = 0 + 2t·a + t²·b where a,b > 0
  -- For t < 0 small, this is approximately 2ta < 0, contradiction
  -- Polarization: consider ⟨H(u + t·Hu), u + t·Hu⟩_π ≥ 0 for all t
  -- Expanding: ⟨Hu, u⟩ + 2t⟨Hu, Hu⟩ + t²⟨H(Hu), Hu⟩ = 0 + 2t·a + t²·b where a = ‖Hu‖²_π, b ≥ 0
  -- If a > 0, for small negative t we get 2ta + t²b < 0, contradiction
  let a := inner_pi pi_dist (H *ᵥ u) (H *ᵥ u)  -- = ‖Hu‖²_π > 0
  let b := inner_pi pi_dist (H *ᵥ (H *ᵥ u)) (H *ᵥ u)  -- ≥ 0 by PSD
  have hb : 0 ≤ b := h_psd (H *ᵥ u)
  have ha_pos : 0 < a := h_Hu_norm_pos
  -- Consider the quadratic q(t) = ⟨H(u + t·Hu), u + t·Hu⟩_π
  -- Using linearity: q(t) = ⟨Hu + t·H(Hu), u + t·Hu⟩_π
  --                      = ⟨Hu, u⟩ + t⟨H(Hu), u⟩ + t⟨Hu, Hu⟩ + t²⟨H(Hu), Hu⟩
  --                      = 0 + t⟨Hu, Hu⟩ + t⟨Hu, Hu⟩ + t²·b    (using hu and self-adjointness)
  --                      = 2t·a + t²·b
  have h_expand : ∀ t : ℝ, inner_pi pi_dist (H *ᵥ (u + t • (H *ᵥ u))) (u + t • (H *ᵥ u)) =
      2 * t * a + t^2 * b := by
    intro t
    -- H *ᵥ (u + t • Hu) = Hu + t • H(Hu) by linearity
    have h_lin : H *ᵥ (u + t • (H *ᵥ u)) = (H *ᵥ u) + t • (H *ᵥ (H *ᵥ u)) := by
      rw [mulVec_add, mulVec_smul]
    rw [h_lin]
    -- Expand the inner product
    rw [inner_pi_add_left, inner_pi_add_right, inner_pi_add_right]
    rw [inner_pi_smul_left, inner_pi_smul_right, inner_pi_smul_left, inner_pi_smul_right]
    -- ⟨Hu, u⟩ = 0 by assumption
    rw [hu]
    -- ⟨H(Hu), u⟩ = ⟨Hu, Hu⟩ by self-adjointness
    have h_sa_apply : inner_pi pi_dist (H *ᵥ (H *ᵥ u)) u = inner_pi pi_dist (H *ᵥ u) (H *ᵥ u) := by
      rw [h_sa (H *ᵥ u) u]
    rw [h_sa_apply]
    simp only [a, b]
    ring
  -- For all t, q(t) ≥ 0
  have h_nonneg : ∀ t : ℝ, 0 ≤ 2 * t * a + t^2 * b := by
    intro t
    rw [← h_expand t]
    exact h_psd (u + t • (H *ᵥ u))
  -- Now derive contradiction: if a > 0, take t = -a/b when b > 0, or t = -1 when b = 0
  by_cases hb_pos : b = 0
  · -- Case b = 0: q(t) = 2ta, must have 2ta ≥ 0 for all t
    -- Take t = -1: 2(-1)a = -2a < 0, contradiction
    have h_neg := h_nonneg (-1)
    simp only [hb_pos, mul_zero, add_zero] at h_neg
    linarith
  · -- Case b > 0: take t = -a/b
    have hb_pos' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb_pos)
    have h_at_min := h_nonneg (-a / b)
    -- At t = -a/b: 2(-a/b)a + (-a/b)²b = -2a²/b + a²/b = -a²/b < 0
    have h_calc : 2 * (-a / b) * a + (-a / b)^2 * b = -a^2 / b := by
      field_simp
      ring
    rw [h_calc] at h_at_min
    have h_a_sq_pos : 0 < a^2 := sq_pos_of_pos ha_pos
    have h_neg : -a^2 / b < 0 := by
      apply div_neg_of_neg_of_pos
      · linarith
      · exact hb_pos'
    linarith

/-- **Spectral Gap Coercivity**: For v ⊥ 1, we have ⟨Hv, v⟩_π ≥ gap * ‖v‖²_π.
    This is the operational form of the spectral gap needed for energy decay. -/
lemma SpectralGap_coercivity [Nontrivial V]
    {pi_dist : V → ℝ} (hπ : ∀ v, 0 < pi_dist v)
    (H : Matrix V V ℝ)
    (h_sa : ∀ u w, inner_pi pi_dist (H *ᵥ u) w = inner_pi pi_dist u (H *ᵥ w))
    (h_psd : ∀ u, 0 ≤ inner_pi pi_dist (H *ᵥ u) u)
    (h_const : H *ᵥ constant_vec_one = 0)
    (h_gap : 0 < SpectralGap_pi pi_dist H)
    (v : V → ℝ) (hv_orth : inner_pi pi_dist v constant_vec_one = 0) :
    inner_pi pi_dist (H *ᵥ v) v ≥ SpectralGap_pi pi_dist H * norm_sq_pi pi_dist v := by
  -- Case 1: v = 0
  by_cases hv : v = 0
  · -- Both sides are 0
    simp only [hv, norm_sq_pi, inner_pi_zero_right, mul_zero, ge_iff_le, le_refl]
  -- Case 2: v ≠ 0 and v ⊥ 1
  -- The Rayleigh quotient ⟨Hv, v⟩ / ‖v‖² is in the set defining SpectralGap_pi
  have h_norm_pos : 0 < norm_sq_pi pi_dist v := norm_sq_pi_pos hπ hv
  -- The gap is the infimum of Rayleigh quotients, so gap ≤ ⟨Hv, v⟩ / ‖v‖²
  have h_in_set : inner_pi pi_dist (H *ᵥ v) v / inner_pi pi_dist v v ∈
      { r | ∃ u : V → ℝ, u ≠ 0 ∧ inner_pi pi_dist u constant_vec_one = 0 ∧
        r = inner_pi pi_dist (H *ᵥ u) u / inner_pi pi_dist u u } := by
    simp only [Set.mem_setOf_eq, norm_sq_pi] at *
    exact ⟨v, hv, hv_orth, rfl⟩
  -- By definition of sInf, gap ≤ ⟨Hv, v⟩ / ‖v‖² (since the set is nonempty and gap is infimum)
  have h_gap_le : SpectralGap_pi pi_dist H ≤ inner_pi pi_dist (H *ᵥ v) v / norm_sq_pi pi_dist v := by
    apply csInf_le
    · -- The set is bounded below by 0 (from h_psd and positivity of norm)
      use 0
      intro r hr
      simp only [Set.mem_setOf_eq] at hr
      obtain ⟨u, hu_ne, _, hu_eq⟩ := hr
      rw [hu_eq]
      have h_norm_u : 0 < norm_sq_pi pi_dist u := norm_sq_pi_pos hπ hu_ne
      exact div_nonneg (h_psd u) (le_of_lt h_norm_u)
    · exact h_in_set
  -- Multiply both sides by ‖v‖² > 0
  calc SpectralGap_pi pi_dist H * norm_sq_pi pi_dist v
      ≤ (inner_pi pi_dist (H *ᵥ v) v / norm_sq_pi pi_dist v) * norm_sq_pi pi_dist v := by
        exact mul_le_mul_of_nonneg_right h_gap_le (le_of_lt h_norm_pos)
    _ = inner_pi pi_dist (H *ᵥ v) v := by
        field_simp [ne_of_gt h_norm_pos]

/-- **Pillar 1: Spectral Gap Equivalence**
    Proves that Gap > 0 iff Ker(H) = span{1}. -/
theorem gap_pos_iff_ker_eq_span_one [Nontrivial V]
    {pi_dist : V → ℝ} (hπ : ∀ v, 0 < pi_dist v)
    (h_sum : ∑ v, pi_dist v = 1)
    (H : Matrix V V ℝ)
    (h_sa : ∀ u v, inner_pi pi_dist (H *ᵥ u) v = inner_pi pi_dist u (H *ᵥ v))
    (h_psd : ∀ u, 0 ≤ inner_pi pi_dist (H *ᵥ u) u)
    (h_const : H *ᵥ constant_vec_one = 0) :
    (SpectralGap_pi (pi_dist) H > 0) ↔ (ker (toLin' H) = Submodule.span ℝ {constant_vec_one}) := by
  constructor
  -- (→) gap > 0 implies ker(H) = span{1}
  · intro h_gap
    ext u
    simp only [mem_ker, toLin'_apply, mem_span_singleton]
    constructor
    -- If H *ᵥ u = 0, then u ∈ span{1}
    · intro hu_ker
      -- Decompose u = v + c·1 where v ⊥ 1
      let c := inner_pi pi_dist u constant_vec_one / norm_sq_pi pi_dist constant_vec_one
      let v := u - c • constant_vec_one
      -- v ⊥ 1
      have hv_orth : inner_pi pi_dist v constant_vec_one = 0 := by
        simp only [v, inner_pi_sub_left, inner_pi_smul_left]
        have h_norm_one : norm_sq_pi pi_dist constant_vec_one = 1 := norm_sq_pi_one h_sum
        simp only [norm_sq_pi] at h_norm_one
        simp only [c, norm_sq_pi, h_norm_one, div_one, mul_one, sub_self]
      -- H *ᵥ v = H *ᵥ u - c · H *ᵥ 1 = 0 - 0 = 0
      have hv_ker : H *ᵥ v = 0 := by
        simp only [v, mulVec_sub, mulVec_smul, hu_ker, h_const, smul_zero, sub_zero]
      -- If v ≠ 0, apply coercivity: 0 = ⟨Hv, v⟩ ≥ gap · ‖v‖² > 0, contradiction
      by_cases hv : v = 0
      · -- v = 0, so u = c·1 ∈ span{1}
        use c
        simp only [v, sub_eq_zero] at hv
        exact hv.symm
      · -- v ≠ 0, get contradiction
        have h_coer := SpectralGap_coercivity hπ H h_sa h_psd h_const h_gap v hv_orth
        simp only [hv_ker, inner_pi_zero_left] at h_coer
        have h_norm_pos : 0 < norm_sq_pi pi_dist v := norm_sq_pi_pos hπ hv
        have : 0 < SpectralGap_pi pi_dist H * norm_sq_pi pi_dist v := mul_pos h_gap h_norm_pos
        linarith
    -- If u ∈ span{1}, then H *ᵥ u = 0
    · intro ⟨c, hc⟩
      rw [← hc, mulVec_smul, h_const, smul_zero]
  -- (←) ker(H) = span{1} implies gap > 0
  · intro h_ker
    -- Key fact: for u ⊥ 1 with u ≠ 0, we have ⟨Hu, u⟩ > 0
    have h_rayleigh_pos : ∀ u : V → ℝ, u ≠ 0 → inner_pi pi_dist u constant_vec_one = 0 →
        0 < inner_pi pi_dist (H *ᵥ u) u := by
      intro u hu_ne hu_orth
      -- u ∉ ker(H) since ker(H) = span{1} and u ⊥ 1 with u ≠ 0
      have hu_not_ker : H *ᵥ u ≠ 0 := by
        by_contra h_in_ker
        -- H *ᵥ u = 0 means u ∈ ker(H) = span{1}
        have hu_in_span : u ∈ Submodule.span ℝ {constant_vec_one} := by
          rw [← h_ker]
          simp only [mem_ker, toLin'_apply, h_in_ker]
        -- So u = c • 1 for some c
        rw [mem_span_singleton] at hu_in_span
        obtain ⟨c, hc⟩ := hu_in_span
        -- But u ⊥ 1 means ⟨u, 1⟩ = 0
        -- ⟨c • 1, 1⟩ = c * ⟨1, 1⟩ = c * 1 = c
        have h_inner : inner_pi pi_dist u constant_vec_one = c * norm_sq_pi pi_dist constant_vec_one := by
          rw [← hc, inner_pi_smul_left, norm_sq_pi]
        rw [norm_sq_pi_one h_sum, mul_one] at h_inner
        rw [hu_orth] at h_inner
        -- So c = 0, hence u = c • 1 = 0 • 1 = 0
        have hc_zero : c = 0 := h_inner.symm
        rw [hc_zero, zero_smul] at hc
        exact hu_ne hc.symm
      -- By PSD: ⟨Hu, u⟩ ≥ 0
      have h_nonneg : 0 ≤ inner_pi pi_dist (H *ᵥ u) u := h_psd u
      -- If ⟨Hu, u⟩ = 0 then Hu = 0 by inner_H_zero_of_psd_zero, contradiction
      by_contra h_not_pos
      push_neg at h_not_pos
      have h_zero : inner_pi pi_dist (H *ᵥ u) u = 0 := le_antisymm h_not_pos h_nonneg
      have h_Hu_zero := inner_H_zero_of_psd_zero hπ H h_sa h_psd h_zero
      exact hu_not_ker h_Hu_zero
    -- Now show the infimum is positive
    -- The set defining SpectralGap_pi is {⟨Hu, u⟩/‖u‖² | u ≠ 0 ∧ u ⊥ 1}
    -- All elements are positive, so we need: nonempty and bounded below by ε > 0
    --
    -- Strategy: find any nonzero u ⊥ 1 and use its Rayleigh quotient as evidence
    -- Then show the infimum is positive using sInf_pos
    --
    -- First, show the set is nonempty by constructing a nonzero vector in 1⊥
    -- Since V is nontrivial, we have at least 2 elements v₀ ≠ v₁
    -- The vector e_v₀ - (π(v₀)/∑π) • 1 is orthogonal to 1 and nonzero for appropriate choice
    have h_exists_orth : ∃ w : V → ℝ, w ≠ 0 ∧ inner_pi pi_dist w constant_vec_one = 0 := by
      -- In nontrivial V, there exist distinct elements
      obtain ⟨v₀, v₁, hne⟩ := Nontrivial.exists_pair_ne (α := V)
      -- Consider the vector that is pi_dist v₁ at v₀, -pi_dist v₀ at v₁, and 0 elsewhere
      let w : V → ℝ := fun v => if v = v₀ then pi_dist v₁ else if v = v₁ then -(pi_dist v₀) else 0
      use w
      constructor
      · -- w ≠ 0 since w v₀ = pi_dist v₁ > 0
        intro hw
        have : w v₀ = 0 := congrFun hw v₀
        simp only [w, if_true] at this
        have hπ₁ : 0 < pi_dist v₁ := hπ v₁
        linarith
      · -- ⟨w, 1⟩_π = ∑ π(v) * w(v) * 1 = π(v₀) * π(v₁) + π(v₁) * (-π(v₀)) + 0 = 0
        simp only [inner_pi, constant_vec_one, mul_one]
        -- Split the sum
        have h_split : ∑ x, pi_dist x * w x =
            pi_dist v₀ * w v₀ + pi_dist v₁ * w v₁ + ∑ x ∈ Finset.univ.filter (fun x => x ≠ v₀ ∧ x ≠ v₁), pi_dist x * w x := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => x = v₀ ∨ x = v₁)]
          congr 1
          · -- Sum over {v₀, v₁}
            have h_filt : Finset.univ.filter (fun x => x = v₀ ∨ x = v₁) = {v₀, v₁} := by
              ext x
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
            rw [h_filt, Finset.sum_insert (Finset.notMem_singleton.mpr hne), Finset.sum_singleton]
          · -- Filter complement
            congr 1
            ext x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_or]
        rw [h_split]
        simp only [w, if_true, if_neg hne.symm, if_neg hne]
        -- The remaining sum is 0 since w x = 0 for x ∉ {v₀, v₁}
        have h_rest : ∑ x ∈ Finset.univ.filter (fun x => x ≠ v₀ ∧ x ≠ v₁), pi_dist x * w x = 0 := by
          apply Finset.sum_eq_zero
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          simp only [w, if_neg hx.1, if_neg hx.2, mul_zero]
        rw [h_rest, add_zero]
        ring
    -- Get a witness
    obtain ⟨w, hw_ne, hw_orth⟩ := h_exists_orth
    -- The Rayleigh quotient of w is positive
    have h_w_ray_pos : 0 < inner_pi pi_dist (H *ᵥ w) w / inner_pi pi_dist w w := by
      have h_num_pos : 0 < inner_pi pi_dist (H *ᵥ w) w := h_rayleigh_pos w hw_ne hw_orth
      have h_denom_pos : 0 < inner_pi pi_dist w w := norm_sq_pi_pos hπ hw_ne
      exact div_pos h_num_pos h_denom_pos
    -- The set is nonempty
    have h_set_nonempty : { r | ∃ v : V → ℝ, v ≠ 0 ∧ inner_pi pi_dist v constant_vec_one = 0 ∧
        r = inner_pi pi_dist (H *ᵥ v) v / inner_pi pi_dist v v }.Nonempty := by
      use inner_pi pi_dist (H *ᵥ w) w / inner_pi pi_dist w w
      simp only [Set.mem_setOf_eq]
      exact ⟨w, hw_ne, hw_orth, rfl⟩
    -- All elements of the set are positive
    have h_all_pos : ∀ r ∈ { r | ∃ v : V → ℝ, v ≠ 0 ∧ inner_pi pi_dist v constant_vec_one = 0 ∧
        r = inner_pi pi_dist (H *ᵥ v) v / inner_pi pi_dist v v }, 0 < r := by
      intro r hr
      simp only [Set.mem_setOf_eq] at hr
      obtain ⟨v, hv_ne, hv_orth, hr_eq⟩ := hr
      rw [hr_eq]
      have h_num_pos : 0 < inner_pi pi_dist (H *ᵥ v) v := h_rayleigh_pos v hv_ne hv_orth
      have h_denom_pos : 0 < inner_pi pi_dist v v := norm_sq_pi_pos hπ hv_ne
      exact div_pos h_num_pos h_denom_pos
    -- The infimum of positive Rayleigh quotients is positive in finite dimensions.
    -- This follows from: (1) scale invariance of Rayleigh quotient, (2) compactness of the
    -- normalized constraint set {v | ‖v‖²_π = 1, v ⊥_π 1}, and (3) extreme value theorem.
    --
    -- In finite V, the Rayleigh quotient R(v) = ⟨Hv, v⟩_π / ‖v‖²_π achieves its minimum
    -- ε > 0 on the compact set, so sInf S ≥ ε > 0.
    --
    -- Technical implementation: we use that the set S has a positive lower bound.
    -- Since all elements are positive, sInf S ≥ 0. We show sInf S > 0 by contradiction:
    -- if sInf S = 0, then for any ε > 0 there exists r ∈ S with r < ε, but this would
    -- contradict the finite-dimensional compactness argument.
    --
    -- For now, we use sInf_pos with a positive lower bound from h_all_pos.
    by_contra h_not_pos
    push_neg at h_not_pos
    -- sInf S ≤ 0, and since S is bounded below by 0 (all elements positive), sInf S ≥ 0
    have h_sInf_nonneg : 0 ≤ SpectralGap_pi pi_dist H := by
      apply Real.sInf_nonneg
      intro r hr
      exact le_of_lt (h_all_pos r hr)
    have h_sInf_zero : SpectralGap_pi pi_dist H = 0 := le_antisymm h_not_pos h_sInf_nonneg
    -- Finite-dimensional compactness argument:
    -- The set of Rayleigh quotients S = {⟨Hv,v⟩/‖v‖² | v≠0, v⊥1} equals, by scale invariance,
    -- the set {⟨Hv,v⟩ | ‖v‖²=1, v⊥1}. On this compact normalized set, the continuous
    -- function v ↦ ⟨Hv,v⟩ achieves its positive minimum, so sInf S > 0.

    -- Define the normalized constraint set K = {v | ‖v‖²_π = 1 ∧ v ⊥_π 1}
    let K := {v : V → ℝ | inner_pi pi_dist v constant_vec_one = 0 ∧ norm_sq_pi pi_dist v = 1}

    -- K is nonempty: normalize our witness w
    have h_K_nonempty : K.Nonempty := by
      have hw_pos : 0 < norm_sq_pi pi_dist w := norm_sq_pi_pos hπ hw_ne
      let c := 1 / Real.sqrt (norm_sq_pi pi_dist w)
      use c • w
      constructor
      · -- Orthogonality preserved under scaling
        rw [inner_pi_smul_left, hw_orth, mul_zero]
      · -- Normalized to have ‖·‖² = 1
        rw [norm_sq_pi, inner_pi_smul_left, inner_pi_smul_right, ← norm_sq_pi]
        simp only [c]
        have h_sqrt_pos : 0 < Real.sqrt (norm_sq_pi pi_dist w) := Real.sqrt_pos.mpr hw_pos
        field_simp
        rw [Real.sq_sqrt (le_of_lt hw_pos)]

    -- Continuity of inner_pi (as a function of first argument with second fixed)
    have h_inner_cont : ∀ u₀ : V → ℝ, Continuous (fun v => inner_pi pi_dist v u₀) := by
      intro u₀
      simp only [inner_pi]
      apply continuous_finset_sum
      intro x _
      exact (continuous_const.mul (continuous_apply x)).mul continuous_const

    -- Continuity of norm_sq_pi
    have h_norm_sq_cont : Continuous (fun v => norm_sq_pi pi_dist v) := by
      simp only [norm_sq_pi, inner_pi]
      apply continuous_finset_sum
      intro x _
      exact (continuous_const.mul (continuous_apply x)).mul (continuous_apply x)

    -- K is closed: intersection of level sets of continuous functions
    have hK_closed : IsClosed K := by
      apply IsClosed.inter
      · exact isClosed_eq (h_inner_cont constant_vec_one) continuous_const
      · exact isClosed_eq h_norm_sq_cont continuous_const

    -- K is bounded in the standard sup norm
    -- Since ‖v‖²_π = 1 and π weights are positive, each |v(x)|² ≤ 1/π_min
    have hK_bounded : Bornology.IsBounded K := by
      rw [Metric.isBounded_iff_subset_closedBall (0 : V → ℝ)]
      -- Find π_min > 0 as the minimum weight
      let π_min := Finset.univ.inf' (Finset.univ_nonempty) pi_dist
      have hπ_min_pos : 0 < π_min := by
        rw [Finset.lt_inf'_iff]
        exact fun x _ => hπ x
      -- The sup norm of any v ∈ K is bounded by √(1/π_min)
      use Real.sqrt (1 / π_min)
      intro v hv
      simp only [K, Set.mem_setOf_eq] at hv
      rw [Metric.mem_closedBall, dist_zero_right]
      have hv_norm : norm_sq_pi pi_dist v = 1 := hv.2
      -- For any coordinate x, π(x) v(x)² ≤ ‖v‖²_π = 1, so v(x)² ≤ 1/π(x) ≤ 1/π_min
      have h_coord_bound : ∀ x, |v x| ≤ Real.sqrt (1 / π_min) := by
        intro x
        have hπx_pos : 0 < pi_dist x := hπ x
        have hπx_ge : π_min ≤ pi_dist x := Finset.inf'_le _ (Finset.mem_univ x)
        -- π(x) v(x)² is one term in the sum ‖v‖²_π = 1
        have h_term_le : pi_dist x * (v x)^2 ≤ 1 := by
          simp only [norm_sq_pi, inner_pi] at hv_norm
          have h_sum_eq : ∑ y : V, pi_dist y * v y * v y = 1 := hv_norm
          have h_term_in_sum : pi_dist x * (v x)^2 ≤ ∑ y : V, pi_dist y * v y * v y := by
            have : pi_dist x * (v x)^2 = pi_dist x * v x * v x := by ring
            rw [this]
            apply Finset.single_le_sum _ (Finset.mem_univ x)
            intro y _
            have := mul_nonneg (le_of_lt (hπ y)) (mul_self_nonneg (v y))
            linarith [this]
          linarith
        have h_sq_le : (v x)^2 ≤ 1 / π_min := by
          calc (v x)^2 = (pi_dist x * (v x)^2) / pi_dist x := by field_simp
            _ ≤ 1 / pi_dist x := div_le_div_of_nonneg_right h_term_le (le_of_lt hπx_pos)
            _ ≤ 1 / π_min := div_le_div_of_nonneg_left (by linarith) hπ_min_pos hπx_ge
        rw [← Real.sqrt_sq (abs_nonneg (v x)), sq_abs]
        exact Real.sqrt_le_sqrt h_sq_le
      -- The sup norm is the maximum of |v x| over all x
      rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
      exact h_coord_bound

    -- In finite dimension, closed + bounded = compact
    haveI : FiniteDimensional ℝ (V → ℝ) := Module.Finite.pi
    have hK_compact : IsCompact K := Metric.isCompact_of_isClosed_isBounded hK_closed hK_bounded

    -- Define the Rayleigh numerator function R(v) = ⟨Hv, v⟩
    let R := fun v => inner_pi pi_dist (H *ᵥ v) v

    -- R is continuous
    have hR_cont : Continuous R := by
      simp only [R, inner_pi, mulVec]
      apply continuous_finset_sum
      intro x _
      apply Continuous.mul
      apply Continuous.mul
      · exact continuous_const
      · -- (H *ᵥ v) x = ∑ y, H x y * v y is continuous in v
        apply continuous_finset_sum
        intro y _
        exact continuous_const.mul (continuous_apply y)
      · exact continuous_apply x

    -- By extreme value theorem: R achieves minimum on compact nonempty K
    -- The image R(K) is compact (continuous image of compact)
    have hRK_compact : IsCompact (R '' K) := hK_compact.image hR_cont
    -- R(K) is nonempty
    have hRK_nonempty : (R '' K).Nonempty := h_K_nonempty.image R
    -- R(K) is bounded below (compact sets in ℝ are bounded)
    have hRK_bddBelow : BddBelow (R '' K) := hRK_compact.bddBelow
    -- In ℝ, nonempty compact sets contain their infimum
    have h_sInf_mem : sInf (R '' K) ∈ R '' K := hRK_compact.isClosed.csInf_mem hRK_nonempty hRK_bddBelow
    -- Get the minimizer v₀
    obtain ⟨v₀, hv₀_mem, hv₀_eq⟩ := h_sInf_mem

    -- v₀ ∈ K means v₀ ⊥ 1 and ‖v₀‖²_π = 1
    have hv₀_orth : inner_pi pi_dist v₀ constant_vec_one = 0 := hv₀_mem.1
    have hv₀_norm : norm_sq_pi pi_dist v₀ = 1 := hv₀_mem.2

    -- v₀ ≠ 0 since ‖v₀‖² = 1 > 0
    have hv₀_ne : v₀ ≠ 0 := by
      intro h
      rw [h, norm_sq_pi, inner_pi_zero_right] at hv₀_norm
      linarith

    -- R(v₀) > 0 since v₀ is nonzero and orthogonal to 1
    have h_min_pos : 0 < R v₀ := h_rayleigh_pos v₀ hv₀_ne hv₀_orth

    -- R(v₀) = sInf (R '' K), and R(v₀) is a lower bound for all R values on K
    have hv₀_is_min : ∀ u ∈ K, R v₀ ≤ R u := by
      intro u hu
      rw [hv₀_eq]
      exact csInf_le hRK_compact.bddBelow (Set.mem_image_of_mem R hu)

    -- For any r ∈ S, we have r ≥ R(v₀) by scale invariance
    -- If r = ⟨Hu,u⟩/‖u‖² with u≠0, u⊥1, then normalizing u' = u/√‖u‖² gives r = R(u')
    have h_lower_bound : ∀ r ∈ { r | ∃ v : V → ℝ, v ≠ 0 ∧ inner_pi pi_dist v constant_vec_one = 0 ∧
        r = inner_pi pi_dist (H *ᵥ v) v / inner_pi pi_dist v v }, R v₀ ≤ r := by
      intro r hr
      simp only [Set.mem_setOf_eq] at hr
      obtain ⟨u, hu_ne, hu_orth, hr_eq⟩ := hr
      -- Normalize u to get u' ∈ K
      have hu_pos : 0 < norm_sq_pi pi_dist u := norm_sq_pi_pos hπ hu_ne
      let c := 1 / Real.sqrt (norm_sq_pi pi_dist u)
      let u' := c • u
      have hc_pos : 0 < c := div_pos one_pos (Real.sqrt_pos.mpr hu_pos)
      have hu'_mem : u' ∈ K := by
        constructor
        · rw [inner_pi_smul_left, hu_orth, mul_zero]
        · rw [norm_sq_pi, inner_pi_smul_left, inner_pi_smul_right, ← norm_sq_pi]
          simp only [c]
          have h_sqrt_pos : 0 < Real.sqrt (norm_sq_pi pi_dist u) := Real.sqrt_pos.mpr hu_pos
          field_simp
          rw [Real.sq_sqrt (le_of_lt hu_pos)]
      -- r = R(u') by scale invariance
      have hr_eq' : r = R u' := by
        rw [hr_eq]
        simp only [R, u', mulVec_smul, inner_pi_smul_left, inner_pi_smul_right, c]
        have h_sqrt_pos : 0 < Real.sqrt (norm_sq_pi pi_dist u) := Real.sqrt_pos.mpr hu_pos
        have h_denom_ne : norm_sq_pi pi_dist u ≠ 0 := ne_of_gt hu_pos
        have h_uu : inner_pi pi_dist u u = norm_sq_pi pi_dist u := rfl
        rw [h_uu]
        field_simp
        rw [Real.sq_sqrt (le_of_lt hu_pos)]
      rw [hr_eq']
      exact hv₀_is_min u' hu'_mem

    -- Therefore sInf S ≥ R(v₀) > 0
    have h_sInf_ge : R v₀ ≤ SpectralGap_pi pi_dist H := le_csInf h_set_nonempty h_lower_bound

    -- But sInf S = 0, so R(v₀) ≤ 0, contradicting R(v₀) > 0
    linarith

end Assumptions
end SGC.Spectral
