/-
  UPAT/Stability/Functoriality/Lumpability.lean
  
  Strong Lumpability and Functorial Stability (UFHDT).
  
  This file upgrades FHDT to the Universal Functorial Heat Dominance Theorem:
  the stability triad (λ_gap, β(t), B(t)) is functorial under RG coarse-graining.
  
  Key theorems:
  - heat_kernel_quot_commute: e^{tL̄} ∘ Q = Q ∘ e^{tL}
  - spectrum_subset: Spec(L̄) ⊆ Spec(L)
  - gap_non_decrease: λ̄_gap ≥ λ_gap
  - fhdt_functorial: |β̄(t)| ≤ C̄ e^{-λ̄_gap t}
  
  Design: Setoid-based partition with explicit quotient map Q.
-/

import UPAT.Axioms.Geometry
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Data.Setoid.Partition
import Mathlib.Tactic

noncomputable section
open Finset LinearMap Matrix Real NormedSpace

namespace UPAT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### 1. Strong Lumpability Definition -/

/-- A partition of V into blocks (coarse-grained states).
    Uses Setoid for clean quotient handling. -/
structure Partition (V : Type*) [DecidableEq V] where
  rel : Setoid V
  decRel : DecidableRel rel.r

/-- The quotient type (coarse-grained state space). -/
abbrev Partition.Quot {V : Type*} [DecidableEq V] (P : Partition V) : Type _ := Quotient P.rel

instance Partition.instDecidableRel {V : Type*} [DecidableEq V] (P : Partition V) : 
    DecidableRel P.rel.r := P.decRel

instance Partition.instFintype {V : Type*} [Fintype V] [DecidableEq V] (P : Partition V) : 
    Fintype P.Quot := @Quotient.fintype V _ P.rel P.decRel

instance Partition.instDecidableEq {V : Type*} [DecidableEq V] (P : Partition V) : 
    DecidableEq P.Quot := @Quotient.decidableEq V P.rel P.decRel

/-- The quotient map: V → V̄. -/
def Partition.quot_map (P : Partition V) : V → P.Quot := Quotient.mk P.rel

/-- The aggregation weight: π̄(ā) = Σ_{x∈ā} π(x). -/
def pi_bar (P : Partition V) (pi_dist : V → ℝ) : P.Quot → ℝ :=
  fun a_bar => ∑ x : V, if P.quot_map x = a_bar then pi_dist x else 0

/-- Helper: sum over equivalence class. -/
lemma pi_bar_eq_sum_class (P : Partition V) (pi_dist : V → ℝ) (a_bar : P.Quot) :
    pi_bar P pi_dist a_bar = ∑ x : V, if P.quot_map x = a_bar then pi_dist x else 0 := rfl

/-- π̄ is positive when π is positive. -/
lemma pi_bar_pos (P : Partition V) {pi_dist : V → ℝ} (hπ : ∀ v, 0 < pi_dist v) 
    (a_bar : P.Quot) : 0 < pi_bar P pi_dist a_bar := by
  unfold pi_bar
  obtain ⟨a, ha⟩ := Quotient.exists_rep a_bar
  have h_mem : P.quot_map a = a_bar := by simp [Partition.quot_map, ha]
  apply Finset.sum_pos'
  · intro x _
    by_cases h : P.quot_map x = a_bar <;> simp [h, le_of_lt (hπ x)]
  · exact ⟨a, Finset.mem_univ a, by simp [h_mem, hπ a]⟩

/-- π̄ sums to 1 when π sums to 1. -/
lemma pi_bar_sum_one (P : Partition V) {pi_dist : V → ℝ} (h_sum : ∑ v, pi_dist v = 1) :
    ∑ a_bar, pi_bar P pi_dist a_bar = 1 := by
  unfold pi_bar
  rw [← h_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have h_eq : (∑ a_bar : P.Quot, if P.quot_map x = a_bar then pi_dist x else 0) = pi_dist x := by
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_univ]
  exact h_eq

/-! ### 2. Strong Lumpability Condition -/

/-- **Strong Lumpability**: L is strongly lumpable w.r.t. partition P if
    for all x, y in the same block, and all blocks b̄:
    Σ_{z∈b̄} L_{xz} = Σ_{z∈b̄} L_{yz}
    
    This ensures the quotient generator is well-defined. -/
def IsStronglyLumpable (L : Matrix V V ℝ) (P : Partition V) : Prop :=
  ∀ x y : V, P.rel.r x y → ∀ b_bar : P.Quot,
    (∑ z : V, if P.quot_map z = b_bar then L x z else 0) =
    (∑ z : V, if P.quot_map z = b_bar then L y z else 0)

/-! ### 3. Quotient Generator -/

/-- The quotient generator L̄ on V̄.
    L̄_{āb̄} = (1/π̄(ā)) * Σ_{x∈ā} π(x) * (Σ_{z∈b̄} L_{xz})
    
    Under strong lumpability, this is independent of representative choice. -/
def QuotientGenerator (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) : Matrix P.Quot P.Quot ℝ :=
  fun a_bar b_bar =>
    let sum_over_a := ∑ x : V, if P.quot_map x = a_bar 
      then pi_dist x * (∑ z : V, if P.quot_map z = b_bar then L x z else 0)
      else 0
    sum_over_a / pi_bar P pi_dist a_bar

/-- Helper: The inner sum for quotient generator. -/
def inner_sum_L (L : Matrix V V ℝ) (P : Partition V) (x : V) (b_bar : P.Quot) : ℝ :=
  ∑ z : V, if P.quot_map z = b_bar then L x z else 0

/-- Under strong lumpability, the inner sum is constant on equivalence classes. -/
lemma inner_sum_L_const_on_class (L : Matrix V V ℝ) (P : Partition V)
    (hL : IsStronglyLumpable L P) (x y : V) (hxy : P.rel.r x y) (b_bar : P.Quot) :
    inner_sum_L L P x b_bar = inner_sum_L L P y b_bar :=
  hL x y hxy b_bar

/-! ### 4. Quotient Map as Linear Operator -/

/-- The averaging/quotient map Q : (V → ℝ) → (V̄ → ℝ).
    (Q f)(ā) = (1/π̄(ā)) * Σ_{x∈ā} π(x) * f(x) -/
def Q_map (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) : 
    (V → ℝ) →ₗ[ℝ] (P.Quot → ℝ) where
  toFun f a_bar := 
    (∑ x : V, if P.quot_map x = a_bar then pi_dist x * f x else 0) / pi_bar P pi_dist a_bar
  map_add' f g := by
    ext a_bar
    show (∑ x, if P.quot_map x = a_bar then pi_dist x * (f x + g x) else 0) / _ = _
    have h_num : (∑ x, if P.quot_map x = a_bar then pi_dist x * (f x + g x) else 0) =
        (∑ x, if P.quot_map x = a_bar then pi_dist x * f x else 0) +
        (∑ x, if P.quot_map x = a_bar then pi_dist x * g x else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : P.quot_map x = a_bar
      · simp only [h, ↓reduceIte, mul_add]
      · simp only [h, ↓reduceIte, add_zero]
    rw [h_num, add_div]
    rfl
  map_smul' c f := by
    ext a_bar
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    have h_num : (∑ x, if P.quot_map x = a_bar then pi_dist x * (c * f x) else 0) =
        c * (∑ x, if P.quot_map x = a_bar then pi_dist x * f x else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : P.quot_map x = a_bar
      · simp [h]; ring
      · simp [h]
    rw [h_num, mul_div_assoc]

/-- The lifting map: (V̄ → ℝ) → (V → ℝ).
    (lift g)(x) = g(q(x)) -/
def lift_map (P : Partition V) : (P.Quot → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun g x := g (P.quot_map x)
  map_add' f g := by ext x; simp [Pi.add_apply]
  map_smul' c f := by ext x; simp [Pi.smul_apply, smul_eq_mul]

/-! ### 5. Intertwining Relation -/

/-- The intertwining relation: Q ∘ L = L̄ ∘ Q.
    This is the key algebraic property of strong lumpability. -/
theorem intertwining_QL (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (hL : IsStronglyLumpable L P) :
    Q_map P pi_dist hπ ∘ₗ toLin' L = 
    toLin' (QuotientGenerator L P pi_dist hπ) ∘ₗ Q_map P pi_dist hπ := by
  apply LinearMap.ext
  intro f
  ext a_bar
  simp only [LinearMap.comp_apply, toLin'_apply, Q_map, LinearMap.coe_mk, AddHom.coe_mk]
  -- LHS: (Q (L f))(ā) = (Σ_{x∈ā} π(x) * (Σ_y L_{xy} f(y))) / π̄(ā)
  -- RHS: (L̄ (Q f))(ā) = Σ_b̄ L̄_{āb̄} * (Q f)(b̄)
  -- Goal: Show these are equal using strong lumpability
  -- 
  -- The full intertwining proof requires careful manipulation of sums
  -- Using strong lumpability to show independence of representative choice
  -- This is a non-trivial calculation involving Fubini and the lumpability condition
  sorry

/-! ### 6. Heat Kernel Commutation -/

/-- The heat kernel on the quotient space. -/
def HeatKernel_bar (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) 
    (hπ : ∀ v, 0 < pi_dist v) (t : ℝ) : Matrix P.Quot P.Quot ℝ :=
  exp ℝ (t • QuotientGenerator L P pi_dist hπ)

/-- **Heat Kernel Commutation**: e^{tL̄} ∘ Q = Q ∘ e^{tL}.
    The semigroup intertwines with the quotient map. -/
theorem heat_kernel_quot_commute (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (hL : IsStronglyLumpable L P) (t : ℝ) :
    toLin' (HeatKernel_bar L P pi_dist hπ t) ∘ₗ Q_map P pi_dist hπ = 
    Q_map P pi_dist hπ ∘ₗ toLin' (exp ℝ (t • L)) := by
  -- Strategy: Use that intertwining Q L = L̄ Q implies Q L^n = L̄^n Q by induction
  -- Then by linearity of exp series: Q exp(tL) = exp(tL̄) Q
  sorry

/-! ### 7. Spectrum Containment -/

/-- The spectral gap on the quotient. -/
def SpectralGap_bar (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) 
    (hπ : ∀ v, 0 < pi_dist v) : ℝ :=
  let L_bar : Matrix P.Quot P.Quot ℝ := QuotientGenerator L P pi_dist hπ
  let H_bar : Matrix P.Quot P.Quot ℝ := (1/2 : ℝ) • (L_bar + L_barᵀ)
  let pi_bar' : P.Quot → ℝ := pi_bar P pi_dist
  sInf { r | ∃ g : P.Quot → ℝ, g ≠ 0 ∧ 
    inner_pi pi_bar' g (fun _ => 1) = 0 ∧
    r = inner_pi pi_bar' (H_bar *ᵥ g) g / inner_pi pi_bar' g g }

/-- **Spectral Gap Non-Decrease**: λ̄_gap ≥ λ_gap.
    Coarse-graining cannot decrease the spectral gap. -/
theorem gap_non_decrease (L H : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (h_sum : ∑ v, pi_dist v = 1)
    (hL : IsStronglyLumpable L P)
    (h_sa : ∀ u v, inner_pi pi_dist (H *ᵥ u) v = inner_pi pi_dist u (H *ᵥ v))
    (h_psd : ∀ u, 0 ≤ inner_pi pi_dist (H *ᵥ u) u) :
    SpectralGap_bar L P pi_dist hπ ≥ 
    sInf { r | ∃ v : V → ℝ, v ≠ 0 ∧ inner_pi pi_dist v constant_vec_one = 0 ∧
      r = inner_pi pi_dist (H *ᵥ v) v / inner_pi pi_dist v v } := by
  -- Strategy: Every test function on V̄ lifts to a test function on V
  -- The Rayleigh quotient of the lift is ≤ the quotient Rayleigh quotient
  -- Therefore the infimum over V̄ is ≥ the infimum over V
  sorry

/-! ### 8. Functorial FHDT -/

/-- **Functorial Heat Dominance Theorem (UFHDT)**:
    The stability bound descends to the quotient with preserved structure. -/
theorem fhdt_functorial (L H : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (h_sum : ∑ v, pi_dist v = 1)
    (hL : IsStronglyLumpable L P)
    (h_gap_pos : 0 < sInf { r | ∃ v : V → ℝ, v ≠ 0 ∧ 
      inner_pi pi_dist v constant_vec_one = 0 ∧
      r = inner_pi pi_dist (H *ᵥ v) v / inner_pi pi_dist v v })
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ C_bar ≥ 0, 
      opNorm_pi (pi_bar P pi_dist) (pi_bar_pos P hπ) 
        (toLin' (HeatKernel_bar L P pi_dist hπ t) ∘ₗ 
         P_ortho_pi (pi_bar P pi_dist) (pi_bar_sum_one P h_sum) (pi_bar_pos P hπ)) ≤ 
      C_bar * exp (-(SpectralGap_bar L P pi_dist hπ) * t) := by
  -- The bound on V̄ follows from:
  -- 1. The intertwining Q K(t) = K̄(t) Q
  -- 2. The gap non-decrease λ̄_gap ≥ λ_gap
  -- 3. The FHDT bound on V descends via Q
  sorry

end UPAT
