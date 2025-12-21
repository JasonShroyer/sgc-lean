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

/-! ### 3. Quotient Generator (Simple Form) -/

/-- Row sum over a block: Σ_{k∈B} L_{i,k}. -/
def row_sum_block (L : Matrix V V ℝ) (P : Partition V) (i : V) (B : P.Quot) : ℝ :=
  ∑ k : V, if P.quot_map k = B then L i k else 0

/-- Under strong lumpability, row_sum_block is constant on equivalence classes. -/
lemma row_sum_block_const (L : Matrix V V ℝ) (P : Partition V)
    (hL : IsStronglyLumpable L P) (i j : V) (hij : P.rel.r i j) (B : P.Quot) :
    row_sum_block L P i B = row_sum_block L P j B :=
  hL i j hij B

/-- The quotient generator M on Q (simple form using any representative).
    M_{A,B} = Σ_{k∈B} L_{u,k} for any u ∈ A.
    
    Under strong lumpability, this is well-defined. -/
def QuotientGeneratorSimple (L : Matrix V V ℝ) (P : Partition V) : Matrix P.Quot P.Quot ℝ :=
  fun A B => row_sum_block L P (Quotient.out A) B

/-- The lift matrix K : V × Q where K_{i,B} = 1 if i ∈ B, else 0. -/
def lift_matrix (P : Partition V) : Matrix V P.Quot ℝ :=
  fun i B => if P.quot_map i = B then 1 else 0

/-! ### 4. The Intertwining Theorem -/

/-- LHS of intertwining: (L * K)_{i,B} = Σ_k L_{ik} * K_{kB} = Σ_{k∈B} L_{ik}. -/
lemma LK_entry (L : Matrix V V ℝ) (P : Partition V) (i : V) (B : P.Quot) :
    (L * lift_matrix P) i B = row_sum_block L P i B := by
  simp only [Matrix.mul_apply, lift_matrix]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : P.quot_map k = B
  · simp [h]
  · simp [h]

/-- RHS of intertwining: (K * M)_{i,B} = Σ_C K_{iC} * M_{CB} = M_{⟦i⟧,B}. -/
lemma KM_entry (L : Matrix V V ℝ) (P : Partition V) (i : V) (B : P.Quot) :
    (lift_matrix P * QuotientGeneratorSimple L P) i B = 
    QuotientGeneratorSimple L P (P.quot_map i) B := by
  simp only [Matrix.mul_apply, lift_matrix, QuotientGeneratorSimple]
  -- Sum over C: if P.quot_map i = C then 1 * row_sum else 0
  -- Only C = P.quot_map i contributes
  have h_sum : (∑ C : P.Quot, (if P.quot_map i = C then (1 : ℝ) else 0) * 
      row_sum_block L P (Quotient.out C) B) = 
      row_sum_block L P (Quotient.out (P.quot_map i)) B := by
    -- Only the term where C = P.quot_map i contributes
    rw [Finset.sum_eq_single (P.quot_map i)]
    · -- When C = P.quot_map i: the condition is true
      simp only [↓reduceIte, one_mul]
    · -- When C ≠ P.quot_map i: the term is 0
      intro C _ hC
      rw [if_neg (Ne.symm hC), zero_mul]
    · -- P.quot_map i is in univ
      intro h
      exact (h (Finset.mem_univ _)).elim
  exact h_sum

/-- Under strong lumpability, the quotient generator at ⟦i⟧ equals row_sum at i. -/
lemma quot_gen_eq_row_sum (L : Matrix V V ℝ) (P : Partition V)
    (hL : IsStronglyLumpable L P) (i : V) (B : P.Quot) :
    QuotientGeneratorSimple L P (P.quot_map i) B = row_sum_block L P i B := by
  simp only [QuotientGeneratorSimple]
  -- Need: row_sum_block L P (Quotient.out (P.quot_map i)) B = row_sum_block L P i B
  -- Since Quotient.out (P.quot_map i) ≈ i
  have h_out_eq : Quotient.mk P.rel (Quotient.out (P.quot_map i)) = P.quot_map i := 
    Quotient.out_eq (P.quot_map i)
  have h_i_eq : Quotient.mk P.rel i = P.quot_map i := rfl
  have h_equiv : P.rel.r (Quotient.out (P.quot_map i)) i := by
    have h := h_out_eq.trans h_i_eq.symm
    exact Quotient.eq'.mp h
  exact row_sum_block_const L P hL _ i h_equiv B

/-- **The Intertwining Theorem (Dynkin Formula)**: L * K = K * M.
    
    The original dynamics L and quotient dynamics M are related by the lift operator.
    This is the fundamental algebraic property of strong lumpability. -/
theorem intertwining (L : Matrix V V ℝ) (P : Partition V) (hL : IsStronglyLumpable L P) :
    L * lift_matrix P = lift_matrix P * QuotientGeneratorSimple L P := by
  ext i B
  rw [LK_entry, KM_entry, quot_gen_eq_row_sum L P hL]

/-! ### 5. Weighted Quotient Generator -/

/-- The weighted quotient generator L̄ on V̄.
    L̄_{āb̄} = (1/π̄(ā)) * Σ_{x∈ā} π(x) * (Σ_{z∈b̄} L_{xz})
    
    Under strong lumpability, this equals the simple form. -/
def QuotientGenerator (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) : Matrix P.Quot P.Quot ℝ :=
  fun a_bar b_bar =>
    let sum_over_a := ∑ x : V, if P.quot_map x = a_bar 
      then pi_dist x * row_sum_block L P x b_bar
      else 0
    sum_over_a / pi_bar P pi_dist a_bar

/-- Under strong lumpability, weighted and simple quotient generators agree. -/
lemma quotient_generator_eq_simple (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (hL : IsStronglyLumpable L P) (A B : P.Quot) :
    QuotientGenerator L P pi_dist hπ A B = QuotientGeneratorSimple L P A B := by
  simp only [QuotientGenerator, QuotientGeneratorSimple]
  -- The sum is Σ_{x∈A} π(x) * row_sum_block = row_sum_block(rep) * Σ_{x∈A} π(x)
  -- since row_sum_block is constant on A by lumpability
  obtain ⟨a, ha⟩ := Quotient.exists_rep A
  have h_const : ∀ x, P.quot_map x = A → row_sum_block L P x B = row_sum_block L P a B := by
    intro x hx
    have h_eq : P.rel.r x a := by
      simp only [Partition.quot_map] at hx
      rw [← ha] at hx
      exact Quotient.eq'.mp hx
    exact row_sum_block_const L P hL x a h_eq B
  have h_sum : (∑ x, if P.quot_map x = A then pi_dist x * row_sum_block L P x B else 0) =
      row_sum_block L P a B * (∑ x, if P.quot_map x = A then pi_dist x else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : P.quot_map x = A
    · simp only [hx, ↓reduceIte]
      rw [h_const x hx]
      ring
    · simp [hx]
  rw [h_sum]
  have h_pi_bar_eq : (∑ x, if P.quot_map x = A then pi_dist x else 0) = pi_bar P pi_dist A := rfl
  rw [h_pi_bar_eq]
  have hπ_bar_pos : 0 < pi_bar P pi_dist A := pi_bar_pos P hπ A
  have hπ_bar_ne : pi_bar P pi_dist A ≠ 0 := ne_of_gt hπ_bar_pos
  rw [mul_div_assoc, div_self hπ_bar_ne, mul_one]
  -- Now show: row_sum_block L P a B = row_sum_block L P (Quotient.out A) B
  have h_a_in_A : P.quot_map a = A := ha
  have h_out_in_A : Quotient.mk P.rel (Quotient.out A) = A := Quotient.out_eq A
  have h_equiv : P.rel.r a (Quotient.out A) := by
    have h1 : Quotient.mk P.rel a = A := h_a_in_A
    have h2 := h1.trans h_out_in_A.symm
    exact Quotient.eq'.mp h2
  exact row_sum_block_const L P hL a _ h_equiv B

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
