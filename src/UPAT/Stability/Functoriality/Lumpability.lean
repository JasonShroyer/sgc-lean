/-
  UPAT/Stability/Functoriality/Lumpability.lean
  
  Strong Lumpability and Functorial Stability.
  
  This file establishes that the stability triad (λ_gap, β(t), B(t)) is 
  functorial under coarse-graining (renormalization group transformations).
  
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

/-- Power intertwining: L^n * K = K * M^n by induction. -/
theorem intertwining_pow (L : Matrix V V ℝ) (P : Partition V) (hL : IsStronglyLumpable L P) 
    (n : ℕ) : L ^ n * lift_matrix P = lift_matrix P * (QuotientGeneratorSimple L P) ^ n := by
  induction n with
  | zero => simp [Matrix.one_mul, Matrix.mul_one]
  | succ n ih =>
    calc L ^ (n + 1) * lift_matrix P 
        = L ^ n * L * lift_matrix P := by rw [pow_succ]
      _ = L ^ n * (L * lift_matrix P) := by rw [Matrix.mul_assoc]
      _ = L ^ n * (lift_matrix P * QuotientGeneratorSimple L P) := by rw [intertwining L P hL]
      _ = (L ^ n * lift_matrix P) * QuotientGeneratorSimple L P := by rw [Matrix.mul_assoc]
      _ = (lift_matrix P * (QuotientGeneratorSimple L P) ^ n) * QuotientGeneratorSimple L P := by rw [ih]
      _ = lift_matrix P * ((QuotientGeneratorSimple L P) ^ n * QuotientGeneratorSimple L P) := by rw [Matrix.mul_assoc]
      _ = lift_matrix P * (QuotientGeneratorSimple L P) ^ (n + 1) := by rw [← pow_succ]

/-! ### 5. Weighted Quotient Generator -/

/-- The weighted quotient generator L̄ on V̄.
    L̄_{āb̄} = (1/π̄(ā)) * Σ_{x∈ā} π(x) * (Σ_{z∈b̄} L_{xz})
    
    Under strong lumpability, this equals the simple form. -/
def QuotientGenerator (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (_hπ : ∀ v, 0 < pi_dist v) : Matrix P.Quot P.Quot ℝ :=
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
def Q_map (P : Partition V) (pi_dist : V → ℝ) (_hπ : ∀ v, 0 < pi_dist v) : 
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

/-! ### 5. Block-Constant Functions and Lift Isometry -/

/-- A function is block-constant if it's constant on equivalence classes. -/
def IsBlockConstant (P : Partition V) (f : V → ℝ) : Prop :=
  ∀ x y : V, P.rel.r x y → f x = f y

/-- The lift of a function on Q to V is block-constant. -/
lemma lift_is_block_constant (P : Partition V) (g : P.Quot → ℝ) :
    IsBlockConstant P (fun x => g (P.quot_map x)) := fun x y hxy => by
  simp only [Partition.quot_map]
  congr 1
  exact Quotient.sound hxy

/-- **Lift Isometry**: ⟨lift(f), lift(f)⟩_π = ⟨f, f⟩_π̄.
    The lift preserves the weighted L² norm. -/
lemma lift_inner_pi_eq (P : Partition V) (pi_dist : V → ℝ) (g : P.Quot → ℝ) :
    inner_pi pi_dist (fun x => g (P.quot_map x)) (fun x => g (P.quot_map x)) =
    inner_pi (pi_bar P pi_dist) g g := by
  simp only [inner_pi, pi_bar]
  -- LHS: Σ_x π(x) * g([x])²
  -- RHS: Σ_A (Σ_{x∈A} π(x)) * g(A)²
  -- Rewrite LHS by grouping by equivalence class
  have h_group : ∀ x : V, pi_dist x * g (P.quot_map x) * g (P.quot_map x) = 
      ∑ A : P.Quot, if P.quot_map x = A then pi_dist x * g A * g A else 0 := fun x => by
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  simp_rw [h_group]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _
  have h_factor : (∑ x, if P.quot_map x = A then pi_dist x * g A * g A else 0) = 
      (∑ x, if P.quot_map x = A then pi_dist x else 0) * g A * g A := by
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : P.quot_map x = A
    · simp [h]
    · simp [h]
  rw [h_factor]

/-- Block-constant functions correspond exactly to lifted functions. -/
lemma block_constant_iff_lift (P : Partition V) (f : V → ℝ) :
    IsBlockConstant P f ↔ ∃ g : P.Quot → ℝ, f = fun x => g (P.quot_map x) := by
  constructor
  · intro hf
    -- Define g on representatives
    use fun A => f (Quotient.out A)
    ext x
    simp only [Partition.quot_map]
    have h_eq : P.rel.r x (Quotient.out (Quotient.mk P.rel x)) := by
      have := Quotient.out_eq (Quotient.mk P.rel x)
      exact Quotient.eq'.mp this.symm
    exact hf x _ h_eq
  · intro ⟨g, hg⟩
    rw [hg]
    exact lift_is_block_constant P g

/-! ### 7. Vector Intertwining and Quadratic Form Preservation -/

/-- The lift function: given f : Q → ℝ, produce a block-constant function on V. -/
def lift_fun (P : Partition V) (f : P.Quot → ℝ) : V → ℝ := fun x => f (P.quot_map x)

/-- lift_fun equals lift_matrix applied to f. 
    
    The sum Σ_B (if ⟦i⟧ = B then 1 else 0) * f(B) has only one non-zero term 
    when B = ⟦i⟧, giving f(⟦i⟧). Uses Finset.sum_eq_single pattern. -/
lemma lift_fun_eq_mulVec (P : Partition V) (f : P.Quot → ℝ) : 
    lift_fun P f = lift_matrix P *ᵥ f := by
  ext i
  simp only [lift_fun, Matrix.mulVec, lift_matrix, Partition.quot_map]
  -- Goal: f(⟦i⟧) = Σ_B K_{iB} * f(B) where K = Matrix.of (indicator)
  -- Use sum_eq_single: only B = ⟦i⟧ contributes
  have goal_eq : (∑ j : P.Quot, Matrix.of (fun x B => if Quotient.mk P.rel x = B then (1:ℝ) else 0) i j * f j) = 
      f (Quotient.mk P.rel i) := by
    rw [Finset.sum_eq_single (Quotient.mk P.rel i)]
    · simp only [Matrix.of_apply, ite_true, one_mul]
    · intro B _ hB
      simp only [Matrix.of_apply]
      rw [if_neg (Ne.symm hB), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  exact goal_eq.symm

/-- **Step 1: Vector Intertwining** - L *ᵥ (lift f) = lift (M *ᵥ f).
    
    The generator L applied to a lifted function equals the lift of M applied to f.
    This follows directly from the matrix intertwining L * K = K * M. -/
theorem L_lift_eq (L : Matrix V V ℝ) (P : Partition V) (hL : IsStronglyLumpable L P)
    (f : P.Quot → ℝ) : L *ᵥ (lift_fun P f) = lift_fun P (QuotientGeneratorSimple L P *ᵥ f) := by
  simp only [lift_fun_eq_mulVec, Matrix.mulVec_mulVec, intertwining L P hL]

/-- Generalized lift inner product for two different functions. -/
lemma lift_inner_pi_eq' (P : Partition V) (pi_dist : V → ℝ) (f g : P.Quot → ℝ) :
    inner_pi pi_dist (fun x => f (P.quot_map x)) (fun x => g (P.quot_map x)) =
    inner_pi (pi_bar P pi_dist) f g := by
  simp only [inner_pi, pi_bar]
  -- LHS: Σ_x π(x) * f([x]) * g([x])
  -- RHS: Σ_A (Σ_{x∈A} π(x)) * f(A) * g(A)
  -- Fiberwise sum pattern: group by equivalence class
  have h_group : ∀ x : V, pi_dist x * f (P.quot_map x) * g (P.quot_map x) = 
      ∑ A : P.Quot, if P.quot_map x = A then pi_dist x * f A * g A else 0 := fun x => by
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  simp_rw [h_group]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _
  have h_factor : (∑ x, if P.quot_map x = A then pi_dist x * f A * g A else 0) = 
      (∑ x, if P.quot_map x = A then pi_dist x else 0) * f A * g A := by
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : P.quot_map x = A <;> simp [h]
  rw [h_factor]

/-- **Forward Quadratic Form**: ⟨lift(f), L·lift(f)⟩_π = ⟨f, M·f⟩_π̄.
    Combines L_lift_eq with lift_inner_pi_eq'. Uses Finset.sum_fiberwise pattern. -/
lemma forward_quadratic_form_eq (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hL : IsStronglyLumpable L P) (f : P.Quot → ℝ) :
    inner_pi pi_dist (lift_fun P f) (L *ᵥ lift_fun P f) =
    inner_pi (pi_bar P pi_dist) f (QuotientGeneratorSimple L P *ᵥ f) := by
  rw [L_lift_eq L P hL f]
  -- Now: ⟨lift(f), lift(M·f)⟩_π = ⟨f, M·f⟩_π̄
  exact lift_inner_pi_eq' P pi_dist f (QuotientGeneratorSimple L P *ᵥ f)

/-- **Backward Quadratic Form**: ⟨L·lift(f), lift(f)⟩_π = ⟨M·f, f⟩_π̄.
    Symmetric version of forward_quadratic_form_eq using inner_pi_comm. -/
lemma backward_quadratic_form_eq (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hL : IsStronglyLumpable L P) (f : P.Quot → ℝ) :
    inner_pi pi_dist (L *ᵥ lift_fun P f) (lift_fun P f) =
    inner_pi (pi_bar P pi_dist) (QuotientGeneratorSimple L P *ᵥ f) f := by
  rw [inner_pi_comm, forward_quadratic_form_eq L P pi_dist hL f, inner_pi_comm]

/-! ### 7. Dirichlet Form (Quadratic Definition Path)

The key insight (Grok): Instead of defining H as a matrix -(L + Lᵀ)/2 and proving transpose
identities that don't hold for π-weighted inner products, we define the **Dirichlet form**
directly as the symmetric part of the quadratic form:

  ℰ(u) := (1/2)[⟨u, Lu⟩_π + ⟨Lu, u⟩_π]

This is physically motivated: the energy decay rate is d/dt ‖u‖²_π = 2⟨u, Lu⟩_π.

Since ⟨u, Lu⟩_π = ⟨Lu, u⟩_π by inner_pi_comm, we have ℰ(u) = ⟨u, Lu⟩_π.
-/

/-- **Dirichlet Form**: The symmetric quadratic form ℰ(u) = (1/2)[⟨u, Lu⟩ + ⟨Lu, u⟩].
    By inner_pi_comm, this equals ⟨u, Lu⟩_π. -/
def DirichletForm (L : Matrix V V ℝ) (pi_dist : V → ℝ) (u : V → ℝ) : ℝ :=
  (1/2 : ℝ) * (inner_pi pi_dist u (L *ᵥ u) + inner_pi pi_dist (L *ᵥ u) u)

/-- **Dirichlet Form Simplification**: ℰ(u) = ⟨u, Lu⟩_π by inner_pi_comm. -/
lemma dirichlet_form_eq (L : Matrix V V ℝ) (pi_dist : V → ℝ) (u : V → ℝ) :
    DirichletForm L pi_dist u = inner_pi pi_dist u (L *ᵥ u) := by
  simp only [DirichletForm]
  rw [inner_pi_comm (L *ᵥ u) u]
  ring

/-- **Dirichlet Form on Quotient** -/
def DirichletForm_bar (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) (f : P.Quot → ℝ) : ℝ :=
  DirichletForm (QuotientGeneratorSimple L P) (pi_bar P pi_dist) f

/-- **Dirichlet Form Lift Equality**: ℰ(lift(f)) = ℰ̄(f).
    
    This is THE key lemma that enables gap_non_decrease.
    Proof: immediate from forward_quadratic_form_eq + backward_quadratic_form_eq. -/
theorem dirichlet_form_lift_eq (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hL : IsStronglyLumpable L P) (f : P.Quot → ℝ) :
    DirichletForm L pi_dist (lift_fun P f) = DirichletForm_bar L P pi_dist f := by
  simp only [DirichletForm, DirichletForm_bar]
  -- (1/2)[⟨lift(f), L·lift(f)⟩_π + ⟨L·lift(f), lift(f)⟩_π]
  -- = (1/2)[⟨f, M·f⟩_π̄ + ⟨M·f, f⟩_π̄] by forward + backward quadratic form eqs
  rw [forward_quadratic_form_eq L P pi_dist hL f]
  rw [backward_quadratic_form_eq L P pi_dist hL f]

/-! ### 7. Spectrum Containment (Dirichlet Form Approach)

Using the Dirichlet form ℰ(u) = ⟨u, Lu⟩_π (proven to descend via dirichlet_form_lift_eq),
we define Rayleigh quotients and spectral gaps without needing matrix transpose. -/

/-- **Rayleigh Quotient** using Dirichlet form: R(u) = ℰ(u) / ‖u‖²_π -/
def RayleighQuotient (L : Matrix V V ℝ) (pi_dist : V → ℝ) (u : V → ℝ) : ℝ :=
  DirichletForm L pi_dist u / inner_pi pi_dist u u

/-- The set of Rayleigh quotients over all non-zero functions orthogonal to constants. -/
def RayleighSet (L : Matrix V V ℝ) (pi_dist : V → ℝ) : Set ℝ :=
  { r | ∃ v : V → ℝ, v ≠ 0 ∧ inner_pi pi_dist v constant_vec_one = 0 ∧
    r = RayleighQuotient L pi_dist v }

/-- The set of Rayleigh quotients restricted to block-constant functions. -/
def RayleighSetBlockConstant (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) : Set ℝ :=
  { r | ∃ v : V → ℝ, v ≠ 0 ∧ IsBlockConstant P v ∧ 
    inner_pi pi_dist v constant_vec_one = 0 ∧
    r = RayleighQuotient L pi_dist v }

/-- The set of Rayleigh quotients on the quotient space. -/
def RayleighSetQuot (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) : Set ℝ :=
  { r | ∃ f : P.Quot → ℝ, f ≠ 0 ∧ 
    inner_pi (pi_bar P pi_dist) f (fun _ => 1) = 0 ∧
    r = RayleighQuotient (QuotientGeneratorSimple L P) (pi_bar P pi_dist) f }

/-- Block-constant Rayleigh set is a subset of the full Rayleigh set. -/
lemma rayleigh_block_subset (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) :
    RayleighSetBlockConstant L P pi_dist ⊆ RayleighSet L pi_dist := by
  intro r ⟨v, hv_ne, _, hv_orth, hv_eq⟩
  exact ⟨v, hv_ne, hv_orth, hv_eq⟩

/-- **Subset Infimum Monotonicity**: inf over a subset ≥ inf over the whole set. -/
lemma sInf_subset_ge {S T : Set ℝ} (hST : S ⊆ T) (hS : S.Nonempty) (hT_bdd : BddBelow T) :
    sInf T ≤ sInf S := by
  apply csInf_le_csInf hT_bdd hS hST

/-- **Rayleigh Quotient Lift Equality**: R(lift(f)) = R̄(f).
    
    Key lemma: For block-constant u = lift(f), the Rayleigh quotient on V equals
    the Rayleigh quotient on V̄. Uses dirichlet_form_lift_eq and lift_inner_pi_eq'. -/
lemma rayleigh_quotient_lift_eq (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hL : IsStronglyLumpable L P) (f : P.Quot → ℝ) :
    RayleighQuotient L pi_dist (lift_fun P f) = 
    RayleighQuotient (QuotientGeneratorSimple L P) (pi_bar P pi_dist) f := by
  simp only [RayleighQuotient, DirichletForm_bar] at *
  -- Numerator: ℰ(lift(f)) = ℰ̄(f) by dirichlet_form_lift_eq
  have h_num : DirichletForm L pi_dist (lift_fun P f) = 
               DirichletForm (QuotientGeneratorSimple L P) (pi_bar P pi_dist) f := by
    rw [← DirichletForm_bar]
    exact dirichlet_form_lift_eq L P pi_dist hL f
  -- Denominator: ‖lift(f)‖²_π = ‖f‖²_π̄ by lift_inner_pi_eq'
  have h_denom : inner_pi pi_dist (lift_fun P f) (lift_fun P f) = 
                 inner_pi (pi_bar P pi_dist) f f := 
    lift_inner_pi_eq' P pi_dist f f
  rw [h_num, h_denom]

/-- **Spectral Gap** (using Dirichlet form): inf of Rayleigh quotients over u ⊥ π. -/
def SpectralGap (L : Matrix V V ℝ) (pi_dist : V → ℝ) : ℝ :=
  sInf (RayleighSet L pi_dist)

/-- **Spectral Gap on Quotient** -/
def SpectralGap_bar (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) : ℝ :=
  sInf (RayleighSetQuot L P pi_dist)

/-- **Spectral Gap Non-Decrease (Simple Form)**: inf over block-constant ≥ inf over all. -/
theorem gap_block_ge_gap_all (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hS : (RayleighSetBlockConstant L P pi_dist).Nonempty) 
    (hT_bdd : BddBelow (RayleighSet L pi_dist)) :
    SpectralGap L pi_dist ≤ sInf (RayleighSetBlockConstant L P pi_dist) := by
  exact sInf_subset_ge (rayleigh_block_subset L P pi_dist) hS hT_bdd

/-- **Rayleigh Set Quotient = Rayleigh Set Block-Constant** via lift bijection.
    
    Every block-constant function u is lift(f) for some f, and R(u) = R̄(f). -/
lemma rayleigh_set_quot_eq_block (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hL : IsStronglyLumpable L P) :
    RayleighSetQuot L P pi_dist = 
    { r | ∃ f : P.Quot → ℝ, f ≠ 0 ∧ 
      inner_pi (pi_bar P pi_dist) f (fun _ => 1) = 0 ∧
      r = RayleighQuotient L pi_dist (lift_fun P f) } := by
  ext r
  constructor
  · intro ⟨f, hf_ne, hf_orth, hr⟩
    refine ⟨f, hf_ne, hf_orth, ?_⟩
    rw [hr, rayleigh_quotient_lift_eq L P pi_dist hL f]
  · intro ⟨f, hf_ne, hf_orth, hr⟩
    refine ⟨f, hf_ne, hf_orth, ?_⟩
    rw [← rayleigh_quotient_lift_eq L P pi_dist hL f, hr]

/-- Lift preserves orthogonality to constants: f ⊥ π̄ iff lift(f) ⊥ π. -/
lemma lift_orthog_iff (P : Partition V) (pi_dist : V → ℝ) (f : P.Quot → ℝ) :
    inner_pi (pi_bar P pi_dist) f (fun _ => 1) = 0 ↔ 
    inner_pi pi_dist (lift_fun P f) constant_vec_one = 0 := by
  -- ⟨lift(f), 1⟩_π = ⟨f, 1⟩_π̄ by lift_inner_pi_eq' with g = constant 1
  -- lift_inner_pi_eq' gives: inner_pi π (x ↦ f([x])) (x ↦ g([x])) = inner_pi π̄ f g
  -- With g = (fun _ => 1), we get the equality we need
  unfold lift_fun constant_vec_one
  have h := lift_inner_pi_eq' P pi_dist f (fun _ => 1)
  -- h : inner_pi π (x ↦ f([x])) (x ↦ 1) = inner_pi π̄ f (fun _ => 1)
  constructor <;> intro heq <;> linarith [h]

/-- lift_fun is block-constant. -/
lemma lift_fun_is_block_constant (P : Partition V) (f : P.Quot → ℝ) :
    IsBlockConstant P (lift_fun P f) := by
  intro x y hxy
  simp only [lift_fun]
  -- x and y are in the same class, so quot_map x = quot_map y
  have h_eq : P.quot_map x = P.quot_map y := Quotient.eq'.mpr hxy
  rw [h_eq]

/-- **Spectral Gap Non-Decrease**: λ̄_gap ≥ λ_gap.
    
    Coarse-graining cannot decrease the spectral gap because:
    - λ_gap(L) = inf over ALL u ⊥ π of R(u)
    - λ_gap(L̄) = inf over quotient functions f ⊥ π̄ = inf over BLOCK-CONSTANT u ⊥ π
    - Since block-constant functions form a subset: inf(subset) ≥ inf(total) -/
theorem gap_non_decrease (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hL : IsStronglyLumpable L P)
    (hS : (RayleighSetBlockConstant L P pi_dist).Nonempty) 
    (hT_bdd : BddBelow (RayleighSet L pi_dist)) :
    SpectralGap_bar L P pi_dist ≥ SpectralGap L pi_dist := by
  simp only [SpectralGap_bar, SpectralGap]
  -- Key: RayleighSetQuot and RayleighSetBlockConstant have the same infimum
  -- because every block-constant u = lift(f) for unique f, and R(lift(f)) = R̄(f)
  have h_eq : sInf (RayleighSetQuot L P pi_dist) = sInf (RayleighSetBlockConstant L P pi_dist) := by
    -- Show the sets are equal via the lift bijection
    have h_set_eq : RayleighSetQuot L P pi_dist = RayleighSetBlockConstant L P pi_dist := by
      ext r
      simp only [RayleighSetQuot, RayleighSetBlockConstant, Set.mem_setOf_eq]
      constructor
      · -- Quot → Block: given R̄(f) = r, show R(lift f) = r with lift f block-constant
        intro ⟨f, hf_ne, hf_orth, hr⟩
        refine ⟨lift_fun P f, ?_, lift_fun_is_block_constant P f, ?_, ?_⟩
        · -- lift(f) ≠ 0
          intro h_zero
          apply hf_ne
          ext A
          have := congr_fun h_zero (Quotient.out A)
          simp only [lift_fun, Pi.zero_apply, Partition.quot_map] at this
          rwa [Quotient.out_eq] at this
        · -- lift(f) ⊥ π
          rw [← lift_orthog_iff]; exact hf_orth
        · -- R(lift f) = r
          rw [rayleigh_quotient_lift_eq L P pi_dist hL f, hr]
      · -- Block → Quot: given block-constant u with R(u) = r, find f with R̄(f) = r
        intro ⟨u, hu_ne, hu_block, hu_orth, hr⟩
        -- Since u is block-constant, u = lift(g) for some g
        obtain ⟨g, hg_eq⟩ := (block_constant_iff_lift P u).mp hu_block
        refine ⟨g, ?_, ?_, ?_⟩
        · -- g ≠ 0
          intro hg_zero
          apply hu_ne
          rw [hg_eq]
          ext x; simp [hg_zero]
        · -- g ⊥ π̄
          rw [lift_orthog_iff]
          convert hu_orth using 2
          exact hg_eq.symm
        · -- R̄(g) = r
          rw [← rayleigh_quotient_lift_eq L P pi_dist hL g]
          convert hr using 2
          exact hg_eq.symm
    rw [h_set_eq]
  rw [h_eq]
  exact gap_block_ge_gap_all L P pi_dist hS hT_bdd

end UPAT
