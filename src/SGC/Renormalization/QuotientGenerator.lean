/-
  # SGC/Renormalization/QuotientGenerator.lean

  The Induced Generator on Quotient Spaces (Multi-Level RG Infrastructure).

  This module provides the machinery for applying generators to quotient spaces,
  enabling multi-level renormalization group composition. The key construction is
  the **quotient generator** L̄ : (V̄ → ℝ) →ₗ[ℝ] (V̄ → ℝ), which is the induced
  dynamics on the coarse-grained state space V̄ = V/P.

  ## Main Definitions
  - `QuotientGenerator`: The induced generator L̄ on V̄ = V/P
  - `QuotientGenerator_welldef`: L̄ is well-defined for lumpable partitions

  ## Main Theorems
  - `dirichlet_gap_composition`: γ(V/P₂) ≥ γ(V/P₁) when P₁ ≤ P₂
  - `composition_monotone`: Multi-level RG composition preserves gap ordering

  ## Significance

  This file fills the gap identified in `OptimalPartition.lean`:
  > "The missing Lean infrastructure is QuotientGenerator.lean — a file that
  >  constructs the induced generator on a quotient type."

  Once this is proved, `composition_monotone` follows from applying
  `dirichlet_gap_non_decrease` to the quotient generators.

  **NOTE**: Uses the **Explicit Weight Pattern** (`pi_dist` as an argument).
-/

import SGC.Renormalization.Lumpability
import SGC.Renormalization.OptimalPartition

noncomputable section

namespace SGC
namespace Renormalization

open Finset Matrix Real NormedSpace

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Section 1: The Quotient Generator -/

/-- The **quotient generator** L̄ induced on V̄ = V/P.

    For a lumpable partition P, the dynamics on the quotient space is given by:
    (L̄ f)(A) = Σ_{B} L̄_{AB} f(B)

    where L̄_{AB} = (1/π̄(A)) Σ_{x∈A, y∈B} π(x) L_{xy}

    This is the π̄-weighted average of transition rates from block A to block B.

    For strongly lumpable partitions, L̄ is a valid Markov generator on V̄. -/
def QuotientGenerator (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) : (Quotient P.rel) → (Quotient P.rel) → ℝ :=
  fun A B =>
    let A_rep := Quotient.out A
    let sum_AB := ∑ x : V, ∑ y : V,
      if P.quot_map x = A ∧ P.quot_map y = B then pi_dist x * L x y else 0
    sum_AB / pi_bar P pi_dist A

/-- The quotient generator is well-defined: does not depend on representative choice. -/
lemma QuotientGenerator_welldef (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (A B : Quotient P.rel) :
    QuotientGenerator L P pi_dist hπ A B =
    (∑ x : V, ∑ y : V, if P.quot_map x = A ∧ P.quot_map y = B then pi_dist x * L x y else 0) /
    pi_bar P pi_dist A := by
  rfl

/-- Row sums of L̄ equal zero (generator property). -/
lemma QuotientGenerator_row_sum_zero (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (hL : ∀ x : V, ∑ y : V, L x y = 0) (A : Quotient P.rel) :
    ∑ B : Quotient P.rel, QuotientGenerator L P pi_dist hπ A B = 0 := by
  simp only [QuotientGenerator]
  -- Σ_B (Σ_{x,y} if [x]=A ∧ [y]=B then π(x)·L(x,y) else 0) / π̄(A) = 0
  -- Factor out the division by π̄(A)
  rw [← Finset.sum_div]
  -- Suffices to show the numerator is 0 (then 0/π̄ = 0)
  suffices h : ∑ B, ∑ x, ∑ y, (if P.quot_map x = A ∧ P.quot_map y = B
      then pi_dist x * L x y else 0) = 0 by
    rw [h, zero_div]
  -- Swap: Σ_B Σ_x Σ_y → Σ_x Σ_y Σ_B
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro x _
  rw [Finset.sum_comm]
  -- For fixed x: Σ_y Σ_B (if [x]=A ∧ [y]=B then π(x)·L(x,y) else 0)
  -- The inner Σ_B collapses: for each y, exactly one B = [y] matches
  by_cases hx : P.quot_map x = A
  · -- x is in block A: Σ_y Σ_B (if [y]=B then π(x)·L(x,y) else 0) = Σ_y π(x)·L(x,y) = π(x)·0
    -- First simplify each inner B-sum: for fixed y, Σ_B (if [x]=A ∧ [y]=B then ...) = π(x)·L(x,y)
    have h_inner : ∀ y : V, ∑ B : Quotient P.rel,
        (if P.quot_map x = A ∧ P.quot_map y = B then pi_dist x * L x y else 0) =
        pi_dist x * L x y := by
      intro y
      simp only [hx, true_and, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    simp only [h_inner]
    -- Now: Σ_y π(x)·L(x,y) = π(x)·Σ_y L(x,y) = π(x)·0 = 0
    rw [← Finset.mul_sum, hL x, mul_zero]
  · -- x is not in block A: all terms are 0
    apply Finset.sum_eq_zero
    intro y _
    apply Finset.sum_eq_zero
    intro B _
    simp [hx]

/-! ## Section 2: Quotient Stationary Distribution -/

/-- π̄ is a probability distribution on V̄ when π is on V. -/
lemma pi_bar_sum_one_qg (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (h_sum : ∑ v, pi_dist v = 1) :
    ∑ A : Quotient P.rel, pi_bar P pi_dist A = 1 :=
  SGC.pi_bar_sum_one P h_sum

/-! ## Section 3: Lift Infrastructure for Block-Constant Functions -/

/-- **Factor a block-constant function through the quotient.**

    If f : V → ℝ is P-block-constant, then f factors uniquely through the quotient:
    f = factor_block_fun P f hf ∘ P.quot_map

    This is the key construction for relating Rayleigh quotients on V to those on V̄. -/
noncomputable def factor_block_fun (P : Partition V) (f : V → ℝ)
    (hf : IsBlockConstant P f) : Quotient P.rel → ℝ :=
  Quotient.lift f (fun a b hab => hf a b hab)

/-- factor_block_fun correctly inverts the quotient map. -/
lemma factor_block_fun_spec (P : Partition V) (f : V → ℝ) (hf : IsBlockConstant P f) (v : V) :
    factor_block_fun P f hf (P.quot_map v) = f v := by
  simp only [factor_block_fun, Partition.quot_map]
  rfl

/-- Nonzero functions lift to nonzero functions on the quotient. -/
lemma factor_block_fun_ne_zero (P : Partition V) (f : V → ℝ) (hf : IsBlockConstant P f)
    (hf_ne : f ≠ 0) : factor_block_fun P f hf ≠ 0 := by
  intro h_eq
  apply hf_ne
  ext v
  have : factor_block_fun P f hf (P.quot_map v) = 0 := by rw [h_eq]; rfl
  rw [← factor_block_fun_spec P f hf v]
  exact this

/-- **Norm equality under factorization.**

    The π-weighted norm on V equals the π̄-weighted norm on V̄ for block-constant functions:
    ⟨f, f⟩_π = ⟨factor f, factor f⟩_{π̄}

    This is because both sums aggregate the same values, just grouped differently. -/
lemma inner_pi_eq_factor_inner (P : Partition V) (pi_dist : V → ℝ)
    (f : V → ℝ) (hf : IsBlockConstant P f) :
    inner_pi pi_dist f f =
    inner_pi (pi_bar P pi_dist) (factor_block_fun P f hf) (factor_block_fun P f hf) := by
  -- LHS: Σ_v π(v) f(v)²
  -- RHS: Σ_A π̄(A) (factor f)(A)² = Σ_A (Σ_{v∈A} π(v)) f(v_A)²
  -- Both aggregate the same terms grouped differently. By factor_block_fun_spec,
  -- (factor f)([v]) = f(v), so the sums are equal after reindexing.
  simp only [inner_pi, pi_bar]
  -- After simp: both sides reduce to sums over v with f(v)² terms
  -- The reindexing from A to v is mechanical but requires sum manipulation
  sorry

/-- **Orthogonality lifts through factorization.**

    If f ⊥ 1 in L²(π), then (factor f) ⊥ 1 in L²(π̄). -/
lemma factor_preserves_orthogonality (P : Partition V) (pi_dist : V → ℝ)
    (f : V → ℝ) (hf : IsBlockConstant P f)
    (h_orth : inner_pi pi_dist f constant_vec_one = 0) :
    inner_pi (pi_bar P pi_dist) (factor_block_fun P f hf) constant_vec_one = 0 := by
  -- Same reindexing argument: Σ_A π̄(A) · 1 = Σ_v π(v) · 1
  simp only [inner_pi, constant_vec_one, mul_one, pi_bar] at h_orth ⊢
  sorry

/-! ## Section 4: Rayleigh Quotient Equivalence -/

/-- Coarsening preserves block-constant Rayleigh sets:
    RayleighSetBlockConstant L P₂ pi_dist ⊆ RayleighSetBlockConstant L P₁ pi_dist
    when P₁ ≤ P₂ (P₁ refines P₂). -/
lemma rayleigh_block_subset_of_refines (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (P₁ P₂ : Partition V) (h : P₁ ≤ P₂) :
    RayleighSetBlockConstant L P₂ pi_dist ⊆ RayleighSetBlockConstant L P₁ pi_dist := by
  intro r ⟨v, hv_ne, hv_block, hv_orth, hv_eq⟩
  exact ⟨v, hv_ne, proj_refines_subset P₁ P₂ h v hv_block, hv_orth, hv_eq⟩

/-- **Dirichlet Gap Composition**: When P₁ refines P₂ (P₁ ≤ P₂), the Dirichlet gap
    is non-decreasing along the chain V → V/P₁ → V/P₂.

    This is the key lemma for multi-level RG: coarsening can only increase the gap.

    The key insight is that P₂-block-constant functions on V form a SUBSET of
    P₁-block-constant functions on V when P₁ refines P₂. Since DirichletGap_bar
    is the infimum of Rayleigh quotients over block-constant functions, taking
    the infimum over a smaller set gives a larger (or equal) value. -/
theorem dirichlet_gap_composition (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v)
    (P₁ P₂ : Partition V) (h_refines : P₁ ≤ P₂)
    (hL₁ : IsStronglyLumpable L P₁) (hL₂ : IsStronglyLumpable L P₂)
    (hS₁ : (RayleighSetBlockConstant L P₁ pi_dist).Nonempty)
    (hS₂ : (RayleighSetBlockConstant L P₂ pi_dist).Nonempty)
    (hT_bdd : BddBelow (RayleighSet L pi_dist)) :
    DirichletGap_bar L P₂ pi_dist ≥ DirichletGap_bar L P₁ pi_dist := by
  -- Step 1: DirichletGap_bar = sInf(RayleighSetQuot) = sInf(RayleighSetBlockConstant)
  -- This equality is proved in rayleigh_set_quot_eq_block via the lift bijection.
  simp only [DirichletGap_bar]
  -- Step 2: RayleighSetQuot = RayleighSetBlockConstant for lumpable partitions
  have h_eq₁ : RayleighSetQuot L P₁ pi_dist = RayleighSetBlockConstant L P₁ pi_dist :=
    rayleigh_set_quot_eq_block_constant L P₁ pi_dist hL₁
  have h_eq₂ : RayleighSetQuot L P₂ pi_dist = RayleighSetBlockConstant L P₂ pi_dist :=
    rayleigh_set_quot_eq_block_constant L P₂ pi_dist hL₂
  rw [h_eq₁, h_eq₂]
  -- Step 3: P₂-block-constant ⊆ P₁-block-constant when P₁ ≤ P₂
  have h_subset := rayleigh_block_subset_of_refines L pi_dist P₁ P₂ h_refines
  -- Step 4: sInf over smaller set ≥ sInf over larger set
  have h_bdd₁ : BddBelow (RayleighSetBlockConstant L P₁ pi_dist) :=
    BddBelow.mono (rayleigh_block_subset L P₁ pi_dist) hT_bdd
  exact sInf_subset_ge h_subset hS₂ h_bdd₁

/-- **Composition Monotonicity**: The hidden entropy production decreases monotonically
    up the RG tower.

    If P₁ ≤ P₂ ≤ ... ≤ Pₖ is a chain of refinements, then:
    - γ(V/P₁) ≤ γ(V/P₂) ≤ ... ≤ γ(V/Pₖ)
    - The spectral gap is non-decreasing under coarse-graining

    This theorem justifies the SGC algorithm's recursive coarse-graining:
    at each level, the effective dynamics has an equal or larger gap,
    meaning the coarse-grained system mixes at least as fast as the original.

    CLASSIFICATION: OPEN — requires additional infrastructure for quotient generators.
    The theorem statement is correct; the proof requires connecting
    dirichlet_gap_composition to the full entropy production framework. -/
theorem composition_monotone (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v)
    (P₁ P₂ : Partition V) (h_refines : P₁ ≤ P₂)
    (hL₁ : IsStronglyLumpable L P₁) (hL₂ : IsStronglyLumpable L P₂)
    (hS₁ : (RayleighSetBlockConstant L P₁ pi_dist).Nonempty)
    (hS₂ : (RayleighSetBlockConstant L P₂ pi_dist).Nonempty)
    (hT_bdd : BddBelow (RayleighSet L pi_dist)) :
    DirichletGap_bar L P₂ pi_dist ≥ DirichletGap_bar L P₁ pi_dist :=
  dirichlet_gap_composition L pi_dist hπ P₁ P₂ h_refines hL₁ hL₂ hS₁ hS₂ hT_bdd

/-! ## Section 4: The Full RG Chain -/

/-- **Dirichlet Gap Chain**: For any chain of refinements, the Dirichlet gap
    is non-decreasing along the chain.

    trivial ≤ P₁ ≤ P₂ ≤ ... ≤ indiscrete

    implies

    γ(V) ≤ γ(V/P₁) ≤ γ(V/P₂) ≤ ... ≤ γ({*}) = ∞

    This is the formalization of "entropy production decreases up the RG tower". -/
theorem dirichlet_gap_chain (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v)
    (P₁ P₂ : Partition V) (h_refines : P₁ ≤ P₂)
    (hL₁ : IsStronglyLumpable L P₁) (hL₂ : IsStronglyLumpable L P₂)
    (hS₁ : (RayleighSetBlockConstant L P₁ pi_dist).Nonempty)
    (hS₂ : (RayleighSetBlockConstant L P₂ pi_dist).Nonempty)
    (hT_bdd : BddBelow (RayleighSet L pi_dist)) :
    DirichletGap_bar L P₂ pi_dist ≥ DirichletGap L pi_dist := by
  calc DirichletGap_bar L P₂ pi_dist
      ≥ DirichletGap_bar L P₁ pi_dist := composition_monotone L pi_dist hπ P₁ P₂ h_refines hL₁ hL₂ hS₁ hS₂ hT_bdd
    _ ≥ DirichletGap L pi_dist := dirichlet_gap_non_decrease L P₁ pi_dist hL₁ hS₁ hT_bdd

end Renormalization
end SGC
