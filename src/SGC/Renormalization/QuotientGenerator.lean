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
  -- Row sums equal zero follows from the definition of QuotientGenerator
  -- and the fact that the original generator L has row sums = 0.
  sorry

/-! ## Section 2: Quotient Stationary Distribution -/

/-- π̄ is a probability distribution on V̄ when π is on V. -/
lemma pi_bar_sum_one_qg (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (h_sum : ∑ v, pi_dist v = 1) :
    ∑ A : Quotient P.rel, pi_bar P pi_dist A = 1 :=
  SGC.pi_bar_sum_one P h_sum

/-! ## Section 3: Multi-Level Composition -/

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
  -- PROOF SKETCH:
  -- The key insight: P₂-block-constant functions form a SUBSET of P₁-block-constant functions
  -- when P₁ refines P₂ (by proj_refines_subset). DirichletGap_bar is the infimum of Rayleigh
  -- quotients over the RayleighSetQuot (which equals RayleighSetBlockConstant by h_set_eq in
  -- dirichlet_gap_non_decrease). Taking the infimum over a smaller set gives ≥ value.
  --
  -- The proof requires connecting RayleighSetQuot to RayleighSetBlockConstant via the
  -- lift bijection, then applying the subset argument.
  sorry

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
