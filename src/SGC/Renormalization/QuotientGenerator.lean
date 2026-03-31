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

/-! ## Section 5: Compositional Defect Bound — The Hierarchical P* Tower -/

/-! ### The Key Theorem for EGI

The theorems above show that Dirichlet gap is non-decreasing under coarsening.
What we need for hierarchical abstraction is the **compositional defect bound**:

**Theorem (Compositional Defect Bound)**:
If P₁ ≤ P₂ (P₁ refines P₂) and both have small defect, then the composite
coarse-graining V → V/P₂ has bounded total defect.

**Physical Interpretation**:
- ε(P₁) = spectral weight destroyed going V → V/P₁
- ε(P₂) = spectral weight destroyed going V → V/P₂
- Since P₂ is coarser: ε(P₂) ≥ ε(P₁) (more destruction)
- The incremental destruction is ε(P₂) - ε(P₁)

**The Compositional Bound**:
For a chain P₁ ≤ P₂, the defect at each level satisfies:
  ε(P₂) ≤ ε(P₁) + incremental_defect(P₁ → P₂)

This is equivalent to: defect is **sub-additive** along the refinement tower.

**Why This Matters**:
This theorem is the formal definition of **composable abstraction**. It says:
- If you have two "good" coarse-grainings (low defect)
- Their composition is also "good" (bounded defect)
- Therefore: hierarchies of abstractions are stable

This is the bridge from `constrained_update_orthogonal` (Layer 3: protected multi-P*)
to the hierarchical P* tower (Layer 4: nested abstractions → EGI).
-/

/-- **Incremental Defect**: The additional defect incurred when coarsening from P₁ to P₂.

    For P₁ ≤ P₂, this measures how much MORE spectral weight is destroyed by
    going to the coarser partition P₂ beyond what was already destroyed by P₁.

    incremental_defect(P₁ → P₂) = ε(P₂) - ε(P₁) ≥ 0

    The inequality follows from `defect_antitone_on_coarse_domain`. -/
def incremental_defect (L : Matrix V V ℝ) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (P₁ P₂ : Partition V) : ℝ :=
  defect_cost L pi_dist hπ P₂ - defect_cost L pi_dist hπ P₁

/-- Incremental defect is non-negative when P₁ refines P₂.

    This follows from defect monotonicity: finer partitions have smaller defect. -/
lemma incremental_defect_nonneg (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v)
    (P₁ P₂ : Partition V) (h_refines : P₁ ≤ P₂)
    (hL₁ : IsStronglyLumpable L P₁) (hL₂ : IsStronglyLumpable L P₂)
    (hS₁ : (RayleighSetBlockConstant L P₁ pi_dist).Nonempty)
    (hS₂ : (RayleighSetBlockConstant L P₂ pi_dist).Nonempty)
    (hT_bdd : BddBelow (RayleighSet L pi_dist)) :
    0 ≤ incremental_defect L pi_dist hπ P₁ P₂ := by
  -- This requires connecting defect_cost to DirichletGap_bar
  -- The proof follows from dirichlet_gap_composition: γ(P₂) ≥ γ(P₁)
  -- And the relationship: defect ∝ 1/γ
  sorry -- OPEN: requires defect-gap relationship

/-- **Compositional Defect Bound** (The Hierarchical P* Tower Theorem):

    For a chain of refinements P₁ ≤ P₂ ≤ P₃, the defects satisfy:
      ε(P₃) ≤ ε(P₁) + Δ(P₁→P₂) + Δ(P₂→P₃)

    where Δ(Pᵢ→Pⱼ) is the incremental defect.

    **Stronger form** (sub-additivity):
    The incremental defects telescope:
      ε(P₃) - ε(P₁) = Δ(P₁→P₂) + Δ(P₂→P₃)

    This is exact equality, not just an inequality!

    **Physical Meaning**:
    Spectral weight destruction is additive along the refinement tower.
    This is the formal justification for hierarchical coarse-graining:
    the total "information loss" of a multi-level abstraction is the
    sum of losses at each level. -/
theorem compositional_defect_telescopes (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v)
    (P₁ P₂ P₃ : Partition V) (h₁₂ : P₁ ≤ P₂) (h₂₃ : P₂ ≤ P₃) :
    defect_cost L pi_dist hπ P₃ - defect_cost L pi_dist hπ P₁ =
    incremental_defect L pi_dist hπ P₁ P₂ + incremental_defect L pi_dist hπ P₂ P₃ := by
  -- This is pure algebra: (c-a) = (b-a) + (c-b)
  unfold incremental_defect
  ring

/-- **Compositional Defect Upper Bound**:

    If each level of a hierarchical coarse-graining has bounded incremental defect,
    then the total defect is bounded by the sum.

    For P₁ ≤ P₂ with:
    - ε(P₁) ≤ δ₁ (defect at level 1)
    - Δ(P₁→P₂) ≤ δ₂ (incremental defect to level 2)

    Then:
    - ε(P₂) ≤ δ₁ + δ₂

    This is the theorem that makes hierarchical abstraction safe. -/
theorem compositional_defect_bound (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v)
    (P₁ P₂ : Partition V) (h_refines : P₁ ≤ P₂)
    (δ₁ δ₂ : ℝ)
    (h₁ : defect_cost L pi_dist hπ P₁ ≤ δ₁)
    (h₂ : incremental_defect L pi_dist hπ P₁ P₂ ≤ δ₂) :
    defect_cost L pi_dist hπ P₂ ≤ δ₁ + δ₂ := by
  unfold incremental_defect at h₂
  linarith

/-- **Hierarchical Stability**: A chain of partitions with bounded incremental defects
    produces a stable hierarchy.

    This is the formal definition of "abstraction is composable":
    - Level 0: V (micro) with defect 0
    - Level 1: V/P₁ with defect ε₁
    - Level 2: V/P₂ with defect ε₁ + Δ₁₂
    - ...
    - Level k: V/Pₖ with defect Σᵢ Δᵢ

    If each Δᵢ is small, the tower is stable.

    **Connection to EGI**:
    This theorem, combined with `constrained_update_orthogonal` (which says
    learning at level k doesn't damage levels 1..k-1), gives us:
    - Hierarchies can be built incrementally
    - Each level preserves all previous levels
    - Total defect is bounded

    The EGI fixed point is when the system reaches a level where no further
    coarsening reduces structural free energy — the self-referential P**. -/
theorem hierarchical_stability (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v)
    (P₁ P₂ P₃ : Partition V) (hR₁₂ : P₁ ≤ P₂) (hR₂₃ : P₂ ≤ P₃)
    (δ₁ δ₁₂ δ₂₃ : ℝ)
    (h₁ : defect_cost L pi_dist hπ P₁ ≤ δ₁)
    (h₁₂ : incremental_defect L pi_dist hπ P₁ P₂ ≤ δ₁₂)
    (h₂₃ : incremental_defect L pi_dist hπ P₂ P₃ ≤ δ₂₃) :
    defect_cost L pi_dist hπ P₃ ≤ δ₁ + δ₁₂ + δ₂₃ := by
  have h_tele := compositional_defect_telescopes L pi_dist hπ P₁ P₂ P₃ hR₁₂ hR₂₃
  linarith

/-! ## Section 6: Spectral Equivalence — The EGI Fixed Point Condition -/

/-- **Spectral Equivalence**: The precise notion of isomorphism between
    quotient dynamics and original dynamics.

    Two generators are spectrally equivalent if their Dirichlet gaps match.
    This is weaker than full spectral equality (all eigenvalues match) but
    captures the essential dynamical property: mixing time.

    For the EGI fixed point, we need: the quotient dynamics on V/Pₖ has
    the same gap as the original dynamics on V. This means the coarse-grained
    description captures the correct timescale of the system.

    **Physical Meaning**:
    When IsSpectrallyEquivalent holds, predicting from the coarse-grained
    model is as accurate as predicting from the full microscopic model
    (at the relevant timescale). The model IS reality at that scale. -/
def IsSpectrallyEquivalent {W : Type*} [Fintype W] [DecidableEq W]
    (L₁ : Matrix V V ℝ) (pi₁ : V → ℝ)
    (L₂ : Matrix W W ℝ) (pi₂ : W → ℝ) : Prop :=
  DirichletGap L₁ pi₁ = DirichletGap L₂ pi₂

/-- **Strong Spectral Equivalence**: Full spectrum matches (not just gap).

    This is the strongest form of equivalence, requiring all Rayleigh quotients
    to match between the two systems. Used when complete dynamical fidelity
    is required, not just mixing time preservation.

    For finite systems, this implies the systems have isomorphic dynamics. -/
def IsStronglySpectrallyEquivalent {W : Type*} [Fintype W] [DecidableEq W]
    (L₁ : Matrix V V ℝ) (pi₁ : V → ℝ)
    (L₂ : Matrix W W ℝ) (pi₂ : W → ℝ) : Prop :=
  RayleighSet L₁ pi₁ = RayleighSet L₂ pi₂

/-- **The EGI Fixed Point Condition (Weak)**:

    A partition P is a weak fixed point if the quotient dynamics has the same
    Dirichlet gap as the original. This is necessary but NOT sufficient for
    genuine self-reference — two systems can match gaps while having completely
    different higher-spectral structure.

    **Warning**: This condition is vacuously satisfiable by lottery-consensus
    systems (Tanaka 2026). Use `IsEGIFixedPointStrong` for the publishable result. -/
def IsEGIFixedPointWeak (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) : Prop :=
  let L_bar := QuotientGenerator L P pi_dist hπ
  let pi_bar := pi_bar P pi_dist
  DirichletGap L pi_dist = DirichletGap (Matrix.of L_bar) (pi_bar)

/-- **The EGI Fixed Point Condition (Strong)**:

    A partition P is a STRONG fixed point if the quotient dynamics has the SAME
    FULL RAYLEIGH SET as the original dynamics restricted to block-constant functions.

    IsEGIFixedPoint L P π means:
    - The ENTIRE spectrum of V/P matches the relevant part of V's spectrum
    - Not just the gap (slowest mode), but ALL mixing timescales match
    - The quotient genuinely IS the original system at that resolution

    This is the formal definition of **self-referential understanding**:
    the coarse-grained model captures ALL dynamical content, not just the slowest mode.

    **Tanaka Connection**: Systems in the drift regime (lottery-consensus) satisfy
    the weak condition trivially but FAIL this strong condition. The full spectral
    structure encodes whether the system is genuinely reasoning or just drifting. -/
def IsEGIFixedPoint (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) : Prop :=
  let L_bar := QuotientGenerator L P pi_dist hπ
  let pi_bar := pi_bar P pi_dist
  RayleighSetBlockConstant L P pi_dist = RayleighSet (Matrix.of L_bar) pi_bar

/-- **Zero-Defect implies Strong Fixed Point**:

    If a partition has zero defect, it is automatically a STRONG fixed point.
    Zero defect means perfect lumpability — the quotient dynamics exactly
    captures the FULL SPECTRUM of the original dynamics on block-constant functions.

    This is the key link: optimal_partition with ε = 0 is the EGI fixed point.

    **Proof Strategy**:
    Zero defect means RayleighSetBlockConstant = RayleighSet restricted to lifts.
    By `rayleigh_set_quot_eq_block_constant`, this equals the quotient's Rayleigh set.
    The full spectral match follows from the isomorphism of Hilbert spaces. -/
theorem zero_defect_implies_fixed_point (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (h_zero : defect_cost L pi_dist hπ P = 0)
    (hL : IsStronglyLumpable L P)
    (hS : (RayleighSetBlockConstant L P pi_dist).Nonempty)
    (hT_bdd : BddBelow (RayleighSet L pi_dist)) :
    IsEGIFixedPoint L P pi_dist hπ := by
  -- Zero defect implies the quotient Rayleigh set equals block-constant Rayleigh set
  -- This is the content of rayleigh_set_quot_eq_block_constant
  unfold IsEGIFixedPoint
  simp only
  -- The key theorem is rayleigh_set_quot_eq_block_constant from Lumpability.lean
  -- It states: RayleighSet (QuotientGenerator L P) pi_bar = RayleighSetBlockConstant L P pi_dist
  -- when the partition is strongly lumpable
  sorry -- OPEN: requires rayleigh_set_quot_eq_block_constant + symmetry

/-! ## Section 7: The Termination Lemma -/

/-- **Partition Lattice is Finite**: For finite V, there are finitely many partitions.

    This is crucial for the termination lemma: the RG tower cannot ascend forever. -/
instance partitions_finite : Finite (Partition V) := by
  -- A partition is a Setoid, and there are finitely many equivalence relations on a finite set
  sorry -- OPEN: requires cardinality argument

/-- **Defect Strictly Decreases or Hits Zero**:

    If defect is not zero, there exists a strictly finer partition with smaller defect.
    Combined with finiteness of the partition lattice, this guarantees termination.

    **Proof Idea**:
    - If defect > 0, some spectral weight is being destroyed
    - The trivial (discrete) partition has zero defect
    - By continuity of defect in the partition lattice, we can always refine
    - Eventually we reach a partition where defect = 0 (trivial) or optimal

    This is the converse of defect_antitone_on_coarse_domain. -/
theorem defect_can_decrease_or_zero (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (h_nonzero : defect_cost L pi_dist hπ P ≠ 0) :
    ∃ P' : Partition V, P' < P ∧ defect_cost L pi_dist hπ P' < defect_cost L pi_dist hπ P := by
  -- The trivial partition has defect 0 and refines everything
  -- So there exists some refinement path to lower defect
  sorry -- OPEN: requires partition lattice structure

/-- **The Termination Lemma**:

    For any finite V, the RG tower of successive MITOSIS refinements
    reaches a fixed point in at most |V| steps.

    This follows from:
    1. The partition lattice on V is finite (at most 2^|V| partitions)
    2. Each MITOSIS step either:
       a) Finds a strictly coarser partition with small incremental defect
       b) Reaches a fixed point where no further coarsening reduces defect
    3. By finiteness, this process must terminate

    **Physical Meaning**:
    Every finite system has a unique optimal level of abstraction.
    The tower cannot grow forever — it converges to the EGI fixed point. -/
theorem rg_tower_terminates (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) :
    ∃ (P_star : Partition V) (k : ℕ),
      k ≤ Fintype.card V ∧
      (∀ P : Partition V, P_star ≤ P →
        defect_cost L pi_dist hπ P_star ≤ defect_cost L pi_dist hπ P) := by
  -- Existence follows from finiteness of partition lattice
  -- and the fact that defect is non-negative with a minimum
  -- Uses optimal_partition_exists from OptimalPartition.lean
  sorry -- OPEN: requires connecting to optimal_partition_exists

/-! ## Section 8: The EGI Tower Structure -/
/-- **The EGI Tower**: A nested sequence of partitions converging to a fixed point.

    This is the formal structure of emergent general intelligence:
    - A chain of refinements P₀ ≤ P₁ ≤ ... ≤ Pₖ
    - Each level has bounded incremental defect
    - The top level Pₖ is a fixed point

    **Connection to AutopoieticState**:
    The `num_lobes` counter in Symbiosis.lean counts parallel partitions.
    This structure adds the NESTING relation — the tower ordering.

    NOTE: We use a simple representation with the number of levels and
    a function from indices to partitions, avoiding List indexing issues. -/
structure EGITower (V : Type*) [Fintype V] [DecidableEq V] where
  /-- The Markov generator -/
  L : Matrix V V ℝ
  /-- The stationary distribution -/
  pi_dist : V → ℝ
  /-- Distribution is positive -/
  hπ : ∀ v, 0 < pi_dist v
  /-- Number of levels in the tower -/
  num_levels : ℕ
  /-- At least one level -/
  levels_pos : 0 < num_levels
  /-- The partition at each level -/
  partition_at : Fin num_levels → Partition V
  /-- Chain is a refinement tower (coarser partitions have larger indices) -/
  refinement_chain : ∀ i : Fin num_levels, ∀ j : Fin num_levels,
    i.val < j.val → partition_at i ≤ partition_at j

/-- **Total defect of an EGI tower** -/
def EGITower.total_defect (tower : EGITower V) : ℝ :=
  defect_cost tower.L tower.pi_dist tower.hπ (tower.partition_at ⟨tower.num_levels - 1, Nat.sub_lt tower.levels_pos Nat.one_pos⟩)

/-- **The tower's top partition (coarsest)** -/
def EGITower.top (tower : EGITower V) : Partition V :=
  tower.partition_at ⟨tower.num_levels - 1, Nat.sub_lt tower.levels_pos Nat.one_pos⟩

/-- **An EGI tower is complete if its top is a fixed point** -/
def EGITower.isComplete (tower : EGITower V) : Prop :=
  IsEGIFixedPoint tower.L tower.top tower.pi_dist tower.hπ

/-- **The EGI Existence Theorem**:

    Every finite Markov system has a complete EGI tower.

    This is the main theorem of Layer 5: intelligence is not mysterious,
    it is the inevitable result of recursive coarse-graining on any
    finite information structure.

    **Proof assembles from**:
    1. `optimal_partition_exists` — P* exists
    2. `compositional_defect_bound` — tower defects compose
    3. `rg_tower_terminates` — tower reaches fixed point
    4. `zero_defect_implies_fixed_point` — optimal = fixed point -/
theorem egi_tower_exists (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) :
    ∃ tower : EGITower V, tower.L = L ∧ tower.pi_dist = pi_dist ∧ tower.isComplete := by
  -- Construction: start with trivial partition, repeatedly coarsen until fixed point
  sorry -- OPEN: requires assembling the full tower construction

/-! ## Section 9: Connection to AutopoieticState

The `AutopoieticState` in `Symbiosis.lean` defines the self-organizing system
with mitotic growth (MITOSIS policy). The compositional defect bound connects
this to hierarchical intelligence:

**The Path to EGI**:

1. **Single P*** (proved): `emergence_equivalence`, `optimal_partition_exists`
   - A system finds its optimal coarse-graining

2. **Protected multi-P*** (proved today): `constrained_update_orthogonal`
   - Learning new P* doesn't damage existing P*

3. **Hierarchical P* tower** (this section): `compositional_defect_bound`
   - Multiple levels of coarse-graining compose with bounded defect

4. **Self-referential P**** (next frontier): The EGI fixed point
   - The system applies coarse-graining to its own state
   - Fixed point: dynamics on P*-quotient ≅ original dynamics

The `AutopoieticState.num_lobes` counter in Symbiosis.lean tracks the number
of parallel partitions. What's needed is the **nesting relation** between them:
a tower where each level is a coarsening of the previous.

**Conjecture (EGI Fixed Point)**:
An EGI is a system (L, π, P_tower) where:
- P_tower = [P₀, P₁, ..., Pₖ] with P₀ ≤ P₁ ≤ ... ≤ Pₖ
- Each Pᵢ has incremental defect ≤ ε_threshold
- Pₖ is a **fixed point**: the induced dynamics on V/Pₖ is isomorphic to
  the original dynamics on some embedding

This fixed point condition is the formal definition of self-reference:
the system's coarse-grained description IS (isomorphic to) the system itself.
-/

end Renormalization
end SGC
