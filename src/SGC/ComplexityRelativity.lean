/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team

# The Complexity Relativity Theorem

This module states and proves the **Complexity Relativity Theorem**: the
formal assertion that complexity is not an intrinsic property of a Markov
system `L`, but a relational property between `L` and an observer's
partition `P`.

## The Central Claim

For any finite Markov generator `L` with stationary distribution `π`,
complexity is not in `L`. Complexity is in the **observer's partition `P`
relative to `L`**. Two observers with different partitions of the same
underlying system experience different complexities; no observer-independent
"intrinsic complexity" of `L` exists.

This is the SGC analog of two well-known relativity principles:
- In physics: what counts as "information" depends on the choice of
  measurement basis.
- In thermodynamics: what counts as "useful energy" depends on the choice
  of reservoir.

## How It Differs From Kolmogorov Complexity

| | Kolmogorov `K(x)` | SGC `defect_cost L π P` |
|---|---|---|
| Observer | Fixed UTM | The partition `P` |
| Computability | Uncomputable | Computable on finite `V` |
| Range | `[0, ∞)` | `[0, ∞)` with attained min |
| Zero | No string achieves `K = 0` | `trivialPartition` achieves cost `= 0` |
| Thermodynamic interpretation | None | Bounds `σ_hid / γ` ratio |
| Refinement structure | None | Monotone in partition refinement |

The defect cost is the **first observer-relative, computable, and
thermodynamically-charged complexity measure** for finite Markov systems.

## The Theorem's Five Clauses

The capstone theorem `complexity_is_relational` bundles five structural
facts, each composed from existing PROVED theorems:

1. **Non-negativity**: every observer carries complexity ≥ 0.
2. **Trivial-partition zero**: the most-resolved (discrete) observer carries
   exactly zero complexity. The global minimum of `defect_cost` IS zero.
3. **Refinement monotonicity** (the substantive claim): along any chain in
   the partition refinement order, a finer observer has lower complexity on
   the coarse domain. This is the precise mathematical content of "knowing
   the shape of the problem".
4. **Global minimum exists**: at least one partition attains the minimum
   complexity (always the trivial partition; possibly others in the
   reversible / lumpable case).
5. **Reversibility uniqueness**: for detailed-balance `L`, any locally
   optimal partition is globally optimal. For NESS `L`, this uniqueness
   may fail — multiple distinct partitions can carry equally-minimal
   complexity. **The arrow of time creates ambiguity in what constitutes
   an "optimal" coarse-graining.**

## Honest Note on the Trivial-Partition Degeneracy

Because the global minimum of `defect_cost` is attained at the trivial
partition (every state its own block) with value `0`, the literal
**complexity gap** `ComplexityGap(P, P_star) = defect_cost(P) - defect_cost(P_star)`
reduces to `defect_cost(P)` when `P_star` is the global minimum.

This is not a defect of the theorem — it is a **substantive observation**:
the most-resolved observer (the one who sees every state distinctly) always
has zero complexity, regardless of the underlying generator. The interesting
question is not "what is the global minimum?" but rather:

> *"At a given coarseness (number of blocks ≤ K), what is the lowest-cost
> partition, and how far is the observer's current partition from it?"*

This is the **constrained-coarseness** version of the theorem, which
requires defining a "coarseness class" sub-lattice — left as a future
formalization target. The five clauses below state what is unconditionally
provable from the current Lean infrastructure.

## Connection to "To Persist is to Predict"

Combined with the proved `to_persist_is_to_predict` theorem:

  `σ_hid(L, P) < δ  ⟹  ‖D(L, P)‖² < δ / γ`

the Complexity Relativity Theorem gives a precise version of the slogan
*"intelligence is the process of reducing complexity by refining one's
partition toward the optimal"*: any observer whose partition is far from
the optimum pays a thermodynamic tax proportional to the gap squared.

## References

- Kolmogorov (1965) — Three approaches to the quantitative definition
  of information
- Chentsov (1972) — Statistical Decision Rules and Optimal Inference
- SGC (this module) — The Complexity Relativity Theorem (2026-05-25)

## Main Definitions and Theorems

- `ComplexityGap` — the gap between an observer's defect and a reference
- `complexity_gap_nonneg_of_optimal` — gap is non-negative when reference is a global min
- `complexity_gap_eq_zero_iff_eq_cost` — gap vanishes iff defect costs agree
- `complexity_is_relational` — the capstone five-clause theorem (PROVED)
-/

import SGC.Renormalization.OptimalPartition

noncomputable section

namespace SGC.ComplexityRelativity

open SGC.Approximate SGC.Renormalization

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Section 1: The Complexity Gap -/

/-- The **complexity gap** between observer partition `P` and reference
    partition `P_ref`, measured by the difference of their defect costs.

      `ComplexityGap L π h P P_ref := defect_cost L π h P - defect_cost L π h P_ref`

    When `P_ref` is a global minimizer of `defect_cost`, this gap is
    non-negative (Lemma `complexity_gap_nonneg_of_optimal`).

    **Physical interpretation**: the thermodynamic tax an observer with
    partition `P` pays for failing to align with the reference. By
    `to_persist_is_to_predict`, this tax bounds the system's hidden entropy
    production from below.

    **Note on degeneracy**: when `P_ref` is the global minimum, `P_ref` can
    always be taken to be the trivial (discrete) partition, for which
    `defect_cost = 0`. In that case `ComplexityGap = defect_cost(P)`. -/
def ComplexityGap (L : Matrix V V ℝ) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (P P_ref : Partition V) : ℝ :=
  defect_cost L pi_dist hπ P - defect_cost L pi_dist hπ P_ref

/-- **The complexity gap is non-negative when the reference is a global
    minimum**.

    This is the formal content of *"complexity is observer-relative"*:
    an observer's complexity is always at least the minimum achievable, and
    the gap measures the observer's distance from optimality. -/
lemma complexity_gap_nonneg_of_optimal
    (L : Matrix V V ℝ) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (P P_ref : Partition V)
    (h_min : ∀ P' : Partition V, defect_cost L pi_dist hπ P_ref ≤
                                 defect_cost L pi_dist hπ P') :
    0 ≤ ComplexityGap L pi_dist hπ P P_ref := by
  unfold ComplexityGap
  linarith [h_min P]

/-- **Complexity gap vanishes iff defect costs agree**.

    For any reference partition `P_ref`, an observer `P` has zero
    relative complexity precisely when their defect costs match.

    **NESS observation**: for non-reversible `L`, multiple distinct
    partitions may achieve the same defect cost. Zero gap does NOT in
    general imply `P = P_ref` — only equal cost. The "arrow of time
    creates degeneracy in the space of emergent descriptions"
    (see `EmergenceEquivalence.lean`). -/
lemma complexity_gap_eq_zero_iff_eq_cost
    (L : Matrix V V ℝ) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (P P_ref : Partition V) :
    ComplexityGap L pi_dist hπ P P_ref = 0 ↔
    defect_cost L pi_dist hπ P = defect_cost L pi_dist hπ P_ref := by
  unfold ComplexityGap
  exact ⟨fun h => by linarith, fun h => by linarith⟩

/-- **The trivial partition realizes zero complexity**.

    The most-resolved observer (every state its own block) carries zero
    complexity for any underlying generator `L`. This makes the trivial
    partition a universally-available "zero reference" for the complexity
    gap.

    Direct consequence of `trivialPartition_defect_cost_zero`. -/
lemma complexity_gap_relative_to_trivial
    (L : Matrix V V ℝ) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (P : Partition V) :
    ComplexityGap L pi_dist hπ P (trivialPartition V) = defect_cost L pi_dist hπ P := by
  unfold ComplexityGap
  rw [trivialPartition_defect_cost_zero L pi_dist hπ, sub_zero]

/-! ## Section 2: The Capstone Theorem -/

/-- **THE COMPLEXITY RELATIVITY THEOREM**.

    For any finite Markov system `(V, L, π)`, complexity is observer-
    relative in the following precise five-fold sense:

    **(1) Non-negativity** — every observer carries complexity ≥ 0.
       This is the formal counterpart of *"complexity is bounded below"*.

    **(2) Trivial-partition zero** — the most-resolved (discrete) observer
       has zero complexity. The global minimum of the defect cost over the
       entire partition lattice IS `0`, attained at the trivial partition.

    **(3) Refinement monotonicity** — along any chain in the partition
       refinement order, a finer observer has lower complexity on the
       coarse domain. This is the substantive claim of the theorem:
       *"knowing the shape of the problem"* is formalized as having a
       finer partition within the lattice.

    **(4) Global minimum exists** — there is at least one partition
       attaining the minimum complexity. (The trivial partition always
       qualifies; for lumpable `L`, other partitions may tie.)

    **(5) Reversibility uniqueness** — for `L` satisfying detailed
       balance, local optimality implies global optimality. For NESS `L`
       (no detailed balance), this uniqueness may fail: multiple distinct
       partitions can carry equally-minimal complexity. The arrow of time
       creates ambiguity in what constitutes an "optimal" coarse-graining.

    **PROVED** by composition of five PROVED theorems:
    `defect_cost_nonneg`, `trivialPartition_defect_cost_zero`,
    `defect_antitone_on_coarse_domain`, `optimal_partition_exists`,
    `reversible_local_eq_global`. No new axioms, no sorries.

    This is the SGC formalization of the colleague's slogan
    *"complexity is a relationship, not a property"*. -/
theorem complexity_is_relational (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) :
    -- (1) Non-negativity: complexity is bounded below by 0
    (∀ P : Partition V, 0 ≤ defect_cost L pi_dist hπ P) ∧
    -- (2) Trivial-partition zero: most-resolved observer has zero complexity
    (defect_cost L pi_dist hπ (trivialPartition V) = 0) ∧
    -- (3) Refinement monotonicity: finer observers have lower complexity
    --     on the coarse domain
    (∀ P₁ P₂ : Partition V, P₁ ≤ P₂ → ∀ f : V → ℝ, IsBlockConstant P₂ f →
        norm_pi pi_dist (DefectOperator L P₁ pi_dist hπ f) ≤
        norm_pi pi_dist (DefectOperator L P₂ pi_dist hπ f)) ∧
    -- (4) Global minimum exists: there is a complexity-minimizing partition
    (∃ P_star : Partition V,
        ∀ P : Partition V, defect_cost L pi_dist hπ P_star ≤
                           defect_cost L pi_dist hπ P) ∧
    -- (5) Reversibility uniqueness: for detailed-balance L,
    --     local optimality implies global optimality
    (IsReversible L pi_dist →
      sgc_spec_local L pi_dist hπ → sgc_spec_global L pi_dist hπ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (1) defect_cost is non-negative for every partition
    exact defect_cost_nonneg L pi_dist hπ
  · -- (2) trivialPartition has zero defect cost
    exact trivialPartition_defect_cost_zero L pi_dist hπ
  · -- (3) defect is antitone on the coarse domain
    exact defect_antitone_on_coarse_domain L pi_dist hπ
  · -- (4) optimal partition exists
    exact optimal_partition_exists L pi_dist hπ
  · -- (5) reversible local optimality implies global optimality
    exact reversible_local_eq_global L pi_dist hπ

/-! ## Section 3: Corollaries for Conceptual Clarity -/

/-- **Corollary: Complexity vanishes at full resolution**.

    The trivial (discrete) partition — where every state is its own block —
    is a global minimum of the complexity. Stated directly without the
    five-clause bundle. -/
theorem trivial_partition_is_global_min (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) :
    ∀ P : Partition V,
      defect_cost L pi_dist hπ (trivialPartition V) ≤ defect_cost L pi_dist hπ P := by
  intro P
  rw [trivialPartition_defect_cost_zero L pi_dist hπ]
  exact defect_cost_nonneg L pi_dist hπ P

/-- **Corollary: Two observers in the same refinement chain experience
    monotone complexity on the coarser observer's domain**.

    If `P₁ ≤ P₂` (i.e. `P₁` is finer than `P₂`) and `f` is constant on
    `P₂`-blocks, then the finer observer `P₁` sees less leakage on `f`. -/
theorem finer_observer_lower_complexity_on_coarse
    (L : Matrix V V ℝ) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (P₁ P₂ : Partition V) (h_refines : P₁ ≤ P₂)
    (f : V → ℝ) (hf : IsBlockConstant P₂ f) :
    norm_pi pi_dist (DefectOperator L P₁ pi_dist hπ f) ≤
    norm_pi pi_dist (DefectOperator L P₂ pi_dist hπ f) :=
  defect_antitone_on_coarse_domain L pi_dist hπ P₁ P₂ h_refines f hf

/-- **Corollary: Detailed balance implies uniqueness of the emergent
    description**.

    For reversible `L`, the local SGC specification is equivalent to the
    global one. This means there is a unique "most-emergent" coarse-graining
    up to the equivalence relation on partitions.

    For NESS `L` (no detailed balance), this corollary does **not** hold —
    multiple distinct partitions may simultaneously be locally optimal
    without all being globally optimal. -/
theorem reversibility_implies_unique_emergence
    (L : Matrix V V ℝ) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (hrev : IsReversible L pi_dist)
    (h_local : sgc_spec_local L pi_dist hπ) :
    sgc_spec_global L pi_dist hπ :=
  reversible_local_eq_global L pi_dist hπ hrev h_local

/-! ## Section 4: The Constrained-Coarseness Complexity Theorem

The `complexity_is_relational` theorem above states that the GLOBAL minimum
of `defect_cost` is `0`, attained at the trivial (discrete) partition. This
makes the literal "complexity gap" relative to the global minimum vacuous —
it collapses to `defect_cost(P)` itself.

The substantive complexity theorem is the **constrained-coarseness** version:
given a resolution budget `K` (an observer with at most `K` macroscopic
states), the optimal partition within that budget generally has **non-zero**
defect, and the complexity gap measures the observer's distance from that
constrained optimum.

This section formalizes the constrained version. The infrastructure
(`indiscretePartition`, `Partition.blockCount`, `Partition.IsKBounded`,
`optimal_kBounded_partition_exists`) lives in
`SGC.Renormalization.OptimalPartition`.

**Conceptual significance**: this is the public-library analog of the
constrained-coarseness optimization performed by the (proprietary) SGC
runtime engine. The runtime engine implements gradient descent on a
parametric family of `K`-bounded partitions; this theorem certifies that
such a search has a target — a Lean-verified optimum to converge toward.
-/

/-- **THE CONSTRAINED-COARSENESS COMPLEXITY RELATIVITY THEOREM**.

    For any resolution budget `K ≥ 1`, there exists a `K`-bounded partition
    `P_K_star` such that:

    (1) `P_K_star` is itself `K`-bounded (achievable by the observer).

    (2) `P_K_star` minimizes the defect cost **among all `K`-bounded
        partitions** — no observer with resolution `K` can do better.

    (3) Every `K`-bounded observer `P` has a non-negative complexity gap
        relative to `P_K_star`: `defect_cost(P) - defect_cost(P_K_star) ≥ 0`.

    **Unlike the unconstrained `complexity_is_relational` theorem**, the
    minimum value here is generally **non-zero**: for non-lumpable `L` at
    coarseness `K < |V|`, no `K`-block partition achieves zero defect, and
    the complexity gap is a substantive (positive) quantity.

    **PROVED** by direct composition with `optimal_kBounded_partition_exists`.
    Zero new axioms.

    **Physical interpretation**: this is the formal counterpart of the
    *renormalization-group coarse-graining* — the irreducible model error
    when one's resolution budget is finite.

    **Connection to runtime engines**: the proprietary SGC runtime performs
    gradient descent over a parametric family of `K`-bounded partitions.
    This theorem certifies that the search has a well-defined target. -/
theorem constrained_complexity_is_relational
    (L : Matrix V V ℝ) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (K : ℕ) (hK : 1 ≤ K) :
    ∃ P_K_star : Partition V,
      -- (1) The minimizer is K-bounded
      P_K_star.IsKBounded K ∧
      -- (2) The minimizer attains the K-constrained minimum
      (∀ P : Partition V, P.IsKBounded K →
          defect_cost L pi_dist hπ P_K_star ≤ defect_cost L pi_dist hπ P) ∧
      -- (3) The K-constrained complexity gap is non-negative
      (∀ P : Partition V, P.IsKBounded K →
          0 ≤ ComplexityGap L pi_dist hπ P P_K_star) := by
  obtain ⟨P_K_star, h_kbounded, h_min⟩ :=
    optimal_kBounded_partition_exists L pi_dist hπ K hK
  refine ⟨P_K_star, h_kbounded, h_min, ?_⟩
  intro P hP
  unfold ComplexityGap
  linarith [h_min P hP]

/-- **Corollary: a constrained-optimal partition exists**.

    Existence-only form of `constrained_complexity_is_relational`, useful
    when the minimality and non-negativity clauses are not needed. -/
theorem constrained_optimum_exists
    (L : Matrix V V ℝ) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (K : ℕ) (hK : 1 ≤ K) :
    ∃ P_K_star : Partition V, P_K_star.IsKBounded K := by
  obtain ⟨P_K_star, h_kbounded, _, _⟩ :=
    constrained_complexity_is_relational L pi_dist hπ K hK
  exact ⟨P_K_star, h_kbounded⟩

/-- **The constrained minimum is bounded above by the unconstrained
    optimum's defect (when that optimum happens to be K-bounded)**.

    This is the trivial "monotonicity in resolution": more resolution
    (larger K) never makes the constrained minimum larger. Stated as a
    fact about specific witnesses; the universal monotonicity statement
    would require comparing minimizers across different K values, which
    is more delicate. -/
theorem constrained_minimum_le_of_isKBounded
    (L : Matrix V V ℝ) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (K : ℕ) (hK : 1 ≤ K)
    (P_witness : Partition V) (h_witness_kbounded : P_witness.IsKBounded K) :
    ∃ P_K_star : Partition V,
      P_K_star.IsKBounded K ∧
      defect_cost L pi_dist hπ P_K_star ≤ defect_cost L pi_dist hπ P_witness := by
  obtain ⟨P_K_star, h_kbounded, h_min, _⟩ :=
    constrained_complexity_is_relational L pi_dist hπ K hK
  exact ⟨P_K_star, h_kbounded, h_min P_witness h_witness_kbounded⟩

end SGC.ComplexityRelativity
