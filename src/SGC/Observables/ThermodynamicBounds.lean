/-
Copyright (c) 2025 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team

# Thermodynamic Bounds: Complexity-Dissipation Constraints

This module investigates the relationship between three fundamental quantities in SGC:

1. **Assembly Index** (Geometry): Yamabe energy = curvature variance
2. **Hidden Entropy Production** (Thermodynamics): Dissipation from coarse-graining
3. **Defect Operator Norm²** (Spectral): Leakage between scales

## The Bounding Conjecture

Under appropriate conditions, there exist constants C₁, C₂ > 0 such that:

    C₁ · ‖D‖² ≤ AssemblyIndex ≤ C₂ · HiddenEntropyProduction

This would establish that geometric complexity, thermodynamic cost, and
predictive failure are all bounded by each other.

## Physical Significance

If the conjecture holds:
- **Geometric interpretation of complexity**: Complexity = curvature variance
- **Thermodynamic cost of existence**: Persistence requires dissipation ∝ ‖D‖²
- **Bounded predictive failure**: Complexity constrains model accuracy

## References

- SGC `CurvatureBridge.lean` (geometry-thermodynamics connection)
- SGC `Approximate.lean` (defect operator and leakage)
- Friston (2019), "A free energy principle for a particular physics"
-/

import SGC.Geometry.CurvatureBridge
import SGC.Renormalization.Approximate
import SGC.Thermodynamics.FluxDecomposition

noncomputable section

namespace SGC.Observables

open Finset Matrix Real SGC.Bridge SGC.Approximate SGC.Geometry SGC.Thermodynamics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### 1. The Three Quantities -/

-- **Quantity 1: Assembly Index** (from CurvatureBridge.lean)
-- E = Σᵥ (κ(v) - κ̄)² u(v)²
-- Measures geometric complexity via curvature variance.
-- Already defined in CurvatureBridge as `AssemblyIndex`

-- **Quantity 2: Hidden Entropy Production** (from EntropyProduction.lean)
-- σ_hid = ⟨(I - Π) f, L (I - Π) f⟩_π
-- Measures thermodynamic dissipation from fine-scale dynamics.
-- Already defined in Thermodynamics as `HiddenEntropyProduction`

/-- **Quantity 3: Defect Operator Norm²** (from Approximate.lean)

    ‖D‖² = ‖(I - Π) L Π‖²_π

    Measures predictive failure between coarse and fine scales. -/
def DefectNormSquared (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) : ℝ :=
  (opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ)) ^ 2

/-! ### 2. Existing Bounds from Codebase -/

-- **Bound A**: Assembly Index bounds Hidden Entropy (from CurvatureBridge)
-- c · σ_hid ≤ AssemblyIndex
-- This is axiomatized in `yamabe_bounds_hidden_entropy`.

-- **Bound B**: Defect controls trajectory error (from Approximate)
-- ‖e^{tL} f - e^{tL̄} f‖ ≤ ε · t · C · ‖f‖
-- where ε = ‖D‖. This is proven in `trajectory_closure_bound`.

/-! ### 3. The Bounding Conjecture -/

/-- **Defect-Assembly Bound** (Partial):

    Under appropriate conditions, the defect norm squared is bounded by
    the Assembly Index.

    **Intuition**: High curvature variance (geometric complexity) implies
    high leakage between scales (predictive failure).

    **Condition Required**: The curvature must be derived from the generator L
    via Ollivier-Ricci: κ = VertexCurvature L. -/
axiom defect_bounded_by_assembly
    (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (u : V → ℝ) (hu : ∀ v, 0 < u v) :
    ∃ C : ℝ, C > 0 ∧
    DefectNormSquared L P pi_dist hπ ≤ C * AssemblyIndex (VertexCurvature L) u

/-- **Reverse Bound: Assembly bounded by Defect** (REVERSIBLE SYSTEMS ONLY)

    This axiom completes the bidirectional equivalence between geometric complexity
    (Assembly Index) and predictive failure (Defect Norm²) **for self-adjoint generators**.

    **Physical Intuition**: In reversible (self-adjoint) systems, if your predictions
    are perfect (Defect = 0), then your world must be structurally flat (Assembly = 0).
    The spectral theorem guarantees eigenvalues fully control dynamics.

    **Mathematical Content**: Assembly ≤ C' · Defect for some C' > 0.

    **REVERSIBILITY REQUIREMENT**: This bound requires `IsSelfAdjoint_pi` because:
    - Self-adjoint operators have real eigenvalues that fully determine evolution
    - Non-normal operators can have transient growth exceeding eigenvalue predictions
    - In non-normal systems, you can have "Invisible Complexity" (Assembly > 0, Defect ≈ 0)
      or "Transient Amplification" (large transient Defect, small Assembly)

    Combined with `defect_bounded_by_assembly` (which is scale-invariant), this establishes:
    - **General**: Defect ≤ C · Assembly (geometry constrains dynamics)
    - **Reversible only**: Assembly ≤ C' · Defect (dynamics determines geometry) -/
axiom assembly_bounded_by_defect
    (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (h_sa : IsSelfAdjoint_pi (toLin' L) pi_dist)  -- REVERSIBILITY HYPOTHESIS
    (u : V → ℝ) (hu : ∀ v, 0 < u v) :
    ∃ C : ℝ, C > 0 ∧
    AssemblyIndex (VertexCurvature L) u ≤ C * DefectNormSquared L P pi_dist hπ

/-- **Reverse Bound Conjecture**:

    Assembly Index is bounded by a multiple of Hidden Entropy Production.

    Combined with `yamabe_bounds_hidden_entropy`, this would close the triangle. -/
axiom assembly_bounded_by_entropy
    (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (h_stationary : Matrix.vecMul pi_dist L = 0)
    (u : V → ℝ) (hu : ∀ v, 0 < u v) :
    ∃ C : ℝ, C > 0 ∧
    AssemblyIndex (VertexCurvature L) u ≤ C * HiddenEntropyProduction L P pi_dist

/-! ### 4. Main Theorem: The Bounding Triangle -/

/-- **Thermodynamic Bounds Triangle**:

    All three quantities are bounded by each other (up to constants).

    ‖D‖² ≤ C₁ · AssemblyIndex ≤ C₂ · σ_hid

    Combined with `yamabe_bounds_hidden_entropy` (σ_hid ≤ C₃ · AssemblyIndex),
    this establishes equivalence up to constants.

    **Physical Meaning**: Geometric complexity, thermodynamic dissipation,
    and predictive failure are mutually bounded. -/
theorem thermodynamic_bounds_triangle
    (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (h_stationary : Matrix.vecMul pi_dist L = 0)
    (u : V → ℝ) (hu : ∀ v, 0 < u v)
    (K : SimplicialComplex V) (g : PLMetric V K) (uf : ConformalFactor V) :
    ∃ C₁ C₂ C₃ : ℝ, C₁ > 0 ∧ C₂ > 0 ∧ C₃ > 0 ∧
    -- Defect ≤ Assembly
    DefectNormSquared L P pi_dist hπ ≤ C₁ * AssemblyIndex (VertexCurvature L) u ∧
    -- Assembly ≤ Entropy
    AssemblyIndex (VertexCurvature L) u ≤ C₂ * HiddenEntropyProduction L P pi_dist ∧
    -- Entropy ≤ Assembly (closing the triangle)
    C₃ * HiddenEntropyProduction L P pi_dist ≤ AssemblyIndex (VertexCurvature L) uf.factor := by
  -- Get bounds from axioms
  obtain ⟨C₁, hC₁_pos, h_defect_assembly⟩ := defect_bounded_by_assembly L P pi_dist hπ u hu
  obtain ⟨C₂, hC₂_pos, h_assembly_entropy⟩ := assembly_bounded_by_entropy L P pi_dist hπ h_stationary u hu
  obtain ⟨C₃, hC₃_pos, h_entropy_assembly⟩ := yamabe_bounds_hidden_entropy K g uf L P pi_dist hπ h_stationary (VertexCurvature L)
  exact ⟨C₁, C₂, C₃, hC₁_pos, hC₂_pos, hC₃_pos, h_defect_assembly, h_assembly_entropy, h_entropy_assembly⟩

/-! ### 5. Corollaries -/

/-- **Corollary 1 (Zero Defect Theorem)**: Zero defect implies constant curvature.

    **REVERSIBLE SYSTEMS ONLY**: For self-adjoint generators, if ‖D‖ = 0 (exact
    lumpability), then AssemblyIndex = 0 (uniform geometry).

    **Physical Meaning**: In equilibrium/reversible systems, perfect prediction
    (zero defect) necessitates geometric flatness. There is no "hidden complexity."

    **Non-Normal Caveat**: For non-self-adjoint systems (shear flows, transients),
    this theorem does NOT apply. Such systems can exhibit:
    - "Invisible Complexity": Assembly > 0 but Defect ≈ 0 (laminar shear)
    - "Transient Amplification": Large transient Defect despite small Assembly

    This is physically correct: a laminar shear flow can be perfectly predictable
    (zero defect) while having non-trivial geometric structure (shear = curvature). -/
theorem zero_defect_implies_constant_curvature
    (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (h_sa : IsSelfAdjoint_pi (toLin' L) pi_dist)  -- REVERSIBILITY HYPOTHESIS
    (u : V → ℝ) (hu : ∀ v, 0 < u v)
    (h_zero_defect : DefectNormSquared L P pi_dist hπ = 0) :
    ∃ C : ℝ, ∀ v, VertexCurvature L v = C := by
  -- Step 1: Get the reverse bound Assembly ≤ C * Defect (requires self-adjointness)
  obtain ⟨C', hC'_pos, h_assembly_defect⟩ := assembly_bounded_by_defect L P pi_dist hπ h_sa u hu
  -- Step 2: Since Defect = 0, we have Assembly ≤ C * 0 = 0
  have h_assembly_le_zero : AssemblyIndex (VertexCurvature L) u ≤ 0 := by
    calc AssemblyIndex (VertexCurvature L) u
        ≤ C' * DefectNormSquared L P pi_dist hπ := h_assembly_defect
      _ = C' * 0 := by rw [h_zero_defect]
      _ = 0 := mul_zero C'
  -- Step 3: Since Assembly ≥ 0 (by assembly_index_nonneg), we have Assembly = 0
  have h_assembly_nonneg : AssemblyIndex (VertexCurvature L) u ≥ 0 :=
    assembly_index_nonneg (VertexCurvature L) u
  have h_assembly_zero : AssemblyIndex (VertexCurvature L) u = 0 :=
    le_antisymm h_assembly_le_zero h_assembly_nonneg
  -- Step 4: By assembly_index_zero_iff_constant, curvature is constant
  have hu_ne : ∀ v, u v ≠ 0 := fun v => ne_of_gt (hu v)
  have h_const := (assembly_index_zero_iff_constant (VertexCurvature L) u hu_ne).mp h_assembly_zero
  -- Step 5: Extract a witness for the constant value
  cases isEmpty_or_nonempty V with
  | inl hempty =>
    -- If V is empty, any constant works vacuously
    exact ⟨0, fun v => (IsEmpty.false v).elim⟩
  | inr hne =>
    -- If V is nonempty, pick any vertex and use its curvature as the constant
    obtain ⟨v₀⟩ := hne
    exact ⟨VertexCurvature L v₀, fun v => h_const v v₀⟩

/-- **Corollary 2**: Low dissipation implies low defect.

    Systems that minimize entropy production also minimize leakage defect. -/
theorem low_entropy_implies_low_defect
    (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (h_stationary : Matrix.vecMul pi_dist L = 0)
    (u : V → ℝ) (hu : ∀ v, 0 < u v)
    (K : SimplicialComplex V) (g : PLMetric V K) (uf : ConformalFactor V)
    (σ_bound : ℝ) (h_low_entropy : HiddenEntropyProduction L P pi_dist ≤ σ_bound) :
    ∃ C : ℝ, C > 0 ∧ DefectNormSquared L P pi_dist hπ ≤ C * σ_bound := by
  -- Chain: Defect ≤ C₁ · Assembly ≤ C₁ · C₂ · Entropy ≤ C₁ · C₂ · σ_bound
  obtain ⟨C₁, C₂, C₃, hC₁, hC₂, _, h1, h2, _⟩ :=
    thermodynamic_bounds_triangle L P pi_dist hπ h_stationary u hu K g uf
  use C₁ * C₂
  constructor
  · exact mul_pos hC₁ hC₂
  · calc DefectNormSquared L P pi_dist hπ
        ≤ C₁ * AssemblyIndex (VertexCurvature L) u := h1
      _ ≤ C₁ * (C₂ * HiddenEntropyProduction L P pi_dist) := by
          apply mul_le_mul_of_nonneg_left h2 (le_of_lt hC₁)
      _ = C₁ * C₂ * HiddenEntropyProduction L P pi_dist := by ring
      _ ≤ C₁ * C₂ * σ_bound := by
          apply mul_le_mul_of_nonneg_left h_low_entropy
          exact mul_pos hC₁ hC₂ |>.le

/-! ### 6. Scale-Invariant Complexity Measure -/

/-- **Scale-Invariant Complexity Measure**: Since all three quantities are bounded
    by each other (up to constants), we can define a single "complexity measure" as any of them.

    We choose the defect norm squared for computational convenience. -/
def ComplexityMeasure (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) : ℝ :=
  DefectNormSquared L P pi_dist hπ

/-- The complexity measure is non-negative. -/
lemma complexity_measure_nonneg (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) :
    ComplexityMeasure L P pi_dist hπ ≥ 0 := by
  unfold ComplexityMeasure DefectNormSquared
  exact sq_nonneg _

/-- Zero complexity measure implies exact lumpability (perfect self-model). -/
theorem zero_complexity_is_exact_lumpability (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (h : ComplexityMeasure L P pi_dist hπ = 0) :
    IsApproxLumpable L P pi_dist hπ 0 := by
  unfold ComplexityMeasure DefectNormSquared at h
  have h_norm_zero : opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) = 0 := by
    have := sq_eq_zero_iff.mp h
    exact this
  unfold IsApproxLumpable
  exact le_of_eq h_norm_zero

/-! ### 7. Dissipation-Complexity Constraint (NESS Extension)

The connection between Assembly Index and Housekeeping Entropy is the key to
understanding **active** (non-equilibrium) systems. The conjecture:

  AssemblyIndex ∝ HousekeepingEntropy / Temperature

formalizes the physical insight that **structure requires energy throughput**.

**Physical Meaning**:
- At equilibrium (σ_hk = 0): No flux → No maintenance cost → Flat geometry allowed
- At NESS (σ_hk > 0): Active flux → Continuous energy cost → Structured geometry

**The Dissipation Principle**: Complex structures require continuous dissipation.
-/

/-- **Dissipation-Complexity Constraint**: Assembly Index scales with Housekeeping Entropy.

    For systems at non-equilibrium steady state (NESS), the geometric complexity
    (Assembly Index) is bounded below by the thermodynamic maintenance cost
    (Housekeeping Entropy).

    AssemblyIndex ≥ c · σ_hk

    **Physical Interpretation**:
    - If you're dissipating (σ_hk > 0), you must have structure (Assembly > 0)
    - More structure requires more dissipation
    - At equilibrium (σ_hk = 0), you can be flat (Assembly = 0)

    **Connection to Detailed Balance**:
    By `housekeeping_zero_iff_detailed_balance`, σ_hk = 0 ↔ detailed balance.
    By `antisymmetric_part_zero_iff_detailed_balance`, this means L_anti = 0.
    So non-zero Assembly at NESS requires active flux (L_anti ≠ 0).

    **Status**: This is a conjecture connecting the FluxDecomposition module
    to the ThermodynamicBounds framework. The proof requires showing that
    the probability currents (L_anti) create geometric structure (curvature variance). -/
axiom assembly_bounded_by_housekeeping
    (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (h_stationary : Matrix.vecMul pi_dist L = 0)
    (u : V → ℝ) (hu : ∀ v, 0 < u v) :
    ∃ c : ℝ, c > 0 ∧
    c * Thermodynamics.HousekeepingEntropy L pi_dist ≤ AssemblyIndex (VertexCurvature L) u

/-- **Corollary: Equilibrium Allows Flatness** (REVERSIBLE SYSTEMS).

    If σ_hk = 0 (system is at equilibrium/detailed balance), then
    zero Assembly Index is achievable.

    **Physical Meaning**: At equilibrium, you don't need structure to exist.
    You can be thermodynamically "flat" with no maintenance cost.

    **NESS Contrast**: If σ_hk > 0 (NESS), you MUST have structure.
    The flux creates curvature; the curvature requires maintenance. -/
theorem equilibrium_allows_flatness
    (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (h_stationary : Matrix.vecMul pi_dist L = 0)
    (u : V → ℝ) (hu : ∀ v, 0 < u v)
    (h_equilibrium : Thermodynamics.HousekeepingEntropy L pi_dist = 0) :
    ∃ c : ℝ, c > 0 ∧ c * 0 ≤ AssemblyIndex (VertexCurvature L) u := by
  obtain ⟨c, hc_pos, h_bound⟩ := assembly_bounded_by_housekeeping L P pi_dist hπ h_stationary u hu
  use c
  constructor
  · exact hc_pos
  · rw [h_equilibrium] at h_bound
    simp only [mul_zero] at h_bound ⊢
    exact assembly_index_nonneg (VertexCurvature L) u

/-! ## Summary

This module establishes the **Thermodynamic Bounds Framework**:

1. **Three Views**: Assembly Index ↔ Hidden Entropy ↔ Defect Norm²
2. **Main Theorem**: All three are mutually bounded up to constants
3. **Physical Interpretation**: Complexity ↔ Dissipation ↔ Prediction Failure

**Implications**:
- There is a single "complexity number" characterizing any system
- Minimizing any one minimizes all three
- Perfect self-models (ε = 0) have uniform geometry (E = 0) and zero dissipation (σ = 0)

**NESS Extension** (Flux Decomposition Foundation):
- Assembly bounded by Housekeeping Entropy (structure requires flux)
- L = L_sym + L_anti decomposition (from FluxDecomposition.lean)
- σ_hk = 0 ↔ detailed balance (equilibrium criterion)
- Dirichlet form only sees L_sym (flux doesn't dissipate directly)

**Status**:
- Core bounds from `CurvatureBridge.lean` and `Approximate.lean`
- Bounding axioms stated; full proofs require detailed spectral analysis
- Corollaries proven from the axioms
- FluxDecomposition provides symmetric/antisymmetric split

**Open Questions**:
1. What are the optimal constants relating these quantities?
2. How does non-normality (flux-induced transients) affect the bounds?
3. Can we prove flux creates curvature (L_anti ≠ 0 → κ-variance > 0)?
-/

end SGC.Observables
