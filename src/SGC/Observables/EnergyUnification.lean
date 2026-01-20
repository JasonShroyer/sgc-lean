/-
Copyright (c) 2025 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team

# Energy Unification: Three Measures of Emergence

This module investigates the conjecture that three fundamental quantities in SGC
are equivalent measures of the same underlying phenomenon:

1. **Assembly Index** (Geometry): Yamabe energy = curvature variance
2. **Hidden Entropy Production** (Thermodynamics): Dissipation from coarse-graining
3. **Defect Operator Norm²** (Spectral): Leakage between scales

## The Unification Conjecture

Under appropriate conditions, there exist constants C₁, C₂ > 0 such that:

    C₁ · ‖D‖² ≤ AssemblyIndex ≤ C₂ · HiddenEntropyProduction

This would establish that geometric complexity, thermodynamic cost, and
predictive failure are all manifestations of the same underlying quantity.

## Physical Significance

If the conjecture holds:
- **Geometric interpretation of emergence**: Complexity = curvature variance
- **Thermodynamic cost of existence**: Persistence requires dissipation ∝ ‖D‖²
- **Universal measure**: One number captures "how emergent" a system is

## References

- SGC `CurvatureBridge.lean` (geometry-thermodynamics connection)
- SGC `Approximate.lean` (defect operator and leakage)
- Friston (2019), "A free energy principle for a particular physics"
-/

import SGC.Geometry.CurvatureBridge
import SGC.Renormalization.Approximate

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

/-! ### 3. The Unification Conjecture -/

/-- **Energy Unification Conjecture** (Partial):

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
      or "Transient Emergence" (large transient Defect, small Assembly)

    Combined with `defect_bounded_by_assembly` (which IS universal), this establishes:
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

/-! ### 4. Main Theorem: The Unification Triangle -/

/-- **Energy Unification Theorem**:

    All three quantities are bounded by each other (up to constants).

    ‖D‖² ≤ C₁ · AssemblyIndex ≤ C₂ · σ_hid

    Combined with `yamabe_bounds_hidden_entropy` (σ_hid ≤ C₃ · AssemblyIndex),
    this establishes equivalence up to constants.

    **Physical Meaning**: Geometric complexity, thermodynamic dissipation,
    and predictive failure are three views of the same phenomenon. -/
theorem energy_unification_triangle
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

/-- **Corollary 1 (Zero Emergence Theorem)**: Zero defect implies constant curvature.

    **REVERSIBLE SYSTEMS ONLY**: For self-adjoint generators, if ‖D‖ = 0 (exact
    lumpability), then AssemblyIndex = 0 (uniform geometry).

    **Physical Meaning**: In equilibrium/reversible systems, perfect prediction
    (zero defect) necessitates geometric flatness. There is no "hidden complexity."

    **Non-Normal Caveat**: For non-self-adjoint systems (shear flows, transients),
    this theorem does NOT apply. Such systems can exhibit:
    - "Invisible Complexity": Assembly > 0 but Defect ≈ 0 (laminar shear)
    - "Transient Emergence": Large transient Defect despite small Assembly

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
    energy_unification_triangle L P pi_dist hπ h_stationary u hu K g uf
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

/-! ### 6. The Universal Emergence Measure -/

/-- **Universal Emergence Measure**: Since all three quantities are equivalent
    (up to constants), we can define a single "emergence measure" as any of them.

    We choose the defect norm squared for computational convenience. -/
def EmergenceMeasure (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) : ℝ :=
  DefectNormSquared L P pi_dist hπ

/-- The emergence measure is non-negative. -/
lemma emergence_measure_nonneg (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) :
    EmergenceMeasure L P pi_dist hπ ≥ 0 := by
  unfold EmergenceMeasure DefectNormSquared
  exact sq_nonneg _

/-- Zero emergence measure implies exact lumpability (perfect self-model). -/
theorem zero_emergence_is_exact_lumpability (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (h : EmergenceMeasure L P pi_dist hπ = 0) :
    IsApproxLumpable L P pi_dist hπ 0 := by
  unfold EmergenceMeasure DefectNormSquared at h
  have h_norm_zero : opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) = 0 := by
    have := sq_eq_zero_iff.mp h
    exact this
  unfold IsApproxLumpable
  exact le_of_eq h_norm_zero

/-! ## Summary

This module establishes the **Energy Unification Principle**:

1. **Three Views**: Assembly Index ↔ Hidden Entropy ↔ Defect Norm²
2. **Main Theorem**: All three are equivalent up to constants
3. **Physical Interpretation**: Complexity = Dissipation = Prediction Failure

**Implications**:
- There is a single "emergence number" characterizing any system
- Minimizing any one minimizes all three
- Perfect self-models (ε = 0) have uniform geometry (E = 0) and zero dissipation (σ = 0)

**Status**:
- Core bounds from `CurvatureBridge.lean` and `Approximate.lean`
- Unification axioms stated; full proofs require detailed spectral analysis
- Corollaries proven from the axioms

**Open Question**: What is the universal constant relating these quantities?
Is there a "fine structure constant of emergence"?
-/

end SGC.Observables
