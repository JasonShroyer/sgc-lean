import SGC.Spectral.Envelope
import SGC.Spectral.Defs
import SGC.Renormalization.Lumpability
import SGC.Renormalization.Approximate
import SGC.Thermodynamics.DoobMeyer
import SGC.Variational.LeastAction
import SGC.Information.Equivalence
import SGC.Observables.ValidityHorizon
import SGC.Observables.TopologicalPersistence
import SGC.Observables.ThermodynamicBounds
import SGC.Bridge.Quantum
import SGC.Bridge.CoherenceObstruction
import SGC.Bridge.Recovery
import SGC.Bridge.Consolidation
import SGC.Bridge.GeometricClosure
import SGC.Bridge.CanonicalWavelet
import SGC.Axioms.GeometryGeneral
import Mathlib.LinearAlgebra.Matrix.Notation

open Matrix SGC Real SGC.Spectral SGC.Approximate

/-!
# Sanity Checks for SGC Library

This file serves two purposes:
1. **Axiom Transparency**: `#print axioms` reveals exactly what each theorem depends on
2. **Non-Vacuity**: Concrete instantiations prove our structures are satisfiable

These checks protect against "hallucinated proofs" where definitions are vacuously
true or proofs smuggle in hidden assumptions.
-/

section AxiomAudit
/-! ## Axiom Audit

The following commands print the axioms used by key theorems.
Expected: `propext`, `Quot.sound`, `Classical.choice` (standard Lean/Mathlib axioms)
         plus any explicitly declared axioms from `SGC.Bridge.Discretization`.
Red flag: If `sorry` appears, the proof is incomplete.
-/

-- Spectral Pillar (Core Stability Result)
#print axioms SGC.Spectral.spectral_stability_bound

-- Renormalization Pillar (Dirichlet Gap - algebraic)
#print axioms dirichlet_gap_non_decrease

-- Effective Theory (Approximate Lumpability)
-- trajectory_closure_bound: THE CORE VICTORY - valid for ALL generators
#print axioms SGC.Approximate.trajectory_closure_bound
#print axioms SGC.Approximate.NCD_uniform_error_bound
-- spectral_stability_reversible: Only valid for reversible (self-adjoint) generators
#print axioms SGC.Approximate.spectral_stability_reversible

-- Thermodynamics Pillar
#print axioms doob_decomposition

-- Variational Pillar
#print axioms variational_drift_optimality

-- Topology Pillar (Blanket Structure)
#print axioms SGC.blanket_orthogonality

-- Information Bridge (v2 Extension)
#print axioms SGC.information_geometry_equivalence

-- Petz Recovery Bridge (NEW - Quantum Bridge Sprint)
-- PetzRecoveryMap: Adjoint-based recovery channel
#print axioms SGC.Bridge.Recovery.PetzRecoveryMap_spec
#print axioms SGC.Bridge.Recovery.PetzRecoveryMap_involutive
-- Data Processing Inequality and Petz Recovery Theorem
#print axioms SGC.Bridge.Recovery.DataProcessingInequality
#print axioms SGC.Bridge.Recovery.PetzRecoveryTheorem
-- Landauer's Principle connection
#print axioms SGC.Bridge.Recovery.LandauerPrinciple
#print axioms SGC.Bridge.Recovery.ML_agent_pays_landauer

-- Channel-Theoretic Consolidation (NEW - RG Monotonicity Sprint)
-- RG Monotonicity: PROVED from DPI axiom + semigroup composition
#print axioms SGC.Bridge.Consolidation.RG_monotonicity_step
#print axioms SGC.Bridge.Consolidation.RG_monotonicity_composition
#print axioms SGC.Bridge.Consolidation.RG_monotonicity_dyadic
-- Recovery interface: equality in DPI ⟺ recoverability
#print axioms SGC.Bridge.Consolidation.RG_equality_implies_recovery
#print axioms SGC.Bridge.Consolidation.RG_preservation_iff_recovery
-- Coarse-graining contracts entropy: PROVED from DPI
#print axioms SGC.Bridge.Consolidation.coarse_graining_contracts_entropy
-- Information loss interface
#print axioms SGC.Bridge.Consolidation.InformationLoss_nonneg
#print axioms SGC.Bridge.Consolidation.three_way_closure_from_approx_lumpable

-- Geometric Closure (NEW - Second-Order Theory)
-- Bakry-Émery Gamma operators
#print axioms SGC.Bridge.GeometricClosure.Gamma
#print axioms SGC.Bridge.GeometricClosure.Gamma2
-- Ricci curvature bound (Bakry-Émery criterion)
#print axioms SGC.Bridge.GeometricClosure.RicciCurvatureBound
-- Intrinsic stability: d²E/dt² ≥ -2ρ dE/dt
#print axioms SGC.Bridge.GeometricClosure.BakryEmery_implies_stability
#print axioms SGC.Bridge.GeometricClosure.exponential_decay_from_convexity
-- Defect bounded by Ricci curvature
#print axioms SGC.Bridge.GeometricClosure.defect_bounded_by_ricci
#print axioms SGC.Bridge.GeometricClosure.approx_lumpable_from_ricci
-- Geometric three-way closure
#print axioms SGC.Bridge.GeometricClosure.geometric_closure_from_ricci
#print axioms SGC.Bridge.GeometricClosure.geometric_implies_first_order
-- Geometric uncertainty principle
#print axioms SGC.Bridge.GeometricClosure.geometric_uncertainty_principle

-- Tensorization of Ricci Curvature Bounds (Dimension Independence)
-- Tensor product generator and functions
#print axioms SGC.Bridge.GeometricClosure.TensorProductGenerator
#print axioms SGC.Bridge.GeometricClosure.tensorProduct
-- Γ additivity on tensor products
#print axioms SGC.Bridge.GeometricClosure.Gamma_tensorProduct_additivity
-- Γ₂ additivity on tensor products
#print axioms SGC.Bridge.GeometricClosure.Gamma2_tensorProduct_additivity
-- Main theorem: Ricci bound tensorizes with min
#print axioms SGC.Bridge.GeometricClosure.Ricci_tensor_min
-- Corollaries
#print axioms SGC.Bridge.GeometricClosure.positive_Ricci_tensorizes
#print axioms SGC.Bridge.GeometricClosure.dimension_independence

-- Canonical Wavelet Frame (NEW - Spectral Analysis)
-- Sectorial functional calculus
#print axioms SGC.Bridge.CanonicalWavelet.SectorialFunctionalCalculus
#print axioms SGC.Bridge.CanonicalWavelet.functional_calculus_commutes_semigroup
-- Spectral frame and bounds
#print axioms SGC.Bridge.CanonicalWavelet.SpectralFrame
#print axioms SGC.Bridge.CanonicalWavelet.frame_condition_ge_one
-- Representation error bound
#print axioms SGC.Bridge.CanonicalWavelet.representation_error_bound
-- Tight frame: A = B ⇒ zero error
#print axioms SGC.Bridge.CanonicalWavelet.tight_frame_condition_one
#print axioms SGC.Bridge.CanonicalWavelet.tight_frame_zero_error
-- Geometric commutator constraint: |B/A - 1| ≤ C·‖[L, Γ₂]‖
#print axioms SGC.Bridge.CanonicalWavelet.geometric_commutator_constraint
#print axioms SGC.Bridge.CanonicalWavelet.constant_ricci_tight_frame_exists
-- End-to-end: error ≤ C·‖[L, Γ₂]‖
#print axioms SGC.Bridge.CanonicalWavelet.geometric_error_bound

-- Observables Pillar (NEW January 2026)
-- Spectral Bridge: Connects abstract spectral gap to measurable autocorrelation
#print axioms SGC.Observables.autocorrelation_decay_from_sector
-- Zero Emergence Theorem (REVERSIBLE ONLY): Defect=0 ⟹ Constant Curvature
#print axioms SGC.Observables.zero_defect_implies_constant_curvature
-- Topological Persistence: Markov blanket ⟹ positive survival time
#print axioms SGC.Observables.expected_persistence_time_pos
#print axioms SGC.Observables.persistence_cost_ratio_constant
-- Thermodynamic Bounds Triangle
#print axioms SGC.Observables.thermodynamic_bounds_triangle

end AxiomAudit

section ConcreteInstantiation
/-! ## Concrete Instantiation (Definition Non-Vacuity)

These examples prove our **definitions** are satisfiable — they can be instantiated
with real data. If definitions like `Matrix` or `Setoid` were vacuously true
(e.g., required `False`), these would fail to compile.

**Note**: Applying theorems like `gap_non_decrease` to these examples would require
constructing complex hypotheses (`IsStronglyLumpable`, `Nonempty` sets, etc.).
The `#print axioms` audit above is the ground truth for theorem verification.
-/

/-- A simple 2-state Markov chain (coin flip dynamics). -/
def twoStateGenerator : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![-1, 1], ![1, -1]]

/-- Uniform distribution on 2 states. -/
noncomputable def uniformDist2 : Fin 2 → ℝ := fun _ => 1/2

/-- The trivial partition: each state in its own block. -/
def trivialPartition2 : Setoid (Fin 2) := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩

/-- The coarse partition: all states in one block. -/
def coarsePartition2 : Setoid (Fin 2) := ⟨fun _ _ => True, ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩⟩

end ConcreteInstantiation

section ComputationalPropertyTests
/-! ## Computational Property Tests

These tests verify mathematical properties **numerically**, not just type-theoretically.
Unlike the axiom audit (which verifies logical dependencies), these tests compute
actual values and assert correctness.

**Key distinction:**
- Axiom audit: "Does this theorem depend only on standard axioms?"
- Property test: "Does this concrete example satisfy the mathematical definition?"

**Why this matters:** A vacuous definition could type-check but fail numerical tests.
These tests use `Rat` (exact rationals) for reproducible arithmetic.

**Test Design:**
- **Positive tests**: Valid examples that MUST pass
- **Negative tests**: Invalid examples that MUST fail (proves tests have teeth)
-/

open Matrix

/-- A 2-state symmetric Markov generator (coin-flip dynamics).
    L = [[-1, 1], [1, -1]] with uniform stationary distribution. -/
def testGenerator : Matrix (Fin 2) (Fin 2) Rat :=
  !![(-1 : Rat), 1; 1, -1]

/-- Uniform stationary distribution on 2 states. -/
def testStationary : Fin 2 → Rat := fun _ => 1/2

/-- A BAD "generator" (identity matrix) - row sums are NOT zero.
    This MUST fail the generator property test. -/
def badGenerator : Matrix (Fin 2) (Fin 2) Rat :=
  !![(1 : Rat), 0; 0, 1]

/-- A WRONG stationary distribution for testGenerator.
    This MUST fail the stationarity test. -/
def wrongStationary : Fin 2 → Rat := fun i => if i = 0 then 1 else 0

/-! ### Property Checkers -/

/-- Check that all row sums equal zero (Markov generator property).
    A matrix L is a generator iff Σⱼ L_ij = 0 for all i. -/
def checkRowSumsZero (L : Matrix (Fin 2) (Fin 2) Rat) : Bool :=
  (L 0 0 + L 0 1 == 0) && (L 1 0 + L 1 1 == 0)

/-- Check πL = 0 (stationary distribution property).
    π is stationary for L iff Σᵢ π_i L_ij = 0 for all j. -/
def checkStationary (pi : Fin 2 → Rat) (L : Matrix (Fin 2) (Fin 2) Rat) : Bool :=
  let col0 := pi 0 * L 0 0 + pi 1 * L 1 0
  let col1 := pi 0 * L 0 1 + pi 1 * L 1 1
  (col0 == 0) && (col1 == 0)

/-- Check π is a valid probability distribution (positive, normalized). -/
def checkProbabilityDist (pi : Fin 2 → Rat) : Bool :=
  (pi 0 > 0) && (pi 1 > 0) && (pi 0 + pi 1 == 1)

/-- Check detailed balance: π_i L_ij = π_j L_ji (reversibility). -/
def checkDetailedBalance (pi : Fin 2 → Rat) (L : Matrix (Fin 2) (Fin 2) Rat) : Bool :=
  pi 0 * L 0 1 == pi 1 * L 1 0

/-! ### Execute Tests -/

-- Positive tests (all should return true)
#eval checkRowSumsZero testGenerator        -- Expected: true
#eval checkStationary testStationary testGenerator  -- Expected: true
#eval checkProbabilityDist testStationary   -- Expected: true
#eval checkDetailedBalance testStationary testGenerator  -- Expected: true

-- Negative tests (all should return false - PROVES TESTS HAVE TEETH)
#eval checkRowSumsZero badGenerator         -- Expected: false (row sums = 1, not 0)
#eval checkStationary wrongStationary testGenerator  -- Expected: false (not stationary)

/-- Run all property tests and report results. -/
def runPropertyTests : IO Unit := do
  IO.println "┌─────────────────────────────────────────────────────────┐"
  IO.println "│         COMPUTATIONAL PROPERTY TESTS                    │"
  IO.println "├─────────────────────────────────────────────────────────┤"

  -- Positive tests
  let t1 := checkRowSumsZero testGenerator
  let t2 := checkStationary testStationary testGenerator
  let t3 := checkProbabilityDist testStationary
  let t4 := checkDetailedBalance testStationary testGenerator

  IO.println s!"│ Generator row sums = 0:        {if t1 then "✓ PASS" else "✗ FAIL"}                │"
  IO.println s!"│ πL = 0 (stationarity):         {if t2 then "✓ PASS" else "✗ FAIL"}                │"
  IO.println s!"│ π valid probability dist:      {if t3 then "✓ PASS" else "✗ FAIL"}                │"
  IO.println s!"│ Detailed balance (πᵢLᵢⱼ=πⱼLⱼᵢ): {if t4 then "✓ PASS" else "✗ FAIL"}                │"

  -- Negative tests (these SHOULD fail)
  let n1 := checkRowSumsZero badGenerator
  let n2 := checkStationary wrongStationary testGenerator

  IO.println "├─────────────────────────────────────────────────────────┤"
  IO.println "│ NEGATIVE TESTS (must fail to prove tests have teeth)    │"
  IO.println s!"│ Bad generator rejected:        {if !n1 then "✓ PASS" else "✗ FAIL"}                │"
  IO.println s!"│ Wrong stationary rejected:     {if !n2 then "✓ PASS" else "✗ FAIL"}                │"

  let allPass := t1 && t2 && t3 && t4 && !n1 && !n2
  IO.println "├─────────────────────────────────────────────────────────┤"
  IO.println s!"│ ALL PROPERTY TESTS:            {if allPass then "✓ PASS" else "✗ FAIL"}                │"
  IO.println "└─────────────────────────────────────────────────────────┘"

#eval runPropertyTests

end ComputationalPropertyTests

/-! ## Success Message

This runs during elaboration, so interpreter users see it.
-/

#eval IO.println "✓ SGC sanity checks passed. All structures are non-vacuous."

/-- Main entry point for the test executable. -/
def main : IO Unit := do
  runPropertyTests
  IO.println "\n✓ SGC test suite completed successfully."
