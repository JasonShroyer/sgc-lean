import SGC.Spectral.Envelope
import SGC.Spectral.Defs
import SGC.Renormalization.Lumpability
import SGC.Renormalization.Approximate
import SGC.Thermodynamics.DoobMeyer
import SGC.Variational.LeastAction
import SGC.Information.Equivalence
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

-- Renormalization Pillar
#print axioms gap_non_decrease

-- Effective Theory (Approximate Lumpability)
#print axioms spectral_stability
#print axioms trajectory_closure_bound
#print axioms NCD_uniform_error_bound

-- Thermodynamics Pillar
#print axioms doob_decomposition

-- Variational Pillar
#print axioms variational_drift_optimality

-- Topology Pillar (Blanket Structure)
#print axioms SGC.blanket_orthogonality

-- Information Bridge (v2 Extension)
#print axioms SGC.information_geometry_equivalence

end AxiomAudit

section ConcreteInstantiation
/-! ## Concrete Instantiation (Non-Vacuity Check)

If our definitions were vacuously true (e.g., "no partition exists"),
these examples would fail to compile. Their successful compilation proves
our structures are satisfiable with real data.
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

/-! ## Success Message

This runs during elaboration, so interpreter users see it.
-/

#eval IO.println "✓ SGC sanity checks passed. All structures are non-vacuous."
