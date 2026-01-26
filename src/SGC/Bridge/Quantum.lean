/-
Copyright (c) 2026 Jason Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Shroyer
-/
import SGC.Axioms.GeometryGeneral
import SGC.Spectral.Core.Assumptions
import SGC.Renormalization.Approximate

/-!
# Quantum Bridge: Classical-Quantum Dictionary

This file establishes the formal correspondence between classical Markov chain
theory and quantum information theory. The key insight is that lumpability
(coarse-graining that preserves Markov structure) corresponds to quantum error
correction (encoding that preserves quantum information).

## Main Correspondences

| Classical (Markov)              | Quantum                              |
|---------------------------------|--------------------------------------|
| Probability distribution π      | Density matrix ρ                     |
| Stochastic matrix P             | Quantum channel (CPTP map) Φ         |
| Generator L (= P - I)           | Lindbladian ℒ                        |
| Partition of state space        | Projection onto code subspace        |
| Lumpability (exact)             | Knill-Laflamme conditions (ε = 0)    |
| Approximate lumpability         | Approximate QEC                      |
| Spectral gap γ                  | Lindbladian gap γ_L                  |
| Mixing time τ_mix               | Decoherence time T_2                 |

## References

* [Knill-Laflamme 1997] Theory of quantum error-correcting codes
* [Lindblad 1976] On the generators of quantum dynamical semigroups
* [Kempe et al. 2001] Quantum random walks

-/

noncomputable section

namespace SGC
namespace Bridge
namespace Quantum

open Finset
open SGC.Axioms.GeometryGeneral
open SGC.Spectral
open SGC.Approximate

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-! ## Classical Objects

We first recall the classical objects from SGC that will be bridged to quantum. -/

/-- A classical state is a probability distribution over V. -/
structure ClassicalState (V : Type*) [Fintype V] where
  dist : V → ℝ
  nonneg : ∀ v, 0 ≤ dist v
  sum_one : ∑ v, dist v = 1

/-- A classical generator is a rate matrix (rows sum to 0, off-diagonal nonneg). -/
structure ClassicalGenerator (V : Type*) [Fintype V] where
  L : Matrix V V ℝ
  row_sum_zero : ∀ i, ∑ j, L i j = 0
  off_diag_nonneg : ∀ i j, i ≠ j → 0 ≤ L i j

/-! ## Quantum Objects

Quantum objects use complex scalars and the Hermitian inner product from GeometryGeneral. -/

/-- A quantum state (density matrix) is a positive semidefinite operator with trace 1.
    We use ℂ as the scalar field for quantum mechanics. -/
abbrev QuantumState (V : Type*) [Fintype V] [DecidableEq V] (pi_dist : V → ℝ) :=
  { ρ : (V → ℂ) →ₗ[ℂ] (V → ℂ) // IsDensityMatrix pi_dist ρ }

/-- A Lindbladian is the generator of a quantum dynamical semigroup.
    It takes the form ℒ(ρ) = -i[H,ρ] + Σ_k (L_k ρ L_k† - ½{L_k†L_k, ρ})
    where H is Hermitian and L_k are jump operators. -/
structure Lindbladian (V : Type*) [Fintype V] [DecidableEq V] (pi_dist : V → ℝ) where
  /-- The superoperator acting on density matrices -/
  superop : ((V → ℂ) →ₗ[ℂ] (V → ℂ)) →ₗ[ℂ] ((V → ℂ) →ₗ[ℂ] (V → ℂ))
  /-- Trace-preserving: Tr(ℒ(ρ)) = 0 for all ρ -/
  trace_preserving : ∀ ρ, trace_pi pi_dist (superop ρ) = 0
  /-- Complete positivity (CPTP property, axiomatized) -/
  cptp : True  -- Placeholder; full CPTP requires Kraus representation

/-! ## Code Subspace and Projections

The quantum analog of a partition is a projection onto a code subspace.
Error correction works by projecting back onto this subspace. -/

/-- A code subspace is defined by a projection operator. -/
structure CodeSubspace (V : Type*) [Fintype V] [DecidableEq V] (pi_dist : V → ℝ) where
  /-- The projector onto the code subspace -/
  proj : (V → ℂ) →ₗ[ℂ] (V → ℂ)
  /-- Projector is self-adjoint -/
  self_adjoint : IsSelfAdjoint_pi pi_dist proj
  /-- Projector satisfies P² = P -/
  idempotent : proj ∘ₗ proj = proj

/-! ## Knill-Laflamme Conditions

The Knill-Laflamme conditions characterize when a code can perfectly correct
a set of errors. This is the quantum analog of exact lumpability. -/

/-- Error operators are the quantum analog of "leakage" in approximate lumpability. -/
structure ErrorOperators (V : Type*) [Fintype V] [DecidableEq V] (n : ℕ) where
  /-- Set of error operators {E_k} -/
  errors : Fin n → ((V → ℂ) →ₗ[ℂ] (V → ℂ))

/-- The Knill-Laflamme conditions: P E_i† E_j P = α_ij P for some scalars α_ij.
    When satisfied, errors can be perfectly corrected.

    This is the quantum error correction condition: the projection of error
    compositions back onto the code subspace is proportional to the projector itself,
    meaning errors don't distinguish between codewords. -/
def KnillLaflamme (pi_dist : V → ℝ) (code : CodeSubspace V pi_dist)
    {n : ℕ} (errors : ErrorOperators V n) : Prop :=
  ∃ (α : Fin n → Fin n → ℂ), ∀ (i : Fin n) (j : Fin n),
    code.proj ∘ₗ (adjoint_pi pi_dist (errors.errors i)) ∘ₗ (errors.errors j) ∘ₗ code.proj =
    α i j • code.proj

/-! ## The Bridge: Lumpability ↔ Quantum Error Correction

This is the central theorem establishing the equivalence between classical
lumpability and quantum error correction. -/

/-- Embed a classical state as a diagonal quantum state. -/
def embedClassical (pi_dist : V → ℝ) (s : ClassicalState V) :
    (V → ℂ) →ₗ[ℂ] (V → ℂ) :=
  { toFun := fun v => fun x => (s.dist x : ℂ) * v x
    map_add' := fun u v => by ext x; simp [mul_add]
    map_smul' := fun c v => by ext x; simp [mul_comm, mul_assoc] }

/-- The embedding of a classical state is a valid quantum state. -/
axiom embedClassical_isDensityMatrix (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (s : ClassicalState V) :
    IsDensityMatrix pi_dist (embedClassical pi_dist s)

/-- Convert a classical partition to a code subspace projector.
    Each partition block becomes a basis vector in the code subspace. -/
axiom partitionToCodeSubspace (pi_dist : V → ℝ) (P : Partition V) :
    CodeSubspace V pi_dist

/-- The defect operator from approximate lumpability corresponds to
    the error syndrome in quantum error correction.

    For a classical generator L and partition P, the defect D = (I - Π) L Π
    becomes the single error operator in the quantum picture.

    We axiomatize the complexification D_ℂ : (V → ℂ) →ₗ[ℂ] (V → ℂ). -/
axiom complexifyDefect (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V) : (V → ℂ) →ₗ[ℂ] (V → ℂ)

/-- The complexified defect is zero iff the real defect has zero operator norm. -/
axiom complexifyDefect_zero_iff (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V) :
    complexifyDefect pi_dist hπ L P = 0 ↔ opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) = 0

def defectToErrorOperators (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V) : ErrorOperators V 1 :=
  { errors := fun _ => complexifyDefect pi_dist hπ L P }

/-- **Easy Direction**: If the defect operator is zero (exact lumpability),
    then Knill-Laflamme conditions hold trivially with α = 0.

    Proof idea: D = 0 ⟹ E = 0 ⟹ E†E = 0 ⟹ P E†E P = 0 = 0·P -/
theorem lumpability_implies_knill_laflamme (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V)
    (hD : opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) = 0) :
    let code := partitionToCodeSubspace pi_dist P
    let errors := defectToErrorOperators pi_dist hπ L P
    KnillLaflamme pi_dist code errors := by
  intro code errors
  -- When opNorm D = 0, the complexified defect E is also zero
  have hE_zero : complexifyDefect pi_dist hπ L P = 0 :=
    (complexifyDefect_zero_iff pi_dist hπ L P).mpr hD
  -- So E† E = 0, and P ∘ 0 ∘ P = 0 = 0 • P
  use fun _ _ => 0  -- α_ij = 0 for all i,j
  intro i j
  simp only [zero_smul]
  -- errors.errors _ = complexifyDefect = 0
  have hEi : errors.errors i = 0 := hE_zero
  have hEj : errors.errors j = 0 := hE_zero
  -- P ∘ 0† ∘ 0 ∘ P = 0
  rw [hEi, hEj, adjoint_pi_zero]
  simp only [LinearMap.comp_zero, LinearMap.zero_comp]

/-- **Hard Direction**: If Knill-Laflamme conditions hold,
    then the defect operator norm is zero.

    This is more subtle: KL says P E† E P ∝ P, which constrains the error structure.
    When the error comes from a classical defect operator, this forces D = 0. -/
theorem knill_laflamme_implies_lumpability (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V)
    (hKL : let code := partitionToCodeSubspace pi_dist P
           let errors := defectToErrorOperators pi_dist hπ L P
           KnillLaflamme pi_dist code errors) :
    opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) = 0 := by
  -- The Knill-Laflamme condition P E† E P = α P, combined with:
  -- 1. E is the complexification of the real defect operator D
  -- 2. P is the complexification of the real coarse projector Π
  -- 3. Π is self-adjoint (symmetric for real operators)
  -- implies that D must be zero.
  --
  -- Key insight: For the single-error case with E = D_ℂ:
  -- If P D† D P = α P and D comes from (I-Π)LΠ, then
  -- the only way this can hold for all codewords is if D = 0.
  sorry

/-- The full bridge theorem combining both directions. -/
theorem knill_laflamme_iff_lumpability (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V) :
    let code := partitionToCodeSubspace pi_dist P
    let errors := defectToErrorOperators pi_dist hπ L P
    (opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) = 0) ↔
    KnillLaflamme pi_dist code errors :=
  ⟨lumpability_implies_knill_laflamme pi_dist hπ L P,
   knill_laflamme_implies_lumpability pi_dist hπ L P⟩

/-! ## Approximate Version: Error Bounds

For approximate lumpability, we get approximate QEC with error bounds. -/

/-- The defect norm in classical lumpability bounds the trace distance error
    in the quantum channel simulation. -/
axiom approximate_qec_bound (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V) (t : ℝ) (ht : 0 ≤ t) :
    let ε := opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ)
    let code := partitionToCodeSubspace pi_dist P
    ∀ (ρ : (V → ℂ) →ₗ[ℂ] (V → ℂ)) (hρ : IsDensityMatrix pi_dist ρ),
      traceDistance_pi pi_dist
        (code.proj ∘ₗ ρ ∘ₗ code.proj)
        ρ ≤ ε * t

/-! ## Quantum Validity Horizon

The validity horizon bounds how long coarse-grained dynamics remain accurate.
In the quantum setting, this becomes a bound on decoherence. -/

/-- The quantum validity horizon: time until trace distance exceeds threshold. -/
def quantumValidityHorizon (pi_dist : V → ℝ) (ℒ : Lindbladian V pi_dist)
    (code : CodeSubspace V pi_dist) (δ : ℝ) : ℝ :=
  sInf { t : ℝ | t > 0 ∧ ∀ (ρ : (V → ℂ) →ₗ[ℂ] (V → ℂ)) (hρ : IsDensityMatrix pi_dist ρ),
    traceDistance_pi pi_dist (code.proj ∘ₗ ρ ∘ₗ code.proj) ρ > δ }

/-- **Quantum Validity Horizon Theorem**:
    The validity horizon is bounded in terms of the spectral gap and code quality. -/
axiom quantum_validity_horizon_bound (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V) (δ : ℝ) (hδ : 0 < δ) :
    let ε := opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ)
    let code := partitionToCodeSubspace pi_dist P
    ε > 0 → ∃ (ℒ : Lindbladian V pi_dist),
      quantumValidityHorizon pi_dist ℒ code δ ≥ δ / ε

end Quantum
end Bridge
end SGC
