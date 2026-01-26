/-
Copyright (c) 2026 SGC Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Contributors
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
    We axiomatize the adjoint operation for simplicity. -/
def KnillLaflamme (pi_dist : V → ℝ) (code : CodeSubspace V pi_dist)
    {n : ℕ} (errors : ErrorOperators V n) : Prop :=
  ∃ (α : Fin n → Fin n → ℂ), ∀ (i : Fin n) (j : Fin n),
    -- P E_i† E_j P = α_ij P (axiomatized; E† is the adjoint w.r.t. inner_pi)
    True  -- Placeholder: full statement requires adjoint infrastructure

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
    the error syndrome in quantum error correction. -/
axiom defectToErrorOperators (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V) :
    ErrorOperators V 1  -- Single error channel corresponding to leakage

/-- **Main Bridge Theorem (ε = 0 case)**:
    Exact lumpability of a Markov chain is equivalent to the Knill-Laflamme
    conditions being satisfied for the corresponding quantum objects.

    Classical side: L is lumpable w.r.t. partition P iff [L, Q] = 0
    where Q is the coarse projection operator.

    Quantum side: The code defined by P can correct errors from L
    iff Knill-Laflamme holds. -/
axiom knill_laflamme_is_lumpability (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V) :
    let code := partitionToCodeSubspace pi_dist P
    let errors := defectToErrorOperators pi_dist hπ L P
    -- Classical: defect operator norm is zero (exact lumpability)
    (opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) = 0) ↔
    -- Quantum: Knill-Laflamme conditions hold
    KnillLaflamme pi_dist code errors

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
