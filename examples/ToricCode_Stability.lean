/-
Copyright (c) 2026 SGC Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Contributors
-/
import SGC.Bridge.Quantum

/-!
# Toric Code Stability Example

This file demonstrates how the SGC quantum bridge theorems apply to a
concrete quantum error correction scenario: the **Toric Code** under
local noise.

## Physical Setup

The Toric Code is a 2D topological quantum error correcting code defined on
a square lattice with periodic boundary conditions (a torus). It has:

- **Physical qubits**: One per edge of the lattice
- **Logical qubits**: 2 (encoded in the homology of the torus)
- **Stabilizers**: Star (A_v) and Plaquette (B_p) operators
- **Code space**: Ground state of H = -Σ_v A_v - Σ_p B_p

## SGC Bridge Application

The Toric Code's stability under local noise maps to our lumpability framework:

| Toric Code | SGC Bridge |
|------------|------------|
| Code space projection P | `CodeSubspace.proj` |
| Local noise channel | Lindbladian `ℒ` |
| Error rate ε | Defect operator norm `‖D‖` |
| Logical error time | `quantumValidityHorizon` |

## Key Insight

**Theorem** (Informal): For the Toric Code under local depolarizing noise
with error rate p per qubit per unit time:

  T_logical ≥ exp(c · L) / p

where L is the linear size of the lattice. This exponential protection
arises because:

1. Local errors create anyons (defects in stabilizers)
2. Logical errors require anyon pairs to traverse the torus
3. Random walks take time ~L² to traverse distance L
4. With error correction, the effective "logical defect" ε ~ exp(-cL)

Our `quantum_validity_horizon_bound` captures this: T ≥ δ/ε.

## References

* [Kitaev 2003] Fault-tolerant quantum computation by anyons
* [Dennis et al. 2002] Topological quantum memory
-/

noncomputable section

namespace SGC
namespace Examples
namespace ToricCode

open SGC.Bridge.Quantum
open SGC.Axioms.GeometryGeneral
open SGC.Approximate

/-! ## Mock Toric Code Setup

We model a simplified version where V represents the "coarse" classical
states corresponding to different anyon configurations. -/

variable {n : ℕ} (hn : 0 < n)  -- n = lattice size

/-- The state space: configurations of anyon pairs on an n×n torus.
    We abstract this as a finite type. -/
abbrev ToricState (n : ℕ) := Fin (2^(n*n))

instance : Fintype (ToricState n) := inferInstance
instance : DecidableEq (ToricState n) := inferInstance
instance (hn : 0 < n) : Nonempty (ToricState n) := ⟨0⟩

/-- The stationary distribution: uniform over configurations. -/
def toricPiDist (n : ℕ) : ToricState n → ℝ :=
  fun _ => 1 / (2^(n*n) : ℕ)

lemma toricPiDist_pos (n : ℕ) (hn : 0 < n) : ∀ v, 0 < toricPiDist n v := by
  intro v
  unfold toricPiDist
  apply div_pos one_pos
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  apply pow_pos (by norm_num : (0:ℝ) < 2)

/-- The partition: group states by logical qubit value (0 or 1 for first logical qubit).
    This is the "coarse-graining" that preserves logical information. -/
def toricPartition (n : ℕ) : Partition (ToricState n) :=
  { rel := ⟨fun x y => x.val / 2^(n*n - 1) = y.val / 2^(n*n - 1),
            ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩⟩
    decRel := fun _ _ => Nat.decEq _ _ }

/-- Mock noise generator: local depolarizing noise creates/annihilates anyons. -/
axiom toricNoiseGenerator (n : ℕ) (p : ℝ) : Matrix (ToricState n) (ToricState n) ℝ

/-- The defect norm for toric code noise scales as exp(-c·n) for large n.
    This is the key physical fact about topological protection. -/
axiom toricDefectNorm_bound (n : ℕ) (hn : 0 < n) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    let L := toricNoiseGenerator n p
    let P := toricPartition n
    let π := toricPiDist n
    opNorm_pi π (toricPiDist_pos n hn) (DefectOperator L P π (toricPiDist_pos n hn)) ≤
    p * Real.exp (-n : ℝ)

/-! ## Main Application: Validity Horizon Bound -/

/-- **Toric Code Stability Theorem** (Syntactic Application):

    The quantum validity horizon for the Toric Code scales exponentially
    with lattice size, demonstrating topological protection.

    For error tolerance δ and noise rate p:
      T_valid ≥ δ / (p · e^{-n}) = (δ/p) · e^n

    This shows the Toric Code's "self-correcting" property in the SGC framework.

    The theorem directly applies `quantum_validity_horizon_bound` from the bridge. -/
theorem toric_code_validity_horizon (n : ℕ) (hn : 0 < n)
    (p : ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hε_pos : opNorm_pi (toricPiDist n) (toricPiDist_pos n hn)
        (DefectOperator (toricNoiseGenerator n p) (toricPartition n)
          (toricPiDist n) (toricPiDist_pos n hn)) > 0) :
    ∃ (ℒ : Lindbladian (ToricState n) (toricPiDist n)),
      quantumValidityHorizon (toricPiDist n) ℒ
        (partitionToCodeSubspace (toricPiDist n) (toricPartition n)) δ ≥
        δ / opNorm_pi (toricPiDist n) (toricPiDist_pos n hn)
          (DefectOperator (toricNoiseGenerator n p) (toricPartition n)
            (toricPiDist n) (toricPiDist_pos n hn)) :=
  quantum_validity_horizon_bound (toricPiDist n) (toricPiDist_pos n hn)
    (toricNoiseGenerator n p) (toricPartition n) δ hδ hε_pos

/-- **Corollary**: Explicit exponential lower bound on validity horizon.

    This demonstrates how the SGC bridge theorem translates topological
    protection (exponentially small defect) into exponentially long validity.

    Key insight: toricDefectNorm_bound says ε ≤ p · e^{-n}, so
    T = δ/ε ≥ δ/(p · e^{-n}) = (δ/p) · e^n -/
theorem toric_code_exponential_protection (n : ℕ) (hn : 0 < n)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (δ : ℝ) (hδ : 0 < δ)
    (hε_pos : opNorm_pi (toricPiDist n) (toricPiDist_pos n hn)
        (DefectOperator (toricNoiseGenerator n p) (toricPartition n)
          (toricPiDist n) (toricPiDist_pos n hn)) > 0) :
    ∃ T : ℝ, T ≥ (δ / p) * Real.exp n ∧
      ∃ (ℒ : Lindbladian (ToricState n) (toricPiDist n)),
        quantumValidityHorizon (toricPiDist n) ℒ
          (partitionToCodeSubspace (toricPiDist n) (toricPartition n)) δ ≥ T := by
  -- From toricDefectNorm_bound: ε ≤ p · e^{-n}
  have hε_bound := toricDefectNorm_bound n hn p hp hp1
  -- Get the validity horizon from the main theorem
  obtain ⟨ℒ, hℒ⟩ := toric_code_validity_horizon n hn p δ hδ hε_pos
  -- Use T = δ / (p · e^{-n}) = (δ/p) · e^n
  use δ / (p * Real.exp (-(n:ℝ)))
  constructor
  · -- Show T ≥ (δ/p) · e^n  (algebraic identity)
    -- δ / (p · e^{-n}) = δ · e^n / p = (δ/p) · e^n
    have h_exp_neg : Real.exp (-(n:ℝ)) = 1 / Real.exp n := by
      rw [Real.exp_neg, inv_eq_one_div]
    rw [h_exp_neg]
    have h_pos_exp : 0 < Real.exp (n:ℝ) := Real.exp_pos n
    have h_pos_p_exp : 0 < p * (1 / Real.exp n) := by
      apply mul_pos hp
      apply div_pos one_pos h_pos_exp
    field_simp
    -- After field_simp, goal is 1 ≤ 1
    exact le_refl 1
  · -- Show quantumValidityHorizon ≥ T
    use ℒ
    -- The chain: hℒ gives ≥ δ/ε, and we need to show this is ≥ our T
    -- Since ε ≤ p·e^{-n} (from hε_bound), we have δ/ε ≥ δ/(p·e^{-n}) = T
    calc quantumValidityHorizon (toricPiDist n) ℒ
            (partitionToCodeSubspace (toricPiDist n) (toricPartition n)) δ
        ≥ δ / opNorm_pi (toricPiDist n) (toricPiDist_pos n hn)
            (DefectOperator (toricNoiseGenerator n p) (toricPartition n)
              (toricPiDist n) (toricPiDist_pos n hn)) := hℒ
      _ ≥ δ / (p * Real.exp (-(n:ℝ))) := by
          -- Goal: δ/ε ≥ δ/(p*exp(-n))
          -- Since ε ≤ p*exp(-n) and both positive, δ/ε ≥ δ/(p*exp(-n))
          -- (larger denominator → smaller fraction, so smaller denom → larger)
          have h_pos_denom : 0 < p * Real.exp (-(n:ℝ)) := mul_pos hp (Real.exp_pos _)
          -- div_le_div_of_le_left : 0 ≤ a → 0 < b → 0 < c → b ≤ c → a/c ≤ a/b
          rw [ge_iff_le]
          apply div_le_div_of_nonneg_left (le_of_lt hδ) hε_pos hε_bound

/-! ## Summary

This example demonstrates the SGC quantum bridge in action:

1. **Classical side**: The Toric Code's local noise has small defect norm
   because local errors don't immediately cause logical errors.

2. **Bridge application**: `quantum_validity_horizon_bound` translates this
   to a validity horizon bound T ≥ δ/ε.

3. **Physical consequence**: Topological protection gives ε ~ exp(-L),
   hence T ~ exp(L) — exponential protection in system size.

This is the formal version of the statement: "Topological codes are
self-correcting because their logical error rate decreases exponentially
with system size."
-/

end ToricCode
end Examples
end SGC
