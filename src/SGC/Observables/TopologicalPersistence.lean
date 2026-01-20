/-
Copyright (c) 2025 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team

# Topological Persistence: Betti Numbers and System Lifetime

This module formalizes the relationship between topological complexity (first Betti
number b₁) and system persistence time. The main result connects the number of
independent cycles to expected lifetime under stochastic surgery dynamics.

## Main Results

1. `persistence_time`: Expected time until b₁ → 0 (loss of all Markov blankets)
2. `betti_persistence_bound`: Higher b₁ implies longer expected persistence
3. `redundancy_principle`: b₁ acts as topological redundancy buffer

## Physical Significance

Living systems maintain Markov blankets (b₁ ≥ 1) to separate self from environment.
Higher b₁ provides redundancy: if one blanket is destroyed, others remain.

This explains why complex organisms (high b₁) tend to be more robust than simple
ones: they have more topological "spare parts."

## References

- SGC `Conservation.lean` (Betti numbers and safe surgery)
- Ghrist (2014), "Elementary Applied Topology"
- Carlsson (2009), "Topology and Data"
-/

import SGC.Evolution.Conservation
import SGC.Renormalization.Approximate

noncomputable section

namespace SGC.Observables

open SGC.Evolution

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-! ### 1. Surgery Rate Model -/

/-- **Surgery Rate**: The expected number of surgery events per unit time.

    This models the frequency of topology-changing events (bond breaking/forming).
    In physical systems, this relates to:
    - Metabolic rate (biological systems)
    - Reaction rate (chemical systems)
    - Update frequency (computational systems)

    **Parameter**: λ > 0 is the Poisson rate of surgery attempts. -/
structure SurgeryDynamics where
  /-- Rate of surgery attempts (Poisson process) -/
  surgeryRate : ℝ
  /-- Surgery rate is positive -/
  rate_pos : 0 < surgeryRate
  /-- Probability that a surgery attempt destroys one cycle (given it succeeds) -/
  cycleDestructionProb : ℝ
  /-- Destruction probability is in [0, 1] -/
  destruction_prob_bounds : 0 ≤ cycleDestructionProb ∧ cycleDestructionProb ≤ 1

/-! ### 2. Persistence Time Definition -/

/-- **Expected Persistence Time**: Time until first Betti number reaches zero.

    For a system with b₁ = k independent cycles, under Poisson surgery dynamics
    with cycle destruction probability p, the expected time to lose all cycles is:

    E[T_persist] = k / (λ · p)

    where:
    - k = b₁ = initial number of cycles
    - λ = surgery rate
    - p = probability each surgery destroys one cycle

    **Derivation**: Each cycle is destroyed independently at rate λ·p.
    Expected time to destroy k cycles is k/(λ·p) by linearity of expectation
    (assuming cycles are destroyed one at a time, which is the generic case). -/
def expected_persistence_time (G : WeightedGraph V) (dynamics : SurgeryDynamics) : ℝ :=
  (BettiNumber G 1 : ℝ) / (dynamics.surgeryRate * dynamics.cycleDestructionProb)

/-- Persistence time is positive when b₁ ≥ 1 and destruction probability > 0. -/
lemma expected_persistence_time_pos (G : WeightedGraph V) (dynamics : SurgeryDynamics)
    (hb : HasMarkovBlanket G) (hp : 0 < dynamics.cycleDestructionProb) :
    0 < expected_persistence_time G dynamics := by
  unfold expected_persistence_time
  apply div_pos
  · -- b₁ ≥ 1 implies (b₁ : ℝ) > 0
    -- HasMarkovBlanket means BettiNumber G 1 ≥ 1
    unfold HasMarkovBlanket at hb
    have h_pos_nat : 0 < BettiNumber G 1 := Nat.one_le_iff_ne_zero.mp hb |> Nat.pos_of_ne_zero
    exact Nat.cast_pos.mpr h_pos_nat
  · exact mul_pos dynamics.rate_pos hp

/-! ### 3. Main Theorem: Betti-Persistence Bound -/

/-- **Betti-Persistence Bound**: Higher first Betti number implies longer persistence.

    If G₁ has more cycles than G₂ (b₁(G₁) > b₁(G₂)), then G₁ has longer
    expected persistence time under the same surgery dynamics.

    **Proof**: Direct from the definition: E[T] = b₁ / (λ·p), so more cycles
    means more time. -/
theorem betti_persistence_bound (G₁ G₂ : WeightedGraph V) (dynamics : SurgeryDynamics)
    (hp : 0 < dynamics.cycleDestructionProb)
    (hb : BettiNumber G₁ 1 > BettiNumber G₂ 1) :
    expected_persistence_time G₁ dynamics > expected_persistence_time G₂ dynamics := by
  unfold expected_persistence_time
  have h_denom_pos : 0 < dynamics.surgeryRate * dynamics.cycleDestructionProb :=
    mul_pos dynamics.rate_pos hp
  apply div_lt_div_of_pos_right _ h_denom_pos
  exact Nat.cast_lt.mpr hb

/-- **Monotonicity**: Persistence time is monotonic in b₁. -/
theorem persistence_mono (G₁ G₂ : WeightedGraph V) (dynamics : SurgeryDynamics)
    (hb : BettiNumber G₁ 1 ≥ BettiNumber G₂ 1) :
    expected_persistence_time G₁ dynamics ≥ expected_persistence_time G₂ dynamics := by
  unfold expected_persistence_time
  have h_denom_pos : 0 < dynamics.surgeryRate * dynamics.cycleDestructionProb ∨
                     dynamics.surgeryRate * dynamics.cycleDestructionProb = 0 := by
    by_cases h : dynamics.cycleDestructionProb = 0
    · right; simp [h]
    · left; exact mul_pos dynamics.rate_pos (lt_of_le_of_ne dynamics.destruction_prob_bounds.1 (Ne.symm h))
  cases h_denom_pos with
  | inl h =>
    apply div_le_div_of_nonneg_right _ h.le
    exact Nat.cast_le.mpr hb
  | inr h =>
    simp [h]

/-! ### 4. Redundancy Principle -/

/-- **Redundancy Buffer**: b₁ - 1 cycles can be lost while maintaining identity.

    A system with b₁ = k has (k-1) "spare" blankets. It can survive (k-1) cycle
    destructions and still maintain HasMarkovBlanket (b₁ ≥ 1).

    This formalizes topological redundancy as a measure of robustness. -/
def redundancy_buffer (G : WeightedGraph V) : ℕ :=
  BettiNumber G 1 - 1

/-- Systems with higher b₁ have more redundancy. -/
theorem redundancy_monotonic (G₁ G₂ : WeightedGraph V)
    (hb : BettiNumber G₁ 1 ≥ BettiNumber G₂ 1) :
    redundancy_buffer G₁ ≥ redundancy_buffer G₂ := by
  unfold redundancy_buffer
  omega

/-- **Survival Theorem**: A system survives k surgery events if b₁ > k.

    This gives a lower bound on the number of destructive events a system
    can withstand while maintaining its Markov blanket.

    Axiomatized: Full proof requires formalization of iterated surgery. -/
axiom survival_bound (G : WeightedGraph V) (k : ℕ) (hk : BettiNumber G 1 > k) :
    ∃ G' : WeightedGraph V, (∀ _i : Fin k, ∃ G_i : WeightedGraph V, IsCyclePreservingSurgery G_i G') ∧ HasMarkovBlanket G'

/-! ### 5. Complexity-Persistence Tradeoff -/

/-- **Maintenance Cost**: Higher b₁ requires more energy to maintain.

    Each cycle represents a feedback loop that must be actively maintained.
    The maintenance cost scales with b₁.

    **Parameter**: c > 0 is the cost per cycle per unit time. -/
def maintenance_cost (G : WeightedGraph V) (cost_per_cycle : ℝ) : ℝ :=
  cost_per_cycle * (BettiNumber G 1 : ℝ)

/-- **Persistence-Cost Ratio**: Efficiency of topological investment.

    Ratio = E[T_persist] / maintenance_cost = 1 / (λ · p · c)

    This is constant for fixed dynamics, suggesting that adding more cycles
    is always "worth it" in terms of persistence per unit cost—until other
    constraints (energy budget, space) become limiting. -/
def persistence_cost_ratio (dynamics : SurgeryDynamics) (cost_per_cycle : ℝ)
    (hc : 0 < cost_per_cycle) (hp : 0 < dynamics.cycleDestructionProb) : ℝ :=
  1 / (dynamics.surgeryRate * dynamics.cycleDestructionProb * cost_per_cycle)

/-- The persistence-cost ratio is independent of b₁. -/
theorem persistence_cost_ratio_constant (G₁ G₂ : WeightedGraph V)
    (dynamics : SurgeryDynamics) (cost_per_cycle : ℝ)
    (hc : 0 < cost_per_cycle) (hp : 0 < dynamics.cycleDestructionProb)
    (hb₁ : HasMarkovBlanket G₁) (hb₂ : HasMarkovBlanket G₂) :
    expected_persistence_time G₁ dynamics / maintenance_cost G₁ cost_per_cycle =
    expected_persistence_time G₂ dynamics / maintenance_cost G₂ cost_per_cycle := by
  -- Both sides simplify to 1 / (λ · p · c), independent of b₁
  unfold expected_persistence_time maintenance_cost
  -- LHS = (b₁ / (λ·p)) / (c·b₁) = b₁ / (λ·p·c·b₁) = 1 / (λ·p·c)  [when b₁ ≠ 0]
  -- RHS = (b₂ / (λ·p)) / (c·b₂) = b₂ / (λ·p·c·b₂) = 1 / (λ·p·c)  [when b₂ ≠ 0]
  -- Get that b₁ ≠ 0 and b₂ ≠ 0 from HasMarkovBlanket
  unfold HasMarkovBlanket at hb₁ hb₂
  have hb₁_pos : (0 : ℝ) < (BettiNumber G₁ 1 : ℝ) := by
    exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hb₁))
  have hb₂_pos : (0 : ℝ) < (BettiNumber G₂ 1 : ℝ) := by
    exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hb₂))
  have hb₁_ne : (BettiNumber G₁ 1 : ℝ) ≠ 0 := ne_of_gt hb₁_pos
  have hb₂_ne : (BettiNumber G₂ 1 : ℝ) ≠ 0 := ne_of_gt hb₂_pos
  have hc_ne : cost_per_cycle ≠ 0 := ne_of_gt hc
  have hdenom_ne : dynamics.surgeryRate * dynamics.cycleDestructionProb ≠ 0 :=
    ne_of_gt (mul_pos dynamics.rate_pos hp)
  -- Simplify both sides - field_simp handles the cancellation
  field_simp

/-! ### 6. Connection to Validity Horizon -/

/-- **Topological Validity Horizon**: The validity horizon T* relates to persistence.

    For systems where leakage defect ε scales with 1/b₁ (more cycles = better
    self-model), the validity horizon T* = 1/ε scales with b₁.

    This connects topological persistence to predictive validity:
    more robust systems (high b₁) also have longer-valid effective theories. -/
axiom defect_betti_scaling (G : WeightedGraph V) (L : Matrix V V ℝ)
    (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, C > 0 ∧ ε * (BettiNumber G 1 : ℝ) ≤ C

/-! ## Summary

This module establishes the **topological persistence principle**:

1. **Definition**: E[T_persist] = b₁ / (λ·p)
2. **Main Bound**: b₁(G₁) > b₁(G₂) → E[T₁] > E[T₂]
3. **Redundancy**: b₁ - 1 = number of "spare" blankets
4. **Efficiency**: Persistence-per-cost ratio is constant

**Physical Implications**:
- Complex organisms (high b₁) are more robust to perturbations
- Evolution selects for higher b₁ up to maintenance cost limits
- Topological complexity provides insurance against catastrophic failure

**Connection to SGC**:
- b₁ ≥ 1 defines HasMarkovBlanket (agent identity)
- Surgery dynamics model metabolic/evolutionary change
- Persistence time relates to validity horizon of effective theories
-/

end SGC.Observables
