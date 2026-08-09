/-
Copyright (c) 2025 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team

# Exploration Mass: Principled Heat-Phase Control via Accumulated Noise

This module formalizes the **Exploration Mass** concept: instead of triggering
quench after a fixed number of epochs, we trigger when the accumulated noise
injection Σηₜ crosses a threshold derived from mixing guarantees.

## Main Results

1. `contraction_product_bound`: ∏(1-aᵢ) ≤ exp(-Σaᵢ) for aᵢ ∈ [0,1]
2. `exploration_mass_mixing_bound`: After N steps with per-step noise ηₜ,
   distance to equilibrium ≤ exp(-Σηₜ) × initial_distance
3. `exploration_mass_threshold`: The threshold M_explore = log(d₀/δ) guarantees
   mixing to within tolerance δ

## Physical Significance

In neural network training with noise injection:
- Each noise injection step with strength η contracts distance to equilibrium by (1-η)
- The **exploration mass** M = Σηₜ accumulates over time
- When M ≥ log(d₀/δ), we have provably mixed to within δ of equilibrium

This replaces arbitrary epoch-based triggers with a **principled mixing guarantee**,
breaking the feedback loop that traps entropy-triggered controllers.

## Connection to Phase-4 HeatQuench

Phase-4's empirical success came from forcing a sequential explore→consolidate order.
The exploration mass theorem provides the mathematical justification:
- Heat phase: inject noise ηₜ > 0, accumulate M = Σηₜ
- Quench trigger: when M ≥ M_explore = log(d₀/δ)
- This is **exogenous** (based on our noise injection, not network state)
  but **principled** (derived from mixing theory)

## References

- Levin, Peres, Wilmer (2009), Markov Chains and Mixing Times
- SGC `sector_envelope_bound_canonical` (Sector.lean)
-/

import SGC.Axioms.Geometry
import SGC.Spectral.Core.Assumptions
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace SGC.Observables.ExplorationMass

open Finset Real BigOperators

/-! ### 1. Fundamental Inequality: Product vs Exponential Sum -/

/-- **Log inequality**: log(1-x) ≤ -x for x ∈ [0,1).
    This is the key lemma for converting products to exponential sums. -/
lemma log_one_sub_le_neg (x : ℝ) (hx_nonneg : 0 ≤ x) (hx_lt_one : x < 1) :
    Real.log (1 - x) ≤ -x := by
  -- log(1-x) ≤ -x is equivalent to log(1-x) + x ≤ 0
  -- This follows from the concavity of log: log(y) ≤ y - 1 for y > 0
  -- Setting y = 1-x: log(1-x) ≤ (1-x) - 1 = -x
  have h_pos : 0 < 1 - x := by linarith
  -- Use log_le_sub_one: log x ≤ x - 1 for x > 0
  have h_concave := Real.log_le_sub_one_of_pos h_pos
  -- h_concave : log(1-x) ≤ (1-x) - 1 = -x
  linarith

/-- **Product-to-exponential bound** (finite version):
    For a finite sequence (aᵢ) with aᵢ ∈ [0,1],
    ∏ᵢ (1 - aᵢ) ≤ exp(-Σᵢ aᵢ)

    **Proof**: Take log of both sides.
    log(∏(1-aᵢ)) = Σ log(1-aᵢ) ≤ Σ(-aᵢ) = -Σaᵢ
    Exponentiating: ∏(1-aᵢ) ≤ exp(-Σaᵢ) -/
theorem contraction_product_bound {n : ℕ} (a : Fin n → ℝ)
    (ha_nonneg : ∀ i, 0 ≤ a i) (ha_lt_one : ∀ i, a i < 1) :
    ∏ i, (1 - a i) ≤ Real.exp (- ∑ i, a i) := by
  by_cases hn : n = 0
  · -- Empty product = 1, empty sum = 0, exp(0) = 1
    subst hn
    simp only [Fintype.univ_ofIsEmpty, prod_empty, sum_empty, neg_zero, exp_zero, le_refl]
  · -- n > 0 case: use log inequality
    have h_prod_pos : 0 < ∏ i, (1 - a i) := by
      apply prod_pos
      intro i _
      have := ha_lt_one i
      have := ha_nonneg i
      linarith
    -- Take log: log(∏(1-aᵢ)) ≤ -Σaᵢ
    rw [← Real.log_le_log_iff h_prod_pos (Real.exp_pos _)]
    rw [Real.log_exp]
    -- log(∏(1-aᵢ)) = Σ log(1-aᵢ)
    rw [Real.log_prod (s := univ) (fun i _ => by linarith [ha_nonneg i, ha_lt_one i] : ∀ i ∈ univ, 1 - a i ≠ 0)]
    -- Σ log(1-aᵢ) ≤ Σ(-aᵢ) = -Σaᵢ
    rw [← sum_neg_distrib]
    apply sum_le_sum
    intro i _
    exact log_one_sub_le_neg (a i) (ha_nonneg i) (ha_lt_one i)

/-! ### 2. Exploration Mass Definition -/

/-- **Exploration Mass**: The accumulated noise injection over a sequence of steps.
    M = Σₜ ηₜ where ηₜ ∈ [0,1] is the noise strength at step t. -/
def exploration_mass {n : ℕ} (η : Fin n → ℝ) : ℝ := ∑ i, η i

/-- Exploration mass is non-negative when all noise strengths are non-negative. -/
lemma exploration_mass_nonneg {n : ℕ} (η : Fin n → ℝ) (hη : ∀ i, 0 ≤ η i) :
    0 ≤ exploration_mass η := by
  unfold exploration_mass
  exact sum_nonneg (fun i _ => hη i)

/-! ### 3. Mixing Bound via Exploration Mass -/

/-- **Exploration Mass Mixing Bound**:
    If each step contracts distance by factor (1-ηₜ), then after n steps:
    d(μₙ, π) ≤ exp(-M) × d(μ₀, π)
    where M = Σηₜ is the exploration mass.

    This is the core theorem justifying exploration mass as a mixing criterion. -/
theorem exploration_mass_mixing_bound {n : ℕ} (η : Fin n → ℝ)
    (hη_nonneg : ∀ i, 0 ≤ η i) (hη_lt_one : ∀ i, η i < 1)
    (d₀ : ℝ) (hd₀_nonneg : 0 ≤ d₀) :
    (∏ i, (1 - η i)) * d₀ ≤ Real.exp (- exploration_mass η) * d₀ := by
  by_cases hd₀ : d₀ = 0
  · simp [hd₀]
  · have hd₀_pos : 0 < d₀ := lt_of_le_of_ne hd₀_nonneg (Ne.symm hd₀)
    apply mul_le_mul_of_nonneg_right _ (le_of_lt hd₀_pos)
    exact contraction_product_bound η hη_nonneg hη_lt_one

/-! ### 4. Exploration Mass Threshold -/

/-- **Exploration Mass Threshold**: The minimum exploration mass needed to
    guarantee mixing to within tolerance δ from initial distance d₀.

    M_explore = log(d₀/δ)

    When M ≥ M_explore, we have d(μ, π) ≤ δ. -/
def exploration_mass_threshold (d₀ δ : ℝ) (hd₀ : 0 < d₀) (hδ : 0 < δ) : ℝ :=
  Real.log (d₀ / δ)

/-- The threshold is non-negative when d₀ ≥ δ. -/
lemma exploration_mass_threshold_nonneg (d₀ δ : ℝ) (hd₀ : 0 < d₀) (hδ : 0 < δ)
    (h_ge : d₀ ≥ δ) : 0 ≤ exploration_mass_threshold d₀ δ hd₀ hδ := by
  unfold exploration_mass_threshold
  rw [Real.log_nonneg_iff (div_pos hd₀ hδ)]
  exact (one_le_div hδ).mpr h_ge

/-- **Mixing Guarantee**: When exploration mass exceeds the threshold,
    distance to equilibrium is within tolerance δ.

    If M ≥ log(d₀/δ), then exp(-M) × d₀ ≤ δ. -/
theorem mixing_guarantee (d₀ δ : ℝ) (hd₀ : 0 < d₀) (hδ : 0 < δ)
    (M : ℝ) (hM : M ≥ exploration_mass_threshold d₀ δ hd₀ hδ) :
    Real.exp (-M) * d₀ ≤ δ := by
  unfold exploration_mass_threshold at hM
  -- exp(-M) ≤ exp(-log(d₀/δ)) = δ/d₀
  have h1 : Real.exp (-M) ≤ Real.exp (- Real.log (d₀ / δ)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have h2 : Real.exp (- Real.log (d₀ / δ)) = δ / d₀ := by
    rw [Real.exp_neg, Real.exp_log (div_pos hd₀ hδ)]
    field_simp
  calc Real.exp (-M) * d₀
      ≤ (δ / d₀) * d₀ := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hd₀)
        calc Real.exp (-M) ≤ Real.exp (- Real.log (d₀ / δ)) := h1
           _ = δ / d₀ := h2
    _ = δ := by field_simp

/-! ### 5. Ready for Quench Predicate -/

/-- **Ready for Quench via Exploration Mass**:
    The system is ready for quench when the accumulated exploration mass
    exceeds the threshold derived from initial distance and target tolerance.

    This replaces epoch-based triggers with a principled mixing guarantee. -/
def ready_for_quench_exploration_mass {n : ℕ} (η : Fin n → ℝ)
    (d₀ δ : ℝ) (hd₀ : 0 < d₀) (hδ : 0 < δ) : Prop :=
  exploration_mass η ≥ exploration_mass_threshold d₀ δ hd₀ hδ

/-- **Quench Readiness Implies Mixing**:
    If ready_for_quench_exploration_mass holds, then the distance to equilibrium
    is within the target tolerance δ. -/
theorem quench_ready_implies_mixed {n : ℕ} (η : Fin n → ℝ)
    (hη_nonneg : ∀ i, 0 ≤ η i) (hη_lt_one : ∀ i, η i < 1)
    (d₀ δ : ℝ) (hd₀ : 0 < d₀) (hδ : 0 < δ)
    (h_ready : ready_for_quench_exploration_mass η d₀ δ hd₀ hδ) :
    (∏ i, (1 - η i)) * d₀ ≤ δ := by
  calc (∏ i, (1 - η i)) * d₀
      ≤ Real.exp (- exploration_mass η) * d₀ :=
        exploration_mass_mixing_bound η hη_nonneg hη_lt_one d₀ (le_of_lt hd₀)
    _ ≤ δ := mixing_guarantee d₀ δ hd₀ hδ (exploration_mass η) h_ready

/-! ## Summary

This module establishes the mathematical foundation for **exploration mass control**:

1. **Product-to-exponential**: ∏(1-ηᵢ) ≤ exp(-Σηᵢ)
2. **Exploration mass**: M = Σηₜ (accumulated noise injection)
3. **Mixing bound**: distance ≤ exp(-M) × d₀
4. **Threshold**: M_explore = log(d₀/δ)
5. **Guarantee**: M ≥ M_explore ⟹ distance ≤ δ

**Key Insight**: The quench trigger is now **exogenous** (based on our noise injection)
but **principled** (derived from mixing theory). This breaks the feedback loop that
traps entropy-triggered controllers while providing mathematical guarantees.

**Usage in Python Controller**:
```python
# During heat phase, accumulate exploration mass
exploration_mass += noise_strength * tau_opt  # Per Markov step

# Quench when exploration mass exceeds threshold
M_explore = log(d0 / delta)
if exploration_mass >= M_explore:
    trigger_quench()
```
-/

end SGC.Observables.ExplorationMass
