/-
Copyright (c) 2025 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team

# Coupled Exploration Mass: κ-Weighted Mixing with Spectral Efficiency

This module extends the Exploration Mass framework with a **coupling coefficient** κ
that captures the efficiency of noise injection—how much of the injected noise
actually couples to the loss-relevant/representation-relevant subspace.

## Motivation

In Phase-5.1, we observed an 87× gap between theoretical threshold M_theory ≈ 2.3
and practical threshold M_actual ≈ 200. This "mixing inefficiency" arises because
most injected noise lands in directions that don't affect the coarse state.

The α-inefficiency theorem formalizes this: if only fraction κ of noise produces
contraction, the threshold scales as M ≥ (1/κ) × log(d₀/δ).

## Physical Interpretation

κ is the **emissivity** or **spectral coupling coefficient**:
- In blackbody physics: ε measures how efficiently a surface radiates
- In field theory: coupling strength between noise and relevant operators
- In neural networks: overlap between perturbation and loss-relevant subspace

## Main Results

1. `coupled_contraction_product_bound`: ∏(1-κᵢηᵢ) ≤ exp(-Σκᵢηᵢ)
2. `effective_exploration_mass`: M_eff = Σκₜηₜ (coupling-weighted mass)
3. `coupled_mixing_bound`: distance ≤ exp(-M_eff) × d₀
4. `coupled_mixing_guarantee`: M_eff ≥ log(d₀/δ) ⟹ distance ≤ δ
5. `inefficient_mixing_threshold`: M ≥ (1/κ) × log(d₀/δ) for constant κ

## Connection to Wavelet-Coupled Control

The κ coefficient can be made time-varying (κₜ) and estimated from:
- Spectral overlap between noise and slow manifold
- Frame tightness bounds from wavelet analysis
- Empirical contraction rates in distance proxy

This enables "spectral matching": design noise to maximize κ, reducing total M needed.

## References

- ExplorationMass.lean (base mixing theorem)
- Stefan-Boltzmann law (emissivity analogy)
- Fluctuation-dissipation theorem (noise-bath coupling)
-/

import SGC.Observables.ExplorationMass
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace SGC.Observables.ExplorationMassCoupled

open Finset Real BigOperators SGC.Observables.ExplorationMass

/-! ### 1. Coupled Contraction with κ-Efficiency -/

/-- **Effective exploration mass**: The coupling-weighted accumulated noise.
    M_eff = Σₜ κₜηₜ where κₜ ∈ [0,1] is the coupling efficiency at step t
    and ηₜ ∈ [0,1] is the noise strength.

    This generalizes `exploration_mass` by weighting each noise injection
    by how efficiently it couples to the relevant degrees of freedom. -/
def effective_exploration_mass {n : ℕ} (κ η : Fin n → ℝ) : ℝ :=
  ∑ i, κ i * η i

/-- Effective exploration mass is non-negative when coupling and noise are non-negative. -/
lemma effective_exploration_mass_nonneg {n : ℕ} (κ η : Fin n → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (hη : ∀ i, 0 ≤ η i) :
    0 ≤ effective_exploration_mass κ η := by
  unfold effective_exploration_mass
  exact sum_nonneg (fun i _ => mul_nonneg (hκ i) (hη i))

/-- Effective exploration mass bounded by nominal mass when κ ≤ 1. -/
lemma effective_exploration_mass_le_nominal {n : ℕ} (κ η : Fin n → ℝ)
    (hκ_le_one : ∀ i, κ i ≤ 1) (hη_nonneg : ∀ i, 0 ≤ η i) :
    effective_exploration_mass κ η ≤ exploration_mass η := by
  unfold effective_exploration_mass exploration_mass
  apply sum_le_sum
  intro i _
  calc κ i * η i ≤ 1 * η i := mul_le_mul_of_nonneg_right (hκ_le_one i) (hη_nonneg i)
    _ = η i := one_mul _

/-! ### 2. Coupled Product Bound -/

/-- **Coupled contraction product bound**:
    For sequences (κᵢ) and (ηᵢ) with κᵢηᵢ ∈ [0,1],
    ∏ᵢ (1 - κᵢηᵢ) ≤ exp(-Σᵢ κᵢηᵢ) = exp(-M_eff)

    This is the direct application of `contraction_product_bound` to the
    sequence aᵢ = κᵢηᵢ, which represents the *effective* contraction per step. -/
theorem coupled_contraction_product_bound {n : ℕ} (κ η : Fin n → ℝ)
    (h_nonneg : ∀ i, 0 ≤ κ i * η i) (h_lt_one : ∀ i, κ i * η i < 1) :
    ∏ i, (1 - κ i * η i) ≤ Real.exp (- effective_exploration_mass κ η) := by
  -- Define the effective contraction sequence a_i = κ_i * η_i
  let a : Fin n → ℝ := fun i => κ i * η i
  -- Apply the base contraction_product_bound
  have h := contraction_product_bound a h_nonneg h_lt_one
  -- The sums match: Σ a_i = Σ κ_i * η_i = M_eff
  convert h using 2

/-! ### 3. Coupled Mixing Bound -/

/-- **Coupled Exploration Mass Mixing Bound**:
    If each step contracts distance by factor (1-κₜηₜ), then after n steps:
    d(μₙ, π) ≤ exp(-M_eff) × d(μ₀, π)
    where M_eff = Σκₜηₜ is the effective exploration mass.

    This generalizes `exploration_mass_mixing_bound` to account for coupling efficiency.

    **Physical Meaning**: The 87× gap observed in Phase-5.1 (M_theory ≈ 2.3 vs M_actual ≈ 200)
    corresponds to κ ≈ 0.01—only ~1% of injected noise couples to relevant modes. -/
theorem coupled_mixing_bound {n : ℕ} (κ η : Fin n → ℝ)
    (h_nonneg : ∀ i, 0 ≤ κ i * η i) (h_lt_one : ∀ i, κ i * η i < 1)
    (d₀ : ℝ) (hd₀_nonneg : 0 ≤ d₀) :
    (∏ i, (1 - κ i * η i)) * d₀ ≤ Real.exp (- effective_exploration_mass κ η) * d₀ := by
  by_cases hd₀ : d₀ = 0
  · simp [hd₀]
  · have hd₀_pos : 0 < d₀ := lt_of_le_of_ne hd₀_nonneg (Ne.symm hd₀)
    apply mul_le_mul_of_nonneg_right _ (le_of_lt hd₀_pos)
    exact coupled_contraction_product_bound κ η h_nonneg h_lt_one

/-! ### 4. Coupled Mixing Threshold -/

/-- **Effective Exploration Mass Threshold**: The minimum effective exploration mass
    needed to guarantee mixing to within tolerance δ from initial distance d₀.

    M_eff_threshold = log(d₀/δ)

    This is the same threshold as the uncoupled case, but now applies to M_eff = Σκₜηₜ
    rather than M = Σηₜ. -/
def effective_threshold (d₀ δ : ℝ) (hd₀ : 0 < d₀) (hδ : 0 < δ) : ℝ :=
  exploration_mass_threshold d₀ δ hd₀ hδ

/-- **Coupled Mixing Guarantee**: When effective exploration mass exceeds the threshold,
    distance to equilibrium is within tolerance δ.

    If M_eff ≥ log(d₀/δ), then exp(-M_eff) × d₀ ≤ δ. -/
theorem coupled_mixing_guarantee (d₀ δ : ℝ) (hd₀ : 0 < d₀) (hδ : 0 < δ)
    (M_eff : ℝ) (hM : M_eff ≥ effective_threshold d₀ δ hd₀ hδ) :
    Real.exp (-M_eff) * d₀ ≤ δ := by
  -- This is exactly mixing_guarantee applied to M_eff
  exact mixing_guarantee d₀ δ hd₀ hδ M_eff hM

/-- **Quench Readiness with Coupling**:
    If the effective exploration mass (coupling-weighted) exceeds the threshold,
    then the stepwise-contracted distance is within tolerance.

    This is the full "controller correctness" theorem. -/
theorem coupled_quench_ready_implies_mixed {n : ℕ} (κ η : Fin n → ℝ)
    (h_nonneg : ∀ i, 0 ≤ κ i * η i) (h_lt_one : ∀ i, κ i * η i < 1)
    (d₀ δ : ℝ) (hd₀ : 0 < d₀) (hδ : 0 < δ)
    (h_ready : effective_exploration_mass κ η ≥ effective_threshold d₀ δ hd₀ hδ) :
    (∏ i, (1 - κ i * η i)) * d₀ ≤ δ := by
  calc (∏ i, (1 - κ i * η i)) * d₀
      ≤ Real.exp (- effective_exploration_mass κ η) * d₀ :=
        coupled_mixing_bound κ η h_nonneg h_lt_one d₀ (le_of_lt hd₀)
    _ ≤ δ := coupled_mixing_guarantee d₀ δ hd₀ hδ (effective_exploration_mass κ η) h_ready

/-! ### 5. Constant Coupling (α-Inefficiency) -/

/-- **Constant Coupling Simplification**: When κₜ = α for all t (constant coupling),
    the effective exploration mass becomes M_eff = α × M where M = Σηₜ.

    This is the "α-inefficiency" model: uniform coupling coefficient α ∈ (0,1]. -/
lemma effective_mass_constant_coupling {n : ℕ} (α : ℝ) (η : Fin n → ℝ) :
    effective_exploration_mass (fun _ => α) η = α * exploration_mass η := by
  unfold effective_exploration_mass exploration_mass
  rw [← mul_sum]

/-- **Inefficient Mixing Threshold**: For constant coupling α, the threshold on
    *nominal* mass M = Σηₜ becomes M ≥ (1/α) × log(d₀/δ).

    This explains the 87× gap: if α ≈ 0.01, then M_threshold ≈ 100 × log(d₀/δ).

    **Physical Meaning**: α is the "emissivity" of the noise injection—how much
    of the thermal energy actually couples to the modes that matter for mixing. -/
theorem inefficient_mixing_threshold (α : ℝ) (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (d₀ δ : ℝ) (hd₀ : 0 < d₀) (hδ : 0 < δ) :
    ∀ M : ℝ, M ≥ (1 / α) * Real.log (d₀ / δ) →
      α * M ≥ Real.log (d₀ / δ) := by
  intro M hM
  have h1 : α * M ≥ α * ((1 / α) * Real.log (d₀ / δ)) := by
    apply mul_le_mul_of_nonneg_left hM (le_of_lt hα_pos)
  calc α * M
      ≥ α * ((1 / α) * Real.log (d₀ / δ)) := h1
    _ = (α * (1 / α)) * Real.log (d₀ / δ) := by ring
    _ = 1 * Real.log (d₀ / δ) := by rw [mul_one_div_cancel (ne_of_gt hα_pos)]
    _ = Real.log (d₀ / δ) := one_mul _

/-- **Calibrated Threshold Formula**: The practical threshold for nominal mass
    when coupling efficiency is α.

    M_threshold_calibrated = (1/α) × log(d₀/δ)

    For α = 0.01 (1% efficiency), d₀ = 1, δ = 0.1:
    M_threshold = 100 × log(10) ≈ 230

    This matches the empirical finding of M ≈ 200 in Phase-5.1. -/
def calibrated_threshold (α d₀ δ : ℝ) (hα : 0 < α) (hd₀ : 0 < d₀) (hδ : 0 < δ) : ℝ :=
  (1 / α) * Real.log (d₀ / δ)

/-- The calibrated threshold is positive when d₀ > δ. -/
lemma calibrated_threshold_pos (α d₀ δ : ℝ) (hα : 0 < α) (hd₀ : 0 < d₀) (hδ : 0 < δ)
    (h_ge : d₀ > δ) : 0 < calibrated_threshold α d₀ δ hα hd₀ hδ := by
  unfold calibrated_threshold
  apply mul_pos
  · exact one_div_pos.mpr hα
  · rw [Real.log_pos_iff (le_of_lt (div_pos hd₀ hδ))]
    exact (one_lt_div hδ).mpr h_ge

/-! ### 6. Controller Correctness Theorem -/

/-- **Controller Correctness (Constant α)**:
    Given a constant coupling efficiency α and noise schedule (ηₜ),
    if the nominal mass M = Σηₜ exceeds (1/α) × log(d₀/δ),
    then the system has mixed to within tolerance δ.

    This is the "executable safety guarantee" for the exploration mass controller. -/
theorem controller_correctness_constant_alpha {n : ℕ} (α : ℝ) (η : Fin n → ℝ)
    (hα_pos : 0 < α) (hα_le_one : α ≤ 1)
    (hη_nonneg : ∀ i, 0 ≤ η i) (hη_lt_one_over_α : ∀ i, η i < 1 / α)
    (d₀ δ : ℝ) (hd₀ : 0 < d₀) (hδ : 0 < δ)
    (h_threshold : exploration_mass η ≥ calibrated_threshold α d₀ δ hα_pos hd₀ hδ) :
    (∏ i, (1 - α * η i)) * d₀ ≤ δ := by
  -- Convert to effective mass formulation
  have h_eff : effective_exploration_mass (fun _ => α) η ≥ effective_threshold d₀ δ hd₀ hδ := by
    rw [effective_mass_constant_coupling]
    unfold effective_threshold exploration_mass_threshold calibrated_threshold at *
    calc α * exploration_mass η
        ≥ α * ((1 / α) * Real.log (d₀ / δ)) := by
          apply mul_le_mul_of_nonneg_left h_threshold (le_of_lt hα_pos)
      _ = Real.log (d₀ / δ) := by field_simp
  -- Verify contraction bounds
  have h_nonneg : ∀ i, 0 ≤ α * η i := fun i => mul_nonneg (le_of_lt hα_pos) (hη_nonneg i)
  have h_lt_one : ∀ i, α * η i < 1 := by
    intro i
    calc α * η i < α * (1 / α) := mul_lt_mul_of_pos_left (hη_lt_one_over_α i) hα_pos
      _ = 1 := mul_one_div_cancel (ne_of_gt hα_pos)
  -- Apply coupled quench theorem
  exact coupled_quench_ready_implies_mixed (fun _ => α) η h_nonneg h_lt_one d₀ δ hd₀ hδ h_eff

/-! ## Summary

This module establishes the mathematical foundation for **coupling-aware exploration mass control**:

1. **Effective mass**: M_eff = Σκₜηₜ (coupling-weighted accumulation)
2. **Coupled contraction**: ∏(1-κᵢηᵢ) ≤ exp(-M_eff)
3. **Mixing guarantee**: M_eff ≥ log(d₀/δ) ⟹ distance ≤ δ
4. **Calibration**: For constant κ=α, threshold becomes M ≥ (1/α)log(d₀/δ)
5. **Controller correctness**: Executable safety guarantee for the trigger

**Key Insight**: The 87× empirical gap is not a failure of the theory but reveals
a physical parameter α ≈ 0.01—the "emissivity" of noise injection. This opens
the path to **spectral matching**: design noise to maximize κ, reducing total M needed.

**Usage in Python Controller (Phase-6)**:
```python
# Track both nominal and effective mass
M_nominal += noise_scale * epoch_delta
kappa = compute_coupling_coefficient(...)  # Spectral overlap estimator
M_eff += kappa * noise_scale * epoch_delta

# Quench when effective mass exceeds threshold
M_eff_threshold = log(d0 / delta)
if M_eff >= M_eff_threshold:
    trigger_quench()
```
-/

end SGC.Observables.ExplorationMassCoupled
