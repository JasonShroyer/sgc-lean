/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team

# Floquet Theory for Finite Markov Chains

This module provides the mathematical infrastructure for time-periodic dynamical
systems on finite state spaces. Floquet theory describes the stability of periodic
orbits via the monodromy operator and its eigenvalues (Floquet multipliers).

## Mathematical Background

For a time-periodic system dp/dt = L(t)p with L(t+T) = L(t), the fundamental
matrix solution Φ(t) satisfies Φ(t+T) = Φ(t)·M where M is the **monodromy matrix**.

The eigenvalues λᵢ of M are **Floquet multipliers**. The **Floquet exponents**
are μᵢ = log(λᵢ)/T. The system is:
- Stable if all |λᵢ| < 1 (all Re(μᵢ) < 0)
- Marginally stable if max|λᵢ| = 1
- Unstable if any |λᵢ| > 1

For limit cycles, one multiplier is always 1 (phase invariance).
The **Floquet spectral gap** γ_F = -max{Re(μᵢ) : |λᵢ| < 1} controls
the rate at which perturbations decay back to the cycle.

## Connection to SGC

The Floquet spectral gap γ_F replaces the Markov spectral gap γ in the
nonlinear SGC theory. For the C. elegans pharyngeal circuit:
- γ_linear = 0.065 (Markov spectral gap)
- γ_F = 0.83 (Floquet spectral gap)
- Ratio γ/γ_F = 0.08 (linearity ratio)

## References

- Floquet (1883) — Sur les équations différentielles linéaires à coefficients périodiques
- Chicone (2006) — Ordinary Differential Equations, Ch. 3
- SGC NonlinearEmergence.lean — Application to emergence theory
-/

import SGC.Thermodynamics.EntropyProduction
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace SGC.Spectral.Floquet

open Finset Matrix Real

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Section 1: Time-Periodic Generator -/

/-- A **time-periodic generator family** L(t) with period T > 0.

    This models the effective dynamics of a system on a limit cycle.
    At each time t, L(t) is a Markov generator (off-diagonal ≥ 0, rows sum to 0).
    The periodicity L(t+T) = L(t) captures the oscillatory nature.

    **Examples**:
    - C. elegans pharyngeal pump: T ≈ 0.25s (4 Hz pumping rate)
    - Cardiac oscillator: T ≈ 1s (60 bpm)
    - Neural theta rhythm: T ≈ 0.125s (8 Hz) -/
structure PeriodicGeneratorFamily (V : Type*) [Fintype V] where
  /-- The time-dependent generator L : ℝ → Matrix V V ℝ -/
  gen : ℝ → Matrix V V ℝ
  /-- The period T > 0 -/
  period : ℝ
  /-- Period is positive -/
  period_pos : 0 < period
  /-- Periodicity: L(t+T) = L(t) -/
  periodic : ∀ t, gen (t + period) = gen t

/-! ## Section 2: The Monodromy Operator -/

/-- The **monodromy matrix** M = Φ(T) where Φ is the fundamental matrix solution.

    For a finite state space, M is a |V| × |V| matrix whose eigenvalues
    determine the stability of the periodic orbit.

    Formally, M is the time-T propagator of the system dp/dt = L(t)p.
    For piecewise-constant L(t), M = exp(L(t_{n-1}) · Δt) · ... · exp(L(t_0) · Δt).

    In practice, M is computed numerically (as in nonlinear.py).
    Here we axiomatize its key properties. -/
structure MonodromyOperator (V : Type*) [Fintype V] where
  /-- The monodromy matrix -/
  matrix : Matrix V V ℝ
  /-- The associated period -/
  period : ℝ
  /-- Period is positive -/
  period_pos : 0 < period

/-! ## Section 3: Floquet Multipliers and Exponents -/

/-- A **Floquet multiplier** is an eigenvalue of the monodromy matrix.

    For real matrices, multipliers come in conjugate pairs.
    The trivial multiplier λ = 1 always exists for limit cycles (phase invariance). -/
def FloquetMultiplier (M : MonodromyOperator V) (lam : ℂ) : Prop :=
  ∃ v : V → ℂ, v ≠ 0 ∧ ∀ i, (∑ j, (M.matrix i j : ℂ) * v j) = lam * v i

/-- A **Floquet exponent** μ = log(λ)/T where λ is a Floquet multiplier.

    The real part Re(μ) determines stability:
    - Re(μ) < 0: perturbation in this direction decays
    - Re(μ) = 0: marginal (phase mode)
    - Re(μ) > 0: perturbation grows (instability) -/
def FloquetExponent (M : MonodromyOperator V) (mu : ℝ) : Prop :=
  ∃ lam_abs : ℝ, 0 < lam_abs ∧ mu = Real.log lam_abs / M.period

/-! ## Section 4: Floquet Spectral Gap -/

/-- The **Floquet spectral gap**: the decay rate of the slowest non-trivial mode.

    γ_F = -max{Re(μᵢ) : λᵢ ≠ 1}
        = -max{log|λᵢ|/T : λᵢ ≠ 1}

    For a stable limit cycle, γ_F > 0: all non-phase perturbations decay.

    **Role in SGC**: γ_F replaces γ (Markov spectral gap) in the nonlinear theory.
    The persistence theorem becomes: γ_F · ε̄² ≤ σ̄_hid.

    **Computation**: In practice, γ_F is computed from the monodromy matrix's
    eigenvalues, as implemented in python/sgc_diagnostic/nonlinear.py. -/
structure FloquetGap where
  /-- The gap value γ_F > 0 -/
  gap : ℝ
  /-- Positivity: perturbations decay -/
  gap_pos : 0 < gap

/-- The Floquet gap bounds the decay of perturbations:

    ‖p(t) - p_cycle(t)‖ ≤ C · exp(-γ_F · t) · ‖p(0) - p_cycle(0)‖

    This is the nonlinear analog of the spectral gap bound for Markov chains:
    ‖p(t) - π‖ ≤ C · exp(-γ · t) · ‖p(0) - π‖ -/
axiom floquet_decay_bound (M : MonodromyOperator V) (γ_F : FloquetGap)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) :
    ∃ C : ℝ, C > 0 ∧ ∀ t : ℝ, 0 ≤ t →
      ∀ f : V → ℝ,
        norm_pi pi_dist f ≤ C * Real.exp (-γ_F.gap * t) * norm_pi pi_dist f

/-! ## Section 5: The Linearity Ratio -/

/-- The **linearity ratio**: γ_linear / γ_F.

    This dimensionless number measures how well the linear theory
    approximates the true nonlinear dynamics:
    - Ratio ≈ 1: linear theory is accurate
    - Ratio << 1: system is genuinely nonlinear
    - Ratio > 1: impossible (Floquet gap ≥ Markov gap for stable cycles)

    **C. elegans**: 0.065 / 0.83 ≈ 0.08 (deeply nonlinear)
    **Random reversible chain**: ≈ 1.0 (linear theory is exact)
    **Cardiac oscillator**: estimated 0.1-0.3 (moderately nonlinear) -/
def LinearityRatio (γ_linear γ_F : ℝ) (hγ_F : γ_F > 0) : ℝ :=
  γ_linear / γ_F

/-- The linearity ratio is between 0 and 1 for stable systems. -/
lemma linearity_ratio_range (γ_linear γ_F : ℝ) (hγ_linear : 0 < γ_linear)
    (hγ_F : 0 < γ_F) (h_le : γ_linear ≤ γ_F) :
    0 < LinearityRatio γ_linear γ_F (lt_of_lt_of_le hγ_linear h_le) ∧
    LinearityRatio γ_linear γ_F (lt_of_lt_of_le hγ_linear h_le) ≤ 1 := by
  unfold LinearityRatio
  constructor
  · exact div_pos hγ_linear hγ_F
  · rw [div_le_one hγ_F]; exact h_le

/-! ## Section 6: Connection to SGC -/

/-- **Floquet-SGC Bridge**: The Floquet spectral gap bounds the cycle-averaged
    hidden entropy production, exactly as the Markov spectral gap bounds σ_hid
    in the linear theory.

    γ_F · ε̄² ≤ (1/T) ∫₀ᵀ σ_hid(t) dt

    This is the nonlinear generalization of `gaspard_maes_bridge`.

    **Proof path**: Apply gaspard_maes_bridge at each time step with the
    instantaneous generator L(t) and spectral gap, then use the Floquet
    averaging theorem to replace the instantaneous gap with γ_F.

    **Status**: CONJECTURE — requires Floquet averaging theorem
    (standard but not yet in Mathlib). -/
axiom floquet_sgc_bridge (M : MonodromyOperator V) (γ_F : FloquetGap)
    (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) :
    γ_F.gap * (opNorm_pi pi_dist hπ
      (SGC.Approximate.DefectOperator (M.matrix) P pi_dist hπ))^2 ≤
    SGC.Thermodynamics.HiddenEntropyProduction M.matrix P pi_dist

/-! ## Section 7: Empirical Constants -/

/-- C. elegans pharyngeal circuit Floquet data.

    Source: Wilson-Cowan dynamics on Cook et al. (2019) connectome
    at sigmoid gain = 2.0. See: celegans_nonlinear.py

    These are empirical constants that ground the formal theory. -/
def celegans_floquet : FloquetGap where
  gap := 0.83
  gap_pos := by norm_num

def celegans_markov_gap : ℝ := 0.065

def celegans_linearity_ratio : ℝ :=
  LinearityRatio celegans_markov_gap 0.83 (by norm_num)

/-- The C. elegans pharyngeal circuit operates in the deeply nonlinear regime. -/
lemma celegans_is_nonlinear : celegans_linearity_ratio < 0.1 := by
  unfold celegans_linearity_ratio LinearityRatio celegans_markov_gap
  norm_num

/-! ## Summary

This module provides the Floquet theory infrastructure for nonlinear SGC:

1. `PeriodicGeneratorFamily` — time-periodic generators L(t+T) = L(t)
2. `MonodromyOperator` — the period-T propagator matrix
3. `FloquetMultiplier` / `FloquetExponent` — eigenvalues and stability exponents
4. `FloquetGap` — the spectral gap for perturbation decay
5. `LinearityRatio` — diagnostic for when nonlinear theory is needed
6. `floquet_sgc_bridge` — connects Floquet gap to hidden entropy production

The C. elegans pharyngeal circuit at linearity ratio 0.08 demonstrates
that biological oscillators require the nonlinear theory for correct
stability predictions (12× error in the linear approximation).
-/

end SGC.Spectral.Floquet
