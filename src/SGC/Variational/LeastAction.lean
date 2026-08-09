/-
Copyright (c) 2024 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Thermodynamics.DoobMeyer

/-!
# Variational Principle for Predictable Drift

This module derives the kinematic driver of complexity accumulation by proving 
that minimizing the thermodynamic action functional implies maximization of 
the predictable drift component.

## Theoretical Background

Building on the Doob-Meyer decomposition S = M + A from `DoobMeyer.lean`, 
this module establishes that the irreversible accumulation of the predictable 
process A_n follows from supermartingale convergence properties combined with 
a variational optimality condition.

## Main Definitions

- `ExtropicPotential`: Ψ(x) = π(x) - certainty/consolidation measure
- `OptimalTransition`: P* that greedily minimizes expected surprise
- `DriftMagnitude`: |ΔA| = |E[Φ(X')|X] - Φ(X)| measuring consolidation rate

## Main Theorem

**Drift Maximization**: Under the optimal (action-minimizing) transition,
the magnitude of predictable drift is maximized. This follows from a 
variational principle on the expected surprise functional.

## Structure

1. **Doob-Meyer**: Decomposes surprise into predictable (A) and martingale (M)
2. **Optimality**: Defines locally optimal transitions minimizing expected surprise
3. **Variational Result**: Proves optimal transitions maximize |ΔA|

## References

* [Doob] Stochastic Processes
* [Friston] The Free Energy Principle

-/

namespace SGC

open Finset BigOperators Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### 1. The Stationary Density -/

/-- The **stationary density** π(x).

    **Interpretation Note:** In the SGC framework, we interpret this function as the 
    **Extropic Potential** or "Certainty". It serves as the Bregman dual to the 
    entropic "Surprise" potential Φ(x) = -log π(x). Where Φ measures 
    uncertainty, this function measures the system's consolidation.
    
    Maximizing π is equivalent to minimizing Φ (for log-convex π). -/
def stationary_density (pi_dist : V → ℝ) : V → ℝ := pi_dist

/-- Stationary density is positive for positive distributions. -/
lemma stationary_density_pos (pi_dist : V → ℝ) (hπ : ∀ x, 0 < pi_dist x) (x : V) :
    0 < stationary_density pi_dist x := hπ x

/-- Stationary density is bounded above by 1 for probability distributions. -/
lemma stationary_density_bounded (pi_dist : V → ℝ) (hπ : ∀ x, 0 < pi_dist x) 
    (h_sum : ∑ x, pi_dist x = 1) (x : V) :
    stationary_density pi_dist x ≤ 1 := by
  simp only [stationary_density]
  have h : pi_dist x ≤ ∑ y, pi_dist y := single_le_sum (fun y _ => le_of_lt (hπ y)) (mem_univ x)
  rw [h_sum] at h
  exact h

/-! ### 2. The Thermodynamic Gradient -/

/-- The **local surprise gradient** at state x: how much expected surprise decreases.
    
    ∇Φ(x) = Φ(x) - E[Φ(X') | X = x] = -predictableIncrement
    
    Positive gradient means surprise is expected to decrease (consolidation). -/
noncomputable def surprise_gradient (P : Matrix V V ℝ) (pi_dist : V → ℝ) (hπ : ∀ x, 0 < pi_dist x) 
    (x : V) : ℝ :=
  SurprisePotential pi_dist hπ x - condExp P (SurprisePotential pi_dist hπ) x

/-- The surprise gradient is the negative of predictable increment. -/
theorem surprise_gradient_eq_neg_drift (P : Matrix V V ℝ) (pi_dist : V → ℝ) 
    (hπ : ∀ x, 0 < pi_dist x) (x : V) :
    surprise_gradient P pi_dist hπ x = -predictableIncrement P (SurprisePotential pi_dist hπ) x := by
  simp only [surprise_gradient, predictableIncrement]
  ring

/-- Supermartingale property implies positive gradient (consolidation). -/
theorem supermartingale_positive_gradient (P : Matrix V V ℝ) (pi_dist : V → ℝ) 
    (hπ : ∀ x, 0 < pi_dist x) 
    (h : IsSupermartingale P (SurprisePotential pi_dist hπ)) (x : V) :
    0 ≤ surprise_gradient P pi_dist hπ x := by
  rw [surprise_gradient_eq_neg_drift]
  have h_nonpos := supermartingale_predictable_nonpos P (SurprisePotential pi_dist hπ) h x
  linarith

/-! ### 3. Optimal Transitions: Greedy Surprise Minimization -/

/-- A transition matrix P is **locally optimal** at x if it minimizes expected surprise.
    
    This formalizes the thermodynamic drive: at each state x, the system
    "chooses" transitions that most rapidly decrease surprise.
    
    Mathematically: P is optimal if condExp P Φ x ≤ condExp Q Φ x for all Q. -/
def IsLocallyOptimal (P Q : Matrix V V ℝ) (Φ : V → ℝ) (x : V) : Prop :=
  condExp P Φ x ≤ condExp Q Φ x

/-- P is **globally optimal** if it's locally optimal everywhere. -/
def IsGloballyOptimal (P : Matrix V V ℝ) (Φ : V → ℝ) 
    (Transitions : Set (Matrix V V ℝ)) : Prop :=
  ∀ Q ∈ Transitions, ∀ x, IsLocallyOptimal P Q Φ x

/-- The **greedy transition** concentrates probability on the minimum-surprise successor.
    
    For each x, P*_{xy} = 1 if y = argmin_z Φ(z) among neighbors, 0 otherwise.
    This is the "steepest descent" strategy. -/
def IsGreedyTransition (P : Matrix V V ℝ) (Φ : V → ℝ) : Prop :=
  ∀ x, ∃ y_min, (∀ y, Φ y_min ≤ Φ y ∨ P x y = 0) ∧ 
                 P x y_min > 0 ∧ 
                 ∑ y, P x y = 1

/-! ### 4. The Action Functional -/

/-- The **single-step action** at state x: the expected surprise.
    
    A(x; P) = E[Φ(X') | X = x] = Σ_y P_{xy} Φ(y)
    
    Lower action means more efficient consolidation. -/
def stepAction (P : Matrix V V ℝ) (Φ : V → ℝ) (x : V) : ℝ :=
  condExp P Φ x

/-- The **weighted total action** over the state space.
    
    Action(P) = Σ_x π(x) * E[Φ(X') | X = x]
    
    This is the expected surprise under stationary distribution. -/
noncomputable def totalAction (P : Matrix V V ℝ) (Φ : V → ℝ) (pi_dist : V → ℝ) : ℝ :=
  ∑ x, pi_dist x * stepAction P Φ x

/-- Lower action implies more negative drift (more consolidation). -/
theorem lower_action_stronger_drift (P : Matrix V V ℝ) (Φ : V → ℝ) (x : V) :
    stepAction P Φ x = Φ x + predictableIncrement P Φ x := by
  simp only [stepAction, predictableIncrement, condExp]
  ring

/-! ### 5. The Drift Maximization Theorem -/

/-- The **drift magnitude** at x: |ΔA(x)| = |E[Φ(X')|X=x] - Φ(x)|.
    
    For consolidating systems (supermartingale), this equals -(ΔA)
    since ΔA ≤ 0. -/
def driftMagnitude (P : Matrix V V ℝ) (Φ : V → ℝ) (x : V) : ℝ :=
  |predictableIncrement P Φ x|

/-- For supermartingales, drift magnitude equals negative drift. -/
theorem drift_magnitude_supermartingale (P : Matrix V V ℝ) (Φ : V → ℝ) 
    (h : IsSupermartingale P Φ) (x : V) :
    driftMagnitude P Φ x = -(predictableIncrement P Φ x) := by
  simp only [driftMagnitude]
  have h_nonpos := supermartingale_predictable_nonpos P Φ h x
  exact abs_of_nonpos h_nonpos

/-- **Optimal Drift Lemma**: Locally optimal transitions maximize drift magnitude.
    
    If P is locally optimal at x (minimizes E[Φ|X=x]), then P maximizes
    the consolidation rate |ΔA(x)| among all supermartingale transitions.
    
    Proof: ΔA = E[Φ|X=x] - Φ(x). For supermartingales, ΔA ≤ 0.
    Minimizing E[Φ|X=x] makes ΔA more negative, thus |ΔA| larger. -/
theorem optimal_maximizes_drift (P Q : Matrix V V ℝ) (Φ : V → ℝ) (x : V)
    (hP_super : IsSupermartingale P Φ) (hQ_super : IsSupermartingale Q Φ)
    (h_opt : IsLocallyOptimal P Q Φ x) :
    driftMagnitude Q Φ x ≤ driftMagnitude P Φ x := by
  rw [drift_magnitude_supermartingale P Φ hP_super x]
  rw [drift_magnitude_supermartingale Q Φ hQ_super x]
  simp only [predictableIncrement]
  -- P optimal means condExp P Φ x ≤ condExp Q Φ x
  -- So -(condExp P Φ x - Φ x) ≥ -(condExp Q Φ x - Φ x)
  -- h_opt : condExp P Φ x ≤ condExp Q Φ x
  -- Goal: -(condExp Q Φ x - Φ x) ≤ -(condExp P Φ x - Φ x)
  have h := h_opt
  simp only [IsLocallyOptimal] at h
  linarith

/-! ### 6. The Principle of Least Action -/

/-- **The Variational Principle**: Among supermartingale transitions, 
    minimum action implies maximum consolidation.
    
    Σ_x π(x) |ΔA_P(x)| ≥ Σ_x π(x) |ΔA_Q(x)| when P minimizes action. -/
theorem least_action_maximizes_drift (P Q : Matrix V V ℝ) (Φ : V → ℝ) 
    (pi_dist : V → ℝ) (hπ : ∀ x, 0 < pi_dist x)
    (hP_super : IsSupermartingale P Φ) (hQ_super : IsSupermartingale Q Φ)
    (h_opt : ∀ x, IsLocallyOptimal P Q Φ x) :
    ∑ x, pi_dist x * driftMagnitude Q Φ x ≤ 
    ∑ x, pi_dist x * driftMagnitude P Φ x := by
  apply sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left
  · exact optimal_maximizes_drift P Q Φ x hP_super hQ_super (h_opt x)
  · exact le_of_lt (hπ x)

/-! ### 7. The Complete Kinetic Picture -/

/-- **Variational Optimality**: Combines action minimization with drift maximization.
    
    For a system with:
    1. Surprise potential Φ = -log π
    2. Supermartingale dynamics
    3. Locally optimal transitions (minimizing expected surprise)
    
    The optimal transition P satisfies:
    - Action(π, P) ≤ Action(π, Q) for comparison Q
    - Σ π(x)|ΔA_P(x)| ≥ Σ π(x)|ΔA_Q(x)|
    
    This follows from the variational structure of the expected surprise functional. -/
theorem variational_drift_optimality (P Q : Matrix V V ℝ) (pi_dist : V → ℝ) 
    (hπ : ∀ x, 0 < pi_dist x) (_hP : IsStochastic P) (_hQ : IsStochastic Q)
    (hP_super : IsSupermartingale P (SurprisePotential pi_dist hπ))
    (hQ_super : IsSupermartingale Q (SurprisePotential pi_dist hπ))
    (h_P_optimal : ∀ x, IsLocallyOptimal P Q (SurprisePotential pi_dist hπ) x) :
    -- P minimizes action
    totalAction P (SurprisePotential pi_dist hπ) pi_dist ≤ 
    totalAction Q (SurprisePotential pi_dist hπ) pi_dist ∧
    -- P maximizes complexity growth
    ∑ x, pi_dist x * driftMagnitude Q (SurprisePotential pi_dist hπ) x ≤ 
    ∑ x, pi_dist x * driftMagnitude P (SurprisePotential pi_dist hπ) x := by
  constructor
  · -- Action minimization
    simp only [totalAction, stepAction]
    apply sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left (h_P_optimal x) (le_of_lt (hπ x))
  · -- Drift maximization
    exact least_action_maximizes_drift P Q (SurprisePotential pi_dist hπ) 
          pi_dist hπ hP_super hQ_super h_P_optimal

/-! ### 8. Gradient-Drift Equivalence -/

/-- **Gradient-Drift Identity**: For supermartingale dynamics, the surprise 
    gradient equals the drift magnitude.
    
    Given:
    - A stochastic matrix P with positive stationary distribution π
    - Supermartingale property: E[Φ(X')|π] ≤ Φ(X)
    
    Then: ∇Φ(x) = |ΔA(x)| for all states x.
    
    This establishes that consolidation rate equals the local gradient magnitude. -/
theorem gradient_drift_equivalence (P : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ x, 0 < pi_dist x) (_hP : IsStochastic P)
    (h_super : IsSupermartingale P (SurprisePotential pi_dist hπ)) :
    ∀ x, surprise_gradient P pi_dist hπ x = driftMagnitude P (SurprisePotential pi_dist hπ) x := by
  intro x
  rw [surprise_gradient_eq_neg_drift, drift_magnitude_supermartingale P _ h_super x]

end SGC
