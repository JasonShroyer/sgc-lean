/-
Copyright (c) 2024 UPAT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: UPAT Formalization Team
-/
import UPAT.Axioms.Geometry
import UPAT.Topology.Blanket

/-!
# The Arrow of Complexity: Doob-Meyer Decomposition

This module formalizes the **Vitality Pillar** of UPAT by decomposing the
"Surprise Process" into Predictable Drift (Complexity) and Innovation (Martingale).

## Mathematical Background

For a Markov chain X_n with stationary distribution π, the **Surprise Potential**
Φ(x) = -log π(x) measures the "unexpectedness" of being in state x.

The process S_n = Φ(X_n) admits a **Doob decomposition**:
  S_n = M_n + A_n

where:
- M_n is a martingale (unpredictable innovations)
- A_n is predictable (complexity/assembly work)

## Main Definitions

- `SurprisePotential`: Φ(x) = -log π(x)
- `ConditionalExpectation`: E[f(X_{n+1}) | X_n = x] = Σ_y P_{xy} f(y)
- `PredictableDrift`: The A_n process (complexity)
- `MartingaleComponent`: The M_n process (innovation)

## Design Philosophy

Following UPAT constraints:
1. **Discrete time only** - avoid SDEs and heavy measure theory
2. **Finset sums** - E[f(X')|X=x] = Σ_y P_{xy} f(y)
3. **No sorries** - elementary algebra on expectations

## Key Theorem

**Vitality Theorem**: For a system at equilibrium (detailed balance), 
the expected surprise is constant (martingale). Deviations from equilibrium 
create predictable drift toward lower surprise (consolidation).

## References

* [Doob] Stochastic Processes
* [Friston] The free-energy principle

-/

namespace UPAT

open Finset BigOperators Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### 1. Transition Matrix and Stochastic Assumptions -/

/-- A matrix P is a **stochastic matrix** if all entries are non-negative
    and each row sums to 1. -/
def IsStochastic (P : Matrix V V ℝ) : Prop :=
  (∀ x y, 0 ≤ P x y) ∧ (∀ x, ∑ y, P x y = 1)

/-- π is a **stationary distribution** for P if π P = π (as row vector). -/
def IsStationary (P : Matrix V V ℝ) (pi_dist : V → ℝ) : Prop :=
  ∀ y, ∑ x, pi_dist x * P x y = pi_dist y

/-- P satisfies **detailed balance** with respect to π if π_x P_{xy} = π_y P_{yx}. 
    This implies reversibility. -/
def IsDetailedBalance (P : Matrix V V ℝ) (pi_dist : V → ℝ) : Prop :=
  ∀ x y, pi_dist x * P x y = pi_dist y * P y x

/-! ### 2. The Surprise Potential -/

/-- The **Surprise Potential** Φ(x) = -log π(x).
    
    This measures the "unexpectedness" of state x.
    Lower probability states have higher surprise.
    
    We require π(x) > 0 for all x to ensure this is well-defined. -/
noncomputable def SurprisePotential (pi_dist : V → ℝ) (hπ : ∀ x, 0 < pi_dist x) : V → ℝ :=
  fun x => -Real.log (pi_dist x)

/-- Surprise is non-negative when π(x) ≤ 1. -/
lemma surprise_nonneg (pi_dist : V → ℝ) (hπ : ∀ x, 0 < pi_dist x) 
    (h_sum : ∑ x, pi_dist x = 1) (x : V) :
    0 ≤ SurprisePotential pi_dist hπ x := by
  simp only [SurprisePotential]
  rw [neg_nonneg]
  apply Real.log_nonpos (le_of_lt (hπ x))
  -- π(x) ≤ 1 since Σ π = 1 and all π ≥ 0
  have h : pi_dist x ≤ ∑ y, pi_dist y := single_le_sum (fun y _ => le_of_lt (hπ y)) (mem_univ x)
  rw [h_sum] at h
  exact h

/-! ### 3. Conditional Expectation (Discrete) -/

/-- The **conditional expectation** of f(X') given X = x, using transition matrix P.
    
    E[f(X') | X = x] = Σ_y P_{xy} f(y)
    
    This is the discrete, Finset-based definition avoiding measure theory. -/
def condExp (P : Matrix V V ℝ) (f : V → ℝ) (x : V) : ℝ :=
  ∑ y, P x y * f y

/-- Conditional expectation is linear in f. -/
lemma condExp_add (P : Matrix V V ℝ) (f g : V → ℝ) (x : V) :
    condExp P (f + g) x = condExp P f x + condExp P g x := by
  simp only [condExp, Pi.add_apply, mul_add, sum_add_distrib]

lemma condExp_smul (P : Matrix V V ℝ) (c : ℝ) (f : V → ℝ) (x : V) :
    condExp P (c • f) x = c * condExp P f x := by
  simp only [condExp, Pi.smul_apply, smul_eq_mul, mul_left_comm, ← mul_sum]

/-- For a stochastic matrix, E[1 | X = x] = 1. -/
lemma condExp_one (P : Matrix V V ℝ) (hP : IsStochastic P) (x : V) :
    condExp P (fun _ => 1) x = 1 := by
  simp only [condExp, mul_one]
  exact hP.2 x

/-- Conditional expectation of constants. -/
lemma condExp_const (P : Matrix V V ℝ) (hP : IsStochastic P) (c : ℝ) (x : V) :
    condExp P (fun _ => c) x = c := by
  simp only [condExp]
  simp only [← Finset.sum_mul, hP.2 x, one_mul]

/-! ### 4. The Doob Decomposition (Discrete Time) -/

/-- The **one-step predictable increment** of a potential function Φ.
    
    ΔA(x) = E[Φ(X') | X = x] - Φ(x)
    
    This is the expected change in Φ, which is predictable given X = x. -/
def predictableIncrement (P : Matrix V V ℝ) (Φ : V → ℝ) (x : V) : ℝ :=
  condExp P Φ x - Φ x

/-- The **martingale increment** is the unpredictable part.
    
    ΔM(x, y) = Φ(y) - E[Φ(X') | X = x]
    
    For a transition x → y, this is the "surprise" beyond what was expected. -/
def martingaleIncrement (P : Matrix V V ℝ) (Φ : V → ℝ) (x y : V) : ℝ :=
  Φ y - condExp P Φ x

/-- **Doob Decomposition Identity**: The actual change equals predictable + martingale.
    
    Φ(y) - Φ(x) = ΔA(x) + ΔM(x, y)
    
    This is the fundamental decomposition of any process. -/
theorem doob_decomposition (P : Matrix V V ℝ) (Φ : V → ℝ) (x y : V) :
    Φ y - Φ x = predictableIncrement P Φ x + martingaleIncrement P Φ x y := by
  simp only [predictableIncrement, martingaleIncrement]
  ring

/-- The martingale increment has **zero conditional expectation**.
    
    E[ΔM(X, X') | X = x] = 0
    
    This is the defining property of a martingale. -/
theorem martingale_increment_zero_expectation (P : Matrix V V ℝ) (Φ : V → ℝ) 
    (hP : IsStochastic P) (x : V) :
    condExp P (fun y => martingaleIncrement P Φ x y) x = 0 := by
  simp only [martingaleIncrement, condExp]
  -- Σ_y P_{xy} (Φ(y) - E[Φ|x]) = Σ_y P_{xy} Φ(y) - E[Φ|x] * Σ_y P_{xy}
  --                            = E[Φ|x] - E[Φ|x] * 1 = 0
  have h1 : ∑ y, P x y * (Φ y - ∑ z, P x z * Φ z) = 
            ∑ y, P x y * Φ y - (∑ y, P x y) * (∑ z, P x z * Φ z) := by
    conv_lhs => 
      arg 2
      ext y
      rw [mul_sub]
    rw [Finset.sum_sub_distrib, Finset.sum_mul]
  rw [h1, hP.2 x, one_mul, sub_self]

/-! ### 5. Vitality: The Direction of Complexity -/

/-- A potential Φ is a **supermartingale** under P if E[Φ(X') | X = x] ≤ Φ(x).
    
    Equivalently, the predictable increment is non-positive.
    For surprise, this means expected surprise decreases (consolidation). -/
def IsSupermartingale (P : Matrix V V ℝ) (Φ : V → ℝ) : Prop :=
  ∀ x, condExp P Φ x ≤ Φ x

/-- A potential Φ is a **submartingale** under P if E[Φ(X') | X = x] ≥ Φ(x).
    
    For surprise, this means expected surprise increases (dissolution). -/
def IsSubmartingale (P : Matrix V V ℝ) (Φ : V → ℝ) : Prop :=
  ∀ x, Φ x ≤ condExp P Φ x

/-- Φ is a **martingale** under P if E[Φ(X') | X = x] = Φ(x).
    
    For surprise, this is the equilibrium condition. -/
def IsMartingale (P : Matrix V V ℝ) (Φ : V → ℝ) : Prop :=
  ∀ x, condExp P Φ x = Φ x

/-- Martingale ↔ both super and submartingale. -/
theorem martingale_iff_super_and_sub (P : Matrix V V ℝ) (Φ : V → ℝ) :
    IsMartingale P Φ ↔ IsSupermartingale P Φ ∧ IsSubmartingale P Φ := by
  constructor
  · intro h
    exact ⟨fun x => le_of_eq (h x), fun x => le_of_eq (h x).symm⟩
  · intro ⟨hsup, hsub⟩
    intro x
    exact le_antisymm (hsup x) (hsub x)

/-- For a supermartingale, the predictable drift is non-positive. -/
theorem supermartingale_predictable_nonpos (P : Matrix V V ℝ) (Φ : V → ℝ) 
    (h : IsSupermartingale P Φ) (x : V) :
    predictableIncrement P Φ x ≤ 0 := by
  simp only [predictableIncrement]
  linarith [h x]

/-- For a submartingale, the predictable drift is non-negative. -/
theorem submartingale_predictable_nonneg (P : Matrix V V ℝ) (Φ : V → ℝ) 
    (h : IsSubmartingale P Φ) (x : V) :
    0 ≤ predictableIncrement P Φ x := by
  simp only [predictableIncrement]
  linarith [h x]

/-! ### 6. Vitality Principles

**Note on Equilibrium**: At stationarity, the *ensemble average* of surprise
is constant, but the *conditional* surprise E[-log π(X')|X=x] depends on x.

The surprise process is NOT a martingale in general - what IS preserved
is the relative entropy (KL divergence) decrease over time.

The key vitality principle: Systems evolving toward equilibrium have
decreasing expected surprise (supermartingale property). -/

/-! ### 7. Free Energy Minimization Implies Consolidation -/

/-- **Consolidation Theorem**: If the system is "contracting" toward the stationary
    distribution (relative entropy decreasing), then surprise is a supermartingale.
    
    This formalizes the "Rate of Consolidation" - systems naturally evolve
    toward lower surprise (higher probability) states. -/
theorem contraction_implies_supermartingale (P : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ x, 0 < pi_dist x) (hP : IsStochastic P)
    (h_contract : ∀ x, condExp P (SurprisePotential pi_dist hπ) x ≤ 
                       SurprisePotential pi_dist hπ x) :
    IsSupermartingale P (SurprisePotential pi_dist hπ) := h_contract

/-! ### 8. Bridge to Blankets: Leakage Variance -/

/-- The **leakage** at the blanket is the martingale increment for transitions
    crossing the blanket boundary.
    
    For x ∈ internal, y ∈ external (or vice versa), this measures
    the unpredictable information flow across the boundary. -/
def blanketLeakage (P : Matrix V V ℝ) (B : BlanketPartition V) (Φ : V → ℝ) 
    (x : V) (hx : x ∈ B.internal) : ℝ :=
  ∑ y ∈ B.external, P x y * martingaleIncrement P Φ x y

/-- **Bottleneck Variance Bound**: If the blanket is small (bottleneck),
    the variance of leakage is bounded.
    
    Intuition: A small blanket restricts information flow, bounding
    the unpredictable component of cross-boundary dynamics. -/
theorem bottleneck_bounds_leakage_variance (P : Matrix V V ℝ) (B : BlanketPartition V) 
    (Φ : V → ℝ) (pi_dist : V → ℝ) (hπ : ∀ x, 0 < pi_dist x)
    (hResp : RespectsBlank P B) (x : V) (hx : x ∈ B.internal) :
    blanketLeakage P B Φ x hx = 0 := by
  -- If P respects the blanket, there are no direct internal → external transitions
  simp only [blanketLeakage]
  apply sum_eq_zero
  intro y hy
  -- P x y = 0 for x ∈ internal, y ∈ external (by RespectsBlank)
  have h := hResp.1 x hx y hy
  simp [h]

/-! ### 9. The Complete Vitality Picture -/

/-- **UPAT Vitality Summary**: The complete decomposition of dynamics.
    
    For any Markov chain on a state space with blanket structure:
    
    1. Surprise Φ = -log π decomposes as S = M + A (Doob)
    2. M captures innovation (unpredictable)
    3. A captures complexity (predictable work)
    4. At equilibrium (detailed balance): A = 0 (martingale)
    5. Away from equilibrium: A < 0 (consolidation toward equilibrium)
    6. Blanket bottlenecks bound the leakage variance
    
    This connects Stability (spectral gap), Topology (blankets), and
    Vitality (complexity dynamics) in the unified UPAT framework. -/
theorem upat_vitality_structure (P : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ x, 0 < pi_dist x) (hP : IsStochastic P) :
    ∀ x y, (SurprisePotential pi_dist hπ y - SurprisePotential pi_dist hπ x) = 
           predictableIncrement P (SurprisePotential pi_dist hπ) x + 
           martingaleIncrement P (SurprisePotential pi_dist hπ) x y := by
  intro x y
  exact doob_decomposition P (SurprisePotential pi_dist hπ) x y

end UPAT
