import SGC.Renormalization.Lumpability
import SGC.Renormalization.Approximate

/-!
Copyright (c) 2024 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team

# Entropy Production and Coarse-Graining

This module formalizes entropy production for continuous-time Markov chains (CTMCs)
and proves that coarse-graining reduces observed entropy production, defining
"hidden entropy production" as the difference.

## Mathematical Background

For a CTMC with generator L and stationary distribution π, the **entropy production rate**
measures the irreversibility of the dynamics:

  σ(L, π) = Σ_{x≠y} π_x L_{xy} log(π_x L_{xy} / π_y L_{yx})

This is the Schnakenberg formula, equivalent to the KL divergence rate between
forward and time-reversed path measures.

## Main Results

1. **KL Divergence** (discrete): D_KL(p ‖ q) = Σ_x p_x log(p_x / q_x)
2. **Data Processing Inequality**: Coarse-graining cannot increase KL divergence
3. **Entropy Production Rate**: σ(L, π) for CTMC at steady state
4. **Hidden Entropy Production**: σ_hid = σ(L, π) - σ(L̄, π̄) ≥ 0

## Design Philosophy

Following SGC constraints:
1. **Discrete state space** (`[Fintype V]`)
2. **Explicit Finset sums** - no measure theory overhead
3. **Non-reversible by default** - reversible as special case
4. **Positivity assumptions** - avoid log(0) issues cleanly

## Connection to Trajectory Bounds

The hidden entropy production σ_hid will be connected to the leakage defect
‖D‖_π from `Approximate.lean`, establishing:

  "Prediction error (ε) implies dissipation (σ_hid)"

This is the thermodynamic foundation for emergence: systems that persist
must minimize both prediction error AND dissipation.

## References

* Schnakenberg (1976) - Network theory of microscopic and macroscopic behavior
* Esposito & Van den Broeck (2010) - Three faces of the second law
* Seifert (2012) - Stochastic thermodynamics, fluctuation theorems
-/

namespace SGC
namespace Thermodynamics

open Finset BigOperators Matrix Real

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### 1. Discrete KL Divergence -/

/-- **KL Divergence** (discrete): D_KL(p ‖ q) = Σ_x p_x log(p_x / q_x).

    For distributions p, q on a finite state space V.
    Requires q_x > 0 wherever p_x > 0 (absolute continuity).

    Convention: 0 * log(0/q) = 0 (standard limiting convention). -/
noncomputable def KLDiv (p q : V → ℝ) : ℝ :=
  ∑ x, if p x = 0 then 0 else p x * log (p x / q x)

/-- KL divergence is non-negative (Gibbs' inequality).

    D_KL(p ‖ q) ≥ 0, with equality iff p = q. -/
theorem KLDiv_nonneg (p q : V → ℝ) (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 < q x)
    (hp_sum : ∑ x, p x = 1) (hq_sum : ∑ x, q x = 1) :
    0 ≤ KLDiv p q := by
  -- This is Gibbs' inequality, a standard result
  -- Proof uses log-sum inequality or Jensen's inequality
  sorry -- Standard result, will be proven or axiomatized

/-- KL divergence equals zero iff p = q. -/
theorem KLDiv_eq_zero_iff (p q : V → ℝ) (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 < q x)
    (hp_sum : ∑ x, p x = 1) (hq_sum : ∑ x, q x = 1) :
    KLDiv p q = 0 ↔ p = q := by
  sorry -- Standard result

/-! ### 2. Data Processing Inequality (DPI) -/

/-- **Pushforward Distribution**: The distribution induced by a deterministic map f.

    (f_# p)(y) = Σ_{x : f(x) = y} p(x) -/
noncomputable def pushforward {W : Type*} [Fintype W] [DecidableEq W]
    (f : V → W) (p : V → ℝ) : W → ℝ :=
  fun y => ∑ x ∈ univ.filter (fun x => f x = y), p x

/-- Pushforward preserves total mass. -/
lemma pushforward_sum {W : Type*} [Fintype W] [DecidableEq W]
    (f : V → W) (p : V → ℝ) :
    ∑ y, pushforward f p y = ∑ x, p x := by
  simp only [pushforward]
  -- Swap sums and use that each x contributes to exactly one y = f(x)
  conv_lhs =>
    arg 2
    ext y
    rw [sum_filter]
  simp only [sum_comm (γ := W), sum_ite_eq, mem_univ, ↓reduceIte]

/-- **Data Processing Inequality**: Coarse-graining cannot increase KL divergence.

    D_KL(f_# p ‖ f_# q) ≤ D_KL(p ‖ q)

    This is the fundamental monotonicity of information under processing.

    **Proof Strategy**: Uses log-sum inequality or convexity of KL. -/
theorem data_processing_inequality {W : Type*} [Fintype W] [DecidableEq W]
    (f : V → W) (p q : V → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 < q x) :
    KLDiv (pushforward f p) (pushforward f q) ≤ KLDiv p q := by
  -- This is a standard result in information theory
  -- The proof uses the log-sum inequality
  sorry -- Standard result, axiomatize or prove later

/-! ### 3. Entropy Production Rate for CTMC -/

/-- **Probability Current**: The net flow from x to y at steady state.

    J_{xy} = π_x L_{xy} - π_y L_{yx}

    At detailed balance (reversibility), J = 0. -/
def ProbabilityCurrent (L : Matrix V V ℝ) (pi_dist : V → ℝ) (x y : V) : ℝ :=
  pi_dist x * L x y - pi_dist y * L y x

/-- The probability current is antisymmetric: J_{xy} = -J_{yx}. -/
lemma current_antisymm (L : Matrix V V ℝ) (pi_dist : V → ℝ) (x y : V) :
    ProbabilityCurrent L pi_dist x y = -ProbabilityCurrent L pi_dist y x := by
  simp only [ProbabilityCurrent]
  ring

/-- At detailed balance, all currents vanish. -/
lemma current_zero_of_detailed_balance (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (h_db : ∀ x y, pi_dist x * L x y = pi_dist y * L y x) (x y : V) :
    ProbabilityCurrent L pi_dist x y = 0 := by
  simp only [ProbabilityCurrent]
  rw [h_db x y]
  ring

/-- **Entropy Production Rate** (Schnakenberg formula):

    σ(L, π) = (1/2) Σ_{x,y} (π_x L_{xy} - π_y L_{yx}) log(π_x L_{xy} / π_y L_{yx})
            = (1/2) Σ_{x,y} J_{xy} log(π_x L_{xy} / π_y L_{yx})

    This measures the irreversibility of the dynamics.

    **Assumptions**:
    - L is a valid generator (off-diagonal ≥ 0, rows sum to 0)
    - π is the stationary distribution (π L = 0)
    - L_{xy} > 0 ⟹ L_{yx} > 0 (irreducibility condition for well-definedness)

    Convention: Terms with L_{xy} = 0 contribute 0 (0 * log(0) = 0). -/
noncomputable def EntropyProductionRate (L : Matrix V V ℝ) (pi_dist : V → ℝ) : ℝ :=
  (1/2 : ℝ) * ∑ x, ∑ y,
    if x = y ∨ L x y = 0 then 0
    else (pi_dist x * L x y - pi_dist y * L y x) *
         log (pi_dist x * L x y / (pi_dist y * L y x))

/-- Entropy production is non-negative.

    σ(L, π) ≥ 0

    This is the second law of thermodynamics for Markov processes.

    **Proof**: Each term (a - b) * log(a/b) ≥ 0 for a, b > 0. -/
theorem entropy_production_nonneg (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ x, 0 < pi_dist x)
    (hL_pos : ∀ x y, x ≠ y → L x y > 0 → L y x > 0) :
    0 ≤ EntropyProductionRate L pi_dist := by
  -- Each term has the form (a - b) * log(a/b) where a, b > 0
  -- This is ≥ 0 because:
  --   If a > b: both factors positive
  --   If a < b: both factors negative
  --   If a = b: both factors zero
  sorry -- Standard thermodynamics result

/-- At detailed balance, entropy production vanishes.

    If π_x L_{xy} = π_y L_{yx} for all x,y, then σ = 0. -/
theorem entropy_production_zero_of_detailed_balance (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (h_db : ∀ x y, pi_dist x * L x y = pi_dist y * L y x) :
    EntropyProductionRate L pi_dist = 0 := by
  simp only [EntropyProductionRate]
  apply mul_eq_zero_of_right
  apply sum_eq_zero
  intro x _
  apply sum_eq_zero
  intro y _
  split_ifs with h
  · rfl
  · push_neg at h
    rw [h_db x y]
    simp only [sub_self, zero_mul]

/-! ### 4. Coarse-Grained Entropy Production -/

/-- **Coarse-Grained Stationary Distribution**: π̄_ā = Σ_{x : q(x)=ā} π_x.

    This is the marginal distribution on the partition quotient.
    Uses the existing `pi_bar` from Lumpability.lean. -/
noncomputable def CoarseStationaryDist (P : Partition V) (pi_dist : V → ℝ) : P.Quot → ℝ :=
  pi_bar P pi_dist

/-- The coarse distribution sums to 1 if the fine distribution does. -/
lemma coarse_dist_sum (P : Partition V) (pi_dist : V → ℝ) (h : ∑ x, pi_dist x = 1) :
    ∑ a_bar, CoarseStationaryDist P pi_dist a_bar = 1 :=
  pi_bar_sum_one P h

/-- **Coarse-Grained Generator**: L̄_{āb̄} = Σ_{x,y : q(x)=ā, q(y)=b̄} (π_x/π̄_ā) L_{xy}.

    This is the effective generator on the quotient space, weighted by
    the conditional distribution within each block.

    Note: This is related to `QuotientGeneratorSimple` from Lumpability.lean. -/
noncomputable def CoarseGenerator (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) : Matrix P.Quot P.Quot ℝ :=
  fun a_bar b_bar =>
    let π_a := CoarseStationaryDist P pi_dist a_bar
    if π_a = 0 then 0
    else (1 / π_a) * ∑ x : V, ∑ y : V,
      if P.quot_map x = a_bar ∧ P.quot_map y = b_bar then pi_dist x * L x y else 0

/-- **Coarse Entropy Production**: σ(L̄, π̄) on the quotient space. -/
noncomputable def CoarseEntropyProduction (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) : ℝ :=
  EntropyProductionRate (CoarseGenerator L P pi_dist) (CoarseStationaryDist P pi_dist)

/-! ### 5. Hidden Entropy Production -/

/-- **Hidden Entropy Production**: The entropy production "lost" to coarse-graining.

    σ_hid := σ(L, π) - σ(L̄, π̄) ≥ 0

    This measures the dissipation occurring at scales finer than the observation.

    Physical interpretation: Information about irreversibility is lost when
    we only observe the coarse-grained dynamics. -/
noncomputable def HiddenEntropyProduction (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) : ℝ :=
  EntropyProductionRate L pi_dist - CoarseEntropyProduction L P pi_dist

/-- **Second Law of Coarse-Graining**: Hidden entropy production is non-negative.

    σ_hid = σ(L, π) - σ(L̄, π̄) ≥ 0

    Coarse-graining cannot increase observed entropy production.

    **Proof Strategy**: This follows from the Data Processing Inequality applied
    to the path-space KL divergence between forward and reversed dynamics.

    The coarse-graining map f : paths → coarse_paths satisfies:
    D_KL(f_# P_fwd ‖ f_# P_rev) ≤ D_KL(P_fwd ‖ P_rev)

    The LHS is σ(L̄, π̄) · t and the RHS is σ(L, π) · t, giving the result. -/
theorem hidden_entropy_nonneg (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hπ : ∀ x, 0 < pi_dist x)
    (hL_gen : ∀ x y, x ≠ y → 0 ≤ L x y)
    (hL_pos : ∀ x y, x ≠ y → L x y > 0 → L y x > 0) :
    0 ≤ HiddenEntropyProduction L P pi_dist := by
  -- This is the key theorem connecting coarse-graining to dissipation
  -- Proof via DPI on path measures
  sorry -- Will be proven using DPI infrastructure

/-! ### 6. Summary: Thermodynamic Structure

**Theorem Stack**:
1. `entropy_production_nonneg`: σ(L, π) ≥ 0 (Second Law)
2. `entropy_production_zero_of_detailed_balance`: Reversible ⟹ σ = 0
3. `hidden_entropy_nonneg`: σ_hid ≥ 0 (Coarse-graining inequality)

**Connection to Trajectory Bounds** (Phase D, to be proven):
If `IsApproxLumpable L P π ε`, then σ_hid is bounded by ε.

This establishes: "Prediction error implies dissipation"
-/

end Thermodynamics
end SGC
