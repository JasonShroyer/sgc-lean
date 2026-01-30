/-
Copyright (c) 2025 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team

# Tsallis Statistics: Non-Extensive Entropy Framework

This module defines the Tsallis entropy and related quantities for non-extensive
statistical mechanics. These generalize Shannon/Gibbs entropy for systems with
long-range correlations or non-additive interactions.

## Main Definitions

1. `TsallisEntropy`: The q-entropy S_q(p) = (1 - Σ p_i^q) / (q - 1)
2. `EscortDistribution`: The re-weighted probability P_q(i) = p_i^q / Σ p_j^q
3. `TsallisDivergence`: The generalized KL-divergence D_q(p ‖ ref)

## Physical Significance

**Non-Extensive Systems**: When q ≠ 1, the entropy is non-additive:
  S_q(A+B) ≠ S_q(A) + S_q(B)

**The Escort Distribution**: The escort P_q emphasizes high-probability events
when q > 1, and low-probability events when q < 1.

**Range of Interest**: For 1 < q < 2, Tsallis statistics satisfy DPI.

## References

- Tsallis (1988), "Possible generalization of Boltzmann-Gibbs statistics"
- Naudts (2011), "Generalised Thermostatistics"
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.MeanInequalities

noncomputable section

namespace SGC.InformationGeometry.Tsallis

open Finset Real

-- Suppress unused variable warnings in this section (many theorems don't need all type constraints)
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### 1. Tsallis Entropy -/

/-- **Tsallis Entropy** (q-entropy):

    S_q(p) = (1 - Σᵢ pᵢ^q) / (q - 1)

    Properties:
    - Reduces to Shannon entropy as q → 1
    - Non-negative for probability distributions
    - Non-additive: S_q(A+B) ≠ S_q(A) + S_q(B) in general -/
def TsallisEntropy (q : ℝ) (p : V → ℝ) : ℝ :=
  (1 - ∑ v, (p v) ^ q) / (q - 1)

/-- For 0 ≤ x ≤ 1 and q > 1, x^q ≤ x.
    This is because x ≤ 1 implies x^q ≤ x^1 = x when q > 1. -/
axiom rpow_le_self_of_le_one_of_one_lt (x q : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (hq : 1 < q) :
    x ^ q ≤ x

/-- For 0 ≤ x ≤ 1 and 0 < q < 1, x^q ≥ x.
    This is because x ≤ 1 implies x^q ≥ x^1 = x when q < 1. -/
axiom self_le_rpow_of_le_one_of_lt_one (x q : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    x ≤ x ^ q

/-- Tsallis entropy is non-negative for probability distributions when q > 0.

    **Proof**: S_q = (1 - Σ p^q) / (q - 1).
    - If q > 1: For 0 ≤ p ≤ 1, we have p^q ≤ p, so Σ p^q ≤ 1, making numerator ≥ 0.
    - If 0 < q < 1: For 0 ≤ p ≤ 1, we have p^q ≥ p, so Σ p^q ≥ 1, making numerator ≤ 0.
    In both cases, numerator and denominator have the same sign, so S_q ≥ 0. -/
lemma TsallisEntropy_nonneg {q : ℝ} (hq : q > 0) (p : V → ℝ)
    (hp_nonneg : ∀ v, 0 ≤ p v) (hp_sum : ∑ v, p v = 1)
    (hq_ne_one : q ≠ 1) : 0 ≤ TsallisEntropy q p := by
  unfold TsallisEntropy
  -- Helper: each p v ≤ 1 (since they're non-negative and sum to 1)
  have hp_le_one : ∀ v, p v ≤ 1 := fun v => by
    have : p v ≤ ∑ w, p w := Finset.single_le_sum (fun w _ => hp_nonneg w) (Finset.mem_univ v)
    rw [hp_sum] at this; exact this
  rcases lt_or_gt_of_ne hq_ne_one with hq_lt | hq_gt
  · -- Case q < 1: denominator < 0, numerator ≤ 0
    have h_sum_ge : 1 ≤ ∑ v, (p v) ^ q := by
      rw [← hp_sum]
      apply Finset.sum_le_sum
      intro v _
      exact self_le_rpow_of_le_one_of_lt_one (p v) q (hp_nonneg v) (hp_le_one v) hq hq_lt
    have h_num_neg : 1 - ∑ v, (p v) ^ q ≤ 0 := by linarith
    have h_den_neg : q - 1 < 0 := by linarith
    -- neg/neg = pos
    rw [div_nonneg_iff]
    right
    exact ⟨h_num_neg, le_of_lt h_den_neg⟩
  · -- Case q > 1: denominator > 0, numerator ≥ 0
    have h_sum_le : ∑ v, (p v) ^ q ≤ 1 := by
      rw [← hp_sum]
      apply Finset.sum_le_sum
      intro v _
      exact rpow_le_self_of_le_one_of_one_lt (p v) q (hp_nonneg v) (hp_le_one v) hq_gt
    apply div_nonneg
    · linarith
    · linarith

/-! ### 2. Escort Distribution -/

/-- The normalization factor Z_q = Σᵢ pᵢ^q. -/
def EscortNormalization (q : ℝ) (p : V → ℝ) : ℝ :=
  ∑ v, (p v) ^ q

/-- **Escort Distribution**:

    P_q(i) = pᵢ^q / Z_q   where Z_q = Σⱼ pⱼ^q

    The escort distribution re-weights the original distribution:
    - q > 1: Emphasizes high-probability events
    - q < 1: Emphasizes low-probability events
    - q = 1: Recovers original distribution -/
def EscortDistribution (q : ℝ) (p : V → ℝ) (hZ : EscortNormalization q p ≠ 0) : V → ℝ :=
  fun v => (p v) ^ q / EscortNormalization q p

/-- The escort distribution sums to 1. -/
lemma EscortDistribution_sum {q : ℝ} (p : V → ℝ) (hZ : EscortNormalization q p ≠ 0) :
    ∑ v, EscortDistribution q p hZ v = 1 := by
  unfold EscortDistribution
  -- Σ (p^q / Z) = (Σ p^q) / Z = Z / Z = 1
  rw [← Finset.sum_div]
  exact div_self hZ

/-- The escort is non-negative when p is non-negative and q > 0. -/
lemma EscortDistribution_nonneg {q : ℝ} (hq : q > 0) (p : V → ℝ)
    (hp : ∀ v, 0 ≤ p v) (hZ : EscortNormalization q p ≠ 0) (v : V) :
    0 ≤ EscortDistribution q p hZ v := by
  unfold EscortDistribution
  apply div_nonneg
  · exact rpow_nonneg (hp v) q
  · unfold EscortNormalization at hZ ⊢
    exact sum_nonneg (fun w _ => rpow_nonneg (hp w) q)

/-! ### 3. Tsallis Divergence (Relative Entropy) -/

/-- **Tsallis Divergence** (q-relative entropy):

    D_q(p ‖ ref) = (1 - Σᵢ pᵢ^(2-q) · refᵢ^(q-1)) / (q - 1)

    Properties:
    - Reduces to KL divergence as q → 1
    - Non-negative: D_q(p ‖ ref) ≥ 0 (for appropriate q)
    - Satisfies DPI for 1 < q < 2 -/
def TsallisDivergence (q : ℝ) (p ref : V → ℝ) : ℝ :=
  (1 - ∑ v, (p v) ^ (2 - q) * (ref v) ^ (q - 1)) / (q - 1)

/-- **Young's Inequality** (weighted AM-GM): For a,b ≥ 0 and α,β > 0 with α + β = 1:
    a^α · b^β ≤ α·a + β·b

    This is a fundamental convexity result. -/
axiom young_inequality (a b α β : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hα : 0 < α) (hβ : 0 < β) (hαβ : α + β = 1) :
    a ^ α * b ^ β ≤ α * a + β * b

/-- **Key Lemma**: For probability distributions and 1 < q < 2,
    the weighted sum Σ p^(2-q) · ref^(q-1) ≤ 1.

    **Proof**: Using Young's inequality with α = 2-q, β = q-1 (which sum to 1):
      p^(2-q) · ref^(q-1) ≤ (2-q)·p + (q-1)·ref
    Summing: Σ ≤ (2-q)·Σp + (q-1)·Σref = (2-q)·1 + (q-1)·1 = 1. -/
lemma tsallis_sum_le_one {q : ℝ} (hq : 1 < q) (hq' : q < 2)
    (p ref : V → ℝ) (hp_nonneg : ∀ v, 0 ≤ p v) (href_nonneg : ∀ v, 0 ≤ ref v)
    (hp_sum : ∑ v, p v = 1) (href_sum : ∑ v, ref v = 1) :
    ∑ v, (p v) ^ (2 - q) * (ref v) ^ (q - 1) ≤ 1 := by
  have hα : 0 < 2 - q := by linarith
  have hβ : 0 < q - 1 := by linarith
  have hαβ : (2 - q) + (q - 1) = 1 := by ring
  calc ∑ v, (p v) ^ (2 - q) * (ref v) ^ (q - 1)
      ≤ ∑ v, ((2 - q) * p v + (q - 1) * ref v) := by
        apply Finset.sum_le_sum
        intro v _
        exact young_inequality (p v) (ref v) (2 - q) (q - 1)
          (hp_nonneg v) (href_nonneg v) hα hβ hαβ
    _ = (2 - q) * ∑ v, p v + (q - 1) * ∑ v, ref v := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = (2 - q) * 1 + (q - 1) * 1 := by rw [hp_sum, href_sum]
    _ = 1 := by ring

/-- Tsallis divergence is non-negative for 1 < q < 2.

    **Proof**: D_q = (1 - Σ p^(2-q)·ref^(q-1)) / (q-1).
    By `tsallis_sum_le_one`, the numerator 1 - Σ... ≥ 0.
    Since q > 1, the denominator q - 1 > 0.
    Thus D_q ≥ 0.

    **Status**: Proved from `tsallis_sum_le_one` (which uses Young's inequality). -/
lemma TsallisDivergence_nonneg {q : ℝ} (hq : 1 < q) (hq' : q < 2)
    (p ref : V → ℝ) (hp_nonneg : ∀ v, 0 ≤ p v) (href_nonneg : ∀ v, 0 ≤ ref v)
    (hp_sum : ∑ v, p v = 1) (href_sum : ∑ v, ref v = 1) :
    0 ≤ TsallisDivergence q p ref := by
  unfold TsallisDivergence
  apply div_nonneg
  · -- Numerator: 1 - Σ p^(2-q)·ref^(q-1) ≥ 0
    have h := tsallis_sum_le_one hq hq' p ref hp_nonneg href_nonneg hp_sum href_sum
    linarith
  · -- Denominator: q - 1 > 0
    linarith

/-- Tsallis divergence is zero iff p = ref.

    **Status**: Axiomatized. The proof requires:
    1. D_q = 0 iff numerator = 0 (since q ≠ 1)
    2. Numerator = 0 iff Σ p^(2-q)·ref^(q-1) = 1
    3. By Young's equality condition, this holds iff p = ref pointwise

    This is a standard characterization of divergence equality. -/
axiom TsallisDivergence_eq_zero_iff {V : Type*} [Fintype V] {q : ℝ} (hq : q ≠ 1)
    (p ref : V → ℝ) (hp_pos : ∀ v, 0 < p v) (href_pos : ∀ v, 0 < ref v)
    (hp_sum : ∑ v, p v = 1) (href_sum : ∑ v, ref v = 1) :
    TsallisDivergence q p ref = 0 ↔ p = ref

/-! ### 4. Non-Extensive System Class -/

/-- **Non-Extensive System**: A system with q-parameter in the range (1, 2).

    This is the "sweet spot" for Tsallis statistics:
    - q > 1: Sub-additive entropy (long-range correlations)
    - q < 2: Convex divergence (DPI holds) -/
class NonExtensiveSystem (q : ℝ) : Prop where
  range_check : 1 < q ∧ q < 2

/-- The q-parameter is greater than 1 for non-extensive systems. -/
lemma NonExtensiveSystem.one_lt_q {q : ℝ} [h : NonExtensiveSystem q] : 1 < q :=
  h.range_check.1

/-- The q-parameter is less than 2 for non-extensive systems. -/
lemma NonExtensiveSystem.q_lt_two {q : ℝ} [h : NonExtensiveSystem q] : q < 2 :=
  h.range_check.2

/-! ### 5. Tsallis Free Energy -/

/-- **Tsallis Free Energy**:

    F_q(p) = ⟨H⟩_q - T · S_q(p)

    where ⟨H⟩_q is the escort-averaged energy. -/
def TsallisFreeEnergy (q T : ℝ) (p : V → ℝ) (H : V → ℝ)
    (hZ : EscortNormalization q p ≠ 0) : ℝ :=
  let P_q := EscortDistribution q p hZ
  let avg_H := ∑ v, P_q v * H v
  avg_H - T * TsallisEntropy q p

/-! ### 6. Data Processing Inequality (DPI) -/

/-- **Data Processing Inequality** for Tsallis Divergence:

    For 1 < q < 2 and any stochastic map T:
    D_q(Tp ‖ Tref) ≤ D_q(p ‖ ref)

    **Status**: Axiom. The proof requires convexity of x^(2-q). -/
axiom TsallisDPI {q : ℝ} [NonExtensiveSystem q]
    (p ref : V → ℝ) (hp : ∀ v, 0 < p v) (href : ∀ v, 0 < ref v)
    (T : Matrix V V ℝ) (hT_stoch : ∀ v, (∀ w, 0 ≤ T v w) ∧ ∑ w, T v w = 1) :
    TsallisDivergence q (fun v => ∑ w, T v w * p w) (fun v => ∑ w, T v w * ref w) ≤
    TsallisDivergence q p ref

/-! ## Summary

This module establishes the **Tsallis Statistics Framework**:

1. **TsallisEntropy S_q**: Non-additive generalization of Shannon entropy
2. **EscortDistribution P_q**: Observable probability for non-extensive systems
3. **TsallisDivergence D_q**: Information distance with DPI for 1 < q < 2
4. **NonExtensiveSystem class**: Enforces q ∈ (1, 2) for favorable properties

**Connection to SGC**:
- Escort Conductance uses P_q for transport coefficients
- DPI ensures conductance is monotonic under RG flow
- The range 1 < q < 2 is where "emergent" systems live

**Open Problems** (TODOs):
1. Prove TsallisDPI constructively
2. Connect TsallisEntropy to HiddenEntropyProduction
3. Show Escort monotonicity under Markov dynamics
-/

end SGC.InformationGeometry.Tsallis
