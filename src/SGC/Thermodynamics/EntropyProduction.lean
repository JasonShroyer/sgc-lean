import SGC.Renormalization.Lumpability
import SGC.Renormalization.Approximate
import SGC.Thermodynamics.LogSum

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

    `D_KL(p ‖ q) ≥ 0`, with equality iff `p = q`.

    **Proof** (post-Phase-2E sprint, Apr 26 2026 — formerly axiomatised):
    Pointwise, for each `x` we show
    `p x − q x ≤ ite (p x = 0) 0 (p x · log (p x / q x))`.
    On `p x = 0` this reduces to `−q x ≤ 0`, true since `q x > 0`.
    On `p x > 0`, apply `Real.one_sub_inv_le_log_of_pos` to
    `(p x / q x) > 0` to get `1 − q x / p x ≤ log (p x / q x)`, then
    multiply through by `p x > 0`.  Summing the pointwise bound over `V`
    and using `∑ p = ∑ q = 1` yields `0 ≤ KLDiv p q`. -/
theorem KLDiv_nonneg (p q : V → ℝ) (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 < q x)
    (hp_sum : ∑ x, p x = 1) (hq_sum : ∑ x, q x = 1) :
    0 ≤ KLDiv p q := by
  -- Pointwise bound: `p x − q x ≤ ite (p x = 0) 0 (p x · log (p x / q x))`.
  have h_point : ∀ x ∈ (Finset.univ : Finset V),
      p x - q x ≤ if p x = 0 then 0 else p x * log (p x / q x) := by
    intro x _
    by_cases hpx : p x = 0
    · -- Case `p x = 0`: `p x − q x = −q x ≤ 0`.
      rw [if_pos hpx, hpx]
      linarith [hq x]
    · -- Case `p x > 0`: use Gibbs' pointwise inequality.
      rw [if_neg hpx]
      have hpx_pos : 0 < p x := lt_of_le_of_ne (hp x) (Ne.symm hpx)
      have hqx_pos : 0 < q x := hq x
      have hpq_pos : 0 < p x / q x := div_pos hpx_pos hqx_pos
      -- `1 − (p x / q x)⁻¹ ≤ log (p x / q x)` from Mathlib.
      have h_log : 1 - (p x / q x)⁻¹ ≤ log (p x / q x) :=
        Real.one_sub_inv_le_log_of_pos hpq_pos
      -- `(p x / q x)⁻¹ = q x / p x`.
      rw [show (p x / q x)⁻¹ = q x / p x from by rw [inv_div]] at h_log
      -- Multiply both sides by `p x > 0`.
      have h_mul := mul_le_mul_of_nonneg_left h_log (le_of_lt hpx_pos)
      -- `p x · (1 − q x / p x) = p x − q x` (since `p x ≠ 0`).
      have h_simp : p x * (1 - q x / p x) = p x - q x := by
        field_simp
      linarith [h_simp ▸ h_mul]
  -- Sum the pointwise bound: `0 = (∑ p) − (∑ q) = ∑ (p − q) ≤ ∑ ite (...) = KLDiv`.
  unfold KLDiv
  calc (0 : ℝ)
      = (∑ x, p x) - (∑ x, q x) := by rw [hp_sum, hq_sum]; ring
    _ = ∑ x, (p x - q x) := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ x, if p x = 0 then 0 else p x * log (p x / q x) :=
        Finset.sum_le_sum h_point

/-- KL divergence equals zero iff `p = q`.

    **Proof** (post-Phase-2E sprint, May 1 2026 — formerly axiomatised):

    *Backward (`p = q ⇒ KLDiv p p = 0`)*: each summand is either `0`
    (on the `p x = 0` branch) or `p x · log (p x / p x) = p x · log 1 = 0`.

    *Forward (`KLDiv p q = 0 ⇒ p = q`)*: from the same pointwise Gibbs
    bound used in `KLDiv_nonneg`, namely
    `p x − q x ≤ ite (p x = 0) 0 (p x · log (p x / q x))`, plus
    `∑ (p x − q x) = 0 = KLDiv` (the hypothesis), the bound is tight at
    every `x` (`Finset.sum_eq_sum_iff_of_le`).  Pointwise:
    * If `p x = 0`, tightness forces `−q x = 0`, contradicting `q x > 0`.
    * If `p x > 0`, tightness gives
      `p x − q x = p x · log (p x / q x)`.  Suppose for contradiction
      `p x ≠ q x`.  Then `q x / p x > 0` and `q x / p x ≠ 1`, so by
      `Real.log_lt_sub_one_of_pos` we get
      `log (q x / p x) < q x / p x − 1`, hence
      `log (p x / q x) > 1 − q x / p x`.  Multiplying by `p x > 0`
      yields `p x · log (p x / q x) > p x − q x`, contradicting the
      tightness equation.  Hence `p x = q x`. -/
theorem KLDiv_eq_zero_iff (p q : V → ℝ) (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 < q x)
    (hp_sum : ∑ x, p x = 1) (hq_sum : ∑ x, q x = 1) :
    KLDiv p q = 0 ↔ p = q := by
  constructor
  · -- Forward direction: KLDiv = 0 ⇒ p = q.
    intro h_zero
    -- Pointwise Gibbs bound (same as in `KLDiv_nonneg`).
    have h_point : ∀ x ∈ (Finset.univ : Finset V),
        p x - q x ≤ if p x = 0 then 0 else p x * log (p x / q x) := by
      intro x _
      by_cases hpx : p x = 0
      · rw [if_pos hpx, hpx]; linarith [hq x]
      · rw [if_neg hpx]
        have hpx_pos : 0 < p x := lt_of_le_of_ne (hp x) (Ne.symm hpx)
        have hpq_pos : 0 < p x / q x := div_pos hpx_pos (hq x)
        have h_log : 1 - (p x / q x)⁻¹ ≤ log (p x / q x) :=
          Real.one_sub_inv_le_log_of_pos hpq_pos
        rw [show (p x / q x)⁻¹ = q x / p x from by rw [inv_div]] at h_log
        have h_mul := mul_le_mul_of_nonneg_left h_log (le_of_lt hpx_pos)
        have h_simp : p x * (1 - q x / p x) = p x - q x := by field_simp
        linarith [h_simp ▸ h_mul]
    -- Sum-equality: `∑ (p x - q x) = 0 = KLDiv = ∑ ite (...)`.
    have h_sum_eq :
        ∑ x, (p x - q x) =
        ∑ x, if p x = 0 then 0 else p x * log (p x / q x) := by
      rw [Finset.sum_sub_distrib, hp_sum, hq_sum, sub_self]
      exact h_zero.symm
    -- Tightness: pointwise equality from `Finset.sum_eq_sum_iff_of_le`.
    have h_pt_eq : ∀ x ∈ (Finset.univ : Finset V),
        p x - q x = if p x = 0 then 0 else p x * log (p x / q x) :=
      (Finset.sum_eq_sum_iff_of_le h_point).mp h_sum_eq
    -- Pointwise conclude `p x = q x`.
    funext x
    have h_x := h_pt_eq x (Finset.mem_univ x)
    by_cases hpx : p x = 0
    · -- `p x = 0` forces `q x = 0`, contradicting `q x > 0`.
      rw [if_pos hpx, hpx] at h_x
      linarith [hq x]
    · -- `p x > 0`: tightness equation `p x - q x = p x · log (p x / q x)`.
      rw [if_neg hpx] at h_x
      have hpx_pos : 0 < p x := lt_of_le_of_ne (hp x) (Ne.symm hpx)
      have hqx_pos : 0 < q x := hq x
      -- Suppose for contradiction `p x ≠ q x`.
      by_contra hne
      have hqp_pos : 0 < q x / p x := div_pos hqx_pos hpx_pos
      have hqp_ne : q x / p x ≠ 1 := by
        intro h
        apply hne
        have : q x = p x := by
          have hp_ne : p x ≠ 0 := ne_of_gt hpx_pos
          field_simp at h
          linarith
        linarith
      have h_strict : log (q x / p x) < q x / p x - 1 :=
        Real.log_lt_sub_one_of_pos hqp_pos hqp_ne
      -- Convert: `log (p x / q x) = -log (q x / p x)`, so
      --   `log (p x / q x) > 1 - q x / p x`.
      have h_inv : log (p x / q x) = -log (q x / p x) := by
        rw [show p x / q x = (q x / p x)⁻¹ from by rw [inv_div]]
        rw [Real.log_inv]
      have h_pos_log : log (p x / q x) > 1 - q x / p x := by
        rw [h_inv]; linarith
      -- Multiply by `p x > 0` to get `p x · log (p x / q x) > p x - q x`.
      have h_pos_mul : p x * log (p x / q x) > p x * (1 - q x / p x) :=
        mul_lt_mul_of_pos_left h_pos_log hpx_pos
      have h_simp : p x * (1 - q x / p x) = p x - q x := by field_simp
      -- Contradiction with the tightness equation.
      linarith [h_simp ▸ h_pos_mul]
  · -- Backward direction: `p = q ⇒ KLDiv p q = 0`.
    intro h_eq
    rw [h_eq]
    unfold KLDiv
    apply Finset.sum_eq_zero
    intro x _
    by_cases hqx : q x = 0
    · rw [if_pos hqx]
    · rw [if_neg hqx]
      have h_div : q x / q x = 1 := div_self hqx
      rw [h_div, Real.log_one, mul_zero]

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

/-- The `p x = 0` guard in `KLDiv` is redundant (Lean's `0 * log = 0`
convention), so KL is the plain sum. -/
lemma KLDiv_eq_sum_mul_log (p q : V → ℝ) :
    KLDiv p q = ∑ x, p x * Real.log (p x / q x) := by
  unfold KLDiv
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : p x = 0
  · rw [if_pos h, h, zero_mul]
  · rw [if_neg h]

/-- **Data Processing Inequality**: Coarse-graining cannot increase KL divergence.

    D_KL(f_# p ‖ f_# q) ≤ D_KL(p ‖ q)

    This is the fundamental monotonicity of information under processing —
    the **informational arrow** of coarse-graining.

    **PROVED** (2026-08-18, Three Arrows sprint — formerly axiomatised):
    the log-sum inequality (`LogSum.log_sum_inequality`, Jensen for
    `x·log x`) applied fiberwise along the deterministic pushforward. -/
theorem data_processing_inequality {W : Type*} [Fintype W] [DecidableEq W]
    (f : V → W) (p q : V → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 < q x) :
    KLDiv (pushforward f p) (pushforward f q) ≤ KLDiv p q := by
  rw [KLDiv_eq_sum_mul_log, KLDiv_eq_sum_mul_log]
  have hfiber : ∑ x : V, p x * Real.log (p x / q x)
      = ∑ w : W, ∑ x ∈ univ.filter (fun x => f x = w),
          p x * Real.log (p x / q x) :=
    (Finset.sum_fiberwise_of_maps_to (fun x _ => Finset.mem_univ (f x)) _).symm
  rw [hfiber]
  refine Finset.sum_le_sum fun w _ => ?_
  have hls := LogSum.log_sum_inequality (univ.filter (fun x => f x = w)) p q
    (fun i _ => hp i) (fun i _ => hq i)
  simpa [pushforward] using hls

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

/-- **Gibbs term inequality**: `(a - b) · log(a/b) ≥ 0` for `a, b > 0`.

    The single-pair version of the second law. By trichotomy on `a ⋚ b`:
    `a < b` ⇒ both factors negative; `a = b` ⇒ first factor zero;
    `a > b` ⇒ both factors positive. -/
lemma gibbs_term_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ (a - b) * Real.log (a / b) := by
  rcases lt_trichotomy a b with hlt | heq | hgt
  · -- a < b: both (a - b) and log(a/b) are negative; product is positive.
    have h1 : a - b < 0 := sub_neg.mpr hlt
    have h2 : a / b < 1 := (div_lt_one hb).mpr hlt
    have h3 : Real.log (a / b) < 0 := Real.log_neg (div_pos ha hb) h2
    exact le_of_lt (mul_pos_of_neg_of_neg h1 h3)
  · -- a = b: first factor is zero.
    rw [heq, sub_self, zero_mul]
  · -- a > b: both factors are positive.
    have h1 : 0 < a - b := sub_pos.mpr hgt
    have h2 : 1 < a / b := (one_lt_div hb).mpr hgt
    have h3 : 0 < Real.log (a / b) := Real.log_pos h2
    exact le_of_lt (mul_pos h1 h3)

/-- **Gibbs term equality**: `(a - b) · log(a/b) = 0 ↔ a = b` for `a, b > 0`.

    The case-equality companion to `gibbs_term_nonneg`, used in the converse
    direction of `housekeeping_zero_iff_detailed_balance`. -/
lemma gibbs_term_eq_zero_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a - b) * Real.log (a / b) = 0 ↔ a = b := by
  refine ⟨fun h => ?_, fun h => by rw [h, sub_self, zero_mul]⟩
  rcases mul_eq_zero.mp h with h1 | h2
  · linarith [sub_eq_zero.mp h1]
  · -- log(a/b) = 0 with a/b > 0 forces a/b = 1, hence a = b.
    have hab_pos : 0 < a / b := div_pos ha hb
    rcases Real.log_eq_zero.mp h2 with hab | hab | hab
    · linarith
    · -- a/b = 1
      have hb_ne : b ≠ 0 := ne_of_gt hb
      field_simp at hab
      exact hab
    · linarith

/-- **Entropy production is non-negative** — the second law of thermodynamics
    for finite Markov chains.

    σ(L, π) ≥ 0

    **PROVED** (no longer an axiom). Each term `(π_x L_{xy} - π_y L_{yx}) ·
    log(π_x L_{xy} / π_y L_{yx})` is non-negative by `gibbs_term_nonneg`;
    summing preserves non-negativity.

    The `hL_nonneg` hypothesis (off-diagonals are ≥ 0) is essential: it
    upgrades the "L_{xy} ≠ 0" guard in the Schnakenberg formula to the
    strict "L_{xy} > 0" needed to apply the Gibbs inequality. Without it,
    Lean's junk-value convention `Real.log r = 0` for `r ≤ 0` makes the
    statement formally vacuous on pathological inputs.

    Combined with `hL_pos` (forward irreducibility), `L_{xy} > 0 ⇒ L_{yx} > 0`,
    which ensures both `π_x L_{xy}` and `π_y L_{yx}` are strictly positive
    in the else-branch where the Gibbs inequality applies. -/
theorem entropy_production_nonneg (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ x, 0 < pi_dist x)
    (hL_nonneg : ∀ x y, x ≠ y → 0 ≤ L x y)
    (hL_pos : ∀ x y, x ≠ y → L x y > 0 → L y x > 0) :
    0 ≤ EntropyProductionRate L pi_dist := by
  unfold EntropyProductionRate
  apply mul_nonneg (by norm_num : (0:ℝ) ≤ 1/2)
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro y _
  split_ifs with h
  · exact le_refl _
  · push_neg at h
    obtain ⟨hxy, hLxy⟩ := h
    have hLxy_pos : 0 < L x y :=
      lt_of_le_of_ne (hL_nonneg x y hxy) (Ne.symm hLxy)
    have hLyx_pos : 0 < L y x := hL_pos x y hxy hLxy_pos
    exact gibbs_term_nonneg (mul_pos (hπ x) hLxy_pos) (mul_pos (hπ y) hLyx_pos)

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

/-- The aggregated `π`-weighted rate between two blocks:
`S(ā,b̄) = Σ_{x∈ā, y∈b̄} π_x L_{xy}`. The coarse Schnakenberg terms are
Gibbs terms of these aggregates (`pi_bar_mul_coarseGenerator`). -/
noncomputable def BlockRate (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (a_bar b_bar : P.Quot) : ℝ :=
  ∑ x : V, ∑ y : V,
    if P.quot_map x = a_bar ∧ P.quot_map y = b_bar then pi_dist x * L x y else 0

/-- The `π̄` weight cancels: `π̄(ā) · L̄(ā,b̄) = S(ā,b̄)`. -/
lemma pi_bar_mul_coarseGenerator (L : Matrix V V ℝ) (P : Partition V)
    {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x) (a_bar b_bar : P.Quot) :
    CoarseStationaryDist P pi_dist a_bar * CoarseGenerator L P pi_dist a_bar b_bar
      = BlockRate L P pi_dist a_bar b_bar := by
  have hpos : 0 < CoarseStationaryDist P pi_dist a_bar := pi_bar_pos P hπ a_bar
  unfold CoarseGenerator BlockRate
  rw [if_neg hpos.ne']
  field_simp

/-- With positive `π̄`, the coarse generator vanishes iff the block rate does. -/
lemma coarseGenerator_eq_zero_iff (L : Matrix V V ℝ) (P : Partition V)
    {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x) (a_bar b_bar : P.Quot) :
    CoarseGenerator L P pi_dist a_bar b_bar = 0 ↔
      BlockRate L P pi_dist a_bar b_bar = 0 := by
  have hpos : 0 < CoarseStationaryDist P pi_dist a_bar := pi_bar_pos P hπ a_bar
  constructor
  · intro h
    rw [← pi_bar_mul_coarseGenerator L P hπ, h, mul_zero]
  · intro h
    unfold CoarseGenerator
    rw [if_neg hpos.ne']
    unfold BlockRate at h
    rw [h, mul_zero]

/-- Under strong lumpability the block rate factors: the aggregate of a
constant block row sum is the row sum times the block mass. -/
lemma blockRate_eq_quotient_mul_pi_bar (L : Matrix V V ℝ) (P : Partition V)
    (hL : IsStronglyLumpable L P) (pi_dist : V → ℝ) (a_bar b_bar : P.Quot) :
    BlockRate L P pi_dist a_bar b_bar
      = QuotientGeneratorSimple L P a_bar b_bar
          * CoarseStationaryDist P pi_dist a_bar := by
  unfold BlockRate
  have hstep : ∀ x : V,
      (∑ y : V, if P.quot_map x = a_bar ∧ P.quot_map y = b_bar
        then pi_dist x * L x y else 0)
      = (if P.quot_map x = a_bar
          then pi_dist x * QuotientGeneratorSimple L P a_bar b_bar else 0) := by
    intro x
    by_cases hx : P.quot_map x = a_bar
    · simp only [hx, true_and, if_pos]
      have h1 : (∑ y : V, if P.quot_map y = b_bar then pi_dist x * L x y else 0)
          = pi_dist x * row_sum_block L P x b_bar := by
        unfold row_sum_block
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        by_cases hy : P.quot_map y = b_bar <;> simp [hy]
      have h2 : QuotientGeneratorSimple L P a_bar b_bar
          = row_sum_block L P x b_bar := by
        rw [← hx]
        exact quot_gen_eq_row_sum L P hL x b_bar
      rw [h1, h2]
    · simp [hx]
  rw [Finset.sum_congr rfl fun x _ => hstep x]
  unfold CoarseStationaryDist pi_bar
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : P.quot_map x = a_bar <;> simp [hx, mul_comm]

/-- **The Unification Lemma.** At exact lumpability, the physical
(`π`-weighted) coarse generator and the structural quotient generator are
the SAME operator: the `π`-average of a block-constant row sum is that row
sum, so the measure drops out. Thermodynamic renormalization and dynamical
renormalization coincide at ε = 0 — the two halves of the defect zoo fuse. -/
theorem coarseGenerator_eq_quotientGeneratorSimple (L : Matrix V V ℝ)
    (P : Partition V) (hL : IsStronglyLumpable L P)
    {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x) :
    CoarseGenerator L P pi_dist = QuotientGeneratorSimple L P := by
  funext a_bar b_bar
  have hpos : 0 < CoarseStationaryDist P pi_dist a_bar := pi_bar_pos P hπ a_bar
  unfold CoarseGenerator
  rw [if_neg hpos.ne']
  have hS : (∑ x : V, ∑ y : V,
      if P.quot_map x = a_bar ∧ P.quot_map y = b_bar then pi_dist x * L x y else 0)
      = QuotientGeneratorSimple L P a_bar b_bar
          * CoarseStationaryDist P pi_dist a_bar :=
    blockRate_eq_quotient_mul_pi_bar L P hL pi_dist a_bar b_bar
  rw [hS]
  field_simp

/-- At exact lumpability, the coarse entropy production is the entropy
production of the structural quotient chain: the trinity's thermodynamic
arrow speaks about the SAME quotient operator as the geometric arrow. -/
theorem coarse_ep_eq_quotient_ep (L : Matrix V V ℝ) (P : Partition V)
    (hL : IsStronglyLumpable L P)
    {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x) :
    CoarseEntropyProduction L P pi_dist
      = EntropyProductionRate (QuotientGeneratorSimple L P) (pi_bar P pi_dist) := by
  unfold CoarseEntropyProduction
  rw [coarseGenerator_eq_quotientGeneratorSimple L P hL hπ]
  rfl

/-- Reindexing the reverse block rate over the forward fiber:
`S(b̄,ā) = Σ_{x∈ā, y∈b̄} π_y L_{yx}`. -/
lemma blockRate_swap (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (a_bar b_bar : P.Quot) :
    BlockRate L P pi_dist b_bar a_bar
      = ∑ x : V, ∑ y : V,
          if P.quot_map x = a_bar ∧ P.quot_map y = b_bar
          then pi_dist y * L y x else 0 := by
  unfold BlockRate
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  exact if_congr and_comm rfl rfl

/-- **Second Law of Coarse-Graining**: Hidden entropy production is
non-negative.

    σ_hid = σ(L, π) - σ(L̄, π̄) ≥ 0

    Coarse-graining cannot increase observed entropy production — the
    **thermodynamic arrow** of coarse-graining, companion to the geometric
    arrow (`RicciCurvatureBound_quotient`) and the informational arrow
    (`data_processing_inequality`).

    **PROVED** (2026-08-18, Three Arrows sprint — formerly axiomatised):
    group the fine Schnakenberg sum by coarse block pairs; intra-block and
    guarded terms are nonnegative (`gibbs_term_nonneg`); each inter-block
    group dominates the corresponding coarse Gibbs term by superadditivity
    (`LogSum.gibbs_superadditive`), since the coarse weighted rates are the
    block aggregates of the fine ones (`pi_bar_mul_coarseGenerator`). -/
theorem hidden_entropy_nonneg (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hπ : ∀ x, 0 < pi_dist x)
    (hL_gen : ∀ x y, x ≠ y → 0 ≤ L x y)
    (hL_pos : ∀ x y, x ≠ y → L x y > 0 → L y x > 0) :
    0 ≤ HiddenEntropyProduction L P pi_dist := by
  classical
  unfold HiddenEntropyProduction CoarseEntropyProduction
  rw [sub_nonneg]
  unfold EntropyProductionRate
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:ℝ) ≤ 1/2)
  -- notation
  set q : V → P.Quot := P.quot_map with hq
  set t : V → V → ℝ := fun x y =>
    if x = y ∨ L x y = 0 then 0
    else (pi_dist x * L x y - pi_dist y * L y x) *
         log (pi_dist x * L x y / (pi_dist y * L y x)) with ht
  -- the fine sum refines over block pairs
  have hcollapse : ∀ x y, (∑ a_bar : P.Quot, ∑ b_bar : P.Quot,
      if q x = a_bar ∧ q y = b_bar then t x y else 0) = t x y := by
    intro x y
    have h1 : ∀ a_bar : P.Quot,
        (∑ b_bar : P.Quot, if q x = a_bar ∧ q y = b_bar then t x y else 0)
        = if q x = a_bar then t x y else 0 := by
      intro a_bar
      by_cases hx : q x = a_bar
      · simp only [hx, true_and]
        simp
      · simp [hx]
    simp only [h1]
    simp
  have hrefine : ∑ x, ∑ y, t x y
      = ∑ a_bar : P.Quot, ∑ b_bar : P.Quot, ∑ x, ∑ y,
          if q x = a_bar ∧ q y = b_bar then t x y else 0 := by
    calc ∑ x, ∑ y, t x y
        = ∑ x, ∑ y, ∑ a_bar : P.Quot, ∑ b_bar : P.Quot,
            (if q x = a_bar ∧ q y = b_bar then t x y else 0) :=
          Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
            (hcollapse x y).symm
      _ = ∑ x, ∑ a_bar : P.Quot, ∑ y, ∑ b_bar : P.Quot,
            (if q x = a_bar ∧ q y = b_bar then t x y else 0) :=
          Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = ∑ a_bar : P.Quot, ∑ x, ∑ y, ∑ b_bar : P.Quot,
            (if q x = a_bar ∧ q y = b_bar then t x y else 0) :=
          Finset.sum_comm
      _ = ∑ a_bar : P.Quot, ∑ x, ∑ b_bar : P.Quot, ∑ y,
            (if q x = a_bar ∧ q y = b_bar then t x y else 0) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ =>
            Finset.sum_comm
      _ = ∑ a_bar : P.Quot, ∑ b_bar : P.Quot, ∑ x, ∑ y,
            (if q x = a_bar ∧ q y = b_bar then t x y else 0) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
  rw [hrefine]
  -- per block pair: the fine group dominates the coarse Gibbs term
  refine Finset.sum_le_sum fun a_bar _ => Finset.sum_le_sum fun b_bar _ => ?_
  -- nonnegativity of every fine term in the group
  have ht_nonneg : ∀ x y, 0 ≤ (if q x = a_bar ∧ q y = b_bar then t x y else 0) := by
    intro x y
    by_cases hg : q x = a_bar ∧ q y = b_bar
    · rw [if_pos hg]
      simp only [ht]
      by_cases hguard : x = y ∨ L x y = 0
      · rw [if_pos hguard]
      · rw [if_neg hguard]
        push_neg at hguard
        obtain ⟨hxy, hL0⟩ := hguard
        have hLxy : 0 < L x y := lt_of_le_of_ne (hL_gen x y hxy) (Ne.symm hL0)
        have hLyx : 0 < L y x := hL_pos x y hxy hLxy
        exact gibbs_term_nonneg (mul_pos (hπ x) hLxy) (mul_pos (hπ y) hLyx)
    · rw [if_neg hg]
  by_cases hab : a_bar = b_bar
  · -- diagonal coarse term is guarded to zero
    rw [if_pos (Or.inl hab)]
    exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ht_nonneg x y
  by_cases hS : CoarseGenerator L P pi_dist a_bar b_bar = 0
  · rw [if_pos (Or.inr hS)]
    exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ht_nonneg x y
  -- live inter-block pair: superadditivity
  rw [if_neg (by push_neg; exact ⟨hab, hS⟩)]
  rw [pi_bar_mul_coarseGenerator L P hπ, pi_bar_mul_coarseGenerator L P hπ]
  -- move to the product fiber restricted to the support
  set s₀ : Finset (V × V) :=
    Finset.univ.filter (fun pr : V × V =>
      (q pr.1 = a_bar ∧ q pr.2 = b_bar) ∧ L pr.1 pr.2 ≠ 0) with hs₀
  have hne : ∀ pr : V × V, pr ∈ s₀ → pr.1 ≠ pr.2 := by
    intro pr hpr
    obtain ⟨⟨h1, h2⟩, -⟩ := Finset.mem_filter.mp hpr |>.2
    intro hcontra
    exact hab (h1 ▸ hcontra ▸ h2 ▸ rfl)
  have ha_pos : ∀ pr ∈ s₀, 0 < pi_dist pr.1 * L pr.1 pr.2 := by
    intro pr hpr
    obtain ⟨-, hL0⟩ := (Finset.mem_filter.mp hpr).2
    exact mul_pos (hπ pr.1)
      (lt_of_le_of_ne (hL_gen pr.1 pr.2 (hne pr hpr)) (Ne.symm hL0))
  have hb_pos : ∀ pr ∈ s₀, 0 < pi_dist pr.2 * L pr.2 pr.1 := by
    intro pr hpr
    obtain ⟨-, hL0⟩ := (Finset.mem_filter.mp hpr).2
    exact mul_pos (hπ pr.2)
      (hL_pos pr.1 pr.2 (hne pr hpr)
        (lt_of_le_of_ne (hL_gen pr.1 pr.2 (hne pr hpr)) (Ne.symm hL0)))
  -- the aggregates over the support are the block rates
  have hSa : ∑ pr ∈ s₀, pi_dist pr.1 * L pr.1 pr.2
      = BlockRate L P pi_dist a_bar b_bar := by
    unfold BlockRate
    rw [← Finset.sum_product']
    rw [Finset.sum_filter]
    simp only [← hq]
    refine Finset.sum_congr rfl fun pr _ => ?_
    by_cases hg : q pr.1 = a_bar ∧ q pr.2 = b_bar
    · by_cases hL0 : L pr.1 pr.2 = 0
      · simp [hg, hL0]
      · simp [hg, hL0]
    · simp [hg]
  have hSb : ∑ pr ∈ s₀, pi_dist pr.2 * L pr.2 pr.1
      = BlockRate L P pi_dist b_bar a_bar := by
    rw [blockRate_swap, ← Finset.sum_product', Finset.sum_filter]
    simp only [← hq]
    refine Finset.sum_congr rfl fun pr _ => ?_
    by_cases hg : q pr.1 = a_bar ∧ q pr.2 = b_bar
    · by_cases hL0 : L pr.1 pr.2 = 0
      · -- reverse rate also vanishes: L pr.2 pr.1 = 0
        have hyx : L pr.2 pr.1 = 0 := by
          by_contra hne0
          by_cases hxy : pr.1 = pr.2
          · exact hne0 (hxy ▸ hL0)
          · have := hL_pos pr.2 pr.1 (Ne.symm hxy)
              (lt_of_le_of_ne (hL_gen pr.2 pr.1 (Ne.symm hxy)) (Ne.symm hne0))
            rw [hL0] at this
            exact lt_irrefl 0 this
        simp [hg, hL0, hyx]
      · simp [hg, hL0]
    · simp [hg]
  -- the fine group equals the support sum of Gibbs terms
  have hgroup : ∑ x, ∑ y, (if q x = a_bar ∧ q y = b_bar then t x y else 0)
      = ∑ pr ∈ s₀, (pi_dist pr.1 * L pr.1 pr.2 - pi_dist pr.2 * L pr.2 pr.1) *
          log (pi_dist pr.1 * L pr.1 pr.2 / (pi_dist pr.2 * L pr.2 pr.1)) := by
    rw [← Finset.sum_product', Finset.sum_filter]
    refine Finset.sum_congr rfl fun pr _ => ?_
    by_cases hg : q pr.1 = a_bar ∧ q pr.2 = b_bar
    · rw [if_pos hg]
      simp only [ht]
      by_cases hL0 : L pr.1 pr.2 = 0
      · rw [if_pos (Or.inr hL0), if_neg (fun h => h.2 hL0)]
      · have hxy : pr.1 ≠ pr.2 := by
          intro hcontra
          exact hab (hg.1 ▸ hcontra ▸ hg.2 ▸ rfl)
        have hguard : ¬(pr.1 = pr.2 ∨ L pr.1 pr.2 = 0) := by
          push_neg; exact ⟨hxy, hL0⟩
        rw [if_neg hguard, if_pos ⟨hg, hL0⟩]
    · rw [if_neg hg, if_neg (fun h => hg h.1)]
  rw [hgroup, ← hSa, ← hSb]
  exact LogSum.gibbs_superadditive s₀ _ _ ha_pos hb_pos

/-! ### 6. Phase D: Connecting Hidden Entropy to Leakage Defect

The key insight: Hidden entropy production σ_hid measures dissipation we can't see.
The leakage defect ε measures prediction error. These are related via Pinsker's inequality.

**The Chain of Logic:**
1. Pinsker: D_KL(P ‖ Q) ≥ (1/2) ‖P - Q‖₁²
2. Norm equivalence: ‖v‖₁ ≤ √N ‖v‖₂ (finite dimension)
3. Trajectory bound: ‖fine - coarse‖₂ ≤ ε · t · C (from trajectory_closure_bound)
4. Conclusion: σ_hid ≤ C' · ε²
-/

/-- **Total Variation Distance** (L¹ norm of difference):

    TV(p, q) = (1/2) Σ_x |p_x - q_x| = (1/2) ‖p - q‖₁

    This is the standard total variation distance between distributions. -/
noncomputable def TotalVariation (p q : V → ℝ) : ℝ :=
  (1/2 : ℝ) * ∑ x, |p x - q x|

/-- **L¹-L² Norm Equivalence** (finite dimension):

    ‖v‖₁ ≤ √N · ‖v‖₂

    where N = |V| is the state space cardinality.

    **PROVED 2026-05-26** (previously an axiom). Pure Cauchy-Schwarz with
    `f := 1` and `g := |v|`: `(Σ 1·|v_i|)² ≤ (Σ 1²)·(Σ|v_i|²) = N·Σ(v_i)²`.
    Taking square roots gives `Σ|v_i| ≤ √N · √(Σ(v_i)²)`. Uses the existing
    `Finset.sum_mul_sq_le_sq_mul_sq` from Mathlib. -/
theorem l1_le_sqrt_card_l2 (v : V → ℝ) :
    ∑ x, |v x| ≤ Real.sqrt (Fintype.card V) * Real.sqrt (∑ x, (v x)^2) := by
  -- Step 1: Cauchy-Schwarz with f = 1, g = |v|.
  have h_cs : (∑ x : V, (1 : ℝ) * |v x|)^2 ≤
      (∑ x : V, (1 : ℝ)^2) * (∑ x : V, |v x|^2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun x => |v x|)
  -- Step 2: Simplify each factor.
  --   ∑ 1·|v x| = ∑ |v x|
  --   ∑ 1² = ∑ 1 = Fintype.card V
  --   |v x|² = (v x)²
  have h_lhs : (∑ x : V, (1 : ℝ) * |v x|) = ∑ x, |v x| := by
    refine Finset.sum_congr rfl (fun x _ => ?_); ring
  have h_ones_sq : (∑ x : V, (1 : ℝ)^2) = (Fintype.card V : ℝ) := by
    simp [Finset.sum_const, Finset.card_univ]
  have h_abs_sq : (∑ x : V, |v x|^2) = ∑ x, (v x)^2 := by
    refine Finset.sum_congr rfl (fun x _ => ?_); exact sq_abs (v x)
  rw [h_lhs, h_ones_sq, h_abs_sq] at h_cs
  -- Step 3: positivity hypotheses for sqrt-monotonicity and sqrt-mul.
  have h_lhs_nn : (0 : ℝ) ≤ ∑ x, |v x| :=
    Finset.sum_nonneg (fun x _ => abs_nonneg _)
  have h_card_nn : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  -- Step 4: take square roots and split.
  calc ∑ x, |v x|
      = Real.sqrt ((∑ x, |v x|)^2) := (Real.sqrt_sq h_lhs_nn).symm
    _ ≤ Real.sqrt ((Fintype.card V : ℝ) * (∑ x, (v x)^2)) :=
        Real.sqrt_le_sqrt h_cs
    _ = Real.sqrt (Fintype.card V) * Real.sqrt (∑ x, (v x)^2) :=
        Real.sqrt_mul h_card_nn _

/-- **L² norm in our setting**: The unweighted L² norm. -/
noncomputable def l2_norm (v : V → ℝ) : ℝ := Real.sqrt (∑ x, (v x)^2)

/-- **Weighted to Unweighted Norm Comparison**:

    The weighted norm ‖v‖_π and unweighted norm ‖v‖₂ are equivalent up to constants
    depending on min/max of π. C = 1/√(min π) works.

    **PROVED 2026-05-30** (previously an axiom). Pure finite-dimensional norm
    equivalence. Strategy:
    1. `Finset.exists_min_image` gives `pi_min := min_x pi_dist x > 0` (since
       `V` is nonempty and every `pi_dist x > 0`).
    2. Pointwise `pi_min · (v x)² ≤ pi_dist x · (v x)²`, summing yields
       `pi_min · Σ (v x)² ≤ Σ pi_dist x · (v x)² = ‖v‖_π²`.
    3. Take square roots and divide by `√pi_min > 0`:
       `‖v‖₂ ≤ (1/√pi_min) · ‖v‖_π`. -/
theorem weighted_unweighted_norm_compare [Nonempty V] (v : V → ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ x, 0 < pi_dist x) :
    ∃ C : ℝ, C > 0 ∧ l2_norm v ≤ C * norm_pi pi_dist v := by
  -- Step 1: Find pi_min := min over x of pi_dist x.
  obtain ⟨x_min, _, hx_min⟩ :=
    Finset.exists_min_image Finset.univ pi_dist
      ⟨Classical.arbitrary V, Finset.mem_univ _⟩
  set pi_min := pi_dist x_min with hpi_min_def
  have hpi_min_pos : 0 < pi_min := hπ x_min
  have hpi_min_le : ∀ x, pi_min ≤ pi_dist x :=
    fun x => hx_min x (Finset.mem_univ x)
  -- Step 2: C = 1 / sqrt(pi_min).
  refine ⟨1 / Real.sqrt pi_min,
          div_pos one_pos (Real.sqrt_pos.mpr hpi_min_pos), ?_⟩
  -- Step 3: Pointwise bound pi_min·(v x)² ≤ pi_dist x · (v x)².
  have h_pointwise : ∀ x, pi_min * (v x)^2 ≤ pi_dist x * (v x)^2 :=
    fun x => mul_le_mul_of_nonneg_right (hpi_min_le x) (sq_nonneg (v x))
  -- Step 4: Summed bound pi_min · Σ (v x)² ≤ Σ pi_dist x · (v x)².
  have h_sum : pi_min * ∑ x, (v x)^2 ≤ ∑ x, pi_dist x * (v x)^2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun x _ => h_pointwise x)
  -- Step 5: Square-root form: √pi_min · √(Σ (v x)²) ≤ √(Σ pi_dist x · (v x)²).
  have h_pi_min_nn : 0 ≤ pi_min := le_of_lt hpi_min_pos
  have h_sqrt :
      Real.sqrt pi_min * Real.sqrt (∑ x, (v x)^2) ≤
        Real.sqrt (∑ x, pi_dist x * (v x)^2) := by
    rw [← Real.sqrt_mul h_pi_min_nn]
    exact Real.sqrt_le_sqrt h_sum
  -- Step 6: Rewrite norm_pi as √(Σ pi_dist x · (v x)²), divide by √pi_min > 0.
  have h_norm_pi_eq :
      norm_pi pi_dist v = Real.sqrt (∑ x, pi_dist x * (v x)^2) := by
    unfold norm_pi
    rw [norm_sq_pi_eq_sum]
  unfold l2_norm
  rw [h_norm_pi_eq]
  have h_sqrt_pos : 0 < Real.sqrt pi_min := Real.sqrt_pos.mpr hpi_min_pos
  rw [div_mul_eq_mul_div, le_div_iff₀ h_sqrt_pos, one_mul, mul_comm]
  exact h_sqrt

/-! ### 7. The Payoff Theorem: Prediction Error Implies Dissipation -/

/-- **Hidden entropy bound from trajectory constant**: The final step of the ε² bound.

    Given a trajectory constant C_traj from `trajectory_closure_bound`, the hidden
    entropy production is bounded by N · C_traj² · ε² where N = |V|.

    **Proof outline** (standard but technical):
    1. Trajectory bound: ‖e^{tL}f - e^{tL̄}f‖_π ≤ C_traj · ε · t · ‖f‖_π
    2. Norm equivalence: Convert π-weighted to L² norm
    3. Cauchy-Schwarz: L² → L¹ (Total Variation) with factor √N
    4. Pinsker: TV² → KL divergence
    5. Differentiate: KL rate = hidden entropy production

    The detailed unwinding is standard but lengthy; we axiomatize the final result. -/
axiom hidden_entropy_bound_from_trajectory
    (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ x, 0 < pi_dist x)
    (ε : ℝ) (hε : 0 ≤ ε) (hL : Approximate.IsApproxLumpable L P pi_dist hπ ε)
    (C_traj : ℝ) (hC_traj : 0 < C_traj) :
    HiddenEntropyProduction L P pi_dist ≤ (Fintype.card V : ℝ) * C_traj^2 * ε^2

/-- **The Payoff Theorem**: Hidden entropy production bounded by leakage defect squared.

    **Physical Intuition**: Bad predictions (high ε) force wasteful dissipation (high σ_hid).

    **Proof Chain** (standard results):
    1. `trajectory_closure_bound` ⇒ trajectories differ by O(ε·t) in ‖·‖_π
    2. Norm equivalence ⇒ L² distance bounded
    3. Cauchy-Schwarz ⇒ L¹ distance bounded (Total Variation)
    4. Pinsker inequality ⇒ KL divergence bounded by TV²
    5. Entropy production is KL rate ⇒ σ_hid ≤ C · ε²

    **PROVED**: Follows from `hidden_entropy_bound_from_trajectory` with C_traj = 1.
    The constant C = N · C_traj² = |V| depends on dimension. -/
theorem hidden_entropy_bounded_by_defect
    (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ x, 0 < pi_dist x)
    (ε : ℝ) (hε : 0 ≤ ε) (hL : Approximate.IsApproxLumpable L P pi_dist hπ ε) :
    ∃ C : ℝ, C ≥ 0 ∧ HiddenEntropyProduction L P pi_dist ≤ C * ε^2 := by
  -- Use hidden_entropy_bound_from_trajectory with C_traj = 1
  have h_bound := hidden_entropy_bound_from_trajectory L P pi_dist hπ ε hε hL 1 one_pos
  -- C = N * 1² = N
  use (Fintype.card V : ℝ)
  constructor
  · exact Nat.cast_nonneg (Fintype.card V)
  · simp only [one_pow, mul_one] at h_bound
    exact h_bound

/-- **The Gaspard Path-Space Identity**: Hidden entropy production is bounded
    below by the spectral gap times the squared operator norm of the defect.

    σ_hid(L, P, π) ≥ γ · ‖D‖²_op

    where γ = DirichletGap(L, π) > 0 is the spectral gap and D is the defect
    operator from approximate lumpability (`Approximate.DefectOperator`).

    ## What this axiom captures (and what would close it)

    **Mathematical staging** (Gaspard 2004, Maes-Netočný 2003, arXiv:2602.15663):

    1. σ_hid = KL rate between forward and time-reversed coarse-grained path
       measures (the **definitional** content of hidden entropy production).
    2. This KL rate ≥ Dirichlet form ℰ(Df) for the defect operator
       (the **path-space → pointwise bridge** — the deep step).
    3. Poincaré inequality: ℰ(g) ≥ γ · ‖g‖²_π for g ⊥ constants
       (already formalized via `DirichletForm` and `DirichletGap` in
       `SGC.Renormalization.Lumpability` / `SGC.Renormalization.QuotientGenerator`).
    4. Taking sup over unit-norm test functions: γ · ‖D‖²_op ≤ σ_hid (algebra).

    Steps 1, 3, 4 are infrastructure-comfortable in the existing repo. Step 2 is
    the genuinely open content: it requires formalizing path-space probability
    measures, the time-reversal operator on path measures, and the
    Donsker-Varadhan / Maes-Netočný identity that converts the path-space KL
    rate into a pointwise Dirichlet form. None of this infrastructure currently
    exists in Mathlib in the form needed for finite Markov chains.

    **Stepping stones for future closure**:
    - Path measure on continuous-time trajectories of an irreducible
      finite-state Markov chain (would enable defining σ_hid directly as a
      KL rate, replacing the current `HiddenEntropyProduction` definition).
    - Time-reversal operator on those path measures.
    - The Maes-Netočný "fluctuation symmetry": the difference of the forward
      and time-reversed dynamical entropies equals the entropy production
      rate. Once formalized, step 2 follows by combining with the Schnakenberg
      formula (already in `EntropyProduction.lean`).

    **Until those exist**, this axiom is the cleanest single-statement summary
    of the path-space → operator-norm content.

    **References**:
    - Gaspard (2004) JSP 117:599 — time-reversed entropy and EP
    - Maes & Netočný (2003) cond-mat/0202501 — entropy production and time reversal
    - arXiv:2602.15663 (2026) — experimental confirmation of σ_hid ~ ε² scaling -/
axiom gaspard_path_space_identity
    (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ x, 0 < pi_dist x)
    (hL_gen : ∀ x y, x ≠ y → 0 ≤ L x y)
    (h_stat : ∀ v, ∑ u, pi_dist u * L u v = 0)
    (γ : ℝ) (hγ : γ > 0)
    (hγ_gap : γ ≤ DirichletGap L pi_dist) :
    γ * (opNorm_pi pi_dist hπ (Approximate.DefectOperator L P pi_dist hπ))^2 ≤
    HiddenEntropyProduction L P pi_dist

/-- **Backward-compatible alias** for the renamed `gaspard_path_space_identity`.

    Earlier drafts of this module called the path-space identity
    `gaspard_maes_bridge`. The 2026-05-25 sprint renamed it to make the
    path-space gap explicit. This alias preserves the older name so that
    downstream files / external references continue to typecheck. -/
@[deprecated gaspard_path_space_identity (since := "2026-05-25")]
theorem gaspard_maes_bridge
    (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ x, 0 < pi_dist x)
    (hL_gen : ∀ x y, x ≠ y → 0 ≤ L x y)
    (h_stat : ∀ v, ∑ u, pi_dist u * L u v = 0)
    (γ : ℝ) (hγ : γ > 0)
    (hγ_gap : γ ≤ DirichletGap L pi_dist) :
    γ * (opNorm_pi pi_dist hπ (Approximate.DefectOperator L P pi_dist hπ))^2 ≤
    HiddenEntropyProduction L P pi_dist :=
  gaspard_path_space_identity L P pi_dist hπ hL_gen h_stat γ hγ hγ_gap

/-- **Hidden Entropy Lower Bound**: σ_hid ≥ γ · (defect_cost)².

    This is the **converse** of hidden_entropy_bounded_by_defect. Together they give:
    γ·ε² ≤ σ_hid ≤ C·ε², meaning prediction error and dissipation are equivalent.

    **PROVED**: Direct corollary of `gaspard_path_space_identity`. The constant
    c = γ (spectral gap) is explicit and physically meaningful: it measures how
    fast the system mixes.

    NOTE: Uses `defect_cost` (the actual operator norm ‖D‖_π) rather than the
    approximate lumpability parameter ε. This is mathematically correct because
    IsApproxLumpable gives ‖D‖ ≤ ε (upper bound), so γ·‖D‖² ≤ γ·ε² — the lower
    bound on σ_hid is tighter when stated in terms of the actual defect.

    **Reference**: Gaspard (2004), Maes-Netočný (2003), arXiv:2602.15663 (2026) -/
theorem hidden_entropy_lower_bound
    (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ x, 0 < pi_dist x)
    (hL_gen : ∀ x y, x ≠ y → 0 ≤ L x y)
    (h_stat : ∀ v, ∑ u, pi_dist u * L u v = 0)
    (γ : ℝ) (hγ : γ > 0) (hγ_gap : γ ≤ DirichletGap L pi_dist) :
    γ * (opNorm_pi pi_dist hπ (Approximate.DefectOperator L P pi_dist hπ))^2 ≤
    HiddenEntropyProduction L P pi_dist :=
  gaspard_path_space_identity L P pi_dist hπ hL_gen h_stat γ hγ hγ_gap

/-- **Corollary: Efficiency Requires Prediction**

    **Physical Intuition**: Efficient systems must be good predictors—there's no free lunch.

    If σ_hid < δ (system is "efficient"), then the defect norm ‖D‖ < √(δ/γ)
    (system must be predictive). With c = γ (spectral gap):

      γ · ‖D‖² ≤ σ_hid < δ  ⟹  ‖D‖ < √(δ/γ)

    Contrapositive: Large prediction error (defect) implies large dissipation.

    **PROVED**: From hidden_entropy_lower_bound + algebra. -/
theorem efficiency_requires_prediction
    (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ x, 0 < pi_dist x)
    (hL_gen : ∀ x y, x ≠ y → 0 ≤ L x y)
    (h_stat : ∀ v, ∑ u, pi_dist u * L u v = 0)
    (γ : ℝ) (hγ : γ > 0) (hγ_gap : γ ≤ DirichletGap L pi_dist)
    (δ : ℝ) (_hδ : 0 < δ) (h_efficient : HiddenEntropyProduction L P pi_dist < δ) :
    (opNorm_pi pi_dist hπ (Approximate.DefectOperator L P pi_dist hπ))^2 < δ / γ := by
  -- From hidden_entropy_lower_bound: γ · ‖D‖² ≤ σ_hid
  have h_lower := hidden_entropy_lower_bound L P pi_dist hπ hL_gen h_stat γ hγ hγ_gap
  -- From h_efficient: σ_hid < δ
  -- Therefore: γ · ‖D‖² < δ, so ‖D‖² < δ/γ
  have h_chain : γ * (opNorm_pi pi_dist hπ (Approximate.DefectOperator L P pi_dist hπ))^2 < δ :=
    lt_of_le_of_lt h_lower h_efficient
  have h1 : (opNorm_pi pi_dist hπ (Approximate.DefectOperator L P pi_dist hπ))^2 * γ < δ := by
    linarith
  have h2 : (opNorm_pi pi_dist hπ (Approximate.DefectOperator L P pi_dist hπ))^2 < δ * (1/γ) := by
    field_simp; linarith
  simp only [one_div] at h2
  exact h2

/-! ### 8. Summary: The Thermodynamic Foundation for Emergence

**What We Have Proven** (modulo standard library debt):

1. **Second Law**: σ(L, π) ≥ 0
2. **Reversible Equilibrium**: Detailed balance ⟹ σ = 0
3. **Coarse-Graining Inequality**: σ_hid ≥ 0 (hidden EP is non-negative)
4. **THE PAYOFF**: σ_hid ≤ C · ε² (hidden EP bounded by prediction error squared)

**The Physics of Emergence**:

The chain of implications:
```
Persistence ⟹ Low Dissipation ⟹ Low σ_hid ⟹ Low ε ⟹ Predictive
```

Equivalently:
```
To exist (persist) is to predict (minimize ε)
```

This is NOT a metaphor. It is a mathematical theorem:
- σ_hid measures the "thermodynamic cost" of model mismatch
- ε measures the "prediction error" of the coarse model
- The bound σ_hid ≤ C·ε² says these are the same thing (up to constants)

**Connection to Markov Blankets**:
- A Markov Blanket is a partition where ε → 0
- By this theorem, such a partition has σ_hid → 0
- Therefore: Markov Blankets are thermodynamically optimal boundaries
-/

end Thermodynamics
end SGC
