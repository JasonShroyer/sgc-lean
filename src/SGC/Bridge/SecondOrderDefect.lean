/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith

/-!
# The second-order law for the planner defect on block-constant data (P31)

Let `P` be an idempotent (`P * P = P`) in a normed ring — the conditional-expectation projection onto
block-constant observables — and `K` a transition operator. The planner-defect operator is
`B n = P K^n − (P K P)^n P`. On block-constant inputs (`B n * P`) its growth is governed by two
*couplings*: the reverse leakage `‖P K (1−P)‖` and the forward leakage `‖(1−P) K P‖`, under two
*contraction assumptions*: `‖P K^k P‖ ≤ 1` for every `k` (the coarse propagator does not amplify
block-constant data) and `‖(1−P) K (1−P)‖ ≤ 1` (the within-block propagator does not amplify).

**Theorem (P31).** `2 ‖B n P‖ ≤ n (n−1) · ‖P K (1−P)‖ · ‖(1−P) K P‖`.

Consequences: the defect on block-constant data is **zero at horizon one** and **second order** in the
couplings thereafter, with horizon factor `n(n−1)/2` — exactly the exponent and the `n = 1` vanishing
measured in `defect_scaling_v1` (slopes 1.99 at `n = 2, 4`, `≤ 5·10⁻¹⁶` at `n = 1`). The recursion
alone does not make approximate closure universally safe: both contraction assumptions are used, and
the bound concerns block-constant inputs only — for inputs with a within-block component the defect is
first order (`B n (1−P)` is not controlled here).

In the `π`-weighted `L²` geometry of a reversible chain both contraction assumptions hold (`K` is a
contraction and `P` an orthogonal projection); they are stated as hypotheses so the theorem is usable
where that geometry is not available.
-/

namespace SGC.Bridge.SecondOrderDefect

open Finset

section

variable {R : Type*} [NormedRing R]

/-- Idempotence of the complementary projection. -/
theorem compl_idem (P : R) (hP : P * P = P) : (1 - P) * (1 - P) = 1 - P := by
  calc (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
    _ = 1 - P := by rw [hP]; abel

/-- The `k`-step reverse leakage splits through the block decomposition of one step. -/
theorem rev_leak_step (P K : R) (hP : P * P = P) (k : ℕ) :
    P * K ^ (k + 1) * (1 - P) =
      (P * K ^ k * P) * (P * K * (1 - P)) + (P * K ^ k * (1 - P)) * ((1 - P) * K * (1 - P)) := by
  have hQ := compl_idem P hP
  have h1 : P + (1 - P) = 1 := by abel
  symm
  calc (P * K ^ k * P) * (P * K * (1 - P)) + (P * K ^ k * (1 - P)) * ((1 - P) * K * (1 - P))
      = P * K ^ k * (P * P) * K * (1 - P) + P * K ^ k * ((1 - P) * (1 - P)) * K * (1 - P) := by
        noncomm_ring
    _ = P * K ^ k * P * K * (1 - P) + P * K ^ k * (1 - P) * K * (1 - P) := by rw [hP, hQ]
    _ = P * K ^ k * (P + (1 - P)) * K * (1 - P) := by noncomm_ring
    _ = P * K ^ (k + 1) * (1 - P) := by rw [h1, mul_one, pow_succ]; noncomm_ring

/-- **k-step reverse leakage is at most `k` times the one-step reverse leakage.** -/
theorem rev_leak_bound (P K : R) (hP : P * P = P) (hPKP : ∀ k, ‖P * K ^ k * P‖ ≤ 1)
    (hQKQ : ‖(1 - P) * K * (1 - P)‖ ≤ 1) (k : ℕ) :
    ‖P * K ^ k * (1 - P)‖ ≤ (k : ℝ) * ‖P * K * (1 - P)‖ := by
  induction k with
  | zero =>
    have : P * K ^ 0 * (1 - P) = 0 := by
      rw [pow_zero, mul_one]
      calc P * (1 - P) = P - P * P := by noncomm_ring
        _ = 0 := by rw [hP, sub_self]
    rw [this, norm_zero]; simp
  | succ k ih =>
    rw [rev_leak_step P K hP k]
    have hε : 0 ≤ ‖P * K * (1 - P)‖ := norm_nonneg _
    have hA : ‖(P * K ^ k * P) * (P * K * (1 - P))‖ ≤ 1 * ‖P * K * (1 - P)‖ :=
      le_trans (norm_mul_le _ _) (mul_le_mul_of_nonneg_right (hPKP k) hε)
    have hB : ‖(P * K ^ k * (1 - P)) * ((1 - P) * K * (1 - P))‖ ≤ ((k : ℝ) * ‖P * K * (1 - P)‖) * 1 :=
      le_trans (norm_mul_le _ _) (mul_le_mul ih hQKQ (norm_nonneg _) (by positivity))
    have := norm_add_le ((P * K ^ k * P) * (P * K * (1 - P))) ((P * K ^ k * (1 - P)) * ((1 - P) * K * (1 - P)))
    push_cast
    linarith

/-- The planner-defect operator on block-constant inputs. -/
def defectP (P K : R) (n : ℕ) : R := (P * K ^ n - (P * K * P) ^ n * P) * P

/-- One step of the defect on block-constant inputs: propagate, plus reverse leakage times forward leakage. -/
theorem defectP_step (P K : R) (hP : P * P = P) (k : ℕ) :
    defectP P K (k + 1) = defectP P K k * (P * K * P) + (P * K ^ k * (1 - P)) * ((1 - P) * K * P) := by
  unfold defectP
  have hQ := compl_idem P hP
  have h1 : P + (1 - P) = 1 := by abel
  have hPP : P * (P * K * P) = P * K * P := by rw [← mul_assoc, ← mul_assoc, hP]
  have hQQ : (1 - P) * ((1 - P) * K * P) = (1 - P) * K * P := by rw [← mul_assoc, ← mul_assoc, hQ]
  have hPKPP : P * K * P * P = P * K * P := by rw [mul_assoc (P * K) P P, hP]
  have hpow : (P * K * P) ^ (k + 1) * P = (P * K * P) ^ k * (P * K * P) := by
    rw [pow_succ, mul_assoc ((P * K * P) ^ k) (P * K * P) P, hPKPP]
  have hL : (P * K ^ (k + 1) - (P * K * P) ^ (k + 1) * P) * P
      = P * K ^ (k + 1) * P - (P * K * P) ^ k * (P * K * P) := by
    rw [sub_mul, mul_assoc ((P * K * P) ^ (k + 1)) P P, hP, hpow]
  have hsplit : P * K ^ (k + 1) * P = P * K ^ k * P * K * P + P * K ^ k * (1 - P) * K * P := by
    calc P * K ^ (k + 1) * P = P * K ^ k * (P + (1 - P)) * K * P := by rw [h1, mul_one, pow_succ]; noncomm_ring
      _ = P * K ^ k * P * K * P + P * K ^ k * (1 - P) * K * P := by noncomm_ring
  have hR1 : (P * K ^ k - (P * K * P) ^ k * P) * P * (P * K * P)
      = P * K ^ k * P * K * P - (P * K * P) ^ k * (P * K * P) := by
    rw [sub_mul, sub_mul, mul_assoc (P * K ^ k) P (P * K * P), hPP, mul_assoc ((P * K * P) ^ k) P P, hP,
      mul_assoc ((P * K * P) ^ k) P (P * K * P), hPP]
    noncomm_ring
  have hR2 : (P * K ^ k * (1 - P)) * ((1 - P) * K * P) = P * K ^ k * (1 - P) * K * P := by
    rw [mul_assoc (P * K ^ k) (1 - P) ((1 - P) * K * P), hQQ]
    noncomm_ring
  rw [hL, hsplit, hR1, hR2]
  abel

/-- Summed form of the bound. -/
theorem defectP_bound_sum (P K : R) (hP : P * P = P) (hPKP : ∀ k, ‖P * K ^ k * P‖ ≤ 1)
    (hQKQ : ‖(1 - P) * K * (1 - P)‖ ≤ 1) (n : ℕ) :
    ‖defectP P K n‖ ≤ (∑ k ∈ range n, (k : ℝ)) * (‖P * K * (1 - P)‖ * ‖(1 - P) * K * P‖) := by
  induction n with
  | zero =>
    have : defectP P K 0 = 0 := by
      unfold defectP; rw [pow_zero, pow_zero, mul_one, one_mul, sub_self, zero_mul]
    rw [this, norm_zero]; simp
  | succ k ih =>
    rw [defectP_step P K hP k, Finset.sum_range_succ, add_mul]
    have hεr : 0 ≤ ‖P * K * (1 - P)‖ := norm_nonneg _
    have hεf : 0 ≤ ‖(1 - P) * K * P‖ := norm_nonneg _
    have hPKP1 : ‖P * K * P‖ ≤ 1 := by simpa using hPKP 1
    have hA : ‖defectP P K k * (P * K * P)‖ ≤ ‖defectP P K k‖ * 1 :=
      le_trans (norm_mul_le _ _) (mul_le_mul_of_nonneg_left hPKP1 (norm_nonneg _))
    have hB : ‖(P * K ^ k * (1 - P)) * ((1 - P) * K * P)‖ ≤ ((k : ℝ) * ‖P * K * (1 - P)‖) * ‖(1 - P) * K * P‖ :=
      le_trans (norm_mul_le _ _) (mul_le_mul_of_nonneg_right (rev_leak_bound P K hP hPKP hQKQ k) hεf)
    have := norm_add_le (defectP P K k * (P * K * P)) ((P * K ^ k * (1 - P)) * ((1 - P) * K * P))
    nlinarith [this, hA, hB, ih, hεr, hεf, mul_nonneg hεr hεf]

/-- **P31 (closed form).** `2 ‖B n P‖ ≤ n (n − 1) · ‖P K (1−P)‖ · ‖(1−P) K P‖`. -/
theorem defectP_second_order (P K : R) (hP : P * P = P) (hPKP : ∀ k, ‖P * K ^ k * P‖ ≤ 1)
    (hQKQ : ‖(1 - P) * K * (1 - P)‖ ≤ 1) (n : ℕ) :
    2 * ‖defectP P K n‖ ≤ ((n * (n - 1) : ℕ) : ℝ) * (‖P * K * (1 - P)‖ * ‖(1 - P) * K * P‖) := by
  have h := defectP_bound_sum P K hP hPKP hQKQ n
  have hsum : (∑ k ∈ range n, (k : ℝ)) * 2 = ((n * (n - 1) : ℕ) : ℝ) := by
    have h := Finset.sum_range_id_mul_two n
    have h' : (((∑ i ∈ range n, i : ℕ) : ℕ) : ℝ) * 2 = ((n * (n - 1) : ℕ) : ℝ) := by exact_mod_cast h
    rw [Nat.cast_sum] at h'
    exact h'
  have hnn : 0 ≤ ‖P * K * (1 - P)‖ * ‖(1 - P) * K * P‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  calc 2 * ‖defectP P K n‖ ≤ 2 * ((∑ k ∈ range n, (k : ℝ)) * (‖P * K * (1 - P)‖ * ‖(1 - P) * K * P‖)) := by
        linarith
    _ = ((∑ k ∈ range n, (k : ℝ)) * 2) * (‖P * K * (1 - P)‖ * ‖(1 - P) * K * P‖) := by ring
    _ = ((n * (n - 1) : ℕ) : ℝ) * (‖P * K * (1 - P)‖ * ‖(1 - P) * K * P‖) := by rw [hsum]

/-- **Horizon one is exact on block-constant data**, whatever the couplings. -/
theorem defectP_one (P K : R) (hP : P * P = P) : defectP P K 1 = 0 := by
  unfold defectP
  rw [pow_one, pow_one]
  calc (P * K - P * K * P * P) * P = P * K * P - P * K * (P * P) * P := by noncomm_ring
    _ = P * K * P - P * K * P * P := by rw [hP]
    _ = P * K * P - P * K * (P * P) := by noncomm_ring
    _ = 0 := by rw [hP, sub_self]

end

end SGC.Bridge.SecondOrderDefect
