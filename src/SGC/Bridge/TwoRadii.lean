/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Bridge.DecisionHorizon

/-!
# Two radii: coarse-graining plus estimation, in total variation

`DecisionHorizon` bounds the distance between the true law `p_t` and the prediction `p̄_t` of
the **true** coarse model by the orbit radius. A learning agent predicts with an **estimated**
coarse model `K̂` instead. The extra error is an estimation term, and its transfer from kernel
error to prediction error is the L¹ (total-variation) face of the contractive perturbation
bound: stochastic kernels contract the L¹ norm of signed measures, so for laws evolved as row
vectors

  `‖w·(X̂ⁿ − Xⁿ)‖₁ ≤ Σ_{k<n} ‖(w·X̂ᵏ)·(X̂ − X)‖₁ ≤ n · ‖w‖₁ · max_a ‖X̂_a − X_a‖₁`.

No semigroup, spectral gap, or reversibility is needed: only row-stochasticity of `X̂`.
The two-radii certificate then reads

  `‖p_t − p̂_t‖₁ ≤ orbitRadius + estimationRadius`,

and `EstimatedDecision` turns any such radius into refine/stop certificates. The
concentration input — how large `max_a ‖K̂_a − K_a‖₁` is with probability `1 − δ` — is a
hypothesis here, as the L¹ radius was in `EstimatedDecision`; it is the one place where
sampling statistics enter.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SGC.Bridge.TwoRadii

open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- L¹ norm of a (signed) measure on `V`. -/
def l1 (w : V → ℝ) : ℝ := ∑ x, |w x|

/-- Row-wise L¹ distance between two kernels, maximised over rows: `max_a Σ_b |X a b − Y a b|`. -/
def rowL1Dist [Nonempty V] (X Y : Matrix V V ℝ) : ℝ :=
  univ.sup' univ_nonempty (fun a => ∑ b, |X a b - Y a b|)

lemma l1_nonneg (w : V → ℝ) : 0 ≤ l1 w := Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma l1_add_le (v w : V → ℝ) : l1 (v + w) ≤ l1 v + l1 w := by
  unfold l1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun x _ => abs_add_le _ _

/-- **Stochastic kernels contract total variation**: if `X` has nonnegative entries and unit row
sums, `‖w·X‖₁ ≤ ‖w‖₁`. -/
lemma l1_vecMul_le_of_stochastic (X : Matrix V V ℝ) (hnn : ∀ a b, 0 ≤ X a b)
    (hrow : ∀ a, ∑ b, X a b = 1) (w : V → ℝ) : l1 (w ᵥ* X) ≤ l1 w := by
  unfold l1
  calc ∑ b, |(w ᵥ* X) b|
      = ∑ b, |∑ a, w a * X a b| := by simp [Matrix.vecMul, dotProduct]
    _ ≤ ∑ b, ∑ a, |w a| * X a b := by
        apply Finset.sum_le_sum; intro b _
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun a _ => by rw [abs_mul, abs_of_nonneg (hnn a b)]
    _ = ∑ a, |w a| * ∑ b, X a b := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]
    _ = ∑ a, |w a| := by simp [hrow]

/-- A single kernel step moves a measure by at most its L¹ mass times the row-L¹ kernel gap. -/
lemma l1_vecMul_sub_le [Nonempty V] (X Y : Matrix V V ℝ) (w : V → ℝ) :
    l1 (w ᵥ* (X - Y)) ≤ l1 w * rowL1Dist X Y := by
  unfold l1 rowL1Dist
  calc ∑ b, |(w ᵥ* (X - Y)) b|
      = ∑ b, |∑ a, w a * (X a b - Y a b)| := by simp [Matrix.vecMul, dotProduct]
    _ ≤ ∑ b, ∑ a, |w a| * |X a b - Y a b| := by
        apply Finset.sum_le_sum; intro b _
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun a _ => abs_mul _ _
    _ = ∑ a, |w a| * ∑ b, |X a b - Y a b| := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]
    _ ≤ ∑ a, |w a| * univ.sup' univ_nonempty (fun a => ∑ b, |X a b - Y a b|) := by
        apply Finset.sum_le_sum; intro a _
        exact mul_le_mul_of_nonneg_left (Finset.le_sup' (fun a => ∑ b, |X a b - Y a b|) (mem_univ a))
          (abs_nonneg _)
    _ = (∑ a, |w a|) * _ := by rw [Finset.sum_mul]

/-- **Orbit telescoping in total variation.** For a row-stochastic `X̂` and any `Y`,
`‖w·(X̂ⁿ − Yⁿ)‖₁ ≤ Σ_{k<n} ‖(w·Yᵏ)·(X̂ − Y)‖₁`. -/
theorem l1_vecMul_pow_sub_pow_le_sum (Xh Y : Matrix V V ℝ)
    (hnn : ∀ a b, 0 ≤ Xh a b) (hrow : ∀ a, ∑ b, Xh a b = 1) (w : V → ℝ) (n : ℕ) :
    l1 (w ᵥ* (Xh ^ n - Y ^ n)) ≤ ∑ k ∈ Finset.range n, l1 ((w ᵥ* Y ^ k) ᵥ* (Xh - Y)) := by
  induction n with
  | zero => simp [l1]
  | succ m ih =>
    have key : w ᵥ* (Xh ^ (m + 1) - Y ^ (m + 1)) =
        (w ᵥ* (Xh ^ m - Y ^ m)) ᵥ* Xh + (w ᵥ* Y ^ m) ᵥ* (Xh - Y) := by
      rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.vecMul_add]
      congr 1
      rw [pow_succ, pow_succ]
      noncomm_ring
    rw [key, Finset.sum_range_succ]
    refine le_trans (l1_add_le _ _) (add_le_add ?_ le_rfl)
    exact le_trans (l1_vecMul_le_of_stochastic Xh hnn hrow _) ih

/-- **Estimation radius**: a row-stochastic estimate `X̂` and the true kernel `X` with
row-L¹ gap `η` give `‖w·(X̂ⁿ − Xⁿ)‖₁ ≤ n · η · ‖w‖₁`. Together with the orbit radius this is
the two-radii bound: the first radius pays for coarse-graining, this one for estimation. -/
theorem estimation_radius [Nonempty V] (Xh X : Matrix V V ℝ)
    (hnn : ∀ a b, 0 ≤ Xh a b) (hrow : ∀ a, ∑ b, Xh a b = 1)
    (hX : ∀ a b, 0 ≤ X a b) (hXrow : ∀ a, ∑ b, X a b = 1)
    (w : V → ℝ) (n : ℕ) {η : ℝ} (hη : rowL1Dist Xh X ≤ η) :
    l1 (w ᵥ* (Xh ^ n - X ^ n)) ≤ (n : ℝ) * η * l1 w := by
  refine le_trans (l1_vecMul_pow_sub_pow_le_sum Xh X hnn hrow w n) ?_
  have hterm : ∀ k ∈ Finset.range n, l1 ((w ᵥ* X ^ k) ᵥ* (Xh - X)) ≤ η * l1 w := by
    intro k _
    have hpow : ∀ j : ℕ, l1 (w ᵥ* X ^ j) ≤ l1 w := by
      intro j
      induction j with
      | zero => simp
      | succ j ihj =>
        rw [pow_succ, ← Matrix.vecMul_vecMul]
        exact le_trans (l1_vecMul_le_of_stochastic X hX hXrow _) ihj
    have hdist0 : 0 ≤ rowL1Dist Xh X := by
      unfold rowL1Dist
      exact le_trans (Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.le_sup' (fun a => ∑ b, |Xh a b - X a b|) (mem_univ (Classical.arbitrary V)))
    calc l1 ((w ᵥ* X ^ k) ᵥ* (Xh - X))
        ≤ l1 (w ᵥ* X ^ k) * rowL1Dist Xh X := l1_vecMul_sub_le Xh X _
      _ ≤ l1 w * η := mul_le_mul (hpow k) hη hdist0 (l1_nonneg w)
      _ = η * l1 w := mul_comm _ _
  calc ∑ k ∈ Finset.range n, l1 ((w ᵥ* X ^ k) ᵥ* (Xh - X))
      ≤ ∑ _k ∈ Finset.range n, η * l1 w := Finset.sum_le_sum hterm
    _ = (n : ℝ) * η * l1 w := by simp [Finset.sum_const, Finset.card_range]; ring

end SGC.Bridge.TwoRadii
