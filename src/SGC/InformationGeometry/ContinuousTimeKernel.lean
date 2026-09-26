/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# The matrix exponential of a generator is a stochastic kernel

For a finite-state generator `L` (nonnegative off-diagonal entries, zero row
sums), `exp L` has unit row sums and nonnegative entries. These are the two
facts the continuous-time program (decision 0070) needs and Mathlib does not
provide.

* `exp_row_sum` — `Σ_j (exp L) i j = 1`, from the exponential series and
  `L *ᵥ 1 = 0`.
* `exp_entry_nonneg` — via uniformization: `L = (L + λ•1) − λ•1` with
  `L + λ•1` entrywise nonnegative, so `exp L = exp (L + λ•1) · e^{−λ}` is a
  nonnegative matrix times a positive scalar.
* `exp_isStochastic` — the two together; `exp (t • L)` for `t ≥ 0` inherits both.
-/

open scoped Matrix Matrix.Norms.Operator
open NormedSpace Finset

namespace SGC.InformationGeometry.ContinuousTimeKernel

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite-state generator: nonnegative off-diagonal, zero row sums. -/
structure IsGenerator (L : Matrix V V ℝ) : Prop where
  offdiag_nonneg : ∀ x y, x ≠ y → 0 ≤ L x y
  row_zero : ∀ x, ∑ y, L x y = 0

/-! ### Entrywise series -/

lemma exp_entry (M : Matrix V V ℝ) (i j : V) :
    exp ℝ M i j = ∑' n : ℕ, ((n.factorial : ℝ)⁻¹) * (M ^ n) i j := by
  have hs : Summable (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • M ^ n) := expSeries_summable' M
  rw [exp_eq_tsum]
  change (∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • M ^ n) i j = _
  rw [tsum_apply hs, tsum_apply ((Pi.summable.mp hs) i)]
  rfl

lemma entry_summable (M : Matrix V V ℝ) (i j : V) :
    Summable (fun n : ℕ => ((n.factorial : ℝ)⁻¹) * (M ^ n) i j) := by
  have hs : Summable (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • M ^ n) := expSeries_summable' M
  exact (Pi.summable.mp ((Pi.summable.mp hs) i)) j

/-! ### Row sums -/

lemma pow_row_sum (L : Matrix V V ℝ) (hrow : ∀ x, ∑ y, L x y = 0) :
    ∀ n : ℕ, ∀ i, ∑ j, (L ^ n) i j = if n = 0 then 1 else 0 := by
  intro n
  induction n with
  | zero =>
    intro i
    simp only [pow_zero, Matrix.one_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  | succ n ih =>
    intro i
    simp only [Nat.succ_ne_zero, if_false]
    rw [pow_succ]
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [← Finset.mul_sum, hrow k, mul_zero]

/-- **Row sums of `exp L` are one.** -/
theorem exp_row_sum (L : Matrix V V ℝ) (hrow : ∀ x, ∑ y, L x y = 0) (i : V) :
    ∑ j, exp ℝ L i j = 1 := by
  simp only [exp_entry]
  rw [← Summable.tsum_finsetSum (fun j _ => entry_summable L i j)]
  have h : ∀ n : ℕ, ∑ j, ((n.factorial : ℝ)⁻¹) * (L ^ n) i j
      = if n = 0 then (1 : ℝ) else 0 := by
    intro n
    rw [← Finset.mul_sum, pow_row_sum L hrow n i]
    split_ifs with h
    · subst h
      simp
    · simp
  simp only [h]
  exact tsum_ite_eq 0 (fun _ => (1 : ℝ))

/-! ### Nonnegativity via uniformization -/

lemma pow_entry_nonneg (M : Matrix V V ℝ) (hM : ∀ i j, 0 ≤ M i j) :
    ∀ n : ℕ, ∀ i j, 0 ≤ (M ^ n) i j := by
  intro n
  induction n with
  | zero => intro i j; simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (ih i k) (hM k j))

lemma exp_entry_nonneg_of_nonneg (M : Matrix V V ℝ) (hM : ∀ i j, 0 ≤ M i j) (i j : V) :
    0 ≤ exp ℝ M i j := by
  rw [exp_entry]
  exact tsum_nonneg (fun n => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (pow_entry_nonneg M hM n i j))

lemma exp_smul_one (c : ℝ) :
    exp ℝ (c • (1 : Matrix V V ℝ)) = Real.exp c • (1 : Matrix V V ℝ) := by
  rw [← Algebra.algebraMap_eq_smul_one, ← algebraMap_exp_comm, Algebra.algebraMap_eq_smul_one,
    Real.exp_eq_exp_ℝ]

/-- The uniformization shift: `Σ_x |L x x|` dominates every `-L x x`. -/
def shift (L : Matrix V V ℝ) : ℝ := ∑ x, |L x x|

lemma shift_nonneg (L : Matrix V V ℝ) : 0 ≤ shift L :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma shifted_nonneg (L : Matrix V V ℝ) (hL : IsGenerator L) (i j : V) :
    0 ≤ (L + shift L • (1 : Matrix V V ℝ)) i j := by
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases h : i = j
  · subst h
    simp only [if_true, mul_one]
    have : |L i i| ≤ shift L :=
      Finset.single_le_sum (f := fun x => |L x x|) (fun x _ => abs_nonneg _) (Finset.mem_univ i)
    linarith [neg_abs_le (L i i)]
  · simp only [h, if_false, mul_zero, add_zero]
    exact hL.offdiag_nonneg i j h

/-- **Entries of `exp L` are nonnegative.** -/
theorem exp_entry_nonneg (L : Matrix V V ℝ) (hL : IsGenerator L) (i j : V) :
    0 ≤ exp ℝ L i j := by
  set M := L + shift L • (1 : Matrix V V ℝ)
  have hdecomp : L = M + (-shift L) • (1 : Matrix V V ℝ) := by
    simp only [M, neg_smul]
    abel
  have hcomm : Commute M ((-shift L) • (1 : Matrix V V ℝ)) :=
    (Commute.one_right M).smul_right _
  rw [hdecomp, exp_add_of_commute hcomm, exp_smul_one, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_apply, smul_eq_mul]
  exact mul_nonneg (Real.exp_pos _).le (exp_entry_nonneg_of_nonneg M (shifted_nonneg L hL) i j)

/-- **`exp L` is a stochastic kernel.** -/
theorem exp_isStochastic (L : Matrix V V ℝ) (hL : IsGenerator L) :
    (∀ i j, 0 ≤ exp ℝ L i j) ∧ (∀ i, ∑ j, exp ℝ L i j = 1) :=
  ⟨exp_entry_nonneg L hL, exp_row_sum L hL.row_zero⟩

lemma isGenerator_smul (L : Matrix V V ℝ) (hL : IsGenerator L) {t : ℝ} (ht : 0 ≤ t) :
    IsGenerator (t • L) where
  offdiag_nonneg x y hxy := by
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact mul_nonneg ht (hL.offdiag_nonneg x y hxy)
  row_zero x := by
    simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, hL.row_zero x, mul_zero]

/-- The semigroup `t ↦ exp (t • L)`, `t ≥ 0`, consists of stochastic kernels. -/
theorem exp_smul_isStochastic (L : Matrix V V ℝ) (hL : IsGenerator L) {t : ℝ} (ht : 0 ≤ t) :
    (∀ i j, 0 ≤ exp ℝ (t • L) i j) ∧ (∀ i, ∑ j, exp ℝ (t • L) i j = 1) :=
  exp_isStochastic (t • L) (isGenerator_smul L hL ht)

end SGC.InformationGeometry.ContinuousTimeKernel
