/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Finite safeguards: distinctions that must not be collapsed

Small concrete facts, kernel-checked, that block recurring conflations in the emergence literature
and in our own earlier manuscripts ("The Physical Basis of Computational Complexity", 2025; the
SVD-based causal-emergence framework):

* **Operator normality, invertibility, and detailed balance are different properties.** The directed
  3-cycle `0 → 1 → 2 → 0` has a transition matrix that is a permutation: it is *normal*
  (`K Kᵀ = Kᵀ K`), it has a *stochastic inverse* (`K Kᵀ = 1`, so it is "dynamically reversible" in the
  invertibility sense), and it is **not** detailed-balance reversible under its uniform stationary law
  (`π₀ K₀₁ = 1/3 ≠ 0 = π₁ K₁₀`). "Directed ⇒ non-normal" and "invertible ⇒ reversible" are both false.
* **Exact temporal blocking composes transitions on the original state space:** `K^b` is a stochastic
  matrix on the *same* state space (`blocking_row_sums`, `blocking_nonneg`), so blocking is not
  coarse-graining. It does **not** construct a quotient, certify sufficiency, or preserve path
  information: `cyc3 ^ 3 = 1` (`cyc3_pow_three`), so at lag 3 the cycle is indistinguishable from the
  identity.
-/

namespace SGC.Bridge.FiniteSafeguards

open Matrix

/-- The directed 3-cycle `0 → 1 → 2 → 0`. -/
def cyc3 : Matrix (Fin 3) (Fin 3) ℚ := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

/-- The 3-cycle is a permutation matrix: `K Kᵀ = 1` (a stochastic inverse exists). -/
theorem cyc3_mul_transpose : cyc3 * cyc3ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyc3, Matrix.mul_apply, Fin.sum_univ_three]

/-- Hence the 3-cycle is **normal**: `K Kᵀ = Kᵀ K`. -/
theorem cyc3_normal : cyc3 * cyc3ᵀ = cyc3ᵀ * cyc3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyc3, Matrix.mul_apply, Fin.sum_univ_three]

/-- Row-stochastic: every row sums to one. -/
theorem cyc3_row_sums (i : Fin 3) : ∑ j, cyc3 i j = 1 := by
  fin_cases i <;> simp [cyc3, Fin.sum_univ_three]

/-- The uniform law is stationary: `π K = π`. -/
theorem cyc3_uniform_stationary (j : Fin 3) : ∑ i, (1 / 3 : ℚ) * cyc3 i j = 1 / 3 := by
  fin_cases j <;> simp [cyc3, Fin.sum_univ_three]

/-- **Not detailed-balance reversible** under the uniform stationary law:
`π₀ K₀₁ = 1/3` but `π₁ K₁₀ = 0`. -/
theorem cyc3_not_detailed_balance :
    ¬ (∀ i j : Fin 3, (1 / 3 : ℚ) * cyc3 i j = (1 / 3 : ℚ) * cyc3 j i) := by
  intro h
  have := h 0 1
  simp [cyc3] at this

/-- Exact temporal blocking of a row-stochastic matrix is row-stochastic on the same state space:
blocking composes transitions; it does not discard states. -/
theorem blocking_row_sums {n : Type*} [Fintype n] [DecidableEq n] (K : Matrix n n ℚ)
    (hK : ∀ i, ∑ j, K i j = 1) : ∀ b : ℕ, ∀ i, ∑ j, (K ^ b) i j = 1 := by
  intro b
  induction b with
  | zero => intro i; simp [Matrix.one_apply, Finset.sum_ite_eq']
  | succ b ih =>
    intro i
    rw [pow_succ]
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    calc ∑ k, ∑ j, (K ^ b) i k * K k j = ∑ k, (K ^ b) i k * ∑ j, K k j := by
          apply Finset.sum_congr rfl; intro k _; rw [Finset.mul_sum]
      _ = ∑ k, (K ^ b) i k := by
          apply Finset.sum_congr rfl; intro k _; rw [hK k, mul_one]
      _ = 1 := ih i


/-!
## Nonnegativity under blocking (the half `blocking_row_sums` does not cover)

`blocking_row_sums` proves only row normalization. Entrywise nonnegativity is preserved too, so `K^b`
is a genuine stochastic matrix. **Scope:** blocking composes transitions on the original state space;
it does not construct a state-space quotient, does not certify information sufficiency, and does not
preserve path information — the 3-cycle satisfies `K^3 = 1`, indistinguishable at lag 3 from the identity.
-/

theorem blocking_nonneg {n : Type*} [Fintype n] [DecidableEq n] (K : Matrix n n ℚ)
    (hK : ∀ i j, 0 ≤ K i j) : ∀ b : ℕ, ∀ i j, 0 ≤ (K ^ b) i j := by
  intro b
  induction b with
  | zero => intro i j; simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ b ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (ih i k) (hK k j))

/-- The 3-cycle at lag 3 is the identity: temporal subsampling erases the intervening transitions. -/
theorem cyc3_pow_three : cyc3 ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyc3, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

end SGC.Bridge.FiniteSafeguards
