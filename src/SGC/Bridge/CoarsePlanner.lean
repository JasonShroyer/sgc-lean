/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul

/-!
# Closure makes the coarse planner exact

A memoryless coarse planner propagates block-constant data with the quotient generator `PLP` instead
of `L`. If the partition is **lumpable** — `L` maps block-constant functions to block-constant
functions, i.e. `L * P = P * L * P` — then every power agrees on block-constant data:
`(P L P)^k * P = L^k * P` (`coarse_power_exact_of_lumpable`). Hence the planner's horizon-`h` value
`e^{h·PLP} P u` equals the true `e^{hL} P u` term by term, and its *excess loss* (Gap 2 of benchmark
question 2) is zero for block-constant utilities. This is the exact statement behind "closure is what
a reusable autonomous model needs": without it, the planner's error is controlled only by the
leakage bound (`trajectory_closure_bound`, `t·ε`), the dynamics term of the decomposition.

Scope: exact lumpability; the approximate version is the existing horizon bound, not reproved here.
-/

namespace SGC.Bridge.CoarsePlanner

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Under lumpability, every power of `L` preserves block-constancy: `L^k P = P L^k P`. -/
theorem power_preserves_blockConstant (L P : Matrix n n ℝ) (hP : P * P = P)
    (hlump : L * P = P * L * P) : ∀ k : ℕ, L ^ k * P = P * L ^ k * P := by
  intro k
  induction k with
  | zero => simp [hP]
  | succ k ih =>
    calc L ^ (k + 1) * P = L * (L ^ k * P) := by rw [pow_succ', Matrix.mul_assoc]
      _ = L * (P * L ^ k * P) := by rw [ih]
      _ = (L * P) * (L ^ k * P) := by simp only [Matrix.mul_assoc]
      _ = (P * L * P) * (L ^ k * P) := by rw [hlump]
      _ = P * L * (P * L ^ k * P) := by simp only [Matrix.mul_assoc]
      _ = P * L * (L ^ k * P) := by rw [← ih]
      _ = P * L ^ (k + 1) * P := by rw [pow_succ']; simp only [Matrix.mul_assoc]

/-- **Lumpability makes the quotient powers exact on block-constant data.** -/
theorem coarse_power_exact_of_lumpable (L P : Matrix n n ℝ) (hP : P * P = P)
    (hlump : L * P = P * L * P) : ∀ k : ℕ, (P * L * P) ^ k * P = L ^ k * P := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    calc (P * L * P) ^ (k + 1) * P = (P * L * P) * ((P * L * P) ^ k * P) := by
          rw [pow_succ', Matrix.mul_assoc]
      _ = (P * L * P) * (L ^ k * P) := by rw [ih]
      _ = P * L * (P * L ^ k * P) := by simp only [Matrix.mul_assoc]
      _ = P * L * (L ^ k * P) := by rw [← power_preserves_blockConstant L P hP hlump k]
      _ = P * L ^ (k + 1) * P := by rw [pow_succ']; simp only [Matrix.mul_assoc]
      _ = L ^ (k + 1) * P := by rw [← power_preserves_blockConstant L P hP hlump (k + 1)]

end SGC.Bridge.CoarsePlanner
