/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith

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


/-!
## The finite-horizon predictive defect is driven by *reverse* leakage

Let `B_n = P K^n − (PKP)^n P` be the planner's error operator at horizon `n` (projected exact
prediction minus the coarse model's prediction, on all inputs). It satisfies the one-step recursion
`B_{n+1} = (PKP)^n · (P K (1−P)) + B_n K` (`predictive_defect_succ`): each step inserts one factor of
the **reverse leakage** `P K (1−P)` — the effect of the unresolved component on the projected
prediction — not the forward leakage `(1−P) K P`. Hence if the reverse leakage vanishes the planner
is exact for *every* input at every horizon (`planner_exact_of_reverse_closure`), whether or not the
chain is reversible; and the shift register of decision 0103 — forward leakage zero, reverse leakage
nonzero, planner error `0.8` at `n = 1` — is exactly the case the recursion describes. In a reversible
chain the two leakages are adjoint, which is why forward closure sufficed there.
-/

section ReverseLeakage

/-- One-step recursion for the planner's error operator. -/
theorem predictive_defect_succ (K P : Matrix n n ℝ) (hP : P * P = P) (k : ℕ) :
    P * K ^ (k + 1) - (P * K * P) ^ (k + 1) * P =
      (P * K * P) ^ k * (P * K * (1 - P)) + (P * K ^ k - (P * K * P) ^ k * P) * K := by
  have h1 : (P * K * P) ^ (k + 1) * P = (P * K * P) ^ k * (P * K * P) := by
    rw [pow_succ, Matrix.mul_assoc, Matrix.mul_assoc (P * K) P P, hP]
  rw [h1, pow_succ]
  noncomm_ring

/-- **Reverse closure makes the planner exact on every input.** If `P K (1 − P) = 0` then
`P K^k = (PKP)^k P` for all `k`. -/
theorem planner_exact_of_reverse_closure (K P : Matrix n n ℝ) (hP : P * P = P)
    (hrev : P * K * (1 - P) = 0) : ∀ k : ℕ, P * K ^ k = (P * K * P) ^ k * P := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h := predictive_defect_succ K P hP k
    rw [hrev, Matrix.mul_zero, zero_add, ih, sub_self, Matrix.zero_mul] at h
    exact sub_eq_zero.mp h

end ReverseLeakage

/-!
## Decision error is error in contrasts, not in values

With `e_a = v̂_a − v_a`, the regret of the `v̂`-argmax is at most `|e_{â} − e_a|` for the action `a`
it is compared with (`contrast_regret`): common-mode error cancels. If every contrast error is below
the margin of the unique best action, the argmax is unchanged (`margin_preserves_argmax`). The
`2 max |e_a|` bound of `argmax_perturbation` is the conservative corollary.
-/

section Contrast

variable {α : Type*}

/-- Regret of the estimated argmax against `a` is bounded by the contrast error `|e_â − e_a|`. -/
theorem contrast_regret (v vhat : α → ℝ) (ahat : α) (hmax : ∀ a, vhat a ≤ vhat ahat) (a : α) :
    v a - v ahat ≤ |(vhat ahat - v ahat) - (vhat a - v a)| := by
  have h := hmax a
  have : v a - v ahat ≤ (vhat ahat - v ahat) - (vhat a - v a) := by linarith
  exact le_trans this (le_abs_self _)

/-- If all contrast errors are below the margin `m` of `astar`, the estimated argmax is `astar`. -/
theorem margin_preserves_argmax (v vhat : α → ℝ) (astar : α) (m : ℝ)
    (hmargin : ∀ a, a ≠ astar → m ≤ v astar - v a)
    (hcontrast : ∀ a, |(vhat astar - v astar) - (vhat a - v a)| < m) :
    ∀ a, a ≠ astar → vhat a < vhat astar := by
  intro a ha
  have h1 := hmargin a ha
  have h2 := (abs_lt.mp (hcontrast a)).1
  linarith

end Contrast


/-!
## The projected-memory identity (finite Mori–Zwanzig)

For resolved coordinates `p` and unresolved `q` evolving by `p_{t+1} = A p_t + B q_t`,
`q_{t+1} = C p_t + D q_t`, the unresolved state is `q_t = D^t q_0 + Σ_{j<t} D^{t−1−j} C p_j`
(`unresolved_closed_form`), so the resolved dynamics are
`p_{t+1} = A p_t + B D^t q_0 + Σ_{j<t} B D^{t−1−j} C p_j` (`resolved_with_memory`): an autonomous
term, an initial-condition term, and a **memory kernel** `B D^{t−1−j} C`. "Not closed" means the
kernel is nonzero — not that the resolved coordinates are unpredictable. This is the algebraic form
of what replaces closure when variables are eliminated.
-/

section Memory

variable {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k]

open Finset

/-- Closed form of the unresolved coordinate. -/
theorem unresolved_closed_form (A : Matrix m m ℝ) (B : Matrix m k ℝ) (C : Matrix k m ℝ)
    (D : Matrix k k ℝ) (p : ℕ → (m → ℝ)) (q : ℕ → (k → ℝ))
    (hq : ∀ t, q (t + 1) = C.mulVec (p t) + D.mulVec (q t)) :
    ∀ t, q t = (D ^ t).mulVec (q 0) + ∑ j ∈ range t, (D ^ (t - 1 - j)).mulVec (C.mulVec (p j)) := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    rw [hq t, ih, Finset.sum_range_succ, Matrix.mulVec_add, Matrix.mulVec_sum]
    have hpow : (D ^ (t + 1)).mulVec (q 0) = D.mulVec ((D ^ t).mulVec (q 0)) := by
      rw [pow_succ', Matrix.mulVec_mulVec]
    have hlast : (D ^ (t + 1 - 1 - t)).mulVec (C.mulVec (p t)) = C.mulVec (p t) := by
      simp
    have hshift : ∀ j ∈ range t, D.mulVec ((D ^ (t - 1 - j)).mulVec (C.mulVec (p j))) =
        (D ^ (t + 1 - 1 - j)).mulVec (C.mulVec (p j)) := by
      intro j hj
      have hj' : j < t := Finset.mem_range.mp hj
      have : t + 1 - 1 - j = (t - 1 - j) + 1 := by omega
      rw [this, pow_succ', Matrix.mulVec_mulVec]
    rw [hpow, hlast, Finset.sum_congr rfl hshift]
    abel

/-- **Resolved dynamics with memory kernel.** -/
theorem resolved_with_memory (A : Matrix m m ℝ) (B : Matrix m k ℝ) (C : Matrix k m ℝ)
    (D : Matrix k k ℝ) (p : ℕ → (m → ℝ)) (q : ℕ → (k → ℝ))
    (hp : ∀ t, p (t + 1) = A.mulVec (p t) + B.mulVec (q t))
    (hq : ∀ t, q (t + 1) = C.mulVec (p t) + D.mulVec (q t)) :
    ∀ t, p (t + 1) = A.mulVec (p t) + B.mulVec ((D ^ t).mulVec (q 0)) +
      ∑ j ∈ range t, B.mulVec ((D ^ (t - 1 - j)).mulVec (C.mulVec (p j))) := by
  intro t
  rw [hp t, unresolved_closed_form A B C D p q hq t, Matrix.mulVec_add, Matrix.mulVec_sum, add_assoc]

end Memory

end SGC.Bridge.CoarsePlanner
