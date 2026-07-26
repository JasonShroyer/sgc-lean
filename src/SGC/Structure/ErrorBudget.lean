/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Structure.ContinualComposition

/-!
# The Recursive Error Budget

The approximate theory, built on the (now canonical) exact theory of
`ContinualComposition` and `LifelongSubstitution`, per the Artemis
sequencing: a recursively defined error budget `B`, not a prematurely
global Lipschitz formula.

## The object

For learned operations with local defects `|opA a b − (a+b)| ≤ δA` and
`|opM a b − a·b| ≤ δM`, and inputs bounded by `P`, define recursively:

* `valueBound P e` — a bound on the exact value `|evalRing ρ e|`;
* `errorBudget δA δM P e` — the accumulated error budget:
  - `B(var) = B(const) = 0`,
  - `B(e₁ + e₂) = δA + (B(e₁) + B(e₂))`,
  - `B(e₁ * e₂) = δM + (V(e₁) + B(e₁))·B(e₂) + V(e₂)·B(e₁)`.

The multiplication clause is Artemis's `δ_op + Σᵢ Lᵢ B(eᵢ)` with the
*honest, data-dependent* Lipschitz constants: `L₂ = V(e₁) + B(e₁)` (the
learned left value is bounded by exact value plus accumulated error) and
`L₁ = V(e₂)`.  No a-priori bound on learned activations is assumed — the
budget computes its own.

## The theorems

* **`evalLearned_defect_bound`** (the induction theorem):
  `|evalLearned e − evalRing e| ≤ errorBudget δA δM P e`
  for every expression `e` — local defect certification bounds the global
  compositional error at *arbitrary* depth.  The depth-2 case recovers
  `defect_propagation` (T4) from `LocalToGlobal`.

* **`section_defect_bound`** (sheaf level): the unique global section of
  the learned computation sheaf *is* the learned evaluation
  (`evalLearned_isSection`), so the budget bounds the section's deviation
  from the denotational semantics.

* **`defect_collapse`** (grokking as budget collapse): when the local
  defects vanish, the budget telescopes to zero and the learned evaluation
  is *exactly* the ring semantics — the approximate theory degenerates to
  the exact one, formalizing "grokking = defect collapse" at all depths.
-/

namespace SGC.Sheaf

/-! ### Learned evaluation and its section property (any ring) -/

variable {R : Type*} [Ring R] {n : ℕ}

/-- Structural evaluation by the *learned* operations (no certification
    assumed): the forward pass of the learned model on the syntax DAG. -/
def evalLearned (opA opM : R → R → R) (ρ : Fin n → R) : Expr R n → R
  | .var i => ρ i
  | .const c => c
  | .add e₁ e₂ => opA (evalLearned opA opM ρ e₁) (evalLearned opA opM ρ e₂)
  | .mul e₁ e₂ => opM (evalLearned opA opM ρ e₁) (evalLearned opA opM ρ e₂)

/-- The learned evaluation is a global section of the learned computation
    sheaf — with NO certification hypotheses.  Hence, by uniqueness, the
    sheaf's section is always the learned forward pass, certified or not. -/
theorem evalLearned_isSection (opA opM : R → R → R) (ρ : Fin n → R) :
    IsSection (learnedComputation opA opM) (exprBoundary ρ)
      (evalLearned opA opM ρ) := by
  constructor
  · intro e hv
    cases e <;> first | rfl | exact absurd hv (List.cons_ne_nil _ _)
  · intro e hv
    cases e with
    | var i => exact absurd rfl hv
    | const c => exact absurd rfl hv
    | add e₁ e₂ => simp [learnedComputation, Expr.parents, evalLearned]
    | mul e₁ e₂ => simp [learnedComputation, Expr.parents, evalLearned]

/-! ### The budget recursion (over ℝ) -/

/-- Recursive bound on the exact value of a subexpression, given the input
    bound `P`. -/
def valueBound (P : ℝ) : Expr ℝ n → ℝ
  | .var _ => P
  | .const c => |c|
  | .add e₁ e₂ => valueBound P e₁ + valueBound P e₂
  | .mul e₁ e₂ => valueBound P e₁ * valueBound P e₂

/-- **The recursive error budget** `B(e)`:
    zero at leaves, `δ_op` plus Lipschitz-weighted child budgets at
    internal cells. -/
def errorBudget (δA δM P : ℝ) : Expr ℝ n → ℝ
  | .var _ => 0
  | .const _ => 0
  | .add e₁ e₂ => δA + (errorBudget δA δM P e₁ + errorBudget δA δM P e₂)
  | .mul e₁ e₂ => δM +
      (valueBound P e₁ + errorBudget δA δM P e₁) * errorBudget δA δM P e₂ +
      valueBound P e₂ * errorBudget δA δM P e₁

/-- The exact evaluation respects the recursive value bound. -/
theorem abs_evalRing_le {ρ : Fin n → ℝ} {P : ℝ} (hρ : ∀ i, |ρ i| ≤ P)
    (e : Expr ℝ n) : |evalRing ρ e| ≤ valueBound P e := by
  induction e with
  | var i => simpa [evalRing, valueBound] using hρ i
  | const c => simp [evalRing, valueBound]
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [evalRing, valueBound]
    exact (abs_add_le _ _).trans (add_le_add ih₁ ih₂)
  | mul e₁ e₂ ih₁ ih₂ =>
    simp only [evalRing, valueBound]
    calc |evalRing ρ e₁ * evalRing ρ e₂|
        = |evalRing ρ e₁| * |evalRing ρ e₂| := abs_mul _ _
      _ ≤ valueBound P e₁ * valueBound P e₂ :=
          mul_le_mul ih₁ ih₂ (abs_nonneg _) ((abs_nonneg _).trans ih₁)

/-- One addition cell: local defect plus child errors. -/
private theorem add_step {oab a' b' a b δ B₁ B₂ : ℝ}
    (hop : |oab - (a' + b')| ≤ δ)
    (h₁ : |a' - a| ≤ B₁) (h₂ : |b' - b| ≤ B₂) :
    |oab - (a + b)| ≤ δ + (B₁ + B₂) := by
  have key : oab - (a + b) = (oab - (a' + b')) + ((a' - a) + (b' - b)) := by
    ring
  rw [key]
  have t1 := abs_add_le (oab - (a' + b')) ((a' - a) + (b' - b))
  have t2 := abs_add_le (a' - a) (b' - b)
  linarith

/-- One multiplication cell: local defect plus Lipschitz-weighted child
    errors, with the learned left value bounded by `A₁` and the exact right
    value bounded by `V₂`. -/
private theorem mul_step {oab a' b' a b δ A₁ V₂ B₁ B₂ : ℝ}
    (hop : |oab - a' * b'| ≤ δ)
    (h₁ : |a' - a| ≤ B₁) (h₂ : |b' - b| ≤ B₂)
    (ha' : |a'| ≤ A₁) (hb : |b| ≤ V₂) :
    |oab - a * b| ≤ δ + A₁ * B₂ + V₂ * B₁ := by
  have key : oab - a * b = (oab - a' * b') + (a' * (b' - b) + (a' - a) * b) := by
    ring
  rw [key]
  have t1 := abs_add_le (oab - a' * b') (a' * (b' - b) + (a' - a) * b)
  have t2 := abs_add_le (a' * (b' - b)) ((a' - a) * b)
  have t3 : |a' * (b' - b)| ≤ A₁ * B₂ := by
    rw [abs_mul]
    exact mul_le_mul ha' h₂ (abs_nonneg _) ((abs_nonneg _).trans ha')
  have t4 : |(a' - a) * b| ≤ V₂ * B₁ := by
    calc |(a' - a) * b| = |a' - a| * |b| := abs_mul _ _
      _ ≤ B₁ * V₂ := mul_le_mul h₁ hb (abs_nonneg _) ((abs_nonneg _).trans h₁)
      _ = V₂ * B₁ := mul_comm _ _
  linarith

/-- **The Error-Budget Induction Theorem.**

    If the learned cells satisfy their local defect certificates and the
    inputs are bounded by `P`, then for EVERY expression the learned
    forward pass deviates from the denotational semantics by at most the
    recursive budget:

    `|evalLearned(e) − evalRing(e)| ≤ B(e)`.

    Local certification is sufficient to certify any composed global rule,
    at arbitrary depth — the full generalization of the depth-2 bound
    `defect_propagation` (T4). -/
theorem evalLearned_defect_bound {opA opM : ℝ → ℝ → ℝ} {δA δM : ℝ}
    (hA : ∀ a b, |opA a b - (a + b)| ≤ δA)
    (hM : ∀ a b, |opM a b - a * b| ≤ δM)
    {ρ : Fin n → ℝ} {P : ℝ} (hρ : ∀ i, |ρ i| ≤ P)
    (e : Expr ℝ n) :
    |evalLearned opA opM ρ e - evalRing ρ e| ≤ errorBudget δA δM P e := by
  induction e with
  | var i => simp [evalLearned, evalRing, errorBudget]
  | const c => simp [evalLearned, evalRing, errorBudget]
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [evalLearned, evalRing, errorBudget]
    exact add_step (hA _ _) ih₁ ih₂
  | mul e₁ e₂ ih₁ ih₂ =>
    simp only [evalLearned, evalRing, errorBudget]
    have ha' : |evalLearned opA opM ρ e₁| ≤
        valueBound P e₁ + errorBudget δA δM P e₁ := by
      have key : evalLearned opA opM ρ e₁ =
          evalRing ρ e₁ + (evalLearned opA opM ρ e₁ - evalRing ρ e₁) := by
        ring
      rw [key]
      exact (abs_add_le _ _).trans (add_le_add (abs_evalRing_le hρ e₁) ih₁)
    exact mul_step (hM _ _) ih₁ ih₂ ha' (abs_evalRing_le hρ e₂)

/-- **Sheaf-level budget bound**: the unique global section of the learned
    computation sheaf deviates from the denotational semantics by at most
    the recursive budget.  (The section IS the learned forward pass, by
    `evalLearned_isSection` and uniqueness.) -/
theorem section_defect_bound {opA opM : ℝ → ℝ → ℝ} {δA δM : ℝ}
    (hA : ∀ a b, |opA a b - (a + b)| ≤ δA)
    (hM : ∀ a b, |opM a b - a * b| ≤ δM)
    {ρ : Fin n → ℝ} {P : ℝ} (hρ : ∀ i, |ρ i| ≤ P)
    {σ : Expr ℝ n → ℝ}
    (hσ : IsSection (learnedComputation opA opM) (exprBoundary ρ) σ)
    (e : Expr ℝ n) :
    |σ e - evalRing ρ e| ≤ errorBudget δA δM P e := by
  rw [hσ.unique (evalLearned_isSection opA opM ρ)]
  exact evalLearned_defect_bound hA hM hρ e

/-! ### Grokking as budget collapse -/

/-- With vanishing local defects the budget telescopes to zero. -/
theorem errorBudget_zero (P : ℝ) (e : Expr ℝ n) :
    errorBudget 0 0 P e = 0 := by
  induction e with
  | var i => rfl
  | const c => rfl
  | add e₁ e₂ ih₁ ih₂ => simp [errorBudget, ih₁, ih₂]
  | mul e₁ e₂ ih₁ ih₂ => simp [errorBudget, ih₁, ih₂]

/-- **Grokking as defect collapse**: when the local defects reach zero,
    the learned model computes the exact ring semantics of EVERY
    expression.  The approximate theory degenerates to the exact theory
    (`certified_implies_correct`) precisely at the zero-defect transition. -/
theorem defect_collapse {opA opM : ℝ → ℝ → ℝ}
    (hA : ∀ a b, |opA a b - (a + b)| ≤ 0)
    (hM : ∀ a b, |opM a b - a * b| ≤ 0)
    {ρ : Fin n → ℝ} {P : ℝ} (hρ : ∀ i, |ρ i| ≤ P)
    (e : Expr ℝ n) :
    evalLearned opA opM ρ e = evalRing ρ e := by
  have h := evalLearned_defect_bound hA hM hρ e
  rw [errorBudget_zero] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

/-! ### Budget API: nonnegativity -/

/-- The value bound is nonnegative for nonnegative input bounds. -/
theorem valueBound_nonneg {P : ℝ} (hP : 0 ≤ P) (e : Expr ℝ n) :
    0 ≤ valueBound P e := by
  induction e with
  | var i => exact hP
  | const c => exact abs_nonneg c
  | add e₁ e₂ ih₁ ih₂ => exact add_nonneg ih₁ ih₂
  | mul e₁ e₂ ih₁ ih₂ => exact mul_nonneg ih₁ ih₂

/-- The budget is nonnegative for nonnegative defects and input bounds. -/
theorem errorBudget_nonneg {δA δM P : ℝ} (hδA : 0 ≤ δA) (hδM : 0 ≤ δM)
    (hP : 0 ≤ P) (e : Expr ℝ n) : 0 ≤ errorBudget δA δM P e := by
  induction e with
  | var i => exact le_refl 0
  | const c => exact le_refl 0
  | add e₁ e₂ ih₁ ih₂ =>
    have := add_nonneg ih₁ ih₂
    simp only [errorBudget]
    linarith
  | mul e₁ e₂ ih₁ ih₂ =>
    have h1 : 0 ≤ (valueBound P e₁ + errorBudget δA δM P e₁) *
        errorBudget δA δM P e₂ :=
      mul_nonneg (add_nonneg (valueBound_nonneg hP e₁) ih₁) ih₂
    have h2 : 0 ≤ valueBound P e₂ * errorBudget δA δM P e₁ :=
      mul_nonneg (valueBound_nonneg hP e₂) ih₁
    simp only [errorBudget]
    linarith

end SGC.Sheaf
