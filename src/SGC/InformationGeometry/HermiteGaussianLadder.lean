/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import SGC.InformationGeometry.HermiteGaussianExtremal

/-!
# Hermite-Gaussian Ladder Algebra (Phase 2C)

This module extends Phase 2A's ground-state Euler-Lagrange identity
(`@c:\Lean4 Projects\src\SGC\InformationGeometry\HermiteGaussianExtremal.lean`)
to the algebraic **ladder-operator** structure of the Hermite-Gaussian
family, without using measure theory.

## Main Definitions

* `hermitePoly n : ℝ → ℝ` — the n-th probabilists' Hermite polynomial,
  defined via the standard recurrence
  `He_{n+2}(x) = x · He_{n+1}(x) - (n + 1) · He_n(x)`
  with `He_0(x) = 1`, `He_1(x) = x`.
* `hermiteGaussianFn n ω x` — the (unnormalized) Hermite-Gaussian function
  `He_n(x) · gaussAmpl(ω)(x)`, where `gaussAmpl` is Phase 2A's ground
  state `exp(-ω x²/2)`.

## Main Theorems

* `hermitePoly_recurrence` — the defining recurrence identity.
* `hermitePoly_mul_x` — the cross-identity
  `x · He_n(x) = He_{n+1}(x) + n · He_{n-1}(x)` (valid for all `n ≥ 0`
  with `He_{-1}` reading as `He_0 = 1` under `Nat` truncated subtraction,
  which makes the `n = 0` case read `x · 1 = x + 0 · 1 = x`).
* `hasDerivAt_hermitePoly` — the derivative identity
  `He'_n(x) = n · He_{n-1}(x)`, proved by bundled (pair) induction using
  only `HasDerivAt.mul`, `HasDerivAt.const_mul`, `HasDerivAt.sub` and
  `HasDerivAt.id`.
* `hasDerivAt_hermiteGaussianFn` — the full Hermite-Gaussian derivative,
  via the product rule with Phase 2A's `hasDerivAt_gaussAmpl`:

      `(He_n · ψ_0)'(x) = n · He_{n-1}(x) · ψ_0(x) − (ω x) · He_n(x) · ψ_0(x)`.

  With the probabilists' recurrence `x · He_n = He_{n+1} + n · He_{n-1}`,
  this reduces to the clean ladder form

      `(He_n · ψ_0)'(x) = -ω · He_{n+1}(x) · ψ_0(x) + (n − ω · n) · He_{n-1}(x) · ψ_0(x)`

  (at general `ω`) and specialises at `ω = 1` to the classical form

      `(He_n · ψ_0)'(x) = -He_{n+1}(x) · ψ_0(x)`.

## Scope

This file works with **unnormalized** Hermite-Gaussian functions and
avoids all measure-theoretic infrastructure (`MeasureTheory.Integral`,
`L²` spaces, etc.).  The L²(ℝ) orthonormality and completeness claims
require the measure-theoretic layer and are handled in a separate
(currently broken) file `@c:\Lean4 Projects\src\SGC\HGCompleteness.lean`
to be repaired in a future phase.

## Why this file does not touch `HGCompleteness.lean`

Reconnaissance found that `HGCompleteness.lean` currently does not
compile (two dead Mathlib import paths) and contains ~27 `sorry`s
scattered across interdependent definitions (not just the two theorems
flagged by the external review).  Repairing it requires a dedicated
pass, ideally *after* this clean ladder foundation is in place so that
the repaired file can import the correct derivative identities instead
of re-deriving them inside broken scaffolding.

## References

* Phase 2A: `@c:\Lean4 Projects\src\SGC\InformationGeometry\HermiteGaussianExtremal.lean`.
* Abramowitz & Stegun §22 (Hermite polynomials) — the probabilists'
  `He_n` is the `n`-th column of the recurrence table with
  `He_0 = 1, He_1 = x, He'_n = n · He_{n-1}`.
-/

noncomputable section

namespace SGC.InformationGeometry.HermiteGaussianLadder

open SGC.InformationGeometry.HermiteGaussianExtremal

/-! ## 1. Probabilists' Hermite polynomials -/

/-- The n-th probabilists' Hermite polynomial `He_n : ℝ → ℝ`, defined by
    the recurrence

      `He_0(x) = 1`,
      `He_1(x) = x`,
      `He_{n+2}(x) = x · He_{n+1}(x) − (n + 1) · He_n(x)`.

    These polynomials are monic and satisfy the derivative identity
    `He'_n(x) = n · He_{n-1}(x)` (proved below as `hasDerivAt_hermitePoly`). -/
def hermitePoly : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | 1 => fun x => x
  | n + 2 => fun x => x * hermitePoly (n + 1) x - (n + 1 : ℝ) * hermitePoly n x

/-- `He_0(x) = 1`. -/
@[simp] lemma hermitePoly_zero (x : ℝ) : hermitePoly 0 x = 1 := rfl

/-- `He_1(x) = x`. -/
@[simp] lemma hermitePoly_one (x : ℝ) : hermitePoly 1 x = x := rfl

/-- The probabilists' Hermite recurrence.

    `He_{n+2}(x) = x · He_{n+1}(x) − (n + 1) · He_n(x)`. -/
lemma hermitePoly_succ_succ (n : ℕ) (x : ℝ) :
    hermitePoly (n + 2) x = x * hermitePoly (n + 1) x - (n + 1 : ℝ) * hermitePoly n x := rfl

/-- **Cross-recurrence** (multiplication by `x`).

    `x · He_n(x) = He_{n+1}(x) + n · He_{n-1}(x)`.

    For `n = 0` this reads `x · 1 = x + 0 · 1`, which holds trivially;
    for `n ≥ 1` this is a rearrangement of `hermitePoly_succ_succ`.
    Here `Nat` truncated subtraction means `hermitePoly (0 - 1) = hermitePoly 0 = 1`,
    but the coefficient `(0 : ℝ) · hermitePoly (0 - 1) x = 0` kills it. -/
lemma hermitePoly_mul_x (n : ℕ) (x : ℝ) :
    x * hermitePoly n x = hermitePoly (n + 1) x + (n : ℝ) * hermitePoly (n - 1) x := by
  cases n with
  | zero =>
    simp [hermitePoly]
  | succ k =>
    -- `(k + 1) - 1 = k`, and hermitePoly (k + 1 + 1) x = x * hermitePoly (k + 1) x - (k + 1) * hermitePoly k x
    have hrec := hermitePoly_succ_succ k x
    -- hrec : hermitePoly (k + 2) x = x * hermitePoly (k + 1) x - (k + 1) * hermitePoly k x
    simp only [Nat.succ_sub_one]
    -- goal: x * hermitePoly (k + 1) x = hermitePoly (k + 2) x + (k + 1 : ℝ) * hermitePoly k x
    -- Note: (↑(k + 1) : ℝ) and ((k : ℝ) + 1) may differ syntactically
    push_cast
    linarith [hrec]

/-! ## 2. Derivative identity for Hermite polynomials -/

/-- **Differentiability bundle**: the derivative identity
    `He'_n(x) = n · He_{n-1}(x)` together with the same identity for
    `He_{n+1}`.  Proved by bundled induction: the step for `n + 1` uses
    *both* inductive hypotheses at once, avoiding the need for strong
    induction.

    This is the technical core of Phase 2C. -/
lemma hasDerivAt_hermitePoly_pair (n : ℕ) (x : ℝ) :
    HasDerivAt (hermitePoly n) ((n : ℝ) * hermitePoly (n - 1) x) x ∧
    HasDerivAt (hermitePoly (n + 1)) ((n + 1 : ℝ) * hermitePoly n x) x := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · -- `HasDerivAt (hermitePoly 0) ((0 : ℝ) * hermitePoly (0 - 1) x) x`
      -- = `HasDerivAt (fun _ => 1) 0 x`
      simp only [Nat.cast_zero, zero_mul]
      show HasDerivAt (hermitePoly 0) 0 x
      exact hasDerivAt_const x (1 : ℝ)
    · -- `HasDerivAt (hermitePoly 1) ((0 + 1 : ℝ) * hermitePoly 0 x) x`
      -- = `HasDerivAt (fun x => x) 1 x`
      simp only [Nat.cast_zero, zero_add, hermitePoly_zero, mul_one]
      show HasDerivAt (hermitePoly 1) 1 x
      exact hasDerivAt_id x
  | succ k ih =>
    obtain ⟨ih_k, ih_ksucc⟩ := ih
    -- ih_k : HasDerivAt (hermitePoly k) ((k : ℝ) * hermitePoly (k - 1) x) x
    -- ih_ksucc : HasDerivAt (hermitePoly (k + 1)) ((k + 1 : ℝ) * hermitePoly k x) x
    refine ⟨?_, ?_⟩
    · -- First component: `HasDerivAt (hermitePoly (k+1)) ((k+1 : ℝ) * hermitePoly ((k+1) - 1) x) x`
      -- Since `(k + 1) - 1 = k` in ℕ, this equals ih_ksucc after a `push_cast`.
      have hsub : (k + 1 : ℕ) - 1 = k := rfl
      simp only [hsub]
      convert ih_ksucc using 1
      push_cast
      ring
    · -- Second component: `HasDerivAt (hermitePoly (k + 2)) ((k + 1 + 1 : ℝ) * hermitePoly (k + 1) x) x`
      -- Derive from ih_k and ih_ksucc via the recurrence definition of hermitePoly (k + 2).
      -- hermitePoly (k + 2) y = y * hermitePoly (k + 1) y - (k + 1 : ℝ) * hermitePoly k y
      have hx : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
      -- Derivative of y ↦ y * hermitePoly (k+1) y
      have h_prod : HasDerivAt (fun y : ℝ => y * hermitePoly (k + 1) y)
                               (1 * hermitePoly (k + 1) x + x * ((k + 1 : ℝ) * hermitePoly k x)) x :=
        hx.mul ih_ksucc
      -- Derivative of y ↦ (k + 1 : ℝ) * hermitePoly k y
      have h_const_mul : HasDerivAt (fun y : ℝ => (k + 1 : ℝ) * hermitePoly k y)
                                     ((k + 1 : ℝ) * ((k : ℝ) * hermitePoly (k - 1) x)) x :=
        ih_k.const_mul (k + 1 : ℝ)
      -- Difference → derivative of the RHS of the recurrence
      have h_diff : HasDerivAt
          (fun y : ℝ => y * hermitePoly (k + 1) y - (k + 1 : ℝ) * hermitePoly k y)
          (1 * hermitePoly (k + 1) x + x * ((k + 1 : ℝ) * hermitePoly k x)
            - (k + 1 : ℝ) * ((k : ℝ) * hermitePoly (k - 1) x)) x :=
        h_prod.sub h_const_mul
      -- Rewrite the target function as the recurrence RHS.
      have h_rec_fun :
          hermitePoly (k + 2) =
            fun y : ℝ => y * hermitePoly (k + 1) y - (k + 1 : ℝ) * hermitePoly k y := by
        funext y; rfl
      -- Rewrite the target derivative value using the cross-recurrence on `x · He_k x`.
      have h_xk := hermitePoly_mul_x k x
      -- h_xk : x * hermitePoly k x = hermitePoly (k + 1) x + (k : ℝ) * hermitePoly (k - 1) x
      rw [h_rec_fun]
      convert h_diff using 1
      -- Remaining numeric goal (as an equation):
      --   (↑(k + 1) + 1) * hermitePoly (k + 1) x
      -- = 1 * hermitePoly (k + 1) x + x * ((k + 1 : ℝ) * hermitePoly k x)
      --   - (k + 1 : ℝ) * ((k : ℝ) * hermitePoly (k - 1) x)
      -- Replace `x * hermitePoly k x` via `h_xk` and conclude by `ring`.
      push_cast
      have : x * ((k + 1 : ℝ) * hermitePoly k x)
              = (k + 1 : ℝ) * (x * hermitePoly k x) := by ring
      rw [this, h_xk]
      ring

/-- **Derivative identity for probabilists' Hermite polynomials.**

    `He'_n(x) = n · He_{n-1}(x)`.

    The result is the first projection of `hasDerivAt_hermitePoly_pair`. -/
lemma hasDerivAt_hermitePoly (n : ℕ) (x : ℝ) :
    HasDerivAt (hermitePoly n) ((n : ℝ) * hermitePoly (n - 1) x) x :=
  (hasDerivAt_hermitePoly_pair n x).1

/-- Corollary: `He_n` is differentiable everywhere. -/
lemma differentiableAt_hermitePoly (n : ℕ) (x : ℝ) :
    DifferentiableAt ℝ (hermitePoly n) x :=
  (hasDerivAt_hermitePoly n x).differentiableAt

/-! ## 3. Hermite-Gaussian function and its ladder derivative -/

/-- **Unnormalized Hermite-Gaussian function** at frequency `ω`:

      `ψ_n(x) = He_n(x) · exp(-ω x² / 2) = He_n(x) · gaussAmpl(ω)(x)`.

    Built directly from Phase 2A's `gaussAmpl`.  No measure theory, no
    normalisation constant — those belong to the L² formalisation and are
    handled separately. -/
def hermiteGaussianFn (n : ℕ) (ω : ℝ) (x : ℝ) : ℝ :=
  hermitePoly n x * gaussAmpl ω x

/-- `ψ_0(x) = 1 · exp(-ω x² / 2) = gaussAmpl(ω)(x)`. -/
@[simp] lemma hermiteGaussianFn_zero (ω x : ℝ) :
    hermiteGaussianFn 0 ω x = gaussAmpl ω x := by
  simp [hermiteGaussianFn]

/-- `ψ_1(x) = x · exp(-ω x² / 2)`. -/
@[simp] lemma hermiteGaussianFn_one (ω x : ℝ) :
    hermiteGaussianFn 1 ω x = x * gaussAmpl ω x := by
  simp [hermiteGaussianFn]

/-- **Ladder-operator derivative identity** (product-rule form).

    The derivative of `ψ_n(x) = He_n(x) · gaussAmpl(ω)(x)` is

      `ψ'_n(x) = He'_n(x) · gaussAmpl(ω)(x) + He_n(x) · gaussAmpl(ω)'(x)`
              = `n · He_{n-1}(x) · gaussAmpl(ω)(x) + He_n(x) · (-(ω x) · gaussAmpl(ω)(x))`
              = `(n · He_{n-1}(x) − ω x · He_n(x)) · gaussAmpl(ω)(x)`.

    This is the raw product-rule form; the "clean" ladder form is
    obtained by substituting the cross-recurrence `x · He_n = He_{n+1} + n · He_{n-1}`
    (see `hasDerivAt_hermiteGaussianFn_ladder` below). -/
lemma hasDerivAt_hermiteGaussianFn (n : ℕ) (ω x : ℝ) :
    HasDerivAt (hermiteGaussianFn n ω)
               (((n : ℝ) * hermitePoly (n - 1) x - ω * x * hermitePoly n x) * gaussAmpl ω x) x := by
  -- Product rule: `HasDerivAt (f · g) (f' · g + f · g')`
  have hHe := hasDerivAt_hermitePoly n x
  -- hHe : HasDerivAt (hermitePoly n) ((n : ℝ) * hermitePoly (n - 1) x) x
  have hg := hasDerivAt_gaussAmpl ω x
  -- hg : HasDerivAt (gaussAmpl ω) (-(ω * x) * gaussAmpl ω x) x
  have hprod := HasDerivAt.mul hHe hg
  -- hprod : HasDerivAt (fun y => hermitePoly n y * gaussAmpl ω y)
  --                    ((n : ℝ) * hermitePoly (n - 1) x * gaussAmpl ω x
  --                     + hermitePoly n x * (-(ω * x) * gaussAmpl ω x)) x
  have hfun : hermiteGaussianFn n ω = fun y => hermitePoly n y * gaussAmpl ω y := rfl
  rw [hfun]
  convert hprod using 1
  ring

/-- **Clean ladder form** of the Hermite-Gaussian derivative.

    Substituting the cross-recurrence `x · He_n = He_{n+1} + n · He_{n-1}`
    into the product-rule form (`hasDerivAt_hermiteGaussianFn`) yields

      `ψ'_n(x) = ((1 − ω) · n · He_{n-1}(x) − ω · He_{n+1}(x)) · gaussAmpl(ω)(x)`.

    At the canonical frequency `ω = 1` this collapses to the classical
    lowering-to-next identity

      `ψ'_n(x) = -He_{n+1}(x) · gaussAmpl(1)(x)`

    i.e. the creation operator takes `ψ_n` to `-ψ_{n+1}`. -/
lemma hasDerivAt_hermiteGaussianFn_ladder (n : ℕ) (ω x : ℝ) :
    HasDerivAt (hermiteGaussianFn n ω)
               (((1 - ω) * (n : ℝ) * hermitePoly (n - 1) x - ω * hermitePoly (n + 1) x)
                  * gaussAmpl ω x) x := by
  have h := hasDerivAt_hermiteGaussianFn n ω x
  convert h using 1
  -- Algebraic rearrangement via the cross-recurrence.
  have h_xk := hermitePoly_mul_x n x
  -- h_xk : x * hermitePoly n x = hermitePoly (n + 1) x + (n : ℝ) * hermitePoly (n - 1) x
  -- Factor gaussAmpl ω x out, then use h_xk:
  have hω : ω * x * hermitePoly n x = ω * (hermitePoly (n + 1) x + (n : ℝ) * hermitePoly (n - 1) x) := by
    have : ω * x * hermitePoly n x = ω * (x * hermitePoly n x) := by ring
    rw [this, h_xk]
  -- Target: ((1 - ω) * n * h_{n-1} - ω * h_{n+1}) * gauss
  --        = (n * h_{n-1} - ω x * h_n) * gauss
  -- n * h_{n-1} - ω x * h_n
  -- = n * h_{n-1} - ω * (h_{n+1} + n * h_{n-1})   (by hω)
  -- = n * h_{n-1} - ω * h_{n+1} - ω * n * h_{n-1}
  -- = (1 - ω) * n * h_{n-1} - ω * h_{n+1}  ✓
  rw [hω]
  ring

/-- **Canonical ω = 1 corollary** — the creation-operator identity.

    `ψ'_n(x) = -He_{n+1}(x) · exp(-x²/2)`.

    This is the raising-operator action on probabilists' Hermite-Gaussian
    functions at the canonical unit frequency. -/
lemma hasDerivAt_hermiteGaussianFn_unit (n : ℕ) (x : ℝ) :
    HasDerivAt (hermiteGaussianFn n 1)
               (-hermitePoly (n + 1) x * gaussAmpl 1 x) x := by
  have h := hasDerivAt_hermiteGaussianFn_ladder n 1 x
  convert h using 1
  ring

/-! ## 4. Position-multiplication and clean ladder identities -/

/-- **Position-multiplication identity** for the unnormalized Hermite-Gaussian.

    `x · ψ_n(x) = ψ_{n+1}(x) + n · ψ_{n-1}(x)`.

    Direct algebraic consequence of `hermitePoly_mul_x` after factoring
    out the Gaussian envelope `gaussAmpl ω x`. -/
lemma hermiteGaussianFn_x_mul (n : ℕ) (ω x : ℝ) :
    x * hermiteGaussianFn n ω x =
      hermiteGaussianFn (n + 1) ω x + (n : ℝ) * hermiteGaussianFn (n - 1) ω x := by
  unfold hermiteGaussianFn
  have h_xk := hermitePoly_mul_x n x
  -- h_xk : x * hermitePoly n x = hermitePoly (n + 1) x + ↑n * hermitePoly (n - 1) x
  have lhs : x * (hermitePoly n x * gaussAmpl ω x)
              = (x * hermitePoly n x) * gaussAmpl ω x := by ring
  rw [lhs, h_xk]
  ring

/-- **Lowering operator (annihilation) identity at ω = 1.**

    `(d/dx + x) ψ_n(x) = n · ψ_{n-1}(x)`.

    Combines `hasDerivAt_hermiteGaussianFn_unit` (which gives the
    derivative value `-ψ_{n+1}`) with `hermiteGaussianFn_x_mul` (which
    gives `x · ψ_n = ψ_{n+1} + n · ψ_{n-1}`); the `ψ_{n+1}` terms cancel.

    This is the algebraic statement of the quantum-harmonic-oscillator
    annihilation operator `a = (d/dx + x)/√(2)` (modulo the √2 normalisation
    constant) acting on the unnormalized probabilists' Hermite-Gaussian
    states.  At the L²-normalized level the same identity becomes
    `a · ψ_n = √n · ψ_{n-1}`, the form quoted in standard QM textbooks
    and used downstream by `@c:\Lean4 Projects\src\SGC\HGCompleteness.lean`. -/
lemma hermiteGaussianFn_lowering_unit (n : ℕ) (x : ℝ) :
    (-hermitePoly (n + 1) x * gaussAmpl 1 x) + x * hermiteGaussianFn n 1 x
      = (n : ℝ) * hermiteGaussianFn (n - 1) 1 x := by
  -- LHS = (derivative value of ψ_n at x) + x · ψ_n(x)
  have hxψ := hermiteGaussianFn_x_mul n 1 x
  -- hxψ : x * hermiteGaussianFn n 1 x
  --       = hermiteGaussianFn (n + 1) 1 x + ↑n * hermiteGaussianFn (n - 1) 1 x
  rw [hxψ]
  -- Now: (-He_{n+1} x · g x) + (ψ_{n+1} x + n · ψ_{n-1} x) = n · ψ_{n-1} x
  -- Need: -He_{n+1} x · g x = -ψ_{n+1} x.  This is just unfolding ψ_{n+1}.
  unfold hermiteGaussianFn
  ring

/-! ## 5. Commentary: what this module provides for downstream work

* For `@c:\Lean4 Projects\src\SGC\HGCompleteness.lean` (when it is repaired):
  the `hg_momentum_recurrence` theorem can now be proved as a corollary of
  `hasDerivAt_hermiteGaussianFn_ladder` together with the L² normalisation
  constant `1 / √(n!)`.  The convention audit in that file should note
  that the probabilists' normalisation gives
  `ψ'_n = -√(n+1) · ψ_{n+1}` (single term), not the two-term form
  currently stated there.

* For future EL / ladder work: `hasDerivAt_hermiteGaussianFn_ladder`
  at general `ω` gives the creation-operator action on *excited* states
  without invoking Mathlib's `Hermite` API (which is not present in this
  Mathlib revision).  This is the kernel of a Phase 2D that formalises
  the raising operator `a† = -∂_x + ωx` acting as `a† ψ_n ∝ ψ_{n+1}`.

* For the canonical wavelet chain (Phases 2A/2B): this module is
  orthogonal — it does not touch `HGBandPassFilter` or the frame
  theorems.  The canonical wavelet `ψ_{α,β}(u) = u^α · exp(-β u²)` with
  continuous `α` is the *non-integer* generalisation of the `He_n`
  ladder; Phase 2C gives the algebraic integer-`n` side of the picture. -/

end SGC.InformationGeometry.HermiteGaussianLadder

end
