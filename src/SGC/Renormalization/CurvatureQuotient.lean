/-
Copyright (c) 2026 Jason Shroyer. All rights reserved.
Released under Apache 2.0 license.
-/
import SGC.Renormalization.Lumpability
import SGC.Bridge.GeometricClosure

/-!
# Bakry-Émery Curvature Bounds Descend Along Exactly Lumpable Quotients

This settles the question that the Solaris Deep Research foraging run isolated
as **Contested** and load-bearing:

> "whether discrete Bakry-Émery, Ollivier-Ricci, or entropic Ricci curvature
> bounds are preserved under lumpability or quotient operations […] remains an
> unresolved, open research question. The existing literature does not contain
> verified results proving that coarse-graining maps respect the underlying
> Γ-calculus."

For **exact (strong) lumpability** the answer is yes, and it is a two-line
consequence of the intertwining theorem `L_lift_eq` already proved in
`SGC.Renormalization.Lumpability`. The whole Γ-calculus intertwines:

    Γ_L (lift f) (lift g)   = lift (Γ_M f g)         -- `Gamma_lift_eq`
    Γ₂_L (lift f) (lift g)  = lift (Γ₂_M f g)        -- `Gamma2_lift_eq`

because lifting is a *ring* homomorphism on functions (`lift f · lift g =
lift (f·g)`) as well as intertwining the generators. Since every function on
the quotient is a lift, and every quotient state is `⟦x⟧` for some `x`, the
curvature-dimension condition transfers verbatim:

    `RicciCurvatureBound L ρ  →  RicciCurvatureBound (L/P) ρ`

## Direction, and what is *not* claimed

The implication runs **fine → coarse only**. Curvature bounds are inherited
downward: an exactly lumpable quotient of a `CD(ρ,∞)` chain is `CD(ρ,∞)`, and
in general strictly *more* curved (numerically: `C₈ → C₈/rot₂` takes
`min κ` from `0` to `+4`; `K₆ → 2 blocks` takes `+4` to `+6`; `Q_d → Ehrenfest`
holds `+2`). The converse is false in general and is **not** proved here — this
is the same one-way asymmetry already recorded for `KillingDefect` in
`SGC.Bridge.ExoticPairs` (fine irreversibility can hide under a coarse
equilibrium, never the reverse).

Note also that this is *exact* lumpability. Nothing here covers the
approximate/`ε`-lumpable case (`IsRowSumApproxLumpable`), where the Γ-calculus
picks up defect terms; that remains open and is the natural next question.

## Consequence for undecidability

Combined with `SGC.Bridge.CurvatureUndecidability`, this closes the transfer
that the commission's H2 asked for — though not by the route it proposed.
Deciding a global Bakry-Émery bound is `Π⁰₁`-complete downstairs, and by
`RicciCurvatureBound_quotient` a curvature bound upstairs *forces* one
downstairs. So renormalization can only ever **improve** curvature, never
create a violation: a coarse-grained model that fails `CD(ρ,∞)` certifies that
the fine model failed it too. Coarse-graining is therefore a sound (one-sided)
proof technique for curvature *violation*, and useless for curvature
*verification* — the sound direction is the opposite of the one usually wanted.

## Main results

* `lift_fun_mul` — lifting is multiplicative
* `Gamma_lift_eq` — Γ intertwines with the quotient
* `Gamma2_lift_eq` — Γ₂ intertwines with the quotient
* `RicciCurvatureBound_quotient` — `CD(ρ,∞)` descends (the headline)
* `HasPositiveRicci_quotient` — positive Ricci descends
-/

namespace SGC.Renormalization.CurvatureQuotient

open SGC SGC.Bridge.GeometricClosure
open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The quotient of a nonempty state space is nonempty. -/
instance instNonemptyQuot [Nonempty V] (P : Partition V) : Nonempty P.Quot :=
  ⟨P.quot_map (Classical.arbitrary V)⟩

/-! ## 1. Lifting is a ring homomorphism on observables -/

omit [Fintype V] in
/-- Lifting a product is the product of the lifts. This is what makes the
whole Γ-calculus (which is quadratic in the observable) intertwine, on top of
the linear intertwining `L_lift_eq`. -/
lemma lift_fun_mul (P : Partition V) (f g : P.Quot → ℝ) :
    lift_fun P f * lift_fun P g = lift_fun P (f * g) := rfl

/-! ## 2. The Γ-calculus intertwines -/

/-- **Γ intertwines with exact coarse-graining.**

`Γ_L` evaluated on lifted observables is the lift of `Γ_M` evaluated on the
originals: the carré du champ cannot tell the difference between working
upstairs on block-constant functions and working downstairs. -/
theorem Gamma_lift_eq (L : Matrix V V ℝ) (P : Partition V)
    (hL : IsStronglyLumpable L P) (f g : P.Quot → ℝ) :
    Gamma L (lift_fun P f) (lift_fun P g)
      = lift_fun P (Gamma (QuotientGeneratorSimple L P) f g) := by
  funext v
  simp only [Gamma, lift_fun_mul, L_lift_eq L P hL, lift_fun]

/-- **Γ₂ intertwines with exact coarse-graining.**

The iterated carré du champ — the operator that carries the curvature — also
commutes with lifting. Immediate from `Gamma_lift_eq` plus `L_lift_eq`. -/
theorem Gamma2_lift_eq (L : Matrix V V ℝ) (P : Partition V)
    (hL : IsStronglyLumpable L P) (f g : P.Quot → ℝ) :
    Gamma2 L (lift_fun P f) (lift_fun P g)
      = lift_fun P (Gamma2 (QuotientGeneratorSimple L P) f g) := by
  funext v
  simp only [Gamma2, Gamma_lift_eq L P hL, L_lift_eq L P hL, lift_fun]

/-- Squared versions, the form the curvature condition is stated in. -/
theorem GammaSq_lift_eq (L : Matrix V V ℝ) (P : Partition V)
    (hL : IsStronglyLumpable L P) (f : P.Quot → ℝ) :
    GammaSq L (lift_fun P f)
      = lift_fun P (GammaSq (QuotientGeneratorSimple L P) f) :=
  Gamma_lift_eq L P hL f f

theorem Gamma2Sq_lift_eq (L : Matrix V V ℝ) (P : Partition V)
    (hL : IsStronglyLumpable L P) (f : P.Quot → ℝ) :
    Gamma2Sq L (lift_fun P f)
      = lift_fun P (Gamma2Sq (QuotientGeneratorSimple L P) f) :=
  Gamma2_lift_eq L P hL f f

/-! ## 3. The curvature bound descends -/

/-- **Bakry-Émery curvature bounds are inherited by exactly lumpable
quotients.**

If the fine generator satisfies `CD(ρ, ∞)` then so does the coarse-grained
generator, for the *same* `ρ`. Renormalization never destroys a curvature
lower bound.

Proof: pick any representative `a` of the coarse state `A`. Test the fine
bound against the lifted observable at `a`, then push both sides through the
intertwining identities. -/
theorem RicciCurvatureBound_quotient (L : Matrix V V ℝ) (P : Partition V)
    (hL : IsStronglyLumpable L P) (rho : ℝ) (h : RicciCurvatureBound L rho) :
    RicciCurvatureBound (QuotientGeneratorSimple L P) rho where
  curvature_bound := by
    intro f A
    obtain ⟨a, ha⟩ := Quotient.exists_rep A
    have hA : P.quot_map a = A := ha
    have hfine := h.curvature_bound (lift_fun P f) a
    rw [Gamma2Sq_lift_eq L P hL f, GammaSq_lift_eq L P hL f] at hfine
    simpa [lift_fun, hA] using hfine

/-- Positive Ricci curvature descends to exactly lumpable quotients. -/
theorem HasPositiveRicci_quotient (L : Matrix V V ℝ) (P : Partition V)
    (hL : IsStronglyLumpable L P) (h : HasPositiveRicci L) :
    HasPositiveRicci (QuotientGeneratorSimple L P) := by
  obtain ⟨rho, hpos, hbound⟩ := h
  exact ⟨rho, hpos, RicciCurvatureBound_quotient L P hL rho hbound⟩

/-- Contrapositive, and the practically useful direction: if the coarse model
violates `CD(ρ,∞)`, the fine model did too. Coarse-graining is a sound
one-sided certificate for curvature *violation*. -/
theorem not_RicciCurvatureBound_of_quotient (L : Matrix V V ℝ) (P : Partition V)
    (hL : IsStronglyLumpable L P) (rho : ℝ)
    (h : ¬ RicciCurvatureBound (QuotientGeneratorSimple L P) rho) :
    ¬ RicciCurvatureBound L rho :=
  fun hfine => h (RicciCurvatureBound_quotient L P hL rho hfine)

end SGC.Renormalization.CurvatureQuotient
