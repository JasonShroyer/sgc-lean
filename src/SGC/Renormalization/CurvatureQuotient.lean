/-
Copyright (c) 2026 Jason Shroyer. All rights reserved.
Released under Apache 2.0 license.
-/
import SGC.Renormalization.Lumpability
import SGC.Bridge.GeometricClosure

/-!
# Bakry-Émery Curvature Bounds Descend Along Exactly Lumpable Quotients

This formalizes the answer to the question that the Solaris Deep Research
foraging run isolated as **Contested** and load-bearing:

> "whether discrete Bakry-Émery, Ollivier-Ricci, or entropic Ricci curvature
> bounds are preserved under lumpability or quotient operations […] remains an
> unresolved, open research question. The existing literature does not contain
> verified results proving that coarse-graining maps respect the underlying
> Γ-calculus."

## Prior art (2026-08-09 audit — the foraging quote above is superseded)

The *mathematical* content of the descent theorem is not new: Pedrotti–Salez,
"A new cutoff criterion for non-negatively curved chains" (arXiv:2501.13079,
Jan 2025), §2.2 "Markovian projections", record exactly this observation —
the Bakry-Émery curvature condition is preserved under Markovian projection
(their intertwining `T(f ∘ Φ) = (T̂ f) ∘ Φ` is our `L_lift_eq`) — and call it
"elementary (but seemingly new)". Any paper or claim built on this module
MUST cite Pedrotti–Salez. What this module contributes beyond that — to our
knowledge, pending a dedicated cross-prover prior-art search (Lean, Isabelle,
Coq/Rocq): (a) a kernel-checked Lean 4 formalization of the
projection/intertwining curvature argument for finite discrete Markov
generators, and (b) the strict-improvement witness
(`StarExample.curvature_hiding`): a fine chain violating `CD(0,∞)` whose
two-state orbit quotient satisfies `CD(9/2,∞)`, pinning the one-way-ness
quantitatively. For per-vertex Bakry-Émery curvature as an eigenvalue /
semidefinite problem (the computability anchor for the companion module
`SGC.Bridge.CurvatureUndecidability`), see Cushing–Kamtue–Liu–Peyerimhoff,
arXiv:2102.08687.

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

/-! ## 4. The converse fails: coarse-graining can HIDE a curvature violation

The descent theorem is strictly one-way. Witness: the star `K_{1,6}` (centre
plus six leaves), lumped by its automorphism orbits `{centre | leaves}`. The
fine chain **violates** `CD(0,∞)` — the centre has curvature `-3/2` and an
explicit observable below has `Γ₂ = -17/2 < 0` — while the coarse chain (a
two-state generator) satisfies `CD(9/2,∞)`, a *large positive* bound.

The mechanism is visible in the intertwining identities: the quotient sees
exactly the block-constant observables, and the violating observable is
anti-symmetric across the leaf orbit (`f(leaf₀) ≠ f(other leaves)`) — precisely
the direction that coarse-graining kills. A curvature bound on a quotient
therefore carries **no** information about the fine chain beyond the one-sided
descent bound. -/

namespace StarExample

/-- The (negative of the) graph Laplacian of the star `K_{1,6}`: vertex `0` is
the centre, vertices `1..6` are leaves. Rows sum to zero. -/
def starGen : Matrix (Fin 7) (Fin 7) ℝ := fun i j =>
  if i = j then (if i = 0 then -6 else -1) else if i = 0 ∨ j = 0 then 1 else 0

/-- The automorphism-orbit partition of the star: the centre is one block, the
six leaves are the other. Two vertices are related iff they are both the
centre or both leaves. -/
def starSetoid : Setoid (Fin 7) where
  r x y := (x = 0 ↔ y = 0)
  iseqv := ⟨fun _ => Iff.rfl, Iff.symm, Iff.trans⟩

/-- The orbit partition, packaged for the lumpability machinery. -/
def starP : Partition (Fin 7) where
  rel := starSetoid
  decRel := fun x y => inferInstanceAs (Decidable (x = 0 ↔ y = 0))

lemma starP_mk_eq_mk {z w : Fin 7} :
    (Quotient.mk starP.rel z = Quotient.mk starP.rel w) ↔ (z = 0 ↔ w = 0) :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- The star is exactly lumpable with respect to its orbit partition. -/
theorem starGen_lumpable : IsStronglyLumpable starGen starP := by
  intro x y hxy b
  induction b using Quotient.ind with
  | _ w =>
    have hxy' : (x = 0 ↔ y = 0) := hxy
    by_cases hx : x = 0
    · have hy : y = 0 := hxy'.mp hx
      subst hx; subst hy; rfl
    · have hy : ¬ y = 0 := fun h => hx (hxy'.mpr h)
      by_cases hw : w = 0
      · subst hw
        simp only [Partition.quot_map, starP_mk_eq_mk]
        rw [Fin.sum_univ_seven, Fin.sum_univ_seven]
        simp [starGen, hx, hy]
      · simp only [Partition.quot_map, starP_mk_eq_mk]
        rw [Fin.sum_univ_seven, Fin.sum_univ_seven]
        simp only [starGen, hx, hy, hw]
        fin_cases x <;> fin_cases y <;> simp_all

/-- The observable that witnesses the violation: `-1` at the centre, `+2` at
one distinguished leaf, `-2` at the five others. It is anti-symmetric across
the leaf orbit, which is exactly why the quotient cannot see it. -/
def witF : Fin 7 → ℝ := fun v => if v = 0 then -1 else if v = 1 then 2 else -2

/-- The star violates `CD(0,∞)`: at the centre, `Γ₂(witF) = -17/2 < 0`. -/
theorem starGen_not_cd0 : ¬ RicciCurvatureBound starGen 0 := by
  intro h
  have hb := h.curvature_bound witF 0
  have h2 : Gamma2Sq starGen witF 0 = -(17/2) := by
    simp [Gamma2Sq, Gamma2, Gamma, Matrix.mulVec, dotProduct,
      Fin.sum_univ_seven, starGen, witF]
    norm_num
  rw [h2] at hb
  have h1 : (0:ℝ) * GammaSq starGen witF 0 = 0 := zero_mul _
  rw [h1] at hb
  norm_num at hb

/-- Every observable on the quotient lifts to a two-valued observable on the
star, constant on the leaf orbit. -/
lemma lift_two_valued (f : starP.Quot → ℝ) :
    lift_fun starP f = fun v : Fin 7 =>
      if v = 0 then f (Quotient.mk starP.rel 0) else f (Quotient.mk starP.rel 1) := by
  funext v
  simp only [lift_fun, Partition.quot_map]
  by_cases hv : v = 0
  · subst hv; simp
  · rw [if_neg hv]
    congr 1
    exact Quotient.sound (iff_of_false hv (by decide))

set_option maxHeartbeats 1600000 in
/-- **The coarse chain is strongly positively curved.** The two-state orbit
quotient of the star satisfies `CD(9/2, ∞)` — sharp at the centre block. -/
theorem starQuotient_cd : RicciCurvatureBound (QuotientGeneratorSimple starGen starP) (9/2) where
  curvature_bound := by
    intro f A
    obtain ⟨a, ha⟩ := Quotient.exists_rep A
    have h2 := congrFun (Gamma2Sq_lift_eq starGen starP starGen_lumpable f) a
    have h1 := congrFun (GammaSq_lift_eq starGen starP starGen_lumpable f) a
    simp only [lift_fun, Partition.quot_map, ha] at h2 h1
    rw [← h2, ← h1, lift_two_valued f]
    set p := f (Quotient.mk starP.rel 0) with hp
    set q := f (Quotient.mk starP.rel 1) with hq
    fin_cases a <;>
      simp [Gamma2Sq, Gamma2, Gamma, GammaSq, Matrix.mulVec, dotProduct,
        Fin.sum_univ_seven, starGen] <;>
      nlinarith [sq_nonneg (p - q)]

/-- **Coarse-graining can hide a curvature violation.**

The star `K_{1,6}` is exactly lumpable onto a two-state chain; the fine chain
violates `CD(0,∞)` while its quotient satisfies `CD(9/2,∞)`. Together with
`RicciCurvatureBound_quotient` this pins the quotient-curvature relationship
exactly: bounds descend, and nothing comes back up. -/
theorem curvature_hiding :
    IsStronglyLumpable starGen starP ∧
    ¬ RicciCurvatureBound starGen 0 ∧
    RicciCurvatureBound (QuotientGeneratorSimple starGen starP) (9/2) :=
  ⟨starGen_lumpable, starGen_not_cd0, starQuotient_cd⟩

end StarExample

end SGC.Renormalization.CurvatureQuotient
