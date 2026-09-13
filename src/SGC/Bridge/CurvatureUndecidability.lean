/-
Copyright (c) 2026 Jason Shroyer. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Basic

/-!
# Undecidability of a Global Bakry-Émery Curvature Bound

This module formalizes the **hardness half** of the target

> "The Bakry-Émery Ricci curvature of a Markov generator is computable, and
> deciding a global curvature bound is equivalent to the halting problem."

The construction here is deliberately the *cheapest possible* one, and the
point of the module is that the cheapest one already suffices. We work on the
bi-infinite path `ℤ` — a birth-death chain — with **fixed geometry** (every
vertex has degree 2, forever) and vary only the edge rates, which take just
two values, `1` and `4`.

## The two halves

* `cd0_unitW` (the *bulk*): if every edge has rate `1`, then `Γ₂(f)(x) ≥ 0`
  for every `f` and every `x`, i.e. the unweighted line satisfies
  `CD(0, ∞)`. This is certified by the exact discrete Bochner identity
  `gam2_unitW_eq`:

  `Γ₂(f)(x) = ¼(Δ²f)(x-1)² + ½(Δ²f)(x)² + ¼(Δ²f)(x+1)²`

  where `(Δ²f)(y) = f(y-1) - 2f(y) + f(y+1)` is the second difference. The
  right-hand side is a sum of three squares with positive coefficients and no
  Ricci term — the exact discrete shadow of Bochner's formula on a flat space.
  (Consistent with the published fact that abelian Cayley graphs satisfy
  `CD(0, ∞)`; `ℤ` is the Cayley graph of `ℤ` with generators `±1`.)

* `not_cd0_of_heavy_edge` (the *gadget*): if one single edge `{T, T+1}` is
  given rate `4` while its neighbours keep rate `1`, then `CD(0, ∞)` **fails**,
  because the explicit monotone step function `wit T` satisfies
  `Γ₂(wit T)(T) = -1/4 < 0`. A single edge of the wrong rate is enough; no
  degree spike, no change of geometry, no marked point, no orbit.

## The reduction

Feed in any Boolean predicate `H : ℤ → Bool` that is true at most once — for a
deterministic Turing machine `M` on input `w`, take `H i := "M halts on w in
exactly i steps"`, which is a *total decidable* predicate (simulate exactly `i`
steps), uniformly computable in `(M, w)`. Set the rate of edge `{i, i+1}` to
`4` if `H i` and to `1` otherwise (`haltW`). Then `cd0_haltW_iff` says

  `CD(0, ∞) holds  ↔  H is identically false  ↔  M never halts on w`.

So the set of computable rate functions whose generator satisfies a global
Bakry-Émery bound is `Π⁰₁`-hard; together with the standard fact that
`inf_x κ(x)` is upper-semicomputable for a computable locally finite generator
(the `Π⁰₁` upper bound), deciding a global Bakry-Émery curvature bound is
`Π⁰₁`-complete. It is *equivalent to the complement of the halting problem*,
which is the honest form of the target statement.

## Honest scope

* What is formalized is the **reduction**, with the halting predicate
  abstracted as a Boolean function. The step from "`Π⁰₁`-hard" to "no
  algorithm decides it" is the classical undecidability of halting and is not
  re-proved here.
* No fluid dynamics is used, and none is needed. The Euler/Beltrami
  apparatus (Cardona-Miranda-Peralta-Salas) is *not* required for the hardness
  half; see the companion note in the vault. Claims that route the reduction
  through Turing-complete fluid flows are proving something else — typically a
  statement about an *orbit-restricted* infimum along a trajectory from a
  marked point, not about the intrinsic invariant `inf_x κ(x)` of a generator.
* The reduction is **cheap by design**, and that is the finding: it uses only
  three facts — (i) `κ` is a local invariant, (ii) `κ ≥ 0` for uniform rates,
  (iii) some rational rate pattern has `κ < 0`. Any invariant with those three
  properties is `Π⁰₁`-hard for the same reason. This is why curvature
  undecidability is elementary while the spectral-gap undecidability of
  Cubitt-Perez-Garcia-Wolf is not: a spectral gap is *not* a local invariant.
* Consequently the hoped-for Lichnerowicz-type *equivalence* between curvature
  undecidability and spectral-gap undecidability does **not** follow, and in
  fact fails for this construction: the generators in both branches have
  spectral gap `0` (the bi-infinite path has purely continuous spectrum
  reaching `0`), so no information about halting is carried by the gap.
  Lichnerowicz runs one way only.

## Conventions

`Gamma` and `Gamma2` mirror `SGC.Bridge.GeometricClosure` exactly
(`Γ(f,g) = ½(L(fg) - f·Lg - g·Lf)`, `Γ₂(f,g) = ½(LΓ(f,g) - Γ(f,Lg) - Γ(Lf,g))`),
but are stated for the locally finite generator on `ℤ` rather than for a
`Fintype` matrix, since the whole point is that the state space is infinite.
The Laplacian is the non-normalized one: `(Lf)(x) = Σ_{y∼x} q_{xy}(f y - f x)`.

## Main results

* `gam2_unitW_eq` — exact discrete Bochner identity on the unweighted line
* `cd0_unitW` — the unweighted line satisfies `CD(0, ∞)`
* `gam2_heavy_eq` — local computation at a rate-4 edge: `Γ₂ = -1/4`
* `not_cd0_of_heavy_edge` — one heavy edge destroys `CD(0, ∞)`
* `cd0_haltW_iff` — the reduction: `CD(0, ∞) ↔ the machine never halts`
-/

namespace SGC.Bridge.CurvatureUndecidability

/-! ## 1. The weighted line generator -/

/-- Edge rates on the bi-infinite path: `q i` is the rate of the edge
`{i, i+1}`. -/
abbrev Weights := ℤ → ℝ

/-- All rates equal to `1`: the unweighted bi-infinite path, i.e. the Cayley
graph of `ℤ` with generators `±1`. -/
def unitW : Weights := fun _ => 1

/-- The non-normalized weighted Laplacian on `ℤ`:
`(L f)(x) = q(x-1)·(f(x-1) - f x) + q(x)·(f(x+1) - f x)`.

This is a bona fide conservative Markov generator (row sums vanish) and is
reversible with respect to the counting measure whenever `q ≥ 0`. -/
def lineGen (q : Weights) (f : ℤ → ℝ) : ℤ → ℝ := fun x =>
  q (x - 1) * (f (x - 1) - f x) + q x * (f (x + 1) - f x)

/-- Carré du champ `Γ(f,g) = ½(L(fg) - f·Lg - g·Lf)`.

(`noncomputable` only because division on Mathlib's `ℝ` is; the *content* of
this module is that the arithmetic here is exactly rational and effective. The
rate functions we feed in take values in `{1, 4}` and every certificate below
is a finite rational computation.) -/
noncomputable def gam (q : Weights) (f g : ℤ → ℝ) : ℤ → ℝ := fun x =>
  (1 / 2) * (lineGen q (fun y => f y * g y) x
              - f x * lineGen q g x - g x * lineGen q f x)

/-- Iterated carré du champ `Γ₂(f,g) = ½(LΓ(f,g) - Γ(f,Lg) - Γ(Lf,g))`. -/
noncomputable def gam2 (q : Weights) (f g : ℤ → ℝ) : ℤ → ℝ := fun x =>
  (1 / 2) * (lineGen q (gam q f g) x
              - gam q f (lineGen q g) x - gam q (lineGen q f) g x)

/-- The Bakry-Émery curvature-dimension condition `CD(0, ∞)`:
`Γ₂(f)(x) ≥ 0` for every test function and every state. This is
`SGC.Bridge.GeometricClosure.RicciCurvatureBound` with `ρ = 0`, transported to
the locally finite setting. -/
def CD0 (q : Weights) : Prop := ∀ (f : ℤ → ℝ) (x : ℤ), 0 ≤ gam2 q f f x

/-! ## 2. The bulk: the unweighted line is flat

The key computation. `Γ₂` on `ℤ` is a sum of three squares of second
differences — a discrete Bochner formula whose Ricci term is exactly zero. -/

/-- **Exact discrete Bochner identity on `ℤ`.**

`Γ₂(f)(x)` equals a positive combination of the squared second differences of
`f` at `x-1`, `x`, `x+1`, with no remaining curvature term. -/
theorem gam2_unitW_eq (f : ℤ → ℝ) (x : ℤ) :
    gam2 unitW f f x
      = 1 / 4 * (f (x - 2) - 2 * f (x - 1) + f x) ^ 2
      + 1 / 2 * (f (x - 1) - 2 * f x + f (x + 1)) ^ 2
      + 1 / 4 * (f x - 2 * f (x + 1) + f (x + 2)) ^ 2 := by
  have e1 : x - 1 - 1 = x - 2 := by ring
  have e2 : x - 1 + 1 = x := by ring
  have e3 : x + 1 - 1 = x := by ring
  have e4 : x + 1 + 1 = x + 2 := by ring
  simp only [gam2, gam, lineGen, unitW, e1, e2, e3, e4]
  ring

/-- **The unweighted bi-infinite path satisfies `CD(0, ∞)`.**

Every vertex of `ℤ` has non-negative Bakry-Émery curvature. Immediate from the
Bochner identity, since the right-hand side is a sum of squares. -/
theorem cd0_unitW : CD0 unitW := by
  intro f x
  rw [gam2_unitW_eq]
  have h1 : (0:ℝ) ≤ (f (x - 2) - 2 * f (x - 1) + f x) ^ 2 := sq_nonneg _
  have h2 : (0:ℝ) ≤ (f (x - 1) - 2 * f x + f (x + 1)) ^ 2 := sq_nonneg _
  have h3 : (0:ℝ) ≤ (f x - 2 * f (x + 1) + f (x + 2)) ^ 2 := sq_nonneg _
  linarith

/-! ## 3. The gadget: one heavy edge destroys the bound

Note that a *geometric* gadget does not work here and we do not use one: the
endpoint of a ray has Bakry-Émery curvature `+3/2 > 0`, so "the computation
simply stops" is not by itself curvature-violating. What works is a single
edge whose rate differs from its neighbours'. -/

/-- The test function that detects a heavy edge at `{T, T+1}`: a monotone step
that rises from `-1` to `1` across the edge.

`wit T` takes the values `(-1, 0, 1, 1, 1)` at `(T-2, T-1, T, T+1, T+2)`, and
only those five values matter, since `Γ₂(f)(T)` depends on `f` only through
its restriction to the 2-ball around `T`. -/
def wit (T : ℤ) : ℤ → ℝ := fun y => if y ≤ T - 2 then -1 else if y ≤ T - 1 then 0 else 1

@[simp] lemma wit_sub_two (T : ℤ) : wit T (T - 2) = -1 := by simp [wit]

@[simp] lemma wit_sub_one (T : ℤ) : wit T (T - 1) = 0 := by
  have h : ¬ (T - 1 ≤ T - 2) := by omega
  simp [wit, h]

@[simp] lemma wit_self (T : ℤ) : wit T T = 1 := by
  have h1 : ¬ (T ≤ T - 2) := by omega
  have h2 : ¬ (T ≤ T - 1) := by omega
  simp [wit, h1, h2]

@[simp] lemma wit_add_one (T : ℤ) : wit T (T + 1) = 1 := by
  have h1 : ¬ (T + 1 ≤ T - 2) := by omega
  have h2 : ¬ (T + 1 ≤ T - 1) := by omega
  simp [wit, h1, h2]

@[simp] lemma wit_add_two (T : ℤ) : wit T (T + 2) = 1 := by
  have h1 : ¬ (T + 2 ≤ T - 2) := by omega
  have h2 : ¬ (T + 2 ≤ T - 1) := by omega
  simp [wit, h1, h2]

/-- **The local curvature certificate.**

For *any* rate function that is `4` on the edge `{T, T+1}` and `1` on the three
neighbouring edges, the step function `wit T` has strictly negative `Γ₂` at
`T`. Stated with the rates as hypotheses rather than as a definition, so that
it can be reused for any encoding. -/
theorem gam2_heavy_eq (q : Weights) (T : ℤ)
    (hq2 : q (T - 2) = 1) (hq1 : q (T - 1) = 1) (hq0 : q T = 4)
    (hqp : q (T + 1) = 1) :
    gam2 q (wit T) (wit T) T = -(1 / 4) := by
  have e1 : T - 1 - 1 = T - 2 := by ring
  have e2 : T - 1 + 1 = T := by ring
  have e3 : T + 1 - 1 = T := by ring
  have e4 : T + 1 + 1 = T + 2 := by ring
  simp only [gam2, gam, lineGen, e1, e2, e3, e4, hq2, hq1, hq0, hqp,
    wit_sub_two, wit_sub_one, wit_self, wit_add_one, wit_add_two]
  norm_num

/-- **One heavy edge destroys `CD(0, ∞)`.** -/
theorem not_cd0_of_heavy_edge (q : Weights) (T : ℤ)
    (hq2 : q (T - 2) = 1) (hq1 : q (T - 1) = 1) (hq0 : q T = 4)
    (hqp : q (T + 1) = 1) :
    ¬ CD0 q := by
  intro h
  have := h (wit T) T
  rw [gam2_heavy_eq q T hq2 hq1 hq0 hqp] at this
  norm_num at this

/-! ## 4. The reduction

`H i` is intended to be "the machine halts in exactly `i` steps" — a total
decidable predicate, true at most once for a deterministic machine. -/

/-- Rates built from a halting predicate: rate `4` on the edge `{i, i+1}` when
`H i` holds, rate `1` everywhere else. Computable whenever `H` is. -/
def haltW (H : ℤ → Bool) : Weights := fun i => if H i then 4 else 1

lemma haltW_eq_one {H : ℤ → Bool} {i : ℤ} (h : H i = false) : haltW H i = 1 := by
  simp [haltW, h]

lemma haltW_eq_four {H : ℤ → Bool} {i : ℤ} (h : H i = true) : haltW H i = 4 := by
  simp [haltW, h]

/-- If the machine never halts, every rate is `1` and the chain is the flat
line. -/
lemma haltW_eq_unitW {H : ℤ → Bool} (h : ∀ i, H i = false) : haltW H = unitW := by
  funext i
  simp [haltW, unitW, h i]

/-- **The reduction.** For a halting predicate that is true at most once, the
generator of the associated birth-death chain satisfies the global
Bakry-Émery bound `CD(0, ∞)` if and only if the machine never halts.

The state space (`ℤ`), the geometry (degree 2 at every vertex) and the rate
alphabet (`{1, 4}`) are all fixed; only the placement of the single heavy edge
depends on the computation, and whether any heavy edge exists at all is
exactly the halting question. -/
theorem cd0_haltW_iff (H : ℤ → Bool) (hone : ∀ i j, H i = true → H j = true → i = j) :
    CD0 (haltW H) ↔ ∀ i, H i = false := by
  constructor
  · intro hcd i
    by_contra hi
    have hT : H i = true := by
      cases hb : H i with
      | false => exact absurd hb hi
      | true => rfl
    -- every other edge is light, by uniqueness of the halting step
    have light : ∀ j, j ≠ i → haltW H j = 1 := by
      intro j hj
      cases hb : H j with
      | false => exact haltW_eq_one hb
      | true => exact absurd (hone j i hb hT) hj
    exact not_cd0_of_heavy_edge (haltW H) i
      (light (i - 2) (by omega)) (light (i - 1) (by omega))
      (haltW_eq_four hT) (light (i + 1) (by omega)) hcd
  · intro h
    rw [haltW_eq_unitW h]
    exact cd0_unitW

/-- The contrapositive form: a halting computation is witnessed by curvature. -/
theorem not_cd0_haltW_of_halts (H : ℤ → Bool) (T : ℤ)
    (hone : ∀ i j, H i = true → H j = true → i = j) (hT : H T = true) :
    ¬ CD0 (haltW H) := by
  rw [cd0_haltW_iff H hone]
  intro h
  simp [h T] at hT

end SGC.Bridge.CurvatureUndecidability
