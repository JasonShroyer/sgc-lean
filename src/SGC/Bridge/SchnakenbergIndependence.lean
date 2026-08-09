/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Bridge.SchnakenbergBasis

/-!
# Phase F2: independence of the fundamental triangle currents

Phase F built the cycle space and realized every antisymmetric charge
assignment by the chord generator. This module delivers the first half of the
deferred F2 claim: the fundamental triangle currents `triCurrent v₀ x y`,
indexed by ORDERED chords `x < y` (both off the star center), are linearly
independent in the cycle space.

## The unordered-pair mechanism

`triCurrent v₀ x y = -triCurrent v₀ y x`, so the family over all ordered pairs
is dependent. Fixing a linear order on `V` and taking only chords `x < y`
selects one representative per unordered pair. Independence then follows from
the EVALUATION structure: a chord edge `(x, y)` (both endpoints off `v₀`) is
touched by exactly one basis triangle — evaluation at the chord is a dual
functional killing all other generators.

## What is proved

1. `triCurrent_apply_offstar`: off-star evaluation of a triangle current —
   only its chord survives.
2. `triCurrent_chord_linearIndependent`: the ordered-chord family is linearly
   independent (over any `LinearOrder` on the vertex type).

Spanning and the dimension count `(n−1)(n−2)/2` are the second half of F2
(module `SchnakenbergSpan`, forthcoming).
-/

noncomputable section

namespace SGC.Bridge.SchnakenbergIndependence

open Finset
open SGC.Bridge.SchnakenbergBasis

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## §1. Off-star evaluation of triangle currents -/

omit [Fintype V] in
/-- Evaluating a fundamental triangle current at an edge whose endpoints both
    avoid the star center sees ONLY the chord: the two star edges of the
    triangle cannot match. -/
lemma triCurrent_apply_offstar (v₀ x y a b : V)
    (ha : a ≠ v₀) (hb : b ≠ v₀) :
    triCurrent v₀ x y a b
      = (if a = x ∧ b = y then (1 : ℝ) else 0)
        - (if a = y ∧ b = x then (1 : ℝ) else 0) := by
  simp [triCurrent, edgeCurrent, ha, hb]

/-! ## §2. Ordered chords and linear independence -/

variable [LinearOrder V]

/-- An ordered chord of the star tree centered at `v₀`: a pair `x < y` with
    both endpoints off the center. One representative per unordered chord. -/
def Chord (v₀ : V) : Type _ :=
  {p : V × V // p.1 < p.2 ∧ p.1 ≠ v₀ ∧ p.2 ≠ v₀}

instance (v₀ : V) : Fintype (Chord v₀) := by
  unfold Chord; infer_instance

instance (v₀ : V) : DecidableEq (Chord v₀) := by
  unfold Chord; infer_instance

/-- The triangle current attached to an ordered chord. -/
def chordCurrent (v₀ : V) (p : Chord v₀) : V → V → ℝ :=
  triCurrent v₀ p.val.1 p.val.2

omit [Fintype V] in
/-- Evaluating the chord current of `p` at the chord of `i` is the Kronecker
    delta on ordered chords: the reversed match is impossible since both
    chords are strictly increasing. -/
lemma chordCurrent_apply_chord (v₀ : V) (p i : Chord v₀) :
    chordCurrent v₀ p i.val.1 i.val.2 = if p = i then (1 : ℝ) else 0 := by
  obtain ⟨⟨px, py⟩, hpo, hpx, hpy⟩ := p
  obtain ⟨⟨ix, iy⟩, hio, hix, hiy⟩ := i
  rw [chordCurrent, triCurrent_apply_offstar v₀ px py ix iy hix hiy]
  by_cases h : ix = px ∧ iy = py
  · obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    have hne : ix ≠ iy := ne_of_lt hio
    simp [hne]
  · have hne : (⟨(px, py), hpo, hpx, hpy⟩ : Chord v₀)
        ≠ ⟨(ix, iy), hio, hix, hiy⟩ := by
      intro hcon
      apply h
      have := congrArg (fun z : Chord v₀ => z.val) hcon
      simp only at this
      exact ⟨(congrArg Prod.fst this).symm, (congrArg Prod.snd this).symm⟩
    rw [if_neg (by tauto), if_neg hne]
    have hrev : ¬(ix = py ∧ iy = px) := by
      rintro ⟨h1, h2⟩
      subst h1; subst h2
      exact absurd hpo (not_lt.mpr (le_of_lt hio))
    rw [if_neg hrev]
    ring

omit [Fintype V] in
/-- **Linear independence of the fundamental triangle currents** over ordered
    chords: evaluation at each chord is a separating dual family. -/
theorem triCurrent_chord_linearIndependent (v₀ : V) :
    LinearIndependent ℝ (chordCurrent v₀) := by
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have happ : (∑ p ∈ s, g p • chordCurrent v₀ p) i.val.1 i.val.2 = 0 := by
    rw [hsum]; rfl
  rw [Finset.sum_apply, Finset.sum_apply] at happ
  have hcollapse : ∀ p ∈ s, p ≠ i →
      (g p • chordCurrent v₀ p) i.val.1 i.val.2 = 0 := by
    intro p _ hpi
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [chordCurrent_apply_chord v₀ p i, if_neg hpi, mul_zero]
  rw [Finset.sum_eq_single i hcollapse (fun his => absurd hi his)] at happ
  simpa [chordCurrent_apply_chord v₀ i i] using happ

end SGC.Bridge.SchnakenbergIndependence
