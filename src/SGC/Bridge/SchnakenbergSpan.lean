/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Bridge.SchnakenbergIndependence

/-!
# Phase F2 (completion): the chord basis and the dimension of the cycle space

`SchnakenbergIndependence` proved the ordered-chord triangle currents linearly
independent. This module proves they SPAN the cycle space, packages the result
as a `Basis`, and computes the dimension: `2·dim = (n−1)(n−2)` — the first
Betti number of the complete graph, realized by the star-tree fundamental
cycles.

## The two-step decomposition argument

For `J` in the cycle space, the candidate expansion
`S = ∑_{x<y off-star} J x y • triCurrent v₀ x y` agrees with `J`:

1. **Off-star edges** (`a, b ≠ v₀`): the chord evaluation is a Kronecker
   delta, so the sum collapses to the single triangle owning that chord
   (orientation handled by antisymmetry of `J`).
2. **Star edges**: no sum manipulation at all — `D = J − S` lies in the cycle
   space and vanishes off-star, so the divergence-free condition at any
   `b ≠ v₀` forces `D b v₀ = 0`, and antisymmetry finishes the row `v₀`.

Step 2 replaces the classical (and formalization-heavy) telescoping count of
star-edge contributions with a two-line conservation argument: the cycle-space
structure itself propagates agreement from chords to the tree.

## What is proved

1. `chordExpansion_apply_offstar` — the collapse (step 1).
2. `cycleSpace_decomposition` — `J = chordExpansion v₀ J` (step 2).
3. `cycleSpace_eq_span` — the cycle space IS the span of the chord currents.
4. `chordBasis` — the chord currents as a `Basis (Chord v₀) ℝ cycleSpace`.
5. `finrank_cycleSpace_eq_card_chord` — `dim = #Chord`.
6. `two_mul_card_chord` — `2·#Chord = (n−1)(n−2)` (swap-involution halving,
   division-free).
7. **`two_mul_finrank_cycleSpace`** (headline) —
   `2·dim cycleSpace = (n−1)(n−2)`.

## Epistemic state

Every declaration kernel-proven; no sorries, no new axioms. This closes the
F2 debt recorded in `SchnakenbergBasis`: the affinity data is conserved
(Phase E), free (Phase F), and of exact dimension `(n−1)(n−2)/2` (F2) — the
parameter count of the NESS landscape.
-/

noncomputable section

namespace SGC.Bridge.SchnakenbergSpan

open Finset
open SGC.Bridge.DiscreteFluidDynamics
open SGC.Bridge.SchnakenbergBasis
open SGC.Bridge.SchnakenbergIndependence

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

/-! ## §1. The chord expansion and its off-star collapse -/

/-- The candidate decomposition of an edge field: chord-weighted sum of
    fundamental triangle currents. -/
def chordExpansion (v₀ : V) (J : V → V → ℝ) : V → V → ℝ :=
  ∑ p : Chord v₀, J p.val.1 p.val.2 • chordCurrent v₀ p

lemma antisymm_diag_zero {J : V → V → ℝ} (hJ : ∀ x y, J x y = -J y x) (a : V) :
    J a a = 0 := by
  have := hJ a a; linarith

/-- Chord currents are antisymmetric edge fields (unconditionally). -/
lemma chordCurrent_antisymm (v₀ : V) (p : Chord v₀) (x y : V) :
    chordCurrent v₀ p x y = -chordCurrent v₀ p y x := by
  simp only [chordCurrent, triCurrent, Pi.add_apply,
    edgeCurrent_antisymm v₀ p.val.1 x y, edgeCurrent_antisymm p.val.1 p.val.2 x y,
    edgeCurrent_antisymm p.val.2 v₀ x y]
  ring

/-- Reversed Kronecker evaluation: a chord current at the REVERSED chord of
    `i` is `−δ`. -/
lemma chordCurrent_apply_chord_rev (v₀ : V) (p i : Chord v₀) :
    chordCurrent v₀ p i.val.2 i.val.1 = if p = i then (-1 : ℝ) else 0 := by
  rw [chordCurrent_antisymm, chordCurrent_apply_chord]
  split_ifs <;> ring

/-- **Chord evaluation of the expansion**: at the chord of `i`, the expansion
    sum collapses to `J` at that chord. -/
lemma chordExpansion_eval_at (v₀ : V) (J : V → V → ℝ) (i : Chord v₀) :
    chordExpansion v₀ J i.val.1 i.val.2 = J i.val.1 i.val.2 := by
  unfold chordExpansion
  rw [Finset.sum_apply, Finset.sum_apply]
  have hterm : ∀ c : Chord v₀,
      (J c.val.1 c.val.2 • chordCurrent v₀ c) i.val.1 i.val.2
        = if c = i then J i.val.1 i.val.2 else 0 := by
    intro c
    simp only [Pi.smul_apply, smul_eq_mul, chordCurrent_apply_chord v₀ c i]
    by_cases hc : c = i
    · subst hc; simp
    · simp [hc]
  rw [Finset.sum_congr rfl fun c _ => hterm c,
    Finset.sum_ite_eq' Finset.univ i fun _ => J i.val.1 i.val.2,
    if_pos (Finset.mem_univ i)]

/-- Reversed chord evaluation of the expansion. -/
lemma chordExpansion_eval_at_rev (v₀ : V) (J : V → V → ℝ) (i : Chord v₀) :
    chordExpansion v₀ J i.val.2 i.val.1 = -J i.val.1 i.val.2 := by
  unfold chordExpansion
  rw [Finset.sum_apply, Finset.sum_apply]
  have hterm : ∀ c : Chord v₀,
      (J c.val.1 c.val.2 • chordCurrent v₀ c) i.val.2 i.val.1
        = if c = i then -J i.val.1 i.val.2 else 0 := by
    intro c
    simp only [Pi.smul_apply, smul_eq_mul, chordCurrent_apply_chord_rev v₀ c i]
    by_cases hc : c = i
    · subst hc; simp
    · simp [hc]
  rw [Finset.sum_congr rfl fun c _ => hterm c,
    Finset.sum_ite_eq' Finset.univ i fun _ => -J i.val.1 i.val.2,
    if_pos (Finset.mem_univ i)]

/-- **Off-star collapse**: on an edge avoiding the star center, the expansion
    sum sees exactly one triangle — the one owning the chord — and reproduces
    `J` there (antisymmetry supplies the reversed orientation). -/
lemma chordExpansion_apply_offstar (v₀ : V) {J : V → V → ℝ}
    (hJ : ∀ x y, J x y = -J y x) (a b : V) (ha : a ≠ v₀) (hb : b ≠ v₀) :
    chordExpansion v₀ J a b = J a b := by
  rcases eq_or_ne a b with rfl | hab
  · unfold chordExpansion
    rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_zero,
      antisymm_diag_zero hJ]
    intro p _
    obtain ⟨⟨px, py⟩, hpo, hpx, hpy⟩ := p
    simp only [Pi.smul_apply, smul_eq_mul, chordCurrent,
      triCurrent_apply_offstar v₀ px py a a ha ha]
    have h1 : ¬(a = px ∧ a = py) := by
      rintro ⟨rfl, rfl⟩; exact absurd hpo (lt_irrefl _)
    have h2 : ¬(a = py ∧ a = px) := by
      rintro ⟨rfl, rfl⟩; exact absurd hpo (lt_irrefl _)
    rw [if_neg h1, if_neg h2]; ring
  · rcases hab.lt_or_gt with hlt | hgt
    · exact chordExpansion_eval_at v₀ J ⟨(a, b), hlt, ha, hb⟩
    · rw [hJ a b]
      exact chordExpansion_eval_at_rev v₀ J ⟨(b, a), hgt, hb, ha⟩

/-! ## §2. The decomposition theorem -/

/-- The chord expansion lies in the cycle space (it is a finite combination
    of triangle currents). -/
lemma chordExpansion_mem_cycleSpace (v₀ : V) (J : V → V → ℝ) :
    chordExpansion v₀ J ∈ cycleSpace := by
  apply Submodule.sum_mem
  rintro ⟨⟨px, py⟩, hpo, hpx, hpy⟩ _
  exact Submodule.smul_mem _ _
    (triCurrent_mem_cycleSpace v₀ px py hpx hpy (ne_of_lt hpo))

/-- **The decomposition theorem**: every cycle-space element is the
    chord-weighted sum of fundamental triangle currents. Star edges follow
    from conservation: the defect `J − S` is a cycle vanishing off-star, and
    divergence-freeness forces its star edges to vanish too. -/
theorem cycleSpace_decomposition (v₀ : V) (J : V → V → ℝ)
    (hJ : J ∈ cycleSpace) : J = chordExpansion v₀ J := by
  obtain ⟨hanti, hker⟩ := hJ
  have hdiv : ∀ x, ∑ y, J x y = 0 := by
    intro x
    have h0 : divergenceHom J = 0 := LinearMap.mem_ker.mp hker
    simpa [divergenceHom_apply, divergence] using congrFun h0 x
  obtain ⟨hSanti, hSker⟩ := chordExpansion_mem_cycleSpace v₀ J
  have hSdiv : ∀ x, ∑ y, chordExpansion v₀ J x y = 0 := by
    intro x
    have h0 : divergenceHom (chordExpansion v₀ J) = 0 := LinearMap.mem_ker.mp hSker
    simpa [divergenceHom_apply, divergence] using congrFun h0 x
  have hoff : ∀ a b, a ≠ v₀ → b ≠ v₀ → chordExpansion v₀ J a b = J a b :=
    fun a b => chordExpansion_apply_offstar v₀ hanti a b
  -- star column: divergence at b ≠ v₀ has a single unknown term, J b v₀
  have hstar : ∀ b, b ≠ v₀ → J b v₀ = chordExpansion v₀ J b v₀ := by
    intro b hb
    have h1 := hdiv b
    have h2 := hSdiv b
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ v₀)] at h1 h2
    have herase : ∑ y ∈ Finset.univ.erase v₀, chordExpansion v₀ J b y
        = ∑ y ∈ Finset.univ.erase v₀, J b y :=
      Finset.sum_congr rfl fun y hy => hoff b y hb (Finset.mem_erase.mp hy).1
    rw [herase] at h2
    linarith
  funext a b
  by_cases ha : a = v₀
  · by_cases hb : b = v₀
    · rw [ha, hb, antisymm_diag_zero hanti, antisymm_diag_zero hSanti]
    · rw [ha, hanti v₀ b, hSanti v₀ b, hstar b hb]
  · by_cases hb : b = v₀
    · rw [hb]; exact hstar a ha
    · exact (hoff a b ha hb).symm

/-! ## §3. Span, basis, dimension -/

/-- **The cycle space is spanned by the star-tree fundamental cycles**: the
    complete-graph cycle space equals the span of the ordered-chord triangle
    currents. -/
theorem cycleSpace_eq_span (v₀ : V) :
    cycleSpace = Submodule.span ℝ (Set.range (chordCurrent v₀)) := by
  apply le_antisymm
  · intro J hJ
    rw [cycleSpace_decomposition v₀ J hJ]
    exact Submodule.sum_mem _ fun p _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨⟨⟨px, py⟩, hpo, hpx, hpy⟩, rfl⟩
    exact triCurrent_mem_cycleSpace v₀ px py hpx hpy (ne_of_lt hpo)

/-- **The chord basis**: the fundamental triangle currents through `v₀`,
    indexed by ordered chords, form a basis of the cycle space. -/
def chordBasis (v₀ : V) : Module.Basis (Chord v₀) ℝ (cycleSpace (V := V)) :=
  (Module.Basis.span (triCurrent_chord_linearIndependent v₀)).map
    (LinearEquiv.ofEq _ _ (cycleSpace_eq_span v₀).symm)

/-- The dimension of the cycle space is the number of ordered chords. -/
theorem finrank_cycleSpace_eq_card_chord (v₀ : V) :
    Module.finrank ℝ (cycleSpace (V := V)) = Fintype.card (Chord v₀) :=
  Module.finrank_eq_card_basis (chordBasis v₀)

/-! ## §4. Counting the chords -/

/-- Ordered chords count half the off-diagonal pairs of `V \ {v₀}`:
    `2·#Chord = (n−1)(n−2)`, division-free via the swap involution. -/
theorem two_mul_card_chord (v₀ : V) :
    2 * Fintype.card (Chord v₀)
      = (Fintype.card V - 1) * (Fintype.card V - 2) := by
  classical
  have hcard : Fintype.card (Chord v₀)
      = (Finset.univ.filter fun p : V × V =>
          p.1 < p.2 ∧ p.1 ≠ v₀ ∧ p.2 ≠ v₀).card := by
    unfold Chord
    exact Fintype.card_subtype _
  -- descending chords are the swap-image of ascending ones
  have himg : (Finset.univ.filter fun p : V × V =>
        p.2 < p.1 ∧ p.1 ≠ v₀ ∧ p.2 ≠ v₀)
      = (Finset.univ.filter fun p : V × V =>
          p.1 < p.2 ∧ p.1 ≠ v₀ ∧ p.2 ≠ v₀).image Prod.swap := by
    ext ⟨a, b⟩
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
    constructor
    · rintro ⟨hlt, h1, h2⟩
      exact ⟨b, a, ⟨hlt, h2, h1⟩, rfl, rfl⟩
    · rintro ⟨x, y, ⟨hxy, hx, hy⟩, rfl, rfl⟩
      exact ⟨hxy, hy, hx⟩
  have hswap : (Finset.univ.filter fun p : V × V =>
        p.1 < p.2 ∧ p.1 ≠ v₀ ∧ p.2 ≠ v₀).card
      = (Finset.univ.filter fun p : V × V =>
          p.2 < p.1 ∧ p.1 ≠ v₀ ∧ p.2 ≠ v₀).card := by
    rw [himg, Finset.card_image_of_injective _ Prod.swap_injective]
  -- ascending ∪ descending = off-diagonal pairs of the punctured vertex set
  have hunion : (Finset.univ.filter fun p : V × V =>
        p.1 < p.2 ∧ p.1 ≠ v₀ ∧ p.2 ≠ v₀)
      ∪ (Finset.univ.filter fun p : V × V =>
          p.2 < p.1 ∧ p.1 ≠ v₀ ∧ p.2 ≠ v₀)
      = (Finset.univ.erase v₀).offDiag := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_offDiag, Finset.mem_erase, and_true]
    constructor
    · rintro (⟨hlt, h1, h2⟩ | ⟨hgt, h1, h2⟩)
      · exact ⟨h1, h2, ne_of_lt hlt⟩
      · exact ⟨h1, h2, ne_of_gt hgt⟩
    · rintro ⟨h1, h2, hne⟩
      rcases hne.lt_or_gt with hlt | hgt
      · exact Or.inl ⟨hlt, h1, h2⟩
      · exact Or.inr ⟨hgt, h1, h2⟩
  have hdisj : Disjoint
      (Finset.univ.filter fun p : V × V =>
        p.1 < p.2 ∧ p.1 ≠ v₀ ∧ p.2 ≠ v₀)
      (Finset.univ.filter fun p : V × V =>
        p.2 < p.1 ∧ p.1 ≠ v₀ ∧ p.2 ≠ v₀) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [Finset.mem_filter] at hp hq
    exact absurd (hp.2.1.trans hq.2.1) (lt_irrefl _)
  have hoff : (Finset.univ.erase v₀).offDiag.card
      = (Fintype.card V - 1) * (Fintype.card V - 1) - (Fintype.card V - 1) := by
    rw [Finset.offDiag_card, Finset.card_erase_of_mem (Finset.mem_univ v₀),
      Finset.card_univ]
  have hsq : ∀ m : ℕ, m * m - m = m * (m - 1) := by
    intro m
    cases m with
    | zero => rfl
    | succ k => rw [Nat.succ_sub_one, Nat.mul_succ, Nat.add_sub_cancel]
  have hfinal : (Fintype.card V - 1) * (Fintype.card V - 1) - (Fintype.card V - 1)
      = (Fintype.card V - 1) * (Fintype.card V - 2) := by
    rw [show Fintype.card V - 2 = (Fintype.card V - 1) - 1 from by omega]
    exact hsq _
  calc 2 * Fintype.card (Chord v₀)
      = (Finset.univ.filter fun p : V × V =>
          p.1 < p.2 ∧ p.1 ≠ v₀ ∧ p.2 ≠ v₀).card
        + (Finset.univ.filter fun p : V × V =>
            p.2 < p.1 ∧ p.1 ≠ v₀ ∧ p.2 ≠ v₀).card := by
        rw [hcard, two_mul, hswap]
    _ = ((Finset.univ.filter fun p : V × V =>
          p.1 < p.2 ∧ p.1 ≠ v₀ ∧ p.2 ≠ v₀)
        ∪ (Finset.univ.filter fun p : V × V =>
            p.2 < p.1 ∧ p.1 ≠ v₀ ∧ p.2 ≠ v₀)).card :=
        (Finset.card_union_of_disjoint hdisj).symm
    _ = (Finset.univ.erase v₀).offDiag.card := by rw [hunion]
    _ = (Fintype.card V - 1) * (Fintype.card V - 1) - (Fintype.card V - 1) := hoff
    _ = (Fintype.card V - 1) * (Fintype.card V - 2) := hfinal

/-- **The dimension of the NESS landscape** (headline, division-free):
    twice the dimension of the cycle space is `(n−1)(n−2)` — the affinity
    data of Phases E/F has exactly `(n−1)(n−2)/2` free parameters, the first
    Betti number of the complete graph on `n` vertices. -/
theorem two_mul_finrank_cycleSpace (v₀ : V) :
    2 * Module.finrank ℝ (cycleSpace (V := V))
      = (Fintype.card V - 1) * (Fintype.card V - 2) := by
  rw [finrank_cycleSpace_eq_card_chord v₀, two_mul_card_chord v₀]

end SGC.Bridge.SchnakenbergSpan
