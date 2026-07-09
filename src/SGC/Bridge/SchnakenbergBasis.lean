/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Bridge.AffinityProtection

/-!
# The Schnakenberg Basis: realizability of affinity charges

Phase F of the exotic-pairs program. Phase E proved the affinity charge is a
conserved obstruction: charged cycles seal the NESS phase against every positive
measure and every charge-conserving anneal. This module proves the CONVERSE
direction of the classification: the charge data is fully REALIZABLE — every
antisymmetric assignment of charges to the fundamental cycles of a star tree is
carried by an explicit generator, with honest (nonnegative off-diagonal,
zero-row-sum) rates.

## The linearization insight

The classical Schnakenberg theory works with log-affinities
`∑ log(L₊/L₋)`, which decouple linearly but are type-theoretic quicksand
(positivity side conditions, `Real.log`). Our Phase E charge
`Q = ∏ L₊ − ∏ L₋` is polynomial — surgeries generically produce CUBIC charge
equations. The resolution: pin every star-tree edge to symmetric rate `1`. Then
the charge of the fundamental triangle `v₀ → x → y → v₀` collapses to

  `Q = 1 · L x y · 1 − 1 · L y x · 1 = L x y − L y x`

— exactly linear in the chord rates. Each triangle contains exactly one chord,
so the realizability equations decouple completely: the chord matrix IS the
charge data. The polynomial Wilson loop, evaluated on a gauge where the tree is
trivialized, becomes the abelianized holonomy — the discrete shadow of choosing
a maximal torus (framing, not formalized).

## What is proved

1. **Geometric layer**: `CycleSpace` is a genuine `Submodule ℝ (V → V → ℝ)` —
   antisymmetric fields in the kernel of the divergence map (`divergenceHom`).
   Membership coincides with the Prop-level `InCycleSpace` of
   `DiscreteFluidDynamics` (`mem_cycleSpace_iff`). The triangle currents
   `triCurrent v₀ x y` lie in it (`triCurrent_mem_cycleSpace`).
2. **Realizability**: `chordGenerator v₀ q` has zero row sums
   (`chordGenerator_row_sum_zero`), nonnegative off-diagonal entries when
   `q ≥ 0` off the star (`chordGenerator_offdiag_nonneg`), and its fundamental
   triangle charges are exactly `q x y − q y x`
   (`chordGenerator_affinityCharge`).
3. **The Schnakenberg realizability theorem** (`schnakenberg_realizability`):
   for EVERY antisymmetric `A : V → V → ℝ` there is a zero-row-sum,
   nonnegative-off-diagonal generator whose fundamental-cycle charges are
   exactly `A x y` — via the positive-part split `q = A⁺`.
4. **Protection closes the loop** (`killingDefect_pos_of_chord_asym`): one
   asymmetric chord in the constructed generator forces `KillingDefect > 0`
   for every positive measure, by Phase E's protection kernel.

## Epistemic state

Every declaration kernel-proven; no sorries, no new axioms. The linear
independence and dimension count `(n−1)(n−2)/2` of the cycle space (the graph
genus / first Betti number) are Phase F2 — deferred, not claimed.
-/

noncomputable section

namespace SGC.Bridge.SchnakenbergBasis

open Finset Matrix
open SGC.Thermodynamics
open SGC.Bridge.DiscreteFluidDynamics
open SGC.Bridge.AffinityProtection

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## §1. The cycle space as a submodule -/

/-- The divergence, packaged as a linear map on edge fields. -/
def divergenceHom : (V → V → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun J := fun x => ∑ y, J x y
  map_add' J K := by funext x; simp [Finset.sum_add_distrib]
  map_smul' c J := by funext x; simp [Finset.mul_sum]

@[simp] lemma divergenceHom_apply (J : V → V → ℝ) (x : V) :
    divergenceHom J x = divergence J x := rfl

/-- Antisymmetric edge fields form a submodule of `V → V → ℝ`. -/
def antisymmetricSubmodule : Submodule ℝ (V → V → ℝ) where
  carrier := {J | ∀ x y, J x y = -J y x}
  add_mem' := fun ha hb x y => by simp only [Pi.add_apply, ha x y, hb x y]; ring
  zero_mem' := fun x y => by simp
  smul_mem' := fun c J hJ x y => by simp only [Pi.smul_apply, smul_eq_mul, hJ x y]; ring

/-- **The cycle space**: antisymmetric, divergence-free edge fields — a genuine
    vector subspace of `V → V → ℝ` (discrete 1-cycles). -/
def cycleSpace : Submodule ℝ (V → V → ℝ) :=
  antisymmetricSubmodule ⊓ LinearMap.ker (divergenceHom (V := V))

/-- Membership in the submodule coincides with the Prop-level cycle-space
    predicate of `DiscreteFluidDynamics` — the two vocabularies agree. -/
lemma mem_cycleSpace_iff (J : V → V → ℝ) :
    J ∈ cycleSpace ↔ InCycleSpace J := by
  constructor
  · rintro ⟨hanti, hker⟩
    exact ⟨hanti, fun x => congrFun (LinearMap.mem_ker.mp hker) x⟩
  · rintro ⟨hanti, hdiv⟩
    exact ⟨hanti, LinearMap.mem_ker.mpr (funext fun x => hdiv x)⟩

/-! ## §2. Edge and triangle currents -/

/-- The elementary current of a directed edge `a → b`: `+1` on `(a,b)`,
    `−1` on `(b,a)`, `0` elsewhere. -/
def edgeCurrent (a b : V) : V → V → ℝ := fun p q =>
  (if p = a ∧ q = b then (1 : ℝ) else 0) - (if p = b ∧ q = a then (1 : ℝ) else 0)

lemma edgeCurrent_antisymm (a b : V) (p q : V) :
    edgeCurrent a b p q = -edgeCurrent a b q p := by
  unfold edgeCurrent
  by_cases h1 : p = a ∧ q = b <;> by_cases h2 : p = b ∧ q = a <;>
    simp [h1, h2, and_comm] <;> ring

/-- Divergence of an elementary edge current on a proper edge: source `+1`,
    target `−1`, zero elsewhere. -/
lemma divergence_edgeCurrent (a b : V) (hab : a ≠ b) (x : V) :
    divergence (edgeCurrent a b) x
      = (if x = a then (1 : ℝ) else 0) - (if x = b then (1 : ℝ) else 0) := by
  unfold divergence edgeCurrent
  rw [Finset.sum_sub_distrib]
  congr 1
  · by_cases hx : x = a
    · subst hx
      rw [Finset.sum_eq_single b]
      · simp
      · intro c _ hc; simp [hc]
      · intro h; exact absurd (Finset.mem_univ b) h
    · rw [Finset.sum_eq_zero (fun c _ => by simp [hx]), if_neg hx]
  · by_cases hx : x = b
    · subst hx
      rw [Finset.sum_eq_single a]
      · simp
      · intro c _ hc; simp [hc]
      · intro h; exact absurd (Finset.mem_univ a) h
    · rw [Finset.sum_eq_zero (fun c _ => by simp [hx]), if_neg hx]

/-- The fundamental triangle current through the base point:
    `v₀ → x → y → v₀`. -/
def triCurrent (v₀ x y : V) : V → V → ℝ :=
  edgeCurrent v₀ x + edgeCurrent x y + edgeCurrent y v₀

/-- **Triangle currents are 1-cycles**: for pairwise distinct vertices the
    triangle current is antisymmetric and divergence-free — the divergences of
    the three edges telescope around the loop. -/
theorem triCurrent_mem_cycleSpace (v₀ x y : V)
    (hx : x ≠ v₀) (hy : y ≠ v₀) (hxy : x ≠ y) :
    triCurrent v₀ x y ∈ cycleSpace := by
  constructor
  · intro p q
    simp only [triCurrent, Pi.add_apply,
      edgeCurrent_antisymm v₀ x p q, edgeCurrent_antisymm x y p q,
      edgeCurrent_antisymm y v₀ p q]
    ring
  · show divergenceHom (triCurrent v₀ x y) = 0
    funext p
    have hsum : divergenceHom (triCurrent v₀ x y) p
        = divergence (edgeCurrent v₀ x) p + divergence (edgeCurrent x y) p
          + divergence (edgeCurrent y v₀) p := by
      simp [triCurrent, divergence, Finset.sum_add_distrib]
    rw [hsum, divergence_edgeCurrent v₀ x (Ne.symm hx),
        divergence_edgeCurrent x y hxy,
        divergence_edgeCurrent y v₀ hy]
    simp only [Pi.zero_apply]
    ring

/-! ## §3. Fundamental cycles of the star tree -/

/-- The fundamental 3-cycle `v₀ → x → y → v₀` through the star center, in the
    ℕ-indexed cycle vocabulary of `AffinityProtection`. -/
def fundCycle (v₀ x y : V) : ℕ → V := fun m =>
  if m % 3 = 0 then v₀ else if m % 3 = 1 then x else y

lemma fundCycle_closed (v₀ x y : V) : fundCycle v₀ x y 0 = fundCycle v₀ x y 3 := rfl

/-! ## §4. The chord generator: linear realization of charge data

Star-tree edges are pinned to symmetric rate `1`; chord `(x, y)` carries rate
`q x y`. Each fundamental triangle contains exactly one chord, so its Phase E
charge is `q x y − q y x` — the realizability equations decouple and are LINEAR,
despite the charge being a polynomial Wilson loop. -/

/-- Off-diagonal rate profile: `1` on star edges, `q` on chords. -/
def offRate (v₀ : V) (q : V → V → ℝ) (a b : V) : ℝ :=
  if a = v₀ ∨ b = v₀ then 1 else q a b

/-- The chord generator: off-diagonal rates `offRate`, diagonal chosen to make
    every row sum vanish. -/
def chordGenerator (v₀ : V) (q : V → V → ℝ) : Matrix V V ℝ := fun a b =>
  if a = b then -∑ c ∈ Finset.univ.erase a, offRate v₀ q a c else offRate v₀ q a b

/-- The chord generator is conservative: zero row sums. -/
theorem chordGenerator_row_sum_zero (v₀ : V) (q : V → V → ℝ) (a : V) :
    ∑ b, chordGenerator v₀ q a b = 0 := by
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ a)]
  have herase : ∑ b ∈ Finset.univ.erase a, chordGenerator v₀ q a b
      = ∑ b ∈ Finset.univ.erase a, offRate v₀ q a b :=
    Finset.sum_congr rfl fun b hb =>
      if_neg fun h => (Finset.mem_erase.mp hb).1 h.symm
  rw [herase, show chordGenerator v₀ q a a
      = -∑ c ∈ Finset.univ.erase a, offRate v₀ q a c from if_pos rfl]
  ring

/-- The chord generator has nonnegative off-diagonal rates whenever the chord
    data does — it is an honest CTMC generator. -/
theorem chordGenerator_offdiag_nonneg (v₀ : V) (q : V → V → ℝ)
    (hq : ∀ a b, a ≠ v₀ → b ≠ v₀ → 0 ≤ q a b) (a b : V) (hab : a ≠ b) :
    0 ≤ chordGenerator v₀ q a b := by
  rw [show chordGenerator v₀ q a b = offRate v₀ q a b from if_neg hab]
  unfold offRate
  split_ifs with h
  · norm_num
  · push_neg at h
    exact hq a b h.1 h.2

/-- **The linearization**: the affinity charge of the fundamental triangle
    `v₀ → x → y → v₀` under the chord generator is exactly the chord
    antisymmetry `q x y − q y x`. The star gauge trivializes the tree; the
    polynomial Wilson loop abelianizes. -/
theorem chordGenerator_affinityCharge (v₀ x y : V)
    (hx : x ≠ v₀) (hy : y ≠ v₀) (hxy : x ≠ y) (q : V → V → ℝ) :
    AffinityCharge (chordGenerator v₀ q) (fundCycle v₀ x y) 3
      = q x y - q y x := by
  have e1 : chordGenerator v₀ q v₀ x = 1 := by
    unfold chordGenerator offRate
    rw [if_neg (Ne.symm hx), if_pos (Or.inl rfl)]
  have e2 : chordGenerator v₀ q x y = q x y := by
    unfold chordGenerator offRate
    rw [if_neg hxy, if_neg fun h => h.elim hx hy]
  have e3 : chordGenerator v₀ q y v₀ = 1 := by
    unfold chordGenerator offRate
    rw [if_neg hy, if_pos (Or.inr rfl)]
  have e4 : chordGenerator v₀ q x v₀ = 1 := by
    unfold chordGenerator offRate
    rw [if_neg hx, if_pos (Or.inr rfl)]
  have e5 : chordGenerator v₀ q y x = q y x := by
    unfold chordGenerator offRate
    rw [if_neg (Ne.symm hxy), if_neg fun h => h.elim hy hx]
  have e6 : chordGenerator v₀ q v₀ y = 1 := by
    unfold chordGenerator offRate
    rw [if_neg (Ne.symm hy), if_pos (Or.inl rfl)]
  unfold AffinityCharge cycleProdFwd cycleProdBwd
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  norm_num [fundCycle]
  rw [e1, e2, e3, e4, e5, e6]
  ring

/-! ## §5. The Schnakenberg realizability theorem -/

/-- **Realizability converse**: EVERY antisymmetric charge assignment
    `A : V → V → ℝ` on the fundamental cycles of the star tree is realized by
    an explicit conservative generator with nonnegative off-diagonal rates —
    via the positive-part chord data `q = A⁺`. Together with Phase E
    (charges are conserved obstructions), this completes the classification:
    the affinity data is exactly the free parameter of the NESS landscape. -/
theorem schnakenberg_realizability (v₀ : V) (A : V → V → ℝ)
    (hA : ∀ a b, A a b = -A b a) :
    ∃ L : Matrix V V ℝ,
      (∀ a, ∑ b, L a b = 0) ∧
      (∀ a b, a ≠ b → 0 ≤ L a b) ∧
      ∀ x y, x ≠ v₀ → y ≠ v₀ → x ≠ y →
        AffinityCharge L (fundCycle v₀ x y) 3 = A x y := by
  refine ⟨chordGenerator v₀ (fun a b => max (A a b) 0),
    chordGenerator_row_sum_zero v₀ _,
    chordGenerator_offdiag_nonneg v₀ _ (fun a b _ _ => le_max_right _ _), ?_⟩
  intro x y hx hy hxy
  rw [chordGenerator_affinityCharge v₀ x y hx hy hxy]
  simp only [hA y x]
  rcases le_total (A x y) 0 with h | h
  · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
    ring
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    ring

/-- **Protection closes the loop**: one asymmetric chord in the realized
    generator forces a strictly positive Killing defect for every positive
    measure — Phase E's kernel applied to the fundamental cycle. -/
theorem killingDefect_pos_of_chord_asym (v₀ x y : V)
    (hx : x ≠ v₀) (hy : y ≠ v₀) (hxy : x ≠ y) (q : V → V → ℝ)
    (hne : q x y ≠ q y x)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) :
    0 < KillingDefect (chordGenerator v₀ q) pi_dist :=
  killingDefect_pos_of_affinityCharge_ne_zero _ _ 3 (fundCycle_closed v₀ x y)
    (by
      rw [chordGenerator_affinityCharge v₀ x y hx hy hxy]
      exact sub_ne_zero.mpr hne) pi_dist hπ

end SGC.Bridge.SchnakenbergBasis
