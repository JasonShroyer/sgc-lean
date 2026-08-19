/-
Copyright (c) 2026 Jason Shroyer. All rights reserved.
Released under Apache 2.0 license.
-/
import SGC.Topology.Blanket

/-!
# The Boundary Readout Theorem

Link L1 of the predictive-thermodynamics chain
(`docs/predictive-thermodynamics-chain-design.md`): **the coarse-graining
defect of the particle/environment readout is bounded by the boundary
coupling through the blanket** — and the mechanism is strain, not gain.

## The statement

A blanket partition `V = μ | b | η` with `RespectsBlank L B` (no direct
internal-external coupling) induces the canonical CRH readout: the two-block
partition `{μ ∪ b, η}` ("particle" vs "environment"). For a conservative
generator with nonnegative off-diagonal rates whose boundary throughput is
bounded by `γ` (out through the blanket, and in from the environment), the
readout has row-sum lumpability defect at most `γ`:

`IsRowSumApproxLumpable L (readoutPartition B) γ`  (`boundary_readout_bound`)

Combined with the validity-horizon machinery (`trajectory_closure_bound`,
`T* ~ 1/ε`, `SGC.Bridge.ValidityHorizon` / `SGC.Renormalization.Approximate`)
this is the quantitative form of "the blanket quality controls how long the
boundary readout stays predictive". It discharges the strengthening flagged
in `Blanket.lean`'s `blanket_implies_approx_lumpable` docstring ("a
strengthened version bounding ε by the blanket width is the real content"):
the honest bound is by blanket *throughput*, not width — width enters only
as a factor in the throughput of a bounded-rate blanket.

## Strain, not gain (the mechanism)

The proof identifies the defect source exactly: the external-gain field
`extGain(x) = Σ_{z∈η} L x z` on the particle block. Internal states have
`extGain = 0` (by `RespectsBlank`); blanket states have `extGain ∈ [0, γ]`.
The defect is the **spread** of this field within the block — the strain of
the boundary coupling — not the throughput itself. This is the same
mechanism as `SGC.Geometry.OperatorStrain` (constant rate fields are flat;
inhomogeneity is what curves) and the same reason the shift tower has
maximal throughput and zero defect (`shiftTower_defect_zero`): there, every
state in a block has *equal* gain. In the particle/environment readout the
gain contrast between `μ` (zero) and `b` (positive) is structural, so the
spread equals the maximal blanket throughput — for THIS partition, strain
and gain coincide. `readout_strongly_lumpable_of_zero_gain` records the
calibration: zero throughput ⇒ exact (ε = 0) readout.

## Honest scope

* Row-sum register (`IsRowSumApproxLumpable`), the same register in which
  the shift tower's exactness is stated. The `defect_cost`/`π`-weighted
  register of `OptimalPartition` is a separate (compatible) bookkeeping.
* No claim that the two-block readout is *optimal* — `optimal_partition_exists`
  guarantees the optimum does at least this well.
* No selection dynamics here (L3a) and no dissipation statement (L3b,
  `DissipationFloor`); this module is the input end of the chain only.
-/

namespace SGC.Topology.BoundaryReadout

open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## §1. The canonical readout partition of a blanket -/

/-- The particle/environment equivalence: two states are identified iff they
are on the same side of the environment boundary. -/
def readoutSetoid (B : SGC.BlanketPartition V) : Setoid V where
  r x y := (x ∈ B.external ↔ y ∈ B.external)
  iseqv := ⟨fun _ => Iff.rfl, Iff.symm, Iff.trans⟩

/-- **The canonical CRH readout**: the two-block partition
`{μ ∪ b, η}` ("particle" vs "environment") induced by a blanket. -/
def readoutPartition (B : SGC.BlanketPartition V) : SGC.Partition V where
  rel := readoutSetoid B
  decRel := fun x y =>
    inferInstanceAs (Decidable ((x ∈ B.external) ↔ (y ∈ B.external)))

lemma readout_quot_map_eq_iff (B : SGC.BlanketPartition V) (z : V)
    (b_bar : (readoutPartition B).Quot) :
    (readoutPartition B).quot_map z = b_bar ↔
      ((z ∈ B.external) ↔ (Quotient.out b_bar ∈ B.external)) := by
  constructor
  · intro h
    have hmk : Quotient.mk (readoutPartition B).rel z
        = Quotient.mk (readoutPartition B).rel (Quotient.out b_bar) := by
      rw [Quotient.out_eq]; exact h
    exact Quotient.exact hmk
  · intro h
    show Quotient.mk (readoutPartition B).rel z = b_bar
    rw [← Quotient.out_eq b_bar]
    exact Quotient.sound h

/-! ## §2. The external-gain field and its strain -/

/-- The external gain of a state: its total rate into the environment. The
boundary coupling field whose *spread* (strain) is the readout defect. -/
def extGain (L : Matrix V V ℝ) (B : SGC.BlanketPartition V) (x : V) : ℝ :=
  ∑ z ∈ B.external, L x z

/-- Internal states have zero external gain: the blanket screens them. -/
lemma extGain_internal_eq_zero (L : Matrix V V ℝ) (B : SGC.BlanketPartition V)
    (hL : SGC.RespectsBlank L B) {x : V} (hx : x ∈ B.internal) :
    extGain L B x = 0 :=
  Finset.sum_eq_zero fun z hz => hL.1 x hx z hz

/-- For a particle state (not external), the external gain lies in `[0, γ]`
whenever off-diagonal rates are nonnegative and blanket throughput is
bounded by `γ`. -/
lemma extGain_mem_Icc_of_not_external (L : Matrix V V ℝ)
    (B : SGC.BlanketPartition V) (hL : SGC.RespectsBlank L B)
    (hnn : ∀ x z, x ≠ z → 0 ≤ L x z) {γ : ℝ} (hγ : 0 ≤ γ)
    (hout : ∀ u ∈ B.blanket, ∑ z ∈ B.external, L u z ≤ γ)
    {x : V} (hx : x ∉ B.external) :
    0 ≤ extGain L B x ∧ extGain L B x ≤ γ := by
  have hnn_sum : 0 ≤ extGain L B x :=
    Finset.sum_nonneg fun z hz =>
      hnn x z (fun h => hx (h ▸ hz))
  have hAB : x ∈ B.internal ∪ B.blanket := by
    have hcov := B.cover
    have huniv : x ∈ (B.internal ∪ B.blanket ∪ B.external) := by
      rw [hcov]; exact Finset.mem_univ x
    rcases Finset.mem_union.mp huniv with h | h
    · exact h
    · exact absurd h hx
  rcases Finset.mem_union.mp hAB with hint | hbl
  · exact ⟨hnn_sum, by rw [extGain_internal_eq_zero L B hL hint]; exact hγ⟩
  · exact ⟨hnn_sum, hout x hbl⟩

/-- For an environment state, the external gain equals minus its blanket
inflow (conservativity + screening), hence lies in `[-γ, 0]`. -/
lemma extGain_mem_Icc_of_external (L : Matrix V V ℝ)
    (B : SGC.BlanketPartition V) (hL : SGC.RespectsBlank L B)
    (hcons : ∀ x, ∑ z, L x z = 0)
    (hnn : ∀ x z, x ≠ z → 0 ≤ L x z) {γ : ℝ}
    (hin : ∀ e ∈ B.external, ∑ u ∈ B.blanket, L e u ≤ γ)
    {x : V} (hx : x ∈ B.external) :
    -γ ≤ extGain L B x ∧ extGain L B x ≤ 0 := by
  -- split the conservative row over the cover
  have hsplit : extGain L B x
      = -(∑ z ∈ B.internal, L x z + ∑ z ∈ B.blanket, L x z) := by
    have hcov : (B.internal ∪ B.blanket) ∪ B.external = Finset.univ := B.cover
    have hdisj : Disjoint (B.internal ∪ B.blanket) B.external :=
      Finset.disjoint_union_left.mpr ⟨B.disjoint_ie, B.disjoint_be⟩
    have hrow := hcons x
    rw [← hcov, Finset.sum_union hdisj,
      Finset.sum_union B.disjoint_ib] at hrow
    unfold extGain
    linarith
  have hint_zero : (∑ z ∈ B.internal, L x z) = 0 :=
    Finset.sum_eq_zero fun z hz => hL.2 x hx z hz
  have hbl_nonneg : 0 ≤ ∑ z ∈ B.blanket, L x z :=
    Finset.sum_nonneg fun z hz =>
      hnn x z (fun h => (Finset.disjoint_left.mp B.disjoint_be (h ▸ hz)) hx)
  have hbl_le : (∑ z ∈ B.blanket, L x z) ≤ γ := hin x hx
  constructor
  · rw [hsplit, hint_zero]; linarith
  · rw [hsplit, hint_zero]; linarith

/-- **The strain bound on the gain field**: any two states on the same side
of the boundary have external gains within `γ` of each other. -/
lemma extGain_strain_le (L : Matrix V V ℝ) (B : SGC.BlanketPartition V)
    (hL : SGC.RespectsBlank L B)
    (hcons : ∀ x, ∑ z, L x z = 0)
    (hnn : ∀ x z, x ≠ z → 0 ≤ L x z) {γ : ℝ} (hγ : 0 ≤ γ)
    (hout : ∀ u ∈ B.blanket, ∑ z ∈ B.external, L u z ≤ γ)
    (hin : ∀ e ∈ B.external, ∑ u ∈ B.blanket, L e u ≤ γ)
    {x y : V} (hxy : (x ∈ B.external) ↔ (y ∈ B.external)) :
    |extGain L B x - extGain L B y| ≤ γ := by
  by_cases hx : x ∈ B.external
  · have hy := hxy.mp hx
    obtain ⟨h1, h2⟩ := extGain_mem_Icc_of_external L B hL hcons hnn hin hx
    obtain ⟨h3, h4⟩ := extGain_mem_Icc_of_external L B hL hcons hnn hin hy
    rw [abs_le]; constructor <;> linarith
  · have hy : y ∉ B.external := fun h => hx (hxy.mpr h)
    obtain ⟨h1, h2⟩ := extGain_mem_Icc_of_not_external L B hL hnn hγ hout hx
    obtain ⟨h3, h4⟩ := extGain_mem_Icc_of_not_external L B hL hnn hγ hout hy
    rw [abs_le]; constructor <;> linarith

/-! ## §3. The Boundary Readout Theorem -/

/-- Block row sums of the readout are `±extGain` up to a constant: the sum
into the environment block is `extGain`, the sum into the particle block is
`-extGain` (conservativity). -/
lemma readout_block_sum_eq (L : Matrix V V ℝ) (B : SGC.BlanketPartition V)
    (hcons : ∀ x, ∑ z, L x z = 0) (x : V)
    (b_bar : (readoutPartition B).Quot) :
    (∑ z : V, if (readoutPartition B).quot_map z = b_bar then L x z else 0)
      = if Quotient.out b_bar ∈ B.external then extGain L B x
        else -extGain L B x := by
  by_cases hb : Quotient.out b_bar ∈ B.external
  · rw [if_pos hb]
    have hmem : ∀ z : V, ((readoutPartition B).quot_map z = b_bar) ↔ z ∈ B.external := by
      intro z
      rw [readout_quot_map_eq_iff]
      simp [hb]
    calc (∑ z : V, if (readoutPartition B).quot_map z = b_bar then L x z else 0)
        = ∑ z : V, if z ∈ B.external then L x z else 0 :=
          Finset.sum_congr rfl fun z _ => if_congr (hmem z) rfl rfl
      _ = extGain L B x := by
          rw [Finset.sum_ite_mem, Finset.univ_inter]
          rfl
  · rw [if_neg hb]
    have hmem : ∀ z : V, ((readoutPartition B).quot_map z = b_bar) ↔ z ∉ B.external := by
      intro z
      rw [readout_quot_map_eq_iff]
      simp [hb]
    have hsum : (∑ z : V, if (readoutPartition B).quot_map z = b_bar then L x z else 0)
        = ∑ z : V, if z ∈ B.external then 0 else L x z := by
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [if_congr (hmem z) rfl rfl]
      by_cases hz : z ∈ B.external <;> simp [hz]
    rw [hsum]
    have htotal : (∑ z : V, if z ∈ B.external then L x z else 0)
        + (∑ z : V, if z ∈ B.external then 0 else L x z) = ∑ z : V, L x z := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun z _ => ?_
      by_cases hz : z ∈ B.external <;> simp [hz]
    have hext : (∑ z : V, if z ∈ B.external then L x z else 0) = extGain L B x := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
      rfl
    rw [hcons x, hext] at htotal
    linarith

/-- **THE BOUNDARY READOUT THEOREM (L1).** For a conservative generator with
nonnegative off-diagonal rates that respects a blanket partition, the
canonical particle/environment readout is approximately lumpable with defect
bounded by the boundary throughput `γ`:

strain of the boundary coupling ⟹ coarse-graining defect ≤ γ.

Composed with `T* ~ 1/ε` (`ValidityHorizon`/`Approximate`), the blanket
throughput controls how long "reality as boundary readout" stays faithful. -/
theorem boundary_readout_bound (B : SGC.BlanketPartition V) (L : Matrix V V ℝ)
    (hL : SGC.RespectsBlank L B)
    (hcons : ∀ x, ∑ z, L x z = 0)
    (hnn : ∀ x z, x ≠ z → 0 ≤ L x z)
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hout : ∀ u ∈ B.blanket, ∑ z ∈ B.external, L u z ≤ γ)
    (hin : ∀ e ∈ B.external, ∑ u ∈ B.blanket, L e u ≤ γ) :
    SGC.IsRowSumApproxLumpable L (readoutPartition B) γ := by
  intro x y hxy b_bar
  have hstrain := extGain_strain_le L B hL hcons hnn hγ hout hin
    (hxy : (x ∈ B.external) ↔ (y ∈ B.external))
  rw [readout_block_sum_eq L B hcons x b_bar,
    readout_block_sum_eq L B hcons y b_bar]
  by_cases hb : Quotient.out b_bar ∈ B.external
  · simpa [hb] using hstrain
  · rw [if_neg hb, if_neg hb]
    have : |-(extGain L B x) - -(extGain L B y)| = |extGain L B x - extGain L B y| := by
      rw [← abs_neg]; ring_nf
    rw [this]
    exact hstrain

/-- **Calibration (the ε = 0 pole)**: zero boundary throughput makes the
readout exactly (strongly) lumpable — the sealed-particle limit, mirroring
`shiftTower_stronglyLumpable` (uniform gain) and `cd0_const` (zero strain). -/
theorem readout_strongly_lumpable_of_zero_gain (B : SGC.BlanketPartition V)
    (L : Matrix V V ℝ) (hL : SGC.RespectsBlank L B)
    (hcons : ∀ x, ∑ z, L x z = 0)
    (hnn : ∀ x z, x ≠ z → 0 ≤ L x z)
    (hout : ∀ u ∈ B.blanket, ∑ z ∈ B.external, L u z ≤ 0)
    (hin : ∀ e ∈ B.external, ∑ u ∈ B.blanket, L e u ≤ 0) :
    SGC.IsStronglyLumpable L (readoutPartition B) := by
  have h0 := boundary_readout_bound B L hL hcons hnn le_rfl hout hin
  intro x y hxy b_bar
  have := h0 x y hxy b_bar
  rw [abs_nonpos_iff] at this
  linarith [this]

/-! ## §4. The lower bound: interiority prices the readout (two-sided)

`boundary_readout_bound` says the canonical readout pays AT MOST the
boundary throughput. The theorems below close the other side, answering the
red-team critique (insights/0010, Attack 2) that the price-of-interiority
narrative was formalized in the upper direction only: the defect of the
canonical readout is AT LEAST every blanket state's external gain. The
mechanism is interiority itself — a screened internal state (gain `0`)
sits in the same block as the blanket state (gain `g`), so the row-sum
spread is at least `g`. Together: for a blanket with a nonempty interior,

  max blanket gain ≤ (canonical readout defect) ≤ boundary throughput γ,

and with positive throughput the readout is provably NOT exact
(`not_stronglyLumpable_of_interior_gain`): **to have an inside is to pay —
now as a sandwich, not a slogan.** -/

/-- **The lower bound.** Any tolerance `ε` certified for the canonical
readout dominates every blanket state's external gain — provided the
blanket has something to screen (an internal state) and an environment to
lose to (an external state). -/
theorem boundary_readout_lower_bound (B : SGC.BlanketPartition V)
    (L : Matrix V V ℝ) (hL : SGC.RespectsBlank L B)
    (hcons : ∀ x, ∑ z, L x z = 0)
    {ε : ℝ} (hε : SGC.IsRowSumApproxLumpable L (readoutPartition B) ε)
    {x u e : V} (hx : x ∈ B.internal) (hu : u ∈ B.blanket)
    (he : e ∈ B.external) :
    extGain L B u ≤ ε := by
  have hxne : x ∉ B.external := Finset.disjoint_left.mp B.disjoint_ie hx
  have hune : u ∉ B.external := Finset.disjoint_left.mp B.disjoint_be hu
  have hrel : (u ∈ B.external) ↔ (x ∈ B.external) :=
    iff_of_false hune hxne
  have hkey := hε u x hrel ((readoutPartition B).quot_map e)
  have hout : Quotient.out ((readoutPartition B).quot_map e) ∈ B.external := by
    have hq : (readoutPartition B).quot_map
        (Quotient.out ((readoutPartition B).quot_map e))
        = (readoutPartition B).quot_map e := by
      exact Quotient.out_eq _
    have := (readout_quot_map_eq_iff B
      (Quotient.out ((readoutPartition B).quot_map e))
      ((readoutPartition B).quot_map e)).mp hq
    -- `this : out ∈ ext ↔ out(out-block) ∈ ext`; use the representative `e`
    have he' := (readout_quot_map_eq_iff B e
      ((readoutPartition B).quot_map e)).mp rfl
    exact this.mpr (he'.mp he)
  rw [readout_block_sum_eq L B hcons u, readout_block_sum_eq L B hcons x,
    if_pos hout, if_pos hout] at hkey
  have hx0 : extGain L B x = 0 := extGain_internal_eq_zero L B hL hx
  rw [hx0, sub_zero] at hkey
  exact le_trans (le_abs_self _) hkey

/-- **Interiority prices the readout (the two-sided headline).** A blanket
with a screened interior and strictly positive throughput through any
blanket state admits NO exact canonical readout: the particle/environment
coarse-graining necessarily carries defect at least that gain. The `ε = 0`
pole (`readout_strongly_lumpable_of_zero_gain`) and this theorem are the
two jaws of the sandwich. -/
theorem not_stronglyLumpable_of_interior_gain (B : SGC.BlanketPartition V)
    (L : Matrix V V ℝ) (hL : SGC.RespectsBlank L B)
    (hcons : ∀ x, ∑ z, L x z = 0)
    {x u e : V} (hx : x ∈ B.internal) (hu : u ∈ B.blanket)
    (he : e ∈ B.external)
    (hgain : 0 < extGain L B u) :
    ¬ SGC.IsStronglyLumpable L (readoutPartition B) := by
  intro hstrong
  have h0 : SGC.IsRowSumApproxLumpable L (readoutPartition B) 0 :=
    SGC.strong_implies_approx_zero L _ hstrong
  have := boundary_readout_lower_bound B L hL hcons h0 hx hu he
  linarith

end SGC.Topology.BoundaryReadout
