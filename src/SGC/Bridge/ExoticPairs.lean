/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Bridge.DiscreteFluidDynamics

/-!
# Exotic Pairs: the coarse face does not determine the fine invariant

The discrete shadow of the exotic-ℝ⁴ phenomenon, at the finite Markov-generator
layer. In dimension 4, a topological manifold can carry many inequivalent smooth
structures: pairs that are **homeomorphic but not diffeomorphic**, distinguished
only by curvature-built invariants (Donaldson, Seiberg–Witten). This module proves
the precise SGC analogue: pairs of generators that are **coarse-isomorphic but
fine-inequivalent** — identical quotient generator, yet distinguished by the
discrete Chern–Hamilton energy `KillingDefect` (`DiscreteFluidDynamics` §7),
which vanishes on one member and is strictly positive on the other.

## The Dictionary (continuum ↔ discrete; analogy, NOT formalized)

| Smooth 4D topology / QFT              | Discrete (this module)                             |
|---------------------------------------|-----------------------------------------------------|
| homeomorphism type (Freedman)         | `QuotientGeneratorSimple` (coarse face)             |
| smooth structure                      | the fine generator itself                           |
| exotic pair (std ℝ⁴, exotic ℝ⁴)       | (`uniformLift M`, `exoticLift M w₀ δ`)              |
| curvature invariant (Donaldson/SW)    | `KillingDefect` = discrete Chern–Hamilton energy    |
| Sasakian leg (K = 0, [MPSS])          | `killingDefect_uniformLift_zero`                    |
| Anosov/NESS leg (K > 0, [MPSS])       | `killingDefect_exoticLift_pos`                      |
| exoticness invisible to topology      | `exoticLift_coarse_current_zero`                    |

## What is actually proved

For EVERY coarse model `M` reversible w.r.t. a positive `πW`, the two fine
completions on `W × ZMod 3`

  `L₁ = uniformLift M`   and   `L₂ = uniformLift M + fiberCycle w₀ δ`   (δ > 0)

satisfy: (a) identical `QuotientGeneratorSimple`, both strongly lumpable, both
realizing `M` exactly (`exoticLift_same_quotient`, `exoticLift_quotient_realizes`);
(b) `KillingDefect L₁ = 0` while `KillingDefect L₂ > 0`; and (c) the coarse
probability current of `L₂` vanishes identically — the handle's circulation is
strictly hidden from the quotient. So the coarse face can NEVER determine the
fine irreversibility invariant: the defect is strictly finer-than-coarse data,
exactly as smooth structure is strictly finer than homeomorphism type in d = 4.
Combined with `reversible_quotient_of_reversible` (equilibrium is hereditary
downward), the asymmetry is one-way: fine NESS can hide under coarse equilibrium,
but coarse NESS never admits a reversible fine completion.

## Consequence for the annealing experiment (design constraint, not a theorem)

An annealer free to modify all rates while preserving only the coarse face CAN
always reach `K = 0` — take the `uniformLift` member. Topological *protection*
of `K > 0` therefore requires a conserved fine-scale class datum; the natural
candidate is the cycle affinity (Kolmogorov holonomy of the log-rate connection,
the discrete Wilson loop). Formalizing affinity classes is the queued follow-up;
without such a constraint the "exotic lattice cannot be annealed" hypothesis is
falsifiable by construction.

## Epistemic state

Every declaration below is kernel-proven (no sorries, no new axioms). No smooth
4-manifold topology, gauge theory, or supersymmetric QFT is formalized (Mathlib
has none), and no claim is made that SGC defects ARE smooth-structure invariants
of actual 4-manifolds. Chern–Hamilton anchor: arXiv:2311.15833 as in
`DiscreteFluidDynamics` §7.
-/

noncomputable section

namespace SGC.Bridge.ExoticPairs

open Finset Matrix
open SGC.Thermodynamics
open SGC.Bridge.DiscreteFluidDynamics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## §1. Block-neutral perturbations: surgery the quotient cannot see -/

/-- A perturbation is block-neutral for `P` if all its block row sums vanish —
    it moves rates around inside fibers without changing any block flux. -/
def BlockNeutral (Δ : Matrix V V ℝ) (P : Partition V) : Prop :=
  ∀ i B, row_sum_block Δ P i B = 0

/-- Block row sums are additive. -/
lemma row_sum_block_add (A B : Matrix V V ℝ) (P : Partition V) (i : V) (Bq : P.Quot) :
    row_sum_block (A + B) P i Bq = row_sum_block A P i Bq + row_sum_block B P i Bq := by
  unfold row_sum_block
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : P.quot_map k = Bq <;> simp [h]

/-- Adding a block-neutral perturbation preserves strong lumpability. -/
theorem stronglyLumpable_add_blockNeutral {L Δ : Matrix V V ℝ} {P : Partition V}
    (hL : IsStronglyLumpable L P) (hΔ : BlockNeutral Δ P) :
    IsStronglyLumpable (L + Δ) P := by
  intro x y hxy B
  show row_sum_block (L + Δ) P x B = row_sum_block (L + Δ) P y B
  rw [row_sum_block_add, row_sum_block_add, hΔ x B, hΔ y B, add_zero, add_zero]
  exact hL x y hxy B

/-- **Coarse blindness**: a block-neutral perturbation leaves the quotient
    generator literally unchanged — no hypothesis on `L` needed. -/
theorem quotientGenerator_add_blockNeutral (L Δ : Matrix V V ℝ) (P : Partition V)
    (hΔ : BlockNeutral Δ P) :
    QuotientGeneratorSimple (L + Δ) P = QuotientGeneratorSimple L P := by
  funext A B
  show row_sum_block (L + Δ) P (Quotient.out A) B
      = row_sum_block L P (Quotient.out A) B
  rw [row_sum_block_add, hΔ (Quotient.out A) B, add_zero]

/-- Probability currents add. -/
lemma current_add (L Δ : Matrix V V ℝ) (pi_dist : V → ℝ) (x y : V) :
    ProbabilityCurrent (L + Δ) pi_dist x y
      = ProbabilityCurrent L pi_dist x y + ProbabilityCurrent Δ pi_dist x y := by
  simp only [ProbabilityCurrent, Matrix.add_apply]
  ring

/-- Currents are antisymmetric. -/
lemma current_antisymm (L : Matrix V V ℝ) (pi_dist : V → ℝ) (x y : V) :
    ProbabilityCurrent L pi_dist x y = -ProbabilityCurrent L pi_dist y x := by
  simp only [ProbabilityCurrent]
  ring

/-! ## §2. The fiber cycle: a hidden handle inside one block -/

variable (W : Type*) [Fintype W] [DecidableEq W]

/-- The hidden handle: a `δ`-weighted directed 3-cycle in the fiber over the base
    point `w₀`, with compensating diagonal. All action is intra-block. -/
def fiberCycle (w₀ : W) (δ : ℝ) : Matrix (W × ZMod 3) (W × ZMod 3) ℝ :=
  fun p q => (if p.1 = w₀ ∧ q = (w₀, p.2 + 1) then δ else 0)
           - (if p.1 = w₀ ∧ q = p then δ else 0)

/-- The fiber cycle is conservative: zero row sums. -/
lemma fiberCycle_row_sum_zero (w₀ : W) (δ : ℝ) (p : W × ZMod 3) :
    ∑ q, fiberCycle W w₀ δ p q = 0 := by
  unfold fiberCycle
  rw [Finset.sum_sub_distrib]
  by_cases hp : p.1 = w₀
  · simp only [hp, true_and]
    rw [Finset.sum_ite_eq' Finset.univ ((w₀, p.2 + 1) : W × ZMod 3) (fun _ => δ),
        Finset.sum_ite_eq' Finset.univ p (fun _ => δ)]
    simp
  · simp only [hp, false_and, if_false]
    simp

/-- The fiber cycle is block-neutral for the fiber partition. -/
lemma fiberCycle_blockNeutral (w₀ : W) (δ : ℝ) :
    BlockNeutral (fiberCycle W w₀ δ) (fiberPartition W (ZMod 3)) := by
  intro p B
  unfold row_sum_block
  by_cases hp : p.1 = w₀
  · have hsplit : ∀ q : W × ZMod 3,
        (if (fiberPartition W (ZMod 3)).quot_map q = B then fiberCycle W w₀ δ p q else 0)
        = (if q = (w₀, p.2 + 1)
            then (if (fiberPartition W (ZMod 3)).quot_map q = B then δ else 0) else 0)
        - (if q = p
            then (if (fiberPartition W (ZMod 3)).quot_map q = B then δ else 0) else 0) := by
      intro q
      unfold fiberCycle
      simp only [hp, true_and]
      split_ifs <;> ring
    simp_rw [hsplit]
    rw [Finset.sum_sub_distrib,
        Finset.sum_ite_eq' Finset.univ ((w₀, p.2 + 1) : W × ZMod 3)
          (fun q => if (fiberPartition W (ZMod 3)).quot_map q = B then δ else 0),
        Finset.sum_ite_eq' Finset.univ p
          (fun q => if (fiberPartition W (ZMod 3)).quot_map q = B then δ else 0)]
    have hsame : (fiberPartition W (ZMod 3)).quot_map ((w₀, p.2 + 1) : W × ZMod 3)
        = (fiberPartition W (ZMod 3)).quot_map p := by
      apply Quotient.sound
      show ((w₀, p.2 + 1) : W × ZMod 3).1 = p.1
      simp [hp]
    simp [hsame]
  · have hzero : ∀ q : W × ZMod 3, fiberCycle W w₀ δ p q = 0 := by
      intro q
      unfold fiberCycle
      simp [hp]
    simp_rw [hzero]
    simp

/-- The fiber cycle is supported inside the block over `w₀`. -/
lemma fiberCycle_intra_block (w₀ : W) (δ : ℝ) (p q : W × ZMod 3)
    (h : fiberCycle W w₀ δ p q ≠ 0) : p.1 = w₀ ∧ q.1 = w₀ := by
  unfold fiberCycle at h
  by_cases hp : p.1 = w₀
  · refine ⟨hp, ?_⟩
    by_cases h1 : q = (w₀, p.2 + 1)
    · rw [h1]
    · by_cases h2 : q = p
      · rw [h2]; exact hp
      · exfalso; apply h; simp [h1, h2]
  · exfalso; apply h; simp [hp]

/-! ## §3. The exotic pair -/

variable {W}

/-- The exotic completion: the uniform (reversible) lift of `M` plus the hidden
    fiber handle. Same coarse face as `uniformLift M`; different fine invariant. -/
def exoticLift (M : Matrix W W ℝ) (w₀ : W) (δ : ℝ) :
    Matrix (W × ZMod 3) (W × ZMod 3) ℝ :=
  uniformLift W (ZMod 3) M + fiberCycle W w₀ δ

/-- The lifted measure shared by both members of the pair. -/
def liftedMeasure (πW : W → ℝ) : W × ZMod 3 → ℝ :=
  fun r => πW r.1 / (Fintype.card (ZMod 3) : ℝ)

lemma liftedMeasure_pos (πW : W → ℝ) (hπW : ∀ w, 0 < πW w) (v : W × ZMod 3) :
    0 < liftedMeasure πW v := by
  have hcard : (0 : ℝ) < (Fintype.card (ZMod 3) : ℝ) := by
    have h3 : Fintype.card (ZMod 3) = 3 := by decide
    rw [h3]; norm_num
  exact div_pos (hπW v.1) hcard

/-- **Coarse isomorphism (a)**: the exotic lift has literally the same quotient
    generator as the uniform lift. -/
theorem exoticLift_same_quotient (M : Matrix W W ℝ) (w₀ : W) (δ : ℝ) :
    QuotientGeneratorSimple (exoticLift M w₀ δ) (fiberPartition W (ZMod 3))
      = QuotientGeneratorSimple (uniformLift W (ZMod 3) M) (fiberPartition W (ZMod 3)) :=
  quotientGenerator_add_blockNeutral _ _ _ (fiberCycle_blockNeutral W w₀ δ)

/-- **Coarse isomorphism (b)**: the exotic lift is strongly lumpable — flexibility
    squared: every reversible coarse model admits an irreversible exact completion. -/
theorem exoticLift_stronglyLumpable (M : Matrix W W ℝ) (w₀ : W) (δ : ℝ) :
    IsStronglyLumpable (exoticLift M w₀ δ) (fiberPartition W (ZMod 3)) :=
  stronglyLumpable_add_blockNeutral (uniformLift_stronglyLumpable W (ZMod 3) M)
    (fiberCycle_blockNeutral W w₀ δ)

/-- **Coarse isomorphism (c)**: the exotic lift realizes the SAME coarse model `M`. -/
theorem exoticLift_quotient_realizes (M : Matrix W W ℝ) (w₀ : W) (δ : ℝ)
    (w w' : W) (f f' : ZMod 3) :
    QuotientGeneratorSimple (exoticLift M w₀ δ) (fiberPartition W (ZMod 3))
      ((fiberPartition W (ZMod 3)).quot_map (w, f))
      ((fiberPartition W (ZMod 3)).quot_map (w', f'))
      = M w w' := by
  rw [exoticLift_same_quotient]
  exact uniformLift_quotient_realizes W (ZMod 3) M w w' f f'

/-! ## §4. Fine inequivalence: the Chern–Hamilton invariant separates the pair -/

/-- Detailed balance lifts through the uniform lift. -/
lemma uniformLift_detailedBalance (M : Matrix W W ℝ) (πW : W → ℝ)
    (hdb : DetailedBalance M πW) :
    DetailedBalance (uniformLift W (ZMod 3) M) (liftedMeasure πW) := by
  intro p q
  simp only [uniformLift, liftedMeasure]
  have h := hdb p.1 q.1
  field_simp
  linarith [h]

/-- **Sasakian leg (K = 0)**: the uniform lift sits at Chern–Hamilton criticality. -/
theorem killingDefect_uniformLift_zero (M : Matrix W W ℝ) (πW : W → ℝ)
    (hdb : DetailedBalance M πW) :
    KillingDefect (uniformLift W (ZMod 3) M) (liftedMeasure πW) = 0 :=
  (killingDefect_eq_zero_iff_reversible _ _).mpr
    (uniformLift_detailedBalance M πW hdb)

/-- **Anosov/NESS leg (K > 0)**: the exotic lift has strictly positive Killing
    defect — the handle breaks detailed balance on the edge `(w₀,0) → (w₀,1)`. -/
theorem killingDefect_exoticLift_pos (M : Matrix W W ℝ) (πW : W → ℝ) (w₀ : W)
    {δ : ℝ} (hδ : 0 < δ) (hπW : ∀ w, 0 < πW w) :
    0 < KillingDefect (exoticLift M w₀ δ) (liftedMeasure πW) := by
  rcases lt_or_eq_of_le (killingDefect_nonneg (exoticLift M w₀ δ) (liftedMeasure πW))
    with h | h
  · exact h
  · exfalso
    have hdb := (killingDefect_eq_zero_iff_reversible _ _).mp h.symm
    -- evaluate the handle on the edge (w₀,0) → (w₀,1) and its reverse
    have hfwd : fiberCycle W w₀ δ (w₀, (0 : ZMod 3)) (w₀, (1 : ZMod 3)) = δ := by
      unfold fiberCycle
      have e1 : ((w₀, (1 : ZMod 3)) : W × ZMod 3)
          = (w₀, ((w₀, (0 : ZMod 3)) : W × ZMod 3).2 + 1) := by
        norm_num
      rw [if_pos ⟨rfl, e1⟩, if_neg]
      · ring
      · rintro ⟨-, hc⟩
        have h2 : (1 : ZMod 3) = 0 := congrArg Prod.snd hc
        exact absurd h2 (by decide)
    have hbwd : fiberCycle W w₀ δ (w₀, (1 : ZMod 3)) (w₀, (0 : ZMod 3)) = 0 := by
      unfold fiberCycle
      rw [if_neg, if_neg]
      · ring
      · rintro ⟨-, hc⟩
        have h2 : (0 : ZMod 3) = 1 := congrArg Prod.snd hc
        exact absurd h2 (by decide)
      · rintro ⟨-, hc⟩
        have h2 : (0 : ZMod 3) = 1 + 1 := congrArg Prod.snd hc
        exact absurd h2 (by decide)
    have hedge := hdb (w₀, (0 : ZMod 3)) (w₀, (1 : ZMod 3))
    unfold exoticLift at hedge
    simp only [Matrix.add_apply] at hedge
    rw [hfwd, hbwd] at hedge
    -- transport along definitional equality of the symmetric entries
    have hedge' : liftedMeasure πW ((w₀, (0 : ZMod 3)) : W × ZMod 3)
          * (uniformLift W (ZMod 3) M ((w₀, (0 : ZMod 3)) : W × ZMod 3)
              ((w₀, (1 : ZMod 3)) : W × ZMod 3) + δ)
        = liftedMeasure πW ((w₀, (0 : ZMod 3)) : W × ZMod 3)
          * (uniformLift W (ZMod 3) M ((w₀, (0 : ZMod 3)) : W × ZMod 3)
              ((w₀, (1 : ZMod 3)) : W × ZMod 3) + 0) := hedge
    have hkey : liftedMeasure πW ((w₀, (0 : ZMod 3)) : W × ZMod 3) * δ = 0 := by
      linear_combination hedge'
    exact absurd hkey
      (ne_of_gt (mul_pos (liftedMeasure_pos πW hπW (w₀, (0 : ZMod 3))) hδ))

/-! ## §5. Invisibility: the hidden current casts no coarse shadow -/

/-- **Invisibility (d)**: the coarse probability current of the exotic lift
    vanishes identically — the handle's persistent circulation is strictly hidden
    from the quotient. Blockwise aggregation + intra-block support + antisymmetry. -/
theorem exoticLift_coarse_current_zero (M : Matrix W W ℝ) (πW : W → ℝ) (w₀ : W)
    (δ : ℝ) (hdb : DetailedBalance M πW) (hπW : ∀ w, 0 < πW w)
    (A B : (fiberPartition W (ZMod 3)).Quot) :
    ProbabilityCurrent
      (CoarseGenerator (exoticLift M w₀ δ) (fiberPartition W (ZMod 3))
        (liftedMeasure πW))
      (pi_bar (fiberPartition W (ZMod 3)) (liftedMeasure πW)) A B = 0 := by
  rw [coarse_current_eq_sum_fine _ _ _ (liftedMeasure_pos πW hπW) A B]
  have hJ1 : ∀ x y : W × ZMod 3,
      ProbabilityCurrent (uniformLift W (ZMod 3) M) (liftedMeasure πW) x y = 0 :=
    (current_zero_iff_reversible _ _).mpr (uniformLift_detailedBalance M πW hdb)
  have hJsplit : ∀ x y : W × ZMod 3,
      ProbabilityCurrent (exoticLift M w₀ δ) (liftedMeasure πW) x y
        = ProbabilityCurrent (fiberCycle W w₀ δ) (liftedMeasure πW) x y := by
    intro x y
    unfold exoticLift
    rw [current_add, hJ1 x y, zero_add]
  simp_rw [hJsplit]
  have hsupp : ∀ x y : W × ZMod 3,
      ProbabilityCurrent (fiberCycle W w₀ δ) (liftedMeasure πW) x y ≠ 0 →
        x.1 = w₀ ∧ y.1 = w₀ := by
    intro x y h
    by_cases hxy : fiberCycle W w₀ δ x y = 0
    · by_cases hyx : fiberCycle W w₀ δ y x = 0
      · exfalso; apply h; simp [ProbabilityCurrent, hxy, hyx]
      · have hib := fiberCycle_intra_block W w₀ δ y x hyx
        exact ⟨hib.2, hib.1⟩
    · exact fiberCycle_intra_block W w₀ δ x y hxy
  by_cases hAB : A = B
  · subst hAB
    have hflip : (∑ x : W × ZMod 3, ∑ y : W × ZMod 3,
        (if (fiberPartition W (ZMod 3)).quot_map x = A
            ∧ (fiberPartition W (ZMod 3)).quot_map y = A
          then ProbabilityCurrent (fiberCycle W w₀ δ) (liftedMeasure πW) x y else 0))
        = -(∑ x : W × ZMod 3, ∑ y : W × ZMod 3,
        (if (fiberPartition W (ZMod 3)).quot_map x = A
            ∧ (fiberPartition W (ZMod 3)).quot_map y = A
          then ProbabilityCurrent (fiberCycle W w₀ δ) (liftedMeasure πW) x y else 0)) := by
      conv_lhs => rw [Finset.sum_comm]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : (fiberPartition W (ZMod 3)).quot_map x = A <;>
        by_cases hy : (fiberPartition W (ZMod 3)).quot_map y = A <;>
          simp [hx, hy, current_antisymm (fiberCycle W w₀ δ) (liftedMeasure πW) y x]
    linarith [hflip]
  · refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
    by_cases hcond : (fiberPartition W (ZMod 3)).quot_map x = A
        ∧ (fiberPartition W (ZMod 3)).quot_map y = B
    · rw [if_pos hcond]
      by_contra hne
      obtain ⟨hx, hy⟩ := hsupp x y hne
      apply hAB
      rw [← hcond.1, ← hcond.2]
      apply Quotient.sound
      show x.1 = y.1
      rw [hx, hy]
    · rw [if_neg hcond]

/-! Queued: shared stationarity (`fiberCycle_stationary`) and the explicit
    positive-current cycle via `killingDefect_pos_iff_positive_current_cycle`;
    the K > 0 leg already certifies the NESS invariant. Affinity classes
    (Kolmogorov holonomy) and the protection theorem are the next module. -/

end SGC.Bridge.ExoticPairs
