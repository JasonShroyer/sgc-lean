/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Bridge.ExoticPairs

/-!
# Affinity Protection: the conserved charge that seals the exotic phase

Phase E of the exotic-pairs program. `ExoticPairs` showed the coarse face never
determines the fine invariant (`KillingDefect` 0 vs > 0) — but also that an
annealer preserving only the coarse face CAN always reach `K = 0`. This module
supplies the missing conservation law.

## The charge

For a closed cycle `c : ℕ → V` (with `c 0 = c len`), define the **affinity
charge** `Q(L, c) := ∏ L(cᵢ, cᵢ₊₁) − ∏ L(cᵢ₊₁, cᵢ)` — the division-free form of
Kolmogorov's criterion. On positive rates, `Q ≠ 0` iff the cycle affinity
`∑ log(L₊/L₋) ≠ 0`: the holonomy of the log-rate connection around the loop,
a discrete Wilson loop. `Q` is defined from the generator ALONE — no measure.

## What is proved

1. **Kolmogorov obstruction** (`cycleProd_balance_of_detailedBalance`): detailed
   balance w.r.t. ANY positive measure forces `Q = 0` on EVERY closed cycle —
   reversibility = flat connection.
2. **Protection kernel** (`killingDefect_pos_of_affinityCharge_ne_zero`): one
   charged cycle forces `KillingDefect L π > 0` for EVERY positive `π`. The
   defect's positivity is measure-independent — intrinsic to the generator, as a
   smooth-structure invariant is intrinsic to the manifold, not to a chosen metric.
3. **Annealing protection** (`annealing_protection`): along any path of
   generators conserving the charge of one charged cycle, the defect stays
   strictly positive at every time, for every positive measure. The charge is
   the Noether-style class datum that seals the NESS phase.
4. **Instantiation**: the exotic lift's handle cycle carries charge
   `(a+δ)³ − a³ > 0` (`exoticLift_affinityCharge_pos`), for EVERY base model `M`
   — no reversibility of `M` needed. Hence `killingDefect_exoticLift_pos_universal`:
   the exotic lift is irreversible w.r.t. every positive measure. The uniform
   lift of a reversible base has zero charge on every cycle
   (`uniformLift_affinityCharge_zero`), so the pair lies in DIFFERENT affinity
   classes (`affinity_separates_pair`): no charge-conserving anneal connects them.

## Consequence for the 5090 experiment

The protection theorem upgrades the design constraint of `ExoticPairs` into a
positive statement: annealing WITHIN a fixed affinity class can never kill the
defect. "Exotic-annealing" must therefore be tested with charge-conserving
moves; the charge is the discrete analogue of the conserved holonomy/period
data. (Framing, not formalized: this conserved-holonomy protection is the
SGC shadow of Wilson-loop rigidity; any Langlands-flavored reading — holonomy
classes as the "automorphic" side of a correspondence — is a north star for
future work, NOT a claim of this module.)

## Epistemic state

Every declaration is kernel-proven: no sorries, no new axioms. Cycle vocabulary
matches `DiscreteFluidDynamics` §3 (ℕ-indexed closed walks).
-/

noncomputable section

namespace SGC.Bridge.AffinityProtection

open Finset Matrix
open SGC.Thermodynamics
open SGC.Bridge.DiscreteFluidDynamics
open SGC.Bridge.ExoticPairs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## §1. The affinity charge of a closed cycle -/

/-- Forward rate product around a cycle: `∏_{m < len} L (c m) (c (m+1))`. -/
def cycleProdFwd (L : Matrix V V ℝ) (c : ℕ → V) (len : ℕ) : ℝ :=
  ∏ m ∈ Finset.range len, L (c m) (c (m + 1))

/-- Backward rate product around a cycle: `∏_{m < len} L (c (m+1)) (c m)`. -/
def cycleProdBwd (L : Matrix V V ℝ) (c : ℕ → V) (len : ℕ) : ℝ :=
  ∏ m ∈ Finset.range len, L (c (m + 1)) (c m)

/-- **Affinity charge** (division-free Kolmogorov holonomy / discrete Wilson
    loop): the difference of forward and backward rate products. Defined from
    the generator alone — no measure enters. -/
def AffinityCharge (L : Matrix V V ℝ) (c : ℕ → V) (len : ℕ) : ℝ :=
  cycleProdFwd L c len - cycleProdBwd L c len

/-- Around a closed cycle, the shifted measure product equals the unshifted one. -/
lemma cycle_measure_prod_shift (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (c : ℕ → V) (len : ℕ) (hc : c 0 = c len) :
    ∏ m ∈ Finset.range len, pi_dist (c (m + 1))
      = ∏ m ∈ Finset.range len, pi_dist (c m) := by
  have h := (Finset.prod_range_succ' (fun m => pi_dist (c m)) len).symm.trans
    (Finset.prod_range_succ (fun m => pi_dist (c m)) len)
  rw [hc] at h
  exact mul_right_cancel₀ (ne_of_gt (hπ (c len))) h

/-! ## §2. The Kolmogorov obstruction: reversibility = flat connection -/

/-- **Kolmogorov obstruction**: detailed balance w.r.t. a positive measure forces
    forward and backward rate products to agree on every closed cycle. Proof:
    multiply detailed balance around the loop; the measure telescopes. -/
theorem cycleProd_balance_of_detailedBalance (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (hdb : DetailedBalance L pi_dist)
    (c : ℕ → V) (len : ℕ) (hc : c 0 = c len) :
    cycleProdFwd L c len = cycleProdBwd L c len := by
  unfold cycleProdFwd cycleProdBwd
  have key : ∏ m ∈ Finset.range len, (pi_dist (c m) * L (c m) (c (m + 1)))
      = ∏ m ∈ Finset.range len, (pi_dist (c (m + 1)) * L (c (m + 1)) (c m)) :=
    Finset.prod_congr rfl fun m _ => hdb (c m) (c (m + 1))
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      cycle_measure_prod_shift pi_dist hπ c len hc] at key
  exact mul_left_cancel₀
    (ne_of_gt (Finset.prod_pos fun m _ => hπ (c m))) key

/-- Detailed balance w.r.t. any positive measure kills every affinity charge. -/
theorem affinityCharge_eq_zero_of_detailedBalance (L : Matrix V V ℝ)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (hdb : DetailedBalance L pi_dist)
    (c : ℕ → V) (len : ℕ) (hc : c 0 = c len) :
    AffinityCharge L c len = 0 :=
  sub_eq_zero.mpr (cycleProd_balance_of_detailedBalance L pi_dist hπ hdb c len hc)

/-! ## §3. The protection theorems -/

/-- **Protection kernel (measure-independence)**: ONE charged cycle forces a
    strictly positive Killing defect for EVERY positive measure. The
    Chern–Hamilton defect's positivity is intrinsic to the generator — no
    choice of measure (metric) can hide it. -/
theorem killingDefect_pos_of_affinityCharge_ne_zero (L : Matrix V V ℝ)
    (c : ℕ → V) (len : ℕ) (hc : c 0 = c len)
    (hQ : AffinityCharge L c len ≠ 0)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) :
    0 < KillingDefect L pi_dist := by
  rcases lt_or_eq_of_le (killingDefect_nonneg L pi_dist) with h | h
  · exact h
  · exact absurd
      (affinityCharge_eq_zero_of_detailedBalance L pi_dist hπ
        ((killingDefect_eq_zero_iff_reversible L pi_dist).mp h.symm) c len hc) hQ

/-- **Annealing protection (conserved charge ⇒ eternal NESS)**: along ANY path
    of generators that conserves the affinity charge of one charged cycle, the
    Killing defect stays strictly positive at every time, for every positive
    measure. The charge is the conserved class datum protecting the exotic
    phase — annealing within an affinity class can never reach criticality. -/
theorem annealing_protection (Lpath : ℝ → Matrix V V ℝ) (c : ℕ → V) (len : ℕ)
    (hc : c 0 = c len)
    (hcons : ∀ t, AffinityCharge (Lpath t) c len = AffinityCharge (Lpath 0) c len)
    (h0 : AffinityCharge (Lpath 0) c len ≠ 0) :
    ∀ t (pi_dist : V → ℝ), (∀ v, 0 < pi_dist v) →
      0 < KillingDefect (Lpath t) pi_dist :=
  fun t pi_dist hπ =>
    killingDefect_pos_of_affinityCharge_ne_zero (Lpath t) c len hc
      (by rw [hcons t]; exact h0) pi_dist hπ

/-! ## §4. The handle cycle is charged: instantiation on the exotic pair -/

section Handle

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The handle cycle: the fiber 3-cycle over the base point `w₀`. -/
def handleCycle (w₀ : W) : ℕ → W × ZMod 3 := fun m => (w₀, (m : ZMod 3))

lemma handleCycle_closed (w₀ : W) : handleCycle w₀ 0 = handleCycle w₀ 3 := by
  unfold handleCycle
  exact congrArg (Prod.mk w₀) (by decide)

/-- Forward handle edge: base rate share plus the handle weight `δ`. -/
lemma exoticLift_handle_fwd (M : Matrix W W ℝ) (w₀ : W) (δ : ℝ) (m : ℕ) :
    exoticLift M w₀ δ (handleCycle w₀ m) (handleCycle w₀ (m + 1))
      = M w₀ w₀ / 3 + δ := by
  have hcast : ((m + 1 : ℕ) : ZMod 3) = (m : ZMod 3) + 1 := by push_cast; ring
  unfold handleCycle exoticLift
  rw [Matrix.add_apply, hcast]
  have huni : uniformLift W (ZMod 3) M (w₀, (m : ZMod 3)) (w₀, (m : ZMod 3) + 1)
      = M w₀ w₀ / 3 := by
    unfold uniformLift
    rw [show Fintype.card (ZMod 3) = 3 from by decide]
    norm_num
  have hfib : fiberCycle W w₀ δ (w₀, (m : ZMod 3)) (w₀, (m : ZMod 3) + 1) = δ := by
    unfold fiberCycle
    rw [if_pos ⟨rfl, rfl⟩, if_neg, sub_zero]
    rintro ⟨-, hq⟩
    have h2 : (m : ZMod 3) + 1 = (m : ZMod 3) := congrArg Prod.snd hq
    have h1 : (1 : ZMod 3) = 0 := by
      have := congrArg (fun z => z - (m : ZMod 3)) h2
      simpa using this
    exact one_ne_zero h1
  rw [huni, hfib]

/-- Backward handle edge: base rate share only — the handle is one-way. -/
lemma exoticLift_handle_bwd (M : Matrix W W ℝ) (w₀ : W) (δ : ℝ) (m : ℕ) :
    exoticLift M w₀ δ (handleCycle w₀ (m + 1)) (handleCycle w₀ m)
      = M w₀ w₀ / 3 := by
  have hcast : ((m + 1 : ℕ) : ZMod 3) = (m : ZMod 3) + 1 := by push_cast; ring
  unfold handleCycle exoticLift
  rw [Matrix.add_apply, hcast]
  have huni : uniformLift W (ZMod 3) M (w₀, (m : ZMod 3) + 1) (w₀, (m : ZMod 3))
      = M w₀ w₀ / 3 := by
    unfold uniformLift
    rw [show Fintype.card (ZMod 3) = 3 from by decide]
    norm_num
  have hfib : fiberCycle W w₀ δ (w₀, (m : ZMod 3) + 1) (w₀, (m : ZMod 3)) = 0 := by
    unfold fiberCycle
    rw [if_neg, if_neg, sub_zero]
    · rintro ⟨-, hq⟩
      have h2 : (m : ZMod 3) = (m : ZMod 3) + 1 := congrArg Prod.snd hq
      have h1 : (0 : ZMod 3) = 1 := by
        have := congrArg (fun z => z - (m : ZMod 3)) h2
        simpa using this
      exact absurd h1 (by decide)
    · rintro ⟨-, hq⟩
      have h2 : (m : ZMod 3) = (m : ZMod 3) + 1 + 1 := congrArg Prod.snd hq
      have h1 : (0 : ZMod 3) = 1 + 1 := by
        have := congrArg (fun z => z - (m : ZMod 3)) h2
        simpa [add_assoc] using this
      exact absurd h1 (by decide)
  rw [huni, hfib, add_zero]

lemma cycleProdFwd_exotic (M : Matrix W W ℝ) (w₀ : W) (δ : ℝ) :
    cycleProdFwd (exoticLift M w₀ δ) (handleCycle w₀) 3
      = (M w₀ w₀ / 3 + δ) ^ 3 := by
  unfold cycleProdFwd
  rw [Finset.prod_congr rfl fun m _ => exoticLift_handle_fwd M w₀ δ m,
      Finset.prod_const, Finset.card_range]

lemma cycleProdBwd_exotic (M : Matrix W W ℝ) (w₀ : W) (δ : ℝ) :
    cycleProdBwd (exoticLift M w₀ δ) (handleCycle w₀) 3
      = (M w₀ w₀ / 3) ^ 3 := by
  unfold cycleProdBwd
  rw [Finset.prod_congr rfl fun m _ => exoticLift_handle_bwd M w₀ δ m,
      Finset.prod_const, Finset.card_range]

/-- **The handle is charged, for EVERY base model**: `Q = (a+δ)³ − a³ > 0` where
    `a = M w₀ w₀ / 3`. No hypothesis on `M` — the charge is created by the
    surgery, not inherited from the base. -/
theorem exoticLift_affinityCharge_pos (M : Matrix W W ℝ) (w₀ : W)
    {δ : ℝ} (hδ : 0 < δ) :
    0 < AffinityCharge (exoticLift M w₀ δ) (handleCycle w₀) 3 := by
  unfold AffinityCharge
  rw [cycleProdFwd_exotic, cycleProdBwd_exotic]
  set a := M w₀ w₀ / 3 with ha
  have hexp : (a + δ) ^ 3 - a ^ 3
      = δ * ((3 / 4) * (2 * a + δ) ^ 2 + (1 / 4) * δ ^ 2) := by ring
  rw [hexp]
  apply mul_pos hδ
  have h1 : 0 < δ ^ 2 := pow_pos hδ 2
  nlinarith [sq_nonneg (2 * a + δ)]

/-- **HEADLINE (measure-independent exoticness)**: the exotic lift has strictly
    positive Killing defect w.r.t. EVERY positive measure — strengthening
    `killingDefect_exoticLift_pos` from the lifted measure to all measures.
    Exoticness is intrinsic: no equilibrium notion can be restored by any
    choice of stationary data. -/
theorem killingDefect_exoticLift_pos_universal (M : Matrix W W ℝ) (w₀ : W)
    {δ : ℝ} (hδ : 0 < δ)
    (pi_dist : W × ZMod 3 → ℝ) (hπ : ∀ v, 0 < pi_dist v) :
    0 < KillingDefect (exoticLift M w₀ δ) pi_dist :=
  killingDefect_pos_of_affinityCharge_ne_zero _ _ 3 (handleCycle_closed w₀)
    (ne_of_gt (exoticLift_affinityCharge_pos M w₀ hδ)) pi_dist hπ

/-- The uniform lift of a reversible base carries zero charge on EVERY closed
    cycle — it is affinity-trivial (flat log-rate connection). -/
theorem uniformLift_affinityCharge_zero (M : Matrix W W ℝ) (πW : W → ℝ)
    (hπW : ∀ w, 0 < πW w) (hdb : DetailedBalance M πW)
    (c : ℕ → W × ZMod 3) (len : ℕ) (hc : c 0 = c len) :
    AffinityCharge (uniformLift W (ZMod 3) M) c len = 0 :=
  affinityCharge_eq_zero_of_detailedBalance _ _ (liftedMeasure_pos πW hπW)
    (uniformLift_detailedBalance M πW hdb) c len hc

/-- **Affinity separates the exotic pair**: the two members of the pair carry
    different charges on the handle cycle. Since the charge is conserved by
    affinity-preserving annealing (`annealing_protection`), no such anneal
    connects the exotic member to the uniform one — the discrete analogue of
    "homeomorphic but not diffeomorphic". -/
theorem affinity_separates_pair (M : Matrix W W ℝ) (πW : W → ℝ)
    (hπW : ∀ w, 0 < πW w) (hdb : DetailedBalance M πW) (w₀ : W)
    {δ : ℝ} (hδ : 0 < δ) :
    AffinityCharge (exoticLift M w₀ δ) (handleCycle w₀) 3
      ≠ AffinityCharge (uniformLift W (ZMod 3) M) (handleCycle w₀) 3 := by
  rw [uniformLift_affinityCharge_zero M πW hπW hdb _ 3 (handleCycle_closed w₀)]
  exact ne_of_gt (exoticLift_affinityCharge_pos M w₀ hδ)

end Handle

end SGC.Bridge.AffinityProtection
