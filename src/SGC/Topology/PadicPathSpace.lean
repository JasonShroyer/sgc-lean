/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team

# SGC.Topology.PadicPathSpace — Cantor/p-adic Layer (Tier 1 scaffold)

Honest scaffold for the missing symbolic tier, per `CANTOR_LAYER_SPEC.md`.

This file is **self-contained (Mathlib only)**. The wiring to existing SGC modules
(`Renormalization.OptimalPartition`, `Observables.ValidityHorizon`,
`Geometry.Manifold.Convergence` = Conjecture C-0) is marked TODO and will be added once
this Tier-1 layer compiles.

Discipline (CANTOR_LAYER_SPEC §0): every open result is a `theorem … := by sorry`
(a kernel-tracked debt). We add **no new `axiom`s** (the tree already has 229).

What is and isn't here:
- PROVEN (Mathlib-checked, **no `sorry`**; `#print axioms` = {propext, Classical.choice,
  Quot.sound}): the symbolic path space, depth-`n` truncation + its defining equation, the
  depth-`n` quotient cardinality `|Fin n → Fin p| = pⁿ` (`card_truncations`), the canonical
  base-`p` digit encoding (`digitEncoding`), the finite inverse-system law
  (`castHom_digitEncoding`), the comparison map `digitSeq_to_padicInt` with its intertwining
  law (`digitSeq_toZModPow`), injectivity and surjectivity, and the **keystone**
  homeomorphism `PathSpace (Fin p) ≃ₜ ℤ_[p]` (`pathSpace_homeo_padicInt`).
- NO open `sorry`s remain in this file (the Tier-1 debt is discharged).
- NOT here (deliberately): any `q(n) = 1 + 1/n` claim (refuted — see spec §6),
  `MirandaBridge` (no discrete current exists yet), `validity_horizon_from_depth`.
-/
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin

noncomputable section

namespace SGC.Topology.PadicPathSpace

open Topology Filter

/-! ## 1. Symbolic trajectory space over a finite discrete alphabet

With `A = Fin p` this is the uniformly p-ary path space — the explicit branching
hypothesis of `CANTOR_LAYER_SPEC §4`. Keeping the alphabet abstract avoids committing to a
particular `TopologicalSpace (Fin p)` instance here. -/

variable (A : Type*)

/-- Infinite symbolic trajectories over alphabet `A`. `abbrev` so the product topology
instance transfers automatically. -/
abbrev PathSpace : Type _ := ℕ → A

/-- **Depth-`n` truncation**: the first `n` symbols of a trajectory.

    This is the SGC coarse-graining projector in the uniformly-branching case
    (`CANTOR_LAYER_SPEC §4.3`); it is the symbolic analogue of the p-adic projection
    `PadicInt.toZModPow n : ℤ_[p] → ZMod (p^n)`. -/
def truncate (n : ℕ) (x : PathSpace A) : Fin n → A := fun i => x i.val

/-- The defining equation of `truncate` (rfl). -/
@[simp] theorem truncate_apply (n : ℕ) (x : PathSpace A) (i : Fin n) :
    truncate A n x i = x i.val := rfl

/-- **First proven Cantor-layer fact.** The depth-`n` symbolic quotient over a `p`-letter
    alphabet has exactly `pⁿ` values — matching `|ZMod (p^n)| = |ℤ_[p] / pⁿ ℤ_[p]|`. This is
    the cardinality that licenses reading depth-`n` truncation as the p-adic quotient. -/
theorem card_truncations (p n : ℕ) :
    Fintype.card (Fin n → Fin p) = p ^ n := by
  simp [Fintype.card_pi]

/-! ## 2. Identification with the p-adic integers (the keystone)

The keystone homeomorphism `pathSpace_homeo_padicInt` is **proven at the end of this file**.
It is built on the explicit comparison map `digitSeq_to_padicInt` (§3¾), which by construction
**intertwines** `truncate` with `PadicInt.toZModPow` (an iso of inverse systems). So the
existence witness is the canonical digit-wise identification — *not* the content-light
"all Cantor spaces are homeomorphic" appeal (spec §4.2): no Brouwer characterisation is used. -/

/-! ## 3. The finite p-adic quotient -/

/-- Identify `Fin m` with `ZMod m` for `m > 0` via `i ↦ (i : ZMod m)`, inverse `ZMod.val`.
    This is the canonical, structure-respecting identification (not a bare cardinality
    bijection). -/
def finEquivZMod (m : ℕ) [NeZero m] : Fin m ≃ ZMod m where
  toFun i := ((i : ℕ) : ZMod m)
  invFun a := ⟨a.val, ZMod.val_lt a⟩
  left_inv i := by ext; exact ZMod.val_natCast_of_lt i.isLt
  right_inv a := ZMod.natCast_rightInverse a

/-- **Base-`p` digit encoding** `(Fin n → Fin p) ≃ ZMod (p^n)`, PROVEN.

    This is the *canonical* Horner map `x ↦ ∑ i, x i · pⁱ` read into the arithmetic quotient
    `ZMod (p^n) ≅ ℤ_[p] / pⁿ ℤ_[p]`. It is built as Mathlib's explicit base-`p` encoding
    `finFunctionFinEquiv : (Fin n → Fin p) ≃ Fin (pⁿ)` (whose `finFunctionFinEquiv_apply`
    gives `(·).val = ∑ i, x i · pⁱ`) composed with `finEquivZMod`. Because it is the genuine
    Horner map — not a `Fintype.equivOfCardEq` cardinality bijection — it is the correct object
    to later show **intertwines** `truncate` with `PadicInt.toZModPow` (the open keystone). -/
def digitEncoding (p n : ℕ) [NeZero p] : (Fin n → Fin p) ≃ ZMod (p ^ n) :=
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n (NeZero.ne p)⟩
  finFunctionFinEquiv.trans (finEquivZMod (p ^ n))

/-! ## 3½. The inverse-system law (PROVEN): truncation = p-adic quotient projection -/

/-- **Arithmetic tower bridge.** `digitEncoding` *intertwines* the depth restriction
    `f ↦ f ∘ castSucc` (drop the top digit) with the p-adic quotient map
    `ZMod.castHom : ZMod (pⁿ⁺¹) → ZMod (pⁿ)` (reduce mod `pⁿ`). This is the finite-level,
    Mathlib-only content of "symbolic depth-`n` truncation = `PadicInt.toZModPow n`": the
    commuting square that makes the `digitEncoding`s an **iso of inverse systems**, which is
    the real content behind the open homeomorphism keystone (`pathSpace_homeo_padicInt`). -/
theorem castHom_digitEncoding (p n : ℕ) [NeZero p] (f : Fin (n + 1) → Fin p) :
    ZMod.castHom (pow_dvd_pow p n.le_succ) (ZMod (p ^ n)) (digitEncoding p (n + 1) f)
      = digitEncoding p n (fun i => f i.castSucc) := by
  haveI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (NeZero.ne p)⟩
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (NeZero.ne p)⟩
  simp only [digitEncoding, finEquivZMod, Equiv.trans_apply, Equiv.coe_fn_mk]
  rw [map_natCast, finFunctionFinEquiv_apply, finFunctionFinEquiv_apply,
    Fin.sum_univ_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self,
    mul_zero, add_zero]
  simp [Fin.coe_castSucc]

/-! ## 3¾. Toward the keystone: the algebraic comparison tower (in progress) -/

/-- Depth-`n` Horner value of a symbolic path `s`, as a `ZMod (p^n)` element. -/
def digitVal (p n : ℕ) [NeZero p] (s : ℕ → Fin p) : ZMod (p ^ n) :=
  digitEncoding p n (truncate (Fin p) n s)

/-- The whole-path tower is compatible: reducing the depth-`(n+1)` value mod `pⁿ` gives the
    depth-`n` value. This packages `castHom_digitEncoding` into the exact shape of the
    `PadicInt.lift` / `ofIntSeq` compatibility hypothesis. -/
theorem castHom_digitVal (p n : ℕ) [NeZero p] (s : ℕ → Fin p) :
    ZMod.castHom (pow_dvd_pow p n.le_succ) (ZMod (p ^ n)) (digitVal p (n + 1) s)
      = digitVal p n s := by
  rw [digitVal, digitVal, castHom_digitEncoding]
  congr 1

/-- Reducing the depth-`(n+1)` value's `ℕ`-representative mod `pⁿ` recovers the depth-`n`
    value. The bridge from `castHom_digitVal` to the integer-sequence divisibility that
    `PadicInt.ofIntSeq` consumes. -/
theorem natCast_digitVal_succ (p n : ℕ) [NeZero p] (s : ℕ → Fin p) :
    (((digitVal p (n + 1) s).val : ℕ) : ZMod (p ^ n)) = digitVal p n s := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (NeZero.ne p)⟩
  haveI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (NeZero.ne p)⟩
  rw [ZMod.natCast_val, ← castHom_digitVal p n s, ZMod.castHom_apply]

/-- Consecutive depth values differ by a multiple of `pⁿ` — the integer-sequence Cauchy
    condition that `PadicInt.ofIntSeq` (via `isCauSeq_padicNorm_of_pow_dvd_sub`) consumes. -/
theorem dvd_digitVal_succ_sub (p n : ℕ) [NeZero p] (s : ℕ → Fin p) :
    (p : ℤ) ^ n ∣ ((digitVal p (n + 1) s).val : ℤ) - ((digitVal p n s).val : ℤ) := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (NeZero.ne p)⟩
  rw [← Nat.cast_pow, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [sub_eq_zero, natCast_digitVal_succ, ZMod.natCast_val, ZMod.cast_id]

/-- `Fact p.Prime` supplies `NeZero p` (low priority; defers to Mathlib if it ships one). -/
instance (priority := 50) instNeZeroOfFactPrime (p : ℕ) [hp : Fact p.Prime] : NeZero p :=
  ⟨hp.out.pos.ne'⟩

/-- **The comparison map** `PathSpace (Fin p) → ℤ_[p]`. A symbolic path is sent to the p-adic
    integer whose depth-`n` residue is the path's depth-`n` Horner value, assembled by
    `PadicInt.ofIntSeq` from the (Cauchy) tower of partial values. -/
def digitSeq_to_padicInt (p : ℕ) [Fact p.Prime] (s : ℕ → Fin p) : ℤ_[p] :=
  PadicInt.ofIntSeq (fun n => ((digitVal p n s).val : ℤ))
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ p (fun i => dvd_digitVal_succ_sub p i s))

/-- **Defining property (algebraic core).** The comparison map intertwines `truncate` with
    `PadicInt.toZModPow`: the depth-`n` p-adic residue of `digitSeq_to_padicInt s` is exactly
    the depth-`n` symbolic value `digitVal n s`. This is the iso-of-inverse-systems law lifted
    to the actual p-adic integers — the algebraic heart of the homeomorphism keystone. -/
theorem digitSeq_toZModPow (p : ℕ) [Fact p.Prime] (s : ℕ → Fin p) (n : ℕ) :
    PadicInt.toZModPow n (digitSeq_to_padicInt p s) = digitVal p n s := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (NeZero.ne p)⟩
  unfold digitSeq_to_padicInt
  rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub]
  · push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
  · intro i
    exact dvd_digitVal_succ_sub p i s

/-- **Injectivity of the comparison map.** Distinct symbolic paths give distinct p-adic
    integers: if two paths share every depth-`n` residue they share every digit. Uses
    `digitSeq_toZModPow` to pull equality back to the finite quotients, then injectivity of
    the `digitEncoding` equivalence. -/
theorem digitSeq_to_padicInt_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (digitSeq_to_padicInt p) := by
  intro s t h
  funext k
  have hk : digitVal p (k + 1) s = digitVal p (k + 1) t := by
    rw [← digitSeq_toZModPow p s, ← digitSeq_toZModPow p t, h]
  rw [digitVal, digitVal] at hk
  have he := (digitEncoding p (k + 1)).injective hk
  have := congrFun he (Fin.last k)
  simpa [truncate, Fin.val_last] using this

/-! ## 3⅞. The inverse digit tower of a p-adic integer (PROVEN) -/

/-- The depth-`n` digit block of `y : ℤ_[p]`: the `digitEncoding`-preimage of its residue. -/
def gtower (p : ℕ) [Fact p.Prime] (y : ℤ_[p]) (n : ℕ) : Fin n → Fin p :=
  (digitEncoding p n).symm (PadicInt.toZModPow n y)

/-- The digit tower is consistent: dropping the top digit at depth `n+1` recovers depth `n`. -/
theorem gtower_castSucc (p : ℕ) [Fact p.Prime] (y : ℤ_[p]) (n : ℕ) (i : Fin n) :
    gtower p y (n + 1) i.castSucc = gtower p y n i := by
  unfold gtower
  have h1 : digitEncoding p (n + 1)
      ((digitEncoding p (n + 1)).symm (PadicInt.toZModPow (n + 1) y))
      = PadicInt.toZModPow (n + 1) y := (digitEncoding p (n + 1)).apply_symm_apply _
  have key := castHom_digitEncoding p n
    ((digitEncoding p (n + 1)).symm (PadicInt.toZModPow (n + 1) y))
  rw [h1] at key
  have hcast : ZMod.castHom (pow_dvd_pow p n.le_succ) (ZMod (p ^ n))
      (PadicInt.toZModPow (n + 1) y) = PadicInt.toZModPow n y := by
    rw [ZMod.castHom_apply]; exact PadicInt.cast_toZModPow n (n + 1) n.le_succ y
  rw [hcast] at key
  have hsymm : (digitEncoding p n).symm (PadicInt.toZModPow n y)
      = fun i => (digitEncoding p (n + 1)).symm (PadicInt.toZModPow (n + 1) y) i.castSucc :=
    (digitEncoding p n).symm_apply_eq.mpr key
  exact (congrFun hsymm i).symm

/-- Climbing law: the digit tower at any depth `N > k` agrees with the depth-`(k+1)` block at
    position `k`. The consistency that lets a single path realise every truncation. -/
theorem gtower_top (p : ℕ) [Fact p.Prime] (y : ℤ_[p]) :
    ∀ N k (hk : k < N), gtower p y N ⟨k, hk⟩ = gtower p y (k + 1) (Fin.last k) := by
  intro N
  induction N with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ N ih =>
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
    · have hcoe : (⟨k, hk⟩ : Fin (N + 1)) = (⟨k, h⟩ : Fin N).castSucc := Fin.ext rfl
      rw [hcoe, gtower_castSucc p y N ⟨k, h⟩, ih k h]
    · subst h; rfl

/-! ## 3⁹⁄₁₀. Surjectivity, and the keystone homeomorphism (PROVEN) -/

/-- **Surjectivity of the comparison map.** Every p-adic integer is realised by a symbolic
    path — its own digit tower. With injectivity, `digitSeq_to_padicInt` is a bijection. -/
theorem digitSeq_to_padicInt_surjective (p : ℕ) [Fact p.Prime] :
    Function.Surjective (digitSeq_to_padicInt p) := by
  intro y
  refine ⟨fun k => gtower p y (k + 1) (Fin.last k), ?_⟩
  have htr : ∀ n, truncate (Fin p) n (fun k => gtower p y (k + 1) (Fin.last k)) = gtower p y n := by
    intro n
    funext i
    have hi : (⟨i.val, i.isLt⟩ : Fin n) = i := Fin.ext rfl
    calc truncate (Fin p) n (fun k => gtower p y (k + 1) (Fin.last k)) i
        = gtower p y (i.val + 1) (Fin.last i.val) := rfl
      _ = gtower p y n ⟨i.val, i.isLt⟩ := (gtower_top p y n i.val i.isLt).symm
      _ = gtower p y n i := by rw [hi]
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  rw [digitSeq_toZModPow]
  show digitEncoding p n (truncate (Fin p) n (fun k => gtower p y (k + 1) (Fin.last k)))
      = PadicInt.toZModPow n y
  rw [htr n]
  exact (digitEncoding p n).apply_symm_apply _

/-- The symbolic path space and `ℤ_[p]` are in canonical bijection via `digitSeq_to_padicInt`. -/
def pathSpaceEquivPadicInt (p : ℕ) [Fact p.Prime] : PathSpace (Fin p) ≃ ℤ_[p] :=
  Equiv.ofBijective (digitSeq_to_padicInt p)
    ⟨digitSeq_to_padicInt_injective p, digitSeq_to_padicInt_surjective p⟩

/-- **Continuity of the comparison map.** Depth-`n` truncation is locally constant (it factors
    through the discrete finite quotient), and depth-`n` agreement forces the p-adic distance
    below `p^{-n}`; hence `digitSeq_to_padicInt` is continuous. -/
theorem continuous_digitSeq_to_padicInt (p : ℕ) [Fact p.Prime]
    [TopologicalSpace (Fin p)] [DiscreteTopology (Fin p)] :
    Continuous (digitSeq_to_padicInt p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hr : (p : ℝ)⁻¹ < 1 := by rw [inv_eq_one_div, div_lt_one hp0]; exact hp1
  refine continuous_iff_continuousAt.2 fun s => ?_
  have htend : Tendsto (digitSeq_to_padicInt p) (nhds s) (nhds (digitSeq_to_padicInt p s)) := by
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hr
    have hpow : (p : ℝ) ^ (-(n : ℤ)) = ((p : ℝ)⁻¹) ^ n := by
      rw [zpow_neg, zpow_natCast, inv_pow]
    have hcont_tr : Continuous (truncate (Fin p) n) := continuous_pi fun i => continuous_apply _
    have hopen : IsOpen (truncate (Fin p) n ⁻¹' {truncate (Fin p) n s}) :=
      hcont_tr.isOpen_preimage _ (isOpen_discrete _)
    filter_upwards [hopen.mem_nhds rfl] with t ht
    have hteq : truncate (Fin p) n t = truncate (Fin p) n s := ht
    calc dist (digitSeq_to_padicInt p t) (digitSeq_to_padicInt p s)
        ≤ (p : ℝ) ^ (-(n : ℤ)) := by
          rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
            RingHom.mem_ker, map_sub, sub_eq_zero, digitSeq_toZModPow, digitSeq_toZModPow]
          simp only [digitVal, hteq]
      _ < ε := by rw [hpow]; exact hn
  exact htend

/-- **Keystone (Tier 1), PROVEN.** Under uniform p-ary branching, the symbolic trajectory
    space is homeomorphic to `ℤ_[p]`. The witness is the canonical comparison map
    `digitSeq_to_padicInt` (a continuous bijection from a compact space to a Hausdorff space),
    which by construction intertwines `truncate` with `PadicInt.toZModPow` — so this is the
    content-rich identification, not a bare "all Cantor spaces are homeomorphic" appeal. -/
theorem pathSpace_homeo_padicInt (p : ℕ) [Fact p.Prime]
    [TopologicalSpace (Fin p)] [DiscreteTopology (Fin p)] :
    Nonempty (PathSpace (Fin p) ≃ₜ ℤ_[p]) :=
  ⟨Continuous.homeoOfEquivCompactToT2 (f := pathSpaceEquivPadicInt p)
    (continuous_digitSeq_to_padicInt p)⟩

/-! ## 3¹⁰⁄₁₀. The d-fold product: independent integrators (PROVEN) -/

/-- **d independent p-ary integrators, PROVEN.** The symbolic state space of `d` *independent*
    p-ary path integrators is canonically `(ℤ_[p])^d`. Immediate from the keystone via
    `Homeomorph.piCongrRight`.

    This is the honest formal correlate of the grokking-topology experiments (`decisions/0010`):
    a recurrent net tracking `d` independent running sums on `ℤ_p` has, as its symbolic domain,
    exactly `Fin d → ℤ_[p]`. The empirical finding that its *representation* concentrates on the
    continuous torus `T^d = (S¹)^d` (d=1 ring; d=2 flat torus, with orthogonal/direct-sum carriers)
    is the discrete→continuum **image** of THIS domain — the analytic half lives in
    `Geometry.Manifold.Convergence` (Conjecture C-0 / `manifold_hypothesis`), not here. We claim only
    the symbolic identity, which is exact and axiom-clean. -/
theorem pi_pathSpace_homeo_pi_padicInt (p d : ℕ) [Fact p.Prime]
    [TopologicalSpace (Fin p)] [DiscreteTopology (Fin p)] :
    Nonempty ((Fin d → PathSpace (Fin p)) ≃ₜ (Fin d → ℤ_[p])) :=
  ⟨Homeomorph.piCongrRight fun _ => (pathSpace_homeo_padicInt p).some⟩

/-! ## 4. TODO — wiring to existing SGC modules (next increment)

* `coarseGraining_is_truncation`: identify `Renormalization.OptimalPartition`'s
  coarse-graining projector with `truncate` for a nested uniformly p-ary partition chain.
* `truncation_information_monotone`: depth-`n` truncation does not increase accessible
  information (a DPI instance; cf. `TsallisStatistics.TsallisDivergence_nonneg`).
* `discrete_to_continuum`: as `n → ∞`, the truncation tower's generator converges to the
  manifold Fokker–Planck generator — i.e. Conjecture C-0 (`Geometry.Manifold.Convergence`).
-/

end SGC.Topology.PadicPathSpace

end
