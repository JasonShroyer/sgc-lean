/-
Copyright (c) 2026 Jason Shroyer. All rights reserved.
Released under Apache 2.0 license.
-/
import SGC.Thermodynamics.EntropyProduction

/-!
# Measure Re-entry: the canonical language of approximate emergence

The Trinity Theorem (`SGC.Bridge.ThreeArrows`) established that at exact
lumpability the stationary measure is **gauge**: it drops out of
renormalization (`coarseGenerator_eq_quotientGeneratorSimple`). This module
builds the ε > 0 theory around the converse insight: **the measure becomes
physical exactly when lumpability breaks**, and its re-entry is a single
intrinsic functional with three faces:

* **a field** — the `residual`: each microstate's exit-rate deviation from
  its block's conditional-`π` average,
* **a number** — `defectSq` (`𝔇_π²`): the `π`-weighted square mass of that
  field,
* **an operator** — the `closureCommutator` `𝒞 = L·K − K·Q^π`: the exact
  obstruction to the intertwining (Dynkin) identity.

## Main results

* `blockRate_eq_sum_pi_mul_exit` / `coarseGenerator_eq_conditional_exit_average` —
  the physical coarse generator `Q^π` IS the conditional exit average: the
  canonical, representative-free macro operator (Workstream B, ladder 1).
* `residual_all_zero_iff_stronglyLumpable` and
  **`defectSq_eq_zero_iff_stronglyLumpable`** — the zero-defect
  equivalence: `𝔇_π = 0 ⟺ exact strong lumpability` (ladder 2–3). Exact
  emergence is the exact zero set of an intrinsic failure functional.
* **`closureCommutator_entry`** — the commutator's entries ARE the residual
  field: `𝒞 i B = residual i B`. Hence
  **`defectSq_eq_weighted_commutator_frobenius`**: `𝔇_π²` is exactly the
  `π`-weighted Frobenius norm² of the closure commutator. The brief asked
  whether the defect *bounds* a norm of `𝒞`; the answer is that with the
  right (weighted) norm it *equals* it.
* `closureCommutator_eq_zero_iff_stronglyLumpable` — operator form of the
  equivalence; at ε = 0 this recovers the intertwining theorem with `Q^π`
  in place of the structural quotient.
* **`power_closure_telescoping`** — the discrete Duhamel identity:
  `L^n·K − K·(Q^π)^n = Σ_{k<n} L^{n−1−k} · 𝒞 · (Q^π)^k`.
  Every finite-time closure error is a sum of single re-entry events
  propagated by the fine dynamics before and the macro law after. This is
  the finite-time bridge from instantaneous defect to validity horizon
  (Workstream C's commutator identity, in exact algebraic form).
* Toy models: an exactly lumpable 3-state chain (defect provably zero) and
  a minimally non-lumpable one (defect provably positive) — the smallest
  pair witnessing that the functional separates the regimes.

## Honest scope

* Finite state spaces; `π` any strictly positive weight (stationarity is
  NOT assumed — the defect is defined against any reference measure, and
  its physical reading is sharpest at stationarity).
* The defect here sums over ALL target blocks (including a state's own).
  The brief's `B ≠ A` variant is equivalent for conservative generators
  (own-block exit is determined by the others); not formalized here.
* No norm-level horizon bound is stated yet: `power_closure_telescoping`
  is the exact identity from which such bounds follow once a norm is
  fixed; the scaling of `T_η` in `𝔇_π` is a numerical hypothesis
  (`docs/measure-reentry.md`), not a theorem.
* `T* ~ 1/ε`, `ε ≡ E_d`, and any computation-from-defect claims are NOT
  stated as theorems (brief, order 7).
-/

namespace SGC.Renormalization.MeasureReentry

open Finset Matrix
open SGC SGC.Thermodynamics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## §1. The residual field and the defect -/

/-- The block rate is the `π`-weighted aggregate of exit rates: reshaping of
the double sum, making `BlockRate` manifestly measure-weighted exit mass. -/
lemma blockRate_eq_sum_pi_mul_exit (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (a_bar b_bar : P.Quot) :
    BlockRate L P pi_dist a_bar b_bar
      = ∑ i : V, (if P.quot_map i = a_bar
          then pi_dist i * row_sum_block L P i b_bar else 0) := by
  unfold BlockRate
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : P.quot_map i = a_bar
  · rw [if_pos hi]
    simp only [hi, true_and]
    unfold row_sum_block
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : P.quot_map y = b_bar <;> simp [hy]
  · simp [hi]

/-- **The physical coarse generator is the conditional exit average**: for
positive `π`, `Q^π(ā,b̄)` is the mean exit rate into `b̄` under the
conditional stationary measure on `ā`. Canonical and representative-free. -/
theorem coarseGenerator_eq_conditional_exit_average (L : Matrix V V ℝ)
    (P : Partition V) {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x)
    (a_bar b_bar : P.Quot) :
    CoarseGenerator L P pi_dist a_bar b_bar
      = (1 / pi_bar P pi_dist a_bar) *
        ∑ i : V, (if P.quot_map i = a_bar
          then pi_dist i * row_sum_block L P i b_bar else 0) := by
  have hpos : 0 < CoarseStationaryDist P pi_dist a_bar := pi_bar_pos P hπ a_bar
  unfold CoarseGenerator
  rw [if_neg hpos.ne']
  congr 1
  exact blockRate_eq_sum_pi_mul_exit L P pi_dist a_bar b_bar

/-- **The residual field**: the deviation of a microstate's exit rate from
its block's conditional-`π` average. The pointwise face of measure
re-entry; identically zero exactly at strong lumpability. -/
noncomputable def residual (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (i : V) (B : P.Quot) : ℝ :=
  row_sum_block L P i B - CoarseGenerator L P pi_dist (P.quot_map i) B

/-- **The measure-reentry defect (squared)**, `𝔇_π²`: the `π`-weighted
square mass of the residual field. -/
noncomputable def defectSq (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) : ℝ :=
  ∑ i : V, pi_dist i * ∑ B : P.Quot, (residual L P pi_dist i B) ^ 2

lemma defectSq_nonneg (L : Matrix V V ℝ) (P : Partition V)
    {pi_dist : V → ℝ} (hπ : ∀ x, 0 ≤ pi_dist x) :
    0 ≤ defectSq L P pi_dist :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hπ i)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-! ## §2. The zero-defect equivalence -/

/-- At exact lumpability the residual field vanishes: the conditional
average of a block-constant exit rate is that rate. -/
lemma residual_eq_zero_of_stronglyLumpable (L : Matrix V V ℝ)
    (P : Partition V) (hL : IsStronglyLumpable L P)
    {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x) (i : V) (B : P.Quot) :
    residual L P pi_dist i B = 0 := by
  unfold residual
  rw [coarseGenerator_eq_quotientGeneratorSimple L P hL hπ,
    quot_gen_eq_row_sum L P hL, sub_self]

/-- **The core equivalence**: the residual field vanishes identically iff
the partition is exactly strongly lumpable. -/
theorem residual_all_zero_iff_stronglyLumpable (L : Matrix V V ℝ)
    (P : Partition V) {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x) :
    (∀ i B, residual L P pi_dist i B = 0) ↔ IsStronglyLumpable L P := by
  constructor
  · intro h x y hxy b_bar
    have hx := h x b_bar
    have hy := h y b_bar
    unfold residual at hx hy
    have hq : P.quot_map x = P.quot_map y := Quotient.sound hxy
    have hrx : row_sum_block L P x b_bar
        = CoarseGenerator L P pi_dist (P.quot_map x) b_bar := by linarith
    have hry : row_sum_block L P y b_bar
        = CoarseGenerator L P pi_dist (P.quot_map y) b_bar := by linarith
    show row_sum_block L P x b_bar = row_sum_block L P y b_bar
    rw [hrx, hry, hq]
  · intro hL i B
    exact residual_eq_zero_of_stronglyLumpable L P hL hπ i B

/-- **THE ZERO-DEFECT EQUIVALENCE.** `𝔇_π² = 0` iff the coarse-graining is
exactly strongly lumpable: exact emergence is the exact zero set of the
measure-reentry functional. The Trinity is the boundary condition of the
ε > 0 theory. -/
theorem defectSq_eq_zero_iff_stronglyLumpable (L : Matrix V V ℝ)
    (P : Partition V) {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x) :
    defectSq L P pi_dist = 0 ↔ IsStronglyLumpable L P := by
  rw [← residual_all_zero_iff_stronglyLumpable L P hπ]
  constructor
  · intro h0 i B
    have hterm : ∀ x ∈ Finset.univ (α := V),
        0 ≤ pi_dist x * ∑ C : P.Quot, (residual L P pi_dist x C) ^ 2 :=
      fun x _ => mul_nonneg (hπ x).le
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hi := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp h0 i (Finset.mem_univ i)
    have hsum : (∑ C : P.Quot, (residual L P pi_dist i C) ^ 2) = 0 := by
      rcases mul_eq_zero.mp hi with h | h
      · exact absurd h (hπ i).ne'
      · exact h
    have hB := (Finset.sum_eq_zero_iff_of_nonneg
      (fun C _ => sq_nonneg (residual L P pi_dist i C))).mp hsum B
      (Finset.mem_univ B)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hB
  · intro h
    unfold defectSq
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finset.sum_eq_zero fun B _ => by rw [h i B]; ring, mul_zero]

/-! ## §3. The closure commutator -/

/-- Generic lift-multiplication entry: `(K · M) i B = M ⟦i⟧ B` for any
macro matrix `M`. -/
lemma lift_mul_entry (P : Partition V) (M : Matrix P.Quot P.Quot ℝ)
    (i : V) (B : P.Quot) :
    (lift_matrix P * M) i B = M (P.quot_map i) B := by
  simp only [Matrix.mul_apply, lift_matrix]
  rw [Finset.sum_eq_single (P.quot_map i)]
  · rw [if_pos rfl, one_mul]
  · intro C _ hC
    rw [if_neg (Ne.symm hC), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The closure commutator** `𝒞 = L·K − K·Q^π`: the exact obstruction to
the intertwining identity for the physical quotient. -/
noncomputable def closureCommutator (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) : Matrix V P.Quot ℝ :=
  L * lift_matrix P - lift_matrix P * CoarseGenerator L P pi_dist

/-- **The commutator's entries ARE the residual field.** The operator face
and the pointwise face of measure re-entry are the same object. -/
theorem closureCommutator_entry (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (i : V) (B : P.Quot) :
    closureCommutator L P pi_dist i B = residual L P pi_dist i B := by
  unfold closureCommutator residual
  rw [Matrix.sub_apply, LK_entry, lift_mul_entry]

/-- **`𝔇_π²` is exactly the `π`-weighted Frobenius norm² of the closure
commutator.** Not a bound: an identity. Measure re-entry IS the closure
obstruction, measured. -/
theorem defectSq_eq_weighted_commutator_frobenius (L : Matrix V V ℝ)
    (P : Partition V) (pi_dist : V → ℝ) :
    defectSq L P pi_dist
      = ∑ i : V, pi_dist i *
          ∑ B : P.Quot, (closureCommutator L P pi_dist i B) ^ 2 := by
  unfold defectSq
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact Finset.sum_congr rfl fun B _ => by rw [closureCommutator_entry]

/-- Operator form of the equivalence: the commutator vanishes iff the
coarse-graining is exact. At ε = 0 this is the intertwining theorem with
the physical quotient. -/
theorem closureCommutator_eq_zero_iff_stronglyLumpable (L : Matrix V V ℝ)
    (P : Partition V) {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x) :
    closureCommutator L P pi_dist = 0 ↔ IsStronglyLumpable L P := by
  rw [← residual_all_zero_iff_stronglyLumpable L P hπ]
  constructor
  · intro h i B
    rw [← closureCommutator_entry, h]
    rfl
  · intro h
    ext i B
    rw [closureCommutator_entry, h i B]
    rfl

/-! ## §4. The discrete Duhamel identity -/

/-- **Finite-time closure telescoping.** The `n`-step closure error is the
sum of single measure-reentry events, each propagated by the fine dynamics
before the event and by the macro law after it:

`L^n·K − K·(Q^π)^n = Σ_{k<n} L^{n−1−k} · 𝒞 · (Q^π)^k`.

The exact identity behind every validity-horizon bound: fix a norm,
estimate the factors, and `T_η` follows. At `𝒞 = 0` it recovers eternal
closure (`intertwining_pow` with the physical quotient). -/
theorem power_closure_telescoping (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (n : ℕ) :
    L ^ n * lift_matrix P - lift_matrix P * (CoarseGenerator L P pi_dist) ^ n
      = ∑ k ∈ Finset.range n,
          L ^ (n - 1 - k) * closureCommutator L P pi_dist
            * (CoarseGenerator L P pi_dist) ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have expand : L ^ (n + 1) * lift_matrix P
        - lift_matrix P * (CoarseGenerator L P pi_dist) ^ (n + 1)
        = L * (L ^ n * lift_matrix P
            - lift_matrix P * (CoarseGenerator L P pi_dist) ^ n)
          + closureCommutator L P pi_dist
            * (CoarseGenerator L P pi_dist) ^ n := by
      unfold closureCommutator
      rw [pow_succ' L, pow_succ' (CoarseGenerator L P pi_dist)]
      rw [Matrix.mul_sub, Matrix.sub_mul]
      simp only [Matrix.mul_assoc]
      abel
    rw [expand, ih, Matrix.mul_sum, Finset.sum_range_succ]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hkn : k < n := Finset.mem_range.mp hk
      have harith : n + 1 - 1 - k = (n - 1 - k) + 1 := by omega
      rw [harith, pow_succ' L]
      simp only [Matrix.mul_assoc]
    · have : n + 1 - 1 - n = 0 := by omega
      rw [this, pow_zero, Matrix.one_mul]

/-! ## §5. Toy models: the smallest witnesses -/

/-- Exactly lumpable 3-state chain: both `A = {0,1}` states exit to
`{2}` at rate `1`. -/
noncomputable def Ltoy : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
  if i = j then (if (i : ℕ) = 2 then -2 else -1)
  else if (i : ℕ) ≤ 1 ∧ (j : ℕ) = 2 then 1
  else if (i : ℕ) = 2 ∧ (j : ℕ) ≤ 1 then 1
  else 0

/-- Minimally non-lumpable 3-state chain: state `0` exits to `{2}` at rate
`1`, state `1` at rate `2`. -/
noncomputable def Lnl : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
  if i = j then (if (i : ℕ) = 0 then -1 else if (i : ℕ) = 1 then -2 else -2)
  else if (i : ℕ) = 0 ∧ (j : ℕ) = 2 then 1
  else if (i : ℕ) = 1 ∧ (j : ℕ) = 2 then 2
  else if (i : ℕ) = 2 ∧ (j : ℕ) ≤ 1 then 1
  else 0

/-- The two-block partition `{0,1} | {2}` of `Fin 3`. -/
def Ptoy : Partition (Fin 3) where
  rel := ⟨fun x y => ((x : ℕ) ≤ 1 ↔ (y : ℕ) ≤ 1),
    ⟨fun _ => Iff.rfl, Iff.symm, Iff.trans⟩⟩
  decRel := fun x y => inferInstanceAs (Decidable (((x : ℕ) ≤ 1) ↔ ((y : ℕ) ≤ 1)))

lemma Ptoy_mk_eq_mk {z w : Fin 3} :
    (Quotient.mk Ptoy.rel z = Quotient.mk Ptoy.rel w)
      ↔ (((z : ℕ) ≤ 1) ↔ ((w : ℕ) ≤ 1)) :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- The lumpable toy is strongly lumpable. -/
theorem Ltoy_stronglyLumpable : IsStronglyLumpable Ltoy Ptoy := by
  intro x y hxy b_bar
  induction b_bar using Quotient.ind with
  | _ w =>
    have hxy' : (((x : ℕ) ≤ 1) ↔ ((y : ℕ) ≤ 1)) := hxy
    show (∑ z : Fin 3, if Ptoy.quot_map z = Quotient.mk Ptoy.rel w then Ltoy x z else 0)
      = ∑ z : Fin 3, if Ptoy.quot_map z = Quotient.mk Ptoy.rel w then Ltoy y z else 0
    simp only [SGC.Partition.quot_map, Ptoy_mk_eq_mk]
    fin_cases x <;> fin_cases y <;> fin_cases w <;>
      simp_all [Fin.sum_univ_three, Ltoy]

/-- The non-lumpable toy is NOT strongly lumpable: states `0` and `1` share
a block but exit it at rates `1 ≠ 2`. -/
theorem Lnl_not_stronglyLumpable : ¬ IsStronglyLumpable Lnl Ptoy := by
  intro h
  have hrel : Ptoy.rel.r 0 1 := by
    show (((0 : Fin 3) : ℕ) ≤ 1) ↔ (((1 : Fin 3) : ℕ) ≤ 1)
    decide
  have := h 0 1 hrel (Ptoy.quot_map 2)
  have h2 : ∀ z : Fin 3, (Ptoy.quot_map z = Ptoy.quot_map 2) ↔ (z : ℕ) = 2 := by
    intro z
    show (Quotient.mk Ptoy.rel z = Quotient.mk Ptoy.rel 2) ↔ _
    rw [Ptoy_mk_eq_mk]
    fin_cases z <;> decide
  rw [Finset.sum_congr rfl fun z _ => if_congr (h2 z) rfl rfl,
    Finset.sum_congr rfl fun z _ => if_congr (h2 z) rfl rfl] at this
  rw [Fin.sum_univ_three, Fin.sum_univ_three] at this
  norm_num [Lnl] at this
  simp at this

/-- **The defect separates the regimes**: zero for the lumpable toy. -/
theorem defectSq_Ltoy_eq_zero :
    defectSq Ltoy Ptoy (fun _ => 1) = 0 :=
  (defectSq_eq_zero_iff_stronglyLumpable Ltoy Ptoy
    (fun _ => one_pos)).mpr Ltoy_stronglyLumpable

/-- **The defect separates the regimes**: strictly positive for the
non-lumpable toy — measure re-entry detects the minimal failure. -/
theorem defectSq_Lnl_pos :
    0 < defectSq Lnl Ptoy (fun _ => 1) := by
  have hne : defectSq Lnl Ptoy (fun _ => 1) ≠ 0 := by
    intro h0
    exact Lnl_not_stronglyLumpable
      ((defectSq_eq_zero_iff_stronglyLumpable Lnl Ptoy
        (fun _ => one_pos)).mp h0)
  exact lt_of_le_of_ne
    (defectSq_nonneg Lnl Ptoy (fun _ => zero_le_one)) (Ne.symm hne)

end SGC.Renormalization.MeasureReentry
