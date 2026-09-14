/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Bridge.DeterministicLumpability

/-!
# The terminal decoding certificate on a blocked deterministic machine

The two theorems announced in *The Computation Axis, Rebuilt*, Section 5, in the order
they were proved.

## Theorem 2: the certificate meets a computer

For a deterministic dynamics `f` on a finite configuration space, observed through a
partition `P` with closure defect `c = ||T_f J - J Q||_row`, the terminal decoding
certificate of `TerminalDecoding` specializes to:

* `machine_terminal_tv` - after `h` steps the actual observed law and the reference
  coarse prediction differ in total variation by at most `min 1 (h c / 2)`;
* `machine_terminal_tv_of_descends` - if `f` descends (exact factor map) the budget is
  zero: the quotient machine predicts the observed law exactly, for every input law and
  every horizon;
* `machine_point_law` - from a point mass at `x`, the actual observed law after `h` steps
  is the point mass at `quot_map (f^[h] x)`: deterministic machines have deterministic
  observations, so every decoder is either right or wrong, never in between;
* `machine_terminal_reliability` - the per-class reliability transfer, instantiated.

## The mixing refinement is vacuous for deterministic quotients

`dobrushin_detKernel_eq_one`: a deterministic kernel with two distinct outputs has
Dobrushin coefficient `1`. Hence when the *quotient* dynamics is itself a machine (the
exactly lumpable case, `coarseGenerator_detKernel_eq`), the geometric refinement
`c / (2 (1 - delta))` of `TerminalDecoding` gives nothing beyond the linear budget: a
computation does not mix, and its coarse-graining error, when nonzero, can accumulate
linearly in the number of steps. This is the honest SGC form of the 2025 manuscript's
"global integration cost grows with the number of levels".

## Theorem 1 (general form): descent onto kept coordinates

Configurations split as `A × B` (kept × forgotten). `descends_fst_iff`: `f` descends
onto the partition by the kept coordinate iff the kept coordinate evolves autonomously,
`(f x).1` depends only on `x.1`. This is the criterion a concrete Turing-machine window
theorem must verify: *the `b`-step block map descends onto a window iff no information
enters the window from outside during `b` steps*.

## Theorem 1, concrete: the window theorem for a head-moving machine

`tmStep_iterate_window` / `tmBlock_descends_shrink`: for a one-tape machine in
head-relative coordinates with moves bounded by one cell, the `b`-step block map sends the
equivalence "same control state and same tape on `|i| <= r`" to "same control state and
same tape on `|i| <= r - b`". The block map descends onto a window **that shrinks by one
cell per step**; exact descent onto the same window holds only for `b = 0`. The incoming
cells are the leak (`defect_pos_of_leak`; `reader_defect_pos` is the one-cell prototype),
and the shrinkage is exactly the reviewer's observation about `truncate_pathShift`
(depth `n+1` input for a depth-`n` output) in the Bernoulli tower - now proved for a real
machine model. The state space is infinite, so only the descent notion is used; the
finite-`V` defect theorems apply to any finite window truncation.

## Not claimed

No fluid statement; no space lower bound; no universality; no robustness. The results are
specializations of `TerminalDecoding` and `DeterministicLumpability`; their value is that
the certificate now has a computer at one end and the defect at the other.
-/

noncomputable section

namespace SGC.Bridge.MachineCertificate

open Finset Matrix
open SGC SGC.Thermodynamics SGC.Renormalization.MeasureReentry
open SGC.Renormalization.KernelHorizon
open SGC.Bridge.TerminalDecoding SGC.Bridge.BlockRenormalization
open SGC.Bridge.DeterministicLumpability

attribute [local instance] Matrix.linftyOpNormedAddCommGroup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Theorem 2 -/

/-- The closure defect of a machine observed through `P` (max-row `L^1` norm). -/
def machineDefect (f : V → V) (P : Partition V) (pi : V → ℝ) : ℝ :=
  rowL1Norm (closureCommutator (detKernel f) P pi)

theorem machine_terminal_tv (f : V → V) (P : Partition V) {pi : V → ℝ}
    (hpi : ∀ x, 0 < pi x) (rho : ProbabilityRow V) (h : ℕ) :
    tv (actualLaw (detKernel f) P (detKernel_isStochastic f) rho h)
      (referenceLaw (detKernel f) P hpi (detKernel_isStochastic f) rho h) ≤
      min 1 (h * machineDefect f P pi / 2) :=
  kernel_horizon_tv (detKernel f) P hpi (detKernel_isStochastic f) rho h

/-- Exact factor map: zero budget, the quotient machine predicts exactly. -/
theorem machine_terminal_tv_of_descends (f : V → V) (P : Partition V) (hd : Descends f P)
    {pi : V → ℝ} (hpi : ∀ x, 0 < pi x) (rho : ProbabilityRow V) (h : ℕ) :
    tv (actualLaw (detKernel f) P (detKernel_isStochastic f) rho h)
      (referenceLaw (detKernel f) P hpi (detKernel_isStochastic f) rho h) = 0 := by
  apply le_antisymm _ (tv_nonneg _ _)
  have hb := machine_terminal_tv f P hpi rho h
  have hc : machineDefect f P pi = 0 := by
    unfold machineDefect
    rw [(closureCommutator_detKernel_eq_zero_iff f P hpi).mpr hd]
    simp [rowL1Norm]
  rw [hc] at hb
  simpa using hb

/-- Point mass on the configuration `x`. -/
def pointMass (x : V) : ProbabilityRow V where
  mass y := if y = x then 1 else 0
  nonneg y := by split_ifs <;> norm_num
  sum_one := by simp

/-- Deterministic machines have deterministic observations: the actual law after `h`
steps from `x` is the point mass at `quot_map (f^[h] x)`. -/
theorem machine_point_law (f : V → V) (P : Partition V) (x : V) (h : ℕ) (B : P.Quot) :
    actualLaw (detKernel f) P (detKernel_isStochastic f) (pointMass x) h B =
      if P.quot_map (f^[h] x) = B then 1 else 0 := by
  change ((pointMass x : V → ℝ) ᵥ* ((detKernel f) ^ h * lift_matrix P)) B = _
  rw [← Matrix.vecMul_vecMul]
  have hp : (pointMass x : V → ℝ) ᵥ* (detKernel f) ^ h =
      fun y => if y = f^[h] x then 1 else 0 := detKernel_vecMul_point f x h
  rw [hp]
  simp only [Matrix.vecMul, dotProduct, lift_matrix]
  rw [Finset.sum_eq_single (f^[h] x)]
  · simp
  · intro y _ hy
    simp [hy]
  · simp

/-- **The certificate on a machine.** If a fixed decoder is reliable on the quotient
machine's predictions (reference errors `<= beta_b`) and the budget fits
(`beta_b + min 1 (h c / 2) <= p_b`), it is reliable on the actual observations. -/
theorem machine_terminal_reliability (f : V → V) (P : Partition V) {pi : V → ℝ}
    (hpi : ∀ x, 0 < pi x) (mu : Bool → ProbabilityRow V) (d : Decoder P.Quot)
    (beta p : Bool → Set.Icc (0 : ℝ) 1) (h : ℕ)
    (hRef : ∀ b, d.error (referenceLaw (detKernel f) P hpi (detKernel_isStochastic f) (mu b) h) b
      ≤ beta b)
    (hBudget : ∀ b, (beta b : ℝ) + min 1 (h * machineDefect f P pi / 2) ≤ p b) :
    ∀ b, d.error (actualLaw (detKernel f) P (detKernel_isStochastic f) (mu b) h) b ≤ p b :=
  kernel_terminal_reliability (detKernel f) P hpi (detKernel_isStochastic f) mu d beta p h
    hRef hBudget

/-! ## Deterministic quotients do not mix -/

/-- A deterministic kernel with two distinct outputs has Dobrushin coefficient `1`. -/
theorem dobrushin_detKernel_eq_one (f : V → V) {x y : V} (hxy : f x ≠ f y) :
    dobrushin (detKernel f) = 1 := by
  apply le_antisymm (dobrushin_le_one (RowStochastic.of_existing (detKernel_isStochastic f)))
  have h := row_tv_le_dobrushin (detKernel f) x y
  have htv : tv (detKernel f x) (detKernel f y) = 1 := by
    unfold tv l1
    have : ∀ z, |detKernel f x z - detKernel f y z| =
        (if f x = z then 1 else 0) + (if f y = z then 1 else 0) := by
      intro z
      simp only [detKernel]
      by_cases hx : f x = z
      · have hy : f y ≠ z := fun h' => hxy (hx.trans h'.symm)
        simp [hx, hy]
      · by_cases hy : f y = z <;> simp [hx, hy]
    simp only [Pi.sub_apply, this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
    norm_num
  linarith

/-- When the quotient is itself a machine with two distinct outputs, the geometric
refinement of the terminal budget collapses to the linear one: the `epsilon > 0`
coarse-graining error of a computation can accumulate linearly in the number of steps. -/
theorem mixing_budget_trivial_of_quotient_machine (f : V → V) (P : Partition V)
    (hd : Descends f P) {pi : V → ℝ} (hpi : ∀ x, 0 < pi x)
    {A B : P.Quot} (hAB : quotMap f P hd A ≠ quotMap f P hd B) :
    dobrushin (CoarseGenerator (detKernel f) P pi) = 1 := by
  rw [coarseGenerator_detKernel_eq f P hd hpi]
  exact dobrushin_detKernel_eq_one _ hAB

/-! ## Theorem 1, general form: descent onto kept coordinates -/

section Window

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Partition of `A × B` by the kept coordinate `A`. -/
def fstPartition : Partition (A × B) where
  rel := ⟨fun x y => x.1 = y.1, ⟨fun _ => rfl, fun h => h.symm, fun h h' => h.trans h'⟩⟩
  decRel := fun x y => inferInstanceAs (Decidable (x.1 = y.1))

omit [Fintype A] [Fintype B] in
/-- **Window criterion.** `f` descends onto the kept coordinate iff the kept coordinate
evolves autonomously: information may flow from kept to forgotten, never back. -/
theorem descends_fst_iff (f : A × B → A × B) :
    Descends f (fstPartition (A := A) (B := B)) ↔
      ∀ x y : A × B, x.1 = y.1 → (f x).1 = (f y).1 := Iff.rfl

omit [Fintype A] [Fintype B] in
/-- Sufficient form: an explicit autonomous law `g` for the kept coordinate. -/
theorem descends_fst_of_autonomous (f : A × B → A × B) (g : A → A)
    (hg : ∀ x, (f x).1 = g x.1) : Descends f (fstPartition (A := A) (B := B)) := by
  intro x y h
  show (f x).1 = (f y).1
  rw [hg, hg, h]

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
/-- Blocks inherit autonomy: if the kept coordinate follows `g` in one step it follows
`g^[b]` in `b` steps, so every block map descends. -/
theorem iterate_fst_of_autonomous (f : A × B → A × B) (g : A → A)
    (hg : ∀ x, (f x).1 = g x.1) (b : ℕ) (x : A × B) : (f^[b] x).1 = g^[b] x.1 := by
  induction b generalizing x with
  | zero => rfl
  | succ b ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hg]

/-- Positive defect from a single leak: if some forgotten coordinate changes the next kept
coordinate, the coarse-graining by kept coordinates has strictly positive defect for every
positive reference measure. The `b`-step version says exactly when a window of the tape
fails to be an exact coarse description of a machine. -/
theorem defect_pos_of_leak (f : A × B → A × B) {a : A} {b₁ b₂ : B}
    (hleak : (f (a, b₁)).1 ≠ (f (a, b₂)).1) {pi : A × B → ℝ} (hpi : ∀ x, 0 < pi x) :
    0 < defectSq (detKernel f) (fstPartition (A := A) (B := B)) pi := by
  have hnd : ¬ Descends f (fstPartition (A := A) (B := B)) := fun h => hleak (h (a, b₁) (a, b₂) rfl)
  have hne : defectSq (detKernel f) fstPartition pi ≠ 0 :=
    fun h => hnd ((defectSq_detKernel_eq_zero_iff _ _ hpi).mp h)
  exact lt_of_le_of_ne (defectSq_nonneg _ _ fun x => (hpi x).le) hne.symm

end Window

/-! ## Theorem 1, concrete: a head-moving machine and its tape window

A one-tape machine in head-relative coordinates: configuration `(q, t)` with control state
`q : Q` and tape `t : ℤ → Γ` read relative to the head (cell `0` is under the head). One
step reads `t 0`, writes `w q (t 0)` there, moves to `nxt q (t 0)`, and shifts the tape by
the move `mv q (t 0) ∈ {-1, 0, 1}` so the head is again at `0`. This is Mathlib's `TM0`
semantics on `Tape` written out on `ℤ → Γ`; the state space is infinite, so only the
descent notion (which needs no finiteness) is used here.

**Window theorem** (`tmStep_iterate_window`): after `b` steps, the control state and the
tape on the window `|i| <= r - b` depend only on the initial control state and the
initial tape on `|i| <= r`. Hence the `b`-step block map descends onto the partition by
`(q, window of radius r)` *as a map into the window of radius `r - b`*
(`tmBlock_descends_shrink`): information enters from at most one cell per step, per side.
The exact **descent onto the same window** fails in general - the incoming cell is
forgotten - which is `defect_pos_of_leak` at scale; the block tower of *Two Horizons*
Theorem 2.5 (`truncate_pathShift`, depth `n+1` input for a depth-`n` output) was the
reviewer's observation of exactly this shrinkage. -/

section Locality

variable {Q Γ : Type*}

/-- Head-relative configuration. -/
abbrev TMCfg (Q Γ : Type*) := Q × (ℤ → Γ)

/-- One step of a head-relative machine: `nxt` next state, `w` written symbol,
`mv ∈ {-1,0,1}` head move. -/
def tmStep (nxt : Q → Γ → Q) (w : Q → Γ → Γ) (mv : Q → Γ → ℤ) (c : TMCfg Q Γ) : TMCfg Q Γ :=
  let a := c.2 0
  (nxt c.1 a, fun i => Function.update c.2 0 (w c.1 a) (i + mv c.1 a))

/-- Two tapes agree on the window of radius `r`. -/
def AgreeOn (r : ℤ) (t t' : ℤ → Γ) : Prop := ∀ i : ℤ, |i| ≤ r → t i = t' i

omit [Fintype V] [DecidableEq V] in
lemma agreeOn_mono {r r' : ℤ} (h : r' ≤ r) {t t' : ℤ → Γ} (ha : AgreeOn r t t') :
    AgreeOn r' t t' := fun i hi => ha i (hi.trans h)

/-- **One step shrinks the agreement window by at most one** (moves are bounded by `1`). -/
theorem tmStep_window (nxt : Q → Γ → Q) (w : Q → Γ → Γ) (mv : Q → Γ → ℤ)
    (hmv : ∀ q a, |mv q a| ≤ 1) {r : ℤ} (hr : 0 ≤ r)
    {c c' : TMCfg Q Γ} (hq : c.1 = c'.1) (ht : AgreeOn r c.2 c'.2) :
    (tmStep nxt w mv c).1 = (tmStep nxt w mv c').1 ∧
      AgreeOn (r - 1) (tmStep nxt w mv c).2 (tmStep nxt w mv c').2 := by
  have h0 : c.2 0 = c'.2 0 := ht 0 (by simpa using hr)
  refine ⟨?_, ?_⟩
  · simp only [tmStep]; rw [hq, h0]
  · intro i hi
    simp only [tmStep]
    rw [hq, h0]
    have hbound : |i + mv c'.1 (c'.2 0)| ≤ r := by
      calc |i + mv c'.1 (c'.2 0)| ≤ |i| + |mv c'.1 (c'.2 0)| := abs_add_le _ _
        _ ≤ (r - 1) + 1 := add_le_add hi (hmv _ _)
        _ = r := by ring
    by_cases hz : i + mv c'.1 (c'.2 0) = 0
    · rw [hz]; simp
    · rw [Function.update_of_ne hz, Function.update_of_ne hz]
      exact ht _ hbound

/-- **Window theorem.** After `b` steps, control state and the tape on the window of
radius `r - b` are determined by the initial control state and the window of radius `r`. -/
theorem tmStep_iterate_window (nxt : Q → Γ → Q) (w : Q → Γ → Γ) (mv : Q → Γ → ℤ)
    (hmv : ∀ q a, |mv q a| ≤ 1) (b : ℕ) {r : ℤ} (hr : (b : ℤ) ≤ r)
    {c c' : TMCfg Q Γ} (hq : c.1 = c'.1) (ht : AgreeOn r c.2 c'.2) :
    ((tmStep nxt w mv)^[b] c).1 = ((tmStep nxt w mv)^[b] c').1 ∧
      AgreeOn (r - b) ((tmStep nxt w mv)^[b] c).2 ((tmStep nxt w mv)^[b] c').2 := by
  induction b generalizing c c' r with
  | zero => simpa using ⟨hq, ht⟩
  | succ b ih =>
    have hr0 : (0 : ℤ) ≤ r := le_trans (by positivity) hr
    obtain ⟨hq1, ht1⟩ := tmStep_window nxt w mv hmv hr0 hq ht
    have hr1 : (b : ℤ) ≤ r - 1 := by push_cast at hr; linarith
    obtain ⟨hq2, ht2⟩ := ih hr1 hq1 ht1
    refine ⟨?_, ?_⟩
    · simpa [Function.iterate_succ_apply] using hq2
    · have : r - ((b + 1 : ℕ) : ℤ) = r - 1 - b := by push_cast; ring
      rw [this]
      simpa [Function.iterate_succ_apply] using ht2

/-- Equivalence of configurations by control state and tape window of radius `r`
(an equivalence relation; stated directly because `TMCfg` has no decidable equality). -/
def WindowRel (r : ℤ) (c c' : TMCfg Q Γ) : Prop := c.1 = c'.1 ∧ AgreeOn r c.2 c'.2

omit [Fintype V] [DecidableEq V] in
lemma windowRel_equivalence (r : ℤ) : Equivalence (WindowRel (Q := Q) (Γ := Γ) r) where
  refl _ := ⟨rfl, fun _ _ => rfl⟩
  symm h := ⟨h.1.symm, fun i hi => (h.2 i hi).symm⟩
  trans h h' := ⟨h.1.trans h'.1, fun i hi => (h.2 i hi).trans (h'.2 i hi)⟩

/-- **The block map descends onto the shrunken window**: `x ~_r y → f^[b] x ~_{r-b} f^[b] y`.
Exact descent onto the *same* window is the `b = 0` case only; for `b > 0` the incoming
cells are the leak (`defect_pos_of_leak`). -/
theorem tmBlock_descends_shrink (nxt : Q → Γ → Q) (w : Q → Γ → Γ) (mv : Q → Γ → ℤ)
    (hmv : ∀ q a, |mv q a| ≤ 1) (b : ℕ) {r : ℤ} (hr : (b : ℤ) ≤ r)
    {c c' : TMCfg Q Γ} (h : WindowRel r c c') :
    WindowRel (r - b) ((tmStep nxt w mv)^[b] c) ((tmStep nxt w mv)^[b] c') :=
  tmStep_iterate_window nxt w mv hmv b hr h.1 h.2

end Locality

end SGC.Bridge.MachineCertificate

end
