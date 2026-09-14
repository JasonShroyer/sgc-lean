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
  is the point mass at `quot_map (f^[h] x)`. For a *deterministic* decoder and a point-mass
  input this makes every terminal error `0` or `1`; a randomized decoder can still have
  fractional error, and TV error transfer applies to it unchanged;
* `machine_terminal_reliability` - the per-class reliability transfer, instantiated.

## One-step Dobrushin coefficient of a deterministic quotient

`dobrushin_detKernel_eq_one`: a deterministic kernel with two distinct outputs has
one-step Dobrushin coefficient `1`. `mixing_budget_trivial_of_quotient_machine` applies
this to the quotient machine of an *exactly lumpable* coarse-graining - where `c = 0`, so
the budget is zero anyway. It therefore establishes **neither** positive error
accumulation **nor** persistent non-mixing: `Q^k = T_{g^k}` can have coefficient `0` as
soon as `g^k` is constant (`Regression.collapse_dobrushin_two_zero`). An earlier docstring
read this as "the coarse-graining error of a computation accumulates linearly"; that was
an upper bound misread as growth and is withdrawn (external review, 2026-09-13).

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
same tape on `|i| <= r - b`" (for `r >= b`). This is a **uniform sufficiency** statement:
a window of radius `r` always determines a window of radius `r - b` after `b` steps. It is
**not** necessary for a given machine (the identity machine preserves any window forever),
and it is worst-case sharp only for centered windows over unrestricted tapes (a pure shift
with two symbols needs radius exactly `s + b` to determine `[-s, s]`; that necessity
statement is not formalized here). The incoming cells are the potential leak
(`defect_pos_of_leak`; `reader_defect_pos` is the one-cell prototype), matching the
reviewer's observation about `truncate_pathShift` in the Bernoulli tower.

**Scope of the machine model.** `tmStep` is a *total* step that writes and moves
simultaneously. Mathlib's `TM0` step is partial (`Option`) and performs a move *or* a
write per step. The window theorem holds for the custom model as stated; a bridge to
`TM0` execution (simulation, halting, step-count overhead) is a separate adapter and is
not supplied here. The state space is infinite, so only the descent notion is used; the
finite-`V` defect theorems apply to any finite window truncation.

## Block descent does not exclude intermediate leakage

`Regression.swap_block_descends_not_step`: `f (a, b) = (b, a)` has `f^[2] = id`, which
descends onto the first coordinate, while `f` itself does not. Block descent guarantees
endpoint independence only; one-step descent implies descent of all iterates, not
conversely. Moreover the canonical kernel of `f^[2]` is the identity while
`(Q[f])^2` is the all-`1/2` matrix (`Regression.swap_Q_sq_ne_Q_block`): a block theorem
must not equate `Q[f^[b]]` with `Q[f]^b`.

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

/-! ## The deterministic defect gap

External review (2026-09-13) deduced from the definitions that the closure defect of a
deterministic machine cannot be small without being zero. Formalized here.

For each configuration `x` with output fiber `B_x = q (f x)`, the row of the closure
commutator is `[B = B_x] - Q(q x, B)`, whose `L^1` mass is `2 (1 - Q(q x, B_x))`
(`detKernel_row_residual_l1`). Strict positivity of `pi` gives `Q(q x, B_x) > 0`, so every
row has mass `< 2` (`machineDefect_lt_two`). If descent fails, some fiber has two distinct
outputs, one of which has conditional mass `<= 1/2`, so that row has mass `>= 1`
(`machineDefect_ge_one_of_not_descends`). Hence

    `c = 0  ∨  1 <= c < 2`            (`machineDefect_gap`).

Consequence for the *linear* certificate (`machineDefect_linear_budget_vacuous`): in every
nonexact deterministic case the budget `min 1 (h c / 2)` is `>= 1/2` at `h = 1` and equals
`1` for `h >= 2`, so the uniform additive argument `beta + budget <= p` cannot certify any
target `p < 1/2` at a positive horizon. This is a limitation of *that certificate*, not a
lower bound on actual error: law-specific or contraction-aware estimates can be sharp
(`Regression.reader_geometric_budget_half`). -/

section Gap

/-- Row of the deterministic closure commutator: `[B = q (f x)] - Q(q x, B)`. -/
lemma detKernel_commutator_entry (f : V → V) (P : Partition V) (pi : V → ℝ) (x : V)
    (B : P.Quot) :
    closureCommutator (detKernel f) P pi x B =
      (if P.quot_map (f x) = B then 1 else 0) -
        CoarseGenerator (detKernel f) P pi (P.quot_map x) B := by
  rw [closureCommutator_entry]
  unfold SGC.Renormalization.MeasureReentry.residual
  rw [row_sum_block_detKernel]

lemma coarse_entry_le_one (f : V → V) (P : Partition V) {pi : V → ℝ}
    (hpi : ∀ x, 0 < pi x) (A B : P.Quot) :
    CoarseGenerator (detKernel f) P pi A B ≤ 1 := by
  have hQ := coarseKernel_isStochastic (detKernel f) P hpi (detKernel_isStochastic f)
  have := hQ.row_sum_one A
  have hle := Finset.single_le_sum (fun B' _ => hQ.nonneg A B') (Finset.mem_univ B)
  linarith

/-- The `L^1` mass of a deterministic commutator row is `2 (1 - Q(q x, q (f x)))`. -/
theorem detKernel_row_residual_l1 (f : V → V) (P : Partition V) {pi : V → ℝ}
    (hpi : ∀ x, 0 < pi x) (x : V) :
    l1 (closureCommutator (detKernel f) P pi x) =
      2 * (1 - CoarseGenerator (detKernel f) P pi (P.quot_map x) (P.quot_map (f x))) := by
  have hQ := coarseKernel_isStochastic (detKernel f) P hpi (detKernel_isStochastic f)
  have hrow : ∀ B, |closureCommutator (detKernel f) P pi x B| =
      (if P.quot_map (f x) = B
        then 1 - CoarseGenerator (detKernel f) P pi (P.quot_map x) B
        else CoarseGenerator (detKernel f) P pi (P.quot_map x) B) := by
    intro B
    rw [detKernel_commutator_entry]
    by_cases hB : P.quot_map (f x) = B
    · simp [hB, abs_of_nonneg (sub_nonneg.mpr (coarse_entry_le_one f P hpi _ _))]
    · simp [hB, abs_of_nonneg (hQ.nonneg _ B)]
  unfold l1
  simp_rw [hrow]
  have h1 : ∀ B, (if P.quot_map (f x) = B
      then 1 - CoarseGenerator (detKernel f) P pi (P.quot_map x) B
      else CoarseGenerator (detKernel f) P pi (P.quot_map x) B) =
      (if P.quot_map (f x) = B then (1 : ℝ) else 0) +
        CoarseGenerator (detKernel f) P pi (P.quot_map x) B -
        2 * (if P.quot_map (f x) = B then CoarseGenerator (detKernel f) P pi (P.quot_map x) B
          else 0) := by
    intro B; split_ifs <;> ring
  simp_rw [h1]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hQ.row_sum_one]
  simp
  ring

/-- The output fiber of `x` carries at least the conditional mass of `x` itself. -/
lemma coarse_output_mass_pos (f : V → V) (P : Partition V) {pi : V → ℝ}
    (hpi : ∀ x, 0 < pi x) (x : V) :
    0 < CoarseGenerator (detKernel f) P pi (P.quot_map x) (P.quot_map (f x)) := by
  rw [coarseGenerator_eq_conditional_exit_average _ P hpi]
  have hpos : 0 < pi_bar P pi (P.quot_map x) := pi_bar_pos P hpi _
  apply mul_pos (one_div_pos.mpr hpos)
  have hterm : ∀ y, 0 ≤ (if P.quot_map y = P.quot_map x
      then pi y * row_sum_block (detKernel f) P y (P.quot_map (f x)) else 0) := by
    intro y
    split_ifs
    · rw [row_sum_block_detKernel]
      apply mul_nonneg (hpi y).le
      split_ifs <;> norm_num
    · exact le_rfl
  have hx : 0 < (if P.quot_map x = P.quot_map x
      then pi x * row_sum_block (detKernel f) P x (P.quot_map (f x)) else 0) := by
    rw [if_pos rfl, row_sum_block_detKernel, if_pos rfl, mul_one]
    exact hpi x
  exact lt_of_lt_of_le hx (Finset.single_le_sum (fun y _ => hterm y) (Finset.mem_univ x))

/-- Every row of a deterministic commutator has `L^1` mass strictly below `2`. -/
theorem machineDefect_lt_two [Nonempty V] (f : V → V) (P : Partition V) {pi : V → ℝ}
    (hpi : ∀ x, 0 < pi x) : machineDefect f P pi < 2 := by
  obtain ⟨x0, _, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun x => CoarseGenerator (detKernel f) P pi (P.quot_map x) (P.quot_map (f x)))
    Finset.univ_nonempty
  have hm := coarse_output_mass_pos f P hpi x0
  have hQle := coarse_entry_le_one f P hpi (P.quot_map x0) (P.quot_map (f x0))
  have hle : machineDefect f P pi ≤
      2 * (1 - CoarseGenerator (detKernel f) P pi (P.quot_map x0) (P.quot_map (f x0))) := by
    apply rowL1Norm_le _ (by linarith)
    intro x
    rw [detKernel_row_residual_l1 f P hpi x]
    linarith [hmin x (Finset.mem_univ x)]
  linarith

/-- If descent fails, some row has `L^1` mass at least `1`. -/
theorem machineDefect_ge_one_of_not_descends (f : V → V) (P : Partition V) {pi : V → ℝ}
    (hpi : ∀ x, 0 < pi x) (hnd : ¬ Descends f P) : 1 ≤ machineDefect f P pi := by
  have hQ := coarseKernel_isStochastic (detKernel f) P hpi (detKernel_isStochastic f)
  unfold Descends at hnd
  push_neg at hnd
  obtain ⟨x, y, hxy, hne⟩ := hnd
  have hA : P.quot_map y = P.quot_map x := Quotient.sound (P.rel.symm hxy)
  have hBne : P.quot_map (f x) ≠ P.quot_map (f y) := fun h => hne (Quotient.exact h)
  have hsum : CoarseGenerator (detKernel f) P pi (P.quot_map x) (P.quot_map (f x)) +
      CoarseGenerator (detKernel f) P pi (P.quot_map x) (P.quot_map (f y)) ≤ 1 := by
    have h1 := hQ.row_sum_one (P.quot_map x)
    rw [← Finset.sum_pair hBne, ← h1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun B _ _ => hQ.nonneg _ B)
  have hrow_x := detKernel_row_residual_l1 f P hpi x
  have hrow_y := detKernel_row_residual_l1 f P hpi y
  rw [hA] at hrow_y
  have hx := row_l1_le_rowL1Norm (closureCommutator (detKernel f) P pi) x
  have hy := row_l1_le_rowL1Norm (closureCommutator (detKernel f) P pi) y
  unfold machineDefect
  by_cases hhalf : CoarseGenerator (detKernel f) P pi (P.quot_map x) (P.quot_map (f x)) ≤ 1 / 2
  · linarith
  · linarith

/-- **The deterministic defect gap**: `c = 0 ∨ 1 <= c < 2`. -/
theorem machineDefect_gap [Nonempty V] (f : V → V) (P : Partition V) {pi : V → ℝ}
    (hpi : ∀ x, 0 < pi x) :
    machineDefect f P pi = 0 ∨ (1 ≤ machineDefect f P pi ∧ machineDefect f P pi < 2) := by
  by_cases hd : Descends f P
  · left
    unfold machineDefect
    rw [(closureCommutator_detKernel_eq_zero_iff f P hpi).mpr hd]
    simp [rowL1Norm]
  · right
    exact ⟨machineDefect_ge_one_of_not_descends f P hpi hd, machineDefect_lt_two f P hpi⟩

/-- In every nonexact deterministic case the linear budget is `>= 1/2` at `h = 1` and `1`
for `h >= 2`: the uniform additive certificate cannot certify `p < 1/2` at any positive
horizon. A limitation of the linear certificate, not a bound on actual error. -/
theorem machineDefect_linear_budget_vacuous (f : V → V) (P : Partition V) {pi : V → ℝ}
    (hpi : ∀ x, 0 < pi x) (hnd : ¬ Descends f P) :
    1 / 2 ≤ min 1 ((1 : ℕ) * machineDefect f P pi / 2) ∧
      ∀ h : ℕ, 2 ≤ h → min 1 (h * machineDefect f P pi / 2) = 1 := by
  have hc := machineDefect_ge_one_of_not_descends f P hpi hnd
  refine ⟨le_min (by norm_num) (by simp; linarith), fun h hh => ?_⟩
  apply min_eq_left
  have : (2 : ℝ) ≤ h := by exact_mod_cast hh
  nlinarith

end Gap

/-! ## The exact terminal error of a machine, and the all-or-nothing theorem

The gap says the uniform linear certificate is void for every nonexact machine. Two results
replace it with content.

**Exact error** (`machine_point_tv_exact`). From a point input `x`, the terminal TV between
the actual observation and the reference prediction after `h` steps is *exactly*

    `1 - (Q^h) (q x) (q (f^[h] x))`

- one minus the reference mass on the true coarse endpoint. This is an equality, computable
for any concrete machine, and it is what any law-specific certificate for a computation
must bound. `machine_point_tv_eq_zero_iff`: it vanishes iff the reference predicts the
endpoint with probability one.

**All-or-nothing** (`descends_iff_defect_lt_one`, `linear_certificate_implies_descends`).
For a deterministic machine, `Descends f P <-> c < 1`. Hence if the uniform additive
certificate `beta + min 1 (h c / 2) <= p` certifies *any* target `p < 1/2` at *any*
horizon `h >= 1`, the coarse-graining is an exact factor map. There is no "approximately
computing" quotient at the uniform level: a coarse description of a computation is exact
or its uniform certificate is void. Graded guarantees for computations must therefore be
law-specific (the exact formula above) or contraction-aware (`kernel_horizon_tv_mixing`),
never uniform-linear. -/

section Exact

/-- The reference law from a point input is the row `(Q^h) (q x)`. -/
lemma machine_point_reference (f : V → V) (P : Partition V) {pi : V → ℝ}
    (hpi : ∀ x, 0 < pi x) (x : V) (h : ℕ) (B : P.Quot) :
    referenceLaw (detKernel f) P hpi (detKernel_isStochastic f) (pointMass x) h B =
      (CoarseGenerator (detKernel f) P pi ^ h) (P.quot_map x) B := by
  change ((pointMass x : V → ℝ) ᵥ* (lift_matrix P * (CoarseGenerator (detKernel f) P pi) ^ h)) B = _
  rw [← Matrix.vecMul_vecMul]
  have hJ : (pointMass x : V → ℝ) ᵥ* lift_matrix P =
      fun A => if P.quot_map x = A then 1 else 0 := by
    ext A
    simp only [Matrix.vecMul, dotProduct, pointMass, lift_matrix]
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy; simp [hy]
    · simp
  rw [hJ]
  simp only [Matrix.vecMul, dotProduct]
  rw [Finset.sum_eq_single (P.quot_map x)]
  · simp
  · intro A _ hA; simp [Ne.symm hA]
  · simp

/-- TV between a point mass and a probability row is one minus the row's mass at the point. -/
lemma tv_point_prob {X : Type*} [Fintype X] [DecidableEq X] (x0 : X) (rho : ProbabilityRow X) :
    tv (fun y => if y = x0 then (1 : ℝ) else 0) rho = 1 - rho x0 := by
  have hle : rho x0 ≤ 1 := by
    have := rho.sum_one
    have h := Finset.single_le_sum (fun y _ => rho.nonneg y) (Finset.mem_univ x0)
    linarith
  unfold tv l1
  have hterm : ∀ y, |(fun y => if y = x0 then (1 : ℝ) else 0) y - rho y| =
      (if y = x0 then 1 - rho y else rho y) := by
    intro y
    by_cases hy : y = x0
    · simp [hy, abs_of_nonneg (sub_nonneg.mpr hle)]
    · simp [hy, abs_of_nonneg (rho.nonneg y)]
  simp only [Pi.sub_apply]
  simp_rw [hterm]
  have hsplit : ∀ y, (if y = x0 then 1 - rho y else rho y) =
      (if y = x0 then (1 : ℝ) else 0) + rho y - 2 * (if y = x0 then rho y else 0) := by
    intro y; split_ifs <;> ring
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, rho.sum_one]
  simp
  ring

/-- **Exact terminal error of a machine from a point input.** -/
theorem machine_point_tv_exact (f : V → V) (P : Partition V) {pi : V → ℝ}
    (hpi : ∀ x, 0 < pi x) (x : V) (h : ℕ) :
    tv (actualLaw (detKernel f) P (detKernel_isStochastic f) (pointMass x) h)
      (referenceLaw (detKernel f) P hpi (detKernel_isStochastic f) (pointMass x) h) =
      1 - (CoarseGenerator (detKernel f) P pi ^ h) (P.quot_map x) (P.quot_map (f^[h] x)) := by
  have hact : (actualLaw (detKernel f) P (detKernel_isStochastic f) (pointMass x) h : P.Quot → ℝ) =
      fun B => if B = P.quot_map (f^[h] x) then 1 else 0 := by
    funext B
    rw [machine_point_law]
    simp only [eq_comm]
  have hval := tv_point_prob (P.quot_map (f^[h] x))
    (referenceLaw (detKernel f) P hpi (detKernel_isStochastic f) (pointMass x) h)
  rw [machine_point_reference f P hpi x h] at hval
  rw [← hval]
  congr 1

/-- The exact error vanishes iff the reference predicts the true endpoint with probability one. -/
theorem machine_point_tv_eq_zero_iff (f : V → V) (P : Partition V) {pi : V → ℝ}
    (hpi : ∀ x, 0 < pi x) (x : V) (h : ℕ) :
    tv (actualLaw (detKernel f) P (detKernel_isStochastic f) (pointMass x) h)
      (referenceLaw (detKernel f) P hpi (detKernel_isStochastic f) (pointMass x) h) = 0 ↔
      (CoarseGenerator (detKernel f) P pi ^ h) (P.quot_map x) (P.quot_map (f^[h] x)) = 1 := by
  rw [machine_point_tv_exact f P hpi x h]
  constructor <;> intro hh <;> linarith

/-- **All-or-nothing**: a deterministic machine's coarse-graining is exact iff its defect is
below `1`. -/
theorem descends_iff_defect_lt_one [Nonempty V] (f : V → V) (P : Partition V) {pi : V → ℝ}
    (hpi : ∀ x, 0 < pi x) : Descends f P ↔ machineDefect f P pi < 1 := by
  constructor
  · intro hd
    have : machineDefect f P pi = 0 := by
      unfold machineDefect
      rw [(closureCommutator_detKernel_eq_zero_iff f P hpi).mpr hd]
      simp [rowL1Norm]
    linarith
  · intro hc
    by_contra hnd
    linarith [machineDefect_ge_one_of_not_descends f P hpi hnd]

/-- **The uniform certificate is a factor-map detector.** If the additive linear
certificate certifies any target below `1/2` at any positive horizon, the coarse-graining is
an exact factor map. -/
theorem linear_certificate_implies_descends [Nonempty V] (f : V → V) (P : Partition V)
    {pi : V → ℝ} (hpi : ∀ x, 0 < pi x) {beta p : ℝ} (hbeta : 0 ≤ beta) (hp : p < 1 / 2)
    {h : ℕ} (hh : 1 ≤ h) (hcert : beta + min 1 (h * machineDefect f P pi / 2) ≤ p) :
    Descends f P := by
  rw [descends_iff_defect_lt_one f P hpi]
  have hmin : min 1 (h * machineDefect f P pi / 2) < 1 / 2 := by linarith
  have hlt : h * machineDefect f P pi / 2 < 1 / 2 := by
    rcases min_choice 1 (h * machineDefect f P pi / 2) with hm | hm
    · rw [hm] at hmin; norm_num at hmin
    · rw [hm] at hmin; exact hmin
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hc0 : 0 ≤ machineDefect f P pi := norm_nonneg _
  nlinarith

end Exact

/-! ## The confidently-wrong regime: zero Dobrushin coefficient of the reference kernel

`dobrushin_zero_iff_rows_equal`: the canonical coarse kernel has Dobrushin coefficient `0`
iff all its rows coincide - the coarse variable carries no information about its own
successor. In that regime the reference forecast is the same fixed row `rho` at every
positive horizon (`pow_row_const_of_rows_equal`), so from a point input the exact error is
`1 - rho (q (f^[h] x))` for every `h >= 1` (`machine_error_of_dobrushin_zero`): **bounded,
non-accumulating, and generally nonzero**. This is the regime in which a coarse observer is
confidently and boundedly wrong: the reference mixes instantly while the fine machine is
deterministic and never forgets its input. The contraction-aware budget
`(c/2) * sum_{j<h} delta^j = c/2` is the right certificate here, and on the reader class it
is attained (`Regression.reader_budget_sharp`). -/

section ConfidentlyWrong

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
theorem dobrushin_zero_iff_rows_equal (M : Matrix X X ℝ) :
    dobrushin M = 0 ↔ ∀ x y, M x = M y := by
  constructor
  · intro h x y
    have hn : rowL1Norm (rowDifferences M) = 0 := by unfold dobrushin at h; linarith
    have hz : rowDifferences M = 0 := by
      unfold rowL1Norm at hn
      exact norm_eq_zero.mp hn
    funext z
    have := congrFun (congrFun hz (x, y)) z
    simp only [rowDifferences, Matrix.zero_apply] at this
    linarith
  · intro h
    have hz : rowDifferences M = 0 := by
      ext xy z
      simp only [rowDifferences, Matrix.zero_apply]
      rw [h xy.1 xy.2]; ring
    unfold dobrushin rowL1Norm
    rw [hz, norm_zero, zero_div]

/-- With all rows equal, every positive power has the same constant rows. -/
theorem pow_row_const_of_rows_equal (M : Matrix X X ℝ) (hM : RowStochastic M)
    (hrows : ∀ x y, M x = M y) (h : ℕ) (hh : 1 ≤ h) (x x' : X) :
    (M ^ h) x = M x' := by
  induction h with
  | zero => omega
  | succ h ih =>
    rcases Nat.eq_zero_or_pos h with h0 | hpos
    · subst h0; simpa using hrows x x'
    · funext z
      rw [pow_succ, Matrix.mul_apply]
      have hrow : ∀ c, M c z = M x' z := fun c => congrFun (hrows c x') z
      simp_rw [hrow, ← Finset.sum_mul]
      have := (hM.pow h).sum_one x
      rw [this, one_mul]

/-- **Confidently wrong**: with a zero-Dobrushin reference kernel the exact error from a point
input is `1 - Q (any) (q (f^[h] x))` at every positive horizon - bounded and non-accumulating. -/
theorem machine_error_of_dobrushin_zero (f : V → V) (P : Partition V) {pi : V → ℝ}
    (hpi : ∀ x, 0 < pi x) (hδ : dobrushin (CoarseGenerator (detKernel f) P pi) = 0)
    (x : V) (h : ℕ) (hh : 1 ≤ h) (A : P.Quot) :
    tv (actualLaw (detKernel f) P (detKernel_isStochastic f) (pointMass x) h)
      (referenceLaw (detKernel f) P hpi (detKernel_isStochastic f) (pointMass x) h) =
      1 - CoarseGenerator (detKernel f) P pi A (P.quot_map (f^[h] x)) := by
  rw [machine_point_tv_exact f P hpi x h]
  have hQ := RowStochastic.of_existing (coarseKernel_isStochastic (detKernel f) P hpi
    (detKernel_isStochastic f))
  have hrows := (dobrushin_zero_iff_rows_equal _).mp hδ
  rw [pow_row_const_of_rows_equal _ hQ hrows h hh (P.quot_map x) A]

end ConfidentlyWrong

/-! ## Deterministic quotients do not mix (one step, exact case) -/

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

/-- When the coarse-graining is exact and the quotient machine has two distinct outputs,
the one-step Dobrushin coefficient of the canonical coarse kernel is `1`. Since `c = 0`
under `Descends`, this says nothing about error accumulation; it only records that the
geometric refinement has no one-step advantage in the exact deterministic case. -/
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
the move `mv q (t 0) ∈ {-1, 0, 1}` so the head is again at `0`. This is a total,
simultaneous write-and-move model in the spirit of Mathlib's `TM0` on `Tape`, not `TM0`
itself (see the module docstring); the state space is infinite, so only the descent notion
(which needs no finiteness) is used here.

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

/-- **The block map descends onto the shrunken window**: `x ~_r y → f^[b] x ~_{r-b} f^[b] y`
for `r >= b`. Sufficient, uniformly over machines with `|mv| <= 1`; not necessary for a
given machine. The incoming cells are the potential leak (`defect_pos_of_leak`). -/
theorem tmBlock_descends_shrink (nxt : Q → Γ → Q) (w : Q → Γ → Γ) (mv : Q → Γ → ℤ)
    (hmv : ∀ q a, |mv q a| ≤ 1) (b : ℕ) {r : ℤ} (hr : (b : ℤ) ≤ r)
    {c c' : TMCfg Q Γ} (h : WindowRel r c c') :
    WindowRel (r - b) ((tmStep nxt w mv)^[b] c) ((tmStep nxt w mv)^[b] c') :=
  tmStep_iterate_window nxt w mv hmv b hr h.1 h.2

end Locality

/-! ## Regressions from the external review of this module (2026-09-13) -/

namespace Regression

open SGC.Bridge.DeterministicLumpability.Regression

/-- The reader machine coarse-grained by state: defect exactly `1` (the gap's lower end). -/
theorem reader_defect_eq_one {pi : Cfg → ℝ} (hpi : ∀ x, 0 < pi x) :
    machineDefect reader byState pi ≥ 1 :=
  machineDefect_ge_one_of_not_descends reader byState hpi reader_not_descends

/-- With uniform weights the reader's canonical coarse kernel is the all-`1/2` matrix, whose
Dobrushin coefficient is `0`: the *reference* kernel mixes instantly while the fine
dynamics (two fixed points) never forgets its input. Mixing of the reference kernel is not
mixing of the actual projected process. -/
theorem reader_coarse_row (b : Bool) (B : byState.Quot) :
    CoarseGenerator (detKernel reader) byState (fun _ => (1 : ℝ)) (byState.quot_map (b, b)) B
      = 1 / 2 := by
  obtain ⟨⟨s, t⟩, hB⟩ := Quotient.exists_rep B
  have hB' : byState.quot_map (s, t) = B := hB
  rw [← hB', coarseGenerator_eq_conditional_exit_average _ byState (fun _ => one_pos)]
  have hbar : pi_bar byState (fun _ => (1 : ℝ)) (byState.quot_map (b, b)) = 2 := by
    unfold pi_bar
    have : ∀ x : Cfg, (byState.quot_map x = byState.quot_map (b, b)) ↔ x.1 = b := by
      intro x; exact quot_map_eq_iff byState x (b, b)
    simp only [this]
    cases b <;> simp <;> exact_mod_cast (by decide : _)
  rw [hbar]
  have hsum : (∑ x : Cfg, if byState.quot_map x = byState.quot_map (b, b)
      then (1 : ℝ) * row_sum_block (detKernel reader) byState x (byState.quot_map (s, t)) else 0)
      = 1 := by
    have h1 : ∀ x : Cfg, (byState.quot_map x = byState.quot_map (b, b)) ↔ x.1 = b := by
      intro x; exact quot_map_eq_iff byState x (b, b)
    have h2 : ∀ x : Cfg, row_sum_block (detKernel reader) byState x (byState.quot_map (s, t))
        = if x.2 = s then 1 else 0 := by
      intro x
      rw [row_sum_block_detKernel]
      have : (byState.quot_map (reader x) = byState.quot_map (s, t)) ↔ x.2 = s := by
        rw [quot_map_eq_iff]; rfl
      simp only [this]
    simp only [h1, h2, one_mul]
    cases b <;> cases s <;> simp [Fintype.sum_prod_type]
  rw [hsum]
  norm_num

/-- Collapse: `f 0 = 0, f 1 = 0, f 2 = 1` on `Fin 3` with the discrete partition. Descent
holds (`c = 0`), the one-step coarse kernel has Dobrushin coefficient `1` (two distinct
outputs), yet `f^[2]` is constant so the two-step kernel has coefficient `0`. One-step
non-mixing does not persist. -/
def collapse : Fin 3 → Fin 3 := ![0, 0, 1]

theorem collapse_sq_const (x : Fin 3) : collapse^[2] x = 0 := by
  fin_cases x <;> rfl

theorem collapse_dobrushin_one : dobrushin (detKernel collapse) = 1 :=
  dobrushin_detKernel_eq_one collapse (x := 0) (y := 2) (by decide)

theorem collapse_dobrushin_two_zero : dobrushin ((detKernel collapse) ^ 2) = 0 := by
  rw [detKernel_pow]
  have hrd : rowDifferences (detKernel (collapse^[2])) = 0 := by
    ext xy y
    have h1 := collapse_sq_const xy.1
    have h2 := collapse_sq_const xy.2
    simp only [rowDifferences, detKernel, Matrix.zero_apply]
    rw [h1, h2, sub_self]
  unfold dobrushin rowL1Norm
  rw [hrd, norm_zero, zero_div]

/-- Swap: `f (a, b) = (b, a)`. `f^[2] = id` descends onto the first coordinate; `f` does
not. Block descent is endpoint-only. -/
def swap2 (x : Bool × Bool) : Bool × Bool := (x.2, x.1)

theorem swap_block_descends_not_step :
    Descends (swap2^[2]) (fstPartition (A := Bool) (B := Bool)) ∧
      ¬ Descends swap2 (fstPartition (A := Bool) (B := Bool)) := by
  refine ⟨fun x y h => ?_, fun h => ?_⟩
  · show (swap2^[2] x).1 = (swap2^[2] y).1
    simpa [swap2] using h
  · have := h (false, false) (false, true) rfl
    simp [swap2] at this

/-- The canonical kernel of the block `f^[2] = id` is the identity, while the square of the
canonical kernel of `f` is the all-`1/2` matrix: `Q[f^[2]] ≠ Q[f]^2`. -/
theorem swap_Q_sq_ne_Q_block :
    (CoarseGenerator (detKernel swap2) fstPartition (fun _ => (1 : ℝ))) ^ 2 ≠
      CoarseGenerator (detKernel (swap2^[2])) fstPartition (fun _ => (1 : ℝ)) := by
  intro h
  have hid : (swap2^[2]) = id := by funext x; cases x; rfl
  have hdesc : Descends (swap2^[2]) (fstPartition (A := Bool) (B := Bool)) :=
    swap_block_descends_not_step.1
  rw [coarseGenerator_detKernel_eq _ _ hdesc (fun _ => one_pos)] at h
  -- the block quotient is the identity map, so its kernel has a diagonal entry 1
  have hdiag : detKernel (quotMap (swap2^[2]) fstPartition hdesc)
      (fstPartition.quot_map (false, false)) (fstPartition.quot_map (false, false)) = 1 := by
    simp only [detKernel, quotMap_mk]
    exact if_pos rfl
  -- but Q[f] has all rows equal (both fibers send half their mass to each output), so Q^2
  -- has that same entry 1/2
  have hQ : ∀ A B, CoarseGenerator (detKernel swap2) fstPartition (fun _ => (1 : ℝ)) A B = 1 / 2 := by
    intro A B
    obtain ⟨⟨a, b⟩, hA⟩ := Quotient.exists_rep A
    obtain ⟨⟨c, d⟩, hB⟩ := Quotient.exists_rep B
    have hA' : fstPartition.quot_map (a, b) = A := hA
    have hB' : fstPartition.quot_map (c, d) = B := hB
    rw [← hA', ← hB', coarseGenerator_eq_conditional_exit_average _ fstPartition (fun _ => one_pos)]
    have hbar : pi_bar fstPartition (fun _ => (1 : ℝ)) (fstPartition.quot_map (a, b)) = 2 := by
      unfold pi_bar
      have : ∀ x : Bool × Bool,
          (fstPartition.quot_map x = fstPartition.quot_map (a, b)) ↔ x.1 = a := by
        intro x; exact quot_map_eq_iff fstPartition x (a, b)
      simp only [this]
      cases a <;> simp <;> exact_mod_cast (by decide : _)
    have hsum : (∑ x : Bool × Bool, if fstPartition.quot_map x = fstPartition.quot_map (a, b)
        then (1 : ℝ) * row_sum_block (detKernel swap2) fstPartition x (fstPartition.quot_map (c, d))
        else 0) = 1 := by
      have h1 : ∀ x : Bool × Bool,
          (fstPartition.quot_map x = fstPartition.quot_map (a, b)) ↔ x.1 = a := by
        intro x; exact quot_map_eq_iff fstPartition x (a, b)
      have h2 : ∀ x : Bool × Bool, row_sum_block (detKernel swap2) fstPartition x
          (fstPartition.quot_map (c, d)) = if x.2 = c then 1 else 0 := by
        intro x
        rw [row_sum_block_detKernel]
        have : (fstPartition.quot_map (swap2 x) = fstPartition.quot_map (c, d)) ↔ x.2 = c := by
          rw [quot_map_eq_iff]; rfl
        simp only [this]
      simp only [h1, h2, one_mul]
      cases a <;> cases c <;> simp [Fintype.sum_prod_type]
    rw [hbar, hsum]
    norm_num
  have hsq : ((CoarseGenerator (detKernel swap2) fstPartition (fun _ => (1 : ℝ))) ^ 2)
      (fstPartition.quot_map (false, false)) (fstPartition.quot_map (false, false)) = 1 / 2 := by
    rw [pow_two, Matrix.mul_apply]
    simp only [hQ]
    have hcard : Fintype.card (fstPartition (A := Bool) (B := Bool)).Quot = 2 := by
      have hbij : Function.Bijective (fun x : Bool => fstPartition.quot_map (x, false)) := by
        constructor
        · intro x y h
          exact (quot_map_eq_iff fstPartition (x, false) (y, false)).mp h
        · intro B
          obtain ⟨⟨a, b⟩, hB⟩ := Quotient.exists_rep B
          exact ⟨a, hB ▸ Quotient.sound rfl⟩
      rw [← Fintype.card_of_bijective hbij]
      simp
    rw [Finset.sum_const, Finset.card_univ, hcard]
    norm_num
  have := congrFun (congrFun h (fstPartition.quot_map (false, false))) (fstPartition.quot_map (false, false))
  rw [hsq, hdiag] at this
  norm_num at this

/-! ### Sharpness of the contraction-aware budget on the reader class -/

/-- Every entry of the reader's canonical coarse kernel (uniform weights) is `1/2`. -/
theorem reader_Q_entry (A B : byState.Quot) :
    CoarseGenerator (detKernel reader) byState (fun _ => (1 : ℝ)) A B = 1 / 2 := by
  obtain ⟨⟨b, t⟩, hA⟩ := Quotient.exists_rep A
  have hA' : byState.quot_map (b, t) = A := hA
  have hbb : byState.quot_map (b, t) = byState.quot_map (b, b) :=
    (quot_map_eq_iff byState _ _).mpr rfl
  rw [← hA', hbb]
  exact reader_coarse_row b B

theorem reader_dobrushin_zero :
    dobrushin (CoarseGenerator (detKernel reader) byState (fun _ => (1 : ℝ))) = 0 :=
  (dobrushin_zero_iff_rows_equal _).mpr fun A B => by funext C; rw [reader_Q_entry, reader_Q_entry]

/-- The reader's defect is exactly `1`: the lower end of the gap. -/
theorem reader_defect_exact : machineDefect reader byState (fun _ => (1 : ℝ)) = 1 := by
  apply le_antisymm
  · apply rowL1Norm_le _ zero_le_one
    intro x
    rw [detKernel_row_residual_l1 reader byState (fun _ => one_pos) x, reader_Q_entry]
    norm_num
  · exact reader_defect_eq_one (fun _ => one_pos)

/-- The contraction-aware budget of the reader is exactly `1/2` at every positive horizon. -/
theorem reader_mixing_budget (h : ℕ) (hh : 1 ≤ h) :
    mixingBudget (detKernel reader) byState (fun _ => (1 : ℝ)) h = 1 / 2 := by
  unfold mixingBudget
  have hc : rowL1Norm (closureCommutator (detKernel reader) byState (fun _ => (1 : ℝ))) = 1 :=
    reader_defect_exact
  rw [hc, reader_dobrushin_zero]
  have hsum : (∑ j ∈ Finset.range h, (0 : ℝ) ^ j) = 1 := by
    obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
    rw [Finset.sum_range_succ', Finset.sum_eq_zero]
    · simp
    · intro j _; simp
  rw [hsum]
  norm_num

/-- **Sharpness.** From every point input the reader's exact terminal error equals the
contraction-aware budget `1/2` at every positive horizon: the budget is attained, while the
linear budget is `1` from two steps on. -/
theorem reader_budget_sharp (x : Cfg) (h : ℕ) (hh : 1 ≤ h) :
    tv (actualLaw (detKernel reader) byState (detKernel_isStochastic reader) (pointMass x) h)
      (referenceLaw (detKernel reader) byState (fun _ => one_pos) (detKernel_isStochastic reader)
        (pointMass x) h) =
      mixingBudget (detKernel reader) byState (fun _ => (1 : ℝ)) h := by
  rw [machine_error_of_dobrushin_zero reader byState (fun _ => one_pos) reader_dobrushin_zero x h hh
    (byState.quot_map x), reader_Q_entry, reader_mixing_budget h hh]
  norm_num

end Regression

end SGC.Bridge.MachineCertificate

end
