/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Renormalization.KernelHorizon
import Mathlib.Tactic

/-!
# Finite-state terminal decoding certificate

Turns the Kernel Horizon theorem (`kernel_closure_error_le`, a maximum-row `L^1` bound on
`T^m J - J Q^m`) into operational statements about **one terminal decision at step `m`**:
how reliably a fixed decoder reading the coarse observation recovers a required binary
answer, and how much distinguishability between two prepared inputs the observation
retains. Specification: external review, "Finite-state terminal decoding certificate"
(2026-09-13); formalization ours.

## Data and conventions

* `ProbabilityRow X` - nonnegative, unit-mass row vectors; laws evolve by `rho ᵥ* M`.
* `RowStochastic M` - rectangular row-stochastic matrices; `IsStochastic` embeds.
* `tv p q = (1/2) * sum |p - q|` - probability-distance convention, `0 <= tv <= 1`.
* `rowL1Norm M = ‖M‖` in `Matrix.linftyOpNormedAddCommGroup` - the SAME norm as
  `KernelHorizon`: `max_x sum_y |M x y|`.
* `Decoder X` - a (possibly randomized) decoder `probOne : X -> [0,1]`; `error p b` is the
  conditional error under preparation `b`. Deterministic decoders embed.
* `actualLaw`  `= rho T^m J`;  `referenceLaw` `= rho J Q^m`;  `terminalBudget = min 1 (m c / 2)`
  with `c = rowL1Norm (closureCommutator T P pi)`; `exactTerminalBudget = rowL1Norm E_m / 2`.

## Results (all standard consequences; the value is the exact hypotheses)

* `kernel_horizon_tv`, `kernel_horizon_tv_sharp` - `tv(actual, reference) <= min 1 (m c / 2)`,
  and the sharper `<= rowL1Norm(E_m) / 2`; `m = 0` gives exact agreement.
* `fixed_decoder_error_transfer` - `|e_act - e_ref| <= tv(actual, reference)` for each
  class separately (bounded-test inequality; randomized decoders included).
* `kernel_terminal_reliability` - `e_ref_b <= beta_b` and `beta_b + budget <= p_b` imply
  `e_act_b <= p_b`, per class. The reference decoder's correctness is a **hypothesis**.
* `observed_distinguishability_lower` / `_two_sided` - `|D_obs - D_ref| <= eps_0 + eps_1`.
* `tv_lower_of_individual_error_bounds` - both errors `<= p_b` forces
  `D_obs >= 1 - p_0 - p_1` (necessary, not sufficient).
* `joint_terminal_certificate`, `kernel_joint_terminal_certificate` - the sandwich
  `max 0 (D_ref - 2 eps) <= D_obs <= D_full <= Gamma * D_in`, where the contraction
  `Gamma` is an **explicit hypothesis** about the complete state, never derived here.
* `no_terminal_decoder_of_contraction` - `U < 1 - p_0 - p_1` rules out every decoder on
  the complete terminal state (randomized included).
* `iterated_tv_contraction` - product form across changing state spaces.
* Mixing refinement: `dobrushin`, `tv_dobrushin_contraction`,
  `kernel_horizon_tv_mixing`, `kernel_horizon_tv_uniform_mixing` - the linear budget
  `m c / 2` is replaced by `(c/2) * sum_{j<m} delta(Q)^j`, and by `c / (2 (1 - delta))`
  when `delta(Q) < 1`, using only the zero row sums of the commutator. No stationarity.

## Regression cases (namespace `Regression`)

* Exact closure with an information-erasing observation (`T = I`, one cell):
  `c = 0`, exact transfer, `D_obs = 0`, `D_full = 1`, no decoder has both errors `< 1/2`.
  Kills "zero closure defect implies decodability".
* Average vs worst conditional error (`mu_0 = delta_0`, `mu_1 = uniform`, `tv = 1/2`):
  equal-prior optimum `1/4` attained; randomized minimax `1/3` attained and optimal;
  deterministic minimax `1/2`; no decoder has both errors `<= 1/4`.
* Half-`L^1` normalization (`tv(delta_0, delta_1) = 1`).
* Nonstationary reference weights (`T = swap`, `pi = (1,2)`, `pi T != pi`): `c = 0`,
  exact transfer still holds - stationarity is not a hypothesis.
* `swap` has Dobrushin coefficient `1` (no contraction); `reset` has coefficient `0`
  and forgets both inputs in one step (an honest, explicit full-state contraction).

## What is NOT claimed

Nothing about fluids, continuum limits, computational universality, whole-execution
correctness, path-law approximation, or a failure deadline when a budget expires. A
strict contraction `Gamma < 1` is never inferred from closure, positivity of `pi`, or
dissipation; it must be supplied for the complete state actually available to the
decoder. Expiry of a sufficient certificate establishes neither success nor failure.
-/


noncomputable section

namespace SGC.Bridge.TerminalDecoding

open Finset Matrix
open scoped NNReal
open SGC.Thermodynamics SGC.Renormalization.MeasureReentry
open SGC.Renormalization.KernelHorizon

attribute [local instance] Matrix.linftyOpNormedAddCommGroup

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

structure ProbabilityRow (X : Type*) [Fintype X] where
  mass : X → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  sum_one : ∑ x, mass x = 1

instance : CoeFun (ProbabilityRow X) (fun _ => X → ℝ) := ⟨ProbabilityRow.mass⟩

structure RowStochastic (M : Matrix X Y ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ M x y
  sum_one : ∀ x, ∑ y, M x y = 1

def l1 (v : X → ℝ) : ℝ := ∑ x, |v x|

def rowL1Norm (M : Matrix X Y ℝ) : ℝ := ‖M‖

def tv (p q : X → ℝ) : ℝ := l1 (p - q) / 2

lemma l1_nonneg (v : X → ℝ) : 0 ≤ l1 v :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma row_l1_le_rowL1Norm (M : Matrix X Y ℝ) (x : X) :
    l1 (M x) ≤ rowL1Norm M := by
  unfold l1 rowL1Norm
  rw [Matrix.linfty_opNorm_def]
  have h := Finset.le_sup (f := fun i : X => ∑ j : Y, ‖M i j‖₊) (Finset.mem_univ x)
  have hr := NNReal.coe_le_coe.mpr h
  simpa only [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs] using hr

lemma rowL1Norm_le (M : Matrix X Y ℝ) {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ x, l1 (M x) ≤ a) : rowL1Norm M ≤ a := by
  unfold rowL1Norm
  rw [Matrix.linfty_opNorm_def]
  have hs : (Finset.univ.sup fun i : X => ∑ j : Y, ‖M i j‖₊) ≤ (⟨a, ha⟩ : ℝ≥0) := by
    refine Finset.sup_le fun i _ => ?_
    apply NNReal.coe_le_coe.mp
    simpa only [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs] using h i
  exact_mod_cast hs

lemma RowStochastic.of_existing {M : Matrix X X ℝ} (h : IsStochastic M) :
    RowStochastic M := ⟨h.nonneg, h.row_sum_one⟩

omit [Fintype X] in
lemma RowStochastic.mul {M : Matrix X Y ℝ} {N : Matrix Y Z ℝ}
    (hM : RowStochastic M) (hN : RowStochastic N) : RowStochastic (M * N) where
  nonneg x z := Finset.sum_nonneg fun y _ => mul_nonneg (hM.nonneg x y) (hN.nonneg y z)
  sum_one x := by
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hN.sum_one, mul_one]
    exact hM.sum_one x

lemma RowStochastic.one [DecidableEq X] : RowStochastic (1 : Matrix X X ℝ) where
  nonneg x y := by by_cases h : x = y <;> simp [Matrix.one_apply, h]
  sum_one x := by simp [Matrix.one_apply]

lemma RowStochastic.pow [DecidableEq X] {M : Matrix X X ℝ}
    (hM : RowStochastic M) (m : ℕ) : RowStochastic (M ^ m) := by
  induction m with
  | zero => simpa using (RowStochastic.one (X := X))
  | succ m ih => simpa [pow_succ] using ih.mul hM

lemma rowStochastic_lift [DecidableEq X] (P : Partition X) :
    RowStochastic (lift_matrix P) where
  nonneg x y := by unfold lift_matrix; split_ifs <;> norm_num
  sum_one x := by
    classical
    simp [lift_matrix]

lemma ProbabilityRow.nonempty (p : ProbabilityRow X) : Nonempty X := by
  by_contra h
  haveI : IsEmpty X := not_nonempty_iff.mp h
  have hmass := p.sum_one
  simp at hmass

def ProbabilityRow.push (p : ProbabilityRow X) (M : Matrix X Y ℝ)
    (hM : RowStochastic M) : ProbabilityRow Y where
  mass := (p : X → ℝ) ᵥ* M
  nonneg y := Finset.sum_nonneg fun x _ => mul_nonneg (p.nonneg x) (hM.nonneg x y)
  sum_one := by
    simp only [Matrix.vecMul, dotProduct]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hM.sum_one, mul_one]
    exact p.sum_one

@[simp] lemma ProbabilityRow.push_apply (p : ProbabilityRow X) (M : Matrix X Y ℝ)
    (hM : RowStochastic M) (y : Y) : p.push M hM y = ∑ x, p x * M x y := rfl

lemma prob_vecMul_row_l1_le (p : ProbabilityRow X) (M : Matrix X Y ℝ) :
    l1 ((p : X → ℝ) ᵥ* M) ≤ rowL1Norm M := by
  calc
    l1 ((p : X → ℝ) ᵥ* M) ≤ ∑ y, ∑ x, |p x * M x y| := by
      exact Finset.sum_le_sum fun y _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, p x * l1 (M x) := by
      rw [Finset.sum_comm]
      simp only [abs_mul, abs_of_nonneg (p.nonneg _), l1, Finset.mul_sum]
    _ ≤ ∑ x, p x * rowL1Norm M := by
      exact Finset.sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_left (row_l1_le_rowL1Norm M x) (p.nonneg x)
    _ = rowL1Norm M := by rw [← Finset.sum_mul, p.sum_one, one_mul]

lemma l1_vecMul_le {M : Matrix X Y ℝ} (hM : RowStochastic M) (v : X → ℝ) :
    l1 (v ᵥ* M) ≤ l1 v := by
  calc
    l1 (v ᵥ* M) ≤ ∑ y, ∑ x, |v x * M x y| := by
      exact Finset.sum_le_sum fun y _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, |v x| * ∑ y, M x y := by
      rw [Finset.sum_comm]
      simp only [abs_mul, abs_of_nonneg (hM.nonneg _ _), Finset.mul_sum]
    _ = l1 v := by simp only [hM.sum_one, mul_one, l1]

lemma tv_nonneg (p q : X → ℝ) : 0 ≤ tv p q := div_nonneg (l1_nonneg _) (by norm_num)

@[simp] lemma tv_self (p : X → ℝ) : tv p p = 0 := by simp [tv, l1]

lemma tv_symm (p q : X → ℝ) : tv p q = tv q p := by
  simp only [tv, l1, Pi.sub_apply, abs_sub_comm]

lemma tv_triangle (p q r : X → ℝ) : tv p r ≤ tv p q + tv q r := by
  unfold tv l1
  simp only [Pi.sub_apply]
  rw [← add_div, ← Finset.sum_add_distrib]
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun x _ => abs_sub_le (p x) (q x) (r x)) (by norm_num)

lemma tv_le_one (p q : ProbabilityRow X) : tv p q ≤ 1 := by
  have h : l1 ((p : X → ℝ) - (q : X → ℝ)) ≤ 2 := by
    calc
      l1 ((p : X → ℝ) - (q : X → ℝ)) ≤ ∑ x, (p x + q x) := by
        refine Finset.sum_le_sum fun x _ => ?_
        simpa [abs_of_nonneg (p.nonneg x), abs_of_nonneg (q.nonneg x)] using
          (abs_sub (p x) (q x))
      _ = 2 := by rw [Finset.sum_add_distrib, p.sum_one, q.sum_one]; norm_num
  unfold tv
  linarith

lemma abs_bounded_test_le_half_l1 {v f : X → ℝ} (hv : ∑ x, v x = 0)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    |∑ x, v x * f x| ≤ l1 v / 2 := by
  have heq : (∑ x, v x * f x) = ∑ x, v x * (f x - 1 / 2) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hv, zero_mul, sub_zero]
  rw [heq]
  calc
    |∑ x, v x * (f x - 1 / 2)| ≤ ∑ x, |v x * (f x - 1 / 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, |v x| * (1 / 2) := by
      refine Finset.sum_le_sum fun x _ => ?_
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact abs_le.mpr ⟨by linarith [(hf x).1], by linarith [(hf x).2]⟩
    _ = l1 v / 2 := by rw [← Finset.sum_mul]; simp [l1, div_eq_mul_inv]

lemma bounded_test_tv (p q : ProbabilityRow X) {f : X → ℝ}
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    |(∑ x, p x * f x) - ∑ x, q x * f x| ≤ tv p q := by
  have hz : ∑ x, (p x - q x) = 0 := by
    rw [Finset.sum_sub_distrib, p.sum_one, q.sum_one, sub_self]
  have h := abs_bounded_test_le_half_l1 hz hf
  simpa [tv, l1, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib] using h

lemma tv_vecMul_le_half_row_l1 (p : ProbabilityRow X)
    (M N : Matrix X Y ℝ) :
    tv ((p : X → ℝ) ᵥ* M) ((p : X → ℝ) ᵥ* N) ≤ rowL1Norm (M - N) / 2 := by
  rw [tv, ← Matrix.vecMul_sub]
  exact div_le_div_of_nonneg_right (prob_vecMul_row_l1_le p (M - N)) (by norm_num)

lemma tv_data_processing (p q : X → ℝ) {M : Matrix X Y ℝ} (hM : RowStochastic M) :
    tv (p ᵥ* M) (q ᵥ* M) ≤ tv p q := by
  rw [tv, ← Matrix.sub_vecMul]
  exact div_le_div_of_nonneg_right (l1_vecMul_le hM (p - q)) (by norm_num)

def RowStochastic.row {M : Matrix X Y ℝ} (hM : RowStochastic M) (x : X) :
    ProbabilityRow Y := ⟨M x, hM.nonneg x, hM.sum_one x⟩

lemma stochastic_difference_rowL1Norm_le_two {M N : Matrix X Y ℝ}
    (hM : RowStochastic M) (hN : RowStochastic N) : rowL1Norm (M - N) ≤ 2 := by
  apply rowL1Norm_le _ (by norm_num)
  intro x
  have h := tv_le_one (hM.row x) (hN.row x)
  change l1 (fun y => M x y - N x y) / 2 ≤ 1 at h
  change l1 (fun y => M x y - N x y) ≤ 2
  linarith

section Kernel

variable [DecidableEq X]

def terminalError (T : Matrix X X ℝ) (P : Partition X) (pi : X → ℝ) (m : ℕ) :
    Matrix X P.Quot ℝ := T ^ m * lift_matrix P - lift_matrix P * (CoarseGenerator T P pi) ^ m

def terminalBudget (T : Matrix X X ℝ) (P : Partition X) (pi : X → ℝ) (m : ℕ) : ℝ :=
  min 1 (m * rowL1Norm (closureCommutator T P pi) / 2)

def exactTerminalBudget (T : Matrix X X ℝ) (P : Partition X) (pi : X → ℝ) (m : ℕ) : ℝ :=
  rowL1Norm (terminalError T P pi m) / 2

def classTerminalBudget (T : Matrix X X ℝ) (P : Partition X) (pi : X → ℝ)
    (rho : ProbabilityRow X) (m : ℕ) : ℝ :=
  l1 ((rho : X → ℝ) ᵥ* terminalError T P pi m) / 2

def actualLaw (T : Matrix X X ℝ) (P : Partition X) (hT : IsStochastic T)
    (rho : ProbabilityRow X) (m : ℕ) : ProbabilityRow P.Quot :=
  rho.push (T ^ m * lift_matrix P)
    (((RowStochastic.of_existing hT).pow m).mul (rowStochastic_lift P))

def referenceLaw (T : Matrix X X ℝ) (P : Partition X) {pi : X → ℝ}
    (hpi : ∀ x, 0 < pi x) (hT : IsStochastic T)
    (rho : ProbabilityRow X) (m : ℕ) : ProbabilityRow P.Quot :=
  rho.push (lift_matrix P * (CoarseGenerator T P pi) ^ m)
    ((rowStochastic_lift P).mul
      ((RowStochastic.of_existing (coarseKernel_isStochastic T P hpi hT)).pow m))

@[simp] lemma terminalError_zero (T : Matrix X X ℝ) (P : Partition X) (pi : X → ℝ) :
    terminalError T P pi 0 = 0 := by simp [terminalError]

@[simp] lemma terminalBudget_zero (T : Matrix X X ℝ) (P : Partition X) (pi : X → ℝ) :
    terminalBudget T P pi 0 = 0 := by simp [terminalBudget]

lemma exact_terminal_budget_le (T : Matrix X X ℝ) (P : Partition X) {pi : X → ℝ}
    (hpi : ∀ x, 0 < pi x) (hT : IsStochastic T) (m : ℕ) :
    exactTerminalBudget T P pi m ≤ terminalBudget T P pi m := by
  apply le_min
  · have h := stochastic_difference_rowL1Norm_le_two
      (((RowStochastic.of_existing hT).pow m).mul (rowStochastic_lift P))
      ((rowStochastic_lift P).mul
        ((RowStochastic.of_existing (coarseKernel_isStochastic T P hpi hT)).pow m))
    change rowL1Norm (terminalError T P pi m) ≤ 2 at h
    unfold exactTerminalBudget
    linarith
  · exact div_le_div_of_nonneg_right (kernel_closure_error_le T P hpi hT m) (by norm_num)

lemma class_terminal_budget_exact (T : Matrix X X ℝ) (P : Partition X) {pi : X → ℝ}
    (hpi : ∀ x, 0 < pi x) (hT : IsStochastic T) (rho : ProbabilityRow X) (m : ℕ) :
    tv (actualLaw T P hT rho m) (referenceLaw T P hpi hT rho m) =
      classTerminalBudget T P pi rho m := by
  change l1 (((rho : X → ℝ) ᵥ* (T ^ m * lift_matrix P)) -
    ((rho : X → ℝ) ᵥ* (lift_matrix P * (CoarseGenerator T P pi) ^ m))) / 2 = _
  rw [← Matrix.vecMul_sub]
  rfl

lemma kernel_horizon_tv_sharp (T : Matrix X X ℝ) (P : Partition X) {pi : X → ℝ}
    (hpi : ∀ x, 0 < pi x) (hT : IsStochastic T) (rho : ProbabilityRow X) (m : ℕ) :
    tv (actualLaw T P hT rho m) (referenceLaw T P hpi hT rho m) ≤
      exactTerminalBudget T P pi m :=
  tv_vecMul_le_half_row_l1 rho _ _

lemma kernel_horizon_tv (T : Matrix X X ℝ) (P : Partition X) {pi : X → ℝ}
    (hpi : ∀ x, 0 < pi x) (hT : IsStochastic T) (rho : ProbabilityRow X) (m : ℕ) :
    tv (actualLaw T P hT rho m) (referenceLaw T P hpi hT rho m) ≤
      terminalBudget T P pi m :=
  (kernel_horizon_tv_sharp T P hpi hT rho m).trans (exact_terminal_budget_le T P hpi hT m)

lemma kernel_horizon_tv_zero (T : Matrix X X ℝ) (P : Partition X) {pi : X → ℝ}
    (hpi : ∀ x, 0 < pi x) (hT : IsStochastic T) (rho : ProbabilityRow X) :
    tv (actualLaw T P hT rho 0) (referenceLaw T P hpi hT rho 0) = 0 := by
  apply le_antisymm _ (tv_nonneg _ _)
  simpa using kernel_horizon_tv T P hpi hT rho 0

end Kernel

structure Decoder (X : Type*) where
  probOne : X → ℝ
  bounds : ∀ x, probOne x ∈ Set.Icc (0 : ℝ) 1

def Decoder.loss (d : Decoder X) (b : Bool) (x : X) : ℝ :=
  if b then 1 - d.probOne x else d.probOne x

def Decoder.error (d : Decoder X) (p : ProbabilityRow X) (b : Bool) : ℝ :=
  ∑ x, p x * d.loss b x

def deterministicDecoder (d : X → Bool) : Decoder X where
  probOne x := if d x then 1 else 0
  bounds x := by cases h : d x <;> simp

omit [Fintype X] in
lemma Decoder.loss_bounds (d : Decoder X) (b : Bool) (x : X) :
    d.loss b x ∈ Set.Icc (0 : ℝ) 1 := by
  cases b with
  | false => exact d.bounds x
  | true =>
    simp only [Decoder.loss, ↓reduceIte, Set.mem_Icc]
    constructor <;> linarith [(d.bounds x).1, (d.bounds x).2]

lemma Decoder.error_bounds (d : Decoder X) (p : ProbabilityRow X) (b : Bool) :
    d.error p b ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg fun x _ => mul_nonneg (p.nonneg x) ((d.loss_bounds b x).1)
  · calc
      d.error p b ≤ ∑ x, p x * 1 := Finset.sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_left ((d.loss_bounds b x).2) (p.nonneg x)
      _ = 1 := by simp only [mul_one, p.sum_one]

lemma deterministic_error_eq (d : X → Bool) (p : ProbabilityRow X) (b : Bool) :
    (deterministicDecoder d).error p b = ∑ x, if d x = b then 0 else p x := by
  apply Finset.sum_congr rfl
  intro x _
  cases b <;> cases h : d x <;> simp [Decoder.loss, deterministicDecoder, h]

lemma fixed_decoder_error_transfer (d : Decoder X) (a r : ProbabilityRow X) (b : Bool) :
    |d.error a b - d.error r b| ≤ tv a r :=
  bounded_test_tv a r (d.loss_bounds b)

lemma terminal_reliability_of_reference_bounds (d : Decoder X)
    (a r : Bool → ProbabilityRow X) (epsilon : Bool → ℝ)
    (beta p : Bool → Set.Icc (0 : ℝ) 1)
    (hTV : ∀ b, tv (a b) (r b) ≤ epsilon b)
    (hRef : ∀ b, d.error (r b) b ≤ beta b)
    (hBudget : ∀ b, (beta b : ℝ) + epsilon b ≤ p b) :
    ∀ b, d.error (a b) b ≤ p b := by
  intro b
  have h := (fixed_decoder_error_transfer d (a b) (r b) b).trans (hTV b)
  have hu := (abs_le.mp h).2
  linarith [hRef b, hBudget b]

lemma observed_distinguishability_two_sided (a r : Bool → ProbabilityRow X)
    (epsilon : Bool → ℝ) (hTV : ∀ b, tv (a b) (r b) ≤ epsilon b) :
    |tv (a false) (a true) - tv (r false) (r true)| ≤ epsilon false + epsilon true := by
  have ha := tv_triangle (a false) (r false) (a true)
  have ha' := tv_triangle (r false) (r true) (a true)
  have hr := tv_triangle (r false) (a false) (r true)
  have hr' := tv_triangle (a false) (a true) (r true)
  rw [tv_symm (r true) (a true)] at ha'
  rw [tv_symm (r false) (a false)] at hr
  apply abs_le.mpr
  constructor <;> linarith [hTV false, hTV true]

lemma observed_distinguishability_lower (a r : Bool → ProbabilityRow X)
    (epsilon : Bool → ℝ) (hTV : ∀ b, tv (a b) (r b) ≤ epsilon b) :
    max 0 (tv (r false) (r true) - (epsilon false + epsilon true)) ≤
      tv (a false) (a true) := by
  apply max_le (tv_nonneg _ _)
  have h := (abs_le.mp (observed_distinguishability_two_sided a r epsilon hTV)).1
  linarith

lemma Decoder.error_sum (d : Decoder X) (p q : ProbabilityRow X) :
    d.error p false + d.error q true =
      1 - ((∑ x, q x * d.probOne x) - ∑ x, p x * d.probOne x) := by
  simp only [Decoder.error, Decoder.loss, Bool.false_eq_true, ↓reduceIte,
    mul_sub, mul_one, Finset.sum_sub_distrib, q.sum_one]
  ring

lemma decoder_error_sum_lower (d : Decoder X) (p q : ProbabilityRow X) :
    1 - tv p q ≤ d.error p false + d.error q true := by
  rw [d.error_sum]
  have h := bounded_test_tv q p d.bounds
  rw [tv_symm q p] at h
  have hh := le_trans (le_abs_self _) h
  linarith

lemma tv_lower_of_individual_error_bounds (d : Decoder X) (a : Bool → ProbabilityRow X)
    (p : Bool → Set.Icc (0 : ℝ) 1) (h : ∀ b, d.error (a b) b ≤ p b) :
    max 0 (1 - (p false : ℝ) - p true) ≤ tv (a false) (a true) := by
  apply max_le (tv_nonneg _ _)
  linarith [decoder_error_sum_lower d (a false) (a true), h false, h true]

lemma joint_terminal_certificate (a r : Bool → ProbabilityRow Y)
    (full : Bool → ProbabilityRow X) (O : Matrix X Y ℝ) (hO : RowStochastic O)
    (alignment : ∀ b, (full b).push O hO = a b)
    (epsilon : Bool → ℝ) (hTV : ∀ b, tv (a b) (r b) ≤ epsilon b)
    {U : ℝ} (hFull : tv (full false) (full true) ≤ U) :
    max 0 (tv (r false) (r true) - (epsilon false + epsilon true)) ≤ tv (a false) (a true) ∧
    tv (a false) (a true) ≤ min (tv (r false) (r true) + epsilon false + epsilon true) U ∧
    tv (a false) (a true) ≤ tv (full false) (full true) ∧
    tv (full false) (full true) ≤ U := by
  have hData : tv (a false) (a true) ≤ tv (full false) (full true) := by
    rw [← alignment false, ← alignment true]
    exact tv_data_processing (full false) (full true) hO
  have hTwo := (abs_le.mp (observed_distinguishability_two_sided a r epsilon hTV)).2
  exact ⟨observed_distinguishability_lower a r epsilon hTV,
    le_min (by linarith) (hData.trans hFull), hData, hFull⟩

lemma reference_contraction_compatibility (a r : Bool → ProbabilityRow X)
    (epsilon : Bool → ℝ) (hTV : ∀ b, tv (a b) (r b) ≤ epsilon b)
    {U : ℝ} (hU : tv (a false) (a true) ≤ U) :
    tv (r false) (r true) ≤ U + epsilon false + epsilon true := by
  have h := (abs_le.mp (observed_distinguishability_two_sided a r epsilon hTV)).1
  linarith

lemma semantic_contraction_compatibility (d : Decoder X) (a r : Bool → ProbabilityRow X)
    (epsilon : Bool → ℝ) (hTV : ∀ b, tv (a b) (r b) ≤ epsilon b)
    {U : ℝ} (hU : tv (a false) (a true) ≤ U) :
    1 - U ≤ d.error (r false) false + d.error (r true) true + epsilon false + epsilon true := by
  have h := reference_contraction_compatibility a r epsilon hTV hU
  linarith [decoder_error_sum_lower d (r false) (r true)]

lemma no_terminal_decoder_of_contraction (full : Bool → ProbabilityRow X)
    (p : Bool → Set.Icc (0 : ℝ) 1) {U : ℝ}
    (hFull : tv (full false) (full true) ≤ U)
    (hStrict : U < 1 - (p false : ℝ) - p true) :
    ∀ d : Decoder X, (p false : ℝ) < d.error (full false) false ∨
      (p true : ℝ) < d.error (full true) true := by
  intro d
  by_contra h
  push_neg at h
  linarith [decoder_error_sum_lower d (full false) (full true)]

lemma iterated_tv_contraction {W : ℕ → Type*} [∀ j, Fintype (W j)]
    (laws : ∀ j, Bool → ProbabilityRow (W j))
    (K : ∀ j, Matrix (W j) (W (j + 1)) ℝ) (hK : ∀ j, RowStochastic (K j))
    (evolution : ∀ j b, (laws j b).push (K j) (hK j) = laws (j + 1) b)
    (theta : ℕ → Set.Icc (0 : ℝ) 1)
    (hStep : ∀ j, tv ((laws j false).push (K j) (hK j))
      ((laws j true).push (K j) (hK j)) ≤
        (theta j : ℝ) * tv (laws j false) (laws j true)) (m : ℕ) :
    tv (laws m false) (laws m true) ≤
      tv (laws 0 false) (laws 0 true) * ∏ j ∈ Finset.range m, (theta j : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := hStep m
    rw [evolution m false, evolution m true] at h
    calc
      tv (laws (m + 1) false) (laws (m + 1) true) ≤
          (theta m : ℝ) * tv (laws m false) (laws m true) := h
      _ ≤ (theta m : ℝ) *
          (tv (laws 0 false) (laws 0 true) * ∏ j ∈ Finset.range m, (theta j : ℝ)) :=
        mul_le_mul_of_nonneg_left ih (theta m).property.1
      _ = tv (laws 0 false) (laws 0 true) *
          ∏ j ∈ Finset.range (m + 1), (theta j : ℝ) := by rw [Finset.prod_range_succ]; ring

@[ext] lemma ProbabilityRow.ext {p q : ProbabilityRow X} (h : ∀ x, p x = q x) : p = q := by
  cases p
  cases q
  congr
  funext x
  exact h x

section KernelCertificate

variable [DecidableEq X]

lemma kernel_fixed_decoder_error_transfer (T : Matrix X X ℝ) (P : Partition X) {pi : X → ℝ}
    (hpi : ∀ x, 0 < pi x) (hT : IsStochastic T) (rho : ProbabilityRow X)
    (d : Decoder P.Quot) (b : Bool) (m : ℕ) :
    |d.error (actualLaw T P hT rho m) b - d.error (referenceLaw T P hpi hT rho m) b| ≤
      terminalBudget T P pi m :=
  (fixed_decoder_error_transfer d _ _ b).trans (kernel_horizon_tv T P hpi hT rho m)

lemma kernel_terminal_reliability (T : Matrix X X ℝ) (P : Partition X) {pi : X → ℝ}
    (hpi : ∀ x, 0 < pi x) (hT : IsStochastic T) (mu : Bool → ProbabilityRow X)
    (d : Decoder P.Quot) (beta p : Bool → Set.Icc (0 : ℝ) 1) (m : ℕ)
    (hRef : ∀ b, d.error (referenceLaw T P hpi hT (mu b) m) b ≤ beta b)
    (hBudget : ∀ b, (beta b : ℝ) + terminalBudget T P pi m ≤ p b) :
    ∀ b, d.error (actualLaw T P hT (mu b) m) b ≤ p b :=
  terminal_reliability_of_reference_bounds d _ _ (fun _ => terminalBudget T P pi m)
    beta p (fun b => kernel_horizon_tv T P hpi hT (mu b) m) hRef hBudget

lemma actualLaw_alignment (T : Matrix X X ℝ) (P : Partition X) (hT : IsStochastic T)
    (rho : ProbabilityRow X) (m : ℕ) :
    (rho.push (T ^ m) ((RowStochastic.of_existing hT).pow m)).push
      (lift_matrix P) (rowStochastic_lift P) = actualLaw T P hT rho m := by
  apply ProbabilityRow.ext
  intro y
  change (((rho : X → ℝ) ᵥ* (T ^ m)) ᵥ* lift_matrix P) y =
    ((rho : X → ℝ) ᵥ* (T ^ m * lift_matrix P)) y
  rw [Matrix.vecMul_vecMul]

lemma kernel_joint_terminal_certificate (T : Matrix X X ℝ) (P : Partition X) {pi : X → ℝ}
    (hpi : ∀ x, 0 < pi x) (hT : IsStochastic T) (mu : Bool → ProbabilityRow X)
    (m : ℕ) (Gamma : Set.Icc (0 : ℝ) 1)
    (hContract : tv ((mu false : X → ℝ) ᵥ* T ^ m) ((mu true : X → ℝ) ᵥ* T ^ m) ≤
      (Gamma : ℝ) * tv (mu false) (mu true)) :
    let a := fun b => actualLaw T P hT (mu b) m
    let r := fun b => referenceLaw T P hpi hT (mu b) m
    max 0 (tv (r false) (r true) - 2 * exactTerminalBudget T P pi m) ≤ tv (a false) (a true) ∧
    tv (a false) (a true) ≤ tv ((mu false : X → ℝ) ᵥ* T ^ m) ((mu true : X → ℝ) ᵥ* T ^ m) ∧
    tv ((mu false : X → ℝ) ᵥ* T ^ m) ((mu true : X → ℝ) ᵥ* T ^ m) ≤
      (Gamma : ℝ) * tv (mu false) (mu true) := by
  have h := joint_terminal_certificate
    (fun b => actualLaw T P hT (mu b) m) (fun b => referenceLaw T P hpi hT (mu b) m)
    (fun b => (mu b).push (T ^ m) ((RowStochastic.of_existing hT).pow m))
    (lift_matrix P) (rowStochastic_lift P) (fun b => actualLaw_alignment T P hT (mu b) m)
    (fun _ => exactTerminalBudget T P pi m)
    (fun b => kernel_horizon_tv_sharp T P hpi hT (mu b) m) hContract
  exact ⟨by simpa only [two_mul] using h.1, h.2.2.1, h.2.2.2⟩

end KernelCertificate

def rowDifferences (M : Matrix X Y ℝ) : Matrix (X × X) Y ℝ :=
  fun xy y => M xy.1 y - M xy.2 y

def dobrushin (M : Matrix X Y ℝ) : ℝ := rowL1Norm (rowDifferences M) / 2

lemma dobrushin_nonneg (M : Matrix X Y ℝ) : 0 ≤ dobrushin M :=
  div_nonneg (norm_nonneg _) (by norm_num)

lemma row_tv_le_dobrushin (M : Matrix X Y ℝ) (x x' : X) :
    tv (M x) (M x') ≤ dobrushin M :=
  div_le_div_of_nonneg_right (row_l1_le_rowL1Norm (rowDifferences M) (x, x')) (by norm_num)

lemma dobrushin_le_one {M : Matrix X Y ℝ} (hM : RowStochastic M) : dobrushin M ≤ 1 := by
  have h : rowL1Norm (rowDifferences M) ≤ 2 := by
    apply rowL1Norm_le _ (by norm_num)
    intro xy
    have hh := tv_le_one (hM.row xy.1) (hM.row xy.2)
    change l1 (fun y => M xy.1 y - M xy.2 y) / 2 ≤ 1 at hh
    change l1 (fun y => M xy.1 y - M xy.2 y) ≤ 2
    linarith
  unfold dobrushin
  linarith

lemma abs_interval_test_le {v f : X → ℝ} (hv : ∑ x, v x = 0)
    {a b : ℝ} (hf : ∀ x, f x ∈ Set.Icc a b) :
    |∑ x, v x * f x| ≤ l1 v * ((b - a) / 2) := by
  have heq : (∑ x, v x * f x) = ∑ x, v x * (f x - (a + b) / 2) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hv, zero_mul, sub_zero]
  rw [heq]
  calc
    |∑ x, v x * (f x - (a + b) / 2)| ≤ ∑ x, |v x * (f x - (a + b) / 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, |v x| * ((b - a) / 2) := by
      refine Finset.sum_le_sum fun x _ => ?_
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact abs_le.mpr ⟨by linarith [(hf x).1], by linarith [(hf x).2]⟩
    _ = l1 v * ((b - a) / 2) := by rw [← Finset.sum_mul]; rfl

lemma signed_l1_vecMul_dobrushin (M : Matrix X Y ℝ) (v : X → ℝ)
    (hv : ∑ x, v x = 0) : l1 (v ᵥ* M) ≤ dobrushin M * l1 v := by
  classical
  by_cases hX : Nonempty X
  · letI : Nonempty X := hX
    let s : Y → ℝ := fun y => if 0 ≤ (v ᵥ* M) y then 1 else -1
    let g : X → ℝ := fun x => ∑ y, M x y * s y
    have hs : ∀ y, |s y| = 1 := by intro y; simp only [s]; split_ifs <;> norm_num
    have heq : l1 (v ᵥ* M) = ∑ x, v x * g x := by
      calc
        l1 (v ᵥ* M) = ∑ y, (v ᵥ* M) y * s y := by
          refine Finset.sum_congr rfl fun y _ => ?_
          dsimp [s]
          split_ifs with h
          · simp [abs_of_nonneg h]
          · simp [abs_of_neg (lt_of_not_ge h)]
        _ = ∑ x, v x * g x := by
          simp only [Matrix.vecMul, dotProduct, Finset.sum_mul, g, Finset.mul_sum]
          rw [Finset.sum_comm]
          simp only [mul_assoc]
    have hdiff : ∀ x z, |g x - g z| ≤ 2 * dobrushin M := by
      intro x z
      calc
        |g x - g z| = |∑ y, (M x y - M z y) * s y| := by
          simp only [g, sub_mul, Finset.sum_sub_distrib]
        _ ≤ ∑ y, |(M x y - M z y) * s y| := Finset.abs_sum_le_sum_abs _ _
        _ = l1 (fun y => M x y - M z y) := by simp only [abs_mul, hs, mul_one, l1]
        _ ≤ 2 * dobrushin M := by
          have h := row_tv_le_dobrushin M x z
          change l1 (fun y => M x y - M z y) / 2 ≤ _ at h
          linarith
    obtain ⟨x, _, hmin⟩ := Finset.exists_min_image Finset.univ g Finset.univ_nonempty
    have hinterval : ∀ z, g z ∈ Set.Icc (g x) (g x + 2 * dobrushin M) := by
      intro z
      refine ⟨hmin z (Finset.mem_univ z), ?_⟩
      have hh := (abs_le.mp (hdiff z x)).2
      linarith
    rw [heq]
    calc
      (∑ x, v x * g x) ≤ |∑ x, v x * g x| := le_abs_self _
      _ ≤ l1 v * ((g x + 2 * dobrushin M - g x) / 2) := abs_interval_test_le hv hinterval
      _ = dobrushin M * l1 v := by ring
  · haveI : IsEmpty X := not_nonempty_iff.mp hX
    simp [l1, Matrix.vecMul, dotProduct]

lemma tv_dobrushin_contraction (p q : ProbabilityRow X) (M : Matrix X Y ℝ) :
    tv ((p : X → ℝ) ᵥ* M) ((q : X → ℝ) ᵥ* M) ≤ dobrushin M * tv p q := by
  have hz : ∑ x, (p x - q x) = 0 := by
    rw [Finset.sum_sub_distrib, p.sum_one, q.sum_one, sub_self]
  have h := signed_l1_vecMul_dobrushin M (fun x => p x - q x) hz
  rw [tv, ← Matrix.sub_vecMul]
  change l1 ((fun x => p x - q x) ᵥ* M) / 2 ≤ dobrushin M * (l1 (fun x => p x - q x) / 2)
  linarith

lemma sum_vecMul_stochastic {M : Matrix X Y ℝ} (hM : RowStochastic M) (v : X → ℝ) :
    ∑ y, (v ᵥ* M) y = ∑ x, v x := by
  simp only [Matrix.vecMul, dotProduct]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hM.sum_one, mul_one]

lemma rowL1Norm_mul_dobrushin (M : Matrix X Y ℝ) (Q : Matrix Y Z ℝ)
    (hZero : ∀ x, ∑ y, M x y = 0) : rowL1Norm (M * Q) ≤ dobrushin Q * rowL1Norm M := by
  apply rowL1Norm_le _ (mul_nonneg (dobrushin_nonneg Q) (norm_nonneg _))
  intro x
  calc
    l1 ((M * Q) x) ≤ dobrushin Q * l1 (M x) := signed_l1_vecMul_dobrushin Q (M x) (hZero x)
    _ ≤ dobrushin Q * rowL1Norm M :=
      mul_le_mul_of_nonneg_left (row_l1_le_rowL1Norm M x) (dobrushin_nonneg Q)

lemma rowL1Norm_mul_pow_dobrushin [DecidableEq Y] (M : Matrix X Y ℝ) (Q : Matrix Y Y ℝ)
    (hQ : RowStochastic Q) (hZero : ∀ x, ∑ y, M x y = 0) (m : ℕ) :
    rowL1Norm (M * Q ^ m) ≤ dobrushin Q ^ m * rowL1Norm M := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hz : ∀ x, ∑ y, (M * Q ^ m) x y = 0 := by
      intro x
      exact (sum_vecMul_stochastic (hQ.pow m) (M x)).trans (hZero x)
    calc
      rowL1Norm (M * Q ^ (m + 1)) = rowL1Norm ((M * Q ^ m) * Q) := by rw [pow_succ, Matrix.mul_assoc]
      _ ≤ dobrushin Q * rowL1Norm (M * Q ^ m) := rowL1Norm_mul_dobrushin _ Q hz
      _ ≤ dobrushin Q * (dobrushin Q ^ m * rowL1Norm M) :=
        mul_le_mul_of_nonneg_left ih (dobrushin_nonneg Q)
      _ = dobrushin Q ^ (m + 1) * rowL1Norm M := by rw [pow_succ]; ring

section Mixing

variable [DecidableEq X]

lemma closureCommutator_row_sum_zero (T : Matrix X X ℝ) (P : Partition X) {pi : X → ℝ}
    (hpi : ∀ x, 0 < pi x) (hT : IsStochastic T) (x : X) :
    ∑ y, closureCommutator T P pi x y = 0 := by
  have hA := (RowStochastic.of_existing hT).mul (rowStochastic_lift P)
  have hB := (rowStochastic_lift P).mul
    (RowStochastic.of_existing (coarseKernel_isStochastic T P hpi hT))
  simp only [closureCommutator, Matrix.sub_apply, Finset.sum_sub_distrib,
    hA.sum_one, hB.sum_one, sub_self]

lemma kernel_error_dobrushin (T : Matrix X X ℝ) (P : Partition X) {pi : X → ℝ}
    (hpi : ∀ x, 0 < pi x) (hT : IsStochastic T) (m : ℕ) :
    rowL1Norm (terminalError T P pi m) ≤
      (∑ j ∈ Finset.range m, dobrushin (CoarseGenerator T P pi) ^ j) *
        rowL1Norm (closureCommutator T P pi) := by
  let Q := CoarseGenerator T P pi
  let C := closureCommutator T P pi
  have hQ : RowStochastic Q := RowStochastic.of_existing (coarseKernel_isStochastic T P hpi hT)
  have hz : ∀ x, ∑ y, C x y = 0 := closureCommutator_row_sum_zero T P hpi hT
  unfold rowL1Norm terminalError
  rw [power_closure_telescoping]
  calc
    ‖∑ k ∈ Finset.range m, T ^ (m - 1 - k) * C * Q ^ k‖ ≤
        ∑ k ∈ Finset.range m, ‖T ^ (m - 1 - k) * C * Q ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range m, dobrushin Q ^ k * rowL1Norm C := by
      refine Finset.sum_le_sum fun k _ => ?_
      calc
        ‖T ^ (m - 1 - k) * C * Q ^ k‖ = ‖T ^ (m - 1 - k) * (C * Q ^ k)‖ := by rw [Matrix.mul_assoc]
        _ ≤ ‖T ^ (m - 1 - k)‖ * ‖C * Q ^ k‖ := Matrix.linfty_opNorm_mul _ _
        _ ≤ 1 * ‖C * Q ^ k‖ := mul_le_mul_of_nonneg_right
          (stochastic_pow_norm_le_one T hT _) (norm_nonneg _)
        _ ≤ dobrushin Q ^ k * rowL1Norm C := by
          rw [one_mul]
          exact rowL1Norm_mul_pow_dobrushin C Q hQ hz k
    _ = (∑ j ∈ Finset.range m, dobrushin Q ^ j) * rowL1Norm C := by rw [Finset.sum_mul]

def mixingBudget (T : Matrix X X ℝ) (P : Partition X) (pi : X → ℝ) (m : ℕ) : ℝ :=
  min 1 ((rowL1Norm (closureCommutator T P pi) / 2) *
    ∑ j ∈ Finset.range m, dobrushin (CoarseGenerator T P pi) ^ j)

lemma kernel_horizon_tv_mixing (T : Matrix X X ℝ) (P : Partition X) {pi : X → ℝ}
    (hpi : ∀ x, 0 < pi x) (hT : IsStochastic T) (rho : ProbabilityRow X) (m : ℕ) :
    tv (actualLaw T P hT rho m) (referenceLaw T P hpi hT rho m) ≤ mixingBudget T P pi m := by
  apply le_min (tv_le_one _ _)
  have h := kernel_error_dobrushin T P hpi hT m
  have ht := kernel_horizon_tv_sharp T P hpi hT rho m
  unfold exactTerminalBudget at ht
  nlinarith

lemma mixing_budget_le_terminal (T : Matrix X X ℝ) (P : Partition X) {pi : X → ℝ}
    (hpi : ∀ x, 0 < pi x) (hT : IsStochastic T) (m : ℕ) :
    mixingBudget T P pi m ≤ terminalBudget T P pi m := by
  have hQ := RowStochastic.of_existing (coarseKernel_isStochastic T P hpi hT)
  have hs : (∑ j ∈ Finset.range m, dobrushin (CoarseGenerator T P pi) ^ j) ≤ (m : ℝ) := by
    calc
      (∑ j ∈ Finset.range m, dobrushin (CoarseGenerator T P pi) ^ j) ≤
          ∑ _j ∈ Finset.range m, (1 : ℝ) := Finset.sum_le_sum fun j _ =>
        pow_le_one₀ (dobrushin_nonneg _) (dobrushin_le_one hQ)
      _ = m := by simp
  apply min_le_min_left
  have hmul := mul_le_mul_of_nonneg_left hs
    (div_nonneg (norm_nonneg (closureCommutator T P pi)) (by norm_num : (0 : ℝ) ≤ 2))
  unfold rowL1Norm
  linarith

lemma kernel_horizon_tv_uniform_mixing (T : Matrix X X ℝ) (P : Partition X) {pi : X → ℝ}
    (hpi : ∀ x, 0 < pi x) (hT : IsStochastic T) (rho : ProbabilityRow X)
    (hMix : dobrushin (CoarseGenerator T P pi) < 1) (m : ℕ) :
    tv (actualLaw T P hT rho m) (referenceLaw T P hpi hT rho m) ≤
      min 1 (rowL1Norm (closureCommutator T P pi) /
        (2 * (1 - dobrushin (CoarseGenerator T P pi)))) := by
  let d := dobrushin (CoarseGenerator T P pi)
  have hd : 0 < 1 - d := sub_pos.mpr hMix
  have hs : (∑ j ∈ Finset.range m, d ^ j) ≤ 1 / (1 - d) := by
    rw [geom_sum_eq hMix.ne]
    have heq : (d ^ m - 1) / (d - 1) = (1 - d ^ m) / (1 - d) := by
      rw [← neg_sub (1 : ℝ) (d ^ m), ← neg_sub (1 : ℝ) d, neg_div_neg_eq]
    rw [heq]
    apply div_le_div_of_nonneg_right _ hd.le
    linarith [pow_nonneg (dobrushin_nonneg (CoarseGenerator T P pi)) m]
  apply le_min (tv_le_one _ _)
  have ht := le_trans (kernel_horizon_tv_mixing T P hpi hT rho m) (min_le_right _ _)
  have hh := mul_le_mul_of_nonneg_left hs
    (div_nonneg (norm_nonneg (closureCommutator T P pi)) (by norm_num : (0 : ℝ) ≤ 2))
  have heq : rowL1Norm (closureCommutator T P pi) / 2 * (1 / (1 - d)) =
      rowL1Norm (closureCommutator T P pi) / (2 * (1 - d)) := by
    field_simp
  unfold rowL1Norm at ht hh heq ⊢
  linarith

end Mixing

namespace Regression

def point (i : Fin 2) : ProbabilityRow (Fin 2) where
  mass x := if x = i then 1 else 0
  nonneg x := by split_ifs <;> norm_num
  sum_one := by simp

def half : ProbabilityRow (Fin 2) where
  mass _ := 1 / 2
  nonneg _ := by norm_num
  sum_one := by norm_num [Fin.sum_univ_two]

def weights : Fin 2 → ℝ := ![1, 2]

def swap : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

lemma weights_positive (x : Fin 2) : 0 < weights x := by fin_cases x <;> norm_num [weights]

lemma weights_not_normalized : ∑ x, weights x ≠ 1 := by norm_num [weights, Fin.sum_univ_two]

lemma weights_not_stationary : weights ᵥ* swap ≠ weights := by
  intro h
  have h0 := congrFun h 0
  norm_num [Matrix.vecMul, dotProduct, Fin.sum_univ_two, weights, swap] at h0

lemma swap_stochastic : IsStochastic swap where
  nonneg x y := by fin_cases x <;> fin_cases y <;> norm_num [swap]
  row_sum_one x := by fin_cases x <;> norm_num [swap, Fin.sum_univ_two]

lemma point_l1_normalization : l1 ((point 0 : Fin 2 → ℝ) - (point 1 : Fin 2 → ℝ)) = 2 := by
  norm_num [point, l1, Fin.sum_univ_two]

lemma point_tv_normalization : tv (point 0) (point 1) = 1 := by
  norm_num [tv, point_l1_normalization]

lemma point_half_tv : tv (point 0) half = 1 / 2 := by
  norm_num [tv, l1, point, half, Fin.sum_univ_two]

lemma asymmetric_errors (d : Decoder (Fin 2)) :
    d.error (point 0) false = d.probOne 0 ∧
    d.error half true = 1 - (d.probOne 0 + d.probOne 1) / 2 := by
  constructor <;> simp [Decoder.error, Decoder.loss, point, half, Fin.sum_univ_two]
  ring

lemma asymmetric_equal_prior_lower (d : Decoder (Fin 2)) :
    (1 : ℝ) / 4 ≤ (d.error (point 0) false + d.error half true) / 2 := by
  have h := decoder_error_sum_lower d (point 0) half
  rw [point_half_tv] at h
  linarith

lemma asymmetric_minimax_lower (d : Decoder (Fin 2)) :
    (1 : ℝ) / 3 ≤ max (d.error (point 0) false) (d.error half true) := by
  have ha := le_max_left (d.error (point 0) false) (d.error half true)
  have hb := le_max_right (d.error (point 0) false) (d.error half true)
  have he := asymmetric_errors d
  linarith [(d.bounds 1).2]

def averageDecoder : Decoder (Fin 2) where
  probOne := ![0, 1]
  bounds x := by fin_cases x <;> norm_num

def minimaxDecoder : Decoder (Fin 2) where
  probOne := ![1 / 3, 1]
  bounds x := by fin_cases x <;> norm_num

lemma asymmetric_equal_prior_attained :
    (averageDecoder.error (point 0) false + averageDecoder.error half true) / 2 = 1 / 4 := by
  norm_num [Decoder.error, Decoder.loss, averageDecoder, point, half, Fin.sum_univ_two]

lemma asymmetric_minimax_attained :
    max (minimaxDecoder.error (point 0) false) (minimaxDecoder.error half true) = 1 / 3 := by
  norm_num [Decoder.error, Decoder.loss, minimaxDecoder, point, half, Fin.sum_univ_two]

lemma asymmetric_no_both_quarter (d : Decoder (Fin 2)) :
    ¬ (d.error (point 0) false ≤ 1 / 4 ∧ d.error half true ≤ 1 / 4) := by
  intro h
  have hh := max_le h.1 h.2
  linarith [asymmetric_minimax_lower d]

lemma asymmetric_deterministic_minimax_lower (d : Fin 2 → Bool) :
    (1 : ℝ) / 2 ≤ max ((deterministicDecoder d).error (point 0) false)
      ((deterministicDecoder d).error half true) := by
  cases h0 : d 0 <;> cases h1 : d 1 <;>
    norm_num [Decoder.error, Decoder.loss, deterministicDecoder, point, half,
      Fin.sum_univ_two, h0, h1]

lemma asymmetric_deterministic_minimax_attained :
    max ((deterministicDecoder (fun x : Fin 2 => x == 1)).error (point 0) false)
      ((deterministicDecoder (fun x : Fin 2 => x == 1)).error half true) = 1 / 2 := by
  norm_num [Decoder.error, Decoder.loss, deterministicDecoder, point, half, Fin.sum_univ_two]

def erasePartition : Partition (Fin 2) where
  rel := ⊤
  decRel := fun _ _ => isTrue trivial

instance erase_quot_subsingleton : Subsingleton erasePartition.Quot :=
  ⟨fun a b => Quotient.inductionOn₂ a b (fun _ _ => Quotient.sound trivial)⟩

lemma erase_lift_entry (x : Fin 2) (y : erasePartition.Quot) : lift_matrix erasePartition x y = 1 := by
  exact if_pos (Subsingleton.elim _ _)

lemma erase_coarse_eq_one (T : Matrix (Fin 2) (Fin 2) ℝ) (hT : IsStochastic T) :
    CoarseGenerator T erasePartition weights = 1 := by
  ext a b
  have h := (coarseKernel_isStochastic T erasePartition weights_positive hT).row_sum_one a
  have hs : (∑ y, CoarseGenerator T erasePartition weights a y) =
      CoarseGenerator T erasePartition weights a b := by
    refine Finset.sum_eq_single b ?_ ?_
    · intro y _ hy
      exact False.elim (hy (Subsingleton.elim _ _))
    · intro hb
      exact False.elim (hb (Finset.mem_univ b))
  rw [hs] at h
  rw [Matrix.one_apply, if_pos (Subsingleton.elim a b)]
  exact h

lemma identity_stochastic : IsStochastic (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  ⟨RowStochastic.one.nonneg, RowStochastic.one.sum_one⟩

lemma erasing_closure_zero : closureCommutator (1 : Matrix (Fin 2) (Fin 2) ℝ)
    erasePartition weights = 0 := by
  simp [closureCommutator, erase_coarse_eq_one _ identity_stochastic]

lemma erasing_budget_zero (m : ℕ) :
    terminalBudget (1 : Matrix (Fin 2) (Fin 2) ℝ) erasePartition weights m = 0 := by
  simp [terminalBudget, erasing_closure_zero, rowL1Norm]

lemma erasing_actual_equal (p q : ProbabilityRow (Fin 2)) (m : ℕ) :
    actualLaw 1 erasePartition identity_stochastic p m =
      actualLaw 1 erasePartition identity_stochastic q m := by
  apply ProbabilityRow.ext
  intro y
  simp only [actualLaw, ProbabilityRow.push_apply, one_pow, Matrix.one_mul, erase_lift_entry,
    mul_one, p.sum_one, q.sum_one]

lemma erasing_observed_tv_zero (m : ℕ) :
    tv (actualLaw 1 erasePartition identity_stochastic (point 0) m)
      (actualLaw 1 erasePartition identity_stochastic (point 1) m) = 0 := by
  rw [erasing_actual_equal (point 0) (point 1) m, tv_self]

lemma erasing_full_tv_one (m : ℕ) :
    tv ((point 0 : Fin 2 → ℝ) ᵥ* (1 : Matrix (Fin 2) (Fin 2) ℝ) ^ m)
      ((point 1 : Fin 2 → ℝ) ᵥ* (1 : Matrix (Fin 2) (Fin 2) ℝ) ^ m) = 1 := by
  simpa using point_tv_normalization

lemma erasing_exact_transfer (rho : ProbabilityRow (Fin 2))
    (d : Decoder erasePartition.Quot) (b : Bool) (m : ℕ) :
    d.error (actualLaw 1 erasePartition identity_stochastic rho m) b =
      d.error (referenceLaw 1 erasePartition weights_positive identity_stochastic rho m) b := by
  have h := kernel_fixed_decoder_error_transfer 1 erasePartition weights_positive
    identity_stochastic rho d b m
  rw [erasing_budget_zero] at h
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))

lemma erasing_no_both_below_half (d : Decoder erasePartition.Quot) (m : ℕ) :
    ¬ (d.error (actualLaw 1 erasePartition identity_stochastic (point 0) m) false < 1 / 2 ∧
      d.error (actualLaw 1 erasePartition identity_stochastic (point 1) m) true < 1 / 2) := by
  intro h
  have hh := decoder_error_sum_lower d
    (actualLaw 1 erasePartition identity_stochastic (point 0) m)
    (actualLaw 1 erasePartition identity_stochastic (point 1) m)
  rw [erasing_observed_tv_zero] at hh
  linarith

def discretePartition : Partition (Fin 2) where
  rel := ⊥
  decRel := fun x y => inferInstanceAs (Decidable (x = y))

@[simp] lemma discrete_quot_eq (x y : Fin 2) :
    discretePartition.quot_map x = discretePartition.quot_map y ↔ x = y :=
  ⟨fun h => Quotient.exact h, fun h => congrArg _ h⟩

lemma discrete_coarse_entry (T : Matrix (Fin 2) (Fin 2) ℝ) (x y : Fin 2) :
    CoarseGenerator T discretePartition weights
      (discretePartition.quot_map x) (discretePartition.quot_map y) = T x y := by
  fin_cases x <;> fin_cases y <;>
    norm_num [CoarseGenerator, CoarseStationaryDist, pi_bar, Fin.sum_univ_two, weights] <;> ring

lemma discrete_commutator_zero (T : Matrix (Fin 2) (Fin 2) ℝ) :
    closureCommutator T discretePartition weights = 0 := by
  ext x y
  obtain ⟨z, rfl⟩ := Quotient.exists_rep y
  rw [closureCommutator_entry]
  change row_sum_block T discretePartition x (discretePartition.quot_map z) -
    CoarseGenerator T discretePartition weights
      (discretePartition.quot_map x) (discretePartition.quot_map z) = 0
  rw [discrete_coarse_entry]
  simp [row_sum_block]

lemma nonstationary_reference_exact (rho : ProbabilityRow (Fin 2)) (m : ℕ) :
    tv (actualLaw swap discretePartition swap_stochastic rho m)
      (referenceLaw swap discretePartition weights_positive swap_stochastic rho m) = 0 := by
  apply le_antisymm _ (tv_nonneg _ _)
  have h := kernel_horizon_tv swap discretePartition weights_positive swap_stochastic rho m
  simpa [terminalBudget, discrete_commutator_zero, rowL1Norm] using h

def erasingCoin : Decoder erasePartition.Quot where
  probOne _ := 1 / 2
  bounds _ := by norm_num

lemma erasing_threshold_equality (p : ProbabilityRow erasePartition.Quot) :
    tv p p = 0 ∧ erasingCoin.error p false = 1 / 2 ∧ erasingCoin.error p true = 1 / 2 := by
  refine ⟨tv_self p, ?_, ?_⟩
  · simp [Decoder.error, Decoder.loss, erasingCoin, ← Finset.sum_mul, p.sum_one]
  · simp [Decoder.error, Decoder.loss, erasingCoin, ← Finset.sum_mul, p.sum_one]
    norm_num

lemma swap_dobrushin_one : dobrushin swap = 1 := by
  apply le_antisymm (dobrushin_le_one (RowStochastic.of_existing swap_stochastic))
  have h := row_tv_le_dobrushin swap 0 1
  norm_num [tv, l1, swap, Fin.sum_univ_two] at h
  exact h

def reset : Matrix (Fin 2) (Fin 2) ℝ := fun _ _ => 1 / 2

lemma reset_stochastic : RowStochastic reset where
  nonneg _ _ := by norm_num [reset]
  sum_one _ := by norm_num [reset, Fin.sum_univ_two]

lemma reset_dobrushin_zero : dobrushin reset = 0 := by
  have h : rowDifferences reset = 0 := by ext x y; simp [rowDifferences, reset]
  simp [dobrushin, h, rowL1Norm]

lemma reset_forgets_both_inputs : tv ((point 0 : Fin 2 → ℝ) ᵥ* reset)
    ((point 1 : Fin 2 → ℝ) ᵥ* reset) = 0 := by
  apply le_antisymm _ (tv_nonneg _ _)
  simpa [reset_dobrushin_zero] using tv_dobrushin_contraction (point 0) (point 1) reset

end Regression

end SGC.Bridge.TerminalDecoding

end
