/-
Copyright (c) 2026 Jason Shroyer. All rights reserved.
Released under Apache 2.0 license.
-/
import SGC.Renormalization.MeasureReentry
import Mathlib.Analysis.Matrix.Normed

/-!
# The Kernel Horizon Theorem

The measure-reentry program's first genuine *dynamic* statement: for a
discrete Markov kernel, the finite-time closure error grows **at most
linearly in the number of steps, with rate constant exactly the norm of
the closure commutator** — hence the validity horizon of the canonical
macro-law is inverse in the defect.

Physical time is unambiguous here (the colleague's calibration point): `T`
is a one-step transition kernel, `T^n` is the state after `n` steps.

## Main results

* `IsStochastic` — row-stochastic kernels (entrywise nonnegative, unit row
  sums).
* `coarseKernel_isStochastic` — the canonical coarse kernel
  `T̂^π = CoarseGenerator T P π` of a stochastic kernel is stochastic:
  the conditional exit average of a probability kernel is a probability
  kernel.
* `linfty_opNorm_le_one_of_stochastic`, `stochastic_pow_norm_le_one`,
  `lift_matrix_linfty_le_one` — all propagators are non-expansive in the
  `L∞ → L∞` operator norm (max row L¹ norm).
* **`kernel_closure_error_le`** — THE KERNEL HORIZON THEOREM:
  `‖T^n·K − K·(T̂^π)^n‖ ≤ n · ‖𝒞_T‖`.
  Finite-time closure error is at most (number of steps) × (one re-entry
  event's size). Immediate from the discrete Duhamel identity
  (`power_closure_telescoping`) plus non-expansiveness.
* `within_tolerance_of_defect_small` — the horizon reading: every step
  count `n` with `n·‖𝒞_T‖ ≤ η` is inside the tolerance-`η` validity
  horizon. Inverse-defect scaling of the horizon, as a theorem.

## Honest scope

* The `L∞` operator norm of `𝒞_T` is `max_i Σ_B |residual(i,B)|` — the
  worst-state total re-entry rate (`𝔇_∞`-flavoured). The relation to the
  `π`-weighted `𝔇_π` (Cauchy-Schwarz, cardinality factors) is a planned
  elementary lemma, not stated here.
* Linear-in-`n` is an upper bound; no claim that it is tight (mixing can
  make the true error saturate — that refinement is the open
  `T_η ~ 1/𝔇` scaling question, `docs/measure-reentry.md` §3).
* Continuous-time bridge (`T = e^{ΔtL}`, error `≤ Δt·𝔇_π + O(Δt²)`) is
  deliberately NOT attempted here (colleague's sequencing: after the
  discrete theorem).
-/

namespace SGC.Renormalization.KernelHorizon

open Finset Matrix
open scoped NNReal
open SGC SGC.Thermodynamics SGC.Renormalization.MeasureReentry

attribute [local instance] Matrix.linftyOpNormedAddCommGroup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## §1. Stochastic kernels and their coarse counterparts -/

/-- A row-stochastic kernel: nonnegative entries, unit row sums. -/
structure IsStochastic (T : Matrix V V ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ T i j
  row_sum_one : ∀ i, ∑ j, T i j = 1

/-- Block row sums over all blocks recover the total row sum. -/
lemma sum_row_sum_block (M : Matrix V V ℝ) (P : Partition V) (i : V) :
    ∑ B : P.Quot, row_sum_block M P i B = ∑ j, M i j := by
  unfold row_sum_block
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

/-- The canonical coarse kernel of a stochastic kernel is stochastic. -/
theorem coarseKernel_isStochastic (T : Matrix V V ℝ) (P : Partition V)
    {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x) (hT : IsStochastic T) :
    IsStochastic (CoarseGenerator T P pi_dist) where
  nonneg := by
    intro A B
    have hpos : 0 < CoarseStationaryDist P pi_dist A := pi_bar_pos P hπ A
    unfold CoarseGenerator
    rw [if_neg hpos.ne']
    refine mul_nonneg (by positivity) ?_
    refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_
    by_cases h : P.quot_map x = A ∧ P.quot_map y = B
    · rw [if_pos h]
      exact mul_nonneg (hπ x).le (hT.nonneg x y)
    · rw [if_neg h]
  row_sum_one := by
    intro A
    have hpos : 0 < CoarseStationaryDist P pi_dist A := pi_bar_pos P hπ A
    have hrow : ∀ B, CoarseGenerator T P pi_dist A B
        = (1 / CoarseStationaryDist P pi_dist A) * BlockRate T P pi_dist A B := by
      intro B
      unfold CoarseGenerator BlockRate
      rw [if_neg hpos.ne']
    simp_rw [hrow, ← Finset.mul_sum]
    have hblocks : (∑ B : P.Quot, BlockRate T P pi_dist A B)
        = CoarseStationaryDist P pi_dist A := by
      have h1 : ∀ B, BlockRate T P pi_dist A B
          = ∑ i : V, (if P.quot_map i = A
              then pi_dist i * row_sum_block T P i B else 0) :=
        fun B => blockRate_eq_sum_pi_mul_exit T P pi_dist A B
      simp_rw [h1]
      rw [Finset.sum_comm]
      unfold CoarseStationaryDist pi_bar
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : P.quot_map i = A
      · simp only [hi, if_true]
        rw [← Finset.mul_sum, sum_row_sum_block, hT.row_sum_one i, mul_one]
      · simp [hi]
    rw [hblocks]
    field_simp

/-! ## §2. Non-expansiveness in the `L∞ → L∞` norm -/

/-- A matrix with nonnegative entries and row sums `≤ 1` is non-expansive
in the `L∞` operator norm. -/
lemma linfty_opNorm_le_one_of_rows (M : Matrix V V ℝ)
    (hnn : ∀ i j, 0 ≤ M i j) (hrow : ∀ i, ∑ j, M i j ≤ 1) :
    ‖M‖ ≤ 1 := by
  rw [Matrix.linfty_opNorm_def]
  rw [show (1 : ℝ) = ((1 : ℝ≥0) : ℝ) by norm_num]
  rw [NNReal.coe_le_coe]
  refine Finset.sup_le fun i _ => ?_
  have hcoe : ((∑ j, ‖M i j‖₊ : ℝ≥0) : ℝ) = ∑ j, M i j := by
    push_cast
    exact Finset.sum_congr rfl fun j _ =>
      Real.norm_of_nonneg (hnn i j)
  have : ((∑ j, ‖M i j‖₊ : ℝ≥0) : ℝ) ≤ ((1 : ℝ≥0) : ℝ) := by
    rw [hcoe]
    simpa using hrow i
  exact_mod_cast this

lemma linfty_opNorm_le_one_of_stochastic (T : Matrix V V ℝ)
    (hT : IsStochastic T) : ‖T‖ ≤ 1 :=
  linfty_opNorm_le_one_of_rows T hT.nonneg fun i => (hT.row_sum_one i).le

/-- Powers of a stochastic kernel are non-expansive. -/
lemma stochastic_pow_norm_le_one (T : Matrix V V ℝ) (hT : IsStochastic T)
    (n : ℕ) : ‖T ^ n‖ ≤ 1 := by
  induction n with
  | zero =>
    rw [pow_zero]
    refine linfty_opNorm_le_one_of_rows _ ?_ ?_
    · intro i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    · intro i
      simp [Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ]
    calc ‖T ^ n * T‖ ≤ ‖T ^ n‖ * ‖T‖ := Matrix.linfty_opNorm_mul _ _
      _ ≤ 1 * 1 := by
          exact mul_le_mul ih (linfty_opNorm_le_one_of_stochastic T hT)
            (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num

/-- The lift matrix has exactly one unit entry per row: non-expansive. -/
lemma lift_matrix_linfty_le_one (P : Partition V) : ‖lift_matrix P‖ ≤ 1 := by
  refine le_trans (le_of_eq (Matrix.linfty_opNorm_def _)) ?_
  rw [show (1 : ℝ) = ((1 : ℝ≥0) : ℝ) by norm_num, NNReal.coe_le_coe]
  refine Finset.sup_le fun i _ => ?_
  have : ∀ B : P.Quot, ‖lift_matrix P i B‖₊
      = if P.quot_map i = B then 1 else 0 := by
    intro B
    unfold lift_matrix
    by_cases h : P.quot_map i = B <;> simp [h]
  rw [Finset.sum_congr rfl fun B _ => this B]
  simp

/-! ## §3. The Kernel Horizon Theorem -/

/-- **THE KERNEL HORIZON THEOREM.** For a stochastic kernel `T` and any
partition `P` with positive reference measure, the `n`-step closure error
of the canonical macro-kernel is at most `n` times the size of a single
re-entry event:

`‖T^n·K − K·(T̂^π)^n‖ ≤ n · ‖𝒞_T‖`.

Proof: the discrete Duhamel identity expands the error into `n` single
re-entry events; every fine and coarse propagator is non-expansive; the
triangle inequality does the rest. -/
theorem kernel_closure_error_le (T : Matrix V V ℝ) (P : Partition V)
    {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x) (hT : IsStochastic T)
    (n : ℕ) :
    ‖T ^ n * lift_matrix P
      - lift_matrix P * (CoarseGenerator T P pi_dist) ^ n‖
      ≤ (n : ℝ) * ‖closureCommutator T P pi_dist‖ := by
  rw [power_closure_telescoping]
  calc ‖∑ k ∈ Finset.range n,
        T ^ (n - 1 - k) * closureCommutator T P pi_dist
          * (CoarseGenerator T P pi_dist) ^ k‖
      ≤ ∑ k ∈ Finset.range n,
        ‖T ^ (n - 1 - k) * closureCommutator T P pi_dist
          * (CoarseGenerator T P pi_dist) ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range n, ‖closureCommutator T P pi_dist‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        have h1 : ‖T ^ (n - 1 - k) * closureCommutator T P pi_dist
            * (CoarseGenerator T P pi_dist) ^ k‖
            ≤ ‖T ^ (n - 1 - k) * closureCommutator T P pi_dist‖
              * ‖(CoarseGenerator T P pi_dist) ^ k‖ :=
          Matrix.linfty_opNorm_mul _ _
        have h2 : ‖T ^ (n - 1 - k) * closureCommutator T P pi_dist‖
            ≤ ‖T ^ (n - 1 - k)‖ * ‖closureCommutator T P pi_dist‖ :=
          Matrix.linfty_opNorm_mul _ _
        have h3 : ‖T ^ (n - 1 - k)‖ ≤ 1 := stochastic_pow_norm_le_one T hT _
        have h4 : ‖(CoarseGenerator T P pi_dist) ^ k‖ ≤ 1 :=
          stochastic_pow_norm_le_one _ (coarseKernel_isStochastic T P hπ hT) k
        have hC : (0:ℝ) ≤ ‖closureCommutator T P pi_dist‖ := norm_nonneg _
        calc ‖T ^ (n - 1 - k) * closureCommutator T P pi_dist
              * (CoarseGenerator T P pi_dist) ^ k‖
            ≤ ‖T ^ (n - 1 - k)‖ * ‖closureCommutator T P pi_dist‖
                * ‖(CoarseGenerator T P pi_dist) ^ k‖ := by
              calc _ ≤ _ := h1
              _ ≤ _ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
          _ ≤ 1 * ‖closureCommutator T P pi_dist‖ * 1 := by
              have := mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right h3 hC) (norm_nonneg
                  ((CoarseGenerator T P pi_dist) ^ k))
              calc ‖T ^ (n - 1 - k)‖ * ‖closureCommutator T P pi_dist‖
                    * ‖(CoarseGenerator T P pi_dist) ^ k‖
                  ≤ 1 * ‖closureCommutator T P pi_dist‖
                    * ‖(CoarseGenerator T P pi_dist) ^ k‖ := this
                _ ≤ 1 * ‖closureCommutator T P pi_dist‖ * 1 := by
                    refine mul_le_mul_of_nonneg_left h4 ?_
                    positivity
          _ = ‖closureCommutator T P pi_dist‖ := by ring
    _ = (n : ℝ) * ‖closureCommutator T P pi_dist‖ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **The horizon reading**: every step count `n` with `n·‖𝒞_T‖ ≤ η` lies
inside the tolerance-`η` validity horizon of the canonical macro-law. The
horizon scales at least inversely in the re-entry defect. -/
theorem within_tolerance_of_defect_small (T : Matrix V V ℝ) (P : Partition V)
    {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x) (hT : IsStochastic T)
    {η : ℝ} (n : ℕ)
    (h : (n : ℝ) * ‖closureCommutator T P pi_dist‖ ≤ η) :
    ‖T ^ n * lift_matrix P
      - lift_matrix P * (CoarseGenerator T P pi_dist) ^ n‖ ≤ η :=
  le_trans (kernel_closure_error_le T P hπ hT n) h

/-! ## §4. Centered commutator and geometric accumulation -/

/-- **The commutator's columns are π-centered**: for every target block,
the `π`-weighted total of the residual field vanishes — pure algebra, no
stationarity of `π` required (the block-mass weighting cancels exactly).
This is why mixing hypotheses on centered observables are the natural
route to sub-linear error accumulation: the closure commutator lives in
exactly the subspace that mixing contracts. -/
theorem commutator_columns_centered (T : Matrix V V ℝ) (P : Partition V)
    {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x) (B : P.Quot) :
    ∑ x : V, pi_dist x * closureCommutator T P pi_dist x B = 0 := by
  have hsplit : ∀ (f : V → ℝ), (∑ x : V, f x)
      = ∑ A : P.Quot, ∑ x : V, if P.quot_map x = A then f x else 0 := by
    intro f
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp
  simp_rw [closureCommutator_entry, MeasureReentry.residual, mul_sub]
  rw [Finset.sum_sub_distrib]
  have h1 : (∑ x : V, pi_dist x * row_sum_block T P x B)
      = ∑ A : P.Quot, BlockRate T P pi_dist A B := by
    rw [hsplit (fun x => pi_dist x * row_sum_block T P x B)]
    exact Finset.sum_congr rfl fun A _ =>
      (blockRate_eq_sum_pi_mul_exit T P pi_dist A B).symm
  have h2 : (∑ x : V, pi_dist x
        * CoarseGenerator T P pi_dist (P.quot_map x) B)
      = ∑ A : P.Quot, BlockRate T P pi_dist A B := by
    rw [hsplit (fun x => pi_dist x
      * CoarseGenerator T P pi_dist (P.quot_map x) B)]
    refine Finset.sum_congr rfl fun A _ => ?_
    have hstep : (∑ x : V, if P.quot_map x = A
        then pi_dist x * CoarseGenerator T P pi_dist (P.quot_map x) B else 0)
        = CoarseGenerator T P pi_dist A B
          * ∑ x : V, (if P.quot_map x = A then pi_dist x else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : P.quot_map x = A
      · simp [hx, mul_comm]
      · simp [hx]
    rw [hstep]
    have hpos : 0 < CoarseStationaryDist P pi_dist A := pi_bar_pos P hπ A
    have hQ : CoarseGenerator T P pi_dist A B
        = (1 / CoarseStationaryDist P pi_dist A) * BlockRate T P pi_dist A B := by
      unfold CoarseGenerator BlockRate
      rw [if_neg hpos.ne']
    have hmass : (∑ x : V, if P.quot_map x = A then pi_dist x else 0)
        = CoarseStationaryDist P pi_dist A := rfl
    rw [hQ, hmass]
    field_simp
  rw [h1, h2, sub_self]

/-- **Geometric accumulation** under an abstract mixing hypothesis: if the
fine dynamics contracts the commutator geometrically
(`‖T^m·𝒞‖ ≤ α^m·‖𝒞‖`), the closure error is bounded by the geometric
series instead of `n·‖𝒞‖`. The hypothesis is NOT claimed for arbitrary
stochastic kernels — `commutator_columns_centered` is exactly why mixing
chains satisfy it on the relevant subspace, but that spectral argument is
future work. -/
theorem kernel_closure_error_le_geom (T : Matrix V V ℝ) (P : Partition V)
    {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x) (hT : IsStochastic T)
    {α : ℝ}
    (hmix : ∀ m : ℕ, ‖T ^ m * closureCommutator T P pi_dist‖
      ≤ α ^ m * ‖closureCommutator T P pi_dist‖) (n : ℕ) :
    ‖T ^ n * lift_matrix P
      - lift_matrix P * (CoarseGenerator T P pi_dist) ^ n‖
      ≤ (∑ k ∈ Finset.range n, α ^ k)
        * ‖closureCommutator T P pi_dist‖ := by
  rw [power_closure_telescoping]
  calc ‖∑ k ∈ Finset.range n,
        T ^ (n - 1 - k) * closureCommutator T P pi_dist
          * (CoarseGenerator T P pi_dist) ^ k‖
      ≤ ∑ k ∈ Finset.range n,
        ‖T ^ (n - 1 - k) * closureCommutator T P pi_dist
          * (CoarseGenerator T P pi_dist) ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range n,
        α ^ (n - 1 - k) * ‖closureCommutator T P pi_dist‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        calc ‖T ^ (n - 1 - k) * closureCommutator T P pi_dist
              * (CoarseGenerator T P pi_dist) ^ k‖
            ≤ ‖T ^ (n - 1 - k) * closureCommutator T P pi_dist‖
              * ‖(CoarseGenerator T P pi_dist) ^ k‖ :=
              Matrix.linfty_opNorm_mul _ _
          _ ≤ ‖T ^ (n - 1 - k) * closureCommutator T P pi_dist‖ * 1 := by
              refine mul_le_mul_of_nonneg_left
                (stochastic_pow_norm_le_one _
                  (coarseKernel_isStochastic T P hπ hT) k)
                (norm_nonneg _)
          _ = ‖T ^ (n - 1 - k) * closureCommutator T P pi_dist‖ := by ring
          _ ≤ α ^ (n - 1 - k) * ‖closureCommutator T P pi_dist‖ :=
              hmix (n - 1 - k)
    _ = (∑ k ∈ Finset.range n, α ^ k)
        * ‖closureCommutator T P pi_dist‖ := by
        rw [Finset.sum_mul]
        exact Finset.sum_range_reflect
          (fun k => α ^ k * ‖closureCommutator T P pi_dist‖) n
    _ = (∑ k ∈ Finset.range n, α ^ k)
        * ‖closureCommutator T P pi_dist‖ := rfl

/-- **UNIFORM-IN-TIME APPROXIMATE CLOSURE.** Under geometric mixing with
rate `α < 1`, the macro-law's closure error NEVER exceeds `‖𝒞‖/(1−α)` —
at any time horizon. Imperfect emergence with mixing is eternally
approximately valid: the leak is bounded, not cumulative. -/
theorem kernel_closure_error_le_uniform (T : Matrix V V ℝ) (P : Partition V)
    {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x) (hT : IsStochastic T)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hmix : ∀ m : ℕ, ‖T ^ m * closureCommutator T P pi_dist‖
      ≤ α ^ m * ‖closureCommutator T P pi_dist‖) (n : ℕ) :
    ‖T ^ n * lift_matrix P
      - lift_matrix P * (CoarseGenerator T P pi_dist) ^ n‖
      ≤ (1 / (1 - α)) * ‖closureCommutator T P pi_dist‖ := by
  refine le_trans (kernel_closure_error_le_geom T P hπ hT hmix n) ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have h1α : (0:ℝ) < 1 - α := by linarith
  rw [geom_sum_eq hα1.ne n]
  have hrw : (α ^ n - 1) / (α - 1) = (1 - α ^ n) / (1 - α) := by
    rw [← neg_sub (1:ℝ) (α ^ n), ← neg_sub (1:ℝ) α, neg_div_neg_eq]
  rw [hrw]
  gcongr <;> linarith [pow_nonneg hα0 n]

/-- At zero defect the macro-law is eternally exact — the `ε = 0` pole of
the horizon theorem, recovering the intertwining/eternal-closure regime. -/
theorem eternal_closure_of_zero_commutator (T : Matrix V V ℝ)
    (P : Partition V) (pi_dist : V → ℝ)
    (h : closureCommutator T P pi_dist = 0) (n : ℕ) :
    T ^ n * lift_matrix P
      = lift_matrix P * (CoarseGenerator T P pi_dist) ^ n := by
  have h0 := power_closure_telescoping T P pi_dist n
  rw [h] at h0
  have hz : T ^ n * lift_matrix P
      - lift_matrix P * (CoarseGenerator T P pi_dist) ^ n = 0 := by
    rw [h0]
    refine Finset.sum_eq_zero fun k _ => ?_
    simp
  exact sub_eq_zero.mp hz
