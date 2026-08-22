/-
Copyright (c) 2026 Jason Shroyer. All rights reserved.
Released under Apache 2.0 license.
-/
import SGC.Renormalization.KernelHorizon
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Sqrt

/-!
# The Physical-Time Horizon: exact Euler bridge + norm conversion

Two results that complete the causal chain
`𝔇_π ⟹ ‖𝒞‖∞ ⟹ T_η` in **physical time**.

## 1. The exact Euler bridge (no `O(Δt²)` loss)

Coarse-graining is affine-linear in the generator, and the coarse of the
identity is the identity. Hence for the first-order propagator
`T_Δt = 1 + Δt·L`:

* `coarseGenerator_eulerStep` — **discretize-then-coarse-grain equals
  coarse-grain-then-discretize**: `(T_Δt)^π = 1 + Δt·Q^π`. The canonical
  macro-kernel of the Euler step is the Euler step of the canonical macro
  generator. No commuting-square defect at the level of construction.
* `closureCommutator_eulerStep` — the one-step closure commutator scales
  EXACTLY: `𝒞(T_Δt) = Δt • 𝒞(L)`. The brief asked for
  `≤ Δt·‖𝒞_L‖ + O(Δt²)`; the true statement is equality with no
  second-order term, because both discretization and coarse-graining are
  affine in the generator.
* `eulerStep_isStochastic` — for a generator (nonnegative off-diagonal,
  zero row sums) and `Δt` below the CFL-type step bound
  `Δt·(−L_ii) ≤ 1`, the Euler step is a bona fide stochastic kernel.
* **`physical_time_closure_error`** — composing with the Kernel Horizon
  Theorem: for `n` Euler steps of size `Δt`, i.e. physical time
  `t = n·Δt`, the closure error obeys `‖·‖ ≤ (n·Δt)·‖𝒞_L‖ = t·‖𝒞_L‖`,
  **uniformly in the discretization**. Physical time enters honestly: the
  bound depends on `n` and `Δt` only through their product.

## 2. The norm-conversion theorem (unifying the defect faces)

* `linfty_opNorm_le_of_rows` — reusable row-sum criterion for the `L∞`
  operator norm.
* **`commutator_linfty_le_sqrt_defect`** — under a stationary lower bound
  `0 < p_min ≤ π`, Cauchy-Schwarz per row converts the stationary defect
  into the worst-case norm:
  `‖𝒞‖∞ ≤ √(|Quot|·𝔇_π²/p_min)`.
  The constant `√(|Quot|/p_min)` is stated exactly and NOT claimed tight:
  rare states (small `π_i`) inflate it — precisely the reason the two
  faces differ, and the reason a local-occupancy refinement is the
  recorded next step (`docs/measure-reentry.md` §2).
* **`end_to_end_physical_horizon`** — the composed chain, one theorem:
  stationary defect ⟹ worst-case commutator ⟹ physical-time closure
  error: `‖error(t = n·Δt)‖ ≤ t·√(|Quot|·𝔇_π²/p_min)`.

## Honest scope

* `T_Δt = 1 + Δt·L` is the first-order (Euler) propagator, not `e^{ΔtL}`;
  the exponential bridge remains open (design target: Duhamel for
  `Matrix.exp`, where the `O(Δt²)` questions genuinely live).
* Linear-in-`t` accumulation is the no-assumptions baseline; mixing /
  contraction refinements (geometric series) are open.
* All bounds are worst-case (`L∞`); stationary-average dynamic bounds in
  a `π`-weighted norm are the other recorded open route.
-/

namespace SGC.Renormalization.PhysicalHorizon

open Finset Matrix
open scoped NNReal
open SGC SGC.Thermodynamics SGC.Renormalization.MeasureReentry
  SGC.Renormalization.KernelHorizon

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpIsBoundedSMul
attribute [local instance] Matrix.linftyOpNormSMulClass

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## §1. Coarse-graining is affine in the generator -/

lemma blockRate_add (M N : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (a_bar b_bar : P.Quot) :
    BlockRate (M + N) P pi_dist a_bar b_bar
      = BlockRate M P pi_dist a_bar b_bar
        + BlockRate N P pi_dist a_bar b_bar := by
  unfold BlockRate
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases h : P.quot_map x = a_bar ∧ P.quot_map y = b_bar
  · simp [h, Matrix.add_apply, mul_add]
  · simp [h]

lemma blockRate_smul (c : ℝ) (M : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (a_bar b_bar : P.Quot) :
    BlockRate (c • M) P pi_dist a_bar b_bar
      = c * BlockRate M P pi_dist a_bar b_bar := by
  unfold BlockRate
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases h : P.quot_map x = a_bar ∧ P.quot_map y = b_bar
  · simp [h, Matrix.smul_apply]
    ring
  · simp [h]

lemma blockRate_one (P : Partition V) (pi_dist : V → ℝ) (a_bar b_bar : P.Quot) :
    BlockRate (1 : Matrix V V ℝ) P pi_dist a_bar b_bar
      = if a_bar = b_bar then CoarseStationaryDist P pi_dist a_bar else 0 := by
  unfold BlockRate CoarseStationaryDist pi_bar
  rw [Finset.sum_comm]
  by_cases hab : a_bar = b_bar
  · subst hab
    rw [if_pos rfl]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single x]
    · by_cases hx : P.quot_map x = a_bar
      · simp [hx, Matrix.one_apply]
      · simp [hx]
    · intro y _ hyx
      by_cases hy : P.quot_map x = a_bar ∧ P.quot_map y = a_bar
      · simp [hy, Matrix.one_apply, Ne.symm hyx]
      · simp [hy]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [if_neg hab]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun x _ => ?_
    refine Finset.sum_eq_zero fun y _ => ?_
    by_cases hxy : P.quot_map x = a_bar ∧ P.quot_map y = b_bar
    · have hne : x ≠ y := by
        rintro rfl
        exact hab (hxy.1 ▸ hxy.2 ▸ rfl)
      simp [hxy, Matrix.one_apply, hne]
    · simp [hxy]

/-- Coarse-graining is additive in the fine operator. -/
lemma coarseGenerator_add (M N : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) :
    CoarseGenerator (M + N) P pi_dist
      = CoarseGenerator M P pi_dist + CoarseGenerator N P pi_dist := by
  funext a_bar b_bar
  unfold CoarseGenerator
  by_cases h : CoarseStationaryDist P pi_dist a_bar = 0
  · simp [h]
  · simp only [if_neg h, Matrix.add_apply]
    have hsplit : (∑ x : V, ∑ y : V,
        if P.quot_map x = a_bar ∧ P.quot_map y = b_bar
          then pi_dist x * (M x y + N x y) else 0)
        = (∑ x : V, ∑ y : V,
            if P.quot_map x = a_bar ∧ P.quot_map y = b_bar
              then pi_dist x * M x y else 0)
          + (∑ x : V, ∑ y : V,
            if P.quot_map x = a_bar ∧ P.quot_map y = b_bar
              then pi_dist x * N x y else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      by_cases hg : P.quot_map x = a_bar ∧ P.quot_map y = b_bar
      · simp [hg, mul_add]
      · simp [hg]
    rw [hsplit, mul_add]

/-- Coarse-graining commutes with scalar rescaling. -/
lemma coarseGenerator_smul (c : ℝ) (M : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) :
    CoarseGenerator (c • M) P pi_dist = c • CoarseGenerator M P pi_dist := by
  funext a_bar b_bar
  unfold CoarseGenerator
  by_cases h : CoarseStationaryDist P pi_dist a_bar = 0
  · simp [h]
  · simp only [if_neg h, Matrix.smul_apply, smul_eq_mul]
    have hsplit : (∑ x : V, ∑ y : V,
        if P.quot_map x = a_bar ∧ P.quot_map y = b_bar
          then pi_dist x * (c * M x y) else 0)
        = c * (∑ x : V, ∑ y : V,
            if P.quot_map x = a_bar ∧ P.quot_map y = b_bar
              then pi_dist x * M x y else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      by_cases hg : P.quot_map x = a_bar ∧ P.quot_map y = b_bar
      · simp only [hg, and_self, if_true]
        ring
      · simp [hg]
    rw [hsplit]
    ring

/-- The coarse of the identity is the identity (positive reference mass). -/
lemma coarseGenerator_one (P : Partition V) {pi_dist : V → ℝ}
    (hπ : ∀ x, 0 < pi_dist x) :
    CoarseGenerator (1 : Matrix V V ℝ) P pi_dist = 1 := by
  funext a_bar b_bar
  have hpos : 0 < CoarseStationaryDist P pi_dist a_bar := pi_bar_pos P hπ a_bar
  unfold CoarseGenerator
  rw [if_neg hpos.ne']
  have hone := blockRate_one P pi_dist a_bar b_bar
  unfold BlockRate at hone
  rw [hone]
  by_cases hab : a_bar = b_bar
  · subst hab
    rw [if_pos rfl, Matrix.one_apply_eq]
    field_simp
  · rw [if_neg hab, Matrix.one_apply_ne hab, mul_zero]

/-! ## §2. The exact Euler bridge -/

/-- The first-order (Euler) propagator of a generator. -/
noncomputable def eulerStep (dt : ℝ) (L : Matrix V V ℝ) : Matrix V V ℝ :=
  1 + dt • L

/-- **Discretize-then-coarse-grain = coarse-grain-then-discretize.** The
canonical macro-kernel of the Euler step is the Euler step of the
canonical macro-generator — exactly. -/
theorem coarseGenerator_eulerStep (dt : ℝ) (L : Matrix V V ℝ)
    (P : Partition V) {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x) :
    CoarseGenerator (eulerStep dt L) P pi_dist
      = eulerStep dt (CoarseGenerator L P pi_dist) := by
  unfold eulerStep
  rw [coarseGenerator_add, coarseGenerator_smul, coarseGenerator_one P hπ]

/-- **The closure commutator scales exactly**: `𝒞(1 + Δt·L) = Δt·𝒞(L)`.
No second-order term — discretization and coarse-graining are both affine
in the generator, so the obstruction is homogeneous of degree one. -/
theorem closureCommutator_eulerStep (dt : ℝ) (L : Matrix V V ℝ)
    (P : Partition V) {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x) :
    closureCommutator (eulerStep dt L) P pi_dist
      = dt • closureCommutator L P pi_dist := by
  unfold closureCommutator
  rw [coarseGenerator_eulerStep dt L P hπ]
  unfold eulerStep
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, smul_sub]
  abel

/-- A conservative rate generator: nonnegative off-diagonal, zero row sums. -/
structure IsGenerator (L : Matrix V V ℝ) : Prop where
  offdiag_nonneg : ∀ i j, i ≠ j → 0 ≤ L i j
  row_sum_zero : ∀ i, ∑ j, L i j = 0

/-- Under the CFL-type step bound `Δt·(−L_ii) ≤ 1`, the Euler step of a
generator is a bona fide stochastic kernel. -/
theorem eulerStep_isStochastic (dt : ℝ) (L : Matrix V V ℝ)
    (hL : IsGenerator L) (hdt : 0 ≤ dt)
    (hstep : ∀ i, dt * (-(L i i)) ≤ 1) :
    IsStochastic (eulerStep dt L) where
  nonneg := by
    intro i j
    unfold eulerStep
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    by_cases h : i = j
    · subst h
      rw [Matrix.one_apply_eq]
      have := hstep i
      nlinarith
    · rw [Matrix.one_apply_ne h]
      have := hL.offdiag_nonneg i j h
      nlinarith
  row_sum_one := by
    intro i
    unfold eulerStep
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hL.row_sum_zero i, mul_zero,
      add_zero]
    simp [Matrix.one_apply]

/-- **THE PHYSICAL-TIME CLOSURE ERROR THEOREM.** For `n` Euler steps of
size `Δt` — physical time `t = n·Δt` — the closure error of the canonical
macro-law obeys

`‖T_Δt^n·K − K·(T̂_Δt)^n‖ ≤ (n·Δt) · ‖𝒞_L‖ = t · ‖𝒞_L‖`,

uniformly in the discretization: the bound depends on `n` and `Δt` only
through the physical time `t`. The generator commutator is the physical
leak rate. -/
theorem physical_time_closure_error (dt : ℝ) (L : Matrix V V ℝ)
    (P : Partition V) {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x)
    (hL : IsGenerator L) (hdt : 0 ≤ dt)
    (hstep : ∀ i, dt * (-(L i i)) ≤ 1) (n : ℕ) :
    ‖(eulerStep dt L) ^ n * lift_matrix P
      - lift_matrix P * (eulerStep dt (CoarseGenerator L P pi_dist)) ^ n‖
      ≤ ((n : ℝ) * dt) * ‖closureCommutator L P pi_dist‖ := by
  have hmain := kernel_closure_error_le (eulerStep dt L) P hπ
    (eulerStep_isStochastic dt L hL hdt hstep) n
  rw [coarseGenerator_eulerStep dt L P hπ] at hmain
  rw [closureCommutator_eulerStep dt L P hπ] at hmain
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hdt] at hmain
  calc ‖(eulerStep dt L) ^ n * lift_matrix P
      - lift_matrix P * (eulerStep dt (CoarseGenerator L P pi_dist)) ^ n‖
      ≤ (n : ℝ) * (dt * ‖closureCommutator L P pi_dist‖) := hmain
    _ = ((n : ℝ) * dt) * ‖closureCommutator L P pi_dist‖ := by ring

/-! ## §3. The norm-conversion theorem -/

/-- Row-sum criterion for the `L∞` operator norm (reusable helper). -/
lemma linfty_opNorm_le_of_rows {W : Type*} [Fintype W] (M : Matrix V W ℝ)
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ i, ∑ j, |M i j| ≤ c) : ‖M‖ ≤ c := by
  rw [Matrix.linfty_opNorm_def]
  rw [show c = ((c.toNNReal : ℝ≥0) : ℝ) from (Real.coe_toNNReal c hc).symm]
  rw [NNReal.coe_le_coe]
  refine Finset.sup_le fun i _ => ?_
  rw [← NNReal.coe_le_coe]
  push_cast
  calc (∑ j, ‖M i j‖) ≤ c := by
        simpa [Real.norm_eq_abs] using h i
    _ = ((c.toNNReal : ℝ≥0) : ℝ) := by
        rw [Real.coe_toNNReal c hc]

/-- Any single row's re-entry mass is dominated by the total defect over
its own stationary weight. -/
lemma row_commutator_sq_le_defectSq (L : Matrix V V ℝ) (P : Partition V)
    {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x) (i : V) :
    pi_dist i * ∑ B : P.Quot, (closureCommutator L P pi_dist i B) ^ 2
      ≤ defectSq L P pi_dist := by
  rw [defectSq_eq_weighted_commutator_frobenius]
  exact Finset.single_le_sum
    (f := fun x => pi_dist x * ∑ B, (closureCommutator L P pi_dist x B) ^ 2)
    (fun x _ => mul_nonneg (hπ x).le
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))
    (Finset.mem_univ i)

/-- **THE NORM-CONVERSION THEOREM.** Under a stationary lower bound
`0 < p_min ≤ π`, the worst-case commutator norm is controlled by the
stationary defect:

`‖𝒞‖∞ ≤ √(|Quot| · 𝔇_π² / p_min)`.

The constant is exact and NOT claimed tight: it degrades as `1/√p_min`,
i.e. rare microstates can dominate the worst case while contributing
little to the stationary average — the honest gap between the two defect
faces. -/
theorem commutator_linfty_le_sqrt_defect (L : Matrix V V ℝ) (P : Partition V)
    {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x)
    {pmin : ℝ} (hp : 0 < pmin) (hmin : ∀ i, pmin ≤ pi_dist i) :
    ‖closureCommutator L P pi_dist‖
      ≤ Real.sqrt ((Fintype.card P.Quot) * defectSq L P pi_dist / pmin) := by
  refine linfty_opNorm_le_of_rows _ (Real.sqrt_nonneg _) fun i => ?_
  refine Real.le_sqrt_of_sq_le ?_
  have hcs : (∑ B : P.Quot, |closureCommutator L P pi_dist i B|) ^ 2
      ≤ (Fintype.card P.Quot)
        * ∑ B : P.Quot, (closureCommutator L P pi_dist i B) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset P.Quot))
      (f := fun B => |closureCommutator L P pi_dist i B|)
    simpa [sq_abs, Finset.card_univ] using this
  have hrow : (∑ B : P.Quot, (closureCommutator L P pi_dist i B) ^ 2)
      ≤ defectSq L P pi_dist / pi_dist i := by
    rw [le_div_iff₀ (hπ i)]
    calc (∑ B, (closureCommutator L P pi_dist i B) ^ 2) * pi_dist i
        = pi_dist i * ∑ B, (closureCommutator L P pi_dist i B) ^ 2 := by ring
      _ ≤ defectSq L P pi_dist := row_commutator_sq_le_defectSq L P hπ i
  have hmono : defectSq L P pi_dist / pi_dist i
      ≤ defectSq L P pi_dist / pmin :=
    div_le_div_of_nonneg_left
      (defectSq_nonneg L P fun x => (hπ x).le) hp (hmin i)
  calc (∑ B : P.Quot, |closureCommutator L P pi_dist i B|) ^ 2
      ≤ (Fintype.card P.Quot)
        * ∑ B : P.Quot, (closureCommutator L P pi_dist i B) ^ 2 := hcs
    _ ≤ (Fintype.card P.Quot) * (defectSq L P pi_dist / pmin) := by
        refine mul_le_mul_of_nonneg_left (le_trans hrow hmono) ?_
        positivity
    _ = (Fintype.card P.Quot) * defectSq L P pi_dist / pmin := by ring

/-! ## §4. The end-to-end chain -/

/-- **THE END-TO-END PHYSICAL HORIZON.** The complete causal chain in one
theorem: hidden within-block variation (`𝔇_π`) controls the worst-case
re-entry rate (`‖𝒞‖∞`), which prices the closure error in physical time
(`t = n·Δt`):

`‖error(t)‖ ≤ t · √(|Quot| · 𝔇_π² / p_min)`.

Zero defect gives eternal exactness (the Trinity pole); positive defect
buys a finite, explicitly priced validity horizon. -/
theorem end_to_end_physical_horizon (dt : ℝ) (L : Matrix V V ℝ)
    (P : Partition V) {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x)
    {pmin : ℝ} (hp : 0 < pmin) (hmin : ∀ i, pmin ≤ pi_dist i)
    (hL : IsGenerator L) (hdt : 0 ≤ dt)
    (hstep : ∀ i, dt * (-(L i i)) ≤ 1) (n : ℕ) :
    ‖(eulerStep dt L) ^ n * lift_matrix P
      - lift_matrix P * (eulerStep dt (CoarseGenerator L P pi_dist)) ^ n‖
      ≤ ((n : ℝ) * dt)
        * Real.sqrt ((Fintype.card P.Quot) * defectSq L P pi_dist / pmin) :=
  le_trans (physical_time_closure_error dt L P hπ hL hdt hstep n)
    (mul_le_mul_of_nonneg_left
      (commutator_linfty_le_sqrt_defect L P hπ hp hmin)
      (by positivity))

end SGC.Renormalization.PhysicalHorizon
