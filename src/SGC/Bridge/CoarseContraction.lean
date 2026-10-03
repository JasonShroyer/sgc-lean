/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Bridge.ContractiveHorizon

/-!
# The coarse semigroup is contractive on coarse data: discharging `hcoarse`

`ContractiveHorizon.trajectory_closure_bound_generator` carried one explicit hypothesis,
`hcoarse`: the coarse semigroup `e^{sL̄}`, `L̄ = ΠLΠ`, does not increase the `π`-norm of a
block-constant initial datum. This module proves it for every stationary rate generator.

The trick avoids quotient types and spectral theory. Put

  `L̃ := ΠLΠ + c·(Π − 1)`.

* `L̃·Π = L̄` (because `Π² = Π`), so by the invariant-subspace series argument
  (`exp_mul_proj_of_mul_proj_eq`, the same induction as
  `DefectHorizonBridge.exp_defectComplement_mul_proj`) `e^{sL̃}·Π = e^{sL̄}·Π`: the two
  semigroups agree on block-constant data.
* `L̃·1 = 0` and `π·L̃ = 0`, because `Π·1 = 1` and `π·Π = π`.
* Off the diagonal, `ΠLΠ` is nonnegative **between** blocks (only off-diagonal entries of
  `L` contribute), while **inside** a block `Π_{xy} = π_y/π̄ > 0`, so for `c` large enough
  `L̃` has nonnegative off-diagonal entries. We take `c` to be the sum over all in-block
  pairs of `max 0 (−(ΠLΠ)_{xy}/Π_{xy})`.

Hence `L̃` is a stationary rate generator, `heatKernel_contractive_of_generator` gives
`‖e^{sL̃}‖_π ≤ 1`, and `‖e^{sL̄}f₀‖_π = ‖e^{sL̃}f₀‖_π ≤ ‖f₀‖_π`. The unconditional bound

  `‖e^{tL}f₀ − e^{tL̄}f₀‖_π ≤ t · ε · ‖f₀‖_π`

(`trajectory_closure_bound_stationary`) follows for every stationary rate generator and
block-constant `f₀`. Standard axioms only.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SGC.Bridge.CoarseContraction

open Finset Matrix NormedSpace
open scoped Nat
open SGC.Approximate SGC.Bridge.DefectHorizonBridge SGC.Bridge.ContractiveHorizon
open SGC.InformationGeometry.ContinuousTimeKernel (IsGenerator)

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (P : Partition V)

local notation "Pr" => CoarseProjectorMatrix P pi_dist hπ

/-! ## §1. Elementary facts about the projector matrix -/

lemma proj_entry_nonneg (x y : V) : 0 ≤ Pr x y := by
  unfold CoarseProjectorMatrix
  split_ifs
  · exact div_nonneg (hπ y).le (pi_bar_pos P hπ _).le
  · exact le_rfl

lemma proj_entry_pos_of_same {x y : V} (h : P.quot_map x = P.quot_map y) : 0 < Pr x y := by
  unfold CoarseProjectorMatrix
  rw [if_pos h]
  exact div_pos (hπ y) (pi_bar_pos P hπ _)

lemma proj_entry_zero_of_ne {x y : V} (h : P.quot_map x ≠ P.quot_map y) : Pr x y = 0 := by
  unfold CoarseProjectorMatrix
  rw [if_neg h]

/-- `Π·1 = 1`: rows of the projector sum to one. -/
lemma proj_mulVec_one : Pr *ᵥ (fun _ => (1 : ℝ)) = fun _ => 1 := by
  funext x
  simp only [Matrix.mulVec, dotProduct, mul_one, CoarseProjectorMatrix]
  have hpos := pi_bar_pos P hπ (P.quot_map x)
  have : ∀ y, (if P.quot_map x = P.quot_map y then pi_dist y / pi_bar P pi_dist (P.quot_map x)
      else 0) = (if P.quot_map y = P.quot_map x then pi_dist y else 0) /
        pi_bar P pi_dist (P.quot_map x) := by
    intro y
    by_cases h : P.quot_map x = P.quot_map y
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h), zero_div]
  simp_rw [this, ← Finset.sum_div]
  rw [← pi_bar_eq_sum_class, div_self hpos.ne']

/-- `π·Π = π`: the stationary weight is invariant under the projector. -/
lemma pi_vecMul_proj : pi_dist ᵥ* Pr = pi_dist := by
  funext y
  simp only [Matrix.vecMul, dotProduct, CoarseProjectorMatrix]
  have hpos := pi_bar_pos P hπ (P.quot_map y)
  have : ∀ x, pi_dist x * (if P.quot_map x = P.quot_map y then
      pi_dist y / pi_bar P pi_dist (P.quot_map x) else 0) =
      (if P.quot_map x = P.quot_map y then pi_dist x else 0) *
        (pi_dist y / pi_bar P pi_dist (P.quot_map y)) := by
    intro x
    by_cases h : P.quot_map x = P.quot_map y
    · rw [if_pos h, if_pos h, h]
    · rw [if_neg h, if_neg h, mul_zero, zero_mul]
  simp_rw [this, ← Finset.sum_mul]
  rw [← pi_bar_eq_sum_class]
  field_simp

/-- Between blocks the coarse generator is nonnegative: only off-diagonal entries of `L`
contribute to `(ΠLΠ)_{xy}` when `x` and `y` lie in different blocks. -/
lemma coarseGen_offblock_nonneg (L : Matrix V V ℝ) (hL : ∀ x y, x ≠ y → 0 ≤ L x y)
    {x y : V} (hxy : P.quot_map x ≠ P.quot_map y) :
    0 ≤ CoarseGeneratorMatrix L P pi_dist hπ x y := by
  unfold CoarseGeneratorMatrix
  simp only [Matrix.mul_apply]
  apply Finset.sum_nonneg
  intro y' _
  by_cases h2 : P.quot_map y' = P.quot_map y
  · apply mul_nonneg _ (proj_entry_nonneg pi_dist hπ P y' y)
    apply Finset.sum_nonneg
    intro x' _
    by_cases h1 : P.quot_map x = P.quot_map x'
    · have hne : x' ≠ y' := by
        intro heq
        apply hxy
        rw [h1, heq, h2]
      exact mul_nonneg (proj_entry_nonneg pi_dist hπ P x x') (hL x' y' hne)
    · rw [proj_entry_zero_of_ne pi_dist hπ P h1, zero_mul]
  · rw [proj_entry_zero_of_ne pi_dist hπ P h2, mul_zero]

/-! ## §2. The modified generator `L̃ = ΠLΠ + c(Π − 1)` -/

variable (L : Matrix V V ℝ)

/-- In-block correction needed at the pair `(x, y)`. -/
def badness (x y : V) : ℝ :=
  if P.quot_map x = P.quot_map y ∧ x ≠ y
  then max 0 (-(CoarseGeneratorMatrix L P pi_dist hπ x y) / Pr x y) else 0

lemma badness_nonneg (x y : V) : 0 ≤ badness pi_dist hπ P L x y := by
  unfold badness; split_ifs
  · exact le_max_left _ _
  · exact le_rfl

/-- The uniform in-block correction: the sum of all pairwise corrections. -/
def shiftConst : ℝ := ∑ x, ∑ y, badness pi_dist hπ P L x y

lemma badness_le_shiftConst (x y : V) : badness pi_dist hπ P L x y ≤ shiftConst pi_dist hπ P L := by
  unfold shiftConst
  calc badness pi_dist hπ P L x y
      ≤ ∑ y', badness pi_dist hπ P L x y' :=
        Finset.single_le_sum (fun y' _ => badness_nonneg pi_dist hπ P L x y') (Finset.mem_univ y)
    _ ≤ ∑ x', ∑ y', badness pi_dist hπ P L x' y' :=
        Finset.single_le_sum (fun x' _ => Finset.sum_nonneg fun y' _ => badness_nonneg pi_dist hπ P L x' y')
          (Finset.mem_univ x)

/-- `L̃ := ΠLΠ + c·(Π − 1)` with `c = shiftConst`. -/
def modifiedGenerator : Matrix V V ℝ :=
  CoarseGeneratorMatrix L P pi_dist hπ + shiftConst pi_dist hπ P L • (Pr - 1)

/-- `L̃·Π = L̄`. -/
lemma modifiedGenerator_mul_proj :
    modifiedGenerator pi_dist hπ P L * Pr = CoarseGeneratorMatrix L P pi_dist hπ := by
  unfold modifiedGenerator
  have hidem : Pr * Pr = Pr := CoarseProjectorMatrix_idempotent P pi_dist hπ
  rw [add_mul, smul_mul_assoc, sub_mul, hidem, Matrix.one_mul, sub_self, smul_zero, add_zero]
  exact coarseGeneratorMatrix_mul_proj pi_dist hπ L P

/-- `L̃` has nonnegative off-diagonal entries. -/
lemma modifiedGenerator_offdiag_nonneg (hL : ∀ x y, x ≠ y → 0 ≤ L x y) (x y : V) (hxy : x ≠ y) :
    0 ≤ modifiedGenerator pi_dist hπ P L x y := by
  unfold modifiedGenerator
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply_ne hxy,
    sub_zero, smul_eq_mul]
  by_cases hb : P.quot_map x = P.quot_map y
  · have hp : 0 < Pr x y := proj_entry_pos_of_same pi_dist hπ P hb
    have hbad : badness pi_dist hπ P L x y =
        max 0 (-(CoarseGeneratorMatrix L P pi_dist hπ x y) / Pr x y) := by
      unfold badness; rw [if_pos ⟨hb, hxy⟩]
    have hc := badness_le_shiftConst pi_dist hπ P L x y
    rw [hbad] at hc
    have h1 : -(CoarseGeneratorMatrix L P pi_dist hπ x y) / Pr x y ≤ shiftConst pi_dist hπ P L :=
      le_trans (le_max_right _ _) hc
    rw [div_le_iff₀ hp] at h1
    linarith
  · rw [proj_entry_zero_of_ne pi_dist hπ P hb, mul_zero, add_zero]
    exact coarseGen_offblock_nonneg pi_dist hπ P L hL hb

/-- `L̃·1 = 0`: zero row sums. -/
lemma modifiedGenerator_row_zero (hrow : ∀ x, ∑ y, L x y = 0) (x : V) :
    ∑ y, modifiedGenerator pi_dist hπ P L x y = 0 := by
  have hL1 : L *ᵥ (fun _ => (1 : ℝ)) = 0 := by
    funext z; simp [Matrix.mulVec, dotProduct, hrow z]
  have hP1 := proj_mulVec_one pi_dist hπ P
  have key : modifiedGenerator pi_dist hπ P L *ᵥ (fun _ => (1 : ℝ)) = 0 := by
    unfold modifiedGenerator CoarseGeneratorMatrix
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hP1,
      sub_self, smul_zero, add_zero, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hP1, hL1,
      Matrix.mulVec_zero]
  have := congr_fun key x
  simpa [Matrix.mulVec, dotProduct] using this

/-- `π·L̃ = 0`: `π` is stationary for the modified generator. -/
lemma pi_vecMul_modifiedGenerator (hstat : pi_dist ᵥ* L = 0) :
    pi_dist ᵥ* modifiedGenerator pi_dist hπ P L = 0 := by
  have hP := pi_vecMul_proj pi_dist hπ P
  unfold modifiedGenerator CoarseGeneratorMatrix
  rw [Matrix.vecMul_add, Matrix.vecMul_smul, Matrix.vecMul_sub, Matrix.vecMul_one, hP, sub_self,
    smul_zero, add_zero, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hP, hstat,
    Matrix.zero_vecMul]

/-- `L̃` is a stationary rate generator. -/
theorem modifiedGenerator_isGenerator (hL : IsGenerator L) :
    IsGenerator (modifiedGenerator pi_dist hπ P L) where
  offdiag_nonneg x y hxy := modifiedGenerator_offdiag_nonneg pi_dist hπ P L hL.offdiag_nonneg x y hxy
  row_zero x := modifiedGenerator_row_zero pi_dist hπ P L hL.row_zero x

/-! ## §3. Invariant-subspace exponentiation, general form -/

/-- If `A·Π = L̄` then `Aⁿ·Π = L̄ⁿ·Π` (the induction of
`DefectHorizonBridge.defectComplement_pow_mul_proj`, with the hypothesis abstracted). -/
lemma pow_mul_proj_of_mul_proj_eq (A : Matrix V V ℝ)
    (hA : A * Pr = CoarseGeneratorMatrix L P pi_dist hπ) (n : ℕ) :
    A ^ n * Pr = CoarseGeneratorMatrix L P pi_dist hπ ^ n * Pr := by
  set Lb := CoarseGeneratorMatrix L P pi_dist hπ with hLb
  have hLbPr : Lb * Pr = Lb := coarseGeneratorMatrix_mul_proj pi_dist hπ L P
  induction n with
  | zero => simp
  | succ m ih =>
    calc A ^ (m + 1) * Pr
        = A ^ m * (A * Pr) := by rw [pow_succ, Matrix.mul_assoc]
      _ = A ^ m * (Lb * Pr) := by rw [hA, hLbPr]
      _ = A ^ m * Pr * (L * Pr) := by
          rw [hLbPr, hLb]
          show A ^ m * (Pr * L * Pr) = A ^ m * Pr * (L * Pr)
          rw [Matrix.mul_assoc (A ^ m) Pr (L * Pr), Matrix.mul_assoc Pr L Pr]
      _ = Lb ^ m * Pr * (L * Pr) := by rw [ih]
      _ = Lb ^ m * (Pr * L * Pr) := by
          rw [Matrix.mul_assoc (Lb ^ m) Pr (L * Pr), Matrix.mul_assoc Pr L Pr]
      _ = Lb ^ m * Lb := by rw [hLb]; rfl
      _ = Lb ^ (m + 1) := by rw [pow_succ]
      _ = Lb ^ (m + 1) * Pr := by rw [pow_succ, Matrix.mul_assoc, hLbPr]

variable [Nonempty V]

omit [Nonempty V] in
/-- If `A·Π = L̄` then `e^{tA}·Π = e^{tL̄}·Π`. -/
theorem exp_mul_proj_of_mul_proj_eq (A : Matrix V V ℝ)
    (hA : A * Pr = CoarseGeneratorMatrix L P pi_dist hπ) (t : ℝ) :
    exp ℝ (t • A) * Pr = exp ℝ (t • CoarseGeneratorMatrix L P pi_dist hπ) * Pr := by
  have key : ∀ X : Matrix V V ℝ,
      HasSum (fun n : ℕ => (n !⁻¹ : ℝ) • (X ^ n * Pr))
        (toMat pi_dist hπ (exp ℝ (ofMat pi_dist hπ X)) * Pr) := by
    intro X
    have h1 : HasSum (fun n : ℕ => (n !⁻¹ : ℝ) • (ofMat pi_dist hπ X) ^ n)
        (exp ℝ (ofMat pi_dist hπ X)) := by
      rw [exp_eq_tsum]
      exact (expSeries_summable' (𝕂 := ℝ) (ofMat pi_dist hπ X)).hasSum
    have h2 := h1.map (mulProjLin (V := V) pi_dist hπ P) (mulProjLin_continuous pi_dist hπ P)
    have hterm : (⇑(mulProjLin (V := V) pi_dist hπ P) ∘ fun n : ℕ =>
        (n !⁻¹ : ℝ) • (ofMat pi_dist hπ X) ^ n) =
        fun n : ℕ => (n !⁻¹ : ℝ) • (X ^ n * Pr) := by
      funext n
      show (((n !⁻¹ : ℝ) • (X ^ n) : Matrix V V ℝ)) * _ = _
      rw [smul_mul_assoc]
    rwa [hterm] at h2
  have hA' := key (t • A)
  have hL' := key (t • CoarseGeneratorMatrix L P pi_dist hπ)
  have hsame : (fun n : ℕ => (n !⁻¹ : ℝ) • ((t • A) ^ n * Pr)) =
      fun n : ℕ => (n !⁻¹ : ℝ) • ((t • CoarseGeneratorMatrix L P pi_dist hπ) ^ n * Pr) := by
    funext n
    rw [smul_pow, smul_pow, smul_mul_assoc, smul_mul_assoc,
      pow_mul_proj_of_mul_proj_eq pi_dist hπ P L A hA n]
  rw [hsame] at hA'
  have := hA'.unique hL'
  rwa [exp_piMat_eq, exp_piMat_eq] at this

/-! ## §4. The coarse semigroup is contractive on coarse data -/

/-- **`hcoarse` discharged.** For a stationary rate generator and block-constant `f₀`,
`‖e^{sL̄}f₀‖_π ≤ ‖f₀‖_π` for all `s ≥ 0`. -/
theorem coarse_heatKernel_contractive (hL : IsGenerator L) (hstat : pi_dist ᵥ* L = 0)
    (s : ℝ) (hs : 0 ≤ s) (f₀ : V → ℝ) (hf₀ : f₀ = CoarseProjector P pi_dist hπ f₀) :
    norm_pi pi_dist (HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) s f₀) ≤
      norm_pi pi_dist f₀ := by
  set Lt := modifiedGenerator pi_dist hπ P L with hLt
  have hPr : Pr *ᵥ f₀ = f₀ := by
    rw [CoarseProjectorMatrix_mulVec]; exact hf₀.symm
  have heq : HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) s f₀ = HeatKernel Lt s *ᵥ f₀ := by
    show exp ℝ (s • CoarseGeneratorMatrix L P pi_dist hπ) *ᵥ f₀ = exp ℝ (s • Lt) *ᵥ f₀
    conv_lhs => rw [← hPr, Matrix.mulVec_mulVec,
      ← exp_mul_proj_of_mul_proj_eq pi_dist hπ P L Lt (modifiedGenerator_mul_proj pi_dist hπ P L) s,
      ← Matrix.mulVec_mulVec, hPr]
  rw [heq]
  have hgen := modifiedGenerator_isGenerator pi_dist hπ P L hL
  have hstat' := pi_vecMul_modifiedGenerator pi_dist hπ P L hstat
  have hc := heatKernel_contractive_of_generator pi_dist hπ Lt hgen hstat' s hs
  have := opNorm_pi_bound pi_dist hπ (matrixToLinearMap (HeatKernel Lt s)) f₀
  refine le_trans this ?_
  exact mul_le_of_le_one_left (norm_pi_nonneg' pi_dist f₀) hc

/-- **Unconditional contractive trajectory bound** for stationary rate generators:

  `‖e^{tL}f₀ − e^{tL̄}f₀‖_π ≤ t · ‖(I−Π)LΠ‖_π · ‖f₀‖_π`

for every block-constant `f₀` and `t ≥ 0`. No exponential factor, no side hypothesis. -/
theorem trajectory_closure_bound_stationary (hL : IsGenerator L) (hstat : pi_dist ᵥ* L = 0)
    (t : ℝ) (ht : 0 ≤ t) (f₀ : V → ℝ) (hf₀ : f₀ = CoarseProjector P pi_dist hπ f₀) :
    norm_pi pi_dist (HeatKernelMap L t f₀ -
      HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f₀) ≤
    t * opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) * norm_pi pi_dist f₀ :=
  trajectory_closure_bound_generator pi_dist hπ L P hL hstat t ht f₀ hf₀
    (fun s hs => coarse_heatKernel_contractive pi_dist hπ P L hL hstat s hs f₀ hf₀)

end SGC.Bridge.CoarseContraction
