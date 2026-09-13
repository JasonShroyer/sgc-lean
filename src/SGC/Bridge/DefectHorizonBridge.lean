/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Renormalization.Approximate
import SGC.Bridge.ValidityHorizon

/-!
# The Defect-Horizon Bridge: identifying the two ε's, retiring two axioms

`Bridge/ValidityHorizon.lean` proved the semigroup perturbation bound in an
abstract real Banach algebra, with ε = ‖B‖ the norm of a SUMMAND in `L = A + B`.
`Renormalization/Approximate.lean` measures leakage concretely as
`opNorm_pi (DefectOperator L P π)` — the π-weighted L²(π) operator norm of the
lower-left BLOCK `D = (I−Π)LΠ` — and pays for its trajectory bounds with
declared axioms (`HeatKernel_opNorm_bound`, `Horizontal_Duhamel_integral_bound`).

This module closes the seam with three pieces of new mathematics:

* **(i) The weighted operator algebra** `PiMat V pi_dist hπ`: a type synonym of
  `Matrix V V ℝ` carrying `‖M‖ := opNorm_pi pi_dist hπ (matrixToLinearMap M)` as
  a genuine `NormedRing`/`NormOneClass`/`NormedAlgebra ℝ`/`CompleteSpace`
  structure. The weight π lives in the TYPE, so Mathlib's static typeclasses
  coexist with dynamically chosen stationary distributions. On this algebra
  `defect_eq_validity_leakage` holds as a literal EQUALITY: the abstract ε IS
  Approximate's ε.

* **(ii) The correct decomposition** `L = (L − D) + D` (NOT `L̄ + D`): the
  modified generator `L − D` leaves the coarse subspace invariant, acting there
  as the coarse generator (`defectComplement_mul_proj`).

* **(iii) Invariant-subspace exponentiation**: `exp(t(L−D))·Π = exp(tL̄)·Π`
  (`exp_defectComplement_mul_proj`), by induction through the exponential
  series — the hard lemma.

**The prize** (`defect_horizon_bound`): for block-constant `f₀`,

  `‖e^{tL}f₀ − e^{tL̄}f₀‖_π ≤ t · ‖D‖_π · e^{t(‖L−D‖_π + ‖D‖_π)} · ‖f₀‖_π`,

kernel-proved with explicit constants. Together with
`heatKernel_opNorm_explicit` (`‖e^{sL}‖_π ≤ e^{s‖L‖_π}`), this supersedes the
two axioms that `trajectory_closure_bound` consumes: the existential constants
`B`, `B²` of `HeatKernel_opNorm_bound` and `Horizontal_Duhamel_integral_bound`
are replaced by computable exponentials. The ε-form
(`trajectory_closure_bound_explicit`) restates the supersession in
`IsApproxLumpable` vocabulary.

* **(iv) The vertical companion** (§6): the leakage OUT of the coarse subspace,
  `(I−Π)e^{tL}f₀`, obeys the SAME explicit bound. The key observation is that the
  vertical defect IS the horizontal gap projected — `(I−Π)e^{tL}f₀ =
  (I−Π)(e^{tL}f₀ − e^{tL̄}f₀)`, since `e^{tL̄}f₀` stays coarse
  (`coarseProj_fixes_coarse_heatKernel`) — and `(I−Π)` is π-contractive
  (`CoarseProjector_compl_contractive`, an UNCONDITIONAL Pythagoras: `Π` is the
  π-self-adjoint conditional expectation for any generator). So
  `vertical_defect_horizon_bound` / `vertical_closure_bound_explicit` supersede the
  third axiom, `Duhamel_integral_bound`, with no MVT and no side conditions.

The other seven axioms of `Approximate.lean` (`rowsum_to_opNorm_bound`, `NCD_*`,
`PropagatorDiff_*`, `Weyl_inequality_pi`) are untouched — separate campaigns.
-/

noncomputable section

namespace SGC.Bridge.DefectHorizonBridge

open Finset Matrix NormedSpace
open scoped Nat
open SGC.Approximate

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## §1. The defect as a matrix -/

/-- The leakage defect as a matrix: `D = L·Π − Π·L·Π` (= `(I−Π)·L·Π`). -/
def DefectMatrix (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) : Matrix V V ℝ :=
  L * CoarseProjectorMatrix P pi_dist hπ -
    CoarseProjectorMatrix P pi_dist hπ * L * CoarseProjectorMatrix P pi_dist hπ

/-- The defect matrix acts exactly as the `DefectOperator` linear map. -/
lemma defectMatrix_mulVec (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (f : V → ℝ) :
    DefectMatrix L P pi_dist hπ *ᵥ f = DefectOperator L P pi_dist hπ f := by
  rw [DefectOperator_apply, DefectMatrix, Matrix.sub_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simp only [CoarseProjectorMatrix_mulVec]

/-- As linear maps: `matrixToLinearMap (DefectMatrix …) = DefectOperator …`. -/
lemma defectMatrix_toLin (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) :
    matrixToLinearMap (DefectMatrix L P pi_dist hπ) = DefectOperator L P pi_dist hπ :=
  LinearMap.ext fun f => defectMatrix_mulVec L P pi_dist hπ f

/-! ## §2. Piece (i): the weighted operator algebra `PiMat` -/

/-- Type synonym: `Matrix V V ℝ` regarded as the L²(π) operator algebra.
    The weight is part of the TYPE, so the norm instances below can depend
    on it without colliding with Mathlib's unweighted matrix norms. -/
def PiMat (V : Type*) [Fintype V] [DecidableEq V] (pi_dist : V → ℝ)
    (_hπ : ∀ v, 0 < pi_dist v) : Type _ := Matrix V V ℝ

variable (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)

/-- Tag a matrix as an element of the weighted algebra. -/
def ofMat (M : Matrix V V ℝ) : PiMat V pi_dist hπ := M

/-- Forget the weighted-algebra tag. -/
def toMat (M : PiMat V pi_dist hπ) : Matrix V V ℝ := M

instance : Ring (PiMat V pi_dist hπ) := inferInstanceAs (Ring (Matrix V V ℝ))

instance : Algebra ℝ (PiMat V pi_dist hπ) := inferInstanceAs (Algebra ℝ (Matrix V V ℝ))

instance : FiniteDimensional ℝ (PiMat V pi_dist hπ) :=
  inferInstanceAs (FiniteDimensional ℝ (Matrix V V ℝ))

/-- The candidate norm: the L²(π) operator norm of the action by `mulVec`. -/
def pmNorm (M : PiMat V pi_dist hπ) : ℝ :=
  opNorm_pi pi_dist hπ (matrixToLinearMap (toMat pi_dist hπ M))

lemma pmNorm_nonneg (M : PiMat V pi_dist hπ) : 0 ≤ pmNorm pi_dist hπ M :=
  opNorm_pi_nonneg pi_dist hπ _

lemma norm_pi_nonneg' (f : V → ℝ) : 0 ≤ norm_pi pi_dist f := Real.sqrt_nonneg _

/-- The action bound, in matrix vocabulary. -/
lemma pmNorm_mulVec_le (M : PiMat V pi_dist hπ) (f : V → ℝ) :
    norm_pi pi_dist (toMat pi_dist hπ M *ᵥ f) ≤ pmNorm pi_dist hπ M * norm_pi pi_dist f :=
  opNorm_pi_bound pi_dist hπ (matrixToLinearMap (toMat pi_dist hπ M)) f

lemma pmNorm_zero : pmNorm pi_dist hπ (0 : PiMat V pi_dist hπ) = 0 := by
  refine le_antisymm (opNorm_pi_le_of_bound pi_dist hπ _ 0 le_rfl fun f => ?_)
    (pmNorm_nonneg pi_dist hπ 0)
  show norm_pi pi_dist ((0 : Matrix V V ℝ) *ᵥ f) ≤ 0 * norm_pi pi_dist f
  rw [Matrix.zero_mulVec, zero_mul]
  exact le_of_eq ((norm_pi_eq_zero_iff pi_dist hπ 0).mpr rfl)

lemma pmNorm_add_le (M N : PiMat V pi_dist hπ) :
    pmNorm pi_dist hπ (M + N) ≤ pmNorm pi_dist hπ M + pmNorm pi_dist hπ N := by
  refine opNorm_pi_le_of_bound pi_dist hπ _ _
    (add_nonneg (pmNorm_nonneg pi_dist hπ M) (pmNorm_nonneg pi_dist hπ N)) fun f => ?_
  show norm_pi pi_dist ((toMat pi_dist hπ M + toMat pi_dist hπ N) *ᵥ f) ≤ _
  rw [Matrix.add_mulVec]
  calc norm_pi pi_dist (toMat pi_dist hπ M *ᵥ f + toMat pi_dist hπ N *ᵥ f)
      ≤ norm_pi pi_dist (toMat pi_dist hπ M *ᵥ f) + norm_pi pi_dist (toMat pi_dist hπ N *ᵥ f) :=
        norm_pi_add_le pi_dist hπ _ _
    _ ≤ pmNorm pi_dist hπ M * norm_pi pi_dist f + pmNorm pi_dist hπ N * norm_pi pi_dist f :=
        add_le_add (pmNorm_mulVec_le pi_dist hπ M f) (pmNorm_mulVec_le pi_dist hπ N f)
    _ = (pmNorm pi_dist hπ M + pmNorm pi_dist hπ N) * norm_pi pi_dist f := by ring

lemma norm_pi_neg (f : V → ℝ) : norm_pi pi_dist (-f) = norm_pi pi_dist f := by
  have h := norm_pi_smul_abs pi_dist (-1 : ℝ) f
  rw [neg_one_smul] at h
  simpa using h

lemma pmNorm_neg (M : PiMat V pi_dist hπ) :
    pmNorm pi_dist hπ (-M) = pmNorm pi_dist hπ M := by
  have key : ∀ N : PiMat V pi_dist hπ, pmNorm pi_dist hπ (-N) ≤ pmNorm pi_dist hπ N := by
    intro N
    refine opNorm_pi_le_of_bound pi_dist hπ _ _ (pmNorm_nonneg pi_dist hπ N) fun f => ?_
    show norm_pi pi_dist ((-toMat pi_dist hπ N) *ᵥ f) ≤ _
    rw [Matrix.neg_mulVec, norm_pi_neg]
    exact pmNorm_mulVec_le pi_dist hπ N f
  refine le_antisymm (key M) ?_
  have h := key (-M)
  rwa [neg_neg] at h

lemma pmNorm_eq_zero {M : PiMat V pi_dist hπ} (h : pmNorm pi_dist hπ M = 0) : M = 0 := by
  have hvec : ∀ f, toMat pi_dist hπ M *ᵥ f = 0 := by
    intro f
    have h1 := pmNorm_mulVec_le pi_dist hπ M f
    rw [h, zero_mul] at h1
    exact (norm_pi_eq_zero_iff pi_dist hπ _).mp (le_antisymm h1 (norm_pi_nonneg' pi_dist _))
  show toMat pi_dist hπ M = 0
  ext i j
  have := congrFun (hvec (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite] using this

lemma pmNorm_mul_le (M N : PiMat V pi_dist hπ) :
    pmNorm pi_dist hπ (M * N) ≤ pmNorm pi_dist hπ M * pmNorm pi_dist hπ N := by
  have hcomp : matrixToLinearMap (toMat pi_dist hπ M * toMat pi_dist hπ N) =
      matrixToLinearMap (toMat pi_dist hπ M) ∘ₗ matrixToLinearMap (toMat pi_dist hπ N) := by
    apply LinearMap.ext; intro f
    show (toMat pi_dist hπ M * toMat pi_dist hπ N) *ᵥ f =
      toMat pi_dist hπ M *ᵥ (toMat pi_dist hπ N *ᵥ f)
    rw [Matrix.mulVec_mulVec]
  show opNorm_pi pi_dist hπ (matrixToLinearMap (toMat pi_dist hπ M * toMat pi_dist hπ N)) ≤ _
  rw [hcomp]
  exact opNorm_pi_comp pi_dist hπ _ _

lemma pmNorm_smul_le (c : ℝ) (M : PiMat V pi_dist hπ) :
    pmNorm pi_dist hπ (c • M) ≤ |c| * pmNorm pi_dist hπ M := by
  refine opNorm_pi_le_of_bound pi_dist hπ _ _
    (mul_nonneg (abs_nonneg c) (pmNorm_nonneg pi_dist hπ M)) fun f => ?_
  show norm_pi pi_dist ((c • toMat pi_dist hπ M) *ᵥ f) ≤ _
  rw [Matrix.smul_mulVec, norm_pi_smul_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left (pmNorm_mulVec_le pi_dist hπ M f) (abs_nonneg c)

/-- The weighted normed group structure on `PiMat`. -/
instance : NormedAddCommGroup (PiMat V pi_dist hπ) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := pmNorm pi_dist hπ
      map_zero' := pmNorm_zero pi_dist hπ
      add_le' := pmNorm_add_le pi_dist hπ
      neg' := pmNorm_neg pi_dist hπ
      eq_zero_of_map_eq_zero' := fun _ h => pmNorm_eq_zero pi_dist hπ h }

lemma pmNorm_def (M : PiMat V pi_dist hπ) :
    ‖M‖ = opNorm_pi pi_dist hπ (matrixToLinearMap (toMat pi_dist hπ M)) := rfl

/-- The weighted normed ring: `opNorm_pi` is submultiplicative. -/
instance : NormedRing (PiMat V pi_dist hπ) :=
  { (inferInstance : NormedAddCommGroup (PiMat V pi_dist hπ)),
    (inferInstance : Ring (PiMat V pi_dist hπ)) with
    norm_mul_le := pmNorm_mul_le pi_dist hπ }

/-- `‖1‖_π = 1` (the identity acts isometrically). Needs an inhabited state space. -/
instance [Nonempty V] : NormOneClass (PiMat V pi_dist hπ) where
  norm_one := by
    have hub : pmNorm pi_dist hπ (1 : PiMat V pi_dist hπ) ≤ 1 := by
      refine opNorm_pi_le_of_bound pi_dist hπ _ 1 zero_le_one fun f => ?_
      show norm_pi pi_dist ((1 : Matrix V V ℝ) *ᵥ f) ≤ 1 * norm_pi pi_dist f
      rw [Matrix.one_mulVec, one_mul]
    have hone : (constant_vec_one : V → ℝ) ≠ 0 := by
      intro h
      have h1 := congrFun h (Classical.arbitrary V)
      simp [constant_vec_one] at h1
    have hpos := norm_pi_pos_of_ne_zero pi_dist hπ _ hone
    have hb := pmNorm_mulVec_le pi_dist hπ (1 : PiMat V pi_dist hπ) constant_vec_one
    rw [show toMat pi_dist hπ (1 : PiMat V pi_dist hπ) = (1 : Matrix V V ℝ) from rfl,
        Matrix.one_mulVec] at hb
    have hlb : 1 ≤ pmNorm pi_dist hπ (1 : PiMat V pi_dist hπ) := by nlinarith [hb, hpos]
    exact le_antisymm hub hlb

instance : NormedAlgebra ℝ (PiMat V pi_dist hπ) :=
  { (inferInstance : Algebra ℝ (PiMat V pi_dist hπ)) with
    norm_smul_le := fun c M => by
      have h := pmNorm_smul_le pi_dist hπ c M
      rw [Real.norm_eq_abs]
      exact h }

instance : CompleteSpace (PiMat V pi_dist hπ) := FiniteDimensional.complete ℝ _

/-! ## §3. Exponential transport: `PiMat` exp = matrix exp -/

/-- The forgetful map as a linear map (the identity, retyped). -/
def toMatLin : PiMat V pi_dist hπ →ₗ[ℝ] Matrix V V ℝ where
  toFun := toMat pi_dist hπ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma toMatLin_continuous : Continuous (toMatLin (V := V) pi_dist hπ) :=
  LinearMap.continuous_of_finiteDimensional _

/-- **Exponential transport**: the Banach-algebra exponential in the weighted
    algebra is the ordinary matrix exponential. -/
lemma exp_piMat_eq (M : Matrix V V ℝ) :
    toMat pi_dist hπ (exp ℝ (ofMat pi_dist hπ M)) = exp ℝ M := by
  have h1 : HasSum (fun n : ℕ => (n !⁻¹ : ℝ) • (ofMat pi_dist hπ M) ^ n)
      (exp ℝ (ofMat pi_dist hπ M)) := by
    rw [exp_eq_tsum]
    exact (expSeries_summable' (𝕂 := ℝ) (ofMat pi_dist hπ M)).hasSum
  have h2 := h1.map (toMatLin (V := V) pi_dist hπ) (toMatLin_continuous pi_dist hπ)
  have hterm : (⇑(toMatLin (V := V) pi_dist hπ) ∘ fun n : ℕ =>
      (n !⁻¹ : ℝ) • (ofMat pi_dist hπ M) ^ n) = fun n : ℕ => (n !⁻¹ : ℝ) • M ^ n := rfl
  rw [hterm] at h2
  have hexp : exp ℝ M = ∑' n : ℕ, (n !⁻¹ : ℝ) • M ^ n := by
    rw [exp_eq_tsum]
  rw [hexp]
  exact h2.tsum_eq.symm

/-! ## §4. Pieces (ii) and (iii): invariance and invariant-subspace exponentiation -/

variable (L : Matrix V V ℝ) (P : Partition V)

/-- Piece (ii), key algebra: the modified generator `L − D` hits the coarse
    subspace exactly as `Π·L·Π` does. -/
lemma defectComplement_mul_proj :
    (L - DefectMatrix L P pi_dist hπ) * CoarseProjectorMatrix P pi_dist hπ =
    CoarseProjectorMatrix P pi_dist hπ * L * CoarseProjectorMatrix P pi_dist hπ := by
  set Pr := CoarseProjectorMatrix P pi_dist hπ with hPr
  have hidem : Pr * Pr = Pr := CoarseProjectorMatrix_idempotent P pi_dist hπ
  rw [DefectMatrix, sub_mul, sub_mul]
  rw [Matrix.mul_assoc L Pr Pr, hidem]
  rw [Matrix.mul_assoc (Pr * L) Pr Pr, hidem]
  rw [sub_sub_cancel]

/-- The coarse generator absorbs a trailing projector. -/
lemma coarseGeneratorMatrix_mul_proj :
    CoarseGeneratorMatrix L P pi_dist hπ * CoarseProjectorMatrix P pi_dist hπ =
    CoarseGeneratorMatrix L P pi_dist hπ := by
  set Pr := CoarseProjectorMatrix P pi_dist hπ with hPr
  have hidem : Pr * Pr = Pr := CoarseProjectorMatrix_idempotent P pi_dist hπ
  show Pr * L * Pr * Pr = Pr * L * Pr
  rw [Matrix.mul_assoc (Pr * L) Pr Pr, hidem]

/-- The modified generator also lands on the coarse generator. -/
lemma defectComplement_mul_proj_eq_coarse :
    (L - DefectMatrix L P pi_dist hπ) * CoarseProjectorMatrix P pi_dist hπ =
    CoarseGeneratorMatrix L P pi_dist hπ := by
  rw [defectComplement_mul_proj]
  rfl

/-- Piece (iii), power form: all powers of `L − D` and of `L̄` agree after `Π`. -/
lemma defectComplement_pow_mul_proj (n : ℕ) :
    (L - DefectMatrix L P pi_dist hπ) ^ n * CoarseProjectorMatrix P pi_dist hπ =
    CoarseGeneratorMatrix L P pi_dist hπ ^ n * CoarseProjectorMatrix P pi_dist hπ := by
  set A := L - DefectMatrix L P pi_dist hπ with hA
  set Lb := CoarseGeneratorMatrix L P pi_dist hπ with hLb
  set Pr := CoarseProjectorMatrix P pi_dist hπ with hPr
  induction n with
  | zero => simp
  | succ m ih =>
    have hAPr : A * Pr = Lb := defectComplement_mul_proj_eq_coarse pi_dist hπ L P
    have hLbPr : Lb * Pr = Lb := coarseGeneratorMatrix_mul_proj pi_dist hπ L P
    calc A ^ (m + 1) * Pr
        = A ^ m * (A * Pr) := by rw [pow_succ, Matrix.mul_assoc]
      _ = A ^ m * (Lb * Pr) := by rw [hAPr, hLbPr]
      _ = A ^ m * Pr * (L * Pr) := by
          rw [hLbPr, hLb]
          show A ^ m * (Pr * L * Pr) = A ^ m * Pr * (L * Pr)
          rw [Matrix.mul_assoc (A ^ m) Pr (L * Pr), Matrix.mul_assoc Pr L Pr]
      _ = Lb ^ m * Pr * (L * Pr) := by rw [ih]
      _ = Lb ^ m * (Pr * L * Pr) := by
          rw [Matrix.mul_assoc (Lb ^ m) Pr (L * Pr), Matrix.mul_assoc Pr L Pr]
      _ = Lb ^ m * Lb := by rw [hLb, hPr]; rfl
      _ = Lb ^ (m + 1) := by rw [pow_succ]
      _ = Lb ^ (m + 1) * Pr := by
          rw [pow_succ, Matrix.mul_assoc, hLbPr]

/-- Time-scaled power form. -/
lemma smul_defectComplement_pow_mul_proj (t : ℝ) (n : ℕ) :
    (t • (L - DefectMatrix L P pi_dist hπ)) ^ n * CoarseProjectorMatrix P pi_dist hπ =
    (t • CoarseGeneratorMatrix L P pi_dist hπ) ^ n * CoarseProjectorMatrix P pi_dist hπ := by
  rw [smul_pow, smul_pow, smul_mul_assoc, smul_mul_assoc,
      defectComplement_pow_mul_proj]

/-- The right-multiplication-by-`Π` functional, out of the weighted algebra. -/
def mulProjLin : PiMat V pi_dist hπ →ₗ[ℝ] Matrix V V ℝ where
  toFun M := toMat pi_dist hπ M * CoarseProjectorMatrix P pi_dist hπ
  map_add' M N := by
    show (toMat pi_dist hπ M + toMat pi_dist hπ N) * _ = _
    rw [add_mul]
  map_smul' c M := by
    show (c • toMat pi_dist hπ M) * _ = _
    rw [smul_mul_assoc]
    rfl

lemma mulProjLin_continuous : Continuous (mulProjLin (V := V) pi_dist hπ P) :=
  LinearMap.continuous_of_finiteDimensional _

/-- **Piece (iii), invariant-subspace exponentiation**: the heat kernels of the
    modified generator `L − D` and of the coarse generator `L̄` agree on the
    coarse subspace — exactly, at every time. -/
theorem exp_defectComplement_mul_proj (t : ℝ) :
    exp ℝ (t • (L - DefectMatrix L P pi_dist hπ)) * CoarseProjectorMatrix P pi_dist hπ =
    exp ℝ (t • CoarseGeneratorMatrix L P pi_dist hπ) * CoarseProjectorMatrix P pi_dist hπ := by
  have key : ∀ X : Matrix V V ℝ,
      HasSum (fun n : ℕ => (n !⁻¹ : ℝ) • (X ^ n * CoarseProjectorMatrix P pi_dist hπ))
        (toMat pi_dist hπ (exp ℝ (ofMat pi_dist hπ X)) * CoarseProjectorMatrix P pi_dist hπ) := by
    intro X
    have h1 : HasSum (fun n : ℕ => (n !⁻¹ : ℝ) • (ofMat pi_dist hπ X) ^ n)
        (exp ℝ (ofMat pi_dist hπ X)) := by
      rw [exp_eq_tsum]
      exact (expSeries_summable' (𝕂 := ℝ) (ofMat pi_dist hπ X)).hasSum
    have h2 := h1.map (mulProjLin (V := V) pi_dist hπ P)
      (mulProjLin_continuous pi_dist hπ P)
    have hterm : (⇑(mulProjLin (V := V) pi_dist hπ P) ∘ fun n : ℕ =>
        (n !⁻¹ : ℝ) • (ofMat pi_dist hπ X) ^ n) =
        fun n : ℕ => (n !⁻¹ : ℝ) • (X ^ n * CoarseProjectorMatrix P pi_dist hπ) := by
      funext n
      show (((n !⁻¹ : ℝ) • (X ^ n) : Matrix V V ℝ)) * _ = _
      rw [smul_mul_assoc]
    rwa [hterm] at h2
  have hA := key (t • (L - DefectMatrix L P pi_dist hπ))
  have hL := key (t • CoarseGeneratorMatrix L P pi_dist hπ)
  have hsame : (fun n : ℕ => (n !⁻¹ : ℝ) •
      ((t • (L - DefectMatrix L P pi_dist hπ)) ^ n * CoarseProjectorMatrix P pi_dist hπ)) =
      fun n : ℕ => (n !⁻¹ : ℝ) •
      ((t • CoarseGeneratorMatrix L P pi_dist hπ) ^ n * CoarseProjectorMatrix P pi_dist hπ) := by
    funext n
    rw [smul_defectComplement_pow_mul_proj]
  rw [hsame] at hA
  have := hA.unique hL
  rwa [exp_piMat_eq, exp_piMat_eq] at this

/-! ## §5. The supersession theorems -/

section AbstractExpBound

variable {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

private lemma norm_pow_le_pow' (x : 𝔸) (n : ℕ) : ‖x ^ n‖ ≤ ‖x‖ ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
    calc ‖x ^ (m + 1)‖ = ‖x ^ m * x‖ := by rw [pow_succ]
      _ ≤ ‖x ^ m‖ * ‖x‖ := norm_mul_le _ _
      _ ≤ ‖x‖ ^ m * ‖x‖ := mul_le_mul_of_nonneg_right ih (norm_nonneg x)
      _ = ‖x‖ ^ (m + 1) := (pow_succ _ _).symm

/-- Series bound for the Banach-algebra exponential: `‖exp x‖ ≤ e^‖x‖`. -/
theorem norm_exp_le (x : 𝔸) : ‖exp ℝ x‖ ≤ Real.exp ‖x‖ := by
  have hsum : Summable fun n : ℕ => (n !⁻¹ : ℝ) • x ^ n := expSeries_summable' (𝕂 := ℝ) x
  have hterm : ∀ n : ℕ, ‖(n !⁻¹ : ℝ) • x ^ n‖ ≤ ‖x‖ ^ n / (n ! : ℝ) := by
    intro n
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n !⁻¹ : ℝ))]
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (norm_pow_le_pow' x n) (by positivity)
  have hmaj : Summable fun n : ℕ => ‖x‖ ^ n / (n ! : ℝ) := Real.summable_pow_div_factorial ‖x‖
  have hnorm : Summable fun n : ℕ => ‖(n !⁻¹ : ℝ) • x ^ n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hmaj
  rw [exp_eq_tsum]
  calc ‖∑' n : ℕ, (n !⁻¹ : ℝ) • x ^ n‖
      ≤ ∑' n : ℕ, ‖(n !⁻¹ : ℝ) • x ^ n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, ‖x‖ ^ n / (n ! : ℝ) := Summable.tsum_le_tsum hterm hnorm hmaj
    _ = Real.exp ‖x‖ := by rw [Real.exp_eq_exp_ℝ, exp_eq_tsum_div]

end AbstractExpBound

/-- **The two ε's are one**: the norm of the defect summand in the weighted
    algebra IS Approximate's leakage measure `opNorm_pi (DefectOperator …)`. -/
theorem defect_eq_validity_leakage (L : Matrix V V ℝ) (P : Partition V) :
    ‖ofMat pi_dist hπ (DefectMatrix L P pi_dist hπ)‖ =
    opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) := by
  rw [pmNorm_def]
  show opNorm_pi pi_dist hπ (matrixToLinearMap (DefectMatrix L P pi_dist hπ)) = _
  rw [defectMatrix_toLin]

variable [Nonempty V]

/-- The π-weighted norm of a matrix exponential, computed in `PiMat`. -/
lemma opNorm_exp_eq_pmNorm (M : Matrix V V ℝ) :
    opNorm_pi pi_dist hπ (matrixToLinearMap (exp ℝ M)) = ‖exp ℝ (ofMat pi_dist hπ M)‖ := by
  rw [pmNorm_def, exp_piMat_eq]

/-- **Supersedes `HeatKernel_opNorm_bound`, quantitatively**: the heat kernel's
    π-weighted operator norm is at most `e^{s‖L‖_π}` — an explicit constant in
    place of the axiom's existential `B`. -/
theorem heatKernel_opNorm_explicit (L : Matrix V V ℝ) (s : ℝ) (hs : 0 ≤ s) :
    opNorm_pi pi_dist hπ (matrixToLinearMap (HeatKernel L s)) ≤
    Real.exp (s * opNorm_pi pi_dist hπ (matrixToLinearMap L)) := by
  show opNorm_pi pi_dist hπ (matrixToLinearMap (exp ℝ (s • L))) ≤ _
  rw [opNorm_exp_eq_pmNorm]
  have h1 : ofMat pi_dist hπ (s • L) = s • ofMat pi_dist hπ L := rfl
  calc ‖exp ℝ (ofMat pi_dist hπ (s • L))‖
      ≤ Real.exp ‖ofMat pi_dist hπ (s • L)‖ := norm_exp_le _
    _ = Real.exp (s * ‖ofMat pi_dist hπ L‖) := by
        rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
    _ = Real.exp (s * opNorm_pi pi_dist hπ (matrixToLinearMap L)) := by rw [pmNorm_def]; rfl

/-- The axiom's exact statement, now a theorem: `B := e^{T‖L‖_π}` works. -/
theorem HeatKernel_opNorm_bound_proved (L : Matrix V V ℝ) (T : ℝ) (hT : 0 ≤ T) :
    ∃ B : ℝ, B ≥ 1 ∧ ∀ s, 0 ≤ s → s ≤ T →
      opNorm_pi pi_dist hπ (matrixToLinearMap (HeatKernel L s)) ≤ B := by
  set nL := opNorm_pi pi_dist hπ (matrixToLinearMap L) with hnL
  have hnL0 : 0 ≤ nL := opNorm_pi_nonneg pi_dist hπ _
  refine ⟨Real.exp (T * nL), ?_, fun s hs0 hsT => ?_⟩
  · have h0 : (0:ℝ) ≤ T * nL := mul_nonneg hT hnL0
    have := Real.exp_le_exp.mpr h0
    rwa [Real.exp_zero] at this
  · refine le_trans (heatKernel_opNorm_explicit pi_dist hπ L s hs0) ?_
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hsT hnL0)

/-- The heat kernel of `L` agrees with the heat kernel of `L − D` composed with
    nothing — for block-constant data, `e^{t(L−D)}f₀ = e^{tL̄}f₀`. -/
lemma exp_defectComplement_apply (L : Matrix V V ℝ) (P : Partition V) (t : ℝ)
    (f₀ : V → ℝ) (hf₀ : f₀ = CoarseProjector P pi_dist hπ f₀) :
    exp ℝ (t • (L - DefectMatrix L P pi_dist hπ)) *ᵥ f₀ =
    HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f₀ := by
  have hPr : CoarseProjectorMatrix P pi_dist hπ *ᵥ f₀ = f₀ := by
    rw [CoarseProjectorMatrix_mulVec]; exact hf₀.symm
  show _ = exp ℝ (t • CoarseGeneratorMatrix L P pi_dist hπ) *ᵥ f₀
  conv_lhs => rw [← hPr, Matrix.mulVec_mulVec, exp_defectComplement_mul_proj,
    ← Matrix.mulVec_mulVec, hPr]

/-- **The Defect-Horizon Bound** (supersedes `Horizontal_Duhamel_integral_bound`,
    quantitatively): for block-constant initial data, the true trajectory and the
    coarse-model trajectory separate at most linearly in `t·ε`, with the explicit
    semigroup constant `e^{t(‖L−D‖_π+ε)}` in place of the axiom's existential
    `B·B`. Kernel-proved end to end: `validity_horizon` on the weighted algebra
    `PiMat`, with the decomposition `L = (L−D) + D` and the invariant-subspace
    identity `e^{t(L−D)}Π = e^{tL̄}Π`. -/
theorem defect_horizon_bound (L : Matrix V V ℝ) (P : Partition V) (t : ℝ) (ht : 0 ≤ t)
    (f₀ : V → ℝ) (hf₀ : f₀ = CoarseProjector P pi_dist hπ f₀) :
    norm_pi pi_dist (HeatKernelMap L t f₀ -
      HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f₀) ≤
    t * opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) *
      Real.exp (t * (opNorm_pi pi_dist hπ (matrixToLinearMap (L - DefectMatrix L P pi_dist hπ)) +
        opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ))) *
      norm_pi pi_dist f₀ := by
  set D := DefectMatrix L P pi_dist hπ with hD
  set A : PiMat V pi_dist hπ := ofMat pi_dist hπ (L - D) with hA
  set B : PiMat V pi_dist hπ := ofMat pi_dist hπ D with hB
  have hAB : A + B = ofMat pi_dist hπ L := by
    show (L - D) + D = L
    rw [sub_add_cancel]
  -- the trajectory difference is the matrix difference acting on f₀
  have hdiff : HeatKernelMap L t f₀ -
      HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f₀ =
      (toMat pi_dist hπ (exp ℝ (t • (A + B)) - exp ℝ (t • A))) *ᵥ f₀ := by
    have h1 : toMat pi_dist hπ (exp ℝ (t • (A + B))) = exp ℝ (t • L) := by
      rw [hAB]
      exact exp_piMat_eq pi_dist hπ (t • L)
    have h2 : toMat pi_dist hπ (exp ℝ (t • A)) = exp ℝ (t • (L - D)) :=
      exp_piMat_eq pi_dist hπ (t • (L - D))
    show _ = (toMat pi_dist hπ (exp ℝ (t • (A + B))) - toMat pi_dist hπ (exp ℝ (t • A))) *ᵥ f₀
    rw [Matrix.sub_mulVec, h1, h2, exp_defectComplement_apply pi_dist hπ L P t f₀ hf₀]
    rfl
  rw [hdiff]
  -- norm bound through the weighted algebra
  have hbound := pmNorm_mulVec_le pi_dist hπ (exp ℝ (t • (A + B)) - exp ℝ (t • A)) f₀
  refine le_trans hbound ?_
  have hvh := SGC.Bridge.ValidityHorizon.validity_horizon A B t ht
  have hBnorm : ‖B‖ = opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) :=
    defect_eq_validity_leakage pi_dist hπ L P
  have hAnorm : ‖A‖ = opNorm_pi pi_dist hπ (matrixToLinearMap (L - D)) := by
    rw [pmNorm_def]; rfl
  rw [hBnorm, hAnorm] at hvh
  exact mul_le_mul_of_nonneg_right hvh (norm_pi_nonneg' pi_dist f₀)

/-- **ε-form** (the `IsApproxLumpable` vocabulary of the superseded axiom):
    tolerance ε bounds the trajectory gap by `t·ε·e^{t(‖L−D‖_π+ε)}·‖f₀‖_π`. -/
theorem trajectory_closure_bound_explicit (L : Matrix V V ℝ) (P : Partition V)
    (ε : ℝ) (hL : IsApproxLumpable L P pi_dist hπ ε) (t : ℝ) (ht : 0 ≤ t)
    (f₀ : V → ℝ) (hf₀ : f₀ = CoarseProjector P pi_dist hπ f₀) :
    norm_pi pi_dist (HeatKernelMap L t f₀ -
      HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f₀) ≤
    t * ε * Real.exp (t * (opNorm_pi pi_dist hπ
        (matrixToLinearMap (L - DefectMatrix L P pi_dist hπ)) + ε)) *
      norm_pi pi_dist f₀ := by
  have hkey := defect_horizon_bound pi_dist hπ L P t ht f₀ hf₀
  set dN := opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) with hdN
  set aN := opNorm_pi pi_dist hπ (matrixToLinearMap (L - DefectMatrix L P pi_dist hπ)) with haN
  have hdN0 : 0 ≤ dN := opNorm_pi_nonneg pi_dist hπ _
  have hε : dN ≤ ε := hL
  have hf0 : 0 ≤ norm_pi pi_dist f₀ := norm_pi_nonneg' pi_dist f₀
  refine le_trans hkey ?_
  have hexp : Real.exp (t * (aN + dN)) ≤ Real.exp (t * (aN + ε)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) ht)
  have h1 : t * dN * Real.exp (t * (aN + dN)) ≤ t * ε * Real.exp (t * (aN + ε)) := by
    have ha : 0 ≤ t * dN := mul_nonneg ht hdN0
    have hb : t * dN ≤ t * ε := mul_le_mul_of_nonneg_left hε ht
    have hc : 0 ≤ Real.exp (t * (aN + dN)) := (Real.exp_pos _).le
    calc t * dN * Real.exp (t * (aN + dN))
        ≤ t * ε * Real.exp (t * (aN + dN)) := mul_le_mul_of_nonneg_right hb hc
      _ ≤ t * ε * Real.exp (t * (aN + ε)) := by
          apply mul_le_mul_of_nonneg_left hexp
          exact mul_nonneg ht (le_trans hdN0 hε)
  exact mul_le_mul_of_nonneg_right h1 hf0

/-! ## §6. The vertical companion: superseding `Duhamel_integral_bound` -/

/-- Left absorption: `Π · L̄ = L̄`. The coarse generator's range is coarse. -/
lemma proj_mul_coarseGen (L : Matrix V V ℝ) (P : Partition V) :
    CoarseProjectorMatrix P pi_dist hπ * CoarseGeneratorMatrix L P pi_dist hπ =
    CoarseGeneratorMatrix L P pi_dist hπ := by
  have hidem : CoarseProjectorMatrix P pi_dist hπ * CoarseProjectorMatrix P pi_dist hπ =
      CoarseProjectorMatrix P pi_dist hπ := CoarseProjectorMatrix_idempotent P pi_dist hπ
  show CoarseProjectorMatrix P pi_dist hπ *
      (CoarseProjectorMatrix P pi_dist hπ * L * CoarseProjectorMatrix P pi_dist hπ) =
      CoarseProjectorMatrix P pi_dist hπ * L * CoarseProjectorMatrix P pi_dist hπ
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hidem]

/-- For block-constant `f₀`, the coarse heat kernel stays coarse:
    `Π e^{tL̄}f₀ = e^{tL̄}f₀`. Proved by transporting the exp series through the
    two linear maps `M ↦ M f₀` and `M ↦ Π(M f₀)`, equal term-by-term since each
    power `(tL̄)ⁿf₀` is already coarse. -/
lemma coarseProj_fixes_coarse_heatKernel (L : Matrix V V ℝ) (P : Partition V) (t : ℝ)
    (f₀ : V → ℝ) (hf₀ : f₀ = CoarseProjector P pi_dist hπ f₀) :
    CoarseProjector P pi_dist hπ
      (HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f₀) =
    HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f₀ := by
  have hPrf : CoarseProjectorMatrix P pi_dist hπ *ᵥ f₀ = f₀ := by
    rw [CoarseProjectorMatrix_mulVec]; exact hf₀.symm
  have hPrL : CoarseProjectorMatrix P pi_dist hπ *
      (t • CoarseGeneratorMatrix L P pi_dist hπ) = t • CoarseGeneratorMatrix L P pi_dist hπ := by
    rw [mul_smul_comm, proj_mul_coarseGen]
  have hpow : ∀ n : ℕ, CoarseProjectorMatrix P pi_dist hπ *ᵥ
      ((t • CoarseGeneratorMatrix L P pi_dist hπ) ^ n *ᵥ f₀) =
      (t • CoarseGeneratorMatrix L P pi_dist hπ) ^ n *ᵥ f₀ := by
    intro n
    induction n with
    | zero => simpa using hPrf
    | succ m _ =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hPrL]
  have h1 : HasSum (fun n : ℕ => (n !⁻¹ : ℝ) •
      (ofMat pi_dist hπ (t • CoarseGeneratorMatrix L P pi_dist hπ)) ^ n)
      (exp ℝ (ofMat pi_dist hπ (t • CoarseGeneratorMatrix L P pi_dist hπ))) := by
    rw [exp_eq_tsum]
    exact (expSeries_summable' (𝕂 := ℝ)
      (ofMat pi_dist hπ (t • CoarseGeneratorMatrix L P pi_dist hπ))).hasSum
  let applyLin : PiMat V pi_dist hπ →ₗ[ℝ] (V → ℝ) :=
    { toFun := fun M => toMat pi_dist hπ M *ᵥ f₀
      map_add' := fun M N => by
        show (toMat pi_dist hπ M + toMat pi_dist hπ N) *ᵥ f₀ = _
        rw [Matrix.add_mulVec]
      map_smul' := fun c M => by
        show (c • toMat pi_dist hπ M) *ᵥ f₀ = _
        rw [Matrix.smul_mulVec]; rfl }
  let projApplyLin : PiMat V pi_dist hπ →ₗ[ℝ] (V → ℝ) :=
    { toFun := fun M => CoarseProjectorMatrix P pi_dist hπ *ᵥ (toMat pi_dist hπ M *ᵥ f₀)
      map_add' := fun M N => by
        show CoarseProjectorMatrix P pi_dist hπ *ᵥ
          ((toMat pi_dist hπ M + toMat pi_dist hπ N) *ᵥ f₀) = _
        rw [Matrix.add_mulVec, Matrix.mulVec_add]
      map_smul' := fun c M => by
        show CoarseProjectorMatrix P pi_dist hπ *ᵥ ((c • toMat pi_dist hπ M) *ᵥ f₀) = _
        rw [Matrix.smul_mulVec, Matrix.mulVec_smul]; rfl }
  have ha := h1.map applyLin (LinearMap.continuous_of_finiteDimensional _)
  have hb := h1.map projApplyLin (LinearMap.continuous_of_finiteDimensional _)
  have hterm_a : (⇑applyLin ∘ fun n : ℕ => (n !⁻¹ : ℝ) •
      (ofMat pi_dist hπ (t • CoarseGeneratorMatrix L P pi_dist hπ)) ^ n) =
      fun n : ℕ => (n !⁻¹ : ℝ) •
        ((t • CoarseGeneratorMatrix L P pi_dist hπ) ^ n *ᵥ f₀) := by
    funext n
    show ((n !⁻¹ : ℝ) • (t • CoarseGeneratorMatrix L P pi_dist hπ) ^ n) *ᵥ f₀ = _
    rw [Matrix.smul_mulVec]
  have hterm_b : (⇑projApplyLin ∘ fun n : ℕ => (n !⁻¹ : ℝ) •
      (ofMat pi_dist hπ (t • CoarseGeneratorMatrix L P pi_dist hπ)) ^ n) =
      fun n : ℕ => (n !⁻¹ : ℝ) •
        ((t • CoarseGeneratorMatrix L P pi_dist hπ) ^ n *ᵥ f₀) := by
    funext n
    show CoarseProjectorMatrix P pi_dist hπ *ᵥ
      (((n !⁻¹ : ℝ) • (t • CoarseGeneratorMatrix L P pi_dist hπ) ^ n) *ᵥ f₀) = _
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul, hpow]
  rw [hterm_a] at ha
  rw [hterm_b] at hb
  have happly : applyLin (exp ℝ (ofMat pi_dist hπ
      (t • CoarseGeneratorMatrix L P pi_dist hπ))) =
      HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f₀ := by
    show toMat pi_dist hπ (exp ℝ (ofMat pi_dist hπ
      (t • CoarseGeneratorMatrix L P pi_dist hπ))) *ᵥ f₀ = _
    rw [exp_piMat_eq]; rfl
  have hproj : projApplyLin (exp ℝ (ofMat pi_dist hπ
      (t • CoarseGeneratorMatrix L P pi_dist hπ))) =
      CoarseProjectorMatrix P pi_dist hπ *ᵥ
        HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f₀ := by
    show CoarseProjectorMatrix P pi_dist hπ *ᵥ (toMat pi_dist hπ (exp ℝ (ofMat pi_dist hπ
      (t • CoarseGeneratorMatrix L P pi_dist hπ))) *ᵥ f₀) = _
    rw [exp_piMat_eq]; rfl
  have huniq := ha.unique hb
  rw [happly, hproj] at huniq
  rw [← CoarseProjectorMatrix_mulVec]
  exact huniq.symm

/-- **The vertical defect-horizon bound** (supersedes `Duhamel_integral_bound`,
    quantitatively). The trajectory's leakage OUT of the coarse subspace obeys the
    SAME explicit bound as the horizontal gap, because the vertical defect IS the
    horizontal gap projected: for block-constant `f₀`,
    `(I−Π)e^{tL}f₀ = (I−Π)(e^{tL}f₀ − e^{tL̄}f₀)` (since `e^{tL̄}f₀` stays coarse),
    and `(I−Π)` is π-contractive. -/
theorem vertical_defect_horizon_bound (L : Matrix V V ℝ) (P : Partition V)
    (t : ℝ) (ht : 0 ≤ t) (f₀ : V → ℝ) (hf₀ : f₀ = CoarseProjector P pi_dist hπ f₀) :
    norm_pi pi_dist (HeatKernelMap L t f₀ -
      CoarseProjector P pi_dist hπ (HeatKernelMap L t f₀)) ≤
    t * opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) *
      Real.exp (t * (opNorm_pi pi_dist hπ (matrixToLinearMap (L - DefectMatrix L P pi_dist hπ)) +
        opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ))) *
      norm_pi pi_dist f₀ := by
  have hfix := coarseProj_fixes_coarse_heatKernel pi_dist hπ L P t f₀ hf₀
  have hId : HeatKernelMap L t f₀ - CoarseProjector P pi_dist hπ (HeatKernelMap L t f₀) =
      (HeatKernelMap L t f₀ - HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f₀) -
        CoarseProjector P pi_dist hπ
          (HeatKernelMap L t f₀ - HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f₀) := by
    rw [map_sub, hfix]
    ext x; simp only [Pi.sub_apply]; ring
  rw [hId]
  refine le_trans (CoarseProjector_compl_contractive P pi_dist hπ _) ?_
  exact defect_horizon_bound pi_dist hπ L P t ht f₀ hf₀

/-- **ε-form** of the vertical bound (the `IsApproxLumpable` vocabulary of the
    superseded `Duhamel_integral_bound`): leakage out of the coarse subspace is
    bounded by `t·ε·e^{t(‖L−D‖_π+ε)}·‖f₀‖_π`. -/
theorem vertical_closure_bound_explicit (L : Matrix V V ℝ) (P : Partition V)
    (ε : ℝ) (hL : IsApproxLumpable L P pi_dist hπ ε) (t : ℝ) (ht : 0 ≤ t)
    (f₀ : V → ℝ) (hf₀ : f₀ = CoarseProjector P pi_dist hπ f₀) :
    norm_pi pi_dist (HeatKernelMap L t f₀ -
      CoarseProjector P pi_dist hπ (HeatKernelMap L t f₀)) ≤
    t * ε * Real.exp (t * (opNorm_pi pi_dist hπ
        (matrixToLinearMap (L - DefectMatrix L P pi_dist hπ)) + ε)) *
      norm_pi pi_dist f₀ := by
  have hkey := vertical_defect_horizon_bound pi_dist hπ L P t ht f₀ hf₀
  set dN := opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) with hdN
  set aN := opNorm_pi pi_dist hπ (matrixToLinearMap (L - DefectMatrix L P pi_dist hπ)) with haN
  have hdN0 : 0 ≤ dN := opNorm_pi_nonneg pi_dist hπ _
  have hε : dN ≤ ε := hL
  have hf0 : 0 ≤ norm_pi pi_dist f₀ := norm_pi_nonneg' pi_dist f₀
  refine le_trans hkey ?_
  have hexp : Real.exp (t * (aN + dN)) ≤ Real.exp (t * (aN + ε)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) ht)
  have h1 : t * dN * Real.exp (t * (aN + dN)) ≤ t * ε * Real.exp (t * (aN + ε)) := by
    have hb : t * dN ≤ t * ε := mul_le_mul_of_nonneg_left hε ht
    have hc : 0 ≤ Real.exp (t * (aN + dN)) := (Real.exp_pos _).le
    calc t * dN * Real.exp (t * (aN + dN))
        ≤ t * ε * Real.exp (t * (aN + dN)) := mul_le_mul_of_nonneg_right hb hc
      _ ≤ t * ε * Real.exp (t * (aN + ε)) := by
          apply mul_le_mul_of_nonneg_left hexp
          exact mul_nonneg ht (le_trans hdN0 hε)
  exact mul_le_mul_of_nonneg_right h1 hf0

/-! ## §7. Total-error Pythagorean split: horizontal ⊕ vertical

The two legs proved above — the horizontal trajectory gap (`defect_horizon_bound`) and
the vertical leakage defect (`vertical_defect_horizon_bound`) — are not independent
bounds on the same quantity. They are the two **orthogonal components** of one error
vector. Because `Π` is the π-self-adjoint conditional-expectation projector, it is an
orthogonal projection in `L²(π)`, so the total trajectory error decomposes by
Pythagoras with **no cross term**. This is an exact identity (no `ε`, no perturbation),
valid for every `t` and every generator `L`. -/

/-- **π-orthogonal Pythagoras for the coarse projector.** Every vector splits into its
    coarse part `Π w` and its leakage part `w − Π w` with no cross term:
    `‖w‖²_π = ‖Π w‖²_π + ‖w − Π w‖²_π`. Holds because `Π` is π-self-adjoint
    (`CoarseProjector_self_adjoint`), hence a π-orthogonal projection. -/
lemma norm_sq_pi_proj_pythagorean (P : Partition V) (w : V → ℝ) :
    norm_sq_pi pi_dist w =
      norm_sq_pi pi_dist (CoarseProjector P pi_dist hπ w) +
      norm_sq_pi pi_dist (w - CoarseProjector P pi_dist hπ w) := by
  have h_ortho := CoarseProjector_orthogonal P pi_dist hπ w
  have h_cross2 : inner_pi pi_dist (w - CoarseProjector P pi_dist hπ w)
      (CoarseProjector P pi_dist hπ w) = 0 := by rw [inner_pi_comm]; exact h_ortho
  have h_decomp : w = CoarseProjector P pi_dist hπ w + (w - CoarseProjector P pi_dist hπ w) := by
    ext x; simp only [Pi.add_apply, Pi.sub_apply]; ring
  conv_lhs => rw [h_decomp]
  unfold norm_sq_pi
  rw [inner_pi_add_left, inner_pi_add_right, inner_pi_add_right, h_ortho, h_cross2]
  ring

/-- **Total-error Pythagorean decomposition.** For a block-constant initial condition
    `f₀ = Π f₀`, the total trajectory error between the full and coarse evolutions splits
    orthogonally in the π-inner-product into an in-subspace (horizontal) error and a
    leakage (vertical) defect:

    `‖e^{tL}f₀ − e^{tL̄}f₀‖²_π = ‖Π e^{tL}f₀ − e^{tL̄}f₀‖²_π + ‖(I−Π)e^{tL}f₀‖²_π`.

    The split is **exact** — it follows purely from π-orthogonality of `Π` plus the fact
    that the coarse trajectory stays coarse (`coarseProj_fixes_coarse_heatKernel`), with
    no closure hypothesis. The horizontal leg `Π e^{tL}f₀ − e^{tL̄}f₀` lives entirely in
    the coarse subspace and is bounded by `defect_horizon_bound` (it is ≤ the
    hypotenuse); the vertical leg `(I−Π)e^{tL}f₀` is bounded by
    `vertical_defect_horizon_bound`. As an immediate corollary, each leg is individually
    ≤ the total gap, and `‖total‖²_π = ‖horizontal‖²_π + ‖vertical‖²_π`.

    (This is pure `L²(π)` projection geometry on the trajectory gap; it is unrelated to
    the refuted learning-defect *ratio* identity in `DefectDynamics`.) -/
theorem total_error_pythagorean (L : Matrix V V ℝ) (P : Partition V)
    (t : ℝ) (f₀ : V → ℝ) (hf₀ : f₀ = CoarseProjector P pi_dist hπ f₀) :
    norm_sq_pi pi_dist (HeatKernelMap L t f₀ -
        HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f₀)
      = norm_sq_pi pi_dist (CoarseProjector P pi_dist hπ (HeatKernelMap L t f₀) -
          HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f₀)
      + norm_sq_pi pi_dist (HeatKernelMap L t f₀ -
          CoarseProjector P pi_dist hπ (HeatKernelMap L t f₀)) := by
  have hfix := coarseProj_fixes_coarse_heatKernel pi_dist hπ L P t f₀ hf₀
  -- Π(full − coarse) = Π full − coarse, since the coarse trajectory stays coarse.
  have hProjE : CoarseProjector P pi_dist hπ
      (HeatKernelMap L t f₀ - HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f₀) =
      CoarseProjector P pi_dist hπ (HeatKernelMap L t f₀) -
        HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f₀ := by
    rw [map_sub, hfix]
  -- General π-Pythagoras on the trajectory gap, then identify the two legs.
  have hPyth := norm_sq_pi_proj_pythagorean pi_dist hπ P
    (HeatKernelMap L t f₀ - HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f₀)
  rw [hProjE] at hPyth
  have hComplE : (HeatKernelMap L t f₀ -
        HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f₀) -
      (CoarseProjector P pi_dist hπ (HeatKernelMap L t f₀) -
        HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f₀) =
      HeatKernelMap L t f₀ - CoarseProjector P pi_dist hπ (HeatKernelMap L t f₀) := by
    ext x; simp only [Pi.sub_apply]; ring
  rw [hComplE] at hPyth
  exact hPyth

end SGC.Bridge.DefectHorizonBridge
