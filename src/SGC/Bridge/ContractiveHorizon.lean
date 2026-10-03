/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Bridge.DefectHorizonBridge
import SGC.InformationGeometry.ContinuousTimeKernel

/-!
# The contractive validity horizon: `‖e^{tL}f₀ − e^{tL̄}f₀‖_π ≤ t·ε·‖f₀‖_π`

`DefectHorizonBridge.defect_horizon_bound` pays an exponential factor
`e^{t(‖L−D‖_π+ε)}` for the semigroup perturbation. When both semigroups are
contractions that factor is 1. The proof avoids integrals: the Duhamel bound
`‖exp(t(A+B)) − exp(tA)‖ ≤ t‖B‖e^{t(‖A‖+‖B‖)}` (`ValidityHorizon.validity_horizon`)
is applied on `n` short steps of length `t/n`, the `n` pieces are telescoped through
contractions (`‖Xⁿ − Yⁿ‖ ≤ n‖X − Y‖` when `‖X‖, ‖Y‖ ≤ 1`), and `n → ∞` removes the
exponential: `t‖B‖e^{tM/n} → t‖B‖`.

Two levels:

* **Banach algebra** (`exp_perturbation_bound_contractive`): both `exp(sA)` and
  `exp(s(A+B))` contractions for `s ≥ 0`.
* **Vectors** (`trajectory_closure_bound_contractive`): the coarse semigroup need only
  be contractive on the trajectory of the block-constant initial datum — necessary
  because `e^{s(L−D)}` is not a contraction on all of `L²(π)`, only on the invariant
  coarse subspace, where it equals `e^{sL̄}`.

The fine-side hypothesis is discharged for genuine stochastic generators:
`heatKernel_contractive_of_generator` — a rate generator with stationary `π` has
`‖e^{sL}‖_π ≤ 1` (Jensen/Cauchy–Schwarz on a stochastic kernel with stationary weight).
The coarse-side hypothesis `hcoarse` is discharged in `Bridge/CoarseContraction.lean`.

Numerical witness: `docs/experiments/gauge_lumpability_v1` (Z₂/Z₃ lattice gauge chains):
`max_t err/(ε t) = 0.9985` over 472 (chain, partition, f₀) pairs, while the exponential
constant of `defect_horizon_bound` overshoots by up to a factor 528.

Coarse side: discharged in `Bridge/CoarseContraction.lean` via `L̃ = ΠLΠ + c(Π − 1)`;
see `trajectory_closure_bound_stationary` there for the unconditional statement.
-/

noncomputable section

namespace SGC.Bridge.ContractiveHorizon

open Finset Matrix NormedSpace Filter Topology
open scoped Nat
open SGC.Approximate SGC.Bridge.DefectHorizonBridge

/-! ## §1. Abstract Banach-algebra level -/

section Abstract

variable {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

omit [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] in
/-- Telescoping through contractions: `‖Xⁿ − Yⁿ‖ ≤ n‖X − Y‖` when `‖X‖, ‖Y‖ ≤ 1`. -/
theorem norm_pow_sub_pow_le_of_contractive (X Y : 𝔸) (hX : ‖X‖ ≤ 1) (hY : ‖Y‖ ≤ 1) (n : ℕ) :
    ‖X ^ n - Y ^ n‖ ≤ (n : ℝ) * ‖X - Y‖ := by
  induction n with
  | zero => simp
  | succ m ih =>
    have key : X ^ (m + 1) - Y ^ (m + 1) = X * (X ^ m - Y ^ m) + (X - Y) * Y ^ m := by
      rw [pow_succ', pow_succ']
      noncomm_ring
    have hYm : ‖Y ^ m‖ ≤ 1 :=
      le_trans (norm_pow_le Y m) (pow_le_one₀ (norm_nonneg Y) hY)
    rw [key]
    calc ‖X * (X ^ m - Y ^ m) + (X - Y) * Y ^ m‖
        ≤ ‖X * (X ^ m - Y ^ m)‖ + ‖(X - Y) * Y ^ m‖ := norm_add_le _ _
      _ ≤ ‖X‖ * ‖X ^ m - Y ^ m‖ + ‖X - Y‖ * ‖Y ^ m‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ 1 * ((m : ℝ) * ‖X - Y‖) + ‖X - Y‖ * 1 := by
          apply add_le_add
          · exact mul_le_mul hX ih (norm_nonneg _) zero_le_one
          · exact mul_le_mul_of_nonneg_left hYm (norm_nonneg _)
      _ = ((m + 1 : ℕ) : ℝ) * ‖X - Y‖ := by push_cast; ring

omit [NormOneClass 𝔸] in
/-- `exp(t•x) = exp((t/n)•x)^n` for `n ≥ 1`. -/
lemma exp_smul_eq_pow (x : 𝔸) (t : ℝ) {n : ℕ} (hn : 0 < n) :
    exp ℝ (t • x) = exp ℝ ((t / n) • x) ^ n := by
  have h := NormedSpace.exp_nsmul (𝕂 := ℝ) n ((t / n) • x)
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have e : (n • ((t / n) • x) : 𝔸) = t • x := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_div_cancel₀ _ hn']
  rw [e] at h
  exact h

/-- **Semigroup perturbation bound for contractions**: if `exp(sA)` and `exp(s(A+B))`
are contractions for all `s ≥ 0`, then `‖exp(t(A+B)) − exp(tA)‖ ≤ t‖B‖` — no
exponential factor. -/
theorem exp_perturbation_bound_contractive (A B : 𝔸) (t : ℝ) (ht : 0 ≤ t)
    (hA : ∀ s : ℝ, 0 ≤ s → ‖exp ℝ (s • A)‖ ≤ 1)
    (hAB : ∀ s : ℝ, 0 ≤ s → ‖exp ℝ (s • (A + B))‖ ≤ 1) :
    ‖exp ℝ (t • (A + B)) - exp ℝ (t • A)‖ ≤ t * ‖B‖ := by
  set M : ℝ := ‖A‖ + ‖B‖ with hM
  -- step bound for every n ≥ 1
  have key : ∀ n : ℕ, 0 < n →
      ‖exp ℝ (t • (A + B)) - exp ℝ (t • A)‖ ≤ t * ‖B‖ * Real.exp (t * M / n) := by
    intro n hn
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    set h : ℝ := t / n with hh
    have hh0 : 0 ≤ h := div_nonneg ht hn'.le
    rw [exp_smul_eq_pow (A + B) t hn, exp_smul_eq_pow A t hn, ← hh]
    have hstep := SGC.Bridge.ValidityHorizon.validity_horizon A B h hh0
    calc ‖exp ℝ (h • (A + B)) ^ n - exp ℝ (h • A) ^ n‖
        ≤ (n : ℝ) * ‖exp ℝ (h • (A + B)) - exp ℝ (h • A)‖ :=
          norm_pow_sub_pow_le_of_contractive _ _ (hAB h hh0) (hA h hh0) n
      _ ≤ (n : ℝ) * (h * ‖B‖ * Real.exp (h * (‖A‖ + ‖B‖))) :=
          mul_le_mul_of_nonneg_left hstep hn'.le
      _ = t * ‖B‖ * Real.exp (t * M / n) := by
          rw [hh, hM]
          field_simp
  -- let n → ∞
  have hlim : Tendsto (fun n : ℕ => t * ‖B‖ * Real.exp (t * M / n)) atTop
      (𝓝 (t * ‖B‖ * Real.exp 0)) := by
    have h1 : Tendsto (fun n : ℕ => t * M / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (t * M)
    exact (Real.continuous_exp.tendsto 0 |>.comp h1).const_mul _
  rw [Real.exp_zero, mul_one] at hlim
  exact ge_of_tendsto hlim (eventually_atTop.2 ⟨1, fun n hn => key n hn⟩)

end Abstract

/-! ## §2. Vector level on the weighted algebra -/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)

/-- Vector telescoping: `X` a `π`-contraction, `Y` contractive along the orbit of `f`. -/
lemma norm_pi_pow_sub_pow_mulVec_le (X Y : Matrix V V ℝ) (f : V → ℝ)
    (hX : opNorm_pi pi_dist hπ (matrixToLinearMap X) ≤ 1)
    (hY : ∀ k : ℕ, norm_pi pi_dist (Y ^ k *ᵥ f) ≤ norm_pi pi_dist f) (n : ℕ) :
    norm_pi pi_dist ((X ^ n - Y ^ n) *ᵥ f) ≤
      (n : ℝ) * opNorm_pi pi_dist hπ (matrixToLinearMap (X - Y)) * norm_pi pi_dist f := by
  induction n with
  | zero => simp [norm_pi, norm_sq_pi, inner_pi]
  | succ m ih =>
    have key : (X ^ (m + 1) - Y ^ (m + 1)) *ᵥ f =
        X *ᵥ ((X ^ m - Y ^ m) *ᵥ f) + (X - Y) *ᵥ (Y ^ m *ᵥ f) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec]
      congr 1
      rw [pow_succ', pow_succ']
      noncomm_ring
    rw [key]
    have hXf : norm_pi pi_dist (X *ᵥ ((X ^ m - Y ^ m) *ᵥ f)) ≤
        norm_pi pi_dist ((X ^ m - Y ^ m) *ᵥ f) := by
      have := opNorm_pi_bound pi_dist hπ (matrixToLinearMap X) ((X ^ m - Y ^ m) *ᵥ f)
      refine le_trans this ?_
      exact mul_le_of_le_one_left (norm_pi_nonneg' pi_dist _) hX
    have hXYf : norm_pi pi_dist ((X - Y) *ᵥ (Y ^ m *ᵥ f)) ≤
        opNorm_pi pi_dist hπ (matrixToLinearMap (X - Y)) * norm_pi pi_dist f := by
      have := opNorm_pi_bound pi_dist hπ (matrixToLinearMap (X - Y)) (Y ^ m *ᵥ f)
      refine le_trans this ?_
      exact mul_le_mul_of_nonneg_left (hY m) (opNorm_pi_nonneg pi_dist hπ _)
    calc norm_pi pi_dist (X *ᵥ ((X ^ m - Y ^ m) *ᵥ f) + (X - Y) *ᵥ (Y ^ m *ᵥ f))
        ≤ norm_pi pi_dist (X *ᵥ ((X ^ m - Y ^ m) *ᵥ f)) +
          norm_pi pi_dist ((X - Y) *ᵥ (Y ^ m *ᵥ f)) := norm_pi_add_le pi_dist hπ _ _
      _ ≤ (m : ℝ) * opNorm_pi pi_dist hπ (matrixToLinearMap (X - Y)) * norm_pi pi_dist f +
          opNorm_pi pi_dist hπ (matrixToLinearMap (X - Y)) * norm_pi pi_dist f :=
          add_le_add (le_trans hXf ih) hXYf
      _ = ((m + 1 : ℕ) : ℝ) * opNorm_pi pi_dist hπ (matrixToLinearMap (X - Y)) *
          norm_pi pi_dist f := by push_cast; ring

variable [Nonempty V]

omit [Nonempty V] in
/-- The π-operator norm of a matrix equals its norm in the weighted algebra `PiMat`. -/
lemma opNorm_pi_eq_pmNorm (M : Matrix V V ℝ) :
    opNorm_pi pi_dist hπ (matrixToLinearMap M) = ‖ofMat pi_dist hπ M‖ := by
  rw [pmNorm_def]; rfl

/-- **Contractive trajectory closure bound.** For block-constant `f₀`, if the fine
semigroup is a `π`-contraction and the coarse semigroup is contractive along the
trajectory of `f₀`, then

  `‖e^{tL}f₀ − e^{tL̄}f₀‖_π ≤ t · ‖D‖_π · ‖f₀‖_π`,

with `D = (I−Π)LΠ` the leakage defect and **no** exponential factor. -/
theorem trajectory_closure_bound_contractive (L : Matrix V V ℝ) (P : Partition V)
    (t : ℝ) (ht : 0 ≤ t) (f₀ : V → ℝ) (hf₀ : f₀ = CoarseProjector P pi_dist hπ f₀)
    (hfine : ∀ s : ℝ, 0 ≤ s → opNorm_pi pi_dist hπ (matrixToLinearMap (HeatKernel L s)) ≤ 1)
    (hcoarse : ∀ s : ℝ, 0 ≤ s →
      norm_pi pi_dist (HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) s f₀) ≤
        norm_pi pi_dist f₀) :
    norm_pi pi_dist (HeatKernelMap L t f₀ -
      HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f₀) ≤
    t * opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) * norm_pi pi_dist f₀ := by
  set D := DefectMatrix L P pi_dist hπ with hD
  set ε := opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) with hε
  have hε0 : 0 ≤ ε := opNorm_pi_nonneg pi_dist hπ _
  have hf0 : 0 ≤ norm_pi pi_dist f₀ := norm_pi_nonneg' pi_dist f₀
  set M : ℝ := opNorm_pi pi_dist hπ (matrixToLinearMap (L - D)) + ε with hM
  -- the difference as a matrix acting on f₀
  have hdiff : ∀ s : ℝ, HeatKernelMap L s f₀ -
      HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) s f₀ =
      (exp ℝ (s • L) - exp ℝ (s • (L - D))) *ᵥ f₀ := by
    intro s
    rw [Matrix.sub_mulVec, exp_defectComplement_apply pi_dist hπ L P s f₀ hf₀]
    rfl
  -- step bound for every n ≥ 1
  have key : ∀ n : ℕ, 0 < n →
      norm_pi pi_dist (HeatKernelMap L t f₀ -
        HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f₀) ≤
      t * ε * Real.exp (t * M / n) * norm_pi pi_dist f₀ := by
    intro n hn
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    set h : ℝ := t / n with hh
    have hh0 : 0 ≤ h := div_nonneg ht hn'.le
    rw [hdiff]
    -- exp(t•X) = exp(h•X)^n, in the weighted algebra
    have hpow : ∀ X : Matrix V V ℝ, exp ℝ (t • X) = exp ℝ (h • X) ^ n := by
      intro X
      have hPM := exp_smul_eq_pow (ofMat pi_dist hπ X) t hn
      have e1 := exp_piMat_eq pi_dist hπ (t • X)
      have e2 := exp_piMat_eq pi_dist hπ (h • X)
      rw [← e1, ← e2]
      exact congrArg (toMat pi_dist hπ) hPM
    have hpowL : exp ℝ (t • L) = exp ℝ (h • L) ^ n := hpow L
    have hpowLD : exp ℝ (t • (L - D)) = exp ℝ (h • (L - D)) ^ n := hpow (L - D)
    rw [hpowL, hpowLD]
    -- the coarse semigroup is contractive along the orbit of f₀
    have hY : ∀ k : ℕ, norm_pi pi_dist (exp ℝ (h • (L - D)) ^ k *ᵥ f₀) ≤ norm_pi pi_dist f₀ := by
      intro k
      have hk : exp ℝ (h • (L - D)) ^ k = exp ℝ ((k * h) • (L - D)) := by
        have hPM := (NormedSpace.exp_nsmul (𝕂 := ℝ) k (ofMat pi_dist hπ (h • (L - D)))).symm
        have h2 : (k • (ofMat pi_dist hπ (h • (L - D))) : PiMat V pi_dist hπ) =
            ofMat pi_dist hπ ((k * h) • (L - D)) := by
          show (k • (h • (L - D)) : Matrix V V ℝ) = (k * h) • (L - D)
          rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
        rw [h2] at hPM
        have e1 := exp_piMat_eq pi_dist hπ (h • (L - D))
        have e2 := exp_piMat_eq pi_dist hπ ((k * h) • (L - D))
        rw [← e1, ← e2]
        exact congrArg (toMat pi_dist hπ) hPM
      rw [hk, exp_defectComplement_apply pi_dist hπ L P (k * h) f₀ hf₀]
      exact hcoarse (k * h) (mul_nonneg (Nat.cast_nonneg k) hh0)
    have hX : opNorm_pi pi_dist hπ (matrixToLinearMap (exp ℝ (h • L))) ≤ 1 := hfine h hh0
    have htel := norm_pi_pow_sub_pow_mulVec_le pi_dist hπ _ _ f₀ hX hY n
    -- one-step Duhamel bound through the weighted algebra
    have hstep : opNorm_pi pi_dist hπ (matrixToLinearMap (exp ℝ (h • L) - exp ℝ (h • (L - D)))) ≤
        h * ε * Real.exp (h * M) := by
      rw [opNorm_pi_eq_pmNorm]
      set A : PiMat V pi_dist hπ := ofMat pi_dist hπ (L - D) with hA
      set B : PiMat V pi_dist hπ := ofMat pi_dist hπ D with hB
      have hAB : A + B = ofMat pi_dist hπ L := by
        show (L - D) + D = L
        rw [sub_add_cancel]
      have hmat : ofMat pi_dist hπ (exp ℝ (h • L) - exp ℝ (h • (L - D))) =
          exp ℝ (h • (A + B)) - exp ℝ (h • A) := by
        rw [hAB]
        show exp ℝ (h • L) - exp ℝ (h • (L - D)) =
          toMat pi_dist hπ (exp ℝ (ofMat pi_dist hπ (h • L))) -
          toMat pi_dist hπ (exp ℝ (ofMat pi_dist hπ (h • (L - D))))
        rw [exp_piMat_eq, exp_piMat_eq]
      rw [hmat]
      have hvh := SGC.Bridge.ValidityHorizon.validity_horizon A B h hh0
      have hBnorm : ‖B‖ = ε := defect_eq_validity_leakage pi_dist hπ L P
      have hAnorm : ‖A‖ = opNorm_pi pi_dist hπ (matrixToLinearMap (L - D)) := by
        rw [pmNorm_def]; rfl
      rw [hBnorm, hAnorm] at hvh
      exact hvh
    calc norm_pi pi_dist ((exp ℝ (h • L) ^ n - exp ℝ (h • (L - D)) ^ n) *ᵥ f₀)
        ≤ (n : ℝ) * opNorm_pi pi_dist hπ
            (matrixToLinearMap (exp ℝ (h • L) - exp ℝ (h • (L - D)))) * norm_pi pi_dist f₀ := htel
      _ ≤ (n : ℝ) * (h * ε * Real.exp (h * M)) * norm_pi pi_dist f₀ := by
          gcongr
      _ = t * ε * Real.exp (t * M / n) * norm_pi pi_dist f₀ := by
          rw [hh]
          field_simp
  -- n → ∞
  have hlim : Tendsto (fun n : ℕ => t * ε * Real.exp (t * M / n) * norm_pi pi_dist f₀) atTop
      (𝓝 (t * ε * Real.exp 0 * norm_pi pi_dist f₀)) := by
    have h1 : Tendsto (fun n : ℕ => t * M / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (t * M)
    exact ((Real.continuous_exp.tendsto 0 |>.comp h1).const_mul _).mul_const _
  rw [Real.exp_zero, mul_one] at hlim
  exact ge_of_tendsto hlim (eventually_atTop.2 ⟨1, fun n hn => key n hn⟩)

/-! ## §3. Discharging the fine-side hypothesis for stochastic generators -/

omit [Nonempty V] in
/-- **Jensen for a stochastic kernel with stationary weight.** If `K` has nonnegative
entries, unit row sums, and `π K = π`, then `‖K f‖_π ≤ ‖f‖_π`. -/
theorem opNorm_pi_le_one_of_stochastic (K : Matrix V V ℝ)
    (hnn : ∀ i j, 0 ≤ K i j) (hrow : ∀ i, ∑ j, K i j = 1) (hstat : pi_dist ᵥ* K = pi_dist) :
    opNorm_pi pi_dist hπ (matrixToLinearMap K) ≤ 1 := by
  apply opNorm_pi_le_of_bound pi_dist hπ _ 1 zero_le_one
  intro f
  rw [one_mul]
  show norm_pi pi_dist (K *ᵥ f) ≤ norm_pi pi_dist f
  unfold norm_pi
  apply Real.sqrt_le_sqrt
  unfold norm_sq_pi inner_pi
  -- pointwise Cauchy–Schwarz: (Σ_j K_ij f_j)² ≤ Σ_j K_ij f_j²
  have hcs : ∀ i, (K *ᵥ f) i * (K *ᵥ f) i ≤ ∑ j, K i j * (f j * f j) := by
    intro i
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j => Real.sqrt (K i j)) (fun j => Real.sqrt (K i j) * f j)
    have e1 : ∀ j, Real.sqrt (K i j) * (Real.sqrt (K i j) * f j) = K i j * f j := by
      intro j; rw [← mul_assoc, Real.mul_self_sqrt (hnn i j)]
    have e2 : ∀ j, Real.sqrt (K i j) ^ 2 = K i j := fun j => Real.sq_sqrt (hnn i j)
    have e3 : ∀ j, (Real.sqrt (K i j) * f j) ^ 2 = K i j * (f j * f j) := by
      intro j; rw [mul_pow, Real.sq_sqrt (hnn i j)]; ring
    simp only [e1, e2, e3, hrow i, one_mul] at h
    have hmv : (K *ᵥ f) i = ∑ j, K i j * f j := by
      simp [Matrix.mulVec, dotProduct]
    rw [hmv, ← sq]
    exact h
  calc ∑ i, pi_dist i * (K *ᵥ f) i * (K *ᵥ f) i
      ≤ ∑ i, pi_dist i * ∑ j, K i j * (f j * f j) := by
        apply Finset.sum_le_sum
        intro i _
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hcs i) (hπ i).le
    _ = ∑ j, (∑ i, pi_dist i * K i j) * (f j * f j) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ j, pi_dist j * f j * f j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have : ∑ i, pi_dist i * K i j = pi_dist j := by
          have := congr_fun hstat j
          simpa [Matrix.vecMul, dotProduct] using this
        rw [this, mul_assoc]

/-- **The heat kernel of a stationary rate generator is a `π`-contraction**:
`‖e^{sL}‖_π ≤ 1` for `s ≥ 0`. Discharges `hfine` in
`trajectory_closure_bound_contractive`. -/
theorem heatKernel_contractive_of_generator (L : Matrix V V ℝ)
    (hL : SGC.InformationGeometry.ContinuousTimeKernel.IsGenerator L)
    (hstat : pi_dist ᵥ* L = 0) (s : ℝ) (hs : 0 ≤ s) :
    opNorm_pi pi_dist hπ (matrixToLinearMap (HeatKernel L s)) ≤ 1 := by
  obtain ⟨hnn, hrow⟩ :=
    SGC.InformationGeometry.ContinuousTimeKernel.exp_smul_isStochastic L hL hs
  have hstat' : pi_dist ᵥ* (s • L) = 0 := by
    rw [Matrix.vecMul_smul, hstat, smul_zero]
  exact opNorm_pi_le_one_of_stochastic pi_dist hπ _ hnn hrow
    (SGC.InformationGeometry.ContinuousTimeKernel.exp_stationary (s • L) hstat')

/-- **Contractive closure bound for stationary generators**: the fine-side hypothesis
discharged. Only the coarse-side contraction along the orbit of `f₀` remains explicit. -/
theorem trajectory_closure_bound_generator (L : Matrix V V ℝ) (P : Partition V)
    (hL : SGC.InformationGeometry.ContinuousTimeKernel.IsGenerator L)
    (hstat : pi_dist ᵥ* L = 0)
    (t : ℝ) (ht : 0 ≤ t) (f₀ : V → ℝ) (hf₀ : f₀ = CoarseProjector P pi_dist hπ f₀)
    (hcoarse : ∀ s : ℝ, 0 ≤ s →
      norm_pi pi_dist (HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) s f₀) ≤
        norm_pi pi_dist f₀) :
    norm_pi pi_dist (HeatKernelMap L t f₀ -
      HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f₀) ≤
    t * opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) * norm_pi pi_dist f₀ :=
  trajectory_closure_bound_contractive pi_dist hπ L P t ht f₀ hf₀
    (fun s hs => heatKernel_contractive_of_generator pi_dist hπ L hL hstat s hs) hcoarse

end SGC.Bridge.ContractiveHorizon
