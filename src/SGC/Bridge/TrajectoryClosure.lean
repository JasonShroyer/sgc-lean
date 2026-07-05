/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Bridge.DefectHorizonBridge

/-!
# Trajectory Closure, Kernel-Clean (Axiom Retirement, 2026-07-05)

This module re-proves — with **zero axioms** beyond `propext`, `Classical.choice`,
`Quot.sound` — the trajectory-closure theorems that previously lived in
`Renormalization/Approximate.lean` on top of three trusted axioms:

* `HeatKernel_opNorm_bound`          (uniform semigroup bound, existential `B`)
* `Duhamel_integral_bound`           (vertical Duhamel/MVT bound)
* `Horizontal_Duhamel_integral_bound` (horizontal Duhamel/MVT bound)

All three axioms are **deleted** as of this module's introduction. The engine is
`SGC.Bridge.DefectHorizonBridge` (2026-06-11), whose explicit bounds
(`trajectory_closure_bound_explicit`, `vertical_closure_bound_explicit`,
`HeatKernel_opNorm_bound_proved`) are strictly stronger than the retired axioms:
each existential constant is realized by the computable witness
`C := e^{t(‖L−D‖_π+ε)}` (resp. `B := e^{T‖L‖_π}`).

## Namespace note

Declarations here live in `namespace SGC.Approximate` **deliberately**: the
canonical names (`SGC.Approximate.trajectory_closure_bound`, …) are stable across
the move; only their home file and their proofs changed. Statements are verbatim
(up to the added `[Nonempty V]` instance required by the weighted operator
algebra `PiMat`).

## Contents

* `trajectory_norm_bound_uniform` — uniform trajectory bound, now via
  `HeatKernel_opNorm_bound_proved`.
* `trajectory_closure_bound` — the flagship O(ε·t) horizontal bound, ∃C form.
* `vertical_error_bound` — the O(ε·t) vertical bound, ∃C form.
* `coarseGen_mul_proj`, `proj_commutes_heatKernel_coarseGen`,
  `proj_swap_heatKernelMap_coarseGen` — the coarse heat kernel commutes with `Π`
  (because `ΠL̄ = L̄ = L̄Π`), transported through the exponential on `PiMat`.
* `PropagatorDiff_eq_proj_trajectory_diff` — **previously an axiom, now a
  theorem** (the fourth retirement): the propagator difference is the projected
  trajectory difference.
* `propagator_approximation_bound` — operator-norm O(ε·t) bound.
* `spectral_stability_reversible` — eigenvalue tracking (still consumes the
  `Weyl_inequality_pi` axiom; that retirement is a separate campaign).
* `NCD_uniform_error_bound` — uniform-in-time O(ε/γ) bound (still consumes the
  two NCD axioms; separate campaign).
-/

noncomputable section

namespace SGC.Approximate

open Finset Matrix Real NormedSpace
open SGC.Bridge.DefectHorizonBridge

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-! ### 1. Uniform semigroup bound (replaces the `HeatKernel_opNorm_bound` axiom) -/

/-- The norm of the trajectory is bounded uniformly on [0, T]:
    ‖e^{sL} f₀‖ ≤ B · ‖f₀‖ for all s ∈ [0, T]. Kernel-clean via
    `HeatKernel_opNorm_bound_proved` (B := e^{T‖L‖_π}). -/
lemma trajectory_norm_bound_uniform (L : Matrix V V ℝ) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (f₀ : V → ℝ) (T : ℝ) (hT : 0 ≤ T) :
    ∃ B : ℝ, B ≥ 1 ∧ ∀ s, 0 ≤ s → s ≤ T → norm_pi pi_dist (HeatKernelMap L s f₀) ≤ B * norm_pi pi_dist f₀ := by
  obtain ⟨B, hB_pos, hB⟩ := HeatKernel_opNorm_bound_proved pi_dist hπ L T hT
  use B, hB_pos
  intro s hs_lo hs_hi
  have hB_s := hB s hs_lo hs_hi
  have h := opNorm_pi_bound pi_dist hπ (matrixToLinearMap (HeatKernel L s)) f₀
  calc norm_pi pi_dist (HeatKernelMap L s f₀)
      = norm_pi pi_dist (matrixToLinearMap (HeatKernel L s) f₀) := rfl
    _ ≤ opNorm_pi pi_dist hπ (matrixToLinearMap (HeatKernel L s)) * norm_pi pi_dist f₀ := h
    _ ≤ B * norm_pi pi_dist f₀ := by
        apply mul_le_mul_of_nonneg_right hB_s
        unfold norm_pi; exact Real.sqrt_nonneg _

/-! ### 2. The flagship horizontal bound (replaces `Horizontal_Duhamel_integral_bound`) -/

/-- **Trajectory Closure Bound** (Uniform Form, kernel-clean).

    If L is approximately lumpable with leakage defect ε, then for **any** initial
    condition f₀ that is block-constant (f₀ = Π f₀), the trajectory e^{tL} f₀
    stays close to the **coarse trajectory** e^{tL̄} f₀:

    ‖e^{tL} f₀ - e^{tL̄} f₀‖_π ≤ ε * t * C * ‖f₀‖_π

    The constant is explicit and **independent of f₀**:
    `C := e^{t(‖L−D‖_π+ε)}`, realized by
    `SGC.Bridge.DefectHorizonBridge.trajectory_closure_bound_explicit`.
    No Duhamel/MVT axioms are consumed. -/
theorem trajectory_closure_bound
    (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (ε : ℝ) (hε : 0 ≤ ε) (hL : IsApproxLumpable L P pi_dist hπ ε)
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ C : ℝ, C ≥ 0 ∧ ∀ (f₀ : V → ℝ), f₀ = CoarseProjector P pi_dist hπ f₀ →
    norm_pi pi_dist (HeatKernelMap L t f₀ - HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f₀) ≤
    ε * t * C * norm_pi pi_dist f₀ := by
  refine ⟨Real.exp (t * (opNorm_pi pi_dist hπ
      (matrixToLinearMap (L - DefectMatrix L P pi_dist hπ)) + ε)),
    (Real.exp_pos _).le, ?_⟩
  intro f₀ hf₀
  have hkey := trajectory_closure_bound_explicit pi_dist hπ L P ε hL t ht f₀ hf₀
  calc norm_pi pi_dist (HeatKernelMap L t f₀ -
          HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f₀)
      ≤ t * ε * Real.exp (t * (opNorm_pi pi_dist hπ
          (matrixToLinearMap (L - DefectMatrix L P pi_dist hπ)) + ε)) *
        norm_pi pi_dist f₀ := hkey
    _ = ε * t * Real.exp (t * (opNorm_pi pi_dist hπ
          (matrixToLinearMap (L - DefectMatrix L P pi_dist hπ)) + ε)) *
        norm_pi pi_dist f₀ := by ring

/-! ### 3. The vertical bound (replaces `Duhamel_integral_bound`) -/

/-- **Vertical Error Bound** (kernel-clean): how far e^{tL} f₀ leaks out of the
    coarse subspace,

    ‖(I - Π) e^{tL} f₀‖_π ≤ ε * t * C * ‖f₀‖_π,

    with the explicit constant `C := e^{t(‖L−D‖_π+ε)}` from
    `SGC.Bridge.DefectHorizonBridge.vertical_closure_bound_explicit`. -/
theorem vertical_error_bound
    (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (ε : ℝ) (hε : 0 ≤ ε) (hL : IsApproxLumpable L P pi_dist hπ ε)
    (t : ℝ) (ht : 0 ≤ t)
    (f₀ : V → ℝ) (hf₀ : f₀ = CoarseProjector P pi_dist hπ f₀) :
    ∃ C : ℝ, C ≥ 0 ∧
    norm_pi pi_dist (HeatKernelMap L t f₀ - CoarseProjector P pi_dist hπ (HeatKernelMap L t f₀)) ≤
    ε * t * C * norm_pi pi_dist f₀ := by
  refine ⟨Real.exp (t * (opNorm_pi pi_dist hπ
      (matrixToLinearMap (L - DefectMatrix L P pi_dist hπ)) + ε)),
    (Real.exp_pos _).le, ?_⟩
  have hkey := vertical_closure_bound_explicit pi_dist hπ L P ε hL t ht f₀ hf₀
  calc norm_pi pi_dist (HeatKernelMap L t f₀ -
          CoarseProjector P pi_dist hπ (HeatKernelMap L t f₀))
      ≤ t * ε * Real.exp (t * (opNorm_pi pi_dist hπ
          (matrixToLinearMap (L - DefectMatrix L P pi_dist hπ)) + ε)) *
        norm_pi pi_dist f₀ := hkey
    _ = ε * t * Real.exp (t * (opNorm_pi pi_dist hπ
          (matrixToLinearMap (L - DefectMatrix L P pi_dist hπ)) + ε)) *
        norm_pi pi_dist f₀ := by ring

/-! ### 4. `Π` commutes with the coarse heat kernel

`ΠL̄ = L̄` (left absorption, proved in the bridge) and `L̄Π = L̄` (right absorption,
below), so `Π` commutes with `L̄`, hence with `e^{tL̄}` — transported through the
Banach-algebra exponential on `PiMat` via `Commute.exp_right` and `exp_piMat_eq`. -/

/-- Right absorption: `L̄ · Π = L̄`. The coarse generator ingests the projector. -/
lemma coarseGen_mul_proj (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) :
    CoarseGeneratorMatrix L P pi_dist hπ * CoarseProjectorMatrix P pi_dist hπ =
    CoarseGeneratorMatrix L P pi_dist hπ := by
  have hidem : CoarseProjectorMatrix P pi_dist hπ * CoarseProjectorMatrix P pi_dist hπ =
      CoarseProjectorMatrix P pi_dist hπ := CoarseProjectorMatrix_idempotent P pi_dist hπ
  show CoarseProjectorMatrix P pi_dist hπ * L * CoarseProjectorMatrix P pi_dist hπ *
      CoarseProjectorMatrix P pi_dist hπ =
      CoarseProjectorMatrix P pi_dist hπ * L * CoarseProjectorMatrix P pi_dist hπ
  rw [mul_assoc (CoarseProjectorMatrix P pi_dist hπ * L), hidem]

/-- `Π` commutes with the coarse heat kernel: `Π e^{tL̄} = e^{tL̄} Π` (as matrices). -/
lemma proj_commutes_heatKernel_coarseGen (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (t : ℝ) :
    CoarseProjectorMatrix P pi_dist hπ * HeatKernel (CoarseGeneratorMatrix L P pi_dist hπ) t =
    HeatKernel (CoarseGeneratorMatrix L P pi_dist hπ) t * CoarseProjectorMatrix P pi_dist hπ := by
  have hcomm : Commute (ofMat pi_dist hπ (CoarseProjectorMatrix P pi_dist hπ))
      (ofMat pi_dist hπ (t • CoarseGeneratorMatrix L P pi_dist hπ)) := by
    show CoarseProjectorMatrix P pi_dist hπ * (t • CoarseGeneratorMatrix L P pi_dist hπ) =
        (t • CoarseGeneratorMatrix L P pi_dist hπ) * CoarseProjectorMatrix P pi_dist hπ
    rw [mul_smul_comm, smul_mul_assoc, proj_mul_coarseGen pi_dist hπ L P,
        coarseGen_mul_proj L P pi_dist hπ]
  have hexp := (hcomm.exp_right ℝ).eq
  have hstep : CoarseProjectorMatrix P pi_dist hπ *
      toMat pi_dist hπ (exp ℝ (ofMat pi_dist hπ (t • CoarseGeneratorMatrix L P pi_dist hπ))) =
      toMat pi_dist hπ (exp ℝ (ofMat pi_dist hπ (t • CoarseGeneratorMatrix L P pi_dist hπ))) *
      CoarseProjectorMatrix P pi_dist hπ := hexp
  rw [exp_piMat_eq] at hstep
  show CoarseProjectorMatrix P pi_dist hπ * exp ℝ (t • CoarseGeneratorMatrix L P pi_dist hπ) =
      exp ℝ (t • CoarseGeneratorMatrix L P pi_dist hπ) * CoarseProjectorMatrix P pi_dist hπ
  exact hstep

/-- Pointwise form: `Π (e^{tL̄} g) = e^{tL̄} (Π g)` for every `g`. -/
lemma proj_swap_heatKernelMap_coarseGen (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (t : ℝ) (g : V → ℝ) :
    CoarseProjector P pi_dist hπ (HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t g) =
    HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t (CoarseProjector P pi_dist hπ g) := by
  rw [← CoarseProjectorMatrix_mulVec P pi_dist hπ, ← CoarseProjectorMatrix_mulVec P pi_dist hπ]
  show CoarseProjectorMatrix P pi_dist hπ *ᵥ
      (HeatKernel (CoarseGeneratorMatrix L P pi_dist hπ) t *ᵥ g) =
      HeatKernel (CoarseGeneratorMatrix L P pi_dist hπ) t *ᵥ
      (CoarseProjectorMatrix P pi_dist hπ *ᵥ g)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      proj_commutes_heatKernel_coarseGen L P pi_dist hπ t]

/-! ### 5. The propagator identity — previously an axiom, now a theorem -/

/-- **Propagator difference = projected trajectory difference** (RETIRED AXIOM,
    now kernel-proved): applying `PropagatorDiff = Π e^{tL} Π − Π e^{tL̄}` to `f`
    equals the coarse projection of the trajectory difference started at `Π f`:

    `PropagatorDiff f = Π(e^{tL} (Π f) - e^{tL̄} (Π f))`.

    The only nontrivial ingredient is `Π e^{tL̄} f = e^{tL̄} Π f`
    (`proj_swap_heatKernelMap_coarseGen`): the vertical part of `f` passes through
    `e^{tL̄}` untouched and is then annihilated by `Π`. -/
theorem PropagatorDiff_eq_proj_trajectory_diff (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (t : ℝ) (f : V → ℝ) :
    PropagatorDiff L P pi_dist hπ t f =
    CoarseProjector P pi_dist hπ (HeatKernelMap L t (CoarseProjector P pi_dist hπ f) -
                                   HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t (CoarseProjector P pi_dist hπ f)) := by
  have hidem : CoarseProjector P pi_dist hπ (CoarseProjector P pi_dist hπ f) =
      CoarseProjector P pi_dist hπ f := by
    have h := congrFun (congrArg DFunLike.coe (CoarseProjector_idempotent P pi_dist hπ)) f
    simpa only [LinearMap.comp_apply] using h
  show CoarseProjector P pi_dist hπ (HeatKernelMap L t (CoarseProjector P pi_dist hπ f)) -
      CoarseProjector P pi_dist hπ
        (HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f) =
      CoarseProjector P pi_dist hπ (HeatKernelMap L t (CoarseProjector P pi_dist hπ f) -
        HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t (CoarseProjector P pi_dist hπ f))
  rw [map_sub, proj_swap_heatKernelMap_coarseGen L P pi_dist hπ t f,
      proj_swap_heatKernelMap_coarseGen L P pi_dist hπ t (CoarseProjector P pi_dist hπ f),
      hidem]

/-! ### 6. Operator-norm and spectral corollaries (moved, proofs unchanged) -/

/-- **Propagator Approximation Bound**: The operator norm of the propagator difference
    is bounded by O(ε·t):

    ‖Π e^{tL} Π - Π e^{t L̄}‖_op ≤ ε · t · C.

    Proof unchanged from `Approximate.lean`; every ingredient is now kernel-clean. -/
theorem propagator_approximation_bound
    (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (ε : ℝ) (hε : 0 ≤ ε) (hL : IsApproxLumpable L P pi_dist hπ ε)
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ C : ℝ, C ≥ 0 ∧
    opNorm_pi pi_dist hπ (PropagatorDiff L P pi_dist hπ t) ≤ ε * t * C := by
  obtain ⟨C_traj, hC_traj_pos, h_traj_uniform⟩ := trajectory_closure_bound L P pi_dist hπ ε hε hL t ht
  use C_traj
  constructor
  · exact hC_traj_pos
  · apply opNorm_pi_le_of_bound
    · exact mul_nonneg (mul_nonneg hε ht) hC_traj_pos
    · intro f
      let g := CoarseProjector P pi_dist hπ f
      have hg_coarse : g = CoarseProjector P pi_dist hπ g := by
        have h_idem := CoarseProjector_idempotent P pi_dist hπ
        have h := congrFun (congrArg DFunLike.coe h_idem) f
        simp only [LinearMap.comp_apply] at h
        exact h.symm
      have h_traj := h_traj_uniform g hg_coarse
      have h_contr_f := CoarseProjector_contractive P pi_dist hπ f
      have h_contr_diff := CoarseProjector_contractive P pi_dist hπ
        (HeatKernelMap L t g - HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t g)
      rw [PropagatorDiff_eq_proj_trajectory_diff]
      calc norm_pi pi_dist (CoarseProjector P pi_dist hπ
              (HeatKernelMap L t g - HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t g))
          ≤ norm_pi pi_dist (HeatKernelMap L t g - HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t g) :=
            h_contr_diff
        _ ≤ ε * t * C_traj * norm_pi pi_dist g := h_traj
        _ ≤ ε * t * C_traj * norm_pi pi_dist f := by
            apply mul_le_mul_of_nonneg_left h_contr_f
            exact mul_nonneg (mul_nonneg hε ht) hC_traj_pos

/-- **Spectral Stability Theorem** (REVERSIBLE SYSTEMS ONLY): the eigenvalues of the
    effective propagator track the eigenvalues of the coarse propagator,

    |λ_k(Π e^{tL} Π) - λ_k(Π e^{t L̄})| ≤ ε · t · C.

    Still consumes the `Weyl_inequality_pi` axiom (valid for self-adjoint operators
    only); its retirement is a separate campaign. Proof unchanged. -/
theorem spectral_stability_reversible
    (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (ε : ℝ) (hε : 0 ≤ ε) (hL : IsApproxLumpable L P pi_dist hπ ε)
    (t : ℝ) (ht : 0 ≤ t) (k : ℕ)
    (hEffSA : IsSelfAdjoint_pi (EffectivePropagator L P pi_dist hπ t) pi_dist)
    (hCoarseSA : IsSelfAdjoint_pi (CoarsePropagatorLifted L P pi_dist hπ t) pi_dist) :
    ∃ C : ℝ, ∃ eigenvalue_k : ((V → ℝ) →ₗ[ℝ] (V → ℝ)) → ℝ,
    C ≥ 0 ∧
    |eigenvalue_k (EffectivePropagator L P pi_dist hπ t) -
     eigenvalue_k (CoarsePropagatorLifted L P pi_dist hπ t)| ≤ ε * t * C := by
  obtain ⟨C_prop, hC_prop, h_prop_bound⟩ := propagator_approximation_bound L P pi_dist hπ ε hε hL t ht
  obtain ⟨ev_k, h_weyl⟩ := Weyl_inequality_pi
    (EffectivePropagator L P pi_dist hπ t)
    (CoarsePropagatorLifted L P pi_dist hπ t)
    pi_dist hπ k hEffSA hCoarseSA
  use C_prop, ev_k
  constructor
  · exact hC_prop
  · calc |ev_k (EffectivePropagator L P pi_dist hπ t) -
          ev_k (CoarsePropagatorLifted L P pi_dist hπ t)|
        ≤ opNorm_pi pi_dist hπ (EffectivePropagator L P pi_dist hπ t -
            CoarsePropagatorLifted L P pi_dist hπ t) := h_weyl
      _ = opNorm_pi pi_dist hπ (PropagatorDiff L P pi_dist hπ t) := rfl
      _ ≤ ε * t * C_prop := h_prop_bound

/-! ### 7. NCD uniform bound (moved; still consumes the two NCD axioms) -/

/-- **Main NCD Theorem**: Uniform-in-time trajectory error bound for NCD systems,
    O(ε/γ) regardless of t. Proof unchanged from `Approximate.lean`; the
    `trajectory_norm_bound_uniform` ingredient is now kernel-clean, while
    `NCD_defect_split` / `NCD_integral_bound` remain axioms (separate campaign). -/
theorem NCD_uniform_error_bound
    (L L_fast L_slow : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (ε γ : ℝ) (hNCD : IsNCD L L_fast L_slow P pi_dist hπ ε γ)
    (t : ℝ) (ht : 0 ≤ t)
    (f₀ : V → ℝ) (hf₀ : f₀ = CoarseProjector P pi_dist hπ f₀) :
    ∃ C : ℝ, C ≥ 0 ∧
    norm_pi pi_dist (HeatKernelMap L t f₀ - CoarseProjector P pi_dist hπ (HeatKernelMap L t f₀)) ≤
    (ε / γ) * C * norm_pi pi_dist f₀ := by
  have hε := hNCD.hε
  have hγ := hNCD.hγ
  obtain ⟨K, hK_pos, hK_bound⟩ := NCD_slow_defect_bound L_slow P pi_dist hπ
  obtain ⟨B_traj, hB_traj_pos, hB_traj_bound⟩ := trajectory_norm_bound_uniform L pi_dist hπ f₀ t ht
  use K * B_traj
  have hB_traj_nonneg : 0 ≤ B_traj := le_trans (by linarith : (0 : ℝ) ≤ 1) hB_traj_pos
  constructor
  · exact mul_nonneg hK_pos hB_traj_nonneg
  · by_cases ht_zero : t = 0
    · subst ht_zero
      rw [norm_vertical_defect_zero L P pi_dist hπ f₀ hf₀]
      have h1 : 0 ≤ ε / γ := div_nonneg hε (le_of_lt hγ)
      have h2 : 0 ≤ norm_pi pi_dist f₀ := by unfold norm_pi; exact Real.sqrt_nonneg _
      exact mul_nonneg (mul_nonneg h1 (mul_nonneg hK_pos hB_traj_nonneg)) h2
    · have ht_pos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht_zero)
      have h_split := NCD_defect_split L L_fast L_slow P pi_dist hπ ε γ hNCD
      let M := ε * K * B_traj
      have hM_pos : 0 ≤ M := mul_nonneg (mul_nonneg hε hK_pos) hB_traj_nonneg
      have h_forcing_bound : ∀ s, 0 ≤ s → s ≤ t →
          norm_pi pi_dist (DefectOperator L P pi_dist hπ (CoarseProjector P pi_dist hπ (HeatKernelMap L s f₀))) ≤
          M * norm_pi pi_dist f₀ := by
        intro s hs_lo hs_hi
        have h_apply : DefectOperator L P pi_dist hπ (CoarseProjector P pi_dist hπ (HeatKernelMap L s f₀)) =
            ε • DefectOperator L_slow P pi_dist hπ (CoarseProjector P pi_dist hπ (HeatKernelMap L s f₀)) := by
          rw [h_split]; rfl
        rw [h_apply]
        rw [norm_pi_smul pi_dist hε]
        have h_bound := opNorm_pi_bound pi_dist hπ (DefectOperator L_slow P pi_dist hπ)
          (CoarseProjector P pi_dist hπ (HeatKernelMap L s f₀))
        have h_contr := CoarseProjector_contractive P pi_dist hπ (HeatKernelMap L s f₀)
        have h_traj := hB_traj_bound s hs_lo hs_hi
        calc ε * norm_pi pi_dist (DefectOperator L_slow P pi_dist hπ (CoarseProjector P pi_dist hπ (HeatKernelMap L s f₀)))
            ≤ ε * (opNorm_pi pi_dist hπ (DefectOperator L_slow P pi_dist hπ) *
              norm_pi pi_dist (CoarseProjector P pi_dist hπ (HeatKernelMap L s f₀))) := by
                apply mul_le_mul_of_nonneg_left h_bound hε
          _ ≤ ε * (K * norm_pi pi_dist (CoarseProjector P pi_dist hπ (HeatKernelMap L s f₀))) := by
                apply mul_le_mul_of_nonneg_left _ hε
                apply mul_le_mul_of_nonneg_right hK_bound
                unfold norm_pi; exact Real.sqrt_nonneg _
          _ ≤ ε * (K * norm_pi pi_dist (HeatKernelMap L s f₀)) := by
                apply mul_le_mul_of_nonneg_left _ hε
                apply mul_le_mul_of_nonneg_left h_contr hK_pos
          _ ≤ ε * (K * (B_traj * norm_pi pi_dist f₀)) := by
                apply mul_le_mul_of_nonneg_left _ hε
                apply mul_le_mul_of_nonneg_left h_traj hK_pos
          _ = ε * K * B_traj * norm_pi pi_dist f₀ := by ring
      have h_ncd := NCD_integral_bound L L_fast L_slow P pi_dist hπ ε γ hNCD t ht f₀ hf₀
        M hM_pos h_forcing_bound
      have h_eq : M / γ * norm_pi pi_dist f₀ = ε / γ * (K * B_traj) * norm_pi pi_dist f₀ := by
        simp only [M]; ring
      linarith [h_ncd, h_eq.ge]

end SGC.Approximate
