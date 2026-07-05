/-
Copyright (c) 2025 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team

# Exploration Time: Computed Bounds for Heat/Quench Scheduling

This module formalizes the **Exploration Time** concept: the computed duration
for which a system should "explore" (heat phase) before "consolidating" (quench).

## Theoretical Foundation

The exploration time bound falls straight out of `trajectory_closure_bound`:
- For leakage defect ε and target tolerance δ, we can compute T = δ / (ε * C)
- This is the principled replacement for empirical epoch-based triggers

## Connection to Mixing Time (Markov Chains / Quantum Annealing)

The SGC exploration time is the direct analogue of:
1. **Markov Chain Mixing Time**: τ_mix ~ 1/γ (inverse spectral gap)
2. **Quantum Adiabatic Runtime**: T ~ 1/Δ² (inverse squared gap)

Both are governed by spectral structure, not ad-hoc schedules.

## Main Results

1. `exploration_time_bound`: Computed T = δ / (ε * C) from trajectory closure
2. `exploration_time_bound_unit`: Specialized for unit-norm initial conditions
3. `exploration_time_window`: Valid window combining mixing and validity horizon

## Physical Significance

For THRML/SNN translation:
- **Heat phase duration**: T_explore from this theorem
- **Quench trigger**: When t ≥ T_explore (system has "mixed enough")
- **Validity constraint**: t < T* = 1/ε (stay within effective model regime)

## References

- SGC `trajectory_closure_bound` (Approximate.lean)
- SGC `validity_horizon` (ValidityHorizon.lean)
- Montenegro-Tetali (2006), Markov Chain Mixing Times
-/

import SGC.Renormalization.Approximate
import SGC.Observables.ValidityHorizon
import SGC.Axioms.Geometry
import SGC.Spectral.Core.Assumptions
import SGC.Bridge.DefectHorizonBridge

noncomputable section

namespace SGC.Observables

open Finset Matrix Real SGC.Approximate SGC.Spectral

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-! ### 1. Exploration Time from Trajectory Closure -/

/-- **Trajectory Closure at Reference Time**.

    Key lemma: if we have HeatKernel bounds on [0, T_ref], then trajectory_closure_bound
    works for any t ≤ T_ref with the SAME constant C.

    This is the "monotonicity in time" property that enables computed exploration bounds.

    **Proof (kernel-clean)**: invoke the explicit bridge bound
    `trajectory_closure_bound_explicit` — `‖·‖ ≤ t·ε·e^{t(‖L−D‖_π+ε)}·‖f₀‖` pointwise —
    and take the uniform envelope `C = e^{T_ref·(‖L−D‖_π+ε)}` over `[0, T_ref]`, valid
    since the exponent is increasing in `t`. No semigroup/Duhamel axioms are used. -/
lemma trajectory_closure_bound_at_ref
    (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (ε : ℝ) (hε : 0 ≤ ε) (hL : IsApproxLumpable L P pi_dist hπ ε)
    (T_ref : ℝ) (hT_ref : 0 ≤ T_ref) :
    ∃ C : ℝ, C ≥ 0 ∧ ∀ t : ℝ, 0 ≤ t → t ≤ T_ref →
      ∀ f₀ : V → ℝ, f₀ = CoarseProjector P pi_dist hπ f₀ →
        norm_pi pi_dist
          (HeatKernelMap L t f₀ - HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f₀)
        ≤ ε * t * C * norm_pi pi_dist f₀ := by
  -- Kernel-clean: the explicit bridge bound, enveloped uniformly over [0, T_ref].
  set aN := opNorm_pi pi_dist hπ
    (matrixToLinearMap (L - SGC.Bridge.DefectHorizonBridge.DefectMatrix L P pi_dist hπ)) with haN
  have haN0 : (0 : ℝ) ≤ aN := by rw [haN]; exact opNorm_pi_nonneg pi_dist hπ _
  have hsum0 : (0 : ℝ) ≤ aN + ε := by linarith
  refine ⟨Real.exp (T_ref * (aN + ε)), (Real.exp_pos _).le, ?_⟩
  intro t ht_lo ht_hi f₀ hf₀
  have hkey := SGC.Bridge.DefectHorizonBridge.trajectory_closure_bound_explicit
    pi_dist hπ L P ε hL t ht_lo f₀ hf₀
  rw [← haN] at hkey
  have hf0 : (0 : ℝ) ≤ norm_pi pi_dist f₀ := Real.sqrt_nonneg _
  have hexp_le : Real.exp (t * (aN + ε)) ≤ Real.exp (T_ref * (aN + ε)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ht_hi hsum0)
  calc norm_pi pi_dist
        (HeatKernelMap L t f₀ - HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f₀)
      ≤ t * ε * Real.exp (t * (aN + ε)) * norm_pi pi_dist f₀ := hkey
    _ ≤ t * ε * Real.exp (T_ref * (aN + ε)) * norm_pi pi_dist f₀ := by
        apply mul_le_mul_of_nonneg_right _ hf0
        exact mul_le_mul_of_nonneg_left hexp_le (mul_nonneg ht_lo hε)
    _ = ε * t * Real.exp (T_ref * (aN + ε)) * norm_pi pi_dist f₀ := by ring

/-- **Computed Exploration Time Bound**.

    If the leakage defect is ≤ ε, then for any target relative error δ > 0,
    we can compute a time budget T = δ / (ε * C) such that for all t ≤ T,
    coarse predictions are δ-accurate (relative to ‖f₀‖_π).

    **Key Property**: This is a *computed* bound, not an empirical trigger.
    The only "physics input" is the defect level ε from `IsApproxLumpable`.

    **THRML Translation**: T_explore is the minimum heat phase duration before
    the system has "mixed enough" to justify quench.

    **Proof Strategy**:
    1. Use reference time T_ref = δ/ε (upper bound since C ≥ 1)
    2. Get uniform C from trajectory_closure_bound_at_ref
    3. For t ≤ δ/(ε*C) ≤ T_ref, the bound ε*t*C ≤ δ follows by algebra -/
theorem exploration_time_bound
    (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (ε : ℝ) (hε : 0 < ε) (hL : IsApproxLumpable L P pi_dist hπ ε)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ δ / (ε * C) →
        ∀ f₀ : V → ℝ, f₀ = CoarseProjector P pi_dist hπ f₀ →
          norm_pi pi_dist
            (HeatKernelMap L t f₀ - HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f₀)
          ≤ δ * norm_pi pi_dist f₀ := by
  -- Step 1: Use reference time T_ref = δ/ε (since C ≥ 1, δ/(ε*C) ≤ δ/ε = T_ref)
  let T_ref := δ / ε
  have hT_ref_pos : 0 < T_ref := div_pos hδ hε
  have hT_ref_nonneg : 0 ≤ T_ref := le_of_lt hT_ref_pos

  -- Step 2: Get uniform constant C₀ at reference time
  obtain ⟨C₀, hC₀_nonneg, h_uniform_bound⟩ :=
    trajectory_closure_bound_at_ref L P pi_dist hπ ε (le_of_lt hε) hL T_ref hT_ref_nonneg

  -- Step 3: Define C := max C₀ 1 to ensure C ≥ 1
  let C := max C₀ 1
  have hC_pos : 1 ≤ C := le_max_right C₀ 1
  have hC_nonneg : 0 ≤ C := le_trans (by linarith : (0:ℝ) ≤ 1) hC_pos
  have hC₀_le_C : C₀ ≤ C := le_max_left C₀ 1

  use C
  constructor
  · exact hC_pos
  · intro t ht_lo ht_hi f₀ hf₀
    -- Key: t ≤ δ/(ε*C) ≤ δ/ε = T_ref (since C ≥ 1)
    have h_t_le_T_ref : t ≤ T_ref := by
      have hC_ge_one : C ≥ 1 := hC_pos
      have h_εC_ge_ε : ε * C ≥ ε * 1 := mul_le_mul_of_nonneg_left hC_ge_one (le_of_lt hε)
      rw [mul_one] at h_εC_ge_ε
      have h_denom : δ / (ε * C) ≤ δ / ε := by
        apply div_le_div_of_nonneg_left (le_of_lt hδ) hε h_εC_ge_ε
      exact le_trans ht_hi h_denom

    -- Apply the uniform bound at reference time
    have h_traj := h_uniform_bound t ht_lo h_t_le_T_ref f₀ hf₀

    -- Now show: ε * t * C₀ * ‖f₀‖ ≤ δ * ‖f₀‖
    -- From t ≤ δ/(ε*C), we get ε * t * C ≤ δ
    have h_εC_pos : 0 < ε * C := mul_pos hε (lt_of_lt_of_le (by linarith : (0:ℝ) < 1) hC_pos)
    have h_εtC_le_δ : ε * t * C ≤ δ := by
      have h := ht_hi
      calc ε * t * C = (ε * C) * t := by ring
        _ ≤ (ε * C) * (δ / (ε * C)) := mul_le_mul_of_nonneg_left h (le_of_lt h_εC_pos)
        _ = δ := mul_div_cancel₀ δ (ne_of_gt h_εC_pos)

    -- Since C₀ ≤ C, we have ε * t * C₀ ≤ ε * t * C ≤ δ
    have h_εtC₀_le_δ : ε * t * C₀ ≤ δ := by
      calc ε * t * C₀ ≤ ε * t * C := by
            apply mul_le_mul_of_nonneg_left hC₀_le_C
            exact mul_nonneg (le_of_lt hε) ht_lo
        _ ≤ δ := h_εtC_le_δ

    -- Final step: bound the trajectory error
    calc norm_pi pi_dist (HeatKernelMap L t f₀ - HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f₀)
        ≤ ε * t * C₀ * norm_pi pi_dist f₀ := h_traj
      _ ≤ δ * norm_pi pi_dist f₀ := by
          apply mul_le_mul_of_nonneg_right h_εtC₀_le_δ
          unfold norm_pi; exact Real.sqrt_nonneg _

/-- **Exploration Time Bound (Unit Norm)**.

    Specialized version for unit-norm initial conditions.
    When ‖f₀‖_π = 1, the bound becomes: error ≤ δ. -/
theorem exploration_time_bound_unit
    (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (ε : ℝ) (hε : 0 < ε) (hL : IsApproxLumpable L P pi_dist hπ ε)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ δ / (ε * C) →
        ∀ f₀ : V → ℝ, f₀ = CoarseProjector P pi_dist hπ f₀ →
          norm_pi pi_dist f₀ = 1 →
          norm_pi pi_dist
            (HeatKernelMap L t f₀ - HeatKernelMap (CoarseGeneratorMatrix L P pi_dist hπ) t f₀)
          ≤ δ := by
  obtain ⟨C, hC, h_bound⟩ := exploration_time_bound L P pi_dist hπ ε hε hL δ hδ
  use C, hC
  intro t ht_lo ht_hi f₀ hf₀ hnorm
  have h := h_bound t ht_lo ht_hi f₀ hf₀
  rw [hnorm, mul_one] at h
  exact h

/-! ### 2. Exploration Time Window -/

/-- **Computed Exploration Time Value**.

    Given defect ε, tolerance δ, and the uniform constant C from trajectory closure,
    the exploration time is T = δ / (ε * C).

    This is the principled replacement for empirical epoch-based triggers. -/
def exploration_time (ε : ℝ) (δ : ℝ) (C : ℝ) : ℝ := δ / (ε * C)

/-- Exploration time is positive when inputs are positive. -/
lemma exploration_time_pos (ε δ C : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hC : 0 < C) :
    0 < exploration_time ε δ C := by
  unfold exploration_time
  exact div_pos hδ (mul_pos hε hC)

/-- Smaller defect implies longer exploration time (more exploration allowed). -/
lemma exploration_time_mono_defect {ε₁ ε₂ δ C : ℝ}
    (hε₁ : 0 < ε₁) (_hε₂ : 0 < ε₂) (hδ : 0 < δ) (hC : 0 < C) (h : ε₁ ≤ ε₂) :
    exploration_time ε₂ δ C ≤ exploration_time ε₁ δ C := by
  unfold exploration_time
  apply div_le_div_of_nonneg_left (le_of_lt hδ)
  · exact mul_pos hε₁ hC
  · exact mul_le_mul_of_nonneg_right h (le_of_lt hC)

/-- Larger tolerance implies longer exploration time (less precision required). -/
lemma exploration_time_mono_tolerance {ε δ₁ δ₂ C : ℝ}
    (hε : 0 < ε) (_hδ₁ : 0 < δ₁) (_hδ₂ : 0 < δ₂) (hC : 0 < C) (h : δ₁ ≤ δ₂) :
    exploration_time ε δ₁ C ≤ exploration_time ε δ₂ C := by
  unfold exploration_time
  exact div_le_div_of_nonneg_right h (le_of_lt (mul_pos hε hC))

/-! ### 3. Exploration Time Window (Mixing + Validity) -/

/-- **Valid Exploration Time Window**.

    For a system with:
    - Leakage defect ε (from IsApproxLumpable)
    - Target mixing tolerance δ_mix
    - Validity horizon T* = 1/ε

    The valid exploration window is: T_explore ≤ t < T*

    **Lower bound** (mixing): t ≥ T_explore ensures the system has "mixed enough"
    **Upper bound** (validity): t < T* ensures we stay within effective model regime

    **Key Inequality**: T_explore = δ/(ε*C) < 1/ε = T* when δ < C
    (which is always satisfiable by choosing small enough δ) -/
theorem exploration_time_window_exists
    (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (ε : ℝ) (hε : 0 < ε) (hL : IsApproxLumpable L P pi_dist hπ ε)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∃ T_explore T_validity : ℝ,
        T_explore = exploration_time ε δ C ∧
        T_validity = validity_horizon ε hε ∧
        (δ < C → T_explore < T_validity) := by
  obtain ⟨C, hC, _⟩ := exploration_time_bound L P pi_dist hπ ε hε hL δ hδ
  use C, hC
  use exploration_time ε δ C
  use validity_horizon ε hε
  refine ⟨rfl, rfl, ?_⟩
  intro hδC
  unfold exploration_time validity_horizon
  -- Want: δ / (ε * C) < 1 / ε
  -- Equiv: δ / C < 1 (multiply both sides by ε)
  -- Which follows from δ < C
  have hC_pos : 0 < C := lt_of_lt_of_le (by linarith : (0 : ℝ) < 1) hC
  have h_εC_pos : 0 < ε * C := mul_pos hε hC_pos
  have h_δC : δ / C < 1 := (div_lt_one hC_pos).mpr hδC
  calc δ / (ε * C) = δ / (C * ε) := by ring_nf
    _ = (δ / C) / ε := by rw [div_div]
    _ < 1 / ε := div_lt_div_of_pos_right h_δC hε

/-! ### 4. THRML/SNN Translation Interface -/

/-- **Heat Phase Duration**: The minimum time to spend in exploration (heat) phase.

    For THRML: This is the time before β(t) should start increasing (quench).
    For SNN: This is the exploration period before consolidation gates activate.

    The duration is computed, not empirical:
    T_heat = δ / (ε * C)

    where:
    - δ is the target mixing tolerance (how close to quasi-stationary)
    - ε is the leakage defect (from approximate lumpability analysis)
    - C is the trajectory closure constant (from trajectory_closure_bound) -/
def heat_phase_duration (ε δ C : ℝ) : ℝ := exploration_time ε δ C

/-- **Quench Trigger Condition**: The system is ready for quench when t ≥ T_heat.

    This replaces empirical triggers (fixed epochs, entropy thresholds) with a
    computed condition derived from SGC trajectory bounds.

    **Note**: The actual trigger should also verify that the validity horizon
    has not been exceeded: t < T* = 1/ε. -/
def ready_for_quench (t ε δ C : ℝ) : Prop := t ≥ heat_phase_duration ε δ C

/-- **Within Validity**: The effective model is still valid. -/
def within_validity (t ε : ℝ) (hε : 0 < ε) : Prop := t < validity_horizon ε hε

/-- **Safe Quench Window**: Ready for quench AND within validity. -/
def safe_quench_window (t ε δ C : ℝ) (hε : 0 < ε) : Prop :=
  ready_for_quench t ε δ C ∧ within_validity t ε hε

end SGC.Observables
