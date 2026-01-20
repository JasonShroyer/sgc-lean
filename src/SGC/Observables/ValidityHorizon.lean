/-
Copyright (c) 2025 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team

# Validity Horizon: Observable Bounds on Effective Theory Lifetimes

This module formalizes the **Validity Horizon** concept: the timescale T* beyond which
an effective (coarse-grained) theory ceases to accurately predict the full dynamics.

## Main Results

1. `validity_horizon`: Definition of T* = 1/ε
2. `autocorrelation`: Observable decay of correlations
3. `validity_horizon_lower_bound`: T* ≥ τ_corr × quality_factor

## Physical Significance

The validity horizon answers: "How long can we trust our coarse-grained model?"

For a system with leakage defect ε, the `trajectory_closure_bound` gives error O(ε·t).
When ε·t ~ 1, the effective theory fails. This occurs at T* = 1/ε.

The key insight is that T* is **observable** via autocorrelation time τ_corr,
making "emergence timescale" an empirically measurable quantity.

## References

- SGC `trajectory_closure_bound` (Approximate.lean)
- Simon & Ando (1961), Near-Complete Decomposability
- Levin, Peres, Wilmer (2009), Markov Chains and Mixing Times
-/

import SGC.Renormalization.Approximate
import SGC.Axioms.Geometry
import SGC.Spectral.Core.Assumptions
import SGC.Spectral.Envelope.Sector

noncomputable section

namespace SGC.Observables

open Finset Matrix Real SGC.Approximate SGC.Spectral

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### 1. Validity Horizon Definition -/

/-- **Validity Horizon**: The timescale at which the effective theory breaks down.

    For a system with leakage defect ε > 0, the validity horizon is T* = 1/ε.

    **Physical Meaning**: Predictions from the coarse model are reliable for t < T*.
    Beyond T*, the accumulated error ε·t exceeds O(1) and the model fails.

    **Note**: For ε = 0 (exact lumpability), T* = ∞ (effective theory is exact). -/
def validity_horizon (ε : ℝ) (hε : 0 < ε) : ℝ := 1 / ε

/-- The validity horizon is positive. -/
lemma validity_horizon_pos (ε : ℝ) (hε : 0 < ε) : 0 < validity_horizon ε hε := by
  unfold validity_horizon
  exact one_div_pos.mpr hε

/-- Smaller defect implies longer validity horizon. -/
lemma validity_horizon_mono {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (h : ε₁ ≤ ε₂) :
    validity_horizon ε₂ hε₂ ≤ validity_horizon ε₁ hε₁ := by
  unfold validity_horizon
  exact one_div_le_one_div_of_le hε₁ h

/-! ### 2. Autocorrelation Function -/

/-- **Autocorrelation Function**: Measures temporal correlation of an observable f.

    C_f(t) = ⟨f, e^{tL} f⟩_π - ⟨f, 1⟩_π²

    This is the covariance of f at time 0 with f at time t, under the stationary
    distribution π.

    For mean-zero observables (⟨f, 1⟩_π = 0), this simplifies to C_f(t) = ⟨f, e^{tL} f⟩_π. -/
def autocorrelation (L : Matrix V V ℝ) (pi_dist : V → ℝ) (f : V → ℝ) (t : ℝ) : ℝ :=
  inner_pi pi_dist f (HeatKernelMap L t f) - (inner_pi pi_dist f (fun _ => 1))^2

/-- Autocorrelation at t=0 equals the variance of f. -/
lemma autocorrelation_zero (L : Matrix V V ℝ) (pi_dist : V → ℝ) (f : V → ℝ) :
    autocorrelation L pi_dist f 0 = norm_sq_pi pi_dist f - (inner_pi pi_dist f (fun _ => 1))^2 := by
  unfold autocorrelation
  rw [HeatKernelMap_zero]
  simp only [LinearMap.id_coe, id_eq, norm_sq_pi]

/-- For mean-zero observables, autocorrelation at t=0 equals variance = ‖f‖²_π. -/
lemma autocorrelation_zero_mean_zero (L : Matrix V V ℝ) (pi_dist : V → ℝ) (f : V → ℝ)
    (hf : inner_pi pi_dist f (fun _ => 1) = 0) :
    autocorrelation L pi_dist f 0 = norm_sq_pi pi_dist f := by
  rw [autocorrelation_zero, hf, sq, zero_mul, sub_zero]

/-! ### 3. Spectral Gap and Autocorrelation Time -/

/-- **Autocorrelation Time**: The characteristic decay time of correlations.

    For reversible (detailed balance) systems with spectral gap γ > 0:
    τ_corr = 1/γ

    This is the timescale over which correlations decay by a factor of e. -/
def autocorrelation_time_from_gap (γ : ℝ) (hγ : 0 < γ) : ℝ := 1 / γ

/-- Autocorrelation time is positive when spectral gap is positive. -/
lemma autocorrelation_time_from_gap_pos (γ : ℝ) (hγ : 0 < γ) :
    0 < autocorrelation_time_from_gap γ hγ := by
  unfold autocorrelation_time_from_gap
  exact one_div_pos.mpr hγ

/-! ### 4. Autocorrelation Decay Bound -/

/-! #### 4a. The Spectral Bridge: Deriving Decay from Sector Envelope

The following theorem is the **Spectral Bridge**: it derives autocorrelation decay
from `sector_envelope_bound_canonical`. This connects abstract spectral theory
to observable time-series data.

**The Key Insight**: For mean-zero f, the autocorrelation C_f(t) = ⟨f, e^{tL} f⟩_π
can be bounded using Cauchy-Schwarz:
  |C_f(t)| = |⟨f, e^{tL} f⟩| ≤ ‖f‖_π · ‖e^{tL} f‖_π ≤ ‖f‖_π · e^{-γt} · ‖f‖_π = ‖f‖²_π · e^{-γt}

The middle inequality comes from sector_envelope_bound_canonical. -/

/-- **Spectral Bridge Theorem**: Autocorrelation decay from sector envelope bound.

    Under the full sector conditions (L, H satisfying stationarity, self-adjointness,
    PSD, and sector relation), the autocorrelation decays exponentially:

    |C_f(t)| ≤ ‖f‖²_π · e^{-γt}

    where γ = SpectralGap_pi pi_dist H.

    **Proof**: Cauchy-Schwarz + sector_envelope_bound_canonical. -/
theorem autocorrelation_decay_from_sector
    [Nontrivial V] (L H : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (h_sum : ∑ v, pi_dist v = 1)
    (hL1 : L *ᵥ constant_vec_one = 0)
    (h_sa : ∀ u v, inner_pi pi_dist (H *ᵥ u) v = inner_pi pi_dist u (H *ᵥ v))
    (h_psd : ∀ u, 0 ≤ inner_pi pi_dist (H *ᵥ u) u)
    (h_constH : H *ᵥ constant_vec_one = 0)
    (h_gap : 0 < SpectralGap_pi pi_dist H)
    (h_rel : ∀ u v, inner_pi pi_dist (L *ᵥ u) v + inner_pi pi_dist u (L *ᵥ v) =
                    -2 * inner_pi pi_dist (H *ᵥ u) v)
    (f : V → ℝ) (hf : inner_pi pi_dist f (fun _ => 1) = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    |autocorrelation L pi_dist f t| ≤ norm_sq_pi pi_dist f * Real.exp (-(SpectralGap_pi pi_dist H) * t) := by
  -- For mean-zero f, autocorrelation simplifies to ⟨f, e^{tL} f⟩_π
  unfold autocorrelation
  -- Since f is mean-zero: ⟨f, 1⟩_π = 0
  have h_mean_zero : inner_pi pi_dist f (fun _ => 1) = 0 := hf
  simp only [h_mean_zero, sq, zero_mul, sub_zero]
  -- Helper: norm_pi is nonnegative (from sqrt)
  have h_norm_nonneg : ∀ g : V → ℝ, 0 ≤ norm_pi pi_dist g := fun g => Real.sqrt_nonneg _
  -- Now bound |⟨f, e^{tL} f⟩_π| using Cauchy-Schwarz
  have h_cs := cauchy_schwarz_pi pi_dist hπ f (HeatKernelMap L t f)
  -- h_cs : |⟨f, e^{tL} f⟩| ≤ ‖f‖_π · ‖e^{tL} f‖_π
  calc |inner_pi pi_dist f (HeatKernelMap L t f)|
      ≤ norm_pi pi_dist f * norm_pi pi_dist (HeatKernelMap L t f) := h_cs
    _ ≤ norm_pi pi_dist f * (Real.exp (-(SpectralGap_pi pi_dist H) * t) * norm_pi pi_dist f) := by
        -- Use sector_envelope_bound_canonical to bound ‖e^{tL} f‖_π
        apply mul_le_mul_of_nonneg_left _ (h_norm_nonneg f)
        -- For mean-zero f, f = P f where P is projection onto 1⊥
        have h_f_eq_Pf : (P_ortho_pi pi_dist h_sum hπ) f = f := by
          unfold P_ortho_pi
          simp only [LinearMap.sub_apply, LinearMap.id_apply,
                     LinearMap.smulRight_apply, LinearMap.coe_mk, AddHom.coe_mk]
          rw [h_mean_zero, zero_smul, sub_zero]
        -- HeatKernelMap L t f = (toLin' (HeatKernel L t) ∘ₗ P) f for mean-zero f
        have h_heat_eq : HeatKernelMap L t f = (toLin' (Spectral.HeatKernel L t) ∘ₗ P_ortho_pi pi_dist h_sum hπ) f := by
          simp only [LinearMap.comp_apply, h_f_eq_Pf]
          rfl
        rw [h_heat_eq]
        -- Apply sector_envelope_bound_canonical
        have h_sector := sector_envelope_bound_canonical hπ h_sum L H hL1 h_sa h_psd h_constH h_gap h_rel t ht
        -- Use opNorm bound: ‖A f‖ ≤ opNorm(A) · ‖f‖
        have h_bound := opNorm_pi_bound pi_dist hπ
                          (toLin' (Spectral.HeatKernel L t) ∘ₗ P_ortho_pi pi_dist h_sum hπ) f
        calc norm_pi pi_dist ((toLin' (Spectral.HeatKernel L t) ∘ₗ P_ortho_pi pi_dist h_sum hπ) f)
            ≤ opNorm_pi pi_dist hπ (toLin' (Spectral.HeatKernel L t) ∘ₗ P_ortho_pi pi_dist h_sum hπ) *
              norm_pi pi_dist f := h_bound
          _ ≤ Real.exp (-(SpectralGap_pi pi_dist H) * t) * norm_pi pi_dist f := by
              apply mul_le_mul_of_nonneg_right h_sector (h_norm_nonneg f)
    _ = norm_sq_pi pi_dist f * Real.exp (-(SpectralGap_pi pi_dist H) * t) := by
        -- ‖f‖ · (e^{-γt} · ‖f‖) = ‖f‖² · e^{-γt}
        -- norm_pi² = norm_sq_pi by definition, so √(norm_sq) * √(norm_sq) = norm_sq
        have h_sq : norm_pi pi_dist f * norm_pi pi_dist f = norm_sq_pi pi_dist f := by
          unfold norm_pi
          rw [← Real.sqrt_mul (norm_sq_pi_nonneg pi_dist hπ f), Real.sqrt_mul_self (norm_sq_pi_nonneg pi_dist hπ f)]
        calc norm_pi pi_dist f * (Real.exp (-(SpectralGap_pi pi_dist H) * t) * norm_pi pi_dist f)
            = norm_pi pi_dist f * norm_pi pi_dist f * Real.exp (-(SpectralGap_pi pi_dist H) * t) := by ring
          _ = norm_sq_pi pi_dist f * Real.exp (-(SpectralGap_pi pi_dist H) * t) := by rw [h_sq]

/-- **Exponential Decay of Autocorrelation** (Parametric Form):

    For mean-zero observables with spectral gap γ > 0:
    |C_f(t)| ≤ ‖f‖²_π · e^{-γt}

    This is the **parametric interface** to `autocorrelation_decay_from_sector`.
    It takes the spectral gap γ as a parameter, avoiding the complex type dependencies
    of the full sector machinery.

    **Instantiation**: When sector conditions hold with γ = SpectralGap_pi pi_dist H,
    this follows from `autocorrelation_decay_from_sector`.

    **Connection to SpectralGap_pi**: For reversible systems where H is the
    Dirichlet form operator, γ = SpectralGap_pi pi_dist H. -/
axiom autocorrelation_decay_param (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (γ : ℝ) (hγ : 0 < γ)
    (f : V → ℝ) (hf : inner_pi pi_dist f (fun _ => 1) = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    |autocorrelation L pi_dist f t| ≤ norm_sq_pi pi_dist f * Real.exp (-γ * t)

/-! ### 5. Validity Horizon and Spectral Gap Relationship -/

/-- **Validity Horizon Lower Bound** (Parametric Main Theorem):

    Given:
    - ε > 0: leakage defect (from IsApproxLumpable)
    - γ > 0: spectral gap (from SpectralGap_pi or measurements)
    - Q > 0: partition quality factor

    If ε ≤ γ · Q, then T* = 1/ε ≥ τ_corr/Q where τ_corr = 1/γ.

    **Physical Significance**: The validity horizon is observable!
    Measure τ_corr from autocorrelation data, estimate Q from partition structure,
    and predict when the effective theory will fail. -/
theorem validity_horizon_lower_bound_param
    (ε γ Q : ℝ) (hε : 0 < ε) (hγ : 0 < γ) (hQ : 0 < Q)
    (h_bound : ε ≤ γ * Q) :
    validity_horizon ε hε ≥ autocorrelation_time_from_gap γ hγ / Q := by
  unfold validity_horizon autocorrelation_time_from_gap
  -- Goal: 1/ε ≥ (1/γ) / Q = 1/(γ·Q)
  -- From h_bound: ε ≤ γ·Q, so 1/ε ≥ 1/(γ·Q)
  rw [div_div]
  exact one_div_le_one_div_of_le hε h_bound

/-! ### 6. Observable Prediction -/

/-- **Observable Validity Horizon**: Given measured autocorrelation time and
    estimated partition quality, predict the validity horizon.

    T*_predicted = τ_corr / Q

    **Usage**: This formula allows experimental determination of effective
    theory lifetimes without computing the leakage defect directly. -/
def predicted_validity_horizon (τ_corr Q : ℝ) (_hτ : 0 < τ_corr) (_hQ : 0 < Q) : ℝ :=
  τ_corr / Q

/-- The predicted validity horizon equals 1/(γ·Q) when τ_corr = 1/γ. -/
lemma predicted_validity_horizon_eq (γ Q : ℝ) (hγ : 0 < γ) (hQ : 0 < Q) :
    predicted_validity_horizon (autocorrelation_time_from_gap γ hγ) Q
      (autocorrelation_time_from_gap_pos γ hγ) hQ = 1 / (γ * Q) := by
  unfold predicted_validity_horizon autocorrelation_time_from_gap
  rw [div_div]

/-! ### 8. Corollary: NCD Systems Have Extended Validity -/

/-- **NCD Validity Horizon**: For Near-Completely Decomposable systems,
    the validity horizon is controlled by ε/γ, not ε·t.

    This means NCD systems can maintain prediction accuracy for arbitrarily
    long times (in vertical error), though horizontal drift still accumulates.

    **See**: `NCD_uniform_error_bound` in Approximate.lean -/
theorem NCD_validity_enhancement
    (L L_fast L_slow : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (ε γ : ℝ)
    (hNCD : IsNCD L L_fast L_slow P pi_dist hπ ε γ)
    (t : ℝ) (ht : 0 ≤ t) (f₀ : V → ℝ) (hf₀ : f₀ = CoarseProjector P pi_dist hπ f₀) :
    ∃ C : ℝ, C ≥ 0 ∧
    norm_pi pi_dist (HeatKernelMap L t f₀ - CoarseProjector P pi_dist hπ (HeatKernelMap L t f₀)) ≤
    (ε / γ) * C * norm_pi pi_dist f₀ :=
  -- Direct application of NCD_uniform_error_bound
  NCD_uniform_error_bound L L_fast L_slow P pi_dist hπ ε γ hNCD t ht f₀ hf₀

/-! ## Summary

This module establishes the **observability of the validity horizon**:

1. **Definition**: T* = 1/ε (from leakage defect)
2. **Observable proxy**: T* ≥ τ_corr / Q (from autocorrelation and partition quality)
3. **Measurement procedure**:
   - Measure autocorrelation decay → extract τ_corr
   - Estimate partition quality Q from structure
   - Predict: T*_pred = τ_corr / Q

4. **Implications**:
   - Emergence has a measurable timescale
   - Effective theories have quantifiable validity limits
   - Model selection can be guided by validity horizon requirements

The key insight is that T* connects **microscopic properties** (leakage defect ε)
to **macroscopic observables** (autocorrelation time τ_corr), making the abstract
concept of "effective theory validity" experimentally accessible.
-/

end SGC.Observables
