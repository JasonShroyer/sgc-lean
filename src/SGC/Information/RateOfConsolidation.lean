/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team

# Rate of Consolidation: Exponential Decay of Cross-Boundary Correlations

This module discharges the **correlation-decay form** of the Rate-of-Consolidation
Theorem (UPAT Boundaries §4.3): the information leakage across a Markov blanket
decays exponentially at the spectral-gap rate `γ_gap = SpectralGap_pi pi_dist H`.

## Main Results

1. `heat_decay_mean_zero`: for a mean-zero observable `f`, the heat-evolved observable
   contracts as `‖e^{tL} f‖_π ≤ e^{-γt} · ‖f‖_π`. (The reusable spectral core of
   `autocorrelation_decay_from_sector`, depending only on `f` being mean-zero.)
2. `cross_correlation_decay`: for ANY external observable `g` and a mean-zero internal
   observable `f`, `|⟨g, e^{tL} f⟩_π| ≤ ‖g‖_π · ‖f‖_π · e^{-γt}`. (Generalizes the
   autocorrelation bound `g = f` to cross-correlations via Cauchy–Schwarz.)
3. `rate_of_consolidation`: the time-indexed L¹ sum of cross-block correlations — the
   dynamical analogue of the static CMI proxy `conditionalMutualInfo` (`∑∑ |entry|`) —
   obeys `I(t) ≤ I₀ · e^{-γ_gap · t}` with `I₀ := ∑_{i,e} ‖fE e‖_π · ‖fI i‖_π`.

## Honest scope (v1, ε = 0)

This is the *correlation-decay* form: it proves that the cross-block coupling measured
by the L¹ proxy decays at the consolidation rate. The literal log-determinant
**Gaussian-CMI** dressing `I(μ;η|s,a;t) ≤ I₀ e^{-ctγ}` (passing these decaying
covariance entries through the differential-entropy formula) is the **v2** deepening:
it is justified pointwise by `dynamical_blanket_iff_information_blanket`
(`SGC/Information/Equivalence.lean`) but is NOT discharged here — it requires
determinant/log machinery beyond the current scope.

## References

- SGC `autocorrelation_decay_from_sector` (Observables/ValidityHorizon.lean) — the
  spectral bridge this module generalizes.
- SGC `sector_envelope_bound_canonical` (Spectral/Envelope/Sector.lean) — the ε=0
  contraction `‖e^{tL} P_⊥‖_π ≤ e^{-γt}`.
- SGC `conditionalMutualInfo` (Information/Equivalence.lean) — the static L¹ CMI proxy.
- UPAT_SGC_mapping §F "Rate-of-Consolidation Theorem".
-/

import SGC.Observables.ValidityHorizon

noncomputable section

namespace SGC.Observables

open Finset Matrix Real SGC.Approximate SGC.Spectral

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### 1. Mean-zero heat contraction (the reusable spectral core) -/

/-- **Mean-zero heat contraction**: for a mean-zero observable `f`, the heat-evolved
    observable contracts at the spectral-gap rate:

    `‖e^{tL} f‖_π ≤ e^{-γt} · ‖f‖_π`.

    This is the reusable spectral core extracted from `autocorrelation_decay_from_sector`
    (it depends only on `f` being mean-zero, not on any second observable). The proof is
    `f = P_⊥ f` (mean-zero) + the operator-norm bound + `sector_envelope_bound_canonical`. -/
lemma heat_decay_mean_zero
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
    norm_pi pi_dist (HeatKernelMap L t f)
      ≤ Real.exp (-(SpectralGap_pi pi_dist H) * t) * norm_pi pi_dist f := by
  have h_norm_nonneg : ∀ g : V → ℝ, 0 ≤ norm_pi pi_dist g := fun g => Real.sqrt_nonneg _
  -- For mean-zero f, f = P_⊥ f (the projection onto 1⊥ fixes it).
  have h_f_eq_Pf : (P_ortho_pi pi_dist h_sum hπ) f = f := by
    unfold P_ortho_pi
    simp only [LinearMap.sub_apply, LinearMap.id_apply,
               LinearMap.smulRight_apply, LinearMap.coe_mk, AddHom.coe_mk]
    rw [hf, zero_smul, sub_zero]
  -- So e^{tL} f = (e^{tL} ∘ P_⊥) f.
  have h_heat_eq : HeatKernelMap L t f
      = (toLin' (Spectral.HeatKernel L t) ∘ₗ P_ortho_pi pi_dist h_sum hπ) f := by
    simp only [LinearMap.comp_apply, h_f_eq_Pf]
    rfl
  rw [h_heat_eq]
  have h_sector := sector_envelope_bound_canonical hπ h_sum L H hL1 h_sa h_psd h_constH h_gap h_rel t ht
  have h_bound := opNorm_pi_bound pi_dist hπ
                    (toLin' (Spectral.HeatKernel L t) ∘ₗ P_ortho_pi pi_dist h_sum hπ) f
  calc norm_pi pi_dist ((toLin' (Spectral.HeatKernel L t) ∘ₗ P_ortho_pi pi_dist h_sum hπ) f)
      ≤ opNorm_pi pi_dist hπ (toLin' (Spectral.HeatKernel L t) ∘ₗ P_ortho_pi pi_dist h_sum hπ)
          * norm_pi pi_dist f := h_bound
    _ ≤ Real.exp (-(SpectralGap_pi pi_dist H) * t) * norm_pi pi_dist f :=
        mul_le_mul_of_nonneg_right h_sector (h_norm_nonneg f)

/-! ### 2. Cross-correlation decay -/

/-- **Cross-correlation decay**: the L²(π) temporal cross-correlation between any
    observable `g` and a mean-zero observable `f` decays at the spectral-gap rate:

    `|⟨g, e^{tL} f⟩_π| ≤ ‖g‖_π · ‖f‖_π · e^{-γt}`.

    Generalizes `autocorrelation_decay_from_sector` from the autocorrelation `g = f`
    to an arbitrary external observable `g`. Proof: Cauchy–Schwarz + `heat_decay_mean_zero`. -/
lemma cross_correlation_decay
    [Nontrivial V] (L H : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (h_sum : ∑ v, pi_dist v = 1)
    (hL1 : L *ᵥ constant_vec_one = 0)
    (h_sa : ∀ u v, inner_pi pi_dist (H *ᵥ u) v = inner_pi pi_dist u (H *ᵥ v))
    (h_psd : ∀ u, 0 ≤ inner_pi pi_dist (H *ᵥ u) u)
    (h_constH : H *ᵥ constant_vec_one = 0)
    (h_gap : 0 < SpectralGap_pi pi_dist H)
    (h_rel : ∀ u v, inner_pi pi_dist (L *ᵥ u) v + inner_pi pi_dist u (L *ᵥ v) =
                    -2 * inner_pi pi_dist (H *ᵥ u) v)
    (f g : V → ℝ) (hf : inner_pi pi_dist f (fun _ => 1) = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    |inner_pi pi_dist g (HeatKernelMap L t f)|
      ≤ norm_pi pi_dist g * norm_pi pi_dist f * Real.exp (-(SpectralGap_pi pi_dist H) * t) := by
  have h_norm_nonneg : ∀ u : V → ℝ, 0 ≤ norm_pi pi_dist u := fun u => Real.sqrt_nonneg _
  have h_cs := cauchy_schwarz_pi pi_dist hπ g (HeatKernelMap L t f)
  have h_decay := heat_decay_mean_zero L H pi_dist hπ h_sum hL1 h_sa h_psd h_constH h_gap h_rel f hf t ht
  calc |inner_pi pi_dist g (HeatKernelMap L t f)|
      ≤ norm_pi pi_dist g * norm_pi pi_dist (HeatKernelMap L t f) := h_cs
    _ ≤ norm_pi pi_dist g * (Real.exp (-(SpectralGap_pi pi_dist H) * t) * norm_pi pi_dist f) :=
        mul_le_mul_of_nonneg_left h_decay (h_norm_nonneg g)
    _ = norm_pi pi_dist g * norm_pi pi_dist f * Real.exp (-(SpectralGap_pi pi_dist H) * t) := by
        ring

/-! ### 3. The Rate of Consolidation Theorem (correlation-decay form) -/

/-- **Rate of Consolidation Theorem** (correlation-decay form, ε = 0).

    The time-indexed information leakage across a Markov blanket — measured as the L¹
    sum of cross-block temporal correlations between internal observables `fI i`
    (mean-zero) and external observables `fE e` — decays exponentially at the
    spectral-gap (consolidation) rate:

    `I(t) ≤ I₀ · e^{-γ_gap · t}`,    `I₀ := ∑_{i ∈ internal, e ∈ external} ‖fE e‖_π · ‖fI i‖_π`.

    This is the dynamical analogue of the static L¹ CMI proxy `conditionalMutualInfo`
    (`∑∑ |entry|`, `SGC/Information/Equivalence.lean`): it proves that the cross-block
    coupling that proxy measures relaxes at the consolidation rate
    `γ_gap = SpectralGap_pi pi_dist H`. The constant `I₀` is the t = 0 Cauchy–Schwarz
    envelope of the leakage.

    **Honest scope**: the literal log-determinant Gaussian-CMI form is the v2 deepening
    (see module docstring); this discharges the operational correlation-decay content. -/
theorem rate_of_consolidation
    [Nontrivial V] (L H : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (h_sum : ∑ v, pi_dist v = 1)
    (hL1 : L *ᵥ constant_vec_one = 0)
    (h_sa : ∀ u v, inner_pi pi_dist (H *ᵥ u) v = inner_pi pi_dist u (H *ᵥ v))
    (h_psd : ∀ u, 0 ≤ inner_pi pi_dist (H *ᵥ u) u)
    (h_constH : H *ᵥ constant_vec_one = 0)
    (h_gap : 0 < SpectralGap_pi pi_dist H)
    (h_rel : ∀ u v, inner_pi pi_dist (L *ᵥ u) v + inner_pi pi_dist u (L *ᵥ v) =
                    -2 * inner_pi pi_dist (H *ᵥ u) v)
    (internal external : Finset V) (fI fE : V → (V → ℝ))
    (hfI : ∀ i ∈ internal, inner_pi pi_dist (fI i) (fun _ => 1) = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    (∑ i ∈ internal, ∑ e ∈ external,
        |inner_pi pi_dist (fE e) (HeatKernelMap L t (fI i))|)
      ≤ (∑ i ∈ internal, ∑ e ∈ external,
          norm_pi pi_dist (fE e) * norm_pi pi_dist (fI i))
          * Real.exp (-(SpectralGap_pi pi_dist H) * t) := by
  calc (∑ i ∈ internal, ∑ e ∈ external,
            |inner_pi pi_dist (fE e) (HeatKernelMap L t (fI i))|)
      ≤ ∑ i ∈ internal, ∑ e ∈ external,
          (norm_pi pi_dist (fE e) * norm_pi pi_dist (fI i)
            * Real.exp (-(SpectralGap_pi pi_dist H) * t)) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro e _
        exact cross_correlation_decay L H pi_dist hπ h_sum hL1 h_sa h_psd h_constH h_gap h_rel
                (fI i) (fE e) (hfI i hi) t ht
    _ = (∑ i ∈ internal, ∑ e ∈ external,
            norm_pi pi_dist (fE e) * norm_pi pi_dist (fI i))
            * Real.exp (-(SpectralGap_pi pi_dist H) * t) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_mul]

end SGC.Observables
