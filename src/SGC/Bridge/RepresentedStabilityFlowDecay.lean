/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Bridge.CanonicalWaveletFisherRao
import SGC.Spectral.Defs

/-!
# Phase 4C: Exponential decay of the represented stability flow

This module composes Phase 4A (discrete Calderón on lifted amplitudes)
and Phase 4B (triangle bound) with `spectral_stability_bound`
(`@c:\Lean4 Projects\src\SGC\Spectral\Defs.lean:160-176`) to show that
the **represented** stability flow of the canonical Hermite-Gaussian
wavelet inherits the exponential-decay envelope of the intrinsic SGC
stability flow on lifted amplitudes.

## Headline theorems

* `HG_represented_stability_flow_spectral_decay_tight` — at a
  canonical tight HG frame on a lifted amplitude,
  `|β_rep| ≤ C · exp(−gap · t)`.  (Phase 4A + spectral bound.)
* `HG_represented_stability_flow_spectral_decay_triangle` — for *any*
  HG band-pass filter on a lifted amplitude,
  `|β_rep| ≤ C · exp(−gap · t) + RepresentationError`.
  (Phase 4B + spectral bound.)
* `HG_represented_stability_flow_exponential_envelope` — the fully
  constructive envelope for any HG spectral frame,
  `|β_rep| ≤ C · exp(−gap · t) + C' · (B/A − 1)`.
  (Combining with `HG_representation_error_bound`.)

## What this module is *not*

* It does **not** introduce any new axiom — pure composition of
  Phase 4A + 4B + `spectral_stability_bound` + the Phase 3A
  representation-error bound.
* It does **not** strengthen the hypotheses on `L`, `H`, `pi_dist`
  beyond what `spectral_stability_bound` already requires; the sole
  specialisation is `pi_dist := lift ψ` together with
  `pi_pos := lift_pos hψ` and
  `pi_sum := lift_sum_eq_one hψ_norm`.
* It does **not** prove a converse.  Each decay bound is an upper
  envelope, not an equation.

## Chain of custody

* `HG_canonical_wavelet_recovers_stability_flow_on_lifted_amplitude` (Phase 4A)
* `HG_represented_stability_flow_triangle_bound_lifted_amplitude` (Phase 4B)
* `HG_lifted_amplitude_representation_error_bound` (Phase 3A specialisation)
* `spectral_stability_bound` (core SGC theorem, `Spectral/Defs.lean`)
* **this module** (Phase 4C).
-/

namespace SGC.Bridge.RepresentedStabilityFlowDecay

open SGC.Bridge.CanonicalWavelet
open SGC.Bridge.HermiteGaussianCanonical
open SGC.Bridge.CanonicalWaveletFisherRao
open SGC.InformationGeometry.HellingerLift
open SGC.Spectral
open Matrix LinearMap

set_option linter.unusedSectionVars false

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-! ## 1. Tight-frame case: exact substitution into the spectral bound -/

/-- **Exponential decay of the represented stability flow at a canonical
    tight HG frame on a lifted amplitude.**

    At a `CanonicalTightFrame` whose `pi_dist` is the Hellinger lift of
    a pointwise-positive unit-ℓ²-norm amplitude `ψ`, the represented
    stability flow equals the intrinsic SGC stability flow
    (Phase 4A: `HG_canonical_wavelet_recovers_stability_flow_on_lifted_amplitude`),
    so it inherits the exponential-decay envelope of
    `spectral_stability_bound` verbatim:

      `∃ C ≥ 0, |β_rep| ≤ C · exp(−(SpectralGap_pi (lift ψ) H) · t)`.

    **Why this matters.**  On the load-bearing case (tight frame), the
    wavelet-reconstructed dynamics decay at the spectral-gap rate of
    the underlying Markov chain.  There is no extra penalty from the
    wavelet representation because, at tightness, the representation
    is exact.

    **Proof.**  Rewrite using Phase 4A's equation, then apply
    `spectral_stability_bound` with `pi_dist := lift ψ`,
    `pi_pos := lift_pos hψ`,
    `pi_sum := lift_sum_eq_one hψ_norm`. -/
theorem HG_represented_stability_flow_spectral_decay_tight
    [Nontrivial V]
    (L H : Matrix V V ℝ) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (ψ : V → ℝ) (hψ : ∀ x, 0 < ψ x) (hψ_norm : ∑ x, (ψ x) ^ 2 = 1)
    (frame : CanonicalTightFrame L (HGBandPassFilter α β hα hβ) (lift ψ)
              (lift_pos hψ))
    (h_irred : IrreducibilityAssumptions L H (lift ψ))
    (h_gap_pos : SpectralGap_pi (lift ψ) H > 0)
    (hL1 : toLin' L (fun _ => 1) = 0)
    (hH_const : H *ᵥ constant_vec_one = 0)
    (h_sa : ∀ u v, inner_pi (lift ψ) (H *ᵥ u) v =
                   inner_pi (lift ψ) u (H *ᵥ v))
    (h_psd : ∀ u, 0 ≤ inner_pi (lift ψ) (H *ᵥ u) u)
    (h_rel : ∀ u v, inner_pi (lift ψ) (L *ᵥ u) v +
                    inner_pi (lift ψ) u (L *ᵥ v) =
                    -2 * inner_pi (lift ψ) (H *ᵥ u) v)
    (epsilon : ℝ)
    (h_pos' : ∀ x t, K_norm L t x (lift ψ x) + epsilon > 0)
    (h_eps_min : ∃ ε_min > 0,
        ∀ x t, K_norm L t x (lift ψ x) + epsilon ≥ ε_min)
    (t : ℝ) (ht : 0 ≤ t)
    (hK1 : toLin' (HeatKernel L t) (fun _ => 1) = fun _ => 1) :
    ∃ C ≥ 0,
      |RepresentedStabilityFlow L (HGBandPassFilter α β hα hβ) (lift ψ)
          (lift_pos hψ) epsilon t| ≤
      C * Real.exp (-(SpectralGap_pi (lift ψ) H) * t) := by
  rw [HG_canonical_wavelet_recovers_stability_flow_on_lifted_amplitude
        L α β hα hβ ψ hψ frame epsilon t]
  exact spectral_stability_bound h_irred h_gap_pos hL1 hK1 hH_const
    h_sa h_psd h_rel h_pos' h_eps_min (lift_pos hψ)
    (lift_sum_eq_one hψ_norm) t ht

/-! ## 2. General (non-tight) case: triangle bound + spectral bound -/

/-- **Triangle decay of the represented stability flow on a lifted
    amplitude.**

    For *any* HG band-pass filter (tight or not) on a lifted amplitude,
    the represented stability flow is bounded by the exponential
    envelope of the intrinsic flow *plus* the representation error:

      `|β_rep| ≤ C · exp(−gap · t) + RepresentationError`.

    **Why this matters.**  This is the non-tight analogue of Phase 4C
    tight-frame decay.  The first summand tracks the *intrinsic
    dynamics* and the second tracks the *representation error from
    frame non-tightness*.  At a canonical tight frame, the second
    summand vanishes (Phase 4A) and the bound reduces to the
    tight-frame decay.

    **Proof.**  The Phase 4B triangle bound says
    `|β_rep| ≤ |stability_flow| + RepresentationError`; the spectral
    stability bound gives `|stability_flow| ≤ C · exp(−gap · t)`.
    Adding `RepresentationError ≥ 0` to the RHS of the spectral bound
    and applying transitivity yields the claim. -/
theorem HG_represented_stability_flow_spectral_decay_triangle
    [Nontrivial V]
    (L H : Matrix V V ℝ) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (ψ : V → ℝ) (hψ : ∀ x, 0 < ψ x) (hψ_norm : ∑ x, (ψ x) ^ 2 = 1)
    (h_irred : IrreducibilityAssumptions L H (lift ψ))
    (h_gap_pos : SpectralGap_pi (lift ψ) H > 0)
    (hL1 : toLin' L (fun _ => 1) = 0)
    (hH_const : H *ᵥ constant_vec_one = 0)
    (h_sa : ∀ u v, inner_pi (lift ψ) (H *ᵥ u) v =
                   inner_pi (lift ψ) u (H *ᵥ v))
    (h_psd : ∀ u, 0 ≤ inner_pi (lift ψ) (H *ᵥ u) u)
    (h_rel : ∀ u v, inner_pi (lift ψ) (L *ᵥ u) v +
                    inner_pi (lift ψ) u (L *ᵥ v) =
                    -2 * inner_pi (lift ψ) (H *ᵥ u) v)
    (epsilon : ℝ)
    (h_pos' : ∀ x t, K_norm L t x (lift ψ x) + epsilon > 0)
    (h_eps_min : ∃ ε_min > 0,
        ∀ x t, K_norm L t x (lift ψ x) + epsilon ≥ ε_min)
    (t : ℝ) (ht : 0 ≤ t)
    (hK1 : toLin' (HeatKernel L t) (fun _ => 1) = fun _ => 1) :
    ∃ C ≥ 0,
      |RepresentedStabilityFlow L (HGBandPassFilter α β hα hβ) (lift ψ)
          (lift_pos hψ) epsilon t| ≤
      C * Real.exp (-(SpectralGap_pi (lift ψ) H) * t) +
      RepresentationError L (HGBandPassFilter α β hα hβ) (lift ψ)
        (lift_pos hψ) epsilon t := by
  -- Obtain the spectral envelope C ≥ 0, |β| ≤ C · exp(−gap · t).
  obtain ⟨C, hC_nonneg, h_spectral⟩ :=
    spectral_stability_bound h_irred h_gap_pos hL1 hK1 hH_const
      h_sa h_psd h_rel h_pos' h_eps_min (lift_pos hψ)
      (lift_sum_eq_one hψ_norm) t ht
  refine ⟨C, hC_nonneg, ?_⟩
  -- Triangle: |β_rep| ≤ |β| + error ≤ C·exp(...) + error.
  have h_tri :
      |RepresentedStabilityFlow L (HGBandPassFilter α β hα hβ) (lift ψ)
          (lift_pos hψ) epsilon t| ≤
      |stability_flow L (lift ψ) epsilon t| +
      RepresentationError L (HGBandPassFilter α β hα hβ) (lift ψ)
        (lift_pos hψ) epsilon t :=
    HG_represented_stability_flow_triangle_bound_lifted_amplitude
      L α β hα hβ ψ hψ epsilon t
  -- Chain the two bounds.
  exact h_tri.trans
    (add_le_add_right h_spectral
      (RepresentationError L (HGBandPassFilter α β hα hβ) (lift ψ)
        (lift_pos hψ) epsilon t))

/-! ## 3. Fully constructive envelope with frame non-tightness penalty -/

/-- **Fully constructive exponential envelope for the represented
    stability flow on a lifted amplitude.**

    Combines Phase 4C triangle decay with the Phase 3A representation-
    error bound to give a fully constructive upper envelope for the
    represented stability flow of *any* HG spectral frame on a lifted
    amplitude:

      `|β_rep| ≤ C · exp(−gap · t) + C' · (B/A − 1)`

    where `C ≥ 0` is the spectral-stability constant and `C' > 0` is
    the representation-error constant.  The first summand decays
    exponentially in `t` at the spectral-gap rate; the second is a
    time-independent penalty that vanishes at a canonical tight frame
    (`B = A`).

    **Why this matters.**  Every term is constructive: the spectral
    constant `C` is packaged inside `spectral_stability_bound` (which
    depends on the `Vec`-card, `‖L‖`, `ε_min`, `π_min`), and the
    representation-error constant `C'` is packaged inside
    `HG_representation_error_bound` (which is Phase 3A).  Given the
    frame condition number `B/A ≥ 1`, the envelope is explicit.

    **Proof.**  Chain
    `HG_represented_stability_flow_spectral_decay_triangle` with
    `HG_lifted_amplitude_representation_error_bound`. -/
theorem HG_represented_stability_flow_exponential_envelope
    [Nontrivial V]
    (L H : Matrix V V ℝ) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (ψ : V → ℝ) (hψ : ∀ x, 0 < ψ x) (hψ_norm : ∑ x, (ψ x) ^ 2 = 1)
    (frame : SpectralFrame L (HGBandPassFilter α β hα hβ) (lift ψ)
              (lift_pos hψ))
    (h_irred : IrreducibilityAssumptions L H (lift ψ))
    (h_gap_pos : SpectralGap_pi (lift ψ) H > 0)
    (hL1 : toLin' L (fun _ => 1) = 0)
    (hH_const : H *ᵥ constant_vec_one = 0)
    (h_sa : ∀ u v, inner_pi (lift ψ) (H *ᵥ u) v =
                   inner_pi (lift ψ) u (H *ᵥ v))
    (h_psd : ∀ u, 0 ≤ inner_pi (lift ψ) (H *ᵥ u) u)
    (h_rel : ∀ u v, inner_pi (lift ψ) (L *ᵥ u) v +
                    inner_pi (lift ψ) u (L *ᵥ v) =
                    -2 * inner_pi (lift ψ) (H *ᵥ u) v)
    (epsilon : ℝ) (heps : epsilon > 0)
    (h_pos' : ∀ x t, K_norm L t x (lift ψ x) + epsilon > 0)
    (h_eps_min : ∃ ε_min > 0,
        ∀ x t, K_norm L t x (lift ψ x) + epsilon ≥ ε_min)
    (t : ℝ) (ht : 0 ≤ t)
    (hK1 : toLin' (HeatKernel L t) (fun _ => 1) = fun _ => 1) :
    ∃ C ≥ 0, ∃ C' > 0,
      |RepresentedStabilityFlow L (HGBandPassFilter α β hα hβ) (lift ψ)
          (lift_pos hψ) epsilon t| ≤
      C * Real.exp (-(SpectralGap_pi (lift ψ) H) * t) +
      C' * (FrameConditionNumber frame - 1) := by
  -- Spectral + triangle envelope.
  obtain ⟨C, hC_nonneg, h_triangle⟩ :=
    HG_represented_stability_flow_spectral_decay_triangle
      L H α β hα hβ ψ hψ hψ_norm h_irred h_gap_pos hL1 hH_const
      h_sa h_psd h_rel epsilon h_pos' h_eps_min t ht hK1
  -- Representation error bound (Phase 3A, lifted-amplitude specialisation).
  obtain ⟨C', hC'_pos, h_err⟩ :=
    HG_lifted_amplitude_representation_error_bound L α β hα hβ ψ hψ frame
      epsilon heps t ht
  refine ⟨C, hC_nonneg, C', hC'_pos, ?_⟩
  -- Chain: |β_rep| ≤ C·exp(...) + error ≤ C·exp(...) + C'·(B/A − 1).
  exact h_triangle.trans (add_le_add_left h_err _)

end

end SGC.Bridge.RepresentedStabilityFlowDecay
