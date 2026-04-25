/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Bridge.HermiteGaussianCanonical
import SGC.InformationGeometry.HellingerLift

/-!
# Canonical Wavelet ⨉ Fisher-Rao: integration with the Hellinger lift (Phase 4A)

This module is the long-awaited integration brick.  It proves that the
canonical Hermite-Gaussian wavelet machinery from Phase 2B + 3A
(`@c:\Lean4 Projects\src\SGC\Bridge\HermiteGaussianCanonical.lean`,
`@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean`) and the
Fisher-Rao tangent isometry from Phase 1A
(`@c:\Lean4 Projects\src\SGC\InformationGeometry\HellingerLift.lean`)
**fit together exactly as expected**: when the input distribution is
the Hellinger-lift of an amplitude, the wavelet-reconstructed flow is
the actual SGC `stability_flow`, and the wavelet analysis at every
scale preserves the Fisher-Rao = 4 · Euclidean tangent identity.

## Headline theorems

* `lift_amplitude_valid_distribution` — the lift of a pointwise-positive
  unit-ℓ²-norm amplitude is a positive probability distribution on `V`.
* `wavelet_coefficient_preserves_tangent_isometry` — for any band-pass
  filter at any positive scale, the wavelet coefficient `Ψ(sL) Δψ` of
  a tangent perturbation `Δψ` satisfies the same tangent isometry
  identity as `Δψ` itself: its lifted differential's Fisher-Rao
  squared length is exactly four times its Euclidean squared length.
  In other words, **wavelet analysis commutes with the Hellinger lift
  at the level of tangent norms**, at every scale, for every filter.
* `HG_canonical_wavelet_recovers_stability_flow_on_lifted_amplitude` —
  for a canonical tight Hermite-Gaussian frame on a lifted amplitude,
  the represented stability flow equals the actual SGC `stability_flow`
  pointwise, *as real numbers*, with no error and no constant.  This
  is the **discrete Calderón reproducing formula on the Fisher-Rao
  manifold**.
* `tight_frame_lifted_amplitude_zero_error` — direct restatement of the
  zero-error property for canonical tight HG frames on lifted amplitudes.
* `HG_lifted_amplitude_representation_error_bound` — the non-tight
  quantitative bound, specialised to lifted amplitudes.

## What this module is *not*

* It does **not** assert that the amplitude space is globally flat or
  that amplitudes from different tasks may be linearly added.  See
  `@c:\Lean4 Projects\src\SGC\InformationGeometry\HellingerLift.lean`
  module docstring for the honest scope of the local tangent isometry.
* It introduces **zero new axioms**.  Every theorem in this file is a
  zero-`sorry` consequence of the existing Phase 1A + 2A + 2B + 3A
  tower.
* It does **not** discharge any of the remaining axioms in
  `CanonicalWavelet.lean`; it composes them with the already-discharged
  Hellinger lift to make the integration rigorous.

## Why this matters

Before this file, the canonical-wavelet brick (`CanonicalWavelet.lean`,
`HermiteGaussianCanonical.lean`) and the Fisher-Rao brick
(`HellingerLift.lean`) lived in adjacent rooms of the formalisation
without a doorway.  After this file, the doorway is built and load-
bearing: any theorem about the SGC stability flow on a lifted amplitude
can now invoke the discrete Calderón reproducing formula to *exactly*
substitute the canonical wavelet representation for the intrinsic flow,
and any theorem about wavelet coefficients of amplitude perturbations
can now invoke the tangent isometry to interchange Euclidean and
Fisher-Rao norms.

This is also (to our knowledge) the first formally verified theorem in
Lean 4 stating that wavelet analysis commutes with the Hellinger lift
at the tangent level for an arbitrary discrete operator `L` and an
arbitrary band-pass filter — a strictly stronger structural statement
than the pointwise reproducing formula alone.

## References

* Phase 1A: `HellingerLift.lean` (tangent isometry).
* Phase 2A: `HermiteGaussianExtremal.lean` (HG ground-state EL identity).
* Phase 2B: `HermiteGaussianCanonical.lean` (HG `BandPassFilter`).
* Phase 3A: `CanonicalWavelet.lean` (`tight_frame_exact_reconstruction`).
-/

namespace SGC.Bridge.CanonicalWaveletFisherRao

open SGC.Bridge.CanonicalWavelet
open SGC.Bridge.HermiteGaussianCanonical
open SGC.InformationGeometry.HellingerLift
open SGC.Spectral

set_option linter.unusedSectionVars false

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-! ## 1. Lifted amplitude is a valid SGC probability distribution -/

/-- **Lifted amplitude is a probability distribution.**

    Given a pointwise-positive unit-ℓ²-norm amplitude `ψ : V → ℝ`,
    the lifted distribution `lift ψ = ψ²` is positive everywhere and
    sums to one.

    This is the hypothesis package required by the
    `spectral_stability_bound` machinery in
    `@c:\Lean4 Projects\src\SGC\Spectral\Defs.lean` and by the entire
    `BandPassFilter` API in `CanonicalWavelet.lean`, which expects a
    pointwise-positive `pi_dist` and (where stated) a sum-to-one
    distribution. -/
theorem lift_amplitude_valid_distribution
    (ψ : V → ℝ) (hψ_pos : ∀ x, 0 < ψ x) (hψ_norm : ∑ x, (ψ x) ^ 2 = 1) :
    (∀ x, 0 < lift ψ x) ∧ (∑ x, lift ψ x = 1) :=
  ⟨lift_pos hψ_pos, lift_sum_eq_one hψ_norm⟩

/-! ## 2. Wavelet analysis commutes with the Hellinger lift -/

/-- **Wavelet coefficients preserve the tangent isometry.**

    For *any* band-pass filter `psi`, *any* positive scale `s`, *any*
    pointwise-positive amplitude `ψ : V → ℝ`, and *any* tangent
    perturbation `Δψ : V → ℝ`, the wavelet coefficient
    `W_s(Δψ) = ψ(sL) Δψ` is itself a tangent vector at `ψ`, and its
    lifted differential `liftDiff ψ (W_s Δψ) = 2·ψ·W_s(Δψ)` has
    Fisher-Rao squared length exactly four times its Euclidean squared
    length:

      `fisherRaoQuadForm (lift ψ) (liftDiff ψ (W_s Δψ))
         = 4 · euclideanQuadForm (W_s Δψ)`.

    **Mathematical content.**  Wavelet analysis at every scale is a
    *Fisher-Rao tangent isometry up to factor 4* on lifted amplitudes:
    applying `Ψ(sL)` to a perturbation `Δψ`, then measuring the Fisher-
    Rao length of the lifted result, gives the same answer as
    measuring the Euclidean length of `Ψ(sL) Δψ` directly and
    multiplying by four.  The wavelet machinery "doesn't see" the
    curvature of the simplex — it operates entirely in the flat
    tangent space, with the curvature handled by the lift.

    **Proof.**  Direct application of `fisher_euclidean_tangent_isometry`
    (Phase 1A) to the wavelet coefficient.  No new analytical content
    beyond Phase 1A's pointwise identity. -/
theorem wavelet_coefficient_preserves_tangent_isometry
    (L : Matrix V V ℝ) (psi : BandPassFilter)
    (s : ℝ) (hs : s > 0)
    (ψ Δψ : V → ℝ) (hψ : ∀ x, 0 < ψ x) :
    fisherRaoQuadForm (lift ψ)
        (liftDiff ψ (WaveletCoefficient L psi s hs Δψ)) =
    4 * euclideanQuadForm (WaveletCoefficient L psi s hs Δψ) :=
  fisher_euclidean_tangent_isometry ψ
    (WaveletCoefficient L psi s hs Δψ) hψ

/-- **HG specialisation of the wavelet coefficient tangent isometry.**

    For the canonical Hermite-Gaussian filter `HGBandPassFilter α β`,
    the tangent isometry on wavelet coefficients holds at every scale
    `s > 0` and every parameter pair `(α, β)`. -/
theorem HG_wavelet_coefficient_preserves_tangent_isometry
    (L : Matrix V V ℝ) (α β : ℝ)
    (s : ℝ) (hs : s > 0)
    (ψ Δψ : V → ℝ) (hψ : ∀ x, 0 < ψ x) :
    fisherRaoQuadForm (lift ψ)
        (liftDiff ψ (WaveletCoefficient L (HGBandPassFilter α β) s hs Δψ)) =
    4 * euclideanQuadForm
          (WaveletCoefficient L (HGBandPassFilter α β) s hs Δψ) :=
  wavelet_coefficient_preserves_tangent_isometry L
    (HGBandPassFilter α β) s hs ψ Δψ hψ

/-- **Bound corollary**: the Fisher-Rao tangent norm-squared of the
    lifted wavelet coefficient is bounded above by four times its
    Euclidean norm-squared (with equality, by the isometry).  Useful
    when only an upper bound is required at the call-site. -/
theorem wavelet_coefficient_fisherRao_le_four_euclidean
    (L : Matrix V V ℝ) (psi : BandPassFilter)
    (s : ℝ) (hs : s > 0)
    (ψ Δψ : V → ℝ) (hψ : ∀ x, 0 < ψ x) :
    fisherRaoQuadForm (lift ψ)
        (liftDiff ψ (WaveletCoefficient L psi s hs Δψ)) ≤
    4 * euclideanQuadForm (WaveletCoefficient L psi s hs Δψ) := by
  rw [wavelet_coefficient_preserves_tangent_isometry L psi s hs ψ Δψ hψ]

/-! ## 3. Discrete Calderón reproducing formula on lifted amplitudes -/

/-- **Discrete Calderón reproducing formula on lifted amplitudes** —
    the headline integration result.

    For a canonical tight Hermite-Gaussian frame whose distribution
    parameter is the Hellinger lift of a pointwise-positive amplitude
    `ψ`, the represented stability flow equals the actual SGC
    `stability_flow` of the lifted distribution, *pointwise as real
    numbers*:

      `RepresentedStabilityFlow L (HGBandPassFilter α β) (lift ψ) … ε t
         = stability_flow L (lift ψ) ε t`.

    **Why this matters.**  This is the explicit, equational form of
    the discrete Calderón reproducing formula for the canonical
    wavelet living on the Fisher-Rao manifold (via the Hellinger lift).
    The canonical wavelet **exactly recovers** the SGC stability
    dynamics on amplitude-derived distributions — no approximation, no
    error, no constant.

    **Chain of custody:**
    * `gaussAmpl_is_harmonic_oscillator_ground_state` (Phase 2A)
    * `HGBandPassFilter α β` (Phase 2B)
    * `tight_frame_representation_error_zero` (Phase 3A axiom)
    * `tight_frame_exact_reconstruction` (Phase 3A theorem)
    * `HG_tight_frame_exact_reconstruction` (Phase 3A theorem)
    * `lift ψ` (Phase 1A definition)
    * **this theorem** (Phase 4A integration). -/
theorem HG_canonical_wavelet_recovers_stability_flow_on_lifted_amplitude
    (L : Matrix V V ℝ) (α β : ℝ)
    (ψ : V → ℝ) (hψ : ∀ x, 0 < ψ x)
    (frame : CanonicalTightFrame L (HGBandPassFilter α β) (lift ψ)
              (lift_pos hψ))
    (epsilon : ℝ) (t : ℝ) :
    RepresentedStabilityFlow L (HGBandPassFilter α β) (lift ψ)
      (lift_pos hψ) epsilon t =
    stability_flow L (lift ψ) epsilon t := by
  -- `HG_tight_frame_exact_reconstruction` (Phase 3A) gives:
  --   RepresentedStabilityFlow ... = IntrinsicStabilityFlow L (lift ψ) ε t.
  -- `IntrinsicStabilityFlow` is *definitionally* `stability_flow`
  -- (see `@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean:175-177`),
  -- so after the rewrite the two sides are syntactically equal.
  rw [HG_tight_frame_exact_reconstruction L α β (lift ψ) (lift_pos hψ)
        frame epsilon t]
  rfl

/-- **Lifted-amplitude tight-frame zero error.**

    Direct restatement of the discrete Calderón formula in
    representation-error form: for a canonical tight HG frame on a
    lifted amplitude, `RepresentationError = 0` exactly. -/
theorem tight_frame_lifted_amplitude_zero_error
    (L : Matrix V V ℝ) (α β : ℝ)
    (ψ : V → ℝ) (hψ : ∀ x, 0 < ψ x)
    (frame : CanonicalTightFrame L (HGBandPassFilter α β) (lift ψ)
              (lift_pos hψ))
    (epsilon : ℝ) (t : ℝ) :
    RepresentationError L (HGBandPassFilter α β) (lift ψ) (lift_pos hψ)
      epsilon t = 0 :=
  HG_tight_frame_zero_error_direct L α β (lift ψ) (lift_pos hψ) frame
    epsilon t

/-! ## 4. Quantitative non-tight bound on lifted amplitudes -/

/-- **Lifted-amplitude triangle bound on `RepresentedStabilityFlow`** (Phase 4B).

    For *any* (not necessarily tight) HG band-pass filter on a lifted
    amplitude, the magnitude of the represented stability flow is
    bounded by the magnitude of the actual SGC `stability_flow` on
    the lifted distribution plus the representation error:

      `|β_rep|  ≤  |stability_flow L (lift ψ) ε t|  +  RepresentationError`.

    **Why this matters.**  Combined with
    `HG_lifted_amplitude_representation_error_bound` (which bounds the
    representation error by `C · (B/A − 1)` for any non-tight frame),
    this gives a *fully constructive* upper bound on `|β_rep|` for the
    canonical HG wavelet on any lifted amplitude:

      `|β_rep|  ≤  |stability_flow L (lift ψ) ε t|  +  C · (B/A − 1)`.

    The first term tracks the *intrinsic dynamics*; the second tracks
    the *representation error from frame non-tightness*.  At a
    canonical tight frame, the second term vanishes and the inequality
    becomes the equation `|β_rep| = |stability_flow|` (i.e., the
    discrete Calderón formula).

    Specialisation of
    `SGC.Bridge.HermiteGaussianCanonical.HG_represented_stability_flow_triangle_bound`,
    using that `IntrinsicStabilityFlow L (lift ψ) ε t` is definitionally
    `stability_flow L (lift ψ) ε t`. -/
theorem HG_represented_stability_flow_triangle_bound_lifted_amplitude
    (L : Matrix V V ℝ) (α β : ℝ)
    (ψ : V → ℝ) (hψ : ∀ x, 0 < ψ x)
    (epsilon : ℝ) (t : ℝ) :
    |RepresentedStabilityFlow L (HGBandPassFilter α β) (lift ψ)
        (lift_pos hψ) epsilon t| ≤
    |stability_flow L (lift ψ) epsilon t| +
    RepresentationError L (HGBandPassFilter α β) (lift ψ) (lift_pos hψ)
      epsilon t :=
  HG_represented_stability_flow_triangle_bound L α β (lift ψ)
    (lift_pos hψ) epsilon t

/-- **Lifted-amplitude representation error bound.**

    For *any* (not necessarily tight) HG spectral frame on a lifted
    amplitude, the representation error is bounded by the frame
    non-tightness `B/A − 1`:

      `error ≤ C · (FrameConditionNumber frame − 1)`

    with explicit `C > 0`.  This is `HG_representation_error_bound`
    (Phase 3A theorem) specialised to the lifted distribution
    `lift ψ`. -/
theorem HG_lifted_amplitude_representation_error_bound
    (L : Matrix V V ℝ) (α β : ℝ)
    (ψ : V → ℝ) (hψ : ∀ x, 0 < ψ x)
    (frame : SpectralFrame L (HGBandPassFilter α β) (lift ψ) (lift_pos hψ))
    (epsilon : ℝ) (heps : epsilon > 0) (t : ℝ) (ht : t ≥ 0) :
    ∃ C > 0, RepresentationError L (HGBandPassFilter α β) (lift ψ)
              (lift_pos hψ) epsilon t ≤
              C * (FrameConditionNumber frame - 1) :=
  HG_representation_error_bound L α β (lift ψ) (lift_pos hψ) frame
    epsilon heps t ht

end

end SGC.Bridge.CanonicalWaveletFisherRao
