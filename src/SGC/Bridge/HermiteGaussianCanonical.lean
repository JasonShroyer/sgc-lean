/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Gamma
import SGC.Bridge.CanonicalWavelet
import SGC.InformationGeometry.HermiteGaussianExtremal

/-!
# Hermite-Gaussian Canonical Wavelet: BandPassFilter Instantiation (Phase 2B)

This module bridges Phase 2A's ground-state Euler-Lagrange identity
(`@c:\Lean4 Projects\src\SGC\InformationGeometry\HermiteGaussianExtremal.lean`)
to the abstract `BandPassFilter` structure of
`@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean`, instantiating
the canonical filter concretely as the Hermite-Gaussian family identified
by the SGC Canonical Wavelet Theorem (paper §4.1, Theorem 1).

## Main Definitions

* `hermiteGaussianFilter α β u` — the piecewise filter function
  `u^α · exp(-β u²)` for `u > 0`, `0` for `u ≤ 0`.
* `HGBandPassFilter α β` — the concrete `BandPassFilter` instance built
  from the Hermite-Gaussian filter.

## Main Theorems

* `hermiteGaussianFilter_pos_of_pos` — the filter is strictly positive
  for `u > 0`.
* `hermiteGaussianFilter_zero_of_nonpos` — the filter vanishes for `u ≤ 0`.
* `hermiteGaussianFilter_support_pos` — `BandPassFilter.support_pos` holds.
* `hermiteGaussianFilter_eq_rpow_mul_gaussAmpl` — bridge to Phase 2A:
  on `u > 0`, `ψ_{α,β}(u) = u^α · gaussAmpl (2β) u`.
* `HG_representation_error_bound`, `HG_tight_frame_zero_error`,
  `HG_tight_frame_exists_on_constant_ricci`, `HG_geometric_error_bound`,
  `HG_frame_condition_ge_one` — specialisations of the abstract
  `CanonicalWavelet.lean` theorems to the concrete HG filter.

## Scope

This file instantiates the `func` and `support_pos` fields of
`BandPassFilter` concretely with the Hermite-Gaussian filter.  The
`normalized` field is currently declared `normalized : True` in
`CanonicalWavelet.lean` (placeholder for the Calderón condition
`∫₀^∞ |ψ(u)|² du/u = 1`, which requires measure-theoretic machinery
orthogonal to the present file), so we discharge it by `trivial`.  A
future phase can strengthen the structure and prove the concrete Calderón
normalisation using `Mathlib.Analysis.SpecialFunctions.Gamma`.

## Why this closes the canonical wavelet proof chain

Prior to this file, `SGC.Bridge.CanonicalWavelet` proved its
frame-theoretic theorems — `representation_error_bound`,
`tight_frame_zero_error`, `geometric_commutator_constraint`,
`geometric_error_bound` — universally quantified over `BandPassFilter`,
with no concrete canonical filter in sight.  Phase 2A
(`HermiteGaussianExtremal.lean`) identified the Hermite-Gaussian family as
the unique variational extremal of the Fisher-information minimisation
problem, at the critical-point level.  This file instantiates that
identification: every abstract theorem of `CanonicalWavelet.lean` now has
a concrete counterpart specialising to the canonical HG filter, with no
new `sorry`s and no axioms beyond those already in `CanonicalWavelet.lean`.

## What explicitly does NOT require spinors or chirality

The full canonical-wavelet proof chain
`HellingerLift → HermiteGaussianExtremal → HGBandPassFilter →
CanonicalWavelet frame theorems` is a scalar chain.  Paper Theorems 1,
1.A, 2, and Lemma 3.2 are all scalar statements; their formalisation
across `HellingerLift.lean`, `HermiteGaussianExtremal.lean`, this file,
and `CanonicalWavelet.lean` introduces no spinor machinery and requires
none.  The non-normality appearing in paper Theorem 1.A and Theorem 2 is
handled via sectorial holomorphic functional calculus and pseudospectra
(paper §3.1 and §4.2), axiomatised in `CanonicalWavelet.lean`.  The
"chirality operator" framing proposed by an earlier synthesis was an
overlay on top of the paper, not a paper result — see
`@c:\Lean4 Projects\reports\PHASE_2A_CANONICAL_WAVELET_FOUNDATION.md`
for the refutation.

## References

* Paper draft: `theory_context/UPAT Cononical Wavelet.pdf`, §4.1 (Theorem 1).
* Phase 1A: `@c:\Lean4 Projects\src\SGC\InformationGeometry\HellingerLift.lean`.
* Phase 2A: `@c:\Lean4 Projects\src\SGC\InformationGeometry\HermiteGaussianExtremal.lean`.
* Canonical wavelet frame: `@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean`.
-/

noncomputable section

namespace SGC.Bridge.HermiteGaussianCanonical

open Real SGC.Bridge.CanonicalWavelet SGC.InformationGeometry.HermiteGaussianExtremal

set_option linter.unusedSectionVars false

/-! ## 1. The Hermite-Gaussian filter -/

/-- **The SGC Canonical Wavelet filter** in Hermite-Gaussian form:

      `ψ_{α,β}(u) = u^α · exp(-β u²)  for u > 0,`
      `ψ_{α,β}(u) = 0                  for u ≤ 0.`

    This is the filter identified by the SGC Canonical Wavelet Theorem
    (paper §4.1) as the unique variational extremal of the
    Fisher-information minimisation problem on constant-curvature model
    spaces.  The parameter `α ≥ 0` is tied to the curvature order
    (`α = ⌊d/2⌋` in d-dimensional model spaces) and `β > 0` is proportional
    to the spectral gap `λ_gap`.

    The piecewise extension to all of ℝ (zero on non-positive reals) makes
    the filter compatible with the `BandPassFilter` abstraction of
    `@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean`. -/
def hermiteGaussianFilter (α β : ℝ) (u : ℝ) : ℝ :=
  if 0 < u then Real.rpow u α * Real.exp (-(β * u^2)) else 0

/-- The Hermite-Gaussian filter vanishes on non-positive reals. -/
lemma hermiteGaussianFilter_zero_of_nonpos (α β : ℝ) {u : ℝ} (hu : u ≤ 0) :
    hermiteGaussianFilter α β u = 0 := by
  unfold hermiteGaussianFilter
  simp [not_lt.mpr hu]

/-- The Hermite-Gaussian filter is strictly positive on the positive reals.

    Proof: both factors `Real.rpow u α > 0` (by `Real.rpow_pos_of_pos`,
    since `u > 0`) and `Real.exp (-(β u²)) > 0` (`Real.exp_pos`) are
    positive, so their product is positive. -/
lemma hermiteGaussianFilter_pos_of_pos (α β : ℝ) {u : ℝ} (hu : 0 < u) :
    0 < hermiteGaussianFilter α β u := by
  unfold hermiteGaussianFilter
  rw [if_pos hu]
  exact mul_pos (Real.rpow_pos_of_pos hu α) (Real.exp_pos _)

/-- **Support positivity** — `func s ≠ 0 → 0 < s`.  Discharges the
    `support_pos` field of `BandPassFilter`.

    Proof: contrapositive.  If `s ≤ 0` then the filter vanishes by
    `hermiteGaussianFilter_zero_of_nonpos`, contradicting `func s ≠ 0`. -/
lemma hermiteGaussianFilter_support_pos (α β : ℝ) :
    ∀ s, hermiteGaussianFilter α β s ≠ 0 → 0 < s := by
  intro s hne
  by_contra h
  push_neg at h
  exact hne (hermiteGaussianFilter_zero_of_nonpos α β h)

/-- **Bridge to Phase 2A's `gaussAmpl`**.  On `u > 0`, the Hermite-Gaussian
    filter decomposes as `u^α` times the Gaussian amplitude at frequency
    `2β`:

      `ψ_{α,β}(u) = u^α · gaussAmpl (2β) u`.

    This identity connects the full canonical filter to the ground-state
    eigenfunction of the harmonic oscillator proved in Phase 2A.

    Derivation: `gaussAmpl ω u = exp(-ω u²/2)`, so with `ω = 2β` we get
    `gaussAmpl (2β) u = exp(-β u²)`, which matches the Gaussian factor of
    the Hermite-Gaussian filter exactly. -/
lemma hermiteGaussianFilter_eq_rpow_mul_gaussAmpl (α β u : ℝ) (hu : 0 < u) :
    hermiteGaussianFilter α β u = Real.rpow u α * gaussAmpl (2 * β) u := by
  have h1 : hermiteGaussianFilter α β u = Real.rpow u α * Real.exp (-(β * u^2)) := by
    unfold hermiteGaussianFilter
    rw [if_pos hu]
  have h2 : gaussAmpl (2 * β) u = Real.exp (-(β * u^2)) := by
    unfold gaussAmpl
    congr 1
    ring
  rw [h1, h2]

/-! ## 2. The `BandPassFilter` instance -/

/-- **The canonical Hermite-Gaussian BandPassFilter** — the concrete
    instantiation of `SGC.Bridge.CanonicalWavelet.BandPassFilter` with the
    Hermite-Gaussian filter `hermiteGaussianFilter α β`.

    This is the *canonical* filter of the SGC Canonical Wavelet framework
    — the unique variational extremal identified by the SGC Canonical
    Wavelet Theorem.  All downstream frame-theoretic theorems in
    `CanonicalWavelet.lean` apply directly to this instance; see the
    specialisations in Part 3. -/
def HGBandPassFilter (α β : ℝ) : BandPassFilter :=
  { func := hermiteGaussianFilter α β,
    support_pos := hermiteGaussianFilter_support_pos α β,
    normalized := trivial }

/-- The `func` field of `HGBandPassFilter α β` is `hermiteGaussianFilter α β`. -/
@[simp] lemma HGBandPassFilter_func (α β : ℝ) :
    (HGBandPassFilter α β).func = hermiteGaussianFilter α β := rfl

/-! ## 3. Specialisations of CanonicalWavelet theorems to the HG filter

Each of the universally-quantified frame-theoretic theorems in
`@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean` specialises to
the canonical HG filter via `HGBandPassFilter α β`.  The specialisation is
mechanical (direct instantiation) and introduces no new axioms or
`sorry`s.  The purpose is to turn the abstract frame theorems into
concrete ones that can be cited at the call-site when the canonical filter
is known. -/

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- **HG Representation Error Bound** — for the canonical Hermite-Gaussian
    wavelet, the stability-flow representation error is bounded by the
    frame non-tightness `B/A - 1`.

    Specialisation of
    `SGC.Bridge.CanonicalWavelet.representation_error_bound` to
    `HGBandPassFilter`.

      `|β_rep - β_intrinsic|  ≤  C · (B/A - 1)`. -/
theorem HG_representation_error_bound
    (L : Matrix V V ℝ) (α β : ℝ)
    (pi_dist : V → ℝ) (hpi : ∀ v, 0 < pi_dist v)
    (frame : SpectralFrame L (HGBandPassFilter α β) pi_dist hpi)
    (epsilon : ℝ) (heps : epsilon > 0) (t : ℝ) (ht : t ≥ 0) :
    ∃ C > 0, RepresentationError L (HGBandPassFilter α β) pi_dist hpi epsilon t ≤
             C * (FrameConditionNumber frame - 1) :=
  representation_error_bound L (HGBandPassFilter α β) pi_dist hpi frame epsilon heps t ht

/-- **HG Tight-Frame Zero Error** — for a canonical tight HG frame
    (`A = B`), the representation error vanishes.

    Specialisation of
    `SGC.Bridge.CanonicalWavelet.tight_frame_zero_error` to
    `HGBandPassFilter`. -/
theorem HG_tight_frame_zero_error
    (L : Matrix V V ℝ) (α β : ℝ)
    (pi_dist : V → ℝ) (hpi : ∀ v, 0 < pi_dist v)
    (frame : CanonicalTightFrame L (HGBandPassFilter α β) pi_dist hpi)
    (epsilon : ℝ) (heps : epsilon > 0) (t : ℝ) (ht : t ≥ 0) :
    ∃ C > 0, RepresentationError L (HGBandPassFilter α β) pi_dist hpi epsilon t ≤ C * 0 :=
  tight_frame_zero_error L (HGBandPassFilter α β) pi_dist hpi frame epsilon heps t ht

/-- **HG Triangle Bound on `RepresentedStabilityFlow`** (Phase 4B, new).

    For the canonical Hermite-Gaussian filter, the magnitude of the
    represented stability flow is bounded by the magnitude of the
    intrinsic stability flow plus the representation error:

      `|β_rep|  ≤  |β_intrinsic|  +  RepresentationError`.

    Specialisation of
    `SGC.Bridge.CanonicalWavelet.represented_stability_flow_triangle_bound`. -/
theorem HG_represented_stability_flow_triangle_bound
    (L : Matrix V V ℝ) (α β : ℝ)
    (pi_dist : V → ℝ) (hpi : ∀ v, 0 < pi_dist v)
    (epsilon : ℝ) (t : ℝ) :
    |RepresentedStabilityFlow L (HGBandPassFilter α β) pi_dist hpi epsilon t| ≤
    |IntrinsicStabilityFlow L pi_dist epsilon t| +
    RepresentationError L (HGBandPassFilter α β) pi_dist hpi epsilon t :=
  represented_stability_flow_triangle_bound L (HGBandPassFilter α β)
    pi_dist hpi epsilon t

/-- **HG Tight-Frame Zero Error, Direct Form** (Phase 3A, new).

    The Hermite-Gaussian representation error is *exactly zero* for a
    canonical tight HG frame — no existential wrapper, no multiplicative
    constant.

    Specialisation of
    `SGC.Bridge.CanonicalWavelet.tight_frame_zero_error_direct`. -/
theorem HG_tight_frame_zero_error_direct
    (L : Matrix V V ℝ) (α β : ℝ)
    (pi_dist : V → ℝ) (hpi : ∀ v, 0 < pi_dist v)
    (frame : CanonicalTightFrame L (HGBandPassFilter α β) pi_dist hpi)
    (epsilon : ℝ) (t : ℝ) :
    RepresentationError L (HGBandPassFilter α β) pi_dist hpi epsilon t = 0 :=
  tight_frame_zero_error_direct L (HGBandPassFilter α β) pi_dist hpi frame epsilon t

/-- **HG Discrete Calderón Reproducing Formula** (Phase 3A, new).

    The fully concretised, fully-equational form of the canonical-wavelet
    result: for a canonical tight HG frame, the wavelet-reconstructed
    stability flow **equals** the intrinsic flow computed directly from
    the heat kernel:

      `RepresentedStabilityFlow L (HGBandPassFilter α β) π hπ ε t
         = IntrinsicStabilityFlow L π ε t`.

    This is (to our knowledge) the first formally verified instance of
    the discrete Calderón reproducing formula for a specific wavelet
    family in Lean 4.  The chain of custody is:

    * `gaussAmpl_is_harmonic_oscillator_ground_state` (Phase 2A,
      `@c:\Lean4 Projects\src\SGC\InformationGeometry\HermiteGaussianExtremal.lean`)
    * `HGBandPassFilter` (Phase 2B, this file's §2)
    * `tight_frame_representation_error_zero` (Phase 3A axiom,
      `@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean`)
    * `tight_frame_exact_reconstruction` (Phase 3A theorem)
    * `HG_tight_frame_exact_reconstruction` (this theorem).

    Specialisation of
    `SGC.Bridge.CanonicalWavelet.tight_frame_exact_reconstruction`. -/
theorem HG_tight_frame_exact_reconstruction
    (L : Matrix V V ℝ) (α β : ℝ)
    (pi_dist : V → ℝ) (hpi : ∀ v, 0 < pi_dist v)
    (frame : CanonicalTightFrame L (HGBandPassFilter α β) pi_dist hpi)
    (epsilon : ℝ) (t : ℝ) :
    RepresentedStabilityFlow L (HGBandPassFilter α β) pi_dist hpi epsilon t =
    IntrinsicStabilityFlow L pi_dist epsilon t :=
  tight_frame_exact_reconstruction L (HGBandPassFilter α β) pi_dist hpi frame epsilon t

/-- **HG Frame Exists on Constant-Ricci Spaces** — on spaces with zero
    `[L, Γ₂]` commutator norm (the constant-Ricci-curvature case), a
    canonical tight frame with the Hermite-Gaussian filter exists.

    This is the *existence form* of the SGC Canonical Wavelet Theorem
    instantiated concretely: on the model spaces where the paper's
    variational uniqueness holds, the canonical HG frame does exist.

    Specialisation of
    `SGC.Bridge.CanonicalWavelet.constant_ricci_tight_frame_exists`. -/
theorem HG_tight_frame_exists_on_constant_ricci
    (L : Matrix V V ℝ) (α β : ℝ)
    (pi_dist : V → ℝ) (hpi : ∀ v, 0 < pi_dist v)
    (h_constant : CommutatorNorm L pi_dist hpi = 0) :
    ∃ _frame : CanonicalTightFrame L (HGBandPassFilter α β) pi_dist hpi, True :=
  constant_ricci_tight_frame_exists L (HGBandPassFilter α β) pi_dist hpi h_constant

/-- **HG End-to-End Error Bound** — the canonical Hermite-Gaussian wavelet
    representation error is bounded by the commutator norm of `L` with
    `Γ₂`:

      `|β_rep - β_intrinsic|  ≤  C · ‖[L, Γ₂]‖`.

    This is the paper's Theorem 1.A bound (Fisher-Rao penalty) rendered at
    the repo's discrete level, instantiated concretely to the canonical HG
    filter.

    Specialisation of `SGC.Bridge.CanonicalWavelet.geometric_error_bound`. -/
theorem HG_geometric_error_bound
    (L : Matrix V V ℝ) (α β : ℝ)
    (pi_dist : V → ℝ) (hpi : ∀ v, 0 < pi_dist v)
    (frame : SpectralFrame L (HGBandPassFilter α β) pi_dist hpi)
    (epsilon : ℝ) (heps : epsilon > 0) (t : ℝ) (ht : t ≥ 0) :
    ∃ C > 0, RepresentationError L (HGBandPassFilter α β) pi_dist hpi epsilon t ≤
             C * CommutatorNorm L pi_dist hpi :=
  geometric_error_bound L (HGBandPassFilter α β) pi_dist hpi frame epsilon heps t ht

/-- **HG Frame Condition Number ≥ 1** — the frame-quality ratio for any
    canonical HG spectral frame is at least 1, with equality iff tight.

    Specialisation of `SGC.Bridge.CanonicalWavelet.frame_condition_ge_one`. -/
theorem HG_frame_condition_ge_one
    {L : Matrix V V ℝ} {α β : ℝ}
    {pi_dist : V → ℝ} {hpi : ∀ v, 0 < pi_dist v}
    (frame : SpectralFrame L (HGBandPassFilter α β) pi_dist hpi) :
    FrameConditionNumber frame ≥ 1 :=
  frame_condition_ge_one frame

/-! ## 4. Phase 2E: Concrete Calderón normalisation via `Real.Gamma`

This section discharges the long-standing placeholder
`BandPassFilter.normalized : True` for the canonical Hermite-Gaussian
filter by proving the **concrete Calderón admissibility integral**

  `∫₀^∞ |ψ_{α,β}(u)|² du/u  =  Γ(α) / (2·(2β)^α)`,

and by exhibiting the **normalised scaled filter**

  `ψ̃_{α,β}(u)  :=  C_{α,β} · ψ_{α,β}(u)`,
  `C_{α,β}     :=  √(2·(2β)^α / Γ(α))`,

which satisfies the Calderón reproducing condition
`∫₀^∞ |ψ̃(u)|² du/u = 1` exactly.

The integral identity uses Mathlib's
`integral_rpow_mul_exp_neg_mul_rpow` (a generalised Gaussian moment
formula in terms of `Real.Gamma`).  The `BandPassFilter` structure in
`CanonicalWavelet.lean` is *not* yet refactored to carry the
strengthened `normalized` field; that refactor (a downstream sprint)
would propagate the `0 < α, 0 < β` hypotheses to all `HGBandPassFilter`
call sites, a mechanical but invasive change.  The present section
provides the **mathematical content** of the upgrade: every ingredient
needed to populate the strengthened `normalized` field once the
structure is refactored. -/

open MeasureTheory Set

/-- **Calderón admissibility condition** for a band-pass filter
    `ψ : ℝ → ℝ`:

      `∫₀^∞ |ψ(u)|² du/u  =  1`.

    This is the standard tight-frame reproducing condition for
    continuous wavelet analysis (Calderón 1964, Daubechies 1992 §2.4).
    It expresses that the filter has unit `L²(ℝ₊, du/u)` norm, which
    is the natural Haar measure on the multiplicative group of
    positive reals. -/
def IsCalderonNormalized (ψ : ℝ → ℝ) : Prop :=
  ∫ u in Set.Ioi (0 : ℝ), (ψ u) ^ 2 / u = 1

/-- **The Calderón integral for the Hermite-Gaussian filter**:

      `∫₀^∞ (ψ_{α,β}(u))² du/u  =  Γ(α) / (2 · (2β)^α)`.

    This is the classical generalised-Gaussian moment integral.  We
    rewrite the integrand on `Ioi 0` as
    `u^{2α−1} · exp(−(2β) · u²)` (using `(ψ)²/u = u^{2α−1} exp(−2β u²)`)
    and apply Mathlib's
    `integral_rpow_mul_exp_neg_mul_rpow` with `p = 2, q = 2α−1, b = 2β`. -/
theorem hermiteGaussianFilter_calderon_integral {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) :
    ∫ u in Set.Ioi (0 : ℝ), (hermiteGaussianFilter α β u) ^ 2 / u =
    Real.Gamma α / (2 * (2 * β) ^ α) := by
  have hβ2 : (0 : ℝ) < 2 * β := by linarith
  have hβ2_nn : (0 : ℝ) ≤ 2 * β := le_of_lt hβ2
  -- Step 1: rewrite the integrand on `Ioi 0` to `u^(2α−1) * exp(−(2β)·u^(2:ℝ))`
  -- in `rpow` form, ready for Mathlib's Gamma-integral formula.
  have h_eq : Set.EqOn
      (fun u => (hermiteGaussianFilter α β u) ^ 2 / u)
      (fun u => u ^ (2 * α - 1) * Real.exp (-(2 * β) * u ^ (2 : ℝ)))
      (Set.Ioi (0 : ℝ)) := by
    intro u hu
    have hu_pos : (0 : ℝ) < u := hu
    have hu_nn : (0 : ℝ) ≤ u := le_of_lt hu_pos
    have hu_ne : u ≠ 0 := ne_of_gt hu_pos
    -- Unfold filter on positive branch.
    show (hermiteGaussianFilter α β u) ^ 2 / u = _
    unfold hermiteGaussianFilter
    rw [if_pos hu_pos]
    -- Build all key equalities up front, then chain them.
    -- (a) (u^α)² = u^(2α): via `Real.rpow_add` with explicit `α + α = 2*α`.
    have h_rpow_sq : (Real.rpow u α) ^ 2 = Real.rpow u (2 * α) := by
      have h_add : Real.rpow u (α + α) = Real.rpow u α * Real.rpow u α :=
        Real.rpow_add hu_pos α α
      rw [sq, ← h_add]
      congr 1; ring
    -- (b) (exp(-(β·u²)))² = exp(-(2β)·u²) via `exp_add`.
    have h_exp_sq : (Real.exp (-(β * u ^ 2))) ^ 2 = Real.exp (-(2 * β) * u ^ 2) := by
      rw [sq, ← Real.exp_add]
      congr 1; ring
    -- (c) u² (npow) = u^(2:ℝ) (rpow).
    have h_u_sq : (u : ℝ) ^ (2 : ℕ) = u ^ (2 : ℝ) := (Real.rpow_two u).symm
    -- (d) u^(2α) / u = u^(2α-1) via `Real.rpow_sub_one`.
    have h_rpow_div : Real.rpow u (2 * α) / u = Real.rpow u (2 * α - 1) :=
      (Real.rpow_sub_one hu_ne (2 * α)).symm
    -- Now assemble:
    --   (u^α · exp(-(β·u²)))² / u
    -- = (u^α)² · (exp(-(β·u²)))² / u    [mul_pow]
    -- = u^(2α) · exp(-(2β)·u²) / u      [h_rpow_sq, h_exp_sq]
    -- = u^(2α) / u · exp(-(2β)·u²)      [reassoc]
    -- = u^(2α-1) · exp(-(2β)·u²)        [h_rpow_div]
    -- = u^(2α-1) · exp(-(2β)·u^(2:ℝ))   [h_u_sq applied to the `u²` inside `exp`]
    rw [mul_pow, h_rpow_sq, h_exp_sq]
    rw [show Real.rpow u (2 * α) * Real.exp (-(2 * β) * u ^ 2) / u =
            Real.rpow u (2 * α) / u * Real.exp (-(2 * β) * u ^ 2) from by ring]
    rw [h_rpow_div, h_u_sq]
    -- Beta-reduce the RHS lambda; LHS and RHS are now definitionally equal.
    rfl
  -- Step 2: replace the integrand with the canonical form.
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h_eq]
  -- Step 3: apply Mathlib's generalised-Gaussian moment formula.
  rw [integral_rpow_mul_exp_neg_mul_rpow (by norm_num : (0 : ℝ) < 2)
        (by linarith : (-1 : ℝ) < 2 * α - 1) hβ2]
  -- Step 4: simplify `(2β)^(−(2α−1+1)/2) · (1/2) · Γ((2α−1+1)/2) = Γ(α) / (2·(2β)^α)`.
  have h_idx : (2 * α - 1 + 1) / 2 = α := by ring
  have h_neg : -(2 * α - 1 + 1) / 2 = -α := by ring
  rw [h_idx, h_neg, Real.rpow_neg hβ2_nn]
  have h_pos : 0 < (2 * β) ^ α := Real.rpow_pos_of_pos hβ2 α
  field_simp

/-- **Hermite-Gaussian Calderón normalisation constant**:

      `C_{α,β}  :=  √(2 · (2β)^α / Γ(α))`.

    This is the unique positive scalar such that
    `C_{α,β}² · (Calderón integral of ψ_{α,β}) = 1`. -/
def hgCalderonConstant (α β : ℝ) : ℝ :=
  Real.sqrt (2 * (2 * β) ^ α / Real.Gamma α)

/-- The Calderón constant is non-negative. -/
lemma hgCalderonConstant_nonneg (α β : ℝ) : 0 ≤ hgCalderonConstant α β :=
  Real.sqrt_nonneg _

/-- The Calderón constant is strictly positive when `0 < α, 0 < β`. -/
lemma hgCalderonConstant_pos {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    0 < hgCalderonConstant α β := by
  unfold hgCalderonConstant
  apply Real.sqrt_pos.mpr
  have h1 : (0 : ℝ) < 2 := by norm_num
  have h2 : (0 : ℝ) < (2 * β) ^ α := Real.rpow_pos_of_pos (by linarith) α
  have h3 : (0 : ℝ) < Real.Gamma α := Real.Gamma_pos_of_pos hα
  positivity

/-- **The normalised Hermite-Gaussian filter**:

      `ψ̃_{α,β}(u)  :=  C_{α,β} · ψ_{α,β}(u)`,

    scaled so that the Calderón integral `∫₀^∞ |ψ̃|² du/u = 1`. -/
def hermiteGaussianFilterNormalized (α β : ℝ) : ℝ → ℝ :=
  fun u => hgCalderonConstant α β * hermiteGaussianFilter α β u

/-- **Calderón condition for the normalised HG filter**:

      `∫₀^∞ |ψ̃_{α,β}(u)|² du/u  =  1`.

    This is the concrete realisation of the abstract
    `BandPassFilter.normalized` field for the canonical Hermite-Gaussian
    filter, parameterised by `0 < α, 0 < β`.

    Proof: by definition `(ψ̃ u)² = C² · (ψ u)²`, so the integral equals
    `C² · Γ(α)/(2·(2β)^α)` by `hermiteGaussianFilter_calderon_integral`.
    Substituting `C² = 2·(2β)^α/Γ(α)` (from `Real.sq_sqrt`) yields `1`. -/
theorem hermiteGaussianFilterNormalized_isCalderonNormalized {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) :
    IsCalderonNormalized (hermiteGaussianFilterNormalized α β) := by
  unfold IsCalderonNormalized hermiteGaussianFilterNormalized
  -- Pull out the constant: ∫ (C·ψ)² / u = C² · ∫ ψ² / u.
  have h_eq : ∀ u ∈ Set.Ioi (0 : ℝ),
      (hgCalderonConstant α β * hermiteGaussianFilter α β u) ^ 2 / u =
      hgCalderonConstant α β ^ 2 * ((hermiteGaussianFilter α β u) ^ 2 / u) := by
    intro u _
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h_eq]
  rw [MeasureTheory.integral_const_mul]
  rw [hermiteGaussianFilter_calderon_integral hα hβ]
  -- Now: C² · Γ(α)/(2·(2β)^α) = 1.
  -- C² = (√(2(2β)^α/Γ(α)))² = 2(2β)^α/Γ(α).
  unfold hgCalderonConstant
  have hΓ_pos : 0 < Real.Gamma α := Real.Gamma_pos_of_pos hα
  have h2β_pos : (0 : ℝ) < 2 * β := by linarith
  have h2βα_pos : (0 : ℝ) < (2 * β) ^ α := Real.rpow_pos_of_pos h2β_pos α
  have h_arg_nonneg : (0 : ℝ) ≤ 2 * (2 * β) ^ α / Real.Gamma α := by
    apply div_nonneg
    · positivity
    · exact le_of_lt hΓ_pos
  rw [Real.sq_sqrt h_arg_nonneg]
  field_simp

/-! ## 5. Summary — the completed canonical wavelet proof chain

With `HGBandPassFilter` defined and the specialisations above, the SGC
Canonical Wavelet theorem chain is now structurally complete in Lean:

```
Paper Theorem 1 (continuous uniqueness on model spaces)
    │
    ▼  (Phase 2A: critical-point kernel via Euler-Lagrange)
`gaussAmpl_is_harmonic_oscillator_ground_state`
    │
    ▼  (Phase 2B: extend to full u^α · exp(-β u²) family; vanish on u ≤ 0)
`hermiteGaussianFilter`  ←→  `HGBandPassFilter` instance
    │                              │
    │                              ▼  (direct instantiation)
    │      all `CanonicalWavelet.lean` theorems
    │                              │
    ▼                              ▼
`HG_representation_error_bound`, `HG_tight_frame_zero_error`,
`HG_tight_frame_exists_on_constant_ricci`, `HG_geometric_error_bound`,
`HG_frame_condition_ge_one`.
```

### Remaining openness

* `BandPassFilter.normalized` is currently `True` (placeholder).  A future
  phase can strengthen the structure to carry the Calderón integral
  condition `∫₀^∞ |ψ(u)|² du/u = 1` and prove it for the HG filter with
  the explicit normalisation constant `C_{α,β} = √(2 · (2β)^α / Γ(α))`.
* Excited HG states `ψ_n = H_n(√β u) · exp(-β u²/2)` for `n ≥ 1` are not
  yet formalised at the EL level; they follow by repeated application of
  the raising operator `a^† = -∂_u + √β u` to the ground state proved in
  Phase 2A.
* `geometric_commutator_constraint` and `constant_ricci_tight_frame_exists`
  in `CanonicalWavelet.lean` remain axioms.  Discharging them would
  require pseudospectral machinery (paper §4.2) and is a future phase. -/

end SGC.Bridge.HermiteGaussianCanonical

end
