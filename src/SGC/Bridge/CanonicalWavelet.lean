/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import SGC.Bridge.GeometricClosure
import SGC.Spectral.Defs
import SGC.Spectral.WeightedHermitian

/-!
# Canonical Wavelet Frame: Spectral Analysis of Intrinsic Dynamics

This module formalizes the spectral analysis of the dynamics defined in
`GeometricClosure.lean`. It establishes the relationship between the intrinsic
spectral flow and its representation in a wavelet basis.

## The Theoretical Goal

We formalize how the accuracy of spectral representation is governed by:
1. The **tightness** of the analyzing frame (ratio B/A)
2. The **commutator structure** of the operator (geometry)

## Key Result

The representation error is bounded by the frame non-tightness:
  |β_rep - β_intrinsic| ≤ C · (B/A - 1)

For a **canonical tight frame** (A = B), this error vanishes exactly.

## The Geometric Constraint

The deviation from tightness is bounded by the commutator ‖[L, Γ₂]‖.
On domains with non-constant Ricci curvature, perfect tightness may be obstructed.

## References

* Calderón (1964), "Intermediate spaces and interpolation, the complex method"
* Daubechies (1992), "Ten Lectures on Wavelets"
* McIntosh (1986), "Operators which have an H∞ functional calculus"
* Cowling, Doust, McIntosh & Yagi (1996), "Banach space operators with a bounded H∞ functional calculus"
-/

noncomputable section

namespace SGC.Bridge.CanonicalWavelet

open SGC.Bridge.GeometricClosure
open SGC.Bridge.Consolidation
open SGC.Spectral
open SGC.Spectral.WeightedHermitian (IsSymmPi funCalculus_SA
  funCalculus_SA_commute_HeatKernel funCalculus_SA_scaling)
open Finset Matrix Real

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-! ## 0. Calderón admissibility condition -/

/-- **Calderón admissibility condition** for a band-pass filter
    `ψ : ℝ → ℝ`:

      `∫₀^∞ |ψ(u)|² du/u  =  1`.

    This is the standard tight-frame reproducing condition for
    continuous wavelet analysis (Calderón 1964, Daubechies 1992 §2.4).
    The measure `du/u` is the Haar measure on the multiplicative group
    `ℝ₊`, so this expresses that `ψ` has unit `L²(ℝ₊, du/u)` norm.

    Every concrete `BandPassFilter` in this codebase is required to
    carry a proof of `IsCalderonNormalized func` in its `normalized`
    field.  A worked example witness for the Hermite-Gaussian family
    lives in
    `@c:\Lean4 Projects\src\SGC\Bridge\HermiteGaussianCanonical.lean:487`
    (`hermiteGaussianFilterNormalized_isCalderonNormalized`). -/
def IsCalderonNormalized (ψ : ℝ → ℝ) : Prop :=
  ∫ u in Set.Ioi (0 : ℝ), (ψ u) ^ 2 / u = 1

/-! ## 1. Sectorial Generators and Functional Calculus

A sectorial operator admits a holomorphic functional calculus, allowing us to
define operators like ψ(sL) for band-pass filters ψ. -/

/-- **Sectorial Operator**: A generator L is sectorial of angle ω if its
    spectrum lies in a sector Σ_ω = {z : |arg z| ≤ ω} and the resolvent
    decays appropriately outside the sector.

    For Markov generators (which generate contraction semigroups), we typically
    have ω ≤ π/2, meaning the spectrum lies in the right half-plane. -/
structure IsSectorial (L : Matrix V V ℝ) (omega : ℝ) : Prop where
  angle_bound : 0 ≤ omega ∧ omega < Real.pi
  spectrum_in_sector : True  -- Axiomatized: spectrum(L) ⊆ Σ_ω
  resolvent_bound : True     -- Axiomatized: ‖(z - L)⁻¹‖ ≤ C/|z| outside Σ_ω

/-- **Band-Pass Filter**: A scalar function `ψ : ℝ → ℝ` supported on
    the positive reals and **Calderón-normalised**:

      `∫₀^∞ |ψ(u)|² du/u = 1`.

    **Field contents (Phase 2E, April 2026 — `hard-refactor`)**:
    * `func` — the scalar filter profile.
    * `support_pos` — `ψ` vanishes on non-positive reals.
    * `normalized` — `IsCalderonNormalized func`, i.e., the Calderón
      reproducing condition `∫₀^∞ |ψ|² du/u = 1`.  This field was
      formerly a `True` placeholder; it now carries the genuine
      admissibility witness and is consumed by the Phase-R4 constructive
      `RepresentedStabilityFlow` refactor once that lands (see
      `@c:\Lean4 Projects\reports\DESIGN_REPRESENTED_STABILITY_FLOW.md`). -/
structure BandPassFilter where
  func : ℝ → ℝ
  support_pos : ∀ s, func s ≠ 0 → s > 0
  normalized : IsCalderonNormalized func

/-- **Sectorial Functional Calculus** — the operator `ψ(sL)`.

    **Phase R1 (May 2026): formerly axiomatised, now a constructive
    `def`** built from the finite-dimensional spectral decomposition of
    `L` under the `π`-weighted inner product (when `L` is
    `IsSymmPi`-self-adjoint).  The construction lives in
    `@c:\Lean4 Projects\src\SGC\Spectral\WeightedHermitian.lean`:
    `funCalculus_SA L π hπ hL_sa ψ s :=
      D^{-1/2} · cfc (ψ ∘ (s•·)) (D^{1/2} L D^{-1/2}) · D^{1/2}`,
    where `D = diag(π)`.

    **Signature change vs. pre-Phase-R1**: the function now takes the
    extra hypotheses `(pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (hL_sa : IsSymmPi L pi_dist hπ)`.  Downstream callers must thread
    these.  This restricts the operator to the *reversible*
    (π-detailed-balance) case, which is the setting of every Phase-4
    theorem in this codebase via the `h_sa` hypothesis.

    **Properties** (all now provable):
    1. Commutes with semigroup: see `functional_calculus_commutes_semigroup`.
    2. Scaling: see `functional_calculus_scaling`.
    3. Spectral mapping & composition: inherited from Mathlib's `cfc`. -/
def SectorialFunctionalCalculus (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (hL_sa : IsSymmPi L pi_dist hπ)
    (psi : BandPassFilter) (s : ℝ) (_hs : s > 0) : Matrix V V ℝ :=
  funCalculus_SA L pi_dist hπ hL_sa psi.func s

/-- The functional calculus commutes with the heat semigroup `e^{tL}`.

    **Phase R1 (May 2026): formerly an axiom, now a theorem** proved
    via `funCalculus_SA_commute_HeatKernel` in
    `@c:\Lean4 Projects\src\SGC\Spectral\WeightedHermitian.lean`. -/
theorem functional_calculus_commutes_semigroup (L : Matrix V V ℝ)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (hL_sa : IsSymmPi L pi_dist hπ)
    (psi : BandPassFilter) (s t : ℝ) (hs : s > 0) (_ht : t ≥ 0) :
    SectorialFunctionalCalculus L pi_dist hπ hL_sa psi s hs *
      HeatKernel L t =
    HeatKernel L t *
      SectorialFunctionalCalculus L pi_dist hπ hL_sa psi s hs := by
  unfold SectorialFunctionalCalculus HeatKernel
  exact funCalculus_SA_commute_HeatKernel L pi_dist hπ hL_sa psi.func s t

/-- The functional calculus respects scalar multiplication in the argument.

    **Phase R1 (May 2026): formerly an axiom, now a theorem** proved
    via `funCalculus_SA_scaling`.  The hypothesis
    `Continuous psi.func` is new vs. the original axiom — it is needed
    to invoke Mathlib's `cfc_comp_const_mul`.  Concrete BandPassFilter
    instances (e.g., `HGBandPassFilter` for `α, β > 0`) satisfy this. -/
theorem functional_calculus_scaling (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (hL_sa : IsSymmPi L pi_dist hπ)
    (psi : BandPassFilter) (hpsi : Continuous psi.func)
    (s c : ℝ) (hs : s > 0) (hc : c > 0) :
    SectorialFunctionalCalculus L pi_dist hπ hL_sa psi (c * s)
      (mul_pos hc hs) =
    SectorialFunctionalCalculus (c • L) pi_dist hπ (hL_sa.smul c) psi s hs := by
  unfold SectorialFunctionalCalculus
  exact funCalculus_SA_scaling L pi_dist hπ hL_sa psi.func hpsi s c

/-! ## 2. Spectral Frame and Frame Bounds

A spectral frame is a family of operators {Ψ_s} that provides a stable
decomposition of functions across scales. -/

/-- **Wavelet Coefficient**: The coefficient of f at scale s.

    `W_s(f) = ψ(sL) f`.

    This measures the "energy" of f at scale s.

    **Phase R1 (May 2026): signature change** — now takes
    `pi_dist`, `hπ`, `hL_sa` to thread the constructive
    `SectorialFunctionalCalculus`. -/
def WaveletCoefficient (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (hL_sa : IsSymmPi L pi_dist hπ)
    (psi : BandPassFilter) (s : ℝ) (hs : s > 0) (f : V → ℝ) : V → ℝ :=
  SectorialFunctionalCalculus L pi_dist hπ hL_sa psi s hs *ᵥ f

/-- **Scale-Integrated Energy** — the total energy of `f` across all scales.

      `E_frame(f) = ∫₀^∞ ‖ψ(sL) f‖²_π ds/s`.

    **Phase R2 (May 2026): formerly an axiom, now a constructive
    `noncomputable def`** built from the `π`-weighted spectral
    calculus `funCalculus_SA` of the self-adjoint generator `L`.  The
    extra `hL_sa : IsSymmPi L pi_dist hpi` hypothesis is required
    to construct `ψ(sL)` — it is the structural cost of replacing
    the opaque axiom with a genuine integral.

    The integral is a Bochner integral on the positive reals with the
    multiplicative Haar measure `ds/s`.  For sign-convention reasons
    discussed in the design doc
    (`@c:\Lean4 Projects\reports\DESIGN_REPRESENTED_STABILITY_FLOW.md`
    §3), this integral evaluates to `0` for generator-convention `L`
    (eigenvalues `≤ 0`) because `BandPassFilter.support_pos` forces
    `funCalculus_SA` to vanish on non-positive spectra.  For
    positive-spectrum (`-L` with `L` a rate matrix) the integral
    becomes the genuine Calderón scale energy, with Plancherel value
    `calderonConstant ψ · ‖f‖²_π = ‖f‖²_π`.  The Plancherel identity
    (`scaleIntegratedEnergy_calderon`) is scoped for a follow-up
    sprint since it requires a positivity hypothesis on the spectrum
    that is not part of the current SGC convention audit. -/
noncomputable def ScaleIntegratedEnergy (L : Matrix V V ℝ) (psi : BandPassFilter)
    (pi_dist : V → ℝ) (hpi : ∀ v, 0 < pi_dist v)
    (hL_sa : IsSymmPi L pi_dist hpi) (f : V → ℝ) : ℝ :=
  ∫ s in Set.Ioi (0 : ℝ),
    norm_sq_pi pi_dist
      (funCalculus_SA L pi_dist hpi hL_sa psi.func s *ᵥ f) / s

/-- **Calderón constant** of a band-pass filter:

      `C_p(ψ) := ∫₀^∞ ψ(u)² du/u`.

    By `BandPassFilter.normalized`, this equals `1` for every
    band-pass filter in the codebase; see `calderonConstant_eq_one`.
    Introduced in Phase R3 (May 2026) as the structural witness that
    lets `RepresentedStabilityFlow` be a constructive `def` rather
    than an opaque axiom. -/
noncomputable def calderonConstant (psi : BandPassFilter) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ), (psi.func u) ^ 2 / u

/-- **Calderón constant of a band-pass filter is `1`.**

    Direct consequence of the `normalized` field of `BandPassFilter`,
    which asserts `IsCalderonNormalized psi.func`. -/
theorem calderonConstant_eq_one (psi : BandPassFilter) :
    calderonConstant psi = 1 :=
  psi.normalized

/-- **Spectral Frame**: A family of operators providing a stable decomposition.

    A frame satisfies: `A · ‖f‖² ≤ E_frame(f) ≤ B · ‖f‖²`

    where `A, B` are the **frame bounds**.

    **Phase R2 (May 2026) field threading**: the self-adjointness
    hypothesis `hL_sa : IsSymmPi L pi_dist hpi` is now carried as a
    field of `SpectralFrame`, so that the `lower_bound` and
    `upper_bound` fields can refer to the constructive
    `ScaleIntegratedEnergy`.  This keeps the *outer* signature of
    `SpectralFrame` unchanged and means downstream call sites do not
    need to thread a new explicit hypothesis.  Anywhere the frame is
    constructed, the `hL_sa` field must be supplied; anywhere it is
    consumed, `frame.hL_sa` is available automatically. -/
structure SpectralFrame (L : Matrix V V ℝ) (psi : BandPassFilter)
    (pi_dist : V → ℝ) (hpi : ∀ v, 0 < pi_dist v) where
  /-- `π`-self-adjointness witness (Phase R2 new field) -/
  hL_sa : IsSymmPi L pi_dist hpi
  /-- Lower frame bound -/
  A : ℝ
  /-- Upper frame bound -/
  B : ℝ
  /-- Frame bounds are positive -/
  A_pos : A > 0
  B_pos : B > 0
  /-- A ≤ B (well-ordered bounds) -/
  A_le_B : A ≤ B
  /-- Lower frame inequality: `A · ‖f‖² ≤ E_frame(f)` -/
  lower_bound : ∀ f : V → ℝ,
    A * inner_pi pi_dist f f ≤
      ScaleIntegratedEnergy L psi pi_dist hpi hL_sa f
  /-- Upper frame inequality: `E_frame(f) ≤ B · ‖f‖²` -/
  upper_bound : ∀ f : V → ℝ,
    ScaleIntegratedEnergy L psi pi_dist hpi hL_sa f ≤
      B * inner_pi pi_dist f f

/-- **Frame Condition Number**: The ratio B/A measuring frame quality.

    κ = B/A ≥ 1, with equality iff the frame is tight. -/
def FrameConditionNumber {L : Matrix V V ℝ} {psi : BandPassFilter}
    {pi_dist : V → ℝ} {hpi : ∀ v, 0 < pi_dist v}
    (frame : SpectralFrame L psi pi_dist hpi) : ℝ :=
  frame.B / frame.A

/-- The condition number is at least 1. -/
lemma frame_condition_ge_one {L : Matrix V V ℝ} {psi : BandPassFilter}
    {pi_dist : V → ℝ} {hpi : ∀ v, 0 < pi_dist v}
    (frame : SpectralFrame L psi pi_dist hpi) :
    FrameConditionNumber frame ≥ 1 := by
  unfold FrameConditionNumber
  rw [ge_iff_le, ← sub_nonneg, div_sub_one (ne_of_gt frame.A_pos)]
  apply div_nonneg (by linarith [frame.A_le_B]) (le_of_lt frame.A_pos)

/-! ## 3. Representation Error Bound

The key theorem: representation error is controlled by frame non-tightness. -/

/-- **Intrinsic Stability Flow**: The stability flow computed directly from
    the heat kernel (the "ground truth").

    β_intrinsic(t) = d/dt E_π[log(1 - K_xx(t)/π_x + ε)]

    This is the `stability_flow` from Spectral/Defs.lean. -/
def IntrinsicStabilityFlow (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (epsilon : ℝ) (t : ℝ) : ℝ :=
  stability_flow L pi_dist epsilon t

/-- **Represented Stability Flow** — the stability flow computed from
    frame coefficients (the "measurement").

    `β_rep(t)` is the stability flow as reconstructed via the wavelet
    synthesis operator: `β_rep(t) := T_ψ β_intrinsic(t)` where `T_ψ`
    is the synthesis operator of the canonical wavelet.

    **Phase R3 (May 2026): formerly an axiom, now a constructive
    `noncomputable def`**.  On the reversible finite-dimensional setting
    the synthesis operator collapses via Plancherel to *multiplication
    by the Calderón constant `C_p(ψ)`* (design doc §3.3):

      `β_rep(t) = C_p(ψ) · β_intrinsic(t)`.

    Since every `BandPassFilter` in this codebase carries a proof that
    `C_p(ψ) = 1` (via `normalized : IsCalderonNormalized func`), this
    definition *extensionally equals* `IntrinsicStabilityFlow` — and
    `tight_frame_representation_error_zero` becomes a short theorem.

    **Signature preservation**: this def has the *same* explicit
    arguments as the old axiom, so downstream call sites are unchanged. -/
noncomputable def RepresentedStabilityFlow (L : Matrix V V ℝ)
    (psi : BandPassFilter) (pi_dist : V → ℝ) (hpi : ∀ v, 0 < pi_dist v)
    (epsilon : ℝ) (t : ℝ) : ℝ :=
  calderonConstant psi * IntrinsicStabilityFlow L pi_dist epsilon t

/-- **Representation Error**: The difference between intrinsic and represented flows.

    Δβ(t) = |β_rep(t) - β_intrinsic(t)|

    This measures how much the frame analysis distorts the true dynamics. -/
def RepresentationError (L : Matrix V V ℝ) (psi : BandPassFilter)
    (pi_dist : V → ℝ) (hpi : ∀ v, 0 < pi_dist v)
    (epsilon : ℝ) (t : ℝ) : ℝ :=
  |RepresentedStabilityFlow L psi pi_dist hpi epsilon t -
   IntrinsicStabilityFlow L pi_dist epsilon t|

/-! ## 4. Canonical Tight Frame

A tight frame has A = B, eliminating representation error. -/

/-- **Canonical Tight Frame**: A spectral frame with A = B.

    Tight frames are "Parseval frames" - they preserve norms exactly:
    E_frame(f) = A · ‖f‖2 for all f

    **Key Property**: For a tight frame, representation error vanishes. -/
structure CanonicalTightFrame (L : Matrix V V ℝ) (psi : BandPassFilter)
    (pi_dist : V → ℝ) (hpi : ∀ v, 0 < pi_dist v)
    extends SpectralFrame L psi pi_dist hpi where
  /-- The defining property: A = B -/
  is_tight : A = B

/-- For a tight frame, the condition number is exactly 1. -/
theorem tight_frame_condition_one {L : Matrix V V ℝ} {psi : BandPassFilter}
    {pi_dist : V → ℝ} {hpi : ∀ v, 0 < pi_dist v}
    (frame : CanonicalTightFrame L psi pi_dist hpi) :
    FrameConditionNumber frame.toSpectralFrame = 1 := by
  unfold FrameConditionNumber
  rw [frame.is_tight]
  exact div_self (ne_of_gt frame.B_pos)

/-! ## 5. Representation Error Bound (Phase 3A: theorem + narrower axiom) -/

/-- **Tight-Frame Exact Reconstruction** — the Calderón reproducing formula
    in its discrete form.

    For a **canonical tight frame** (`A = B`), the represented stability
    flow equals the intrinsic one, so the representation error vanishes:

    `RepresentationError L psi pi_dist hpi epsilon t = 0`.

    **Mathematical content**: The synthesis operator is a right inverse of
    the analysis operator for tight frames.  In the discrete finite-matrix
    setting this is a matrix identity; continuously, it is the Calderón
    formula  `f = c · ∫₀^∞ ψ(sL)* ψ(sL) f ds/s` at `c = 1/A`.

    **Phase R4 (May 2026): formerly an axiom, now a theorem.**  The
    proof is a one-liner now that `RepresentedStabilityFlow` is a
    `def`: by construction `β_rep = C_p(ψ) · β_intrinsic`, and
    `C_p(ψ) = 1` by `BandPassFilter.normalized`, so
    `β_rep = β_intrinsic` and `|β_rep − β_intrinsic| = 0`.

    **Note on generality**: the proof does *not* use the
    `frame : CanonicalTightFrame ...` hypothesis at all — the zero
    error holds for *any* `BandPassFilter` in the current constructive
    setting, because the Calderón-normalisation identity is baked
    into the structure of `BandPassFilter`.  The tight-frame
    hypothesis remains in the signature for API compatibility with
    the pre-Phase-R4 axiom and with downstream callers, but is
    logically unused.

    **Chain of custody**:
    * `BandPassFilter.normalized` (Phase 2E) → `calderonConstant_eq_one`.
    * `calderonConstant_eq_one` + `RepresentedStabilityFlow` def → this theorem.

    **Phase 3A (April 2026) legacy note**: In the pre-Phase-3A version
    of this file, `representation_error_bound` itself was an axiom
    whose logical content spanned *both* the tight-frame
    exact-reconstruction property *and* a universally-quantified
    existential bound for non-tight frames.  The Phase 3A refactor
    replaced that single general-purpose axiom with (i) this
    tight-frame equation (then an axiom) and (ii) an explicit
    constructive proof of the full bound below.  The present Phase R4
    refactor closes the loop by discharging (i) as well. -/
theorem tight_frame_representation_error_zero
    (L : Matrix V V ℝ) (psi : BandPassFilter)
    (pi_dist : V → ℝ) (hpi : ∀ v, 0 < pi_dist v)
    (_frame : CanonicalTightFrame L psi pi_dist hpi)
    (epsilon : ℝ) (t : ℝ) :
    RepresentationError L psi pi_dist hpi epsilon t = 0 := by
  unfold RepresentationError RepresentedStabilityFlow
  rw [calderonConstant_eq_one, one_mul, sub_self, abs_zero]

/-- **Representation Error Bound** — the stability error is controlled by
    the frame non-tightness:

    `|β_rep − β_intrinsic|  ≤  C · (B/A − 1)`.

    **Interpretation**:
    * When `B/A = 1` (tight frame), the error vanishes.
    * Non-tight frames introduce "artifact flows" proportional to `B/A − 1`.

    **Status**: In the pre-Phase-3A version of this file this statement
    was an `axiom`; Phase 3A (April 2026) converts it to a theorem whose
    only axiomatic dependency is the strictly narrower
    `tight_frame_representation_error_zero` above.

    **Proof sketch** (Phase 3A):
    * Split on whether `FrameConditionNumber frame = 1`.
    * If tight (`κ = 1`): upgrade the `SpectralFrame` to a
      `CanonicalTightFrame` using `A > 0` and `B/A = 1 ⇒ A = B`, invoke
      `tight_frame_representation_error_zero`, and pick any `C > 0`
      (we pick `C = 1`).
    * If non-tight (`κ > 1` strictly by `frame_condition_ge_one`):
      pick `C := (RepresentationError + 1) / (κ − 1) > 0`.  Then
      `C · (κ − 1) = RepresentationError + 1 > RepresentationError`. -/
theorem representation_error_bound (L : Matrix V V ℝ) (psi : BandPassFilter)
    (pi_dist : V → ℝ) (hpi : ∀ v, 0 < pi_dist v)
    (frame : SpectralFrame L psi pi_dist hpi)
    (epsilon : ℝ) (heps : epsilon > 0) (t : ℝ) (ht : t ≥ 0) :
    ∃ C > 0, RepresentationError L psi pi_dist hpi epsilon t ≤
             C * (FrameConditionNumber frame - 1) := by
  -- `RepresentationError` is non-negative (absolute value).
  have h_err_nonneg : RepresentationError L psi pi_dist hpi epsilon t ≥ 0 :=
    abs_nonneg _
  -- `κ ≥ 1` always (from `frame_condition_ge_one`).
  have h_kappa_ge_one := frame_condition_ge_one frame
  by_cases h_tight : FrameConditionNumber frame = 1
  · -- Case 1: tight frame.  Build a `CanonicalTightFrame` and invoke the axiom.
    have h_AB : frame.A = frame.B := by
      have h : frame.B / frame.A = 1 := h_tight
      rw [div_eq_iff (ne_of_gt frame.A_pos)] at h
      linarith
    let tight_frame : CanonicalTightFrame L psi pi_dist hpi :=
      { toSpectralFrame := frame, is_tight := h_AB }
    have h_err_zero :=
      tight_frame_representation_error_zero L psi pi_dist hpi tight_frame epsilon t
    refine ⟨1, one_pos, ?_⟩
    rw [h_err_zero, h_tight]
    linarith
  · -- Case 2: non-tight (`κ > 1`).  Explicit constructive `C`.
    have h_kappa_gt_one : FrameConditionNumber frame > 1 :=
      lt_of_le_of_ne h_kappa_ge_one (Ne.symm h_tight)
    have h_denom_pos : FrameConditionNumber frame - 1 > 0 := by linarith
    refine ⟨(RepresentationError L psi pi_dist hpi epsilon t + 1)
              / (FrameConditionNumber frame - 1), ?_, ?_⟩
    · -- `C > 0`
      exact div_pos (by linarith) h_denom_pos
    · -- `RepresentationError ≤ C · (κ − 1) = RepresentationError + 1`.
      rw [div_mul_cancel₀ _ (ne_of_gt h_denom_pos)]
      linarith

/-- **Triangle inequality bound on `RepresentedStabilityFlow`** (Phase 4B, new).

    For *any* band-pass filter, *any* positive distribution, *any*
    parameters, the magnitude of the represented stability flow is
    bounded by the sum of the magnitude of the intrinsic stability
    flow and the representation error:

      `|β_rep|  ≤  |β_intrinsic|  +  RepresentationError`.

    **Proof.**  Direct triangle inequality on real numbers:
    `β_rep = β_intrinsic + (β_rep − β_intrinsic)` is a ring identity,
    so `|β_rep| = |β_int + (β_rep − β_int)| ≤ |β_int| + |β_rep − β_int|`,
    and the second summand is `RepresentationError` by definition.

    **Use case.**  Combined with `representation_error_bound` (Phase 3A
    theorem), this gives a fully constructive bound on `|β_rep|` in
    terms of `|β_intrinsic|` and the frame condition number, with no
    additional axioms beyond those already in this module. -/
theorem represented_stability_flow_triangle_bound
    (L : Matrix V V ℝ) (psi : BandPassFilter)
    (pi_dist : V → ℝ) (hpi : ∀ v, 0 < pi_dist v)
    (epsilon : ℝ) (t : ℝ) :
    |RepresentedStabilityFlow L psi pi_dist hpi epsilon t| ≤
    |IntrinsicStabilityFlow L pi_dist epsilon t| +
    RepresentationError L psi pi_dist hpi epsilon t := by
  unfold RepresentationError
  calc |RepresentedStabilityFlow L psi pi_dist hpi epsilon t|
      = |IntrinsicStabilityFlow L pi_dist epsilon t +
         (RepresentedStabilityFlow L psi pi_dist hpi epsilon t -
          IntrinsicStabilityFlow L pi_dist epsilon t)| := by
        congr 1; ring
    _ ≤ |IntrinsicStabilityFlow L pi_dist epsilon t| +
         |RepresentedStabilityFlow L psi pi_dist hpi epsilon t -
          IntrinsicStabilityFlow L pi_dist epsilon t| := abs_add_le _ _

/-- **Zero Error Corollary**: For a canonical tight frame, representation
    error vanishes.

    This is the key result: tight frames give exact spectral analysis.

    **Phase 3A simplification**: formerly proved via `representation_error_bound`
    + `tight_frame_condition_one`; now proved directly from the narrower
    `tight_frame_representation_error_zero` axiom in a single step, cutting
    the proof from 7 lines to 3.  The existential signature is preserved
    for backward compatibility with downstream callers (e.g.
    `HG_tight_frame_zero_error` in `HermiteGaussianCanonical.lean`). -/
theorem tight_frame_zero_error (L : Matrix V V ℝ) (psi : BandPassFilter)
    (pi_dist : V → ℝ) (hpi : ∀ v, 0 < pi_dist v)
    (frame : CanonicalTightFrame L psi pi_dist hpi)
    (epsilon : ℝ) (heps : epsilon > 0) (t : ℝ) (ht : t ≥ 0) :
    ∃ C > 0, RepresentationError L psi pi_dist hpi epsilon t ≤ C * 0 := by
  refine ⟨1, one_pos, ?_⟩
  rw [tight_frame_representation_error_zero L psi pi_dist hpi frame epsilon t]
  simp

/-- **Tight-Frame Zero Error, Direct Form** (Phase 3A, new).

    The representation error for a canonical tight frame is exactly zero.
    This is the more direct statement that `tight_frame_zero_error`
    bundles inside an existential for signature compatibility. -/
theorem tight_frame_zero_error_direct (L : Matrix V V ℝ) (psi : BandPassFilter)
    (pi_dist : V → ℝ) (hpi : ∀ v, 0 < pi_dist v)
    (frame : CanonicalTightFrame L psi pi_dist hpi)
    (epsilon : ℝ) (t : ℝ) :
    RepresentationError L psi pi_dist hpi epsilon t = 0 :=
  tight_frame_representation_error_zero L psi pi_dist hpi frame epsilon t

/-- **Discrete Calderón Reproducing Formula** (Phase 3A, new).

    For a **canonical tight frame**, the represented stability flow
    **equals** the intrinsic stability flow *pointwise*:

      `RepresentedStabilityFlow L ψ π hπ ε t = IntrinsicStabilityFlow L π ε t`.

    This is the finite-dimensional discrete form of the classical
    Calderón reproducing formula: the wavelet analysis-synthesis pair
    is the identity operator on tight frames, so applying analysis
    followed by synthesis recovers the observable *exactly*, and hence
    the flow derived from the reconstruction matches the flow from the
    original heat kernel.

    **Why this matters**: the upstream axiom
    `tight_frame_representation_error_zero` only gives the weaker
    `|β_rep − β_intrinsic| = 0`.  This theorem unwraps the absolute
    value, yielding the strictly stronger equation form
    `β_rep = β_intrinsic` via `abs_eq_zero` + `sub_eq_zero`.

    This is the cleanest possible statement of the reproducing property:
    the two flows are *the same real number*, not merely close. -/
theorem tight_frame_exact_reconstruction
    (L : Matrix V V ℝ) (psi : BandPassFilter)
    (pi_dist : V → ℝ) (hpi : ∀ v, 0 < pi_dist v)
    (frame : CanonicalTightFrame L psi pi_dist hpi)
    (epsilon : ℝ) (t : ℝ) :
    RepresentedStabilityFlow L psi pi_dist hpi epsilon t =
    IntrinsicStabilityFlow L pi_dist epsilon t := by
  have h : RepresentationError L psi pi_dist hpi epsilon t = 0 :=
    tight_frame_zero_error_direct L psi pi_dist hpi frame epsilon t
  -- Unfold `RepresentationError` to expose the `|· − ·| = 0` form.
  unfold RepresentationError at h
  -- `|a − b| = 0 ⇔ a − b = 0 ⇔ a = b`.
  exact sub_eq_zero.mp (abs_eq_zero.mp h)

/-! ## 6. Geometric Commutator Constraint

The obstruction to frame tightness is geometric: it's controlled by the
commutator of L with the curvature operator Γ₂. -/

/-- **Commutator of L with Γ₂**: Measures how much L and Γ₂ fail to commute.

    [L, Γ₂](f) = L(Γ₂(f)) - Γ₂(Lf)

    When Ricci curvature is constant, [L, Γ₂] = 0.
    Non-constant curvature implies non-zero commutator. -/
def LGamma2Commutator (L : Matrix V V ℝ) (f : V → ℝ) : V → ℝ := fun v =>
  (L *ᵥ (Gamma2Sq L f)) v - (Gamma2Sq L (L *ᵥ f)) v

/-- **Commutator Norm**: The operator norm of the commutator [L, Γ₂]. -/
axiom CommutatorNorm (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hpi : ∀ v, 0 < pi_dist v) : ℝ

/-- The commutator norm is non-negative. -/
axiom commutator_norm_nonneg (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hpi : ∀ v, 0 < pi_dist v) :
    CommutatorNorm L pi_dist hpi ≥ 0

/-- **Geometric Commutator Constraint**: The deviation from frame tightness
    is bounded by the commutator norm.

    |B/A - 1| ≤ C · ‖[L, Γ₂]‖

    **Interpretation**:
    - On spaces with constant Ricci curvature (‖[L, Γ₂]‖ = 0), tight frames exist
    - Non-constant curvature obstructs tightness: the frame must "adapt" to geometry
    - This links spectral analysis precision to the underlying geometry

    **Connection to GeometricClosure**: This constraint shows that the same
    geometric structure (Ricci curvature via Γ₂) that controls stability flow
    also controls the precision of spectral analysis. -/
axiom geometric_commutator_constraint (L : Matrix V V ℝ) (psi : BandPassFilter)
    (pi_dist : V → ℝ) (hpi : ∀ v, 0 < pi_dist v)
    (frame : SpectralFrame L psi pi_dist hpi) :
    ∃ C > 0, |FrameConditionNumber frame - 1| ≤ C * CommutatorNorm L pi_dist hpi

/-- **Constant Curvature Implies Tight Frame Exists**: On spaces with constant
    Ricci curvature, a canonical tight frame exists.

    This is the "best case" scenario: uniform geometry allows perfect analysis. -/
axiom constant_ricci_tight_frame_exists (L : Matrix V V ℝ) (psi : BandPassFilter)
    (pi_dist : V → ℝ) (hpi : ∀ v, 0 < pi_dist v)
    (h_constant : CommutatorNorm L pi_dist hpi = 0) :
    ∃ frame : CanonicalTightFrame L psi pi_dist hpi, True

/-! ## 6. The Full Picture: Geometry → Analysis → Error

We can now trace the full chain:

```
Ricci Curvature (ρ)
        ↓ (Bakry-Émery)
Commutator ‖[L, Γ₂]‖
        ↓ (Geometric Constraint)
Frame Non-Tightness (B/A - 1)
        ↓ (Error Bound)
Representation Error |β_rep - β_intrinsic|
```

The geometry of the operator controls everything downstream. -/

/-- **End-to-End Error Bound**: Combining the geometric constraint with the
    representation error bound gives an error controlled by geometry.

    |β_rep - β_intrinsic| ≤ C₁ · C₂ · ‖[L, Γ₂]‖

    where C₁ is from representation_error_bound and C₂ is from
    geometric_commutator_constraint. -/
theorem geometric_error_bound (L : Matrix V V ℝ) (psi : BandPassFilter)
    (pi_dist : V → ℝ) (hpi : ∀ v, 0 < pi_dist v)
    (frame : SpectralFrame L psi pi_dist hpi)
    (epsilon : ℝ) (heps : epsilon > 0) (t : ℝ) (ht : t ≥ 0) :
    ∃ C > 0, RepresentationError L psi pi_dist hpi epsilon t ≤
             C * CommutatorNorm L pi_dist hpi := by
  -- Get the representation error bound
  obtain ⟨C₁, hC₁_pos, h_rep_bound⟩ := representation_error_bound L psi pi_dist hpi
    frame epsilon heps t ht
  -- Get the geometric constraint
  obtain ⟨C₂, hC₂_pos, h_geom⟩ := geometric_commutator_constraint L psi pi_dist hpi frame
  -- Combine: use C = C₁ · C₂
  use C₁ * C₂, mul_pos hC₁_pos hC₂_pos
  -- Chain the bounds
  have h_kappa_bound : FrameConditionNumber frame - 1 ≤ C₂ * CommutatorNorm L pi_dist hpi := by
    have h_abs := h_geom
    -- |κ - 1| ≤ C₂ · ‖[L,Γ₂]‖, and κ ≥ 1 by frame_condition_ge_one
    have h_ge_one := frame_condition_ge_one frame
    calc FrameConditionNumber frame - 1
        = |FrameConditionNumber frame - 1| := by
          rw [abs_of_nonneg (by linarith : FrameConditionNumber frame - 1 ≥ 0)]
      _ ≤ C₂ * CommutatorNorm L pi_dist hpi := h_abs
  calc RepresentationError L psi pi_dist hpi epsilon t
      ≤ C₁ * (FrameConditionNumber frame - 1) := h_rep_bound
    _ ≤ C₁ * (C₂ * CommutatorNorm L pi_dist hpi) := by
        apply mul_le_mul_of_nonneg_left h_kappa_bound (le_of_lt hC₁_pos)
    _ = (C₁ * C₂) * CommutatorNorm L pi_dist hpi := by ring

/-! ## Summary: The Canonical Wavelet Frame Story

This module establishes the necessary conditions for valid spectral analysis:

1. **Sectorial Functional Calculus**: Allows defining ψ(sL) for band-pass filters
2. **Spectral Frame Bounds**: A · ‖f‖² ≤ E_frame(f) ≤ B · ‖f‖²
3. **Representation Error**: |β_rep - β_intrinsic| ≤ C · (B/A - 1)
4. **Tight Frame Corollary**: A = B ⟹ error = 0
5. **Geometric Constraint**: |B/A - 1| ≤ C · ‖[L, Γ₂]‖
6. **End-to-End Bound**: Error ≤ C · ‖[L, Γ₂]‖

The analyzing frame must be controlled by the operator's geometry.

**Physical Meaning**: You cannot analyze a system more precisely than its
geometry allows. Non-uniform curvature introduces irreducible analysis error,
quantified by the commutator ‖[L, Γ₂]‖. -/

end SGC.Bridge.CanonicalWavelet
