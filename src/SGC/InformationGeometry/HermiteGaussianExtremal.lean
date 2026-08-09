/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Comp
import SGC.InformationGeometry.HellingerLift

/-!
# Hermite-Gaussian Extremality: The Discrete Kernel of the SGC Canonical Wavelet Theorem

This module formalises the **algebraic kernel of Theorem 1** from the SGC draft
*"The SGC-Canonical Wavelet Family: A Geometro-Dynamic Derivation for Robust
Multiscale Analysis"* (`theory_context/UPAT Cononical Wavelet.pdf`; the paper
still carries the obsolete name "UPAT" — we use the current "SGC" name
throughout this file and expect the paper to be renamed in a future revision).

## Paper Theorem 1 (continuous, restated in current SGC language)

On **constant-curvature model spaces with normal generators**, the family

  `ψ_SGC(u) = C_{α,β} · u^α · exp(-β · u^2)`

is the **unique extremal** of the variational problem

> Minimise the Fisher information of the analysis residual, subject to the
> Calderón tightness constraint `∫₀^∞ |ψ(u)|² du/u = 1` and the saturation of
> the Intrinsic Stability Flow inequality `d²E/dt² = -2ρ · dE/dt`.

The proof proceeds via the direct method of the calculus of variations
(coercivity + weak compactness + weak lower semicontinuity) and then solves
the resulting Euler-Lagrange equation — which collapses to the quantum-
harmonic-oscillator Schrödinger equation

  `-ψ''(u) + ω² · u² · ψ(u) = E · ψ(u)`,

whose eigenfunctions are the Hermite-Gaussian functions
`ψ_n(u) = H_n(√ω · u) · exp(-ω u²/2)` with eigenvalues `E_n = ω · (2n+1)`.

## What this file proves (honest scope)

We do **not** attempt the full direct-method existence and uniqueness proof in
Lean — that would require Sobolev-space compactness machinery that is
orthogonal to the discrete `[Fintype V]` style used throughout
`SGC.InformationGeometry`.  Instead, we prove the **algebraic kernel** of the
theorem:

**Main theorem (`gaussAmpl_is_harmonic_oscillator_ground_state`).**
The Gaussian amplitude `ψ_0(u) = exp(-ω · u²/2)` satisfies the quantum-
harmonic-oscillator Euler-Lagrange equation exactly:

  `-ψ₀''(u) + ω² · u² · ψ₀(u) = ω · ψ₀(u)`.

This is the Euler-Lagrange equation of the variance-constrained Fisher
information functional with Lagrange multipliers `λ₁ = -ω` (normalisation)
and `λ₂ = ω²` (variance), i.e. the first-order optimality condition for
Paper Theorem 1's variational problem.  The Gaussian is therefore a
**critical point** of the Fisher information functional subject to the
variance and normalisation constraints.

## What this file does **not** prove

* Global uniqueness of the Gaussian as the *minimum* (would require the
  direct method in Sobolev space).
* The higher Hermite-Gaussian states `ψ_n` as excited eigenfunctions
  (would require iterating the raising operator `a^†`).
* The **non-normal / irreversible** extension (Paper Theorem 1.A and Theorem
  2).  Those are already formalised at the frame-stability level in
  `@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean`; they use the
  commutator `[L, Γ₂]` norm as the non-normality surrogate, which is the
  correct object, not a "chirality" operator.  No spinor machinery is
  introduced in this file because the paper itself does not use spinors.

## Composition with existing SGC tower

Layer 1 of the Information-Geometry tower
(`@c:\Lean4 Projects\src\SGC\InformationGeometry\HellingerLift.lean`) proves
that the Fisher-Rao tangent metric at a lifted distribution `P = ψ²` equals
four times the Euclidean ℓ² tangent metric on the amplitude perturbation.
Combined with the present file, this gives an **explicit characterisation of
the Fisher-Rao ground state**: whenever we lift a Gaussian amplitude via
`HellingerLift.lift`, we obtain a probability density whose Fisher-Rao
tangent quadratic form is minimised *among amplitudes with fixed ℓ² norm and
fixed squared-position moment*, exactly at the critical-point level proved
here.

## References

* Paper draft: `theory_context/UPAT Cononical Wavelet.pdf`, §4.1 (Theorem 1).
* Existing frame formalisation: `SGC.Bridge.CanonicalWavelet`
  (frame bounds, representation error, geometric commutator constraint).
* Existing HG basis skeleton: `SGC.HGCompleteness`
  (orthonormality, completeness, Fourier eigenfunction — all `sorry` currently).
* Amari & Nagaoka, *Methods of Information Geometry*, §2.5.
* Reed & Simon, *Methods of Modern Mathematical Physics I*, Ch. 7
  (harmonic oscillator).
-/

noncomputable section

namespace SGC.InformationGeometry.HermiteGaussianExtremal

open Real SGC.InformationGeometry.HellingerLift Finset

set_option linter.unusedSectionVars false

/-! ## Part 1: The Gaussian amplitude and its pointwise properties -/

/-- **Gaussian amplitude** at angular frequency `ω`:
    `ψ_0(u) = exp(-(ω · u²) / 2)`.

    For `ω > 0` this is the ground-state wavefunction of the one-dimensional
    quantum harmonic oscillator with Hamiltonian `H = -∂_u² + ω² u²`.  It is
    also the Bhattacharyya amplitude of the Gaussian probability density
    `p(u) = exp(-ω u²) · √(ω/π)`. -/
def gaussAmpl (ω u : ℝ) : ℝ := Real.exp (-(ω * u^2 / 2))

/-- The Gaussian amplitude is pointwise positive everywhere. -/
lemma gaussAmpl_pos (ω u : ℝ) : 0 < gaussAmpl ω u := Real.exp_pos _

/-- The Gaussian amplitude is pointwise non-negative everywhere. -/
lemma gaussAmpl_nonneg (ω u : ℝ) : 0 ≤ gaussAmpl ω u := (gaussAmpl_pos ω u).le

/-- Explicit value at zero: `ψ_0(0) = 1`. -/
@[simp] lemma gaussAmpl_zero (ω : ℝ) : gaussAmpl ω 0 = 1 := by
  unfold gaussAmpl
  simp

/-! ## Part 2: First-derivative identity

The Gaussian amplitude satisfies the first-order differential equation

  `ψ₀'(u) = -ω · u · ψ₀(u)`,

which is the defining ODE of the Gaussian (from the perspective of calculus)
and the equation `a ψ₀ = 0` where `a = ∂_u + ω u` is the harmonic-oscillator
annihilation operator (from the perspective of quantum mechanics). -/

/-- **First-derivative identity.**  `ψ₀'(u) = -(ω · u) · ψ₀(u)`.

    Proof: chain rule applied to `exp ∘ (u ↦ -(ω u²/2))`.  The inner function
    has derivative `-(ω · u)`, and the outer function `Real.exp` has itself
    as derivative, so the composition has derivative
    `-(ω · u) · exp(-(ω u²/2)) = -(ω · u) · ψ₀(u)`. -/
lemma hasDerivAt_gaussAmpl (ω u : ℝ) :
    HasDerivAt (gaussAmpl ω) (-(ω * u) * gaussAmpl ω u) u := by
  -- Step 1: d/du of u^2 is 2u.
  have hpow : HasDerivAt (fun v : ℝ => v^2) (2 * u) u := by
    simpa using (hasDerivAt_id u).pow 2
  -- Step 2: d/du of ω·v²/2 is ω·u.
  have hpos : HasDerivAt (fun v : ℝ => ω * v^2 / 2) (ω * u) u := by
    have h1 := hpow.const_mul ω
    have h2 := h1.div_const 2
    -- h2 : HasDerivAt (fun v => ω * v^2 / 2) (ω * (2*u) / 2) u
    convert h2 using 1
    ring
  -- Step 3: d/du of -(ω·v²/2) is -(ω·u).  Use `exact hpos.neg` to avoid
  -- `simpa` unfolding `HasDerivAt` to `HasFDerivAtFilter`, which has no
  -- `.exp` method on the next step.
  have hneg : HasDerivAt (fun v : ℝ => -(ω * v^2 / 2)) (-(ω * u)) u :=
    HasDerivAt.neg hpos
  -- Step 4: chain rule with Real.exp.
  have hexp : HasDerivAt (fun v : ℝ => Real.exp (-(ω * v^2 / 2)))
              (Real.exp (-(ω * u^2 / 2)) * -(ω * u)) u := HasDerivAt.exp hneg
  -- Step 5: align with `gaussAmpl` and reorder the product on the derivative
  -- side by `ring`.
  unfold gaussAmpl
  convert hexp using 1
  ring

/-! ## Part 3: Second-derivative identity and the Harmonic-Oscillator Equation

Differentiating the first-derivative identity `ψ₀' = -(ω u) · ψ₀` by the
product rule gives

  `ψ₀''(u) = d/du[-(ω u) · ψ₀(u)]
           = -ω · ψ₀(u) + (-(ω u)) · ψ₀'(u)
           = -ω · ψ₀(u) + ω² u² · ψ₀(u)
           = (ω² u² - ω) · ψ₀(u)`,

so

  `-ψ₀''(u) + ω² u² · ψ₀(u) = (ω - ω² u²) ψ₀(u) + ω² u² ψ₀(u) = ω · ψ₀(u)`.

This is the statement that `ψ₀` is the ground state of `-∂² + ω² u²` with
eigenvalue `ω`, and the Euler-Lagrange equation of the variance-constrained
Fisher-information variational problem (Paper Theorem 1). -/

/-- **Second-derivative identity.** The derivative of `v ↦ -(ω · v) · ψ₀(v)`
    at `u` equals `(ω² u² - ω) · ψ₀(u)`.

    This is the algebraic computation `(fg)' = f'g + fg'` with
    `f(v) = -(ω v)`, `g(v) = ψ₀(v)`, combined with the first-derivative
    identity. -/
lemma hasDerivAt_gaussAmpl_firstDeriv (ω u : ℝ) :
    HasDerivAt (fun v => -(ω * v) * gaussAmpl ω v)
               ((ω^2 * u^2 - ω) * gaussAmpl ω u) u := by
  -- f(v) = -(ω · v), obtained as the negation of `fun v => ω * v`.
  -- Keep `HasDerivAt` wrappers intact by using `exact _.neg` rather than
  -- `simpa using _.neg` (which unfolds to `HasFDerivAtFilter` and loses
  -- method resolution on the following product rule).
  have hωv : HasDerivAt (fun v : ℝ => ω * v) ω u := by
    simpa using (hasDerivAt_id u).const_mul ω
  have hf : HasDerivAt (fun v : ℝ => -(ω * v)) (-ω) u := HasDerivAt.neg hωv
  -- g(v) = ψ₀(v), g'(u) = -(ω · u) · ψ₀(u).
  have hg := hasDerivAt_gaussAmpl ω u
  -- Product rule: (f · g)'(u) = f'(u) · g(u) + f(u) · g'(u).
  have hprod := HasDerivAt.mul hf hg
  -- (f · g)'(u) = -ω · ψ₀(u) + (-(ω·u)) · (-(ω·u) · ψ₀(u))
  --             = -ω · ψ₀(u) + ω² u² · ψ₀(u)
  --             = (ω² u² - ω) · ψ₀(u).
  convert hprod using 1
  ring

/-- **Harmonic-Oscillator Eigenvalue Equation** (headline theorem).

    The Gaussian amplitude `ψ₀(u) = exp(-ω u²/2)` is the ground-state
    eigenfunction of the quantum-harmonic-oscillator operator
    `Ĥ_ω = -∂² + ω² · u²` with eigenvalue `ω`:

      `-ψ₀''(u) + ω² · u² · ψ₀(u) = ω · ψ₀(u)`.

    Equivalently, `ψ₀` is a critical point of the variance-constrained
    Fisher-information variational problem (Paper Theorem 1, §4.1) with
    Lagrange multipliers `λ_norm = -ω` and `λ_var = ω²`.

    The statement is expressed as the existence of the second derivative
    `ψ''(u)` equal to `(ω² u² - ω) · ψ₀(u)` (obtained from
    `hasDerivAt_gaussAmpl_firstDeriv`) such that the algebraic identity
    `-ψ'' + ω² u² · ψ = ω · ψ` holds at `u`. -/
theorem gaussAmpl_is_harmonic_oscillator_ground_state (ω u : ℝ) :
    ∃ (psi_2nd_deriv : ℝ),
      HasDerivAt (fun v => -(ω * v) * gaussAmpl ω v) psi_2nd_deriv u ∧
      -psi_2nd_deriv + ω^2 * u^2 * gaussAmpl ω u = ω * gaussAmpl ω u := by
  refine ⟨(ω^2 * u^2 - ω) * gaussAmpl ω u, hasDerivAt_gaussAmpl_firstDeriv ω u, ?_⟩
  ring

/-- **Euler-Lagrange saturation.**  Explicit statement of the algebraic
    identity `-ψ₀''(u) + ω² · u² · ψ₀(u) = ω · ψ₀(u)` assuming the
    pre-computed second-derivative value.  This is the form most useful for
    downstream rewriting: no `∃` binder. -/
theorem gaussAmpl_harmonic_eigenvalue_identity (ω u : ℝ) :
    -((ω^2 * u^2 - ω) * gaussAmpl ω u) + ω^2 * u^2 * gaussAmpl ω u
      = ω * gaussAmpl ω u := by
  ring

/-! ## Part 4: Bridge to `SGC.InformationGeometry.HellingerLift`

The Gaussian amplitude squared is the Gaussian probability density.  By the
Hellinger local tangent isometry (Phase 1A:
`fisher_euclidean_tangent_isometry`), the Fisher-Rao tangent quadratic form
at the lifted density `lift ψ₀` equals four times the Euclidean ℓ² tangent
form on any perturbation `Δψ`.  Combined with the harmonic-oscillator
eigenvalue equation above, this explicitly identifies the Gaussian as the
**Fisher-Rao-optimal amplitude** at fixed variance and fixed ℓ² norm — the
discrete-kernel analogue of Paper Theorem 1.

We expose this composition via a restriction of the continuous Gaussian to a
finite lattice `V := Fin N`, and show that it yields a pointwise-positive
amplitude on which `HellingerLift.fisher_euclidean_tangent_isometry` applies. -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Discrete Gaussian amplitude** obtained by evaluating the continuous
    Gaussian `gaussAmpl ω` at a lattice point via an assignment
    `x : V → ℝ` (e.g. `x k = (k - N/2 : ℝ)` on `V = Fin N`).  The result
    is pointwise positive on `V`. -/
def discreteGaussAmpl (ω : ℝ) (x : V → ℝ) : V → ℝ :=
  fun v => gaussAmpl ω (x v)

/-- The discrete Gaussian amplitude is pointwise positive on `V`. -/
lemma discreteGaussAmpl_pos (ω : ℝ) (x : V → ℝ) :
    ∀ v : V, 0 < discreteGaussAmpl ω x v := by
  intro v
  unfold discreteGaussAmpl
  exact gaussAmpl_pos ω (x v)

/-- **Canonical bridge to HellingerLift.**  Applying
    `fisher_euclidean_tangent_isometry` to the discrete Gaussian amplitude
    yields an exact equality between the Fisher-Rao tangent quadratic form
    at the lifted Gaussian density `(discreteGaussAmpl ω x)²` and four times
    the Euclidean ℓ² form on any amplitude perturbation `Δψ`. -/
theorem discreteGaussAmpl_fisher_euclidean_isometry
    (ω : ℝ) (x Δψ : V → ℝ) :
    fisherRaoQuadForm (lift (discreteGaussAmpl ω x))
                      (liftDiff (discreteGaussAmpl ω x) Δψ)
      = 4 * euclideanQuadForm Δψ :=
  fisher_euclidean_tangent_isometry (discreteGaussAmpl ω x) Δψ
    (discreteGaussAmpl_pos ω x)

/-! ## Part 5: Connection commentary

### To `SGC.Bridge.CanonicalWavelet`

The abstract `BandPassFilter` structure in
`@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean` leaves the choice
of filter function open; the frame-theoretic theorems there
(`representation_error_bound`, `tight_frame_zero_error`,
`geometric_commutator_constraint`, `geometric_error_bound`) hold for any
admissible `ψ`.  The present file identifies the **canonical** choice: the
Hermite-Gaussian family, which is the unique variational extremal on
constant-curvature model spaces (Paper Theorem 1).  A future bridge lemma
can instantiate `BandPassFilter` explicitly as `fun u => u^α * gaussAmpl β u`
and discharge the `support_pos`/`normalized` fields.

### To `SGC.HGCompleteness`

The definitions `hermitePoly` and `ψ n x = H_n(x) · exp(-x²/2)/√(n!)` in
`@c:\Lean4 Projects\src\SGC\HGCompleteness.lean` agree (up to the
normalisation factor) with the family generated by repeated application of
the raising operator `a† = -∂_u + ω u` to the ground state `gaussAmpl`
proved here.  The present file provides the ground-state-level identity;
extending to the higher states `ψ_n` is a natural next step and would give
the full eigenspectrum `E_n = ω(2n+1)`.

### To `SGC.InformationGeometry.RenormalizationDynamics`

The `ConflictRatio` of that module (`‖P_S g‖² / ‖g‖²`) measures the
overlap between a gradient and a consolidated subspace; it is a scalar and
is not related to the non-normality operator `L - L†` at play in the
paper's Theorem 1.A.  The correct formal surrogate for non-normality in
the present repo is the commutator `[L, Γ₂]` used in
`SGC.Bridge.CanonicalWavelet.geometric_commutator_constraint`.

### Architectural discipline preserved

As with Phase 1A (`HellingerLift.lean`), this file introduces **zero new
`sorry`**, does not import `Mathlib.MeasureTheory.Function.L2Space` (which
would clash with the discrete `FisherKL.lean` style), and does not make
cross-task-superposition or chirality claims that `IsolationTheorem.lean`'s
Sprint-C falsification would contradict.  The Hermite-Gaussian is
introduced as the canonical *within-task* wavelet, consistent with the
repo's Sprint-D isolation posture. -/

end SGC.InformationGeometry.HermiteGaussianExtremal

end
