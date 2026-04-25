# Phase 2C — Hermite-Gaussian Ladder Algebra

**Date:** April 25, 2026
**Sprint:** post-Phase-2B, algebraic ladder structure for the canonical wavelet tower
**Status:** delivered, zero new `sorry`, builds clean under `lake build`

Phase 2C extends Phase 2A's ground-state Euler-Lagrange identity to the full
algebraic ladder-operator structure of the Hermite-Gaussian family — without
pulling in measure-theoretic infrastructure. It also formally **declines** to
touch the broken `@c:\Lean4 Projects\src\SGC\HGCompleteness.lean` skeleton, with
a documented reason.

## Deliverable summary

| Artifact | Status |
|---|---|
| `@c:\Lean4 Projects\src\SGC\InformationGeometry\HermiteGaussianLadder.lean` (new, ~395 lines) | Compiles clean, **zero `sorry`**, zero new warnings |
| `@c:\Lean4 Projects\reports\PHASE_2C_HERMITE_GAUSSIAN_LADDER.md` | This file |

Verification commands:

```bash
lake build SGC.InformationGeometry.HermiteGaussianLadder
# ✔ [2027/2027] Built SGC.InformationGeometry.HermiteGaussianLadder (7.5s)

lake build SGC.Bridge.HermiteGaussianCanonical SGC.InformationGeometry.HermiteGaussianLadder \
           SGC.InformationGeometry.HermiteGaussianExtremal SGC.InformationGeometry.HellingerLift
# Build completed successfully (3085 jobs)  -- four-brick foundation builds together
```

## Why this is *not* a patch to `HGCompleteness.lean`

Reconnaissance turned up three reasons not to repair `HGCompleteness.lean` in
this sprint:

1. **The file does not compile** — two dead Mathlib import paths
   (`Mathlib.Analysis.SpecialFunctions.Polynomials.Chebyshev` was relocated to
   `.../Trigonometric/Chebyshev.lean`; `Mathlib.LinearAlgebra.Matrix.Spectrum`
   does not exist in this Mathlib revision).
2. **The file contains ~27 `sorry`s** scattered across *interdependent
   definitions* — `FisherMatrix`, `nullDirection`, `hgLift`'s `Fin` bounds,
   `PoissonBracket`, `measureOf`, `hgLift_standardized`'s μ and σ, etc. —
   not just the two theorems flagged by the external review.
3. **The momentum-recurrence statement currently in the file has a
   convention error.** It claims
   `d/dx ψ_n = √n · ψ_{n-1} − √(n+1) · ψ_{n+1}`, but for the probabilists'
   normalisation `ψ_n = He_n · e^{-x²/2}/√(n!)` the correct identity is the
   single-term `ψ'_n = -√(n+1) · ψ_{n+1}` (derived from
   `He'_n = n · He_{n-1}` together with the cross-recurrence
   `x · He_n = He_{n+1} + n · He_{n-1}`, which collapses the would-be first
   term).  Repairing this requires a convention audit before any proof can be
   attempted — proving the current statement would prove a *false* identity.

In addition, `HGCompleteness.lean` is **not imported by any other file** in
the repo (verified by `grep_search`), so its broken state blocks nothing.
Phase 2C is therefore the right granularity: build the clean foundation in a
new file and let a future, dedicated sprint repair `HGCompleteness.lean` by
*importing* from the new foundation rather than re-deriving inside its own
broken scaffolding.

## What Phase 2C proves

Located in `@c:\Lean4 Projects\src\SGC\InformationGeometry\HermiteGaussianLadder.lean`:

| Lemma / Theorem | Statement | Location |
|---|---|---|
| `hermitePoly` | `He_0 = 1`, `He_1 = x`, `He_{n+2} = x · He_{n+1} − (n+1) · He_n` | `:90-93` |
| `hermitePoly_zero`, `hermitePoly_one` | Trivial unfolding `@[simp]` lemmas | `:96-100` |
| `hermitePoly_succ_succ` | The defining recurrence as a named lemma | `:106-107` |
| `hermitePoly_mul_x` | **Cross-recurrence** `x · He_n = He_{n+1} + n · He_{n-1}` | `:117-128` |
| `hasDerivAt_hermitePoly_pair` | **Bundled derivative identity** for `(He_n, He_{n+1})` simultaneously, by induction | `:140-209` |
| `hasDerivAt_hermitePoly` | **`He'_n(x) = n · He_{n-1}(x)`** — first projection of the bundle | `:215-217` |
| `differentiableAt_hermitePoly` | Smoothness corollary | `:220-222` |
| `hermiteGaussianFn` | Unnormalized HG: `ψ_n = He_n · gaussAmpl(ω)` | `:233-234` |
| `hermiteGaussianFn_zero`, `_one` | Trivial unfolding | `:237-243` |
| `hasDerivAt_hermiteGaussianFn` | **Product-rule form** of the HG derivative | `:259-274` |
| `hasDerivAt_hermiteGaussianFn_ladder` | **Clean ladder form** at general ω | `:289-313` |
| `hasDerivAt_hermiteGaussianFn_unit` | **Creation identity** at ω=1: `ψ'_n = -He_{n+1} · g` | `:321-326` |
| `hermiteGaussianFn_x_mul` | **Position-multiplication** `x · ψ_n = ψ_{n+1} + n · ψ_{n-1}` | `:336-345` |
| `hermiteGaussianFn_lowering_unit` | **Annihilation identity** at ω=1: `(d/dx + x) ψ_n = n · ψ_{n-1}` | `:361-372` |

Total: 14 named results, all `zero sorry`, all built on Phase 2A
(`gaussAmpl` and its derivatives) plus standard Mathlib derivative API.

## The technical core: bundled-pair induction

The derivative identity `He'_n(x) = n · He_{n-1}(x)` is proved by an
**induction on a pair** rather than by strong induction. The invariant is

```
P(n) ≡  HasDerivAt (He n) (n · He (n-1) x) x
       ∧ HasDerivAt (He (n+1)) ((n+1) · He n x) x
```

The base case `P(0)` is trivial (`He'_0 = 0`, `He'_1 = 1`).
The step `P(k) → P(k+1)`:

* The first conjunct of `P(k+1)` is exactly the *second* conjunct of `P(k)`
  after a `Nat`-cast cleanup (since `(k+1) - 1 = k` definitionally).
* The second conjunct of `P(k+1)` is the genuinely new content. It uses the
  recurrence `He_{k+2} = x · He_{k+1} − (k+1) · He_k`, the product rule
  `(x · f)' = f + x · f'`, both inductive hypotheses simultaneously, and
  the cross-recurrence `x · He_k = He_{k+1} + k · He_{k-1}` (proved as
  `hermitePoly_mul_x`).

This avoids both `Nat.strong_induction` and any need to re-prove the
recurrence inside the induction.  The proof fits in ~70 lines of tactic
script with all the algebra handled by `ring`, `push_cast`, and a single
`linarith` for the cross-recurrence.

## Why this matters for the canonical-wavelet tower

| Layer | Theorem | File | Status |
|---|---|---|---|
| **0** | Chentsov metric uniqueness | `RenormalizationDynamics.lean` | axiomatised |
| **1** | Hellinger tangent isometry | `HellingerLift.lean` | **✅ zero `sorry`** |
| **2–3** | Fisher geometry + spectral | `FisherKL.lean`, `RenormalizationDynamics.lean` | axiomatised + proved |
| **4** | HG ground-state EL identity | `HermiteGaussianExtremal.lean` | **✅ zero `sorry`** |
| **4b** | Canonical wavelet frame | `CanonicalWavelet.lean` | axiomatised + proved |
| **4c** | HG `BandPassFilter` instantiation | `HermiteGaussianCanonical.lean` | **✅ zero `sorry`** |
| **4d** | HG ladder algebra (this phase) | `HermiteGaussianLadder.lean` | **✅ zero `sorry`** |
| 5 | HG L²-completeness / orthonormality | `HGCompleteness.lean` | broken (27 `sorry`s + dead imports + convention error) |

Layer 4d (Phase 2C) is the **algebraic spine** that connects the canonical
wavelet's *continuous* `α`-parameter (Layer 4c) to the *integer* `n`-parameter
of the harmonic-oscillator excited states.  When Layer 5 is repaired, its
`hg_momentum_recurrence` will be a corollary of `hermiteGaussianFn_lowering_unit`
together with the L² normalisation constant `1/√(n!)`.

## What still remains genuinely open

Documented honestly, not claimed as done:

1. **`HGCompleteness.lean` repair.** Three actions in sequence:
   * Replace the dead `Chebyshev` import (relocated; or remove — it is unused
     in the file).
   * Remove the dead `Matrix.Spectrum` import (unused).
   * Add `Mathlib.Analysis.Fourier.FourierTransform` (needed by
     `hg_fourier_eigenfunction`).
   * Audit and **correct** the convention of `hg_momentum_recurrence` to the
     single-term form.
   * Then attempt to discharge the remaining sorrys, importing from
     `HermiteGaussianLadder` for the algebraic content.
   Estimated scope: ~3–5 hours of careful Lean work, separate sprint.

2. **The full harmonic-oscillator eigenvalue equation for excited states**
   `-ψ''_n + ω² x² ψ_n = (2n+1) ω · ψ_n`.  This is the *physicists'*
   convention statement (with `H_n` and `e^{-x²/2}`).  For the *probabilists'*
   convention used here, the corresponding identity has an extra
   `n(n-1) · ψ_{n-2}` cross-term (computed in working notes).  Closing the
   physicists' form requires either a parallel `physicistsHermitePoly` or a
   conversion lemma `He_n(x) = 2^{-n/2} H_n(x/√2)`. Phase 2D candidate.

3. **`BandPassFilter.normalized` strengthening** to the actual Calderón
   condition `∫₀^∞ |ψ(u)|² du/u = 1`.  Requires `Mathlib.Analysis.SpecialFunctions.Gamma`
   and integration theory.  Phase 2E candidate.

4. **`geometric_commutator_constraint` and `constant_ricci_tight_frame_exists`**
   in `CanonicalWavelet.lean` remain axioms.  Discharging them requires
   pseudospectral machinery (paper §4.2). Future phase.

## Honest scope discipline maintained

Same posture as Phases 1A, 2A, 2B:

* No new axioms beyond Mathlib + Phase 2A.
* No spinor / chirality / Weyl-half machinery.  The paper is scalar; the
  formalisation stays scalar.
* No claims about excited-state eigenvalue equations — only the algebraic
  ladder structure that actually has a clean, convention-correct proof.
* No touching of broken files.  `HGCompleteness.lean` is left as-is with a
  documented repair plan.
* No fabricated "Mathlib has Hermite" claims — verified that this Mathlib
  revision has no `Hermite*.lean` files, so `hermitePoly` is built from
  scratch in this file (cleanly, in 3 lines).

## Artefacts

```
src/SGC/InformationGeometry/HermiteGaussianLadder.lean    (NEW, ~395 lines, zero sorry)
reports/PHASE_2C_HERMITE_GAUSSIAN_LADDER.md               (this file)
```

## Closing posture

Four bricks dry. The canonical-wavelet structural chain (1A → 2A → 2B) and
its algebraic spine (2C) all build together with zero `sorry` and zero new
warnings.

The Phase 2C delivery is honest about what it does *not* prove (the L²
orthonormality, the Calderón normalisation, the physicists'-convention
eigenvalue equation for excited states) and provides explicit, executable
plans for the future phases that would close those gaps.

Ready for whichever next phase the user prioritises:

* Phase 2D: physicists' Hermite + excited-state eigenvalue equation
  (~5 h Lean, builds directly on Phase 2C);
* Phase 2E: Calderón normalisation via `Real.Gamma` (~6 h Lean, requires
  measure theory imports);
* Phase 3: apply the Hellinger lift to close `AdiabaticInvariant.lean`'s
  `catastrophic_forgetting_prevention` sorry (~5 h Lean, builds on Phase 1A);
* `HGCompleteness.lean` repair (~3–5 h Lean, prerequisite for any Layer-5 work).
