/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic

/-!
# HellingerLift: The Local Tangent Isometry between Fisher-Rao and ℓ²

This module formalizes the **Bhattacharyya / Hellinger square-root embedding**:
the map `ψ ↦ ψ²` that sends a real amplitude on a finite state space to a
positive density.  The classical fact (Bhattacharyya 1943, Amari 1985,
Amari & Nagaoka 2000 §2.5 with α = 1/2) is that this map is a **local
Riemannian isometry** between

* the discrete Fisher-Rao metric on the probability simplex, and
* four times the Euclidean ℓ² metric on the unit sphere of amplitudes,

restricted to **tangent vectors at a positive interior point**.

## Honest Scope

**What this module proves.**  For any pointwise-positive amplitude
`ψ : V → ℝ` and any tangent perturbation `Δψ : V → ℝ`, the discrete
Fisher-Rao quadratic form evaluated at the lifted distribution `P = ψ²`
and the induced perturbation `ΔP = 2 · ψ · Δψ` equals exactly four
times the squared Euclidean norm of `Δψ`:

  Σ x, (2·ψ x·Δψ x)² / (ψ x)² = 4 · Σ x, (Δψ x)².

This is a pure algebraic identity, provable pointwise by `field_simp` + `ring`.

**What this module does NOT prove.**

* That the *amplitude space* is globally flat.  It is the unit sphere in
  `ℓ²(V)`, which has constant positive Gaussian curvature 1 — not zero.
  The "flatness" that appears in the theorem is only in the *ambient*
  ℓ² norm of *tangent vectors*; the underlying submanifold is spherical.
* That two amplitudes `ψ₁`, `ψ₂` from different tasks can be safely added.
  The unit sphere is not closed under addition; `ψ₁ + ψ₂` leaves the
  amplitude space.
* That this resolves catastrophic forgetting in a shared-weight architecture.
  See `SGC.ContinualLearning.IsolationTheorem` for the empirical falsification
  (Sprint C, April 2026) of the shared-weight superposition pattern, which
  the SGC team resolved by **isolated models per task** with sheaf
  consistency, not by a more clever metric.

This lemma is a *local* tool — a specialization of the general Fisher-Rao
machinery in `SGC.InformationGeometry.FisherKL` to the case where the
parametric family is `P_θ(x) = ψ_θ(x)²`.  It is the algebraic kernel for
any later Beck-Cohen / superstatistics bridge to non-extensive Tsallis
behaviour, but it does NOT itself license those bridges.

## Main Results

* `lift` — the Hellinger square-root embedding `ψ ↦ ψ²`.
* `liftDiff` — the linearised differential `(ψ, Δψ) ↦ 2·ψ·Δψ`.
* `fisherRaoQuadForm`, `euclideanQuadForm` — the discrete tangent quadratic
  forms on the simplex and on amplitude space.
* `hellinger_pointwise` — the pointwise algebraic identity
  `(2ab)² / a² = 4b²` for `a > 0`.
* `fisher_euclidean_tangent_isometry` (the headline theorem) — the
  summed version, an exact equality of quadratic forms on tangent space.
* `lift_pos`, `lift_sum_eq_one` — the lift of a positive amplitude is a
  positive density, and the lift of a unit-ℓ² amplitude is a probability
  distribution.

## References

* Bhattacharyya, A. (1943). "On a measure of divergence between two
  statistical populations defined by their probability distributions."
  *Bull. Calcutta Math. Soc.* **35**, 99–109.
* Amari, S. (1985). *Differential-Geometrical Methods in Statistics*.
  Lecture Notes in Statistics, Springer.
* Amari, S. & Nagaoka, H. (2000). *Methods of Information Geometry*,
  §2.5 (α-embeddings, the α = 1/2 / square-root case).
* Sprint C/D findings:
  `SGC.ContinualLearning.IsolationTheorem` (this repository).
-/

noncomputable section

namespace SGC.InformationGeometry.HellingerLift

open Finset Real BigOperators

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The Hellinger lift -/

/-- **The Hellinger lift** (Bhattacharyya square-root embedding):
    `lift ψ x = ψ(x)²`.

    This sends a real amplitude to a positive density.  When `ψ` has unit
    `ℓ²` norm — i.e. `Σ ψ² = 1` — the result is a probability distribution
    (see `lift_sum_eq_one`). -/
def lift (ψ : V → ℝ) : V → ℝ := fun x => (ψ x)^2

/-- The lift of a pointwise-positive amplitude is a pointwise-positive density. -/
lemma lift_pos {ψ : V → ℝ} (hψ : ∀ x, 0 < ψ x) (x : V) : 0 < lift ψ x := by
  unfold lift
  exact pow_pos (hψ x) 2

/-- The lift of a pointwise-nonnegative amplitude is pointwise-nonnegative. -/
lemma lift_nonneg (ψ : V → ℝ) (x : V) : 0 ≤ lift ψ x := by
  unfold lift
  exact sq_nonneg _

/-- If `ψ` has unit `ℓ²` norm, its lift sums to one — i.e. it is a probability
    distribution on `V`. -/
lemma lift_sum_eq_one {ψ : V → ℝ} (h : ∑ x, (ψ x)^2 = 1) :
    ∑ x, lift ψ x = 1 := by
  unfold lift
  exact h

/-! ## 2. The lifted tangent differential

For an infinitesimal amplitude perturbation `Δψ` at base point `ψ`,
`(ψ + Δψ)² = ψ² + 2·ψ·Δψ + (Δψ)²`.  Dropping the second-order
`(Δψ)²` term gives the linearised differential `ΔP = 2·ψ·Δψ`.
This is exactly the tangent map of `lift` at `ψ`.
-/

/-- **The lifted differential**: the tangent map of `lift` at amplitude `ψ`,
    evaluated on perturbation `Δψ`.  Linear in `Δψ`. -/
def liftDiff (ψ Δψ : V → ℝ) : V → ℝ := fun x => 2 * ψ x * Δψ x

/-! ## 3. The two tangent quadratic forms -/

/-- **Discrete Fisher-Rao tangent quadratic form** at base distribution `P`
    on a perturbation `ΔP`:

    Σ x, (ΔP x)² / (P x).

    This is the squared length of `ΔP` in the Fisher-Rao metric at `P`, in
    the discrete case.  It diverges if `P` has a zero coordinate at which
    `ΔP` is non-zero, which is why our isometry hypothesis requires
    `ψ x > 0` pointwise. -/
def fisherRaoQuadForm (P ΔP : V → ℝ) : ℝ :=
  ∑ x, (ΔP x)^2 / P x

/-- **Euclidean ℓ² tangent quadratic form** on amplitude perturbations:

    Σ x, (Δψ x)². -/
def euclideanQuadForm (Δψ : V → ℝ) : ℝ :=
  ∑ x, (Δψ x)^2

/-! ## 4. The pointwise identity -/

/-- **Pointwise Hellinger identity** — the algebraic kernel of the metric
    isometry.  For any positive `a` and any real `b`,

      (2 · a · b)² / a² = 4 · b².

    Provable by `field_simp; ring` because the `a²` factors cancel exactly. -/
lemma hellinger_pointwise (a b : ℝ) (ha : 0 < a) :
    (2 * a * b)^2 / a^2 = 4 * b^2 := by
  have h_ne : a^2 ≠ 0 := pow_ne_zero 2 (ne_of_gt ha)
  field_simp
  ring

/-! ## 5. The local tangent isometry (main theorem) -/

/-- **Hellinger Local Tangent Isometry** — the headline theorem.

    For any pointwise-positive amplitude `ψ : V → ℝ` and any tangent
    perturbation `Δψ : V → ℝ`, the discrete Fisher-Rao tangent quadratic
    form at the lifted distribution `lift ψ` evaluated on the lifted
    differential `liftDiff ψ Δψ` equals exactly four times the Euclidean
    `ℓ²` quadratic form on `Δψ`:

      Σ x, (2·ψ x·Δψ x)² / (ψ x)²  =  4 · Σ x, (Δψ x)².

    **Honest scope.**  This is a *tangent-vector identity at a single base
    point* `ψ`.  It does NOT say the amplitude space is globally flat
    (it is the unit sphere) nor that amplitudes from different tasks may
    be linearly added (the sphere is not closed under addition).  See the
    module docstring.

    **Use case.**  Any time the discrete Fisher information at `p = ψ²`
    is needed, this lemma replaces the curved `Σ (ΔP)² / P` form with the
    flat `4 · Σ (Δψ)²` form, *at the level of tangent vectors only*.  The
    consequence on the *manifold* level is that distance in Fisher-Rao
    equals twice ℓ²-distance on the amplitude sphere — see
    `fisher_rao_tangent_eq_four_euclidean` below for the explicit form. -/
theorem fisher_euclidean_tangent_isometry
    (ψ Δψ : V → ℝ) (hψ : ∀ x, 0 < ψ x) :
    fisherRaoQuadForm (lift ψ) (liftDiff ψ Δψ) = 4 * euclideanQuadForm Δψ := by
  unfold fisherRaoQuadForm lift liftDiff euclideanQuadForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  exact hellinger_pointwise (ψ x) (Δψ x) (hψ x)

/-- Alias of `fisher_euclidean_tangent_isometry` with a name that emphasises
    the equality of tangent norm-squared.  Useful when downstream rewriting
    needs an `=` rather than the `≤` of `fisher_rao_tangent_le_four_euclidean`. -/
theorem fisher_rao_tangent_eq_four_euclidean
    (ψ Δψ : V → ℝ) (hψ : ∀ x, 0 < ψ x) :
    fisherRaoQuadForm (lift ψ) (liftDiff ψ Δψ) = 4 * euclideanQuadForm Δψ :=
  fisher_euclidean_tangent_isometry ψ Δψ hψ

/-- **Bound corollary.**  The Fisher-Rao tangent norm-squared at a lifted
    distribution is bounded above by four times the Euclidean norm-squared.
    The bound is tight (equality holds) — this form is convenient for
    downstream rewriting when only an upper bound is required. -/
theorem fisher_rao_tangent_le_four_euclidean
    (ψ Δψ : V → ℝ) (hψ : ∀ x, 0 < ψ x) :
    fisherRaoQuadForm (lift ψ) (liftDiff ψ Δψ) ≤ 4 * euclideanQuadForm Δψ := by
  rw [fisher_euclidean_tangent_isometry ψ Δψ hψ]

/-- **Nonnegativity of the Euclidean tangent quadratic form.** -/
lemma euclideanQuadForm_nonneg (Δψ : V → ℝ) : 0 ≤ euclideanQuadForm Δψ := by
  unfold euclideanQuadForm
  exact Finset.sum_nonneg (fun x _ => sq_nonneg _)

/-- **Nonnegativity of the Fisher-Rao tangent quadratic form** at a positive
    base.  Follows from the isometry plus nonnegativity of the Euclidean
    form.  An independent direct proof would also work; we keep this one
    to advertise the bridge. -/
lemma fisherRaoQuadForm_lift_nonneg
    (ψ Δψ : V → ℝ) (hψ : ∀ x, 0 < ψ x) :
    0 ≤ fisherRaoQuadForm (lift ψ) (liftDiff ψ Δψ) := by
  rw [fisher_euclidean_tangent_isometry ψ Δψ hψ]
  have hsum : 0 ≤ euclideanQuadForm Δψ := euclideanQuadForm_nonneg Δψ
  linarith

/-! ### 5b. Manifold non-degeneracy at interior amplitudes (narrow form)

The next two lemmas formalise the **narrow, locally-statable form of the
"Manifold Admissibility" principle** discussed in the May 2026 strategic
review:

> *Reasoning about probabilities of certainty is geometrically singular —
>  the Fisher-Rao metric collapses at the boundary of the simplex.
>  Training architectures that respect the manifold (analog noise, HG
>  wavelet pump) are precisely those that keep distributions in the
>  interior where the metric is non-degenerate.*

**Honest scope.** The general "iff" form (the Fisher information matrix
is positive definite *iff* the distribution is interior) is *not*
statable against the current `ParametricFamily` structure in
`@c:\Lean4 Projects\src\SGC\InformationGeometry\FisherKL.lean`, because:

* `ParametricFamily.positive` already requires `0 < dist θ v` as a
  *structural* axiom of the type — interiority is built in, not a
  hypothesis we can vary.
* `score_function` is itself axiomatised — there is no concrete
  derivative to compute against.
* `FisherMatrix_posSemidef` is axiomatised at PSD level only; the
  upgrade to PD requires either a concrete score realisation or a
  separate score-linear-independence hypothesis.

What *is* statable, here, against the lifted-amplitude Fisher-Rao
quadratic form whose isometry to the flat ℓ² form we already proved,
is the following pair of lemmas: at a pointwise-positive `ψ`, the
lifted FR form is non-degenerate as a quadratic form on tangent
perturbations `Δψ`.  This is the precise mathematical content of
"the manifold has well-defined geometry at interior amplitudes" in
the structure that actually exists in this repository.

A fully general `fisherMetric_nondegenerate_iff_interior` theorem on
an arbitrary (boundary-allowing) parametric family would be a
multi-week refactor of `FisherKL.lean` and is *deliberately* out of
scope here. -/

/-- **Euclidean tangent quadratic form vanishes iff perturbation is zero.**

    `∑ x, (Δψ x)² = 0 ↔ Δψ = 0` — a basic fact about sums of squares
    over a finite type.  Stated separately so the FR consequence reads
    cleanly. -/
lemma euclideanQuadForm_eq_zero_iff (Δψ : V → ℝ) :
    euclideanQuadForm Δψ = 0 ↔ Δψ = 0 := by
  unfold euclideanQuadForm
  constructor
  · intro h
    -- Sum of nonneg = 0 ⇒ each term = 0 ⇒ each `Δψ x = 0`.
    have h_each : ∀ x ∈ (Finset.univ : Finset V), (Δψ x) ^ 2 = 0 := by
      intro x _
      have h_nonneg : ∀ x ∈ (Finset.univ : Finset V), 0 ≤ (Δψ x) ^ 2 :=
        fun y _ => sq_nonneg _
      exact (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).mp h x (Finset.mem_univ x)
    funext x
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (h_each x (Finset.mem_univ x))
  · intro h
    subst h
    simp

/-- **Fisher-Rao tangent quadratic form is non-degenerate at interior
    amplitudes** (narrow Manifold Admissibility lemma).

    For a pointwise-positive amplitude `ψ : V → ℝ`, the lifted
    Fisher-Rao quadratic form vanishes on a tangent perturbation
    `Δψ` if and only if `Δψ` is identically zero:

    `fisherRaoQuadForm (lift ψ) (liftDiff ψ Δψ) = 0 ↔ Δψ = 0`.

    **Mathematical content.** The Fisher-Rao metric on the lifted
    distribution `P = ψ²` defines a *positive definite* (not merely
    positive semidefinite) bilinear form on tangent vectors at any
    interior amplitude.  In particular the "geometry" at `ψ` — the
    notion of length, angle, and orthogonality of perturbations — is
    well-defined; the manifold is non-degenerate at this point.

    **Proof.** Direct from `fisher_euclidean_tangent_isometry`
    (which equates the FR form to `4 · ‖Δψ‖²_{ℓ²}`) plus
    `euclideanQuadForm_eq_zero_iff`.  The factor `4 ≠ 0` is the only
    arithmetic step.

    **Connection to the wider research programme.** This lemma is the
    Lean-statable kernel of the "Manifold Admissibility" thesis from
    the May 2026 strategic review.  It does NOT prove (and is not
    intended to prove) the wider claims that:

    * the wavelet pump is the *unique* Fisher-Rao-respecting noise
      geometry (multiple Calderón-admissible wavelet families satisfy
      the same property; HG is special for *Heisenberg-Gabor*
      time-frequency uncertainty, which is a different optimality
      criterion); or
    * isotropic Gaussian noise is "provably wrong" (this is an
      empirical observation about coupling efficiency, not a Lean
      theorem).

    What it *does* prove, formally, is that at any positive amplitude
    the geometry is well-defined.  The contrapositive — that
    geometric reasoning fails at boundary amplitudes — is then a
    direct consequence of the divergence of `(Δψ)² / ψ` when `ψ → 0`,
    visible in the very definition of `fisherRaoQuadForm`. -/
theorem fisherRaoQuadForm_lift_eq_zero_iff
    (ψ Δψ : V → ℝ) (hψ : ∀ x, 0 < ψ x) :
    fisherRaoQuadForm (lift ψ) (liftDiff ψ Δψ) = 0 ↔ Δψ = 0 := by
  rw [fisher_euclidean_tangent_isometry ψ Δψ hψ]
  rw [show (4 : ℝ) * euclideanQuadForm Δψ = 0 ↔ euclideanQuadForm Δψ = 0 from
        ⟨fun h => by linarith, fun h => by rw [h]; ring⟩]
  exact euclideanQuadForm_eq_zero_iff Δψ

/-! ## 6. Connection to `SGC.InformationGeometry.FisherKL` (commentary)

The local isometry above specialises the general `FisherQuadForm` machinery
in `SGC.InformationGeometry.FisherKL` to the parametric family

  `P_θ(x) = ψ_θ(x)²`,

where `θ ↦ ψ_θ` is an amplitude parameterisation.  In that case the score
function (currently axiomatised in `FisherKL.lean` line 101) becomes

  `s_i(θ, x) = ∂_i log P_θ(x) = 2 · (∂_i ψ_θ(x)) / ψ_θ(x)`,

and the Fisher matrix entry contracts with a tangent perturbation
`Δθ ↦ Δψ = Σ_i Δθ_i · (∂_i ψ)` to give exactly the identity proved above:
the curved `1/p` factor cancels the `(∂ψ/ψ)` factors of the score, leaving
a flat `ℓ²` inner product on the amplitude tangent.

A future bridge file (one option: `FisherKL_HellingerSpecialisation.lean`)
can make this constructive — replacing the `score_function` axiom by the
explicit `2 · (∂_i ψ) / ψ` form for the lifted family — but that is
optional, and not required for the bare `fisher_euclidean_tangent_isometry`
to be useful at call-sites that already happen to have `P` in the form
`ψ²` and `ΔP` in the form `2·ψ·Δψ`.

## Connection to `SGC.InformationGeometry.TsallisStatistics`

The Beck-Cohen superstatistics theorem says that integrating Gaussian
fluctuations over an inverse-temperature distribution drawn from a Gamma
distribution yields a Tsallis q-Gaussian.  In the present setting, if the
amplitude `ψ` is updated by a Gaussian SGLD step, the resulting distribution
on `P = ψ²` is a `χ²` distribution at each coordinate — *the simplest
heavy-tailed family*.  Lifting that observation into a formal Tsallis bound
on the observable defect is a natural next phase, but it requires a
separate theorem (planned: `gaussian_amplitude_yields_chi_squared_density`)
in `SGC.InformationGeometry.TsallisStatistics`.  We deliberately do NOT
prove that here: it requires either a measure-theoretic setup or an
axiomatic characterisation of the Beck-Cohen integral, both outside the
scope of the present pure-algebraic isometry.

## Sprint C / D Architectural Note

The `fisher_euclidean_tangent_isometry` theorem above is a *local* result:
the Fisher-Rao length of any tangent vector at a lifted positive
distribution equals twice its Euclidean length.  It does NOT claim that the
amplitude submanifold is globally flat (it has constant positive Gaussian
curvature 1) and it does NOT support the inference that two amplitudes
`ψ_A` and `ψ_B` belonging to different consolidated tasks may be linearly
added.

The relevant empirical record on this question is in
`SGC.ContinualLearning.IsolationTheorem`, which formalises the Sprint C
(April 2026) finding that mathematically valid Fisher-orthogonal projection
into a shared-weight network is insufficient for continual learning — a
parity crystallisation consumed ~55 % of capacity, leaving only 45 % for
the next task, which then stalled.  The Sprint D resolution was **isolated
models per task with sheaf-consistency checks**, not a more clever metric.

The Hellinger lift is therefore best understood as a *local simplification
inside a single crystallised model*, not as a cross-task superposition
device.  Inside one crystal, the lift turns curved `1/p` Fisher-Rao terms
into flat `ℓ²` ones — useful for bounding a single task's tail-update
defect or for the `eff_rank`-collapse calculation, but neutral on the
multi-task-superposition question.
-/

end SGC.InformationGeometry.HellingerLift

end
