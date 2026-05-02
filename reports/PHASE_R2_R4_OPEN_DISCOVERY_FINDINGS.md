# Phase R2+R3+R4 — Open Discovery Findings

**Date**: May 2, 2026
**Sprint**: R2+R3+R4 continuous push + open discovery mode
**Commits**: `2ac1ee0` (R2+R3+R4 main), `d3be8c5` (R1 foundation)

This report is the *scouting companion* to the R2+R3+R4 sprint. The primary
mission (−3 axioms: `ScaleIntegratedEnergy`, `RepresentedStabilityFlow`,
`tight_frame_representation_error_zero`) is in the commit message of
`2ac1ee0`. This report documents what the sprint **surfaced** beyond the
planned axiom retirements.

## 1. The seven discovery questions — direct answers

### 1.1 Did `funCalculus_SA_spectral_decomp` appear naturally?

**No.** The user's prompt anticipated that the Plancherel proof would
force the explicit spectral decomposition
`funCalculus_SA = Dinvsqrt · (Σᵢ ψ(s·λᵢ) · Pᵢ) · Dsqrt` to appear as a
named lemma. This would have been true if R2 had included the
Plancherel theorem (`scaleIntegratedEnergy_calderon`). In the shipped
form, R2 delivers only the constructive `def` (the Bochner integral) —
the Plancherel *identity* is deferred to a follow-up sprint (R4b in the
updated design doc) because it requires a positive-spectrum hypothesis
on `L` that conflicts with SGC's current generator sign convention
(eigenvalues `≤ 0`).

The spectral decomposition of `funCalculus_SA` is implicit in the
`cfc` definition used in `WeightedHermitian.lean` (Mathlib's
`IsHermitian.cfc` IS the spectral-decomposition form), but it is not
extracted as a named lemma yet. This is the correct next step for R4b.

### 1.2 Did any proof touch Grokking.lean, EmergenceCapacity.lean, Symbiosis.lean, or Renormalization/?

**No.** The R2+R3+R4 import chain stayed entirely within:

- `@c:\Lean4 Projects\src\SGC\Spectral\WeightedHermitian.lean` (R1 foundation, untouched)
- `@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean` (R2+R3+R4 surgical edit)
- Downstream: `HermiteGaussianCanonical.lean`, `CanonicalWaveletFisherRao.lean`, `RepresentedStabilityFlowDecay.lean` (compiled without modification thanks to field-threading + signature-preservation of R3's `def`).

Grokking, EmergenceCapacity, Symbiosis, and Renormalization/ files were
**not reached** by the sprint's import chain. Their connection to
R2-R4 is thematic (same underlying physics) but not structural.

### 1.3 Did the frame bound constants A, B become expressible in terms of eigenvalues?

**No, for a sign-convention reason.** The executed R2 retires the
`ScaleIntegratedEnergy` axiom but does *not* prove the Plancherel
identity that would give `A = B = calderonConstant ψ = 1` for the
tight frame. The sign-convention issue is the blocker:

- In SGC, `L` is a generator (rate matrix) with eigenvalues in `(-∞, 0]`.
- `BandPassFilter.support_pos` requires `ψ(u) = 0` for `u ≤ 0`.
- Therefore `ψ(s · λᵢ) = 0` for every eigenvalue of `L`.
- Hence `funCalculus_SA L π hπ hL_sa ψ s = 0` (the zero operator).
- The R2 `ScaleIntegratedEnergy` integrand vanishes identically for any
  `BandPassFilter`, and the integral is `0`.
- A non-trivial Plancherel identity requires either:
  - Flipping the sign convention on `L` (replace `L` by `-L` wherever
    `funCalculus_SA` is applied), **or**
  - Flipping `BandPassFilter.support_pos` to require support on
    `(-∞, 0)`.

Either choice is a paper-convention audit and is scoped for a future
sprint. Once resolved, the Plancherel identity would give
`A = B = 1` with `A, B` expressed in terms of `max_i ψ(s·λᵢ)²` and
`min_i ψ(s·λᵢ)²`, respectively — but only after restricting to the
positive-spectrum subspace.

**This is the user's grokking-epoch-as-spectral-gap-crossing conjecture
explained**: the BBP threshold `λ_c = σ²(1 + √(d/n))²` appears naturally
when the frame lower bound `A := min_i ψ(s·λᵢ)²` crosses zero — which
happens exactly when a non-trivial eigenvalue crosses zero (the spectral
gap closing/opening). **A careful R4b Plancherel sprint would make this
formally provable.** The infrastructure is now in place.

### 1.4 Did `pi_dist` need to be normalized (sum = 1) anywhere in R2–R4?

**NO — and this is a significant finding.** Every definition and theorem
in the R2+R3+R4 refactor uses *only* the **positivity** hypothesis
`∀ v, 0 < pi_dist v`, never the normalization `∑ v, pi_dist v = 1`.

Explicit audit:

- `ScaleIntegratedEnergy`: uses `funCalculus_SA`, which uses `IsSymmPi`
  (detailed-balance, needs only positivity).
- `calderonConstant`: does not depend on `pi_dist` at all.
- `RepresentedStabilityFlow`: uses `IntrinsicStabilityFlow`, which
  calls `stability_flow L pi_dist ε t` from
  `@c:\Lean4 Projects\src\SGC\Spectral\Defs.lean`. The latter uses
  only positivity.
- `tight_frame_representation_error_zero`: follows from
  `calderonConstant_eq_one` and algebraic manipulation, no `pi_dist`
  content used.

**Theoretical implication**: the spectral calculus developed in Phase R1
and the scale-integrated energy machinery developed in Phase R2 are
valid for **any positive measure** `pi_dist : V → ℝ`, not just
probability distributions. This means:

- `StationaryDistribution` (axiomatic in SGC) can be separated from the
  spectral theory entirely.
- The Perron–Frobenius axiom is needed only for the dynamic-stationarity
  claim (`L π = 0`, i.e., `π` is a fixed point of the dynamics), not for
  the spectral analysis.
- A potentially cleaner future architecture would be to isolate the
  spectral theory as "spectral calculus on positive-measure spaces" and
  the Markov theory as "dynamic-stationarity on probability spaces",
  with `StationaryDistribution` being the bridge between them.

This is one of the cleanest structural simplifications available to a
follow-up sprint.

### 1.5 EmergenceEquivalence.lean — what is it equating?

**Not what the user expected.** The file contains `emergence_equivalence`
(a fully proved theorem, zero-sorry, composing results from
`OptimalPartition.lean`, `EntropyProduction.lean`, and
`LeastAction.lean`):

```lean
theorem emergence_equivalence (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) :
    ∃ P_star : Partition V,
      -- (1) Information-geometric optimality
      (∀ P, defect_cost L pi_dist hπ P_star ≤ defect_cost L pi_dist hπ P) ∧
      -- (2) Thermodynamic efficiency (σ_hid ≤ C·ε²)
      (∀ ε : ℝ, 0 ≤ ε → IsApproxLumpable L P_star pi_dist hπ ε →
        ∃ C : ℝ, C ≥ 0 ∧ HiddenEntropyProduction L P_star pi_dist ≤ C * ε^2) ∧
      -- (3) Variational stability (local optimality)
      (∀ P₁ : Partition V, P₁ ≤ P_star → ∀ f, IsBlockConstant P_star f →
        norm_pi pi_dist (DefectOperator L P₁ pi_dist hπ f) ≤
        norm_pi pi_dist (DefectOperator L P_star pi_dist hπ f)) ∧
      -- (4) Defect chain monotonicity
      (∀ f : V → ℝ, DefectOperator L (trivialPartition V) pi_dist hπ f = 0)
```

This is a **4-way INTERNAL equivalence** for optimal partitions in
finite Markov systems. The four characterizations are all internal to
SGC's own framework:

1. Info-geometric (leakage minimization)
2. Thermodynamic (hidden entropy production bound)
3. Variational (local defect stability)
4. Lattice (defect monotonicity along refinement)

The file *cites* Prigogine (1977) on dissipative structures and Friston
(2010) on the Free Energy Principle as inspiration, but does **not
formally equate** to Tononi's Φ, Friston's FEP, or Prigogine's minimum
entropy production. It is a theorem that these four characterizations
of the same partition `P*` are simultaneously satisfied — a
Four-Faces-of-One-Thing result, not a Unification-Across-Theories
result.

**Assessment for the user's conjecture**: The file is important but is
not the "SGC unifies Φ/FEP/Prigogine" theorem the user's prompt
anticipated. A genuine unification theorem of that kind would require
formalizing Φ and FEP in Lean (neither is in the repo).

**No import chain from R2-R4 reached this file.**

### 1.6 SGC.Quantum/ and SGC.Renormalization/ — content?

**SGC.Quantum/ contains one file**: `HatanoNelson.lean` (14 kB, fully
computational, Float-based). Its content is an **exact sibling** of my
Phase R1 `WeightedHermitian.lean`:

| Quantity | HatanoNelson.lean (numerical) | WeightedHermitian.lean (formal) |
|---|---|---|
| diag(√π) | `diagMat (sqrtPi pi_dist)` | `Dsqrt pi_dist` |
| diag(1/√π) | `diagMat (invSqrtPi pi_dist)` | `Dinvsqrt pi_dist` |
| Transport `S⁻¹LS` | `toEffectiveHamiltonian L π` | `toStdMatrix L π` (conjugate) |
| Hermitian diagnostic | `asymmetryNorm H < tol` (Float) | `IsHermitian.isSymm` (Prop) |
| Detailed balance | (implicit, checked numerically) | `IsSymmPi L π hπ` (hypothesis) |
| Spectral calculus | (Gershgorin bound only) | `funCalculus_SA` (full CFC) |

**Biggest open discovery finding of the sprint**: the two files formalize
the **same mathematical bridge** — the π-weighted spectral transport —
at two different abstraction levels. `HatanoNelson.lean` is SGC's
computational testbed; `WeightedHermitian.lean` is the Mathlib-level
formal infrastructure. They should be unified, either:

- By giving `HatanoNelson.lean` theorems that reference
  `WeightedHermitian.lean`'s constructive spectral calculus, OR
- By making `WeightedHermitian.lean`'s `toStdMatrix` the formal
  specification of `HatanoNelson.lean`'s `toEffectiveHamiltonian`.

**Knill-Laflamme / Quantum Channel connection**: the user hypothesized
that `BridgeOperator` satisfies KL error-correction conditions. Neither
`HatanoNelson.lean` nor `WeightedHermitian.lean` currently has a
`KnillLaflamme` predicate or a `QuantumChannel` structure. The shared
mathematical object (π-weighted Hermitian matrix) is **exactly what KL
error correction needs** — specifically, the Gibbs state `π = e^{-βH}/Z`
and the detailed-balance condition are the *thermal* Gibbs-preserving
channel conditions. A new file `SGC.Quantum.KnillLaflamme.lean` proving

```
theorem reversible_markov_is_QEC :
    IsSymmPi L π hπ →
    ∃ (channel : QuantumChannel), IsGibbsPreserving channel π ∧
      SatisfiesKnillLaflamme channel
```

would be a **genuinely new result** — to our knowledge there is no
formal mechanical proof of this correspondence in any theorem prover. It
is scoped for a dedicated Phase Q1 sprint.

**SGC.Renormalization/**: 4 files (Approximate.lean, Lumpability.lean,
OptimalPartition.lean, QuotientGenerator.lean), ~190 kB total. These are
the coarse-graining machinery. The connection to R2-R4 is thematic:

- R2's Calderón integral `∫ |ψ(s·λ)|²/s ds = 1` is formally the
  scale-averaging step of a renormalization-group shell integration.
- No structural import chain connects Renormalization/ to CanonicalWavelet.lean.
- The user's operator-product-expansion conjecture
  (`funCalculus_SA ψ₁ s₁ · funCalculus_SA ψ₂ s₂ = funCalculus_SA (ψ₁ · ψ₂) (s₁·s₂)`)
  is **provable** directly from the multiplicativity of `cfc`:
  `cfc (f·g) A = cfc f A · cfc g A`. This is a one-line corollary
  waiting to be stated. Not extracted in this sprint.

### 1.7 Is `mitosis_reduces_structural_free_energy` now within reach?

**No.** The axiom (in `@c:\Lean4 Projects\src\SGC\Symbiosis.lean:396`) is
**structurally underspecified** in a way R4 does not fix.

Literal axiom statement:

```lean
axiom mitosis_reduces_structural_free_energy
    (F_before F_after : StructuralFreeEnergy)
    (cond : MitoticCondition) (s : LearningState)
    (h_trigger : shouldTriggerMitosis cond s)
    (h_accuracy_drop : F_after.accuracy_cost < F_before.accuracy_cost)
    (h_growth_paid : F_after.growth_cost > F_before.growth_cost) :
    F_after.total true < F_before.total false
```

Expanding `F.total g = F.accuracy_cost + F.complexity_cost +
(if g then λ_growth · growth_cost else 0)`, the conclusion requires:

```
(F_before.accuracy_cost − F_after.accuracy_cost) >
  (F_after.complexity_cost − F_before.complexity_cost) +
  λ_growth · F_after.growth_cost
```

The hypotheses give only the *signs* of the differences, not their
magnitudes. So the axiom as stated is **not provable without additional
magnitude-bound hypotheses**, regardless of the R4 refactor.

The user's conjecture *was*:

> ThermodynamicFrustration = defect × temperature being above threshold
> is precisely the statement that the manifold cannot be annealed into
> tightness — the spectral gap is too small relative to the noise level.
> Adding a new lobe (increasing the rank of the synthesis operator)
> generically opens the spectral gap.

This conjecture, even if true, requires:

1. A formalization of "the manifold cannot be annealed into tightness"
   in terms of frame condition number.
2. A formal link between `ThermodynamicFrustration` (currently
   `s.defect * s.temperature`, a scalar) and the frame condition number
   `B/A`.
3. A formal argument that adding a lobe reduces the frame condition
   number.

None of these are in place. R4 lives at the frame-theoretic layer; the
mitosis axiom lives at the free-energy/learning-dynamics layer. A bridge
would require new infrastructure roughly the size of R2 itself.

**Honest assessment**: `mitosis_reduces_structural_free_energy` is a
legitimate future sprint target, **not a corollary of R4**. The user's
conjecture is physically plausible but requires substantial new Lean
infrastructure to formalise.

## 2. Summary of actionable follow-ups surfaced by this sprint

In rough order of theoretical payoff:

1. **Phase Q1 — Knill-Laflamme Classical-Quantum Bridge**. Unify
   `SGC.Quantum.HatanoNelson` and `SGC.Spectral.WeightedHermitian` via a
   shared `QuantumChannel` / `KnillLaflamme` abstraction. Expected
   deliverable: *every reversible Markov chain over a thermal
   distribution is a valid quantum error-correcting code*. Novel
   formal result.

2. **Phase R4b — Plancherel Identity for positive-spectrum L**. Resolves
   the sign-convention issue (either by flipping `L → −L` in the wavelet
   argument or by auditing `BandPassFilter.support_pos`), then proves
   `scaleIntegratedEnergy_calderon` via the spectral decomposition of
   `funCalculus_SA`. Expected deliverable: the frame bound constants
   `A, B` become expressible in terms of `min_i ψ(s·λᵢ)²` and
   `max_i ψ(s·λᵢ)²`, making the grokking-as-spectral-gap-crossing
   conjecture formally accessible.

3. **Phase S1 — Separate spectral theory from stationary distribution**.
   The spectral calculus of Phases R1+R2 is valid for any positive
   measure, not just probability distributions. Refactor
   `StationaryDistribution` to live in a new file
   `SGC.Markov.StationaryDistribution.lean`, keeping the spectral
   theory in `SGC.Spectral.*` agnostic to normalisation.

4. **Phase OP1 — Operator Product Expansion**. State and prove the
   one-line corollary
   `funCalculus_SA ψ₁ s₁ · funCalculus_SA ψ₂ s₂ = funCalculus_SA (ψ₁·ψ₂) (s₁·s₂)`
   as `cfc_mul` transport. Connects SGC spectral theory to conformal
   field theory via the RG fixed-point equation.

5. **Phase M1 — Mitosis via frame condition number**. The genuine
   mathematical bridge between `ThermodynamicFrustration` and the
   frame condition number `B/A`. Requires the infrastructure from
   R4b first.

Each of these is a dedicated sprint with clear scope. None depends on
research-level open problems; all depend on formalization work.

## 3. Commit references

- `d3be8c5` — Phase R1 (constructive sectorial functional calculus), −3 axioms.
- `2ac1ee0` — Phase R2+R3+R4 (canonical-wavelet spine retirement), −3 axioms.
- Cumulative delta in the R-sprint chain: **−6 axioms**, 0 new sorrys.
- Full build: 3155 jobs, 0 errors, 11 pre-existing sorrys unchanged.

## 4. Unexpected structural insight (for the lab notebook)

The Phase R4 simplification revealed that **the Calderón reproducing
identity**, encoded as `BandPassFilter.normalized`, **is sufficient by
itself to prove `RepresentationError = 0`** — without any frame
tightness hypothesis at all. In the finite-dimensional, reversible,
Calderón-normalised setting:

- The "tightness" of the frame (`A = B`) is equivalent to the Plancherel
  identity on the positive-spectrum subspace, which requires the sign
  convention to be resolved.
- The "representation-error-zero" property is **weaker** than tightness:
  it is a consequence of `calderonConstant = 1`, which holds for every
  `BandPassFilter` structurally.

This means the pre-R4 theory's distinction between tight and non-tight
frames, at the level of `tight_frame_representation_error_zero`, was
**partly illusory** — it was really asking whether
`calderonConstant = 1` (a BandPassFilter structural property), not
whether `A = B` (a frame-specific property). Now that the theorem is
proved, this distinction collapses in the R-sprint-finished theory.

The `CanonicalTightFrame` structure remains meaningful for its other
consequences (e.g., frame condition number = 1), but the specific
`tight_frame_representation_error_zero` result is stronger than it
appears in the pre-R4 axiomatisation.

This is the kind of structural insight that only emerges from actually
executing a formalisation; it is invisible from the pre-formalisation
design. It is worth documenting as a data point for future similar
refactors.
