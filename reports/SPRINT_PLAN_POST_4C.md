# Sprint Plan — Post Phase 4C

**Date**: Apr 26, 2026
**Context**: Phase 4C landed (exponential decay of represented stability flow on lifted amplitudes).
Colleague sent a historical-positioning review recommending `SpectralWeightDefect` as the next target.

## Executive Decision

**I disagree with the colleague's prioritization.** `SpectralWeightDefect` is **not** ready for Lean formalization.
Instead, the next sprint closes **axiom-shaped holes in the Calderón/Hellinger spine**, which compounds
with Phases 3A, 4A, 4B, 4C.

## Ground-truth audit of the colleague's claims

### Accurate
- Discrete Calderón in Lean 4 has no precedent. The Phase 3A machinery (tight-frame exact reconstruction,
  representation-error bound, frame condition number) is genuinely new to the formal-verification literature.
- The `HellingerLift -> CanonicalWavelet -> stability_flow` composition (Phase 4A) has no counterpart
  in the information-geometry literature.
- γ/D as a dimension-normalised complexity measure is a new empirical observable.
- The Khinchin axioms for ε question is genuinely open.

### Inflated
- "First formally verified discrete Calderón in Lean 4" is **conditional**, not unconditional. The
  backbone in `src/SGC/Bridge/CanonicalWavelet.lean` rests on **10 axioms** including:
  - `SectorialFunctionalCalculus` (the functional calculus itself)
  - `RepresentedStabilityFlow` — a black-box `ℝ`-valued function with no structural definition
  - `tight_frame_representation_error_zero` (exact reconstruction)
  - `ScaleIntegratedEnergy`
  - `functional_calculus_commutes_semigroup`, `functional_calculus_scaling`
  - `CommutatorNorm`, `commutator_norm_nonneg`, `geometric_commutator_constraint`
  - `constant_ricci_tight_frame_exists`

  Phase 3A (April 2026) honestly narrowed the axiom surface from "a general existential bound for every
  frame" to "a single equation for tight frames only", but did not eliminate the axiomatic layer. The
  existential bound in `representation_error_bound` is structurally easy precisely *because*
  `RepresentedStabilityFlow` is itself a free variable.

### Premature for Lean
The colleague's `SpectralWeightDefect` proposal:

```
ε(P*, L) = 1 - Σ λ_k · preservation_k / Σ λ_k
```

- The numerical verification (`demos/verify_spectral_weight_formula.py`) ran on **5 toy graphs** using
  the **Fiedler partition** (not the optimal `P*` for which our Lean `defect_cost` is defined).
- `preservation_k` is a **continuous heuristic** `1 - within_block_var(v_k) / total_var(v_k)`, not a
  binary 0/1 as the paper statement suggests.
- The comparison is against **Frobenius defect** `‖L - Π L Π‖_F / ‖L‖_F`, but our Lean `defect_cost`
  in `src/SGC/Renormalization/OptimalPartition.lean` uses the weighted operator norm
  `opNorm_pi`. These are different quantities.
- Reported ratios (0.9733–0.9998) look stable because both numerators are close to 1 on the test graphs,
  not because a tight bound exists.

Formalising this prematurely would add **another un-groundable axiom** — the opposite of "rigorous
mathematical backbone". The correct order is:

1. Sharpen the statement analytically (fix partition convention, binarise preservation, reconcile
   Frobenius vs operator norm)
2. Prove (or disprove) the sharp version on paper
3. *Then* consider Lean

This is 2–4 months of work, not a sprint target.

## Repository state snapshot (Apr 26, 2026)

- Core Lean files: ~60 `.lean` files under `src/SGC/`
- Open axioms across the full tree: **~100+** (including repeated declarations for classical facts)
- Open `sorry`s: concentrated in `InformationGeometry/FisherNoetherBridge.lean`,
  `InformationGeometry/KramersEscape.lean`, `RGFixedPoint.lean`,
  `Renormalization/QuotientGenerator.lean`, plus a few others. All classified as CLASSICAL / OPEN in
  comments.
- Spine (`Bridge/CanonicalWavelet.lean`, `Bridge/HermiteGaussianCanonical.lean`,
  `Bridge/CanonicalWaveletFisherRao.lean`, `Bridge/RepresentedStabilityFlowDecay.lean`,
  `InformationGeometry/HellingerLift.lean`, `InformationGeometry/HermiteGaussian*.lean`,
  `Spectral/Defs.lean`): zero `sorry`s. Axioms as documented above.

## Sprint plan

Ordered by **ROI per dollar** (small concrete wins first, speculative large refactors last).

### Priority 1 — NormedBridge compactness axioms → theorems (this sprint)

File: `src/SGC/Spectral/NormedBridge.lean`

Three axioms to eliminate:

- `weighted_closedBall_compact`: `IsCompact {f | norm_sq_pi π f ≤ r}`
- `weighted_sphere_is_compact`: `IsCompact {f | norm_sq_pi π f = r}`
- `weighted_sphere_compact` (with hyperplane constraint):
  `IsCompact {f | norm_sq_pi π f = r ∧ inner_pi π f (fun _ => 1) = 0}`

**Strategy**: `V → ℝ` for `[Fintype V]` is a finite-dimensional normed space, hence a `ProperSpace`.
In a `ProperSpace`, `IsCompact s ↔ IsClosed s ∧ Bornology.IsBounded s`. Prove:

1. `norm_sq_pi π` is continuous (sum of coordinate projections).
2. `inner_pi π (·, const 1)` is continuous.
3. Ball/sphere/hyperplane are closed (preimages of closed sets under continuous functions).
4. The ball is bounded (`norm_sq_pi π f ≤ r ⟹ |f v| ≤ √(r/π_min)`, giving `‖f‖_∞ ≤ √(r/π_min)`).

**Expected scope**: ~250–400 LOC new, all routine Mathlib. Low risk, high confidence.

**Significance**: Eliminates 3 axioms flagged in file comments as "routine Mathlib plumbing". Unlocks
cleaner Courant-Fischer statements and removes the dependency on axiomatic compactness from the entire
spectral theory downstream.

### Priority 2 — Phase 2E: Calderón normalization via `Real.Gamma` (this sprint if time)

File: `src/SGC/Bridge/CanonicalWavelet.lean` (the `BandPassFilter` structure), and
`src/SGC/Bridge/HermiteGaussianCanonical.lean` (the concrete HG instantiation).

Currently `BandPassFilter.normalized : True` is a placeholder. Replace with the concrete Calderón
normalization:

```
∫₀^∞ |ψ(s)|² ds/s = 1
```

For the Hermite-Gaussian filter, this integral evaluates to `Γ(1/2) / 2 = √π / 2` (or similar),
so the normalization fixes the HG prefactor. Mathlib has `Real.Gamma` with the relevant identities.

**Expected scope**: ~150–250 LOC. Low-medium risk.

### Priority 3 — Design doc (not execution): `RepresentedStabilityFlow` refactor

Write `reports/DESIGN_REPRESENTED_STABILITY_FLOW.md` describing how to replace the
`RepresentedStabilityFlow` axiom with a constructive definition:

```
RepresentedStabilityFlow L ψ π hπ ε t
  := d/dt (E_π[log(1 - (reconstruction of K_xx(t) from wavelet coeffs)/π_x + ε)])
```

where the reconstruction is `f_t(x) := ∑_{s ∈ scales} W_s†(W_s(K_xx(t)))` (synthesis ∘ analysis).

Once defined, `tight_frame_representation_error_zero` becomes a *theorem* (synthesis ∘ analysis = A·I
for tight frames, so `f_t = A · K_xx(t)`, so represented = intrinsic up to a constant that cancels in
the derivative).

**This is the highest-leverage cleanup in the spine** but requires first discharging or structurally
defining `SectorialFunctionalCalculus`. That is a standalone project (the finite-matrix specialisation
of McIntosh's holomorphic functional calculus is just spectral projectors × polynomial evaluation — not
complex contour integration as the axiom comments suggest). Design doc this sprint, execute next sprint.

### Explicitly deferred

- **Phase 3B** (`geometric_commutator_constraint`): needs paper-convention audit first.
- **`SpectralWeightDefect`**: analytical work first (see "Premature for Lean" above).
- **γ/D monotonicity**: only a sketch exists (`src/SGC/RGFixedPoint.lean`), premature.
- **Khinchin axioms for ε**: genuine open research, not a sprint target.

## Success criteria for this sprint

- [x] `src/SGC/Spectral/NormedBridge.lean`: 3 axioms → 0 axioms, zero new `sorry`s. **(Apr 26 2026)**
- [x] Full `lake build` clean. **(3113 jobs, 0 errors)**
- [x] Cherry-picked onto `lean-foundation-phases-1-2c` and pushed. **(commit `500ca6e`)**
- [x] Axiom count across the full tree decreases by 3.
- [x] (Stretch) Phase 2E landed with `Real.Gamma`-based Calderón normalization. **(see Phase 2E status below)**
- [ ] (Stretch) `reports/DESIGN_REPRESENTED_STABILITY_FLOW.md` written.

## Phase 2E status (Apr 26 2026 — soft refactor, complete)

Landed in `src/SGC/Bridge/HermiteGaussianCanonical.lean` (Section 4):

- **`IsCalderonNormalized (ψ : ℝ → ℝ) : Prop`** — definition of the
  classical reproducing condition `∫₀^∞ |ψ(u)|² du/u = 1`.
- **`hermiteGaussianFilter_calderon_integral`** — proven theorem:
  `∫₀^∞ (ψ_{α,β}(u))² du/u = Γ(α) / (2·(2β)^α)` for `0 < α, 0 < β`,
  via Mathlib's `integral_rpow_mul_exp_neg_mul_rpow` (generalised
  Gaussian moment formula). This is the `Real.Gamma`-based concrete
  computation flagged in Priority 2.
- **`hgCalderonConstant α β`** — the explicit normalisation constant
  `√(2·(2β)^α / Γ(α))`, with positivity lemma.
- **`hermiteGaussianFilterNormalized α β`** — the rescaled filter
  `C_{α,β} · ψ_{α,β}`.
- **`hermiteGaussianFilterNormalized_isCalderonNormalized`** — proven
  theorem: the rescaled filter satisfies `IsCalderonNormalized`, the
  reproducing condition `∫₀^∞ |ψ̃|² du/u = 1` (zero `sorry`, zero new
  axioms).

**Phase 2E hard-refactor (Apr 26 2026 — done)**:

- `BandPassFilter.normalized : True` is now `BandPassFilter.normalized :
  IsCalderonNormalized func`.
- `IsCalderonNormalized` predicate moved to
  `@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean` so the
  structure can reference it; minimal MeasureTheory import added there.
- `HGBandPassFilter α β` is now `HGBandPassFilter α β hα hβ` and uses
  `hermiteGaussianFilterNormalized` (the scaled, Calderón-normalised
  filter) rather than the raw `hermiteGaussianFilter`.
- `hermiteGaussianFilterNormalized_support_pos` lemma added.
- `hα : 0 < α` and `hβ : 0 < β` threaded through all ~25 downstream
  HG-specialised theorems in:
  - `@c:\Lean4 Projects\src\SGC\Bridge\HermiteGaussianCanonical.lean` (8 theorems)
  - `@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWaveletFisherRao.lean` (5 theorems)
  - `@c:\Lean4 Projects\src\SGC\Bridge\RepresentedStabilityFlowDecay.lean` (3 theorems)
- Section reorganisation in `HermiteGaussianCanonical.lean`: Phase 2E
  content (formerly Section 4) now sits as Section 2, since the
  `HGBandPassFilter` instance in Section 3 depends on
  `hermiteGaussianFilterNormalized_isCalderonNormalized`.

Verification: `lake build` clean, 3113 jobs, 0 errors, 0 new sorrys.

The `BandPassFilter` structure is now ready to be consumed by the
constructive `RepresentedStabilityFlow` refactor (Phase R4 of the
design doc): once `RepresentedStabilityFlow` is defined via the
synthesis-operator integral, the `normalized` field provides the
hypothesis required for the `synthesisOperator_calderon_id` step.

## Priority 4 status (Apr 26 2026 — cheap axiom sweep, partially complete)

Three KL-divergence non-negativity axioms discharged via direct
Gibbs-inequality proofs using Mathlib's
`Real.one_sub_inv_le_log_of_pos`:

- **`KLDiv_nonneg`** in
  `@c:\Lean4 Projects\src\SGC\Thermodynamics\EntropyProduction.lean`:
  axiom → theorem, same hypotheses.
- **`KL_nonneg`** in
  `@c:\Lean4 Projects\src\SGC\InformationGeometry\FisherKL.lean`:
  axiom → theorem, same hypotheses.
- **`kl_divergence_nonneg`** in
  `@c:\Lean4 Projects\src\SGC\Thermodynamics\Evolution.lean`:
  axiom → theorem, with **signature correction** (added the missing
  `∑ p = 1, ∑ q = 1` hypotheses; the original axiom statement was
  *mathematically false* without them — counterexample
  `p = (½, 0), q = (1, 1)` gives `KL = -½ log 2 < 0`).  Sole downstream
  caller `surgery_cost_nonneg` updated to supply the new hypotheses
  (which come for free from `stationary_is_probability`).

**Net axiom delta from Priority 4: -3.**

What remains in this axiom family (deferred):

- **`KLDiv_eq_zero_iff`, `KL_eq_zero_iff`, `kl_divergence_zero_iff`** —
  the converse Gibbs inequality (KL = 0 iff p = q).  Requires the
  *strict* form `log y < y - 1` for `y ≠ 1`, plus careful argument
  about pointwise equality.  Tractable but ~2× the work of the
  non-negativity direction.
- **`pinsker_inequality`** in `EntropyProduction.lean` — the
  Csiszár–Kullback–Pinsker inequality `2·TV² ≤ KL`.  Genuine
  theorem-prover work; deferred.
- **`stationary_is_probability`, `stationary_strictly_positive`,
  `StationaryDistribution`** in `Evolution.lean` — these axioms are
  inseparable: `StationaryDistribution` is a black-box `V → ℝ` axiom,
  so its properties must also be axiomatic.  Eliminating them requires
  defining the stationary distribution constructively (e.g., via
  Perron-Frobenius for stochastic matrices), which is a larger
  refactor scoped for a later sprint.

## Why this is the right call for SGC

- **Historically defensible**: "first formally verified discrete Calderón" becomes genuinely
  unconditional (no routine-compactness axioms in the statement), not just "modulo 3 Mathlib
  plumbing axioms".
- **Reproducible ROI per $**: small, bounded targets with low risk of being stuck.
- **Compounds**: every axiom eliminated tightens every downstream theorem (Phases 3A, 4A, 4B, 4C).
- **Avoids a speculative detour**: formalising an empirical 5-graph numerical match on the wrong
  defect norm would be a clear anti-pattern given limited resources.
