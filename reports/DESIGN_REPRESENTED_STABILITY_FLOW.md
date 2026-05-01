# Design doc: `RepresentedStabilityFlow` axiom-to-definition refactor

**Status**: **Phase R1 complete** (May 1, 2026); R2-R5 queued
**Author**: Cascade (post-4C sprint, Priority 3; updated post-Phase-R1)
**Target branch**: `lean-foundation-phases-1-2c`
**Active commits on Phase R1**: `8eb081e` (`wip-quantum-bridge`), `d3be8c5` (`lean-foundation-phases-1-2c`)

## 0. Progress tracker (updated May 1, 2026)

| Phase | Description | Status | Axiom delta |
|---|---|---|---|
| **R1** | Constructive `funCalculus_SA` via Mathlib's `IsHermitian.cfc` + `weightedToStd` transport.  Replaces `SectorialFunctionalCalculus` (def), `functional_calculus_commutes_semigroup` (theorem), `functional_calculus_scaling` (theorem). | ✅ **complete** (commit `8eb081e`) | **−3** |
| R2 | Convert `ScaleIntegratedEnergy` from axiom to definition (the `∫₀^∞ ‖ψ(sL) f‖² ds/s` integral). | 🟡 queued | −1 |
| R3 | Convert `RepresentedStabilityFlow` from axiom to constructive definition via the synthesis-formula derivative. | 🟡 queued | −1 |
| R4 | Convert `tight_frame_representation_error_zero` from axiom to theorem (using R3's constructive form). | 🟡 queued | −1 |
| R5 | Optional: discharge `geometric_commutator_constraint` and `constant_ricci_tight_frame_exists` via the constructive frame. | 🟡 queued | up to −2 |

**Cumulative axiom reduction so far**: −3 (R1) of an upper-bound −6 (R1–R4) or −8 (R1–R5).

**R2 blocker**: `ScaleIntegratedEnergy` is referenced in 2 fields of the
`SpectralFrame` structure (`lower_bound`, `upper_bound`), which is in turn
used in 12+ sites across 4 files (`CanonicalWavelet.lean`,
`HermiteGaussianCanonical.lean`, `CanonicalWaveletFisherRao.lean`,
`RepresentedStabilityFlowDecay.lean`).  Adding `IsSymmPi` to its signature
propagates through `CanonicalTightFrame` (extends `SpectralFrame`) and all
downstream theorems.  This is a *structural* refactor of comparable size
to R1 itself, not a "stretch goal" within R1.  Suggested approach for R2:
treat as its own dedicated sprint.

**R3 blocker**: `RepresentedStabilityFlow` has even broader reach than
`ScaleIntegratedEnergy`.  Its constructive definition involves the
synthesis operator + a time derivative of `expected_log_return_prob`, both
of which require the R1 spectral decomposition + R2 integration to be in
place first.  R3 should follow R2.

**Precedes**: R2 (ScaleIntegratedEnergy refactor sprint).

## 1. Executive summary

`RepresentedStabilityFlow L ψ π hπ ε t : ℝ` is the **single highest-leverage
axiom** in the SGC Lean formalization.  Eliminating it — or, failing that,
replacing it with a constructive definition backed by a small set of
*structural* axioms rather than a single `ℝ`-valued black box — would:

- **Directly unlock** the conversion of
  `tight_frame_representation_error_zero` from axiom to theorem (the
  discrete Calderón reproducing formula in its strongest form).
- **Indirectly retire** two upstream functional-calculus axioms
  (`functional_calculus_commutes_semigroup`, `functional_calculus_scaling`)
  and one core operator axiom (`SectorialFunctionalCalculus` itself)
  because all three are needed only to give meaning to
  `RepresentedStabilityFlow`.
- **Convert `ScaleIntegratedEnergy`** from axiom to definition (the
  `ℝ`-valued integral that drives frame bounds).
- **Structurally strengthen** every Phase-4 theorem: at present they
  manipulate a real number of unknown provenance; post-refactor they
  manipulate a *computable expression* in `L, π, ψ, ε, t`.

Total axiom reduction (upper bound): **5 axioms → ≤ 1 structural axiom**
(or possibly 0, depending on how far we push the spectral decomposition).

The refactor is *not* blocked on any open research question.  Every
ingredient exists in Mathlib today.  The only genuine cost is a careful
traversal of finite-dimensional spectral theory and a bounded amount of
measure-theoretic plumbing for the `∫₀^∞ · ds/s` integral.

## 2. Current axiom surface

### 2.1 The five axioms at stake

Located in `@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean`:

```lean
-- L88: the sectorial functional calculus operator ψ(sL).
axiom SectorialFunctionalCalculus (L : Matrix V V ℝ) (psi : BandPassFilter)
    (s : ℝ) (hs : s > 0) : Matrix V V ℝ

-- L92: [ψ(sL), e^{tL}] = 0.
axiom functional_calculus_commutes_semigroup (L : Matrix V V ℝ)
    (psi : BandPassFilter) (s t : ℝ) (hs : s > 0) (ht : t ≥ 0) :
    SectorialFunctionalCalculus L psi s hs * HeatKernel L t =
    HeatKernel L t * SectorialFunctionalCalculus L psi s hs

-- L98: ψ((cs)L) = ψ(s·(cL)).
axiom functional_calculus_scaling (L : Matrix V V ℝ) (psi : BandPassFilter)
    (s c : ℝ) (hs : s > 0) (hc : c > 0) :
    SectorialFunctionalCalculus L psi (c * s) (mul_pos hc hs) =
    SectorialFunctionalCalculus (c • L) psi s hs

-- L122: ∫₀^∞ ‖ψ(sL) f‖²_π ds/s.
axiom ScaleIntegratedEnergy (L : Matrix V V ℝ) (psi : BandPassFilter)
    (pi_dist : V → ℝ) (hpi : ∀ v, 0 < pi_dist v) (f : V → ℝ) : ℝ

-- L186: the represented stability flow — a pure ℝ-valued black box.
axiom RepresentedStabilityFlow (L : Matrix V V ℝ) (psi : BandPassFilter)
    (pi_dist : V → ℝ) (hpi : ∀ v, 0 < pi_dist v)
    (epsilon : ℝ) (t : ℝ) : ℝ
```

Plus one downstream **claim-style** axiom that becomes a theorem as soon
as `RepresentedStabilityFlow` has any structure at all:

```lean
-- L258: representation error vanishes on tight frames.
axiom tight_frame_representation_error_zero
    (L : Matrix V V ℝ) (psi : BandPassFilter)
    (pi_dist : V → ℝ) (hpi : ∀ v, 0 < pi_dist v)
    (frame : CanonicalTightFrame L psi pi_dist hpi)
    (epsilon : ℝ) (t : ℝ) :
    RepresentationError L psi pi_dist hpi epsilon t = 0
```

### 2.2 Everything that depends on these axioms

Exhaustive list of dependents (grepped from the tree):

**`SectorialFunctionalCalculus`** is used in:
- `WaveletCoefficient L ψ s hs f := SectorialFunctionalCalculus L ψ s hs *ᵥ f`
  (`@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean:113-115`).
- Nowhere else structurally.  `functional_calculus_commutes_semigroup`
  and `functional_calculus_scaling` are *stated* but never invoked in
  any proof: they are dead code that only constrains the black box.

**`ScaleIntegratedEnergy`** is used in:
- `SpectralFrame.lower_bound` and `.upper_bound` fields
  (`@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean:142-146`).
- Nowhere else.

**`RepresentedStabilityFlow`** is used in:
- `RepresentationError` definition (`CanonicalWavelet.lean:195-199`).
- `represented_stability_flow_triangle_bound` (Phase 4B theorem, pure
  `abs_add_le`, does not need structure in β_rep).
- 10 specialisations in `HermiteGaussianCanonical.lean`,
  `CanonicalWaveletFisherRao.lean`, `RepresentedStabilityFlowDecay.lean`.
- All downstream uses either (i) bound `|β_rep|` via triangle + error
  bound, or (ii) rewrite `β_rep = β_intrinsic` via
  `tight_frame_exact_reconstruction`.

**`tight_frame_representation_error_zero`** is used in:
- `tight_frame_zero_error` (wrapper into an existential for signature
  compatibility).
- `tight_frame_zero_error_direct` (direct form).
- `tight_frame_exact_reconstruction` (Calderón formula).
- All three in `CanonicalWavelet.lean`.
- The HG specialisations in `HermiteGaussianCanonical.lean`.

### 2.3 Black-box leak radius

A `grep` across all of `src/SGC/` shows that **no downstream theorem
inspects the value of `RepresentedStabilityFlow`**.  They treat it as:

1. An opaque real number.
2. Subject to the triangle bound `|β_rep| ≤ |β_int| + Δβ`.
3. Equal to `β_intrinsic` on tight frames (via the error-zero axiom).

This is the *best possible case* for a refactor: the axiom's only
entanglement with the rest of the codebase is (2) and (3), both of
which are mechanical consequences of a constructive definition.

## 3. The key finite-dimensional insight

In the paper's continuous setting on `L²(ℝ₊, du/u)`:

- `ψ(sL)` is a contour integral in the complex plane (McIntosh's
  sectorial `H∞` calculus).
- `∫₀^∞ ‖ψ(sL) f‖² ds/s` is a genuine Bochner integral on the Haar
  measure of the multiplicative group `ℝ₊`.
- The Calderón reproducing formula
  `f = c · ∫₀^∞ ψ(sL)* ψ(sL) f ds/s`
  is a theorem about unbounded self-adjoint operators.

**In our finite-dimensional, self-adjoint setting, all three collapse
into linear algebra.**  Concretely:

### 3.1 `SectorialFunctionalCalculus` via spectral decomposition

Let `V` be our finite vertex set, `L : Matrix V V ℝ` self-adjoint
under `inner_pi π hπ` (this is exactly the `h_sa` hypothesis threaded
through the spectral-stability chain).  Then `L` has an orthogonal
eigendecomposition

```
L = ∑ᵢ λᵢ · (eᵢ ⊗ eᵢ)
```

where `{eᵢ}` is a `π`-orthonormal eigenbasis.  This is available in
Mathlib via `Matrix.IsHermitian.eigenvectorBasis` (after transport
through the weighted inner product isometry already proved in
`NormedBridge.lean`, Priority 1 of this sprint).

For any continuous `ψ : ℝ → ℝ` (such as our
`hermiteGaussianFilter α β`), define

```lean
def sectorialFunctionalCalculus_SA (L : Matrix V V ℝ) (hL_sa : IsSymm_pi L π)
    (ψ : ℝ → ℝ) (s : ℝ) (hs : 0 < s) : Matrix V V ℝ :=
  -- reconstruct L *as a matrix* from its spectral decomposition,
  -- replacing each eigenvalue λᵢ by ψ(s·λᵢ).
  ∑ i, ψ (s * eigenvalues L i) • (eigenvectorMatrix L) (columnProjector i)
```

Exact Lean signature TBD — the spectral-decomposition machinery for
`Matrix.IsHermitian` lives in `Mathlib.LinearAlgebra.Matrix.Hermitian`
and requires a complex → real transport, but the intent is that `ψ(sL)`
is a **definable matrix** with **provable properties**
(`commutes_semigroup`, `scaling`) rather than axioms.

The two commutativity/scaling axioms then follow from:
- *Commutativity with `HeatKernel L t = exp(tL)`*: both operators are
  polynomials in the common eigenbasis, so they commute trivially.
- *Scaling*: `ψ(cs · λᵢ) = ψ(s · (cλᵢ))` is identity on real functions.

### 3.2 `ScaleIntegratedEnergy` via Plancherel

In the diagonal basis, for `f = ∑ᵢ fᵢ eᵢ`:

```
‖ψ(sL) f‖²_π  =  ∑ᵢ |ψ(s·λᵢ)|² · |fᵢ|²
```

So the scale-integrated energy is

```
∫₀^∞ ‖ψ(sL) f‖²_π · ds/s
    =  ∑ᵢ |fᵢ|² · ∫₀^∞ |ψ(s·λᵢ)|² · ds/s
    =  ∑ᵢ |fᵢ|² · ∫₀^∞ |ψ(u)|² · du/u     (substitute u = s·λᵢ)
    =  ‖f‖²_π  ·  Cₚ(ψ)
```

where `Cₚ(ψ) := ∫₀^∞ |ψ(u)|² du/u` is the **Calderón constant of ψ**.
For the normalised HG filter from Phase 2E,
`Cₚ(ψ̃_{α,β}) = 1` exactly — so the frame is **automatically tight
with `A = B = 1`** for every self-adjoint `L` with positive spectrum.

This is the structural content that lets `tight_frame_representation_error_zero`
become a theorem: **for Calderón-normalised ψ and self-adjoint L, the
canonical frame is canonically tight, no existence axiom needed.**

### 3.3 `RepresentedStabilityFlow` as a derivative of the reconstruction

The paper writes the reconstruction as

```
(T_ψ f)(x)  :=  ∫₀^∞  ψ(sL)* ψ(sL) f  ds/s
            =  Cₚ(ψ) · f       (for self-adjoint L)
```

(Plancherel on the multiplicative group, as in §3.2).  So the
**represented version of any observable `f(t)`** — be it `K_norm`, a
heat-trace functional, or whatever — is

```
f_rep(t)  :=  T_ψ (f(t))  =  Cₚ(ψ) · f(t)
```

and the **represented stability flow** of the log-return observable is

```
β_rep(t)  :=  deriv (fun s => ∑_x π_x · log(1 − (T_ψ K)(s,x,x)/π_x + ε)) t
```

For a tight frame (`Cₚ = 1`), `T_ψ K(s,x,x) = K(s,x,x)`, so
`β_rep(t) = β_intrinsic(t)` exactly.  **The error-zero axiom becomes a
`rfl`-level rewrite.**

### 3.4 Honest qualifier: where self-adjointness comes from

The SGC paper's `L` is a *rate matrix* — not obviously self-adjoint.
But under the **detailed-balance (reversibility)** assumption
`π_x L_{xy} = π_y L_{yx}` it becomes self-adjoint under `⟨·,·⟩_π`.
This is *exactly* the `h_sa` / `h_rel` hypothesis already threaded
through `spectral_stability_bound`.

For *non-reversible* chains, the story is different: `L` is sectorial
but not self-adjoint, and the spectral decomposition uses *generalised
eigenvectors* (Jordan form).  That is a genuine extra layer of work.
**Scope decision**: the refactor targets the reversible case, which is
already the setting of every Phase-4 theorem via `h_sa`.

## 4. Target Lean signatures (post-refactor)

This section gives the *aspirational* definitions we are aiming at.
Exact formulations will evolve as the refactor proceeds, but these
sketch the structural commitments.

### 4.1 Finite-dimensional spectral calculus

```lean
/-- The π-weighted self-adjointness condition on L. -/
def IsSymmPi (L : Matrix V V ℝ) (π : V → ℝ) (hπ : ∀ v, 0 < π v) : Prop :=
  ∀ u v : V → ℝ, inner_pi π hπ (L *ᵥ u) v = inner_pi π hπ u (L *ᵥ v)

/-- `ψ(sL)` as a *matrix*, constructively built from the spectral
    decomposition of L under ⟨·,·⟩_π. -/
noncomputable def funCalculus (L : Matrix V V ℝ) {π : V → ℝ}
    (hπ : ∀ v, 0 < π v) (hL : IsSymmPi L π hπ)
    (ψ : ℝ → ℝ) (s : ℝ) : Matrix V V ℝ :=
  /- Use Matrix.IsHermitian.spectralTheorem (after transport through
     NormedBridge's weightedToStd isometry) to decompose L, apply ψ
     pointwise to the eigenvalues scaled by s, reassemble. -/
  sorry
```

The three functional-calculus axioms become:

```lean
theorem funCalculus_commutes_heat (L : Matrix V V ℝ) {π} (hπ) (hL)
    (ψ : ℝ → ℝ) (s t : ℝ) :
    funCalculus L hπ hL ψ s * HeatKernel L t =
    HeatKernel L t * funCalculus L hπ hL ψ s := by
  /- Both operators diagonalise in the shared eigenbasis; polynomials
     in commuting operators commute. -/
  sorry

theorem funCalculus_scaling (L : Matrix V V ℝ) {π} (hπ) (hL)
    (ψ : ℝ → ℝ) (s c : ℝ) (hc : 0 < c) :
    funCalculus L hπ hL ψ (c * s) =
    funCalculus (c • L) hπ (IsSymmPi.smul hL c) ψ s := by
  /- Eigenvalues of c•L are c·λᵢ; apply ψ(cs·λᵢ) = ψ(s·(cλᵢ)). -/
  sorry
```

### 4.2 Scale-integrated energy

```lean
/-- Scale-integrated energy as a *defined* integral over Ioi 0. -/
noncomputable def scaleIntegratedEnergy (L : Matrix V V ℝ) (π : V → ℝ)
    (hπ : ∀ v, 0 < π v) (hL : IsSymmPi L π hπ)
    (ψ : ℝ → ℝ) (f : V → ℝ) : ℝ :=
  ∫ s in Set.Ioi (0 : ℝ),
    norm_sq_pi π (funCalculus L hπ hL ψ s *ᵥ f) / s

/-- Key Plancherel identity: for Calderón-normalised ψ, the energy
    equals ‖f‖²_π (frame is tight with A = B = 1). -/
theorem scaleIntegratedEnergy_calderon (L : Matrix V V ℝ) {π hπ hL}
    {ψ : ℝ → ℝ} (hψ : IsCalderonNormalized ψ)
    (hL_pos : ∀ i, 0 < eigenvalue L i)
    (f : V → ℝ) :
    scaleIntegratedEnergy L π hπ hL ψ f = norm_sq_pi π f := by
  /- Diagonalise, swap integral and finite sum, substitute u = s·λᵢ,
     use Calderón normalisation. -/
  sorry
```

### 4.3 The synthesis operator and represented flow

```lean
/-- Synthesis operator: T_ψ f = ∫₀^∞ ψ(sL)² f · ds/s (self-adjoint case). -/
noncomputable def synthesisOperator (L : Matrix V V ℝ) (π : V → ℝ)
    (hπ : ∀ v, 0 < π v) (hL : IsSymmPi L π hπ)
    (ψ : ℝ → ℝ) : Matrix V V ℝ :=
  /- In Bochner-integral form; on self-adjoint L this equals
     Cₚ(ψ) · I_V by Plancherel. -/
  sorry

/-- Represented stability flow: the derivative of the log-return
    observable computed through the synthesis operator. -/
noncomputable def representedStabilityFlow (L : Matrix V V ℝ)
    (π : V → ℝ) (hπ : ∀ v, 0 < π v) (hL : IsSymmPi L π hπ)
    (ψ : ℝ → ℝ) (ε : ℝ) (t : ℝ) : ℝ :=
  deriv (fun s => ∑ x, π x *
          Real.log ((synthesisOperator L π hπ hL ψ *
                     (1 - fun y => HeatKernel L s y y / π y)) x + ε)) t

/-- On Calderón-normalised ψ, synthesis is the identity (scaled). -/
theorem synthesisOperator_calderon_id (L : Matrix V V ℝ) {π hπ hL}
    {ψ : ℝ → ℝ} (hψ : IsCalderonNormalized ψ)
    (hL_pos : ∀ i, 0 < eigenvalue L i) :
    synthesisOperator L π hπ hL ψ = 1 := by
  /- Spectral diagonalisation + Calderón constant = 1. -/
  sorry

/-- **Discrete Calderón reproducing formula, as a theorem**. -/
theorem represented_equals_intrinsic_on_calderon (L : Matrix V V ℝ)
    {π hπ hL} {ψ : ℝ → ℝ} (hψ : IsCalderonNormalized ψ)
    (hL_pos : ∀ i, 0 < eigenvalue L i) (ε t : ℝ) :
    representedStabilityFlow L π hπ hL ψ ε t =
    stability_flow L π ε t := by
  /- T_ψ = I by the above lemma ⇒ synthesis of K_norm is K_norm itself
     ⇒ represented flow is intrinsic flow by pointwise equality. -/
  simp [representedStabilityFlow, synthesisOperator_calderon_id hψ hL_pos,
        stability_flow, expected_log_return_prob]
```

## 5. Phased refactor plan

Each phase is scoped to land as a self-contained commit (≤ 1 sprint).
Axiom-count deltas are cumulative *upper bounds* — we may accept less
if a phase hits genuine blockers.

### Phase R1 — Spectral decomposition bridge *(1–2 sprint days)*

**Deliverable**: the `Matrix.IsHermitian.spectralTheorem` machinery
transported through `NormedBridge.weightedToStd` so it applies to
`IsSymmPi L π hπ`.

**New lemmas**:
- `IsSymmPi_iff_isHermitian_transport : IsSymmPi L π hπ ↔
    (weightedToStd ∘ L ∘ weightedToStd.symm).IsHermitian`
- `funCalculus` definition (via `IsHermitian.eigenvectorBasis`).
- `funCalculus_apply_eigenvector` (the diagonalisation lemma).

**Axioms discharged**: 0 (structural prep).
**Risk**: medium — Mathlib's spectral theorem for matrices exists but is
complex to thread through non-standard inner products.  Mitigation:
first prove on the standard inner product, then transport at the end.

### Phase R2 — Functional calculus axioms → theorems *(0.5–1 sprint day)*

**Deliverable**: replace the three functional-calculus axioms with
theorems proved from `funCalculus`.

**Axioms discharged**: `SectorialFunctionalCalculus` (now a `def`),
`functional_calculus_commutes_semigroup`, `functional_calculus_scaling`.
**Count delta**: –3 axioms.
**Risk**: low — pure linear algebra given Phase R1.

### Phase R3 — `ScaleIntegratedEnergy` as an honest integral *(1–2 sprint days)*

**Deliverable**: `scaleIntegratedEnergy` definition (the Bochner
integral) + the Plancherel theorem (`scaleIntegratedEnergy_calderon`).

**Axioms discharged**: `ScaleIntegratedEnergy` (now a `noncomputable
def`).
**Count delta**: –1 axiom (cumulative: –4).
**Risk**: medium.  The `Ioi 0` integral + the `s ↦ 1/s` change-of-
variable in Mathlib is not as well-trodden as the Gamma-function
integrals from Phase 2E, but `integral_comp_smul_deriv` and related
substitution lemmas should handle it.  Fallback: discretise the
integral as a finite sum over a user-chosen scale grid, which is
still structurally better than an axiom.

### Phase R4 — `RepresentedStabilityFlow` constructive *(1–2 sprint days)*

**Deliverable**: `representedStabilityFlow` as the `deriv` of the
reconstructed log-return observable, via `synthesisOperator`.

**Prerequisites**: R1 + R2 + R3.

**Axioms discharged**:
- `RepresentedStabilityFlow` (now a `noncomputable def`).
- `tight_frame_representation_error_zero` (now a theorem, provable by
  `synthesisOperator_calderon_id` + `rfl`-level unfolds).

**Count delta**: –2 axioms (cumulative: –6).

This also promotes:
- `tight_frame_zero_error`, `tight_frame_zero_error_direct`,
  `tight_frame_exact_reconstruction`: all remain theorems but their
  proofs simplify dramatically (no longer hide behind an existence
  axiom).

**Risk**: low–medium.  The main work is *threading the new `hL_sa`
hypothesis* through every downstream specialisation (including Phase 4
files that already exist).  Signature churn, not proof complexity.

### Phase R5 — Propagate through HG-specific theorems *(0.5 sprint day, optional)*

**Deliverable**: update `HermiteGaussianCanonical.lean`,
`CanonicalWaveletFisherRao.lean`, and `RepresentedStabilityFlowDecay.lean`
to use the constructive `representedStabilityFlow` + the
`IsCalderonNormalized (hermiteGaussianFilterNormalized α β)` proof
from Phase 2E.

**Axioms discharged**: 0 (downstream cleanup).
**Count delta**: 0.
**Risk**: trivial — mechanical renames and hypothesis threading.

### Cumulative delta

| Phase | Cost (days) | Axioms discharged | Cumulative |
|-------|-------------|-------------------|------------|
| R1    | 1–2         | 0                 | 0          |
| R2    | 0.5–1       | 3                 | 3          |
| R3    | 1–2         | 1                 | 4          |
| R4    | 1–2         | 2                 | 6          |
| R5    | 0.5         | 0                 | 6          |
| **Total** | **4–7.5** | **6 axioms** | **6**      |

For comparison, Priority 1 of this sprint eliminated 3 axioms in
~1 day.  R1–R4 as a package is ~4 sprint days for 6 axioms, roughly
the same ratio.

## 6. Risks and remaining axioms in the ideal case

Even after R1–R5, the following remain axiomatic and are **genuinely
hard to discharge**:

1. **`geometric_commutator_constraint`** (paper §4.2): the claim that
   `‖[L, Γ₂]‖ ≥ some defect quantity`.  This is genuine research
   territory — the *statement itself* requires a paper-convention
   audit because the current Lean version appears stronger than the
   paper's claim.

2. **`constant_ricci_tight_frame_exists`**: existence of a tight frame
   on constant-Ricci spaces.  This is interesting because *after
   R1–R4* the answer is **trivially yes** for any self-adjoint `L` —
   the canonical HG frame at Calderón normalisation is already tight.
   So this axiom may simply be **retired as redundant**.

3. `weighted_compactness` family: already discharged in Priority 1 of
   this sprint, commit `500ca6e`.

There are also **optional strengthening axioms** that the current
codebase doesn't need but might want later (e.g., `L`'s positivity
threshold for the Gamma-integral substitution in §3.2).  These would be
introduced fresh in the refactor commit; none would increase the net
count.

## 7. Recommended first move

**Phase R1 is the correct first sprint.**  Rationale:

- It has the largest unknown (Mathlib's `Matrix.IsHermitian`
  ergonomics under a non-standard inner product).
- It blocks R2, R3, R4 strictly.
- It produces no axiom reduction on its own, so there is no temptation
  to stop early.
- Once R1 is done, R2–R4 are almost entirely mechanical.

Estimate: 1–2 sprint days.

### Alternative first move (conservative): discrete-scale fallback

If Mathlib's matrix spectral theorem proves unwieldy at the weighted-
inner-product level, a **discrete scale grid** version of the refactor
is available:

```lean
structure DiscreteScaleGrid where
  scales : Finset ℝ
  pos : ∀ s ∈ scales, 0 < s

noncomputable def scaleIntegratedEnergy_discrete (grid : DiscreteScaleGrid)
    (L : Matrix V V ℝ) (π : V → ℝ) (hπ : ∀ v, 0 < π v)
    (hL : IsSymmPi L π hπ) (ψ : ℝ → ℝ) (f : V → ℝ) : ℝ :=
  ∑ s ∈ grid.scales, norm_sq_pi π (funCalculus L hπ hL ψ s *ᵥ f) / s
```

This sidesteps the `Ioi 0` integral and the `ds/s` Haar-measure issues
entirely.  Axiom reduction remains 6; the cost is that "the Calderón
reproducing formula" becomes "the Calderón reproducing formula *at
this particular scale grid*", which is mathematically weaker but
Lean-tractable.  **Acceptable fallback if Phase R3 hits a wall.**

## 8. Open questions for the user

1. **Scope**: is the reversible-chain assumption acceptable, or should
   the refactor target general (non-reversible) rate matrices?  (The
   latter is ~3× harder; no SGC application currently uses it.)

2. **Integration setting**: full Bochner integral over `Ioi 0` (Phase
   R3 proper) vs. discrete-scale fallback (§7 alternative)?  The
   former is "more correct"; the latter is "more tractable".
   Recommendation: start with full Bochner, downgrade only if blocked.

3. **Branching**: should R1–R4 land as a single atomic commit (big
   review unit, clean diff) or as a five-commit chain on a dedicated
   `phase-R` feature branch?  Recommendation: five commits on
   `lean-foundation-phases-1-2c` directly (consistent with the sprint's
   existing cadence).

4. **Deferred work**: do we also want to scope
   `geometric_commutator_constraint` at the same time, or leave it
   for a dedicated paper-convention audit sprint?  Recommendation:
   defer.  The constraint statement needs to be corrected before any
   Lean work.

## 9. Summary line for the commit message

> `RepresentedStabilityFlow` axiom → constructive definition via
> finite-dim spectral decomposition; `ScaleIntegratedEnergy` →
> Bochner integral; five functional-calculus axioms become theorems;
> `tight_frame_representation_error_zero` becomes a short corollary
> of `synthesisOperator_calderon_id`.  Net axiom reduction: 6.

---

**Next action after this design is accepted**: begin Phase R1
(spectral-decomposition bridge) on a new commit.  Nothing in this
document edits Lean source; the doc is written as a pre-commit
scoping artefact.
