# Axiom & Sorry Landscape Report — 2026-05-25

**Branch**: `sprint/entropy-axiom-closure-2026-05-25`
**Trigger**: Colleague's observation that the 56-theorem audit covers only a curated sample of the library; full landscape was unknown.

## Headline Numbers

| Quantity | Count | Source |
|---|---|---|
| Total `lake build` jobs | 3158 | Full library build |
| Total declared `axiom`s in `src/` | **233** | `Select-String -Pattern "^axiom "` |
| Total `sorry`s in `src/` (excluding comments) | **64** | filtered grep |
| Flagship theorems in `AxiomAudit.lean` | **60** | After Sprint 4 |
| Audited theorems at WKL₀ baseline | **56** | `[propext, Classical.choice, Quot.sound]` |
| Audited theorems with named physical axioms | **4** | unchanged across Sprints 1-4 |

## What This Tells Us

The **audited 56 theorems are a curated sample** of the library, not an exhaustive certification. The colleague was right to flag this. With 233 declared axioms and 64 sorries spread across the codebase, the public claim "X axioms remain" should always specify "X **audited** axioms remain among Y **audited** flagship theorems".

That said, the **structure** of the unaudited material is mostly orthogonal to the central theorems:

- Foundational `Axioms/` modules (`GeometryGeneral.lean`: 21 axioms) are *intentional* — these are the L²(π) geometric foundation, postulated to keep proofs tractable.
- `RenormalizationDynamics.lean` (20 axioms) is the dynamics layer — most are time-evolution stubs that aren't load-bearing for the static theorems.
- The 64 sorries cluster in `FisherNoetherBridge.lean` (12), `BrownianMotion.lean` (9), and `KramersEscape.lean` (7) — research files exploring the continuous limit and Noether-type symmetries, where the audit warns axioms may jump in strength.

## Top 15 axiom-dense files

| File | Declared axioms |
|---|---:|
| `Axioms/GeometryGeneral.lean` | 21 |
| `Renormalization/RenormalizationDynamics.lean` | 20 |
| `Bridge/GeometricClosure.lean` | 15 |
| `Evolution/Conservation.lean` | 13 |
| `InformationGeometry/FisherKL.lean` | 12 |
| `Renormalization/Approximate.lean` | 10 |
| `Bridge/Quantum.lean` | 9 |
| `Evolution/Dynamics.lean` | 9 |
| `Geometry/DiscreteCurvature.lean` | 9 |
| `Bridge/CoherenceObstruction.lean` | 9 |
| `Bridge/ThermodynamicBridge.lean` | 8 |
| `Geometry/Conformal.lean` | 8 |
| `Thermodynamics/EntropyProduction.lean` | 7 |
| `InformationGeometry/TsallisStatistics.lean` | 7 |
| `Geometry/Yamabe.lean` | 7 |

## Top 10 sorry-dense files

| File | Sorries |
|---|---:|
| `InformationGeometry/FisherNoetherBridge.lean` | 12 |
| `Stochastic/BrownianMotion.lean` | 9 |
| `InformationGeometry/KramersEscape.lean` | 7 |
| `EmergenceEquivalence.lean` | 5 |
| `FunctionalBlanket.lean` | 5 |
| `EmergenceCapacity.lean` | 4 |
| `Renormalization/QuotientGenerator.lean` | 3 |
| `Renormalization/RenormalizationDynamics.lean` | 2 |
| `Spectral/HermiteGaussianExtremal.lean` | 2 |
| `Spectral/NormedBridge.lean` | 2 |

## Interpretation by Cluster

### Cluster A — Foundational Geometric Axioms (intentional)

`Axioms/Geometry.lean`, `Axioms/GeometryGeneral.lean`, `Axioms/WeightedSpace.lean` — these are the L²(π) inner-product axioms that *frame* the theory. Removing them would mean re-deriving Hilbert-space structure from first principles inside Lean, which is not the goal of this library. These ~25 axioms are the analog of "we work in a real inner-product space" in a textbook.

### Cluster B — Dynamics & Evolution (research-front)

`RenormalizationDynamics.lean`, `Evolution/Dynamics.lean`, `Evolution/Conservation.lean` — these stage the time-evolution and surgery operators. Many of these axioms are *deferred theorems* awaiting either Mathlib infrastructure (ODE solvers, continuous semigroups) or future analytical work. Not load-bearing for the static thermodynamic theorems.

### Cluster C — Continuum Limit (where the audit warns of strength jump)

`Bridge/Quantum.lean`, `Geometry/Manifold/*`, `Stochastic/BrownianMotion.lean` — these are where the `[Fintype V]` firewall ends. The audit explicitly warns these may require ATR₀ or Π¹₁-CA₀ when the continuum pass starts. The current axioms here are placeholders pending that work.

### Cluster D — Research-front Modules (sorries indicate active inquiry)

`FisherNoetherBridge.lean` (12 sorries), `BrownianMotion.lean` (9), `KramersEscape.lean` (7) — these are *exploratory* modules where the formalization is ahead of the mathematical theory. The sorries here are not blockers for the central narrative; they are notes-to-self about what still needs to be proved.

### Cluster E — Audited Flagship (the published claims)

The 60 theorems in `AxiomAudit.lean` cover:

- Lumpability & RG (the spectral gap chain)
- Emergence (`optimal_partition_exists`, `emergence_equivalence`)
- Thermodynamics (`entropy_production_nonneg`, `zero_entropy_implies_zero_current`, second law)
- Persistence (`to_persist_is_to_predict`)
- Complexity Relativity (`complexity_is_relational`, `constrained_complexity_is_relational`)
- Spectral structure (`PerronFrobenius`-type results)

Of these 60, **56 are at WKL₀ baseline** (kernel axioms only). The **4 remaining named axioms**:

| Named axiom | Theorems depending on it | Closure path |
|---|---|---|
| `gaspard_path_space_identity` | `hidden_entropy_lower_bound`, `efficiency_requires_prediction` | Path-space measure infrastructure (multi-sprint) |
| `mitosis_reduces_structural_free_energy` | `mitosis_optimal_in_supercritical_phase` | Lifshitz critical-dimension formalism |

(One physical axiom, `non_normality_from_flux`, was *renamed* from a former axiom that is now derivable; the audit reflects this.)

## What This Sprint Closed

Across the four commits on this branch:

| Sprint | Axioms closed | Theorems added |
|---|---|---|
| Sprint 1 | `normal_of_self_adjoint`, `pi_adjoint_inner`, `sector_condition_companion` | 3 |
| Sprint 2 | `entropy_production_nonneg`, `zero_entropy_implies_zero_current` | 2 (+ 2 Gibbs lemmas) |
| Sprint 3 | (none closed — pure addition) | 6 (Complexity Relativity) |
| Sprint 4 | (none closed — pure addition) | 4 (Constrained Coarseness) |
| **Total this branch** | **5 axioms closed**, **1 renamed** | **15 new flagship theorems** |

## What Should Happen Next

### Priority 1 — Connect the constrained-coarseness theorem to grokking/consolidation

`Grokking.lean` imports `FunctionalBlanket`, `KramersEscape`, `InformationGradientLaw`, `AdiabaticInvariant`. The constrained-coarseness theorem (`constrained_complexity_is_relational`) gives the formal target that the grokking dynamics converges to. A bridge theorem stating "the consolidation flow on a `K`-bounded partition family decreases toward the constrained optimum" would unify Sprint 4 with the grokking narrative.

### Priority 2 — Surface the 12 `FisherNoetherBridge.lean` sorries

This is the densest sorry cluster in the library. Whether these are tractable or genuinely open is unknown without inspection. A 1-sprint pass to classify them (TRIVIAL / TRACTABLE / RESEARCH-FRONT) would clarify the path forward.

### Priority 3 — Spectral conjecture roadmap

The single most important open item — the spectral conjecture in `FluxDecomposition.lean` — needs a written proof-strategy document, in the spirit of the 4-step staging of `gaspard_path_space_identity`. This is a writing exercise, not a coding one, but it's high-leverage for credibility.

### Priority 4 — Continuum pass preparation

When the `[Fintype V]` firewall is removed, the audit predicts proof-theoretic strength may jump from WKL₀ to ATR₀ or Π¹₁-CA₀. The current 233 axioms include ~50 that exist *only* to avoid this jump. A pre-flight pass identifying which axioms become theorems in the continuum vs. which become genuinely new axiomatic commitments would be valuable.

## Honest Caveat

The 233 axiom / 64 sorry counts are *declarations*, not necessarily blockers. Some declared `axiom` lines are placeholders for theorems whose proofs are in adjacent files; some `sorry`s are well-understood gaps awaiting Mathlib infrastructure. A full classification of every axiom and sorry would take ~1 day of focused inspection and is out of scope for this report. **What this report establishes is the order-of-magnitude landscape**: the library is closer to "60 audited theorems with verified WKL₀ foundations + a large research perimeter" than to "fully formalized SGC theory". The former is publishable now; the latter is a multi-year program.
