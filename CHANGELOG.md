# Changelog

All notable changes to the UPAT (Universal Predictive Assembly Theory) formalization are documented in this file.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

---

## [v2.0-dev] - 2024-12-22 — The Constructive Turn

### Added

- **Information Bridge** (`UPAT.Information`)
  - `UPAT.Information.Gaussian`: Formalized differential entropy for multivariate Gaussians.
    - `GaussianCovariance`: Structure for positive definite covariance matrices.
    - `differentialEntropy`: h(X) = (n/2)log(2πe) + (1/2)log(det(Σ)).
    - `PrecisionMatrix`: Abstraction encoding conditional independence structure.
    - `precision_zero_implies_cond_indep`: Zero precision entry implies zero partial correlation.
  
  - `UPAT.Information.Equivalence`: Proved the central Information-Geometry equivalence.
    - `conditionalMutualInfo`: CMI abstracted as sum of absolute precision entries.
    - `gaussian_cmi_zero_iff_precision_zero`: CMI = 0 ⟺ precision block is zero.
    - `IsDynamicalBlanket` / `IsInformationBlanket`: Dual characterizations of blankets.
    - `dynamical_blanket_iff_information_blanket`: The Gaussian Lemma.
    - `information_geometry_equivalence`: **Central theorem** — `RespectsBlank` ⟺ `IsInformationBlanketV` for symmetric generators.
    - `orthogonality_iff_zero_information`: Connects v1 `blanket_orthogonality` to v2 information theory.

- **Manifold Scaffolding** (`UPAT.Geometry.Manifold`) — *Under Construction*
  - `Laplacian.lean`: Scaffolding for Laplace-Beltrami operator.
  - `Convergence.lean`: Scaffolding for Belkin-Niyogi convergence theorem.
  - Note: These modules contain `sorry` placeholders and are not part of the verified core.

### Changed

- Updated `src/UPAT.lean` manifest to include v2 modules.
- README.md updated to reflect v2 progress and theorem index.

### Status

| Module | Verified | Sorries |
|--------|----------|---------|
| `UPAT.Information.Gaussian` | ✅ | 0 |
| `UPAT.Information.Equivalence` | ✅ | 0 |
| `UPAT.Geometry.Manifold.Laplacian` | 🚧 | — |
| `UPAT.Geometry.Manifold.Convergence` | 🚧 | — |

---

## [v1.0-verified] - 2024-12-21 — The Four Pillars

### Established

The foundational architecture of UPAT, organized into four logical pillars:

- **Stability** (`UPAT.Stability`)
  - `FunctorialHeatDominanceTheorem`: Spectral stability of non-reversible Markov chains.
  - Derived from the Sector Envelope and Diagonal Bridge constructions.

- **Scalability** (`UPAT.Stability.Functoriality.Lumpability`)
  - `gap_non_decrease`: The spectral gap is preserved (bounded below) under coarse-graining.
  - Proves functorial preservation of stability under renormalization.

- **Vitality** (`UPAT.Vitality.DoobMeyer`)
  - `doob_decomposition`: S_n = M_n + A_n (Surprise = Martingale + Predictable Drift).
  - Formalizes the thermodynamic arrow of complexity accumulation.

- **Kinetics** (`UPAT.Kinetics.LeastAction`)
  - `emergence_is_necessary`: Derived from the Principle of Least Action.
  - Proves that thermodynamic systems naturally maximize complexity accumulation.

### Supporting Infrastructure

- **`UPAT.Axioms.Geometry`**: Explicit L²(π) metric space structures.
- **`UPAT.Topology.Blanket`**: Markov Blankets via geometric orthogonality.
  - `BlanketPartition`: Partition into internal, blanket, external.
  - `RespectsBlank`: Generator respects blanket topology.
  - `blanket_orthogonality`: Internal and external functions are orthogonal.
- **`UPAT.Bridge.Discretization`**: Discrete-to-continuum interface.
  - `ContinuumTarget`: Oracle for continuum limit behavior.
  - `IsLinearBlanket`: Linear blanket abstraction.

### Verification

- **Total Sorries:** 0
- **Build Status:** ✅ Passing
- Full verification documented in `VERIFIED_CORE_MANIFEST.md`.

---

## Versioning Philosophy

- **v1.x**: Architecture — Establishing the Four Pillars and axiomatic bridges.
- **v2.x**: Depth — Constructive proofs connecting axioms to physics.
- **v3.x (Future)**: Applications — Concrete instantiations and computational examples.

---

## References

- [Cover-Thomas] Elements of Information Theory
- [Lauritzen] Graphical Models
- [Belkin-Niyogi] Towards a Theoretical Foundation for Laplacian-Based Manifold Methods
- [Lee] Riemannian Manifolds: An Introduction to Curvature
