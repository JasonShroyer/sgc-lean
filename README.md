# UPAT: The Spectral Geometry of Consolidation

[![Build](https://github.com/JasonShroyer/fhdt-lean4/actions/workflows/build.yml/badge.svg)](https://github.com/JasonShroyer/fhdt-lean4/actions/workflows/build.yml)
[![Lean 4](https://img.shields.io/badge/Lean-4-blue.svg)](https://lean-lang.org/)
[![Zero Sorries](https://img.shields.io/badge/sorries-0-brightgreen.svg)](VERIFIED_CORE_MANIFEST.md)

This repository contains the `sorry-free` Lean 4 formalization of the **UPAT framework** — a rigorous mathematical treatment of structural persistence in stochastic systems.

UPAT formalizes how stable structures emerge and persist in thermodynamic systems by combining spectral geometry, stochastic thermodynamics, and variational principles.

---

## The Four Pillars of Formalization

The library is organized into four logical modules (`src/UPAT/`):

### 1. Spectral Geometry (The Foundation)
- **Module:** `UPAT.Spectral` 
- **Physics:** Establishes that non-reversible Markov chains converge to equilibrium exponentially fast via spectral gap bounds.
- **Key Theorem:** `FunctorialHeatDominanceTheorem` (Derived from the Sector Envelope and Diagonal Bridge).

### 2. Renormalization (Scale Invariance)
- **Module:** `UPAT.Renormalization.Lumpability` 
- **Physics:** Proves that spectral stability is preserved under coarse-graining (renormalization group flow).
- **Key Theorem:** `gap_non_decrease` (The spectral gap of a lumped chain is bounded below by the original gap).

### 3. Thermodynamics (Stochastic Heat)
- **Module:** `UPAT.Thermodynamics.DoobMeyer` 
- **Physics:** The stochastic thermodynamics of surprise. Decomposes self-information into predictable work and martingale heat.
- **Key Theorem:** `doob_decomposition` ($S_n = M_n + A_n$).

### 4. Variational Mechanics (The "Why")
- **Module:** `UPAT.Variational.LeastAction` 
- **Physics:** Derives drift maximization from the Principle of Least Action.
- **Key Theorem:** `emergence_is_necessary` (Variational derivation of complexity accumulation).

---

## Bridges & Axioms

- **`UPAT.Axioms.Geometry`**: Defines the explicit $L^2(\pi)$ metric space structures without heavy typeclass overhead.
- **`UPAT.Topology.Blanket`**: Formalizes Markov Blankets via geometric orthogonality rather than information theory.
- **`UPAT.Bridge.Discretization`**: Defines the **Axiomatic Interface** for the continuum limit. Proves that any discretization satisfying these axioms (Gap Consistency) inherits thermodynamic stability. This separates the thermodynamic logic from the geometric implementation.

---

## Extensions

### Information Geometry
- **Module:** `UPAT.Information`
- **Physics:** Proves that geometric orthogonality is equivalent to conditional independence (vanishing Conditional Mutual Information) in the Gaussian limit.
- **Key Theorem:** `information_geometry_equivalence` — For reversible systems, `RespectsBlank` (geometric) ⟺ `IsInformationBlanketV` (information-theoretic).

### Continuum Limits
- **Module:** `UPAT.Geometry.Manifold`
- **Physics:** Scaffolding for the Belkin-Niyogi convergence theorem (graph Laplacians → Laplace-Beltrami operators).
- **Goal:** Constructive validation of the `ContinuumTarget` axiom.

---

## Theorem Index

| Theorem | Module | Description |
|---------|--------|-------------|
| `FunctorialHeatDominanceTheorem` | `UPAT.Spectral` | Spectral stability of non-reversible chains |
| `gap_non_decrease` | `UPAT.Renormalization.Lumpability` | Spectral gap preservation under coarse-graining |
| `doob_decomposition` | `UPAT.Thermodynamics.DoobMeyer` | Stochastic thermodynamic decomposition of surprise |
| `emergence_is_necessary` | `UPAT.Variational.LeastAction` | Variational derivation of drift maximization |
| `information_geometry_equivalence` | `UPAT.Information.Equivalence` | Geometry ⟺ Information equivalence |

---

## Build & Verify

Prerequisites: `elan`, `lake`.

```bash
# Clone the repository
git clone https://github.com/JasonShroyer/fhdt-lean4.git
cd fhdt-lean4

# Build the library
lake build

# The library root is located at src/UPAT.lean
```

---

## Verification Status

| Component | Status | Sorries |
|-----------|--------|---------|
| UPAT Core (v1) | ✅ Verified | 0 |
| FHDT Core | ✅ Verified | 0 |
| Information Bridge (v2) | ✅ Verified | 0 |
| Manifold Scaffolding (v2) | 🚧 In Progress | — |
| Full Build | ✅ Passing | 0 |

See [`VERIFIED_CORE_MANIFEST.md`](VERIFIED_CORE_MANIFEST.md) for the formal verification statement.
See [`CHANGELOG.md`](CHANGELOG.md) for the project history.

---

## License

Apache 2.0
