# UPAT: Universal Predictive Assembly Theory

[![Build](https://github.com/JasonShroyer/fhdt-lean4/actions/workflows/build.yml/badge.svg)](https://github.com/JasonShroyer/fhdt-lean4/actions/workflows/build.yml)
[![Lean 4](https://img.shields.io/badge/Lean-4-blue.svg)](https://lean-lang.org/)
[![Zero Sorries](https://img.shields.io/badge/sorries-0-brightgreen.svg)](VERIFIED_CORE_MANIFEST.md)
[![Release](https://img.shields.io/badge/release-v2.0--dev-orange.svg)](https://github.com/JasonShroyer/fhdt-lean4)

This repository contains the `sorry-free` Lean 4 formalization of **Universal Predictive Assembly Theory (UPAT)**. 

UPAT extends the spectral stability of Markov chains (FHDT) into a general theory of emergence, formalizing how complexity accumulates in thermodynamic systems via the **Four Pillars** architecture.

**Current Status:** v2.0-dev — Core theory verified; Information Bridge complete.

---

## The Four Pillars of Formalization

The library is organized into four logical modules (`src/UPAT/`):

### 1. Stability (The Foundation)
- **Module:** `UPAT.Stability` 
- **Physics:** Establishes that non-reversible Markov chains converge to equilibrium exponentially fast.
- **Key Theorem:** `FunctorialHeatDominanceTheorem` (Derived from the Sector Envelope and Diagonal Bridge).

### 2. Scalability (Functoriality)
- **Module:** `UPAT.Stability.Functoriality.Lumpability` 
- **Physics:** Proves that stability is preserved under renormalization (coarse-graining).
- **Key Theorem:** `gap_non_decrease` (The spectral gap of a lumped chain is bounded below by the original gap).

### 3. Vitality (Thermodynamics)
- **Module:** `UPAT.Vitality.DoobMeyer` 
- **Physics:** Decomposes the "Surprise" (Self-Information) process into predictable work and martingale innovation.
- **Key Theorem:** `doob_decomposition` ($S_n = M_n + A_n$).

### 4. Kinetics (The "Why")
- **Module:** `UPAT.Kinetics.LeastAction` 
- **Physics:** Proves that thermodynamic systems naturally maximize the accumulation of complexity (Predictable Drift).
- **Key Theorem:** `emergence_is_necessary` (Derived from the Principle of Least Action).

---

## Bridges & Axioms

- **`UPAT.Axioms.Geometry`**: Defines the explicit $L^2(\pi)$ metric space structures without heavy typeclass overhead.
- **`UPAT.Topology.Blanket`**: Formalizes Markov Blankets via geometric orthogonality rather than information theory.
- **`UPAT.Bridge.Discretization`**: Connects the discrete graph operators to continuous manifold physics.

---

## v2 Extensions (The Constructive Turn)

Recent work (v2) extends the core theory with constructive proofs linking the geometric axioms to fundamental physics:

### Information Geometry (Formalized)
- **Module:** `UPAT.Information`
- **Status:** ✅ Verified (sorry-free)
- **Physics:** Proves that geometric orthogonality is equivalent to conditional independence (vanishing Conditional Mutual Information) in the Gaussian limit.
- **Key Theorem:** `information_geometry_equivalence` — For reversible systems, `RespectsBlank` (geometric) ⟺ `IsInformationBlanketV` (information-theoretic).

### Continuum Limits (Scaffolding)
- **Module:** `UPAT.Geometry.Manifold`
- **Status:** 🚧 Under Construction
- **Physics:** Scaffolding for the Belkin-Niyogi convergence theorem (graph Laplacians → Laplace-Beltrami operators).
- **Goal:** Validate the `ContinuumTarget` axiom constructively.

---

## Theorem Index

| Theorem | Module | Description |
|---------|--------|-------------|
| `FunctorialHeatDominanceTheorem` | `UPAT.Stability` | Spectral stability of non-reversible chains |
| `gap_non_decrease` | `UPAT.Stability.Functoriality.Lumpability` | Functorial preservation under coarse-graining |
| `doob_decomposition` | `UPAT.Vitality.DoobMeyer` | Thermodynamic decomposition of surprise |
| `emergence_is_necessary` | `UPAT.Kinetics.LeastAction` | Least Action derivation of drift maximization |
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
