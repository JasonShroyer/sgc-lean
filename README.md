# SGC: The Spectral Geometry of Consolidation

[![Build](https://github.com/JasonShroyer/sgc-lean/actions/workflows/build.yml/badge.svg)](https://github.com/JasonShroyer/sgc-lean/actions/workflows/build.yml)
[![Lean 4](https://img.shields.io/badge/Lean-4-blue.svg)](https://lean-lang.org/)
[![Verified Core](https://img.shields.io/badge/core-verified-brightgreen.svg)](VERIFIED_CORE_MANIFEST.md)

This repository contains a formally verified Lean 4 library characterizing the **algebraic structure of metastability** in discrete stochastic systems. It integrates spectral geometry, stochastic thermodynamics, and variational methods to derive bounds on the stability of partitions in finite-state Markov chains.

**Scope:** The verified core establishes results for **finite state spaces** (`[Fintype V]`). Continuum limits are axiomatized via `SGC.Bridge.Discretization`, providing an honest interface for future formalization of analytic convergence results.

**New in v2:** Approximate lumpability is now a *derived theorem*, not an axiom. We prove that small kinematic defects (leakage between blocks) lead to bounded trajectory errors. See `trajectory_closure_bound` and `spectral_stability`.

---

## The Four Pillars of Formalization

The library is organized into four logical modules (`src/SGC/`):

### 1. Spectral Geometry (The Foundation)
- **Module:** `SGC.Spectral` 
- **Physics:** Establishes that non-reversible Markov chains converge to equilibrium exponentially fast via spectral gap bounds.
- **Key Theorem:** `spectral_stability_bound` (Exponential decay bound derived from the Sector Envelope).

### 2. Renormalization (Scale Invariance)
- **Module:** `SGC.Renormalization.Lumpability` 
- **Physics:** Proves that spectral stability is preserved under coarse-graining (renormalization group flow).
- **Key Theorem:** `gap_non_decrease` (The spectral gap of a lumped chain is bounded below by the original gap).

#### Verified Approximate Lumpability

We have replaced the `approximate_gap_leakage` axiom with a **verified theorem stack**. See [`src/SGC/Renormalization/Approximate.lean`](src/SGC/Renormalization/Approximate.lean).

| Component | Line | Description |
|-----------|------|-------------|
| `IsApproxLumpable` | 303 | Definition: ‖(I-Π)LΠ‖_op ≤ ε |
| `trajectory_closure_bound` | 855 | Theorem: Trajectories stay close (O(ε·t) error) |
| `spectral_stability` | 1245 | Theorem: Eigenvalue stability (**verified**) |

**The Physics:** When a partition is "almost" lumpable (defect operator small), the reduced model accurately tracks the full dynamics. The `spectral_stability` theorem proves this rigorously via:

```
IsApproxLumpable → trajectory_closure_bound → propagator_approximation_bound → spectral_stability
```

For NCD (Near-Completely Decomposable) systems, the error is **uniform in time**: O(ε/γ) instead of O(ε·t).

### 3. Thermodynamics (Stochastic Heat)
- **Module:** `SGC.Thermodynamics.DoobMeyer` 
- **Physics:** The stochastic thermodynamics of surprise. Decomposes self-information into predictable work and martingale heat.
- **Key Theorem:** `doob_decomposition` ($S_n = M_n + A_n$).

### 4. Variational Mechanics (The "Why")
- **Module:** `SGC.Variational.LeastAction` 
- **Physics:** Derives drift maximization from the Principle of Least Action.
- **Key Theorem:** `variational_drift_optimality` (Action minimization implies drift maximization).

---

## Bridges & Axioms

- **`SGC.Axioms.Geometry`**: Defines the explicit $L^2(\pi)$ metric space structures without heavy typeclass overhead.
- **`SGC.Topology.Blanket`**: Formalizes Markov Blankets via geometric orthogonality rather than information theory.
- **`SGC.Bridge.Discretization`**: Defines the **Axiomatic Interface** for the continuum limit. Proves that any discretization satisfying these axioms (Gap Consistency) inherits thermodynamic stability. This separates the thermodynamic logic from the geometric implementation.

---

## Extensions

### Information Geometry
- **Module:** `SGC.Information`
- **Physics:** Proves that geometric orthogonality is equivalent to conditional independence (vanishing Conditional Mutual Information) in the Gaussian limit.
- **Key Theorem:** `information_geometry_equivalence` — For reversible systems, `RespectsBlank` (geometric) ⟺ `IsInformationBlanketV` (information-theoretic).

### Continuum Limits
- **Module:** `SGC.Geometry.Manifold`
- **Physics:** Scaffolding for the Belkin-Niyogi convergence theorem (graph Laplacians → Laplace-Beltrami operators).
- **Goal:** Constructive validation of the `ContinuumTarget` axiom.

---

## Theorem Index

| Theorem | Module | Description |
|---------|--------|-------------|
| `FunctorialHeatDominanceTheorem` | `SGC.Spectral` | Spectral stability of non-reversible chains |
| `gap_non_decrease` | `SGC.Renormalization.Lumpability` | Spectral gap preservation under coarse-graining |
| `trajectory_closure_bound` | `SGC.Renormalization.Approximate` | Trajectory error O(ε·t) for approx-lumpable systems |
| `spectral_stability` | `SGC.Renormalization.Approximate` | Eigenvalue tracking (verified via Weyl) |
| `NCD_uniform_error_bound` | `SGC.Renormalization.Approximate` | Uniform-in-time O(ε/γ) bound for NCD systems |
| `doob_decomposition` | `SGC.Thermodynamics.DoobMeyer` | Stochastic thermodynamic decomposition of surprise |
| `emergence_is_necessary` | `SGC.Variational.LeastAction` | Variational derivation of drift maximization |
| `information_geometry_equivalence` | `SGC.Information.Equivalence` | Geometry ⟺ Information equivalence |

---

## Build & Verify

Prerequisites: `elan`, `lake`.

```bash
# Clone the repository
git clone https://github.com/JasonShroyer/sgc-lean.git
cd sgc-lean

# Build the library
lake build

# The library root is located at src/SGC.lean
```

---

## Verification Status

| Component | Status | Notes |
|-----------|--------|-------|
| SGC Core (v1) | ✅ Verified | Zero sorries |
| Information Bridge (v2) | ✅ Verified | Zero sorries |
| Approximate Lumpability | ✅ Verified | `spectral_stability` fully verified; supporting lemmas have axiomatic bridges |
| Full Build | ✅ Passing | — |

See [`VERIFIED_CORE_MANIFEST.md`](VERIFIED_CORE_MANIFEST.md) for the formal verification statement.
See [`ARCHITECTURE.md`](ARCHITECTURE.md) for design decisions and rationale.
See [`CHANGELOG.md`](CHANGELOG.md) for the project history.

---

## License

Apache 2.0
