# UPAT: Unified Predictive Assembly Theory

[![Lean 4](https://img.shields.io/badge/Lean-4-blue.svg)](https://lean-lang.org/)
[![Zero Sorries](https://img.shields.io/badge/sorries-0-brightgreen.svg)](VERIFIED_CORE_MANIFEST.md)
[![Release](https://img.shields.io/badge/release-v1.0--verified-orange.svg)](https://github.com/JasonShroyer/fhdt-lean4/releases/tag/release-1.0)

A **formally verified** Lean 4 formalization of the Unified Predictive Assembly Theory—a first-principles mathematical theory of emergence, persistence, and complexity.

> *"This is not a model. It is a theorem: emergence is physically necessary."*

---

## Overview

This repository contains a `sorry-free` Lean 4 proof of the **Schuller Tower**—the complete axiomatic foundation for understanding why complex, persistent systems (from cells to minds) must emerge under thermodynamic constraints.

### The Deductive Chain

| Pillar | Question | Module | Key Theorem |
|--------|----------|--------|-------------|
| **Stability** | *What exists?* | `Lumpability.lean` | `gap_non_decrease` |
| **Topology** | *Where are boundaries?* | `Blanket.lean` | `IsLinearBlanket` |
| **Vitality** | *How does complexity grow?* | `DoobMeyer.lean` | `doob_decomposition` |
| **Kinetics** | *Why must it grow?* | `LeastAction.lean` | `least_action_maximum_complexity` |
| **Bridge** | *Is it physically valid?* | `Discretization.lean` | `GapConsistent` |

---

## Quick Start

```bash
# Prerequisites: elan and lake installed
git clone https://github.com/JasonShroyer/fhdt-lean4.git
cd fhdt-lean4
git checkout upat-full   # or release-1.0 for frozen verified version
lake build
```

---

## Architecture

```
src/
├── UPAT/                           # Unified Predictive Assembly Theory
│   ├── Axioms/
│   │   └── Geometry.lean           # L²(π) inner product foundation
│   ├── Stability/
│   │   └── Functoriality/
│   │       └── Lumpability.lean    # Spectral gap monotonicity (Kinematics)
│   ├── Topology/
│   │   └── Blanket.lean            # Markov blankets via L² orthogonality
│   ├── Vitality/
│   │   ├── DoobMeyer.lean          # Doob decomposition S = M + A
│   │   └── LeastAction.lean        # Principle of Least Action for Complexity
│   └── Bridge/
│       └── Discretization.lean     # ε-graph → continuum convergence
│
└── FHDT/                           # Functorial Heat Dominance Theorem (legacy)
    ├── Core/
    │   ├── Assumptions.lean        # L²(π) geometry, Pillar 1
    │   └── Projector.lean          # Operator norms, projectors
    ├── Envelope/
    │   ├── Envelope.lean           # Heat kernel specification
    │   └── Sector.lean             # Contractive envelope (Pillar 2)
    ├── Diagonal.lean               # Diagonal bounds (Pillar 3)
    └── Defs.lean                   # Final FHDT assembly
```

---

## Core Theorems

### UPAT (Emergence Theory)

| Theorem | Statement | File |
|---------|-----------|------|
| `gap_non_decrease` | Spectral gap is preserved under coarse-graining | `Lumpability.lean` |
| `doob_decomposition` | $\Phi(y) - \Phi(x) = \Delta A + \Delta M$ | `DoobMeyer.lean` |
| `least_action_maximum_complexity` | Optimal transitions maximize complexity growth | `LeastAction.lean` |
| `emergence_is_necessary` | Under thermodynamic constraints, consolidation is maximal | `LeastAction.lean` |
| `bridge_to_stability` | Discrete gap bounds → continuous gap bounds | `Discretization.lean` |

### FHDT (Stability Analysis)

| Theorem | Statement | File |
|---------|-----------|------|
| `FunctorialHeatDominanceTheorem` | $\|\beta(t)\| \le C e^{-\lambda_{\text{gap}} t}$ | `Defs.lean` |
| `gap_pos_iff_ker_eq_span_one` | Spectral gap ↔ trivial kernel | `Assumptions.lean` |
| `sector_envelope_bound_canonical` | $\|K(t) \circ P\|_\pi \le e^{-\lambda_{\text{gap}} t}$ | `Sector.lean` |

---

## Theoretical Foundation

UPAT is derived from two axioms:

1. **Thermodynamic Persistence** (Free Energy Principle): Systems persist by minimizing surprise
2. **Geometric Invariance** (Chentsov's Theorem): The Fisher-Rao metric is the unique invariant geometry

From these axioms, the theory proves:
- **Markov blankets** emerge as geometric necessities (L² orthogonality)
- **Complexity** accumulates via the Doob-Meyer decomposition
- **Emergence** follows from a variational principle (Least Action)

---

## Verification Status

| Component | Status | Sorries |
|-----------|--------|---------|
| UPAT Core | ✅ Verified | 0 |
| FHDT Core | ✅ Verified | 0 |
| Full Build | ✅ Passing | 0 |

See [`VERIFIED_CORE_MANIFEST.md`](VERIFIED_CORE_MANIFEST.md) for the formal verification statement.

---

## Tags & Releases

- `v1.0-verified` — First fully verified release
- `release-1.0` — Annotated release with documentation

---

## References

- Chentsov, N. N. — Statistical Decision Rules and Optimal Inference
- Kemeny, J. G. & Snell, J. L. — Finite Markov Chains
- Friston, K. — The Free Energy Principle
- Schuller, F. — Lectures on the Geometric Anatomy of Theoretical Physics
- Doob, J. L. — Stochastic Processes

---

## License

Apache 2.0 — See [LICENSE](LICENSE) for details.

---

*Repository: https://github.com/JasonShroyer/fhdt-lean4*  
*Verified: December 21, 2024*
