# UPAT: Universal Predictive Assembly Theory

[![Lean 4](https://img.shields.io/badge/Lean-4-blue.svg)](https://lean-lang.org/)
[![Zero Sorries](https://img.shields.io/badge/sorries-0-brightgreen.svg)](VERIFIED_CORE_MANIFEST.md)
[![Release](https://img.shields.io/badge/release-v1.0--verified-orange.svg)](https://github.com/JasonShroyer/fhdt-lean4/releases/tag/release-1.0)

This repository contains the `sorry-free` Lean 4 formalization of **Universal Predictive Assembly Theory (UPAT)**. 

UPAT extends the spectral stability of Markov chains (FHDT) into a general theory of emergence, formalizing how complexity accumulates in thermodynamic systems via the **Four Pillars** architecture.

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
| UPAT Core | ✅ Verified | 0 |
| FHDT Core | ✅ Verified | 0 |
| Full Build | ✅ Passing | 0 |

See [`VERIFIED_CORE_MANIFEST.md`](VERIFIED_CORE_MANIFEST.md) for the formal verification statement.

---

## License

Apache 2.0
