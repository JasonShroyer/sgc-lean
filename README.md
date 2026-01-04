# SGC: The Spectral Geometry of Consolidation

[![Build](https://github.com/JasonShroyer/sgc-lean/actions/workflows/build.yml/badge.svg)](https://github.com/JasonShroyer/sgc-lean/actions/workflows/build.yml)
[![Lean 4](https://img.shields.io/badge/Lean-4-blue.svg)](https://lean-lang.org/)
[![Verified Core](https://img.shields.io/badge/core-verified-brightgreen.svg)](VERIFIED_CORE_MANIFEST.md)

An experimental formalization of the algebraic structure of metastability in discrete stochastic systems. This library integrates spectral geometry, stochastic thermodynamics, and variational methods to derive bounds on the stability of partitions in finite-state Markov chains.

**Note:** This project was developed by a non-academic enthusiast (music background, self-taught programmer) using AI to explore formal verification. I treat Lean 4 as a "falsification engine" to test physical intuitions against rigorous logic, in an attempt to prevent self-delusion. I am essentially steering the AI to build the mathematical objects I intuit. Feedback on these definitions is very welcome.

**Scope:** The verified core establishes results for **finite state spaces** (`[Fintype V]`). This is a deliberate design choice—see [`ARCHITECTURE.md`](ARCHITECTURE.md) for rationale. Continuum limits are axiomatized via `SGC.Bridge.Discretization`, providing an explicit interface for future formalization of analytic convergence results.

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

#### Verified Approximate Lumpability (100% Complete)

We have replaced the `approximate_gap_leakage` axiom with a **fully verified theorem stack**. See [`src/SGC/Renormalization/Approximate.lean`](src/SGC/Renormalization/Approximate.lean).

| Component | Status | Description |
|-----------|--------|-------------|
| `IsApproxLumpable` | ✅ Definition | ‖(I-Π)LΠ‖_op ≤ ε |
| `trajectory_closure_bound` | ✅ Verified | Uniform trajectory error O(ε·t) |
| `propagator_approximation_bound` | ✅ Verified | Operator norm bound |
| `spectral_stability` | ✅ Verified | Eigenvalue tracking via Weyl |
| `NCD_uniform_error_bound` | ✅ Verified | Uniform-in-time O(ε/γ) for NCD |
| `pointwise_implies_opNorm_approx` | ✅ Verified | Legacy bridge (row-sum → op-norm) |

**The Physics:** When a partition is "almost" lumpable (defect operator small), the reduced model accurately tracks the full dynamics. The `spectral_stability` theorem proves this rigorously via:

```
IsApproxLumpable → trajectory_closure_bound → propagator_approximation_bound → spectral_stability
```

#### NCD Validity Horizon (A Physical Insight)

For NCD (Near-Completely Decomposable) systems, the formalization successfully distinguished between:

- **Vertical Stability** (✅ Verified): States rapidly collapse to the slow manifold with uniform-in-time error O(ε/γ).
- **Horizontal Drift** (🚫 Disproved): Phase along the slow manifold drifts as O(ε·t).

The proof assistant correctly rejected `NCD_spectral_stability` as false. Effective theories for NCD systems have a **validity horizon** of t ≪ 1/ε. Beyond this timescale, higher-order corrections are required.

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
| `spectral_stability_bound` | `SGC.Spectral.Defs` | Spectral stability of non-reversible chains |
| `gap_non_decrease` | `SGC.Renormalization.Lumpability` | Spectral gap preservation under coarse-graining |
| `trajectory_closure_bound` | `SGC.Renormalization.Approximate` | Trajectory error O(ε·t) for approx-lumpable systems |
| `spectral_stability` | `SGC.Renormalization.Approximate` | Eigenvalue tracking (verified via Weyl) |
| `NCD_uniform_error_bound` | `SGC.Renormalization.Approximate` | Uniform-in-time O(ε/γ) bound for NCD systems |
| `doob_decomposition` | `SGC.Thermodynamics.DoobMeyer` | Stochastic thermodynamic decomposition of surprise |
| `variational_drift_optimality` | `SGC.Variational.LeastAction` | Variational derivation of drift maximization |
| `information_geometry_equivalence` | `SGC.Information.Equivalence` | Geometry ⟺ Information equivalence |

---

## Getting Started

### System Requirements

- **Disk Space:** ~1 GB (includes Mathlib cache and build artifacts)
- **Network:** Requires downloading Mathlib dependencies (approx. 10 mins on standard connections)

### Prerequisites

This project uses [Lean 4](https://lean-lang.org/) with Mathlib. You'll need `elan` (the Lean version manager) installed.

**macOS / Linux:**
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

**Windows:**
Download the installer from [github.com/leanprover/elan](https://github.com/leanprover/elan/releases)

### Build Instructions

**Step 1: Clone the repository**
```bash
git clone https://github.com/JasonShroyer/sgc-lean.git
cd sgc-lean
```

**Step 2: Troubleshooting — Clean Artifacts**

If you encounter path conflicts or build errors, remove the local Lake cache:
```bash
rm -rf .lake
```

**Step 3: Build**
```bash
# Fetch pre-compiled Mathlib binaries (could save an hour or more of compilation time)
lake exe cache get

# Build the project
lake build
```

The library root is located at `src/SGC.lean`.

### Running Tests

To run the sanity checks and see output (axiom transparency, concrete examples):

```bash
lake env lean test/Main.lean
```

This uses the Lean interpreter and runs instantly with cached bytecode.

---

## Verification & Axioms

This library has a **two-tier architecture** that separates algebraic foundations from analytic assumptions:

| Tier | Modules | Verification Status |
|------|---------|---------------------|
| **Algebraic Core** | `Lumpability`, `DoobMeyer`, `LeastAction`, `Blanket` | ✅ Verified from first principles |
| **Effective Theory** | `Approximate.lean` | ✅ Verified *conditional* on standard analysis axioms |

### What This Means

The **algebraic core** (spectral gap monotonicity, Doob-Meyer decomposition, variational principles) is machine-checked with zero sorries—these proofs require only standard Lean/Mathlib axioms (`propext`, `Classical.choice`, `Quot.sound`).

The **effective theory** (`Approximate.lean`) proves trajectory bounds and spectral stability for approximately lumpable systems. These proofs are *conditional* on explicitly declared axioms for:

- **Duhamel's Principle** (`Horizontal_Duhamel_integral_bound`)
- **Weyl Inequality** (`Weyl_inequality_pi`)
- **Heat Kernel Bounds** (`HeatKernel_opNorm_bound`)

These are standard results in functional analysis. We axiomatize them to avoid a multi-month formalization detour while keeping the dependency explicit. Future contributors can discharge these axioms by proving them from Mathlib primitives.

**Run `lake env lean test/Main.lean` to see exactly which axioms each theorem depends on.**

---

## Build Status

| Component | Status | Notes |
|-----------|--------|-------|
| Full Build | ✅ Passing | Zero sorries in all modules |
| Approximate Lumpability | ✅ Complete | All core theorems verified (conditional on analysis axioms) |
| NCD Extension | ✅ Verified | `NCD_spectral_stability` correctly identified as **false** (secular growth) |

**Documentation:**
- [`VERIFIED_CORE_MANIFEST.md`](VERIFIED_CORE_MANIFEST.md) — Formal verification statement
- [`ARCHITECTURE.md`](ARCHITECTURE.md) — Design decisions and rationale for reviewers
- [`CONTRIBUTING.md`](CONTRIBUTING.md) — How to verify and extend the library
- [`CHANGELOG.md`](CHANGELOG.md) — Project history

---

## Future Roadmap

### Executable Semantics (SciLean Target)
While the verified core utilizes `Real` for analytic precision (marking definitions `noncomputable`), the algebraic structure over `Fintype` is inherently algorithmic.
* **Goal:** Instantiate the topological definitions with `Float` using [SciLean](https://github.com/lecopivo/SciLean).
* **Application:** This will allow the exact same theorem-checked code to compile into high-performance C simulators, effectively creating a "verified physics engine" for computing validity horizons.

### Browser-Based Verification (Planned)

Upcoming integration with [Gitpod](https://gitpod.io/) to allow one-click review and verification of proofs directly in the browser—no local installation required.

---

## Community & Feedback

I am looking for collaborators to help refute or refine these definitions.

* **Discussion:** Open a [GitHub Issue](https://github.com/JasonShroyer/sgc-lean/issues)
* **Contact:** Find me on the [Lean Zulip](https://leanprover.zulipchat.com/) as **Jason Shroyer**.

---

## License

Apache 2.0
