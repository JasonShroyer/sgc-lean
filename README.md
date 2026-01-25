# SGC: The Spectral Geometry of Consolidation

[![Build](https://github.com/JasonShroyer/sgc-lean/actions/workflows/build.yml/badge.svg)](https://github.com/JasonShroyer/sgc-lean/actions/workflows/build.yml)
[![Lean 4](https://img.shields.io/badge/Lean-4-blue.svg)](https://lean-lang.org/)
[![Verified Core](https://img.shields.io/badge/core-verified-brightgreen.svg)](VERIFIED_CORE_MANIFEST.md)

An experimental formalization of the algebraic structure of metastability in discrete stochastic systems. This library integrates spectral geometry, stochastic thermodynamics, and variational methods to derive bounds on the stability of partitions in finite-state Markov chains.

**Note:** This project was developed by a non-academic enthusiast (music background, self-taught programmer) using AI to explore formal verification. I treat Lean 4 as a "falsification engine" to test physical intuitions against rigorous logic, in an attempt to prevent self-delusion. I am essentially steering the AI to build the mathematical objects I intuit. Feedback on these definitions is very welcome.

**Scope:** The verified core establishes results for **finite state spaces** (`[Fintype V]`). This is a deliberate design choice—see [`ARCHITECTURE.md`](ARCHITECTURE.md) for rationale. Continuum limits are axiomatized via `SGC.Bridge.Discretization`, providing an explicit interface for future formalization of analytic convergence results.

**New in v2:** Approximate lumpability is now a *derived theorem*, not an axiom. We prove that small kinematic defects (leakage between blocks) lead to bounded trajectory errors. The core result `trajectory_closure_bound` establishes that **prediction is possible in a coarse-grained world**—the mathematical foundation for emergent agency.

**New in v3 (Audit Refinement):** Following rigorous mathematical review, we clarified the scope of spectral vs. dynamical results. The **trajectory bounds** (`trajectory_closure_bound`, `NCD_uniform_error_bound`) are valid for ALL generators, including non-reversible systems. Spectral eigenvalue matching (`spectral_stability_reversible`) requires reversibility. The trajectory-based results are the foundation for a physics of emergence.

---

## The Four Pillars of Formalization

The library is organized into four logical modules (`src/SGC/`):

### 1. Spectral Geometry (The Foundation)
- **Module:** `SGC.Spectral` 
- **Physics:** Establishes that non-reversible Markov chains converge to equilibrium exponentially fast via spectral gap bounds.
- **Key Theorem:** `spectral_stability_bound` (Exponential decay bound derived from the Sector Envelope).

### 2. Renormalization (Scale Invariance)
- **Module:** `SGC.Renormalization.Lumpability` 
- **Physics:** Proves that coarse-graining preserves predictive validity (trajectory closure).
- **Key Theorem:** `dirichlet_gap_non_decrease` (The Dirichlet form infimum is preserved under coarse-graining).

#### Verified Approximate Lumpability (100% Complete)

We have replaced the `approximate_gap_leakage` axiom with a **fully verified theorem stack**. See [`src/SGC/Renormalization/Approximate.lean`](src/SGC/Renormalization/Approximate.lean).

| Component | Status | Scope | Description |
|-----------|--------|-------|-------------|
| `IsApproxLumpable` | ✅ Definition | All L | ‖(I-Π)LΠ‖_op ≤ ε (leakage defect) |
| `trajectory_closure_bound` | ✅ Verified | **All L** | Trajectory error O(ε·t) — **THE CORE VICTORY** |
| `NCD_uniform_error_bound` | ✅ Verified | **All L** | Uniform-in-time O(ε/γ) for NCD systems |
| `propagator_approximation_bound` | ✅ Verified | All L | Operator norm bound on propagator difference |
| `spectral_stability_reversible` | ⚠️ Reversible | L = L* | Eigenvalue tracking via Weyl (requires self-adjoint L) |
| `dirichlet_gap_non_decrease` | ✅ Verified | All L | Algebraic (spectral interpretation requires reversibility) |

**The Physics of Emergence:** The trajectory-based results prove that **prediction is possible** using a coarse-grained model. This is the mathematical foundation for:
- **Effective Field Theory**: A reduced model validly predicts the future
- **Markov Blankets**: Minimizing leakage defect ε mechanically carves out predictive boundaries
- **Emergent Agency**: Systems that persist must minimize prediction error, hence minimize ε

The chain of inference for non-reversible systems:
```
IsApproxLumpable → trajectory_closure_bound → NCD_uniform_error_bound
                                           ↓
                              PREDICTIVE EMERGENCE (valid for all generators)
```

For reversible systems only:
```
trajectory_closure_bound → propagator_approximation_bound → spectral_stability_reversible
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
- **`SGC.Bridge.Discretization`**: Defines the **Gap Consistency** interface for the continuum limit. Proves that any discretization satisfying this interface inherits thermodynamic stability.
- **`SGC.Geometry.Manifold.Convergence`**: Contains the **Axiomatic Interface** (`manifold_hypothesis`, `spectral_convergence_axiom`) encoding the Belkin-Niyogi convergence theorem. This separates the thermodynamic logic from the geometric implementation.

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

### Topological Evolution (Phase 5 - NEW)
- **Module:** `SGC.Evolution`
- **Physics:** Ricci Flow with Surgery—structural emergence via bond breaking/forming.
- **Key Components:**

| Module | Purpose | Key Definition |
|--------|---------|----------------|
| `FormanRicci` | Stress signal | `FormanRicci G u v` — combinatorial edge curvature |
| `Surgery` | Operators | `SurgeryCut`, `SurgerySew` — topology-changing maps |
| `Conservation` | Constraints | `IsSafeSurgery`, `BettiNumber` — topological invariants |

**The Three-Layer Architecture:**
```
Signal:     FormanRicci(e) < 0  →  Edge under stress (bottleneck)
Action:     SurgeryCut(G, θ)   →  Remove stressed edges
Constraint: IsSafeSurgery      →  Preserve b₀=1, b₁≥1 (connectedness + blanket)
```

**Physical Applications:**
- **Origin of Life**: Chemical bond formation/breaking
- **Neural Networks**: Synaptic pruning/growth  
- **Emergent Identity**: Markov blanket (b₁ ≥ 1) as topological "self"

---

## Theorem Index

| Theorem | Module | Tier | Description |
|---------|--------|------|-------------|
| `spectral_stability_bound` | `SGC.Spectral.Defs` | **Core** | Spectral stability of non-reversible chains |
| `gap_non_decrease` | `SGC.Renormalization.Lumpability` | **Core** | Spectral gap preservation under coarse-graining |
| `trajectory_closure_bound` | `SGC.Renormalization.Approximate` | **Core** | Trajectory error O(ε·t) for approx-lumpable systems |
| `spectral_stability` | `SGC.Renormalization.Approximate` | **Core** | Eigenvalue tracking (verified via Weyl) |
| `NCD_uniform_error_bound` | `SGC.Renormalization.Approximate` | **Core** | Uniform-in-time O(ε/γ) bound for NCD systems |
| `doob_decomposition` | `SGC.Thermodynamics.DoobMeyer` | **Core** | Stochastic thermodynamic decomposition of surprise |
| `variational_drift_optimality` | `SGC.Variational.LeastAction` | **Core** | Variational derivation of drift maximization |
| `blanket_orthogonality` | `SGC.Topology.Blanket` | **Core** | Internal-external orthogonality for Markov blankets |
| `information_geometry_equivalence` | `SGC.Information.Equivalence` | **Extension** | Geometry ⟺ Information equivalence |
| `forman_ricci_symm` | `SGC.Evolution.FormanRicci` | **Evolution** | F(u,v) = F(v,u) — curvature symmetry |
| `forman_ricci_bottleneck` | `SGC.Evolution.FormanRicci` | **Evolution** | High-degree endpoints → negative curvature |
| `safe_surgery_preserves_blanket` | `SGC.Evolution.Conservation` | **Evolution** | Safe surgery maintains b₁ ≥ 1 |
| `self_preservation` | `SGC.Evolution.Conservation` | **Evolution** | Constrained surgery preserves Markov blanket |

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

### Reading Guide

**For Physicists/Mathematicians:**
1. Start with this README for the high-level architecture
2. Read [VERIFIED_CORE_MANIFEST.md](VERIFIED_CORE_MANIFEST.md) for verification status
3. Inspect [`src/SGC/Renormalization/Lumpability.lean`](src/SGC/Renormalization/Lumpability.lean) for the `gap_non_decrease` proof
4. See [`test/Main.lean`](test/Main.lean) for concrete examples and axiom audits

**For Lean Developers:**
1. Read [ARCHITECTURE.md](ARCHITECTURE.md) for design rationale (why explicit weights, why finite state spaces)
2. Read [CONTRIBUTING.md](CONTRIBUTING.md) for build instructions and safeguards
3. Run `lake build` and `lake env lean test/Main.lean` to verify
4. Inspect `#print axioms` output to understand dependency chains

**For Peer Reviewers:**
1. Start with [VERIFIED_CORE_MANIFEST.md](VERIFIED_CORE_MANIFEST.md) for the verification statement
2. Check [`src/SGC/Renormalization/Approximate.lean`](src/SGC/Renormalization/Approximate.lean) for the axiomatized effective theory
3. Review axiom docstrings (search for `axiom` keyword) to understand modeling assumptions
4. Verify CI build status and `Verify no sorries` step in [`.github/workflows/build.yml`](.github/workflows/build.yml)

---

## Verification Status (v0.6.0)

**Build Status: ✅ Zero Sorries** — All modules compile without `sorry` placeholders.

### Two-Tier Architecture

| Tier | Description | Verification Level |
|------|-------------|-------------------|
| **Verified Core** | Algebraic theorems proved from Mathlib primitives | ✅ Machine-checked proofs |
| **Axiomatized Effective Theory** | Physical axioms with explicit assumptions | ✅ Conditional on declared axioms |

### Verified Core (No Additional Axioms)

These theorems are proved from first principles using only standard Lean/Mathlib axioms:

| Module | Key Theorem | Status |
|--------|-------------|--------|
| `Renormalization.Lumpability` | `dirichlet_gap_non_decrease` | ✅ Verified |
| `Renormalization.Approximate` | `trajectory_closure_bound` | ✅ Verified |
| `Thermodynamics.DoobMeyer` | `doob_decomposition` | ✅ Verified |
| `Variational.LeastAction` | `variational_drift_optimality` | ✅ Verified |
| `Topology.Blanket` | `blanket_orthogonality` | ✅ Verified |
| `Geometry.CurvatureBridge` | `assembly_index_zero_iff_constant` | ✅ Verified |
| `Geometry.Yamabe` | `YamabeFlowStep.radius_pos` (CFL) | ✅ Verified |

### Axiomatized Effective Theory

These modules use explicitly declared axioms for standard mathematical results:

| Category | Axioms | Purpose |
|----------|--------|---------|
| **Functional Analysis** | `Duhamel_integral_bound`, `Weyl_inequality_pi`, `HeatKernel_opNorm_bound` | Spectral perturbation theory |
| **Stochastic Processes** | `diffusionStep_nonneg`, `diffusionStep_sum` | Markov semigroup properties |
| **Thermodynamics** | `stationary_strictly_positive`, `hidden_entropy_bounded_by_defect` | Perron-Frobenius, entropy bounds |
| **Geometry** | `YamabeFlow`, `eulerCharacteristic` | Discrete flow dynamics |

These axioms represent standard results in analysis that we chose not to formalize from scratch. Each axiom is documented with its mathematical justification. Future contributors can discharge these by proving them from Mathlib primitives.

### Axiom Audit

**Run `lake env lean test/Main.lean`** to see exactly which axioms each theorem depends on.

The only "non-standard" axioms are those explicitly declared in our codebase—all others (`propext`, `Classical.choice`, `Quot.sound`) are standard Lean/Mathlib foundations.

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

### Current Scope: Metric Consolidation (Level 1)

**What we have formalized (Phase 1-4):**
- **Fixed Topology**: The graph structure (which states connect to which) is static
- **Yamabe Flow**: Curvature smoothing via gradient descent on conformal factors
- **Assembly Index**: Measures deviation from uniform predictability
- **Ollivier-Ricci Curvature**: Grounds geometric curvature in transition probabilities

This corresponds to **learning/annealing** on a fixed architecture—optimizing edge weights without changing which edges exist.

### Future Scope: Topological Evolution (Level 2)

**The next frontier (Phase 5+):**

| Concept | Tool | Application |
|---------|------|-------------|
| **Forman-Ricci Curvature** | Combinatorial edge curvature | Identifies "stress points" (likely to break/form) |
| **Ricci Flow with Surgery** | Topology-changing operator | Models bond breaking/forming |
| **Discrete Morse Theory** | Persistent homology (Betti numbers) | Tracks topological invariants through surgery |

**Why This Matters:**
- **Origin of Life**: Chemical bond formation/breaking
- **Neural Architecture Search**: Synaptic pruning/growth
- **Social Network Evolution**: Relationship formation/dissolution
- **Emergent Identity**: Creation of stable Markov blankets (Betti₁ = "self")

**Reserved Interfaces:**
```
TopologicalSurgery : Graph → Graph  -- Discontinuous topology change
FormanRicci : Edge → ℝ              -- Combinatorial stress indicator
BettiNumber : Graph → ℕ → ℕ         -- Topological invariant tracker
```

The current Yamabe flow framework provides the foundation: surgery occurs when weights vanish (w_{ij} → 0) or curvature diverges (κ → -∞).

### Executable Semantics (SciLean Target)
While the verified core utilizes `Real` for analytic precision (marking definitions `noncomputable`), the algebraic structure over `Fintype` is inherently algorithmic.
* **Goal:** Instantiate the topological definitions with `Float` using [SciLean](https://github.com/lecopivo/SciLean).
* **Application:** This will allow the exact same theorem-checked code to compile into high-performance C simulators, effectively creating a "verified physics engine" for computing validity horizons.

### Browser-Based Verification (Planned)

Upcoming integration with [Gitpod](https://gitpod.io/) to allow one-click review and verification of proofs directly in the browser—no local installation required.

---

## Architecture Note

This library provides the **mathematical foundation**—spectral theory, thermodynamics, and geometry—as a formally verified standard. Runtime implementations, measurement harnesses, and experimental control modules are maintained in a separate repository to ensure this library remains a focused, academically accessible artifact.

If you are interested in applying these formalizations to executable simulations or control systems, please reach out via the channels below.

---

## Community & Feedback

I am looking for collaborators to help refute or refine these definitions.

* **Discussion:** Open a [GitHub Issue](https://github.com/JasonShroyer/sgc-lean/issues)
* **Contact:** Find me on the [Lean Zulip](https://leanprover.zulipchat.com/) as **Jason Shroyer**.

---

## License

Apache 2.0
