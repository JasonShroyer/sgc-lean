# SGC-Lean: The Spectral Geometry of Consolidation

**Formal Verification of Emergence in Lean 4**

[![License](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Build Status](https://github.com/JasonShroyer/sgc-lean/actions/workflows/build.yml/badge.svg)](https://github.com/JasonShroyer/sgc-lean/actions)

SGC-Lean is a formal library for the **Physics of Emergence**. It provides a rigorous mathematical framework for "Approximate Lumpability"—the conditions under which a complex micro-system can be validly described by a simpler macro-theory.

> **🎯 New to this project?** Start with [docs/RESEARCH_NARRATIVE.md](docs/RESEARCH_NARRATIVE.md) for a guided tour.

## 🔥 Recent Breakthrough (February 2026)

**Grokking = Topological Lifshitz Transition** — We experimentally validated that neural network grokking is a topological phase transition where the *functional blanket* (algebraic symmetry) collapses while the *geometric blanket* (PCA closure) increases.

| Metric | Pre-Grok | At Grok | Post-Grok |
|--------|----------|---------|----------|
| **Functional Defect** | 1.01 | 0.13 | **0.003** |
| **Class Separation** | 0.01 | 6.45 | **346** |
| **Geometric Defect** | 0.23 | 0.35 | 0.33 |

Key insight: Grokking learns the **symmetry group**, not dimensionality reduction. See [docs/functional_blanket_breakthrough.md](docs/functional_blanket_breakthrough.md).

## 🌌 Quantum Error Correction Bridge

We have established a **formal correspondence** between classical Markov chain lumpability and quantum error correction.

### Main Result: No Coherent Backaction Theorem

**Theorem** (`knill_laflamme_forces_zero_defect`): *For a classical stochastic generator L with conservation (row sums zero), if the complexified defect operator E = (I−Π)LΠ satisfies the Knill-Laflamme condition Π E†E Π = α·Π for some real α, then E = 0.*

**Physical interpretation**: A classical Markov chain cannot exhibit the "coherent backaction" structure required by quantum error-correcting codes. The conservation law (probability preservation) forces α = 0 via the all-ones vector, which then implies E = 0 by positive definiteness.

### Proof Chain (Fully Verified)
1. `all_ones_in_code`: The constant function 𝟙 lies in the code subspace
2. `defect_kills_all_ones`: Conservation implies E(𝟙) = 0  
3. `partition_forces_alpha_zero`: Combined with KL condition, this forces α = 0
4. `operator_zero_iff_norm_sq_zero`: Positive definiteness gives E = 0

### Correspondence Table
| Classical (Markov) | Quantum |
|---|---|
| Partition of state space | Projection onto code subspace |
| Exact lumpability | Knill-Laflamme conditions (ε = 0) |
| Approximate lumpability | Approximate QEC |

**Demo**: See [`examples/ToricCode_Stability.lean`](examples/ToricCode_Stability.lean) for an application to topological code stability bounds.

## 🔭 Core Capabilities

### 1. The Leakage Defect ($\epsilon$)
We formally define the "error" of a macro-theory as the commutator norm between the dynamics $L$ and the coarse-graining projection $\Pi$:
$$ \epsilon = || [L, \Pi] || $$
This metric quantifies how much information "leaks" from the macro-variables back into the micro-details.

### 2. The Validity Horizon ($T^*$)
We prove that any coarse-grained model with defect $\epsilon$ is valid for a specific time window:
$$ T^* \ge \frac{\delta}{\epsilon} $$
After this time, the macro-description is mathematically guaranteed to drift from reality.

### 3. Renormalization Bounds
We provide formal bounds on the error accumulation of "Effective Theories" derived via spectral clustering.

### 4. Grokking Formalization (NEW)
We formalize the physics of grokking:
- **Functional Blanket**: Algebraic equivalence classes learned by the model
- **Kramers Escape**: Temperature-assisted barrier crossing (2x speedup validated)
- **Information Gradient Law**: Transitions occur when ||∇I|| > ||∇E||
- **Adiabatic Invariants**: Functional blanket freezing for continual learning

## 🛠 Installation

1.  **Install Lean 4**: Follow the [official instructions](https://leanprover.github.io/lean4/doc/setup.html).
2.  **Clone the Repo**:
    ```bash
    git clone https://github.com/JasonShroyer/sgc-lean.git
    cd sgc-lean
    lake build
    ```

## 📚 Project Structure

*   `SGC/Axioms`: Foundational geometric structures (Weighted L² spaces).
*   `SGC/Spectral`: Theorems on spectral gaps and timescales.
*   `SGC/Renormalization`: The core "Renormalization Group" flow for Markov chains.
*   `SGC/Bridge`: Connectors to Quantum Information (`SGC.Bridge.Quantum`).
*   `SGC/FunctionalBlanket`: **(NEW)** Functional defect and grokking detection.
*   `SGC/Grokking`: **(NEW)** Unified grokking formalization.
*   `SGC/ContinualLearning`: **(NEW)** Adiabatic invariants for continual learning.

### Documentation

*   `docs/RESEARCH_NARRATIVE.md`: **Start here** - Guided tour of the project
*   `docs/INDEX.md`: Documentation index
*   `docs/functional_blanket_breakthrough.md`: Key discovery documentation
*   `docs/lifshitz_transition_theory.md`: Complete theoretical synthesis

### Experiments

*   `demos/lifshitz_transition_experiment.py`: Validates Lifshitz transition
*   `demos/functional_grokking_detector.py`: Intrinsic grokking detection
*   `reports/`: Phase reports and analysis

## 🤝 Contributing

We welcome contributions from physicists, mathematicians, and formal verification experts.
*   **Classical Emergence**: Help us prove the "Manifold Hypothesis" for specific datasets.
*   **Quantum Information**: Help us extend the Knill-Laflamme bridge to "Approximate Quantum Error Correction" (AQEC).
*   **Grokking Theory**: Help us remove `sorry` placeholders from the grokking formalization.
*   **Continual Learning**: Help validate functional blanket freezing experiments.

See [CONTRIBUTING.md](CONTRIBUTING.md) for workflow details.

## 📜 License

Apache 2.0. See [LICENSE](LICENSE) for details.
