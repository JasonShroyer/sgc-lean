# SGC-Lean Architecture

## Core Design Philosophy

SGC-Lean is built on three architectural pillars:
1.  **Observational Physics**: Definitions are based on observable quantities (trajectories, correlations), not hidden variables.
2.  **Constructive Renormalization**: Coarse-graining is treated as a constructive projection operator, not just a descriptive map.
3.  **Algebraic Universality**: Core theorems are proven over `RCLike` fields to support both Classical (Real) and Quantum (Complex) systems.

## Module Structure

### 1. `SGC.Axioms` (Foundations)
This layer defines the geometric arena for emergence.

*   **`Geometry.lean`**: (Classical Optimized)
    *   Defines `inner_pi`, `norm_sq_pi` specifically for `V → ℝ`.
    *   Optimized for probability distributions and stochastic matrices.
    *   Used by `SGC.Renormalization` for classical bounds.
*   **`GeometryGeneral.lean`**: (Quantum Capable)
    *   Defines geometry over `{𝕜 : Type*} [RCLike 𝕜]`.
    *   Inner product is **conjugate-linear**: $\langle u, v \rangle = \sum \pi(x) \overline{u(x)} v(x)$.
    *   Supports Hermitian operators and complex amplitudes.
    *   Used by `SGC.Bridge.Quantum`.

### 2. `SGC.Spectral` (Timescales)
Theorems relating the spectrum of the generator $L$ to the stability of the system.

*   **`Core/Assumptions.lean`**: Defines `SpectralGap` and `RelaxationTime`.
    *   Now generalized to Hermitian operators (supports real symmetric matrices as a special case).
*   **`Bounds.lean`**: Proves $t_{relax} \le \frac{1}{\gamma}$.

### 3. `SGC.Renormalization` (The Engine)
The core logic of the library. It acts as a "compiler" that takes a micro-theory and a partition, and outputs a macro-theory with error bounds.

*   **`Approximate.lean`**: Defines `IsApproxLumpable`.
    *   Key Metric: `DefectOperator L P` (The commutator $[L, \Pi]$).
    *   Key Theorem: `trajectory_closure_bound` (Error grows as $O(\epsilon \cdot t)$).

### 4. `SGC.Bridge` (Applications)
Experimental modules connecting SGC to other domains.

*   **`Quantum.lean`**: **The Classical-Quantum Isomorphism**.
    *   Maps Classical Lumpability $\leftrightarrow$ Knill-Laflamme Conditions.
    *   Proves that "Leakage" in classical systems is isomorphic to "Uncorrectable Error" in quantum codes.
    *   Provides `quantum_validity_horizon_bound` for topological codes.

## Implementation Details

### The "Explicit Weight" Pattern
SGC does **not** use Mathlib's `MeasureSpace` typeclass for its core probability distributions. Instead, it passes `(pi_dist : V → ℝ)` explicitly.
*   **Why?** Renormalization involves *changing* the measure ($\pi \to \bar{\pi}$). Typeclasses are static; explicit arguments allow dynamic measure transformation.

### ID Resolution
*   States are functions `V → 𝕜`.
*   Matrices are `Matrix V V 𝕜`.
*   Partitions are `Partition V` (a computable structure mapping micro-states to blocks).

## Future Roadmap

1.  **Variational Optimization**: Use the `DefectOperator` gradient to automatically discover optimal partitions.
2.  **Causal Emergence**: Link `IsApproxLumpable` to Effective Information (Hoel et al.).
3.  **Topological Protection**: Formalize the stability of Toric Code ground states using `SGC.Renormalization`.
