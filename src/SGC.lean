/-
Copyright (c) 2025 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/

-- Foundation: The L²(π) Inner Product Structure
import SGC.Axioms.Geometry

-- Spectral Pillar: Heat Kernel, Sector Envelope, and Core Stability Theorem
import SGC.Spectral.Envelope
import SGC.Spectral.Defs

-- Renormalization Pillar: Spectral Gap Monotonicity
import SGC.Renormalization.Lumpability

-- Approximate Renormalization: Trajectory bounds for leakage defects
import SGC.Renormalization.Approximate

-- Topology Pillar: Geometric Markov Blankets
import SGC.Topology.Blanket

-- Thermodynamics Pillar: Stochastic Thermodynamics of Surprise
import SGC.Thermodynamics.DoobMeyer
import SGC.Thermodynamics.EntropyProduction

-- Variational Pillar: Principle of Least Action
import SGC.Variational.LeastAction

-- Bridge Pillar: Continuum Limits
import SGC.Bridge.Discretization

-- ═══════════════════════════════════════════════════════════════════════════
-- SGC Extensions: The Constructive Physics Layer
-- ═══════════════════════════════════════════════════════════════════════════

-- Information Bridge: Shannon Entropy ↔ Geometric Orthogonality
import SGC.Information.Gaussian
import SGC.Information.Equivalence

-- Continuum Bridge: Graphs → Manifolds
import SGC.Geometry.Manifold.Laplacian
import SGC.Geometry.Manifold.Convergence

-- Discrete Curvature: Yamabe Flow and Consolidation
import SGC.Geometry.DiscreteCurvature
import SGC.Geometry.CurvatureBridge

/-!
# SGC: The Spectral Geometry of Consolidation

This is the entry point for the formally verified SGC library.

## The Four Pillars Architecture (v1 Core)

1. **Axioms** - The L²(π) geometric foundation (inspired by Chentsov/Fisher-Rao theory;
   implemented here as **discrete** weighted inner products on `Fintype V`)
2. **Spectral** - Spectral geometry and heat kernel bounds
3. **Renormalization** - Spectral gap preservation under coarse-graining
4. **Topology** - Markov blankets as geometric boundaries
5. **Thermodynamics** - Stochastic thermodynamics of surprise (Doob-Meyer)
6. **Variational** - Least Action principle for emergence
7. **Bridge** - Discrete-to-continuum convergence

## The Constructive Physics Layer (v2 Extensions)

7. **Information** - Shannon entropy ↔ geometric orthogonality equivalence
8. **Geometry.Manifold** - Laplace-Beltrami operator and Belkin-Niyogi convergence

## Verification Status

- **v1 Core**: Formally verified (zero unproven goals)
- **v2 Extensions**: Under construction (axiomatized pending Mathlib integration)

## Scope & Roadmap

### Current Scope: Metric Consolidation (Level 1 - Fixed Topology)

This library formalizes **annealing/learning** on a fixed graph structure:
- Edge weights evolve, but which edges exist is static
- Yamabe flow smooths curvature via conformal factor adjustment
- Ollivier-Ricci curvature grounds geometry in transition probabilities

### Future Scope: Topological Evolution (Level 2 - Reserved)

The next phase will formalize **structural emergence** (bond breaking/forming):
- **Forman-Ricci Curvature**: Combinatorial stress indicator for edges
- **Ricci Flow with Surgery**: Topology-changing operator (w_{ij} → 0 triggers edge removal)
- **Discrete Morse Theory**: Persistent homology to track topological invariants

Reserved type signatures for Phase 5+:
```
TopologicalSurgery : Graph → Graph
FormanRicci : Edge → ℝ
BettiNumber : Graph → ℕ → ℕ
```

-/
