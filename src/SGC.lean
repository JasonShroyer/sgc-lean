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

-- ═══════════════════════════════════════════════════════════════════════════
-- Phase 5: Topological Evolution (Level 2)
-- ═══════════════════════════════════════════════════════════════════════════

-- Evolution: Ricci Flow with Surgery
import SGC.Evolution.FormanRicci
import SGC.Evolution.Surgery
import SGC.Evolution.Conservation

-- ═══════════════════════════════════════════════════════════════════════════
-- Phase 6: Thermodynamics of Evolution (The Cost of Change)
-- ═══════════════════════════════════════════════════════════════════════════

-- Landauer's Principle: Surgery has thermodynamic cost
import SGC.Thermodynamics.Evolution

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

### Level 1: Metric Consolidation (Phases 1-4) ✓

Formalizes **annealing/learning** on a fixed graph structure:
- Edge weights evolve, but which edges exist is static
- Yamabe flow smooths curvature via conformal factor adjustment
- Ollivier-Ricci curvature grounds geometry in transition probabilities

### Level 2: Topological Evolution (Phase 5) ✓

Formalizes **structural emergence** (bond breaking/forming):
- **Forman-Ricci Curvature** (`Evolution.FormanRicci`): Combinatorial stress indicator
- **Surgery Operators** (`Evolution.Surgery`): Cut (remove stressed edges) and Sew (add stabilizing edges)
- **Topological Conservation** (`Evolution.Conservation`): Betti numbers, safe surgery, Markov blanket preservation

Key definitions:
```
FormanRicci : WeightedGraph → V → V → ℝ     -- Edge stress signal
SurgeryCut : WeightedGraph → ℝ → WeightedGraph  -- Remove stressed edges
BettiNumber : WeightedGraph → ℕ → ℕ         -- Topological invariants
IsSafeSurgery : WeightedGraph → WeightedGraph → Prop  -- Preserves b₀=1, b₁≥1
```

-/
