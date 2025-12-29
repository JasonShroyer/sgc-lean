/-
Copyright (c) 2024 UPAT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: UPAT Formalization Team
-/

-- Foundation: The L²(π) Inner Product Structure
import UPAT.Axioms.Geometry

-- Spectral Pillar: Spectral Gap Monotonicity
import UPAT.Renormalization.Lumpability

-- Topology Pillar: Geometric Markov Blankets
import UPAT.Topology.Blanket

-- Thermodynamics Pillar: Stochastic Thermodynamics of Surprise
import UPAT.Thermodynamics.DoobMeyer

-- Variational Pillar: Principle of Least Action
import UPAT.Variational.LeastAction

-- Bridge Pillar: Continuum Limits
import UPAT.Bridge.Discretization

-- ═══════════════════════════════════════════════════════════════════════════
-- UPAT v2 Extensions: The Constructive Physics Layer
-- ═══════════════════════════════════════════════════════════════════════════

-- Information Bridge: Shannon Entropy ↔ Geometric Orthogonality
import UPAT.Information.Gaussian
import UPAT.Information.Equivalence

-- Continuum Bridge: Graphs → Manifolds
import UPAT.Geometry.Manifold.Laplacian
import UPAT.Geometry.Manifold.Convergence

/-!
# Universal Predictive Assembly Theory (UPAT)

This is the entry point for the formally verified UPAT library.

## The Four Pillars Architecture (v1 Core)

1. **Axioms** - The L²(π) geometric foundation (Chentsov + Fisher-Rao)
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

- **v1 Core**: Formally verified with zero `sorry` placeholders
- **v2 Extensions**: Under construction (contains `sorry` for advanced theorems)

-/
