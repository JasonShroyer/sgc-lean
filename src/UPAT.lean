/-
Copyright (c) 2024 UPAT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: UPAT Formalization Team
-/

-- Foundation: The L²(π) Inner Product Structure
import UPAT.Axioms.Geometry

-- Stability Pillar: Spectral Gap Monotonicity
import UPAT.Stability.Functoriality.Lumpability

-- Topology Pillar: Geometric Markov Blankets
import UPAT.Topology.Blanket

-- Vitality Pillar: Arrow of Complexity
import UPAT.Vitality.DoobMeyer

-- Kinetics Pillar: Principle of Least Action
import UPAT.Kinetics.LeastAction

-- Bridge Pillar: Continuum Limits
import UPAT.Bridge.Discretization

/-!
# Universal Predictive Assembly Theory (UPAT)

This is the entry point for the formally verified UPAT library.

## The Four Pillars Architecture

1. **Axioms** - The L²(π) geometric foundation (Chentsov + Fisher-Rao)
2. **Stability** - Spectral gap preservation under coarse-graining
3. **Topology** - Markov blankets as geometric boundaries
4. **Vitality** - Doob-Meyer decomposition of complexity
5. **Kinetics** - Least Action principle for emergence
6. **Bridge** - Discrete-to-continuum convergence

## Verification Status

All modules are formally verified with **zero `sorry` placeholders**.

-/
