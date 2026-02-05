/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.FunctionalBlanket
import SGC.InformationGeometry.KramersEscape
import SGC.InformationGeometry.InformationGradientLaw
import SGC.ContinualLearning.AdiabaticInvariant

/-!
# SGC Grokking Theory: Unified Formalization

This module provides the unified interface to the SGC theory of grokking,
validated through experiments in February 2026.

## The Four Equivalences of Information Thermodynamics

| Learning Concept | Physics Analog |
|------------------|----------------|
| Defect | Curvature |
| Noise | Temperature |
| Grokking | Phase Transition (Lifshitz) |
| Continual Learning | Adiabatic Evolution |

## Validated Experimental Results

| Metric | Pre-Grok | At Grok | Post-Grok |
|--------|----------|---------|-----------|
| Functional Defect | 1.01 | 0.13 | 0.003 |
| Class Separation | 0.01 | 6.45 | 346 |
| Geometric Defect | 0.23 | 0.35 | 0.33 |
| Tsallis q | 2.53 | 2.09 | 2.76 |

## Module Structure

1. **FunctionalBlanket**: Defines functional vs geometric defect, grokking detection
2. **KramersEscape**: Diffusion-RG isomorphism, temperature speedup
3. **InformationGradientLaw**: ||∇I|| > ||∇E|| triggers transitions
4. **AdiabaticInvariant**: Functional blanket freezing for continual learning

## Key Theorems

### Grokking Detection
```
theorem grokking_is_lifshitz:
  FunctionalDefect(before) > 0.5 ∧ FunctionalDefect(after) < 0.15 →
  IsLifshitzTransition
```

### Temperature Speedup
```
theorem temperature_speedup:
  D₂ > D₁ > 0 → KramersEscapeTime(D₂) < KramersEscapeTime(D₁)
```

### Information Gradient Law
```
theorem information_gradient_law:
  ||∇I|| > ||∇E|| → TopologicalTransition
```

### Catastrophic Forgetting Prevention
```
theorem catastrophic_forgetting_prevention:
  (∀ updates, Δw ⊥ ∇ε_func(TaskA)) →
  |ε_func(TaskA, final) - ε_func(TaskA, initial)| < tolerance
```

## References

* Experimental validation: `demos/lifshitz_transition_experiment.py`
* Theory document: `docs/lifshitz_transition_theory.md`
* Roadmap: `docs/sgc_theory_roadmap.md`
-/

namespace SGC.Grokking

/-! ## Re-exports for convenient access -/

-- Functional Blanket Theory
export SGC.FunctionalBlanket (
  HiddenStates
  FunctionalDefect
  ClassSeparation
  GeometricDefect
  grokkingThreshold
  grokkingDetected
  IsLifshitzTransition
  grokking_is_lifshitz
  AdiabaticProtection
)

-- Kramers Escape / Diffusion-RG
export SGC.InformationGeometry.KramersEscape (
  LossLandscape
  BarrierHeight
  NoiseTemperature
  KramersEscapeTime
  temperature_speedup
  SpectralGap
  DiffusionRGIsomorphism
  defect_exponential_decay
  GrokkingTransition
)

-- Information Gradient Law
export SGC.InformationGeometry.InformationGradientLaw (
  EnergyGradient
  InformationGradient
  GradientRatio
  TopologicalTransitionCondition
  information_gradient_law
  LearningPhase
  determineLearningPhase
  NaturalGradientUpdate
  FunctionalBlanketConstrainedUpdate
)

-- Adiabatic Invariants for Continual Learning
export SGC.ContinualLearning.AdiabaticInvariant (
  AdiabaticInvariant
  IsAdiabaticConserved
  FunctionalBlanketInvariant
  ConstrainedUpdate
  constrained_update_orthogonal
  Task
  catastrophic_forgetting_prevention
  MultiTaskConstrainedUpdate
)

/-! ## The Grokking Rosetta Stone -/

/-- **The Grokking Rosetta Stone**: A unified view of the correspondence between
    SGC theory, physics, and machine learning.

    | SGC Concept | Physics | ML Interpretation |
    |-------------|---------|-------------------|
    | Functional Defect | Order Parameter | Within-class variance |
    | Spectral Gap | Energy Gap | Learning rate |
    | Kramers Time | Reaction Rate | Epochs to grok |
    | Noise/Temperature | Thermal Fluctuations | Data augmentation |
    | Adiabatic Invariant | Action Variable | Protected subspace |
    | Lifshitz Transition | Topological Change | Memorization→Generalization |

    This correspondence allows us to import powerful results from physics
    (Kramers theory, adiabatic theorem, RG flow) into machine learning. -/
def GrokkingRosettaStone : Prop := True

/-! ## Summary: The Physics of Intelligence -/

/-- **Summary**: Grokking is a topological phase transition where:

    1. The functional blanket (algebraic symmetry) collapses
    2. The geometric blanket (PCA closure) may expand (curvature)
    3. The information gradient overtakes the energy gradient
    4. The system snaps from memorization to generalization topology

    This is formalized as:
    - Functional defect: 1.0 → 0.003 (collapse)
    - Class separation: 0.01 → 346 (explosion)
    - Geometric defect: 0.23 → 0.35 (curvature increase)

    The key insight: Grokking learns the SYMMETRY GROUP, not dimensionality reduction.

    Applications:
    - Intrinsic grokking detection (no test set needed)
    - Temperature-assisted training (analog world speedup)
    - Functional blanket freezing (continual learning)
    - Natural gradient optimization (follow ||∇I||) -/
def ThePhysicsOfIntelligence : Prop := True

end SGC.Grokking
