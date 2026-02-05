# SGC Research Narrative: From Theory to Validated Breakthroughs

**Last Updated**: February 5, 2026  
**Status**: Multiple Key Discoveries Validated

---

## How to Read This Repository

This document provides a **guided tour** through the SGC research program. If you're new, start here.

### The Three Pillars

1. **Lean Formalization** (`src/SGC/`) - Mathematically verified theorems
2. **Theory Documents** (`docs/`) - Physical interpretation and predictions
3. **Experiments** (`demos/`) - Empirical validation

### The Narrative Arc

```
SGC Core Theory → Quantum Bridge → Grokking Experiments → BREAKTHROUGH: Functional Blanket
     ↓                  ↓                   ↓                        ↓
 Lumpability    Classical=Quantum    Phase Transitions    Lifshitz Transition
   Defect       Correspondence         Observed              VALIDATED
```

---

## Part I: Foundations (Pre-2026)

### What is SGC?

**Spectral Graph Coarsening (SGC)** asks: *When can a complex system be validly approximated by a simpler one?*

**Key Concept: Defect (ε)**
```
ε = ||[L, Π]|| = ||(I-Π)LΠ||
```
The defect measures "leakage" - how much information escapes from the coarse description back to fine details.

**Key Files:**
- `src/SGC/Axioms/Geometry.lean` - Weighted L² geometry
- `src/SGC/Renormalization/Approximate.lean` - Approximate lumpability
- `README.md` - Core capabilities overview

---

## Part II: The Quantum Bridge (January 2026)

### Discovery: Classical Lumpability = Quantum Error Correction

We proved a formal correspondence:

| Classical (Markov) | Quantum |
|---|---|
| Exact lumpability (ε = 0) | Knill-Laflamme conditions |
| Approximate lumpability | Approximate QEC |
| Conservation law | Probability preservation |

**Main Theorem**: `knill_laflamme_forces_zero_defect`
> For classical Markov chains with conservation, the Knill-Laflamme condition forces ε = 0.

**Key Files:**
- `src/SGC/Bridge/Quantum.lean` - The isomorphism
- `ARCHITECTURE.md` - Module structure explanation

---

## Part III: Grokking Experiments (February 1-4, 2026)

### The Mystery

**Grokking**: Neural networks suddenly generalize long after memorizing training data.

We ran extensive experiments on modular arithmetic (a + b mod 97):

| Experiment | Setup | Grokking Epoch | Key Finding |
|------------|-------|----------------|-------------|
| Phase 1 | Standard MLP, WD=1.0 | ~10,800 | Spectral equilibration |
| Phase 1c | Scale-free metrics | ~11,600 | Gauge vs state distinction |
| Exploration Mass | M-triggered quench | ~4,700 | Mixing theory validated |
| Phase 6.1 | Full controller | ~5,200 | Controller bugs identified |

**Why different epochs?** Different hyperparameters, architectures, and controllers. The phenomenon is robust; the timing depends on setup.

**Key Files:**
- `reports/sgc_grokking_phase1_report.md` - Comprehensive Phase 1 analysis
- `demos/reports/exploration_mass_report_20260203.md` - Mixing theory validation
- `docs/math_analysis_20260204.md` - Controller failure analysis

---

## Part IV: THE BREAKTHROUGH (February 5, 2026)

### Discovery: Functional vs Geometric Blanket

**The key insight that changes everything:**

There are **TWO types of Markov blankets**, and they behave **oppositely** during grokking:

| Blanket Type | Definition | At Grokking |
|--------------|------------|-------------|
| **Geometric** (PCA-based) | Closure under linear projection | **INCREASES** (0.23→0.35) |
| **Functional** (Algebraic) | Within-class variance | **COLLAPSES** (1.0→0.003) |

### Why This Matters

**Old theory** (wrong): Grokking = dimensionality reduction (geometric compression)  
**New theory** (validated): Grokking = learning the **symmetry group** (algebraic structure)

The solution manifold is a **torus** (curved), not a flat linear subspace. That's why geometric defect increases!

### The Four Equivalences

```
1. Defect = Curvature       (not error)
2. Noise = Temperature      (Kramers escape)
3. Grokking = Phase Transition   (Lifshitz)
4. Continual Learning = Adiabatic Evolution
```

### Experimental Validation

| Metric | Pre-Grok | At Grok | Post-Grok |
|--------|----------|---------|-----------|
| **Functional Defect** | 1.01 | 0.13 | **0.003** |
| **Class Separation** | 0.01 | 6.45 | **346** |
| **Geometric Defect** | 0.23 | 0.35 | 0.33 |
| **Analog Speedup** | - | 2x | - |

**Key Files:**
- `docs/functional_blanket_breakthrough.md` - Initial discovery documentation
- `docs/lifshitz_transition_theory.md` - Full theoretical synthesis
- `docs/sgc_theory_roadmap.md` - Roadmap and predictions
- `demos/lifshitz_transition_experiment.py` - Validation experiment

---

## Part V: Lean Formalization (February 5, 2026)

### Formalized Concepts

| Module | Key Definitions | Status |
|--------|-----------------|--------|
| `FunctionalBlanket.lean` | FunctionalDefect, ClassSeparation, IsLifshitzTransition | ✓ Compiles |
| `KramersEscape.lean` | KramersEscapeTime, DiffusionRGIsomorphism | ✓ Compiles |
| `InformationGradientLaw.lean` | GradientRatio, TopologicalTransitionCondition | ✓ Compiles |
| `AdiabaticInvariant.lean` | ConstrainedUpdate, catastrophic_forgetting_prevention | ✓ Compiles |
| `Grokking.lean` | Umbrella module with re-exports | ✓ Compiles |

### Key Theorems (with placeholder proofs)

```lean
theorem grokking_is_lifshitz :
    FunctionalDefect(before) > 0.5 ∧ FunctionalDefect(after) < 0.15 →
    IsLifshitzTransition

theorem temperature_speedup :
    D₂ > D₁ > 0 → KramersEscapeTime(D₂) < KramersEscapeTime(D₁)

theorem catastrophic_forgetting_prevention :
    (∀ updates, Δw ⊥ ∇ε_func(TaskA)) →
    |ε_func(final) - ε_func(initial)| < tolerance
```

**Key Files:**
- `src/SGC/Grokking.lean` - Umbrella module
- `src/SGC/FunctionalBlanket.lean` - Core definitions
- `src/SGC/ContinualLearning/AdiabaticInvariant.lean` - Continual learning

---

## Part VI: Open Questions

### Validated ✓
- [x] Grokking is a topological (Lifshitz) transition
- [x] Functional defect collapse is the signature of grokking
- [x] Noise accelerates grokking (Kramers escape)
- [x] Tsallis q ≈ 2.5 scale-free structure

### In Progress
- [ ] Formalize proofs (remove `sorry` from Lean files)
- [ ] Continual learning experiments with functional blanket freezing
- [ ] Scale to transformer architectures

### Open
- Does functional blanket interpretation extend to continuous tasks?
- What is the minimal viable controller?
- How does this scale to billions of parameters?

---

## Quick Reference: Key Documents by Topic

### Theory
| Topic | Document |
|-------|----------|
| Core SGC | `README.md`, `ARCHITECTURE.md` |
| Quantum Bridge | `src/SGC/Bridge/Quantum.lean` |
| Functional Blanket | `docs/functional_blanket_breakthrough.md` |
| Lifshitz Transition | `docs/lifshitz_transition_theory.md` |
| Unified Theory | `docs/unified_theory_sgc_active_inference.md` |
| Roadmap | `docs/sgc_theory_roadmap.md` |

### Experiments
| Topic | Document |
|-------|----------|
| Phase 1 Grokking | `reports/sgc_grokking_phase1_report.md` |
| Exploration Mass | `demos/reports/exploration_mass_report_20260203.md` |
| Functional Defect | `docs/experimental_findings_20260204.md` |

### Code
| Topic | File |
|-------|------|
| Lifshitz Experiment | `demos/lifshitz_transition_experiment.py` |
| Functional Detector | `demos/functional_grokking_detector.py` |
| Analog Embeddings | `demos/analog_modular_arithmetic.py` |

---

## Citation

If you use this work, please cite:
```
SGC-Lean: Spectral Graph Coarsening for the Physics of Emergence
https://github.com/JasonShroyer/sgc-lean
```

---

## Glossary

| Term | Definition |
|------|------------|
| **Defect (ε)** | Commutator norm measuring coarse-graining error |
| **Functional Blanket** | Equivalence classes under algebraic symmetry |
| **Geometric Blanket** | PCA-based linear projection |
| **Grokking** | Delayed generalization after memorization |
| **Lifshitz Transition** | Topological phase transition without symmetry breaking |
| **Kramers Escape** | Barrier crossing rate governed by temperature |
| **Adiabatic Invariant** | Quantity conserved under slow parameter changes |
