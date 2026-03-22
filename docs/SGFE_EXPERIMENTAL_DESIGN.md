# SGC Spectral Gradient Flow Engine (SGFE) — Experimental Design Document

**Version**: 2.0  
**Date**: February 21, 2026  
**Status**: Active Development  
**For**: Third-Party Review  

---

## Executive Summary

This document describes our approach to solving the ARC (Abstraction and Reasoning Corpus) challenge using a theory-driven architecture grounded in formal mathematics. Unlike empirical machine learning approaches, every component traces to verified theorems in our Lean 4 formalization of the **Spectral Geometry of Consolidation (SGC)** theory.

**Key Results (97 ARC Training Tasks)**:
| Metric | Value |
|--------|-------|
| Perfect Solves | 19 (19.6%) |
| Near-Misses (< 15% error) | 51 (52.6%) |
| Tensor Logic Trigger Rate | 36.1% |
| Library Size (primitives) | 0 (no acceptance yet) |

**Current Challenge**: The Tensor Logic module discovers predicates (F1 > 0.30) but synthesized operations fail to improve functional defect across all training examples simultaneously. The bottleneck is **multi-stalk consistency** — predicates have different semantics across examples.

---

## 1. Theoretical Foundation

### 1.1 The Spectral Geometry of Consolidation (SGC)

SGC is a mathematical framework that unifies:
- **Information geometry** (Fisher metric, KL divergence)
- **Spectral graph theory** (Laplacian eigenvalues, diffusion)
- **Statistical physics** (phase transitions, renormalization)
- **Category theory** (sheaves, morphisms)

The central insight is that **learning is a geometric flow** on a statistical manifold, and **grokking** (sudden generalization after prolonged memorization) is a **topological phase transition**.

### 1.2 Formal Foundations (Lean 4)

Our theoretical claims are formalized and verified in Lean 4. Key modules:

| Module | Purpose | Key Theorem |
|--------|---------|-------------|
| `FunctionalBlanket.lean` | Grokking detection | `FunctionalDefect = withinClassVariance / totalVariance` |
| `Renormalization/Approximate.lean` | Coarse-graining | `trajectory_closure_bound` (Duhamel) |
| `InformationGeometry/TsallisStatistics.lean` | Non-extensive entropy | `TsallisEntropy_nonneg` |
| `Grokking.lean` | Unified interface | `grokking_is_lifshitz` |

### 1.3 The Functional Blanket Theory

**Definition** (from `FunctionalBlanket.lean`):

```
FunctionalDefect(h, π, K) = withinClassVariance(h, π, K) / totalVariance(h, π)
```

Where:
- `h : V → ℝ` are hidden states (representations)
- `π : V → ℝ` is the data distribution
- `K` is the number of equivalence classes

**Interpretation**: Functional defect measures whether the model has learned the **algebraic equivalence structure** of the task. When ε_func → 0, equivalent inputs map to identical representations.

**Experimental Validation** (February 2026, modular arithmetic):

| Phase | ε_func | Class Separation | Geometric Defect |
|-------|--------|------------------|------------------|
| Pre-Grok | 1.01 | 0.01 | 0.23 |
| At Grok | 0.13 | 6.45 | 0.35 |
| Post-Grok | 0.003 | 346 | 0.33 |

**Key Finding**: Grokking is a **Topological Lifshitz Transition**. The functional defect collapses while geometric defect may increase (the solution manifold is a flat torus that cannot embed isometrically in PCA subspace).

### 1.4 Renormalization and Coarse-Graining

**Definition** (from `Renormalization/Approximate.lean`):

The **leakage defect** D measures how much dynamics "leaks out" of a coarse-grained partition:

```
D = (I - Π) ∘ L ∘ Π
```

Where:
- `Π = lift ∘ Q` is the coarse-graining projector
- `L` is the generator of dynamics
- `opNorm(D) ≤ ε` defines approximate lumpability

**Theorem** (`trajectory_closure_bound`): If `opNorm(D) ≤ ε`, then trajectories in the full and coarse-grained systems stay within O(ε·t) for time t.

**Application to ARC**: A good partition Π groups pixels that undergo the same transformation. The leakage defect measures how well this partition respects the true task dynamics.

### 1.5 Tsallis Statistics and Temperature

**Definition** (from `TsallisStatistics.lean`):

The Tsallis entropy generalizes Shannon entropy:

```
S_q(p) = (1 - Σᵢ pᵢ^q) / (q - 1)
```

The **escort distribution** re-weights probabilities:

```
P_q(i) = pᵢ^q / Σⱼ pⱼ^q
```

**Experimental Finding**: During grokking, the Tsallis parameter q follows a characteristic trajectory:
- **Pre-grok**: q ≈ 2.53 (sub-additive, memorization)
- **At transition**: q ≈ 2.09 (critical point)
- **Post-grok**: q ≈ 2.76 (super-additive, generalization)

This "double transition" schedule (q: 2.53 → 2.09 → 2.76) is implemented as `tsallis_temperature_schedule` in SGFE.

---

## 2. Architecture Overview

### 2.1 System Diagram

```
┌─────────────────────────────────────────────────────────────────────┐
│                         ARC-SGC Agent                               │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌─────────────────┐  ┌──────────────────┐  ┌───────────────────┐  │
│  │ Long-Term       │  │ Working Memory   │  │ Dream             │  │
│  │ Memory (LTM)    │  │ (Task-Local)     │  │ Consolidation     │  │
│  │                 │  │                  │  │                   │  │
│  │ • Color Maps    │  │ • Current Task   │  │ • Sleep Cycle     │  │
│  │ • Rules         │  │ • Candidates     │  │ • Pattern         │  │
│  │ • Priors        │  │ • Residuals      │  │   Extraction      │  │
│  └────────┬────────┘  └────────┬─────────┘  └─────────┬─────────┘  │
│           │                    │                      │             │
│           └────────────────────┼──────────────────────┘             │
│                                │                                    │
│                                ▼                                    │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                    SOLVER FAMILY                             │   │
│  │                                                              │   │
│  │  ┌──────────────┐  ┌──────────────┐  ┌────────────────────┐ │   │
│  │  │ Phase 45     │  │ Heuristic    │  │ Recursive Residual │ │   │
│  │  │ (Patterns)   │  │ (Macros)     │  │ (Gradient-Guided)  │ │   │
│  │  │              │  │              │  │                    │ │   │
│  │  │ Neighborhood │  │ rot/flip     │  │ + Tensor Logic     │ │   │
│  │  │ constraints  │  │ scale        │  │ + SGFE Engine      │ │   │
│  │  │ zone-gated   │  │ crop         │  │                    │ │   │
│  │  └──────────────┘  └──────────────┘  └────────────────────┘ │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 2.2 The Agent Loop

```python
for task in tasks:
    # 1. PERCEIVE: Extract task features
    features = extract_task_features(task)
    
    # 2. RECALL: Query LTM for matching priors
    priors = ltm.query(features)
    
    # 3. SOLVE: Multi-solver with priority
    result = solve_with_family(task, priors)
    
    # 4. LEARN: Extract successful patterns
    if result.success:
        patterns = extract_patterns(result)
        wm.store(patterns)
    
    # 5. CONSOLIDATE: Promote high-utility patterns to LTM
    ltm.consolidate(wm.high_utility_patterns())
```

### 2.3 Solver Family Priority

1. **Phase 45 (Patterns)**: Neighborhood constraint learning with zone-gated contexts
2. **Heuristic (Macros)**: Global transformations (rotation, scaling, cropping)
3. **Recursive Residual (Gradient-Guided)**: Beam search over operator compositions + Tensor Logic

---

## 3. Key Components

### 3.1 SGFE Engine (`sgfe_engine.py`)

The SGFE Engine provides theory-grounded primitives:

| Component | Theory Source | Purpose |
|-----------|---------------|---------|
| `functional_blanket_variance` | FunctionalBlanket.lean | ANOVA-based ε_func |
| `hermite_gaussian_encode` | Renormalization.lean | Multiscale wavelet features |
| `tsallis_temperature_schedule` | TsallisStatistics.lean | q-annealing schedule |
| `sheaf_consistency_energy` | CellularSheafNetwork | Multi-stalk coherence |
| `SGFEPrimitiveLibrary` | Renormalization.lean | Learned operator catalog |

#### 3.1.1 Functional Defect Scoring

```python
def sgfe_defect_delta(
    grid_before: np.ndarray,
    grid_after: np.ndarray, 
    target: np.ndarray,
    mode: str = 'discrete'
) -> float:
    """
    Universal functional defect delta scorer.
    
    Δε = ε(before) - ε(after)
    Positive = improvement, Negative = regression
    
    Modes:
      - 'discrete': Pixel mismatch rate (fast)
      - 'continuous': ANOVA on Hermite features (theory-aligned)
    """
```

#### 3.1.2 Acceptance Gate

```python
def sgfe_acceptance_gate_v2(
    total_delta: float,      # Sum of per-example Δε
    worst_delta: float,      # Minimum per-example Δε
    mi_score: float,         # Mutual information MI(Π, ChangeLabel)
    sheaf_energy: float,     # E_sheaf from consistency check
    mi_threshold: float = 0.25,
    sheaf_threshold: float = 0.6,
) -> Tuple[bool, str]:
    """
    SGFE v2.0 Acceptance Gate.
    
    Theory grounding:
      - MI > 0.25: Predicate captures meaningful structure (OptimalPartition.lean)
      - Sheaf < 0.6: Consistent semantics across examples (positive_Ricci_tensorizes)
      - worst_delta >= -0.01: Allow small regressions (grokking is gradual)
      - total_delta > 0: Net improvement required
    """
```

### 3.2 Tensor Predicate Learner (`arc_tensor_logic.py`)

The Tensor Predicate Learner discovers spatial predicates via gradient descent:

```python
class TensorPredicateLearner:
    """
    Gradient-descent predicate discovery for residual refinement.
    
    Theory (OptimalPartition.lean):
      - The optimal partition Π maximizes MI(Π, ChangeLabel)
      - This is equivalent to minimizing within-class variance
      - Gradient descent on soft partition parameters finds local optima
    
    Pipeline:
      1. Encode pixels as feature vectors (discrete or Hermite-Gaussian)
      2. Initialize soft partition Π ∈ [0,1]^(H×W)
      3. Gradient descent on BCE loss against residual mask
      4. Threshold to hard predicate
      5. Score via F1, MI, and sheaf consistency
    """
```

#### 3.2.1 Feature Encoding Options

| Mode | Description | Theory |
|------|-------------|--------|
| **Discrete** | Color one-hot + position + neighborhood | Default, fast |
| **Hermite-Gaussian** | Multiscale wavelets at scales (1, 2, 4) | Renormalization.lean |

### 3.3 Recursive Residual Solver (`arc_sgc_residual_solver.py`)

The main solver uses gradient-guided beam search:

```python
class RecursiveResidualSolver:
    """
    Gradient-guided program synthesis for ARC.
    
    Algorithm:
      1. Compute residual gradient G = (pred - target)
      2. Propose operators that address G (recolor, fill, erase, ...)
      3. Score by information gain: IG = ε(before) - ε(after)
      4. Beam search over compositions (depth ≤ 3, width = 8)
      5. Cross-example verification: must improve ALL examples
    
    Tensor Logic integration:
      - Triggers when gradient-guided ops plateau
      - Discovers custom predicates via TensorPredicateLearner
      - Accepted predicates become permanent operators (renormalization)
    """
```

### 3.4 Sheaf Consistency Energy

```python
def sheaf_consistency_energy(
    predicate_masks: List[np.ndarray],  # Per-example masks
    feature_vectors: List[np.ndarray],  # Per-example features
) -> float:
    """
    Measures semantic consistency of a predicate across examples.
    
    Theory (CellularSheafNetwork):
      - A sheaf assigns data (features) to each "stalk" (example)
      - Consistency = how well stalks agree under restriction maps
      - E_sheaf = ||L_sheaf · features||² where L_sheaf is the sheaf Laplacian
      - Low energy = consistent meaning across examples
    
    For ARC:
      - Each training example is a "stalk"
      - Predicate selects a region in each example
      - Consistency = feature similarity of selected regions
    """
```

---

## 4. Prior Experimental Results

### 4.1 Agent Evolution

| Phase | Perfect | Near | Key Change |
|-------|---------|------|------------|
| Phase 45 standalone | 1 | 7 | Neighborhood rules only |
| + Memory (Phase 21) | 9 | 35 | Content-addressed priors |
| + Residual Solver | 14 | 46 | Gradient-guided synthesis |
| + Object Predicates | 16 | 48 | SceneGraph integration |
| + Zone-Gated P45 | 19 | 51 | 5-zone structural context |

### 4.2 Evaluation Set (400 Tasks)

| Metric | Value |
|--------|-------|
| Perfect Solves | 23 (5.75%) |
| Near-Misses | 139 (34.75%) |
| Fails | 238 (59.5%) |

**Solver Family Wins**:
- Phase 45 (patterns): **147 wins** (dominant)
- Residual (synthesis): **16 wins**
- Heuristic (macros): **7 wins**

### 4.3 Dream Consolidation

The agent persists learned patterns across sessions:

| Metric | Value |
|--------|-------|
| Compiled Programs | 28 |
| Persisted Contexts | 17 |
| Average Posterior | 0.81 |

**Cross-Session Grokking**: We observed posteriors evolving across sessions, with 2 patterns "grokking" (posterior > 0.9) after epoch 2.

---

## 5. Current Direction: SGFE v2.0

### 5.1 Goal

Achieve **>30% acceptance rate** on Tensor Logic triggered tasks and demonstrate **measurable library compression** (primitives learned and reused).

### 5.2 Implementation Status

| Step | Status | Description |
|------|--------|-------------|
| 1. Universal Scorer | ✅ Complete | `sgfe_defect_delta` as single source of truth |
| 2. Hermite Wavelets | ✅ Complete | Wired into `TensorPredicateLearner` |
| 3. Renormalization | ✅ Complete | `add_new_primitive` on acceptance |
| 4. Acceptance Gate v2 | ✅ Complete | Refined thresholds (MI > 0.25, sheaf < 0.6) |
| 5. Eval Harness | ✅ Complete | Fixed metrics display (clamped defects) |

### 5.3 Current Bottleneck

**Problem**: Tensor Logic triggers on 36.1% of tasks but **0% acceptance**.

**Root Cause Analysis**:

1. **Predicates ARE discovered** (F1 > 0.30, MI > 0.2)
2. **Operations ARE synthesized** (recolor, fill based on predicate)
3. **But**: Operations worsen some examples even while improving others
4. **Why**: The predicate has **different semantics** across examples

**Example**: A predicate "pixels adjacent to color 5" might select:
- Example 1: Interior pixels (should become red)
- Example 2: Border pixels (should become blue)

The predicate is spatially consistent but semantically inconsistent.

### 5.4 Hypotheses for Resolution

1. **Object-Level Predicates**: Reason about objects (SceneGraph) rather than pixels
2. **Per-Example Acceptance**: Accept if SOME examples improve, then intersect
3. **Semantic Features**: Include "what transformation happens" as a feature
4. **Clustering Before Predicate**: Group examples by transformation type first

---

## 6. Methodological Principles

### 6.1 Theory-First Development

Every implementation change must be **derived from first principles**:

> "We work from SGC Theory FIRST, Physics & Mathematics SECOND, NEVER empirical iteration."

**Prohibited**:
- Random hyperparameter tuning
- "Try and see" iterations
- Empirical fitting without theoretical justification

**Required**:
- Cite relevant Lean theorem or physics principle
- Explain WHY the change should work
- Predict expected quantitative improvement

### 6.2 Verification Standards

1. **No Regressions**: Every change must maintain or improve 97-task perfect count
2. **Axiom Audit**: New Lean theorems must pass `#print axioms`
3. **Cross-Session Stability**: Results must reproduce across fresh agent instances

### 6.3 The Hierarchy of Sources

1. **SGC Theory** (Lean formalization)
2. **Physics & Mathematics** (established principles)
3. **Empirical Observation** (only to validate, never to guide)

---

## 7. Repository Structure

```
C:\Lean4 Projects\
├── src/SGC/                    # Lean 4 formalization
│   ├── FunctionalBlanket.lean  # Grokking detection
│   ├── Grokking.lean           # Unified interface
│   ├── Renormalization/        # Coarse-graining theory
│   ├── InformationGeometry/    # Tsallis, Fisher, KL
│   └── ...
├── demos/                      # Python implementation
│   ├── sgfe_engine.py          # SGFE components
│   ├── arc_sgc_agent.py        # Unified agent
│   ├── arc_sgc_residual_solver.py  # Gradient-guided solver
│   ├── arc_tensor_logic.py     # Predicate learner
│   ├── eval_97_tensor.py       # Evaluation harness
│   └── ...
├── docs/                       # Documentation
│   ├── SGFE_EXPERIMENTAL_DESIGN.md  # This document
│   └── ...
└── lakefile.lean               # Lean build configuration
```

---

## 8. Open Questions

1. **Why does grokking occur in SGD but not in our beam search?**
   - SGD has implicit regularization (weight decay, noise)
   - Beam search is greedy, no "simulated annealing"
   - Possible: Add temperature to operator selection

2. **Can we verify the Lifshitz transition in ARC?**
   - Need to track ε_func across refinement rounds
   - Look for sudden collapse followed by stabilization

3. **Is the 0% acceptance a feature discovery problem or an acceptance criteria problem?**
   - Current evidence suggests feature discovery (predicates don't generalize)
   - But MI and sheaf thresholds may be too strict

---

## 9. References

### 9.1 Internal

- `src/SGC/FunctionalBlanket.lean` — Functional defect formalization
- `src/SGC/Renormalization/Approximate.lean` — Coarse-graining theory
- `src/SGC/InformationGeometry/TsallisStatistics.lean` — Tsallis entropy
- `demos/lifshitz_transition_experiment.py` — Grokking validation

### 9.2 External

- Chollet, F. (2019). "On the Measure of Intelligence" (ARC benchmark)
- Tsallis, C. (1988). "Possible generalization of Boltzmann-Gibbs statistics"
- Naudts, J. (2011). "Generalised Thermostatistics"
- Power et al. (2022). "Grokking: Generalization Beyond Overfitting"

---

## 10. Contact

For questions about this experimental design, contact the SGC Research team.

**Document Version History**:
- v2.0 (Feb 21, 2026): SGFE v2.0 implementation complete
- v1.0 (Feb 14, 2026): Initial architecture document
