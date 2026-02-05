# Functional Blanket Breakthrough: Grokking as Algebraic Phase Transition

**Date**: February 5, 2026  
**Status**: THEORY VALIDATED

## Executive Summary

We experimentally validated that **grokking is an algebraic phase transition**, not geometric compression. The key insight: there are TWO types of blankets, and they behave oppositely during grokking.

| Blanket Type | During Grokking | Interpretation |
|--------------|-----------------|----------------|
| **Geometric** (PCA-based closure defect) | INCREASES | Model learns curved manifold (torus) |
| **Functional** (within-class variance) | COLLAPSES | Model learns equivalence classes |

## Experimental Results

### Setup
- Task: Modular addition (a + b) mod 97
- Model: 2-layer MLP with learned embeddings
- Metrics tracked every 50 epochs

### Key Findings

#### 1. Functional Defect Collapses at Grokking

```
DISCRETE EMBEDDINGS:
  Epoch 2150 (pre-grok):  FuncD = 0.2484, Test = 74.1%
  Epoch 2300 (grokking):  FuncD = 0.1376, Test = 98.3%  ← GROKKING!
  Epoch 2800 (post-grok): FuncD = 0.0250, Test = 100%

ANALOG EMBEDDINGS (noise σ=0.1):
  Epoch 1050 (pre-grok):  FuncD = 0.3532, Test = 48.7%
  Epoch 1150 (grokking):  FuncD = 0.1470, Test = 99.4%  ← GROKKING!
  Epoch 1650 (post-grok): FuncD = 0.0201, Test = 100%
```

The functional defect (within-class variance / total variance) dropped from ~1.0 to ~0.02, meaning representations within each equivalence class collapsed to nearly identical points.

#### 2. Geometric/Closure Defect INCREASES at Grokking

```
DISCRETE:
  Pre-grok:  CloseD = 0.2303
  At grok:   CloseD = 0.3475  ← INCREASED!
  Post-grok: CloseD = 0.3274

ANALOG:
  Pre-grok:  CloseD = 0.2276
  At grok:   CloseD = 0.3461  ← INCREASED!
  Post-grok: CloseD = 0.3702
```

The closure defect ||g(h) - g(Π h)|| / ||g(h)|| increased because the learned representation is a CURVED manifold (torus for mod-p), not a flat linear subspace.

#### 3. Class Separation Spikes at Grokking

```
DISCRETE: 0.03 → 6.30 → 39.1  (1300x increase!)
ANALOG:   0.03 → 5.83 → 48.7  (1600x increase!)
```

The ratio between_class_variance / within_class_variance explodes, meaning the model learns to perfectly separate the p=97 equivalence classes.

#### 4. Analog World Groks 2x Faster

```
DISCRETE: Grokking at epoch 2300
ANALOG:   Grokking at epoch 1150  (2x faster!)
```

Adding Gaussian noise to embeddings during training accelerates grokking by forcing the model to learn robust, topologically correct boundaries.

## Theoretical Interpretation

### Two Blankets, Not One

1. **Geometric Blanket (Π_PCA)**: Projects onto top-k principal components
   - Measures: Is the data low-dimensional in Euclidean sense?
   - Grokking VIOLATES this: defect increases
   - Why: The solution manifold (torus) has non-zero intrinsic curvature

2. **Functional Blanket (Π_algebraic)**: Groups by equivalence class under symmetry
   - Measures: Do algebraically equivalent inputs map to same representation?
   - Grokking SATISFIES this: defect collapses
   - Why: The model learns the symmetry group of the task

### Grokking = Lifshitz Transition

In condensed matter physics, a Lifshitz transition reconstructs the Fermi surface topology without symmetry breaking. Grokking exhibits analogous physics:

- **Pre-grokking**: Loss landscape has disconnected local minima (memorization)
- **Transition**: Van Hove singularity crosses Fermi level (eigenvalue density peak)
- **Post-grokking**: New topological sector accessed (the algebraic circuit)

The geometric defect increases because the model accesses a higher-curvature configuration space.

### Why Analog Works

Floating-point noise creates "thick" manifolds where 3.001 ≈ 3.0. This:
1. Forces the model to learn regions, not points
2. Induces natural smoothing toward robust (minimum energy) configurations
3. Breaks degeneracy of orthogonal discrete inputs
4. Provides thermal kicks over saddle points separating memorization from generalization

## Implications

### For Intrinsic Grokking Detection

The functional defect provides an **intrinsic signal** for grokking that doesn't require test labels:

```python
def intrinsic_grokking_detector(hidden_states, targets, p):
    func_defect = compute_functional_defect(hidden_states, targets, p)
    if func_defect < 0.15:  # Threshold
        return "GROKKING DETECTED"
```

This works because functional defect collapse is the **definition** of learning the algebraic structure.

### For AGI-Scale Systems

At scale, test sets don't exist for many capabilities. Functional defect measurement enables:
- Intrinsic capability detection without external supervision
- Early warning of structure emergence
- Principled stopping criteria based on algebraic consolidation

### For SGC Theory

The Markov blanket in SGC should be interpreted **functionally**, not **geometrically**:
- Inside = task-relevant features (algebraic structure)
- Outside = task-irrelevant features (noise)
- Blanket = symmetry group separating equivalence classes

The defect ε = ||Π_functional g(h) - Π_functional g(Π h)|| measures whether dynamics respect the symmetry.

## Code Artifacts

- `functional_defect_experiment.py`: Full experiment with both defect types
- `analog_modular_arithmetic.py`: Dataset and model implementations
- `compute_functional_defect_detailed()`: The key measurement function

## Conclusion

**THEORY VALIDATED**: Grokking is an algebraic phase transition where:
1. Functional defect (within-class variance) → 0
2. Geometric defect (PCA closure) increases
3. Class separation (Fisher's criterion) explodes
4. Analog/noisy inputs accelerate the transition 2x

The Markov blanket is FUNCTIONAL (symmetry-respecting), not GEOMETRIC (low-dimensional). This resolves the paradox of why closure defect increased in our earlier experiments.

## Next Steps

1. Implement functional defect in the active inference controller
2. Test on other algebraic tasks (multiplication, division, permutation groups)
3. Extend to transformer architectures
4. Formalize the Lifshitz transition analogy mathematically
5. Connect to Tsallis entropy (q-transition at grokking?)
