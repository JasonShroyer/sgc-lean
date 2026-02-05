# Experimental Findings: Defect Dynamics During Grokking

**Date**: February 4, 2026  
**Status**: Key findings that revise the theory

## Summary

We ran A/B experiments comparing discrete vs noisy ("analog") embeddings on modular arithmetic grokking, tracking:
- **Tail defect**: ||h - Π(h)|| / ||h|| (dimensionality proxy)
- **Closure defect**: ||g(h) - g(Π(h))|| / ||g(h)|| (dynamic consistency)
- **Consolidation**: 1 - S_q (Tsallis entropy)

## Key Results

| Condition | Grokking Epoch | Final Tail Defect | Final Closure Defect |
|-----------|----------------|-------------------|----------------------|
| Discrete embeddings | 2100 | 0.298 | 0.391 |
| Noisy embeddings (σ=0.1) | **1100** | 0.313 | 0.323 |

### Finding 1: Noisy Embeddings Grok 2x Faster

**Validates the "analog world" hypothesis**: Adding noise to embeddings during training accelerates grokking from epoch 2100 to 1100 (1.9x speedup).

**Interpretation**: The noise forces the model to learn a more robust representation that generalizes. In the discrete case, the model can memorize exact embeddings; with noise, it must learn the underlying algebraic structure.

This aligns with the "universe cooling" intuition: start with a richer/noisier world, and the model learns to filter and structure.

### Finding 2: Closure Defect INCREASES During Grokking

**Contradicts initial theory**: We predicted closure defect would drop when the "Markov blanket closes." Instead:

```
Discrete: CloseD went from 0.23 (pre-grok) → 0.36 (grok) → 0.39 (post-grok)
Noisy:    CloseD went from 0.23 (pre-grok) → 0.34 (grok) → 0.32 (post-grok)
```

The closure defect **increased** during grokking in both conditions.

### Finding 3: Neither Defect Crossed Our Thresholds

- Tail defect stayed ~0.30 (never below 0.15)
- Closure defect stayed ~0.23-0.40 (never below 0.15)
- Consolidation stayed ~0.003-0.004 (never above 0.5)

Our intrinsic grokking detector would have missed the actual grokking!

## Revised Theory

### Why Closure Defect Increases

The closure defect ||g(h) - g(Π h)|| measures how much the output changes when we project h to its top-k PCs. During grokking:

1. **The representation becomes MORE structured, not less dimensional**
2. **The "tail" carries meaningful algebraic information** that the output layer uses
3. **Grokking = learning to USE the full representation space**, not compress it

This is fundamentally different from the compression hypothesis!

### New Blanket Interpretation

The Markov blanket analogy needs revision:

| Old View | New View |
|----------|----------|
| Inside = top-k PCs | Inside = algebraically relevant features |
| Outside = tail (noise) | Outside = non-algebraic features |
| Blanket closure = tail → 0 | Blanket closure = functional separation |
| Grokking = dimensionality collapse | Grokking = structure emergence |

**Key insight**: The blanket isn't defined by dimensionality (PCA) but by **functional relevance** to the task. The model learns WHICH dimensions matter, not to eliminate dimensions.

### What Defect Should We Measure?

The current closure defect measures sensitivity to PCA projection. What we actually want:

```
Task-relevant defect = How much does the output change when we perturb 
                       task-IRRELEVANT features while preserving task-RELEVANT ones?
```

But this requires knowing which features are task-relevant - which is what the model is learning!

**Circular problem**: We can't define the blanket without knowing the structure, but learning the structure IS the blanket formation.

### Resolution: Defect as Functional Consistency

Instead of ||g(h) - g(Π h)||, consider:

```
Functional defect = How consistent is the model's output across 
                    algebraically equivalent inputs?
```

For modular addition: if (a,b) and (a',b') both equal c mod p, does the model output the same thing?

This measures whether the model has learned the **equivalence classes** of the algebra, not the dimensionality of the representation.

## Implications for the Theory

### What's Validated

1. **Analog/noisy inputs accelerate grokking** ✓
2. **Structure emerges through learning** ✓
3. **The cooling analogy works** (noise → less noise → crystallization) ✓

### What Needs Revision

1. **Defect ≠ blanket quality** (at least not PCA-based defect)
2. **Grokking ≠ dimensionality collapse**
3. **Intrinsic detection needs different observables**

### Candidate Observables for Intrinsic Detection

1. **Train-test gap velocity**: d(train_loss - test_loss)/dt
2. **Weight norm velocity**: d||W||/dt (should stabilize)
3. **Gradient noise scale**: ||∇L||² / ||∇L||² should decrease
4. **Representation similarity across algebraic equivalents**

## Next Steps

1. Implement **functional defect** based on algebraic equivalence classes
2. Track **train-test gap velocity** as grokking signal
3. Test whether **gradient noise scale** predicts grokking
4. Revisit the Markov blanket = functional separation interpretation

## Conclusion

The experiments validate the analog world hypothesis (2x speedup!) but force us to revise the defect theory. Grokking is not about dimensionality collapse - it's about learning the right algebraic structure. The Markov blanket should be defined functionally, not geometrically.

This is progress: we've falsified a hypothesis and gained deeper insight.
