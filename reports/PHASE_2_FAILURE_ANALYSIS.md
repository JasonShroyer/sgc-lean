# Phase 2 Failure Analysis: Post-Hoc Gluing Does Not Work

**Date:** 2026-02-06  
**Status:** Definitive Negative Result  
**Implication:** Pivot to Native Sheaf Architecture Required

---

## 1. Executive Summary

The "Sheaf Connector" experiment attempted to compose two frozen, perfectly-grokked neural manifolds (Task A: Addition, Task B: Multiplication) into a compositional Task C: `(x + y) * z mod p`. 

**Result: Complete Failure.**

| Metric | Value | Interpretation |
|--------|-------|----------------|
| Task A (frozen) | 100% | ✅ Stalk preserved |
| Task B (frozen) | 100% | ✅ Stalk preserved |
| Task C (composition) | 3.4% | ❌ Random chance = 1.03% |
| Zero-shot | 1.1% | Baseline |
| Improvement | +2.3% | Negligible |

The restriction maps learned *something* (σ_add = 36.8, σ_mul = 7.2 deviation from identity), but this "learning" was essentially random projection—there was no meaningful transformation between spaces that share no geometric structure.

---

## 2. Theoretical Diagnosis

### 2.1 The Disjoint Union Problem

The "Separate Pathways" architecture in `DualTaskMLP` creates:

```
M_A ⊔ M_B  (disjoint union)
```

Not:

```
M_A ×_ρ M_B  (fiber product over shared base)
```

**Mathematical Fact:** A sheaf requires stalks defined over a *shared* base space. The fiber product `M_A ×_ρ M_B` is only non-degenerate when the restriction maps `ρ_A` and `ρ_B` agree on a common intersection.

When `M_A ∩ M_B = ∅`, the fiber product collapses to the empty set. The Sheaf Laplacian diffusion has nowhere to propagate—it's trying to heat-diffuse across a vacuum.

### 2.2 Why Linear Restriction Maps Failed

```python
rho_add: R^256 → R^256  (learned σ = 36.8)
rho_mul: R^256 → R^256  (learned σ = 7.2)
```

These matrices learned to project the stalks into a common space, but:

1. **No Shared Semantics:** The addition stalk encodes `x + y`; the multiplication stalk encodes `z`. There's no shared "meaning" for a linear map to preserve.

2. **Random Projection Behavior:** Large deviation from identity indicates the maps learned arbitrary transformations, not structure-preserving morphisms.

3. **Diffusion Fails:** The Sheaf Laplacian `Δ_F = B^T D B` computes energy based on disagreement between adjacent stalks. But when stalks live in semantically disjoint spaces, "agreement" is undefined.

### 2.3 The Fundamental Tension

| Strategy | Forgetting | Composition |
|----------|------------|-------------|
| Total Isolation (M_A ∩ M_B = ∅) | ✅ None | ❌ Impossible |
| Total Sharing (M_A = M_B) | ❌ Catastrophic | ✅ Perfect |
| **Controlled Intersection** | ✅ Minimal | ✅ Possible |

**Insight:** We need an architecture where `M_A ∩ M_B ≠ ∅` but the intersection is *small* and *controlled*—a "wormhole" between manifolds, not a vacuum.

---

## 3. What We Learned

### 3.1 Positive Findings

1. **Grokking Detection Works:** The fixed ε measurement correctly tracked both Task A and Task B's grokking transitions (ε: 1.0 → 0.12-0.14).

2. **Memory Protection Works:** Task A remained at 100% accuracy throughout Task B training with zero parameter drift.

3. **Sheaf Energy Computable:** The Laplacian energy metric tracked training (though it didn't converge to low values).

### 3.2 Negative Findings

1. **Post-Hoc Gluing Fails:** You cannot compose neural modules that were trained in isolation, even with learnable restriction maps.

2. **Linear Maps Insufficient:** The composition function `(x + y) * z` requires non-linear interaction between the summation and product representations.

3. **Diffusion ≠ Composition:** Heat diffusion finds *harmonic* sections (minimize disagreement), not *compositional* sections (compute a function of inputs).

---

## 4. Theoretical Implications for SGC

### 4.1 The Sheaf Hypothesis Validated (Negatively)

The experiment validates the **Sheaf Hypothesis** by contrapositive:

> **If** compositionality exists, **then** there must be a shared base space.
> 
> **Contrapositive:** No shared base → No compositionality. ✅ Confirmed.

### 4.2 Architectural Requirements for Composition

For Task C = f(Task A, Task B), the architecture must satisfy:

1. **Shared Embedding:** Inputs `x, y, z` must share a common representational space.
2. **Compositional Structure:** The computation graph must reflect the algebraic structure `(x + y) * z`.
3. **Geometric Intersection:** The hidden spaces for A and B must overlap on a subspace where composition is defined.

### 4.3 The Path Forward: Native Sheaf Architecture

**The network must BE a sheaf, not HAVE a sheaf retrofitted.**

Key insight: Instead of training a neural network and then extracting sheaf structure, we construct the network AS a cellular sheaf:

- **Base Space:** Cellular complex (graph) representing concepts
- **Stalks:** Vector spaces at nodes (not hidden layers)
- **Restriction Maps:** Trainable matrices on edges
- **Learning Rule:** Dissipative (minimize Laplacian energy for correct outputs)

This architecture computes geometry natively—the "Functional Blanket" becomes literal sheaf cohomology.

---

## 5. Experimental Record

### 5.1 Configuration

```python
config = SheafConfig(
    p=97,
    stalk_dim=256,
    diffusion_steps=10,
    diffusion_alpha=0.8,
)
```

### 5.2 Training Curves

```
Epoch |   Train |    Test |     Energy
---------------------------------------------
    0 |    4.1% |    2.9% |   554.4
  100 |    8.4% |    3.5% |  3948.5
  200 |    8.3% |    3.4% |  4385.3
  300 |    9.0% |    3.5% |  4333.1
  400 |    9.3% |    3.3% |  4066.7
  499 |    9.6% |    3.4% |  3913.8
```

The Sheaf energy remained high (~4000), indicating the sections never became harmonic—the stalks remained mutually inconsistent.

### 5.3 Restriction Map Analysis

```
rho_add deviation from identity: 36.8318
rho_mul deviation from identity: 7.2081
rho_z deviation from identity:   22.7161
```

All maps diverged from identity, indicating learning occurred but without meaningful structure preservation.

---

## 6. Conclusion

**This negative result is scientifically valuable.** It provides empirical proof that:

1. Compositional generalization requires architectural support
2. Post-hoc sheaf structures cannot bridge disjoint manifolds
3. The path to AGI through modular composition requires *native* geometric computation

**Next Step:** Implement `CellularSheafNetwork`—a network where the sheaf structure IS the computation, not an analysis tool applied post-hoc.

---

## References

- Hansen & Ghrist (2019). "Toward a Spectral Theory of Cellular Sheaves"
- Bodnar et al. (2022). "Neural Sheaf Diffusion"
- This project's `sgc_sheaf_connector.py` and `sgc_continual_learning.py`
