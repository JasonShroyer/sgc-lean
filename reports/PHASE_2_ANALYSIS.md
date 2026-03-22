# Phase 2 Analysis: Diagnosis & Theoretical Insights

**Date:** February 6, 2026  
**Status:** Experiment paused for analysis

---

## 1. What Succeeded ✅

### 1.1 Phase 1: Geometric Sensing Works
- **Functional Defect (ε)** successfully detects grokking
- **Geometric Susceptibility (χ_g)** peaks at phase transition
- Confirmed: In SGD, phase transitions are encoded in **geometry, not energy**

### 1.2 Phase 1A: Continual Learning Works (with caveats)
- Task A groks: **100% accuracy, ε = 0.126**
- Task B learns: **100% accuracy** (functional success)
- Memory protection: Task A **preserved at 100%** while Task B trains
- The "freeze-thaw" mechanism prevents catastrophic forgetting

### 1.3 Architecture Insight
The **separate pathways** design successfully achieves:
- **Isolation**: Task A cannot be corrupted by Task B training
- **Capacity**: Each task gets dedicated parameters
- **Stability**: Frozen parameters remain truly frozen

---

## 2. What Failed ❌

### 2.1 Task B's ε Stays at 1.0
Despite 100% accuracy, Task B's functional defect never drops:
```
Task A: 100.0% accuracy, ε = 0.126 ✓
Task B: 100.0% accuracy, ε = 1.000 ✗
```

**Diagnosis:** The ε metric is computed on the **wrong hidden representation**. 
- We measure `get_shared_hidden()` for Task A
- But Task B uses `get_mul_hidden()` (completely separate)
- The metric doesn't "see" Task B's actual representation

**Root Cause:** The measurement assumes shared structure that doesn't exist.

### 2.2 Composition Impossible with Disjoint Pathways
The Perplexity research confirmed our architecture creates:
```
M_A ⊔ M_B  (disjoint union)
```
But composition requires:
```
M_A ×_{M_C} M_B  (fiber product)
```

**Insight:** We solved isolation but **sacrificed interaction**.

### 2.3 Grokking Sensitivity
The simpler training loops in `sgc_sheaf_composition.py` didn't grok because:
- Grokking requires precise hyperparameters (wd=0.5, lr=1e-3, epochs~650+)
- Small architectural changes break the phenomenon
- The "grokking recipe" is fragile

---

## 3. Theoretical Insights 💡

### 3.1 The Perplexity Mapping (Confirmed)

| SGC Concept | Sheaf Theory | Meaning |
|-------------|--------------|---------|
| Functional Defect ε | Sheaf Laplacian Energy | Local inconsistency |
| Grokking | Cohomology Collapse H¹→0 | Global section emerges |
| Functional Blanket | Global Section | Consistent truth across stalks |
| Separate Pathways | Disjoint Union | No interaction possible |

### 3.2 The Isolation-Interaction Tradeoff

```
         ISOLATION (Phase 1A achieves this)
              ↑
              |
    [Separate Pathways]
              |
              ↓
         INTERACTION (Composition requires this)
```

**Key Insight:** You cannot have both with disjoint architectures.

### 3.3 Why ε = 1.0 for Task B

The functional defect measures within-class variance in **representation space**:
```
ε = Var(h | class) / Var(h)
```

For Task B's separate pathway:
- The hidden representation `h_mul` is learned independently
- It has **no geometric relationship** to the classes from Task A's perspective
- From the ε measurement's viewpoint, Task B's representation looks random

**This is a measurement bug, not a learning bug.**

### 3.4 The "Two Models in One Container" Problem

Phase 1A doesn't create a unified representation. It creates:
```python
# Effectively two independent models:
model_A = embed_a + fc1 + fc2 + head_add      # Frozen
model_B = mul_embed + mul_fc1 + mul_fc2 + head_mul  # Trained

# They share nothing except:
# - The nn.Module container
# - The optimizer (but operating on disjoint params)
```

**Implication:** There is no "Functional Blanket" spanning both tasks—there are TWO blankets.

---

## 4. A Better Approach? 🔄

### 4.1 Option A: Shared Embeddings, Task-Specific Heads
```
           [Shared Embeddings]
                   |
           [Shared Hidden]
                 /   \
    [Head_Add]       [Head_Mul]
```

**Pros:** Single representation space; composition possible  
**Cons:** Risk of interference; harder to prevent forgetting

### 4.2 Option B: Sheaf Architecture from the Start
```
    [Stalk_A] --ρ_AB--> [Stalk_B]
         \              /
          \--ρ_AC--+--ρ_BC--/
                   |
              [Stalk_C]
```

**Pros:** Native compositionality; restriction maps enforce consistency  
**Cons:** Requires rethinking training (diffusion instead of backprop)

### 4.3 Option C: The User's Deep Question

> "If learning is geometric, why use neural nets to approximate geometry?"

This suggests a more radical approach:
- **Don't train restriction maps**—compute them analytically
- Use **persistent homology** to detect the blanket directly
- Replace backprop with **energy minimization** on the sheaf

---

## 5. What This Informs

### 5.1 For Continual Learning
The separate pathways approach is a **practical success** but a **theoretical dead end**:
- It works for isolation
- It fails for composition
- The "Functional Blanket" isn't actually shared

### 5.2 For the SGC Theory
The mapping to Sheaf Theory is promising:
- ε ↔ Sheaf Laplacian Energy is clean
- Grokking ↔ Cohomology Collapse makes geometric sense
- But our implementation doesn't create the right topological structure

### 5.3 For Hardware (Extropic Vision)
The diffusion-based inference in `SheafConnector` hints at thermodynamic computing:
- Settling to equilibrium instead of feedforward
- Energy minimization instead of gradient descent
- This is closer to the "native geometric learning" the user asked about

---

## 6. Recommended Next Steps

### Immediate (Fix the Measurement)
1. Add `compute_functional_defect()` for Task B's separate hidden space
2. Verify Task B actually groks geometrically (ε should drop)

### Medium-term (Test Composition)
3. Save the Phase 1A checkpoint (both tasks at 100%)
4. Test Sheaf Connector with proper frozen stalks
5. Compare feedforward vs. diffusion inference

### Long-term (Address the Deep Question)
6. Investigate Sheaf Neural Networks literature
7. Explore persistent homology for blanket detection
8. Consider whether backprop is the right paradigm at all

---

## 7. Summary

| Aspect | Status | Insight |
|--------|--------|---------|
| Geometric Sensing | ✅ Works | ε and χ_g detect grokking |
| Continual Learning | ✅ Works | But creates disjoint structure |
| Composition | ❌ Blocked | Disjoint union ≠ fiber product |
| ε for Task B | ❌ Broken | Measuring wrong representation |
| Sheaf Architecture | ✅ Implemented | Not yet tested with grokked stalks |

**Bottom Line:** We successfully isolated tasks but lost the geometric interaction needed for composition. The fix isn't hyperparameter tuning—it's architectural. Either:
1. Share structure and accept interference risk
2. Use Sheaf architecture with explicit restriction maps
3. Abandon neural approximation for native geometric methods
