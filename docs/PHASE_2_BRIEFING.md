# Phase 2 Briefing: Compositional Generalization & Beyond Neural Networks

## For: New Assistant
## Date: February 6, 2026
## Status: Handoff from Phase 1A completion

---

## 1. What Has Been Accomplished

### Phase 1: Digital SGC Controller ✅
- **File**: `demos/sgc_training_monitor.py`
- **Result**: Successfully detected grokking via Functional Defect (ε) and Geometric Susceptibility (χ_g)
- **Key Finding**: In SGD (driven-dissipative systems), phase transitions are encoded in **geometry**, not energy fluctuations

### Phase 1A: Continual Learning ✅
- **File**: `demos/sgc_continual_learning.py`
- **Result**: Task A (addition) and Task B (multiplication) both grok to 100% without catastrophic forgetting
- **Architecture**: Completely separate pathways for each task

```
Task A: embed_a/b → shared_fc1 → shared_fc2 → head_addition     [FROZEN]
Task B: mul_embed_a/b → mul_fc1 → mul_fc2 → head_multiplication [TRAINED]
```

### Phase 2: Compositional Generalization ❌ (Incomplete)
- **File**: `demos/sgc_compositional_learning.py`
- **Goal**: Test if frozen Task A and Task B representations can be composed: f(x,y,z) = (x+y)*z mod p
- **Status**: Grokking hyperparameters are sensitive; experiments with p=17 and p=59 failed to grok
- **Core Issue**: The "separate pathways" architecture that enabled Phase 1A success doesn't support true representational composition

---

## 2. The Scientific Gap Identified

### The "Separate Pathways" Problem
The Phase 1A success demonstrates that freezing works, but it creates **two disjoint models in one container**:

| Aspect | Phase 1A Result | True Compositionality |
|--------|----------------|----------------------|
| Shared representation | ❌ None | ✅ Required |
| Cross-task transfer | ❌ None | ✅ Required |
| Composition | ❌ Impossible | ✅ The goal |

### The Fundamental Question
> If the "Functional Blanket" is a real geometric/topological structure, can it be:
> 1. **Composed** (blanket A + blanket B → blanket C)?
> 2. **Shared** (blanket learned on A useful for B)?
> 3. **Transferred** (blanket from task → blanket for related task)?

---

## 3. Key Metrics and Equations

| Symbol | Name | Definition | Implementation |
|--------|------|------------|----------------|
| ε | Functional Defect | Within-class variance / Total variance | `compute_functional_defect()` |
| χ_g | Geometric Susceptibility | Var(ε) over sliding window | `GeometricSusceptibility` class |
| T_eff | Effective Temperature | weight_decay / learning_rate | Controller parameter |

**Grokking Detection**: ε < 0.15 AND test_acc > 99%

---

## 4. Proven Hyperparameters (Phase 1A)

```python
p = 97              # Prime modulus
lr = 1e-3           # Learning rate
weight_decay = 0.5  # Regularization
epochs = 3000       # Per phase
train_frac = 0.3    # 30% train, 70% test
embed_dim = 128
hidden_dim = 256
```

---

## 5. User's Deep Questions for Research

The user has posed fundamental questions that go beyond the current neural network paradigm:

### Question 1: Why Neural Networks for Geometry?
> "If we know that learning is stored geometrically or topologically, why are we using neural nets to encode geometry and/or topology?"

**Research Directions**:
- Topological Data Analysis (TDA) for learning
- Discrete Differential Geometry approaches
- Sheaf neural networks
- Geometric deep learning (Bronstein et al.)
- Hyperbolic embeddings

### Question 2: Native Topological Learning
> "Are there techniques that allow us to be more native about the learning process?"

**Research Directions**:
- Persistent homology as a learning signal
- Manifold learning without neural approximation
- Algebraic topology for representation learning
- Category-theoretic approaches (functorial learning)

### Question 3: Real-Time Experiential Learning
> "Could make this real time and experiential like a living creature experiences its environment?"

**Research Directions**:
- Thermodynamic computing (Extropic, Normal Computing)
- Neuromorphic architectures
- Reservoir computing
- Predictive coding networks
- Free energy principle implementations
- Continuous-time neural networks (Neural ODEs)

---

## 6. Relevant Formal Theory (from Lean codebase)

The repository contains formally verified theorems that may guide the search:

### From `src/SGC/Bridge/Quantum.lean`:
- **Knill-Laflamme forces zero defect**: Classical stochastic systems cannot do quantum error correction
- **Implication**: Classical emergence requires *different* stability conditions than quantum coherence

### From `src/SGC/Grokking.lean`:
- Grokking formalized as a phase transition in representation space
- Functional defect as order parameter

### From `src/SGC/ContinualLearning/`:
- Formal model of "memory as cold zones"
- Adiabatic protection theorems

---

## 7. Files to Review

| File | Purpose |
|------|---------|
| `demos/sgc_training_monitor.py` | Working SGC controller |
| `demos/sgc_continual_learning.py` | Working freeze-thaw (Phase 1A) |
| `demos/sgc_compositional_learning.py` | Incomplete Phase 2 attempt |
| `demos/lifshitz_transition_experiment.py` | Original grokking metrics |
| `docs/AGI_ROADMAP.md` | Full development roadmap |
| `reports/THRML_002_BRIDGE_VALIDATION.md` | Geometry vs Energy findings |
| `src/SGC/Bridge/Quantum.lean` | Formal quantum bridge |

---

## 8. Recommended Next Steps

1. **Research** the user's questions about native geometric/topological learning
2. **Investigate** whether the formal Lean theorems suggest alternative architectures
3. **Consider** whether the "Functional Blanket" could be represented directly (not via neural network approximation)
4. **Explore** real-time/continuous learning paradigms that don't require batch training

---

## 9. The Ultimate Vision

The user's questions point toward a deeper goal:

> **If intelligence is geometric, shouldn't the substrate BE geometric?**

The current work uses neural networks as a *simulation* of geometric learning. The user is asking whether we can make the geometry *native* to the computation—as it is in thermodynamic hardware or biological neural tissue.

This connects to the Extropic hardware vision: physical systems that naturally compute in the geometry of the problem, rather than approximating it through gradient descent.

---

*End of Briefing*
