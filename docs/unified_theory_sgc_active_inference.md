# Unified Theory: SGC, Active Inference, and Continual Learning

**Date**: February 4, 2026  
**Status**: Crystallizing synthesis from experimental findings

---

## The Core Unification

Three frameworks converge on the same structure:

| Framework | Inside | Blanket | Outside | Goal |
|-----------|--------|---------|---------|------|
| **SGC** | Coarse representation Π(z) | Projection Π | Tail (I-Π)(z) | Minimize defect ε |
| **Active Inference** | Internal states μ | Markov blanket b | External states η | Minimize free energy F |
| **Continual Learning** | Consolidated knowledge | Stability mechanism | New information | Balance stability/plasticity |

**The key insight**: All three are solving the same problem—**how to maintain coherent internal structure while interfacing with a noisy, changing world**.

---

## 1. SGC as Active Inference

### The Defect IS Free Energy

In SGC, the closure defect measures:
```
ε = ||Π f(x) - Π f(Π(x))||
```

In Active Inference, free energy is:
```
F = D_KL(q(μ) || p(μ|o)) + ... ≈ prediction error + complexity
```

**Connection**: Both measure "surprise" at the boundary:
- ε = how much the outside perturbs the inside unexpectedly
- F = how much observations deviate from internal predictions

**When ε → 0**: The inside is self-consistent, the blanket is closed.
**When F → 0**: The generative model matches observations perfectly.

### The Projection IS the Generative Model

The coarse projector Π:
- Maps fine states to coarse states (encoding)
- Has a lift operator that maps back (decoding/prediction)
- Is idempotent: Π² = Π (consistent encoding)

This IS a generative model:
- Encode observations into latent state
- Generate predictions from latent state
- Update latent state to minimize prediction error

### Learning IS Blanket Formation

Training drives ε → 0, which means:
1. The inside dynamics become self-sufficient
2. The outside cannot perturb the inside (blanket is tight)
3. The model has learned "what to ignore"

This is exactly what Active Inference says:
- Organisms minimize free energy by either:
  - Updating beliefs (perception)
  - Acting to change observations (action)
  - Building blankets that filter irrelevant information (structure learning)

---

## 2. ISR as Iterative Belief Updating

The ISR model does exactly this:

```python
for t in range(T):
    y_t, z_t, defect_t = model.forward_step(z_t, x_enc, return_defect=True)
```

Each step:
1. **Perception**: Update internal state z based on observations x
2. **Defect tracking**: Measure how much the update "leaks" outside the blanket
3. **Convergence**: When defect → 0, beliefs are stable

### The Partition IS the Blanket Structure

ISR uses partition-based projectors:
```
Row partition: cells in same row → same equivalence class
Column partition: cells in same column → same equivalence class
Box partition: cells in same box → same equivalence class
```

This defines the blanket structure:
- Inside: the constraint-consistent subspace (valid Sudoku patterns)
- Outside: the constraint-violating subspace (invalid patterns)

Learning succeeds when the dynamics stay inside the constraint subspace.

---

## 3. Continual Learning as Blanket Preservation

### The Catastrophic Forgetting Problem

When learning new tasks, old knowledge is destroyed. In our terms:
- Old knowledge = inside structure
- New task = perturbation from outside
- Forgetting = blanket rupture (outside invades inside)

### Our Experimental Observation

Phase-6.1 showed exactly this:
```
Epoch 5247: Grokking achieved (99.3% test accuracy)
Epoch 5500: Quench with aggressive WD
Epoch 6000: Accuracy dropped to 66% (FORGOTTEN!)
```

The aggressive quench ruptured the blanket that had just formed.

### The Solution: Gradual Cooling with Blanket Monitoring

Instead of fixed schedules, monitor blanket quality:
```python
if blanket_tight(defect < threshold):
    reduce_noise()  # Consolidate
    maintain_wd()   # Don't over-regularize
else:
    keep_exploring()  # Blanket not formed yet
```

This is **active inference applied to the learning process itself**:
- The meta-learner monitors its own blanket quality
- It adjusts exploration/consolidation to minimize meta-free-energy
- The goal is stable knowledge that resists perturbation

---

## 4. The Inner/Outer World Dynamics

### What Our Theory Says

The contraction lemma:
```
||Π f(x) - Π f(y)|| ≤ (1 - κ) ||Π x - Π y|| + ε
```

Decomposed:
- **Left side**: How much the inside changes
- **(1 - κ) term**: Contraction (stable dynamics pull toward fixed points)
- **ε term**: Leakage (outside perturbing inside)

### The Balance

| Regime | κ | ε | Behavior |
|--------|---|---|----------|
| Exploration | ~0 | High | No stable structure, everything mixes |
| Crystallization | Rising | Falling | Structure emerges, blanket forms |
| Stable | High | Low | Fixed points, blanket tight |
| Brittle | Very high | Very low | Overfitted, no flexibility |

### The Goldilocks Zone

We want:
- **κ high enough** for stable attractors (learned patterns)
- **ε low enough** for noise rejection (blanket works)
- **But not too extreme** or we lose plasticity

This is the **stability-plasticity dilemma** reframed as **blanket tightness tuning**.

---

## 5. What Can We Solve Now?

### Solvable Problem 1: The Cooling Schedule

**Old approach**: Fixed phases (heat → anneal → quench)
**New approach**: Adaptive cooling driven by (ε, entropy, κ)

```python
def get_temperature(state):
    if state.defect > 0.2:
        return T_high  # Blanket leaky, keep exploring
    elif state.defect < 0.1 and state.consolidation > 0.5:
        return T_low   # Blanket forming, accelerate cooling
    elif state.spurious_certainty:
        return T_high  # Confident but wrong, reheat
    else:
        return smooth_decay(state.T_current)
```

### Solvable Problem 2: The Grokking Criterion

**Old approach**: Check test accuracy (external measure)
**New approach**: Check blanket closure (internal measure)

```python
def grokking_detected(state):
    # Grokking = blanket just closed
    return (
        state.defect < defect_threshold and
        state.defect_velocity < 0 and  # Still improving
        state.consolidation > 0.6       # Confident
    )
```

This is **intrinsic** — we don't need ground truth labels.

### Solvable Problem 3: Continual Learning Protection

**Old approach**: Replay buffers, EWC, etc. (external memory)
**New approach**: Monitor blanket quality during new learning

```python
def safe_to_learn_new(state, old_defect):
    # Only allow new learning if old blanket still intact
    current_defect = measure_defect_on_old_task()
    if current_defect > old_defect * 1.5:
        return False  # Old blanket rupturing, stop!
    return True
```

---

## 6. The Meta-Instantiation

You observed: "This is a cool meta instantiation of the theory itself."

Indeed:
- **Our exploration** = reading papers, running experiments, generating noise
- **Our structure emergence** = insights crystallizing into theory
- **Our blanket** = the core concepts that filter irrelevant details
- **This document** = a snapshot of the blanket (what we've decided to keep)

The theory is self-describing: a system that monitors its own coherence and adjusts its exploration accordingly.

---

## 7. Concrete Next Steps

### Experiment 1: Smooth Cooling Validation

Run grokking with smooth cooling controller instead of fixed phases.

**Prediction**: No catastrophic forgetting, grokking preserved.

### Experiment 2: Intrinsic Grokking Detection

Monitor defect during training. Compare:
- Epoch when defect crosses threshold
- Epoch when test accuracy crosses threshold

**Prediction**: Defect crossing predicts grokking by 50-200 epochs.

### Experiment 3: Continual Learning with Blanket Monitoring

Train on Task A until blanket forms.
Then train on Task B while monitoring Task A blanket.
If Task A blanket ruptures, reduce Task B learning rate.

**Prediction**: Less forgetting than fixed regularization.

---

## 8. The Unified Picture

```
                    OUTSIDE (messy world, noise, new data)
                              │
                              ▼
                    ┌─────────────────┐
                    │  Markov Blanket │ ← Defect ε measures quality
                    │    (Π operator) │
                    └────────┬────────┘
                             │
                             ▼
                    ┌─────────────────┐
                    │     INSIDE      │ ← Contraction κ measures stability
                    │ (coarse states) │
                    │                 │
                    │  ┌───────────┐  │
                    │  │Fixed      │  │ ← Learned structure
                    │  │Points     │  │   (grokked solution)
                    │  └───────────┘  │
                    └─────────────────┘

LEARNING DYNAMICS:
- Heat (exploration): ε high, κ ~ 0, no fixed points
- Cooling (crystallization): ε falling, κ rising, fixed points emerge
- Frozen (stable): ε low, κ high, structure preserved

CONTROL LOOP:
- Observe (ε, κ, entropy)
- Decide: explore more or consolidate?
- Act: adjust noise temperature
- Result: gradual blanket formation → grokking → stable knowledge
```

---

## 9. Why This Matters

This isn't just about grokking on modular arithmetic. It's about:

1. **Principled hyperparameter-free learning**: The system self-regulates based on internal observables.

2. **Continual learning without catastrophic forgetting**: Monitor blanket quality, protect old knowledge.

3. **Intrinsic success criteria**: Know when learning has succeeded without external labels.

4. **A bridge to biological plausibility**: Active inference is a theory of brain function. SGC provides the mathematical scaffolding.

5. **Meta-learning**: A system that monitors and regulates its own learning process.

---

## 10. Open Questions

1. **Is κ measurable in practice?** We saw κ_contract ~ 0 during heat. Can we measure it better?

2. **What's the right defect?** Weight tail energy ≠ closure defect. Need to implement proper closure defect.

3. **Does this scale?** We're on 54K parameter networks. What about billions?

4. **Can the blanket be learned?** We hand-specify Π. Can the network discover its own coarse structure?

5. **What about action?** Active inference includes action. How does this map to learning?

These are the research agenda for the next phase.
