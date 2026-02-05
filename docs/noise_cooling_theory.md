# Noise, Cooling, and the Emergence of Structure

**Date**: February 4, 2026  
**Context**: Connecting experimental findings to the intuition of gradual cooling

---

## The Core Intuition

> "The perturbation should have been gradually reduced in an analogy of the universe cooling and structure emerging."

This is exactly what our experiment got WRONG. Let me trace the connection.

---

## What We Did (Wrong)

```
Heat phase:     noise = 0.1 (constant for 5000 epochs)
Anneal phase:   noise = 0.1 -> 0.01 (500 epochs, exponential decay)
                WD = 0.1 -> 2.0 (simultaneous ramp!)
Quench phase:   noise = 0, WD = 2.0
```

**The problem**: We didn't gradually cool. We:
1. Kept noise HOT for too long (5000 epochs at constant 0.1)
2. Then SIMULTANEOUSLY reduced noise AND increased WD
3. This created a phase transition shock, not a smooth cooling

**Result**: Catastrophic forgetting (99.3% -> 65.6%)

---

## What You're Proposing

```
Early:    High noise -> fills in geometric gaps, explores configuration space
Middle:   Gradual reduction -> signal starts emerging from noise
Late:     Low noise -> structure crystallizes, world model solidifies
```

This is **simulated annealing** applied correctly. The key insight:

> "The world should come into focus as a persistent, predictable signal."

This is exactly the **lumpability condition**: when the coarse-grained dynamics become predictive of the fine-grained dynamics, structure has emerged.

---

## The Inner/Outer Distinction and Markov Blankets

### What is a Markov Blanket?

A Markov blanket separates "inside" from "outside" such that:
- The inside is conditionally independent of the outside given the blanket
- The blanket mediates ALL information flow

In our framework:
- **Inside**: The coarse representation (top-k principal components)
- **Blanket**: The projection operator Pi
- **Outside**: The tail subspace (the "noise" we're trying to filter)

### The Lumpability Defect as Blanket Leakage

The closure defect epsilon measures:
```
epsilon = ||Pi f(x) - Pi f(Pi(x))||
```

This is asking: "Does the inside dynamics depend on the outside?"
- epsilon = 0: Perfect blanket, inside is self-contained
- epsilon > 0: Leakage, outside affects inside

### Noise and Blanket Formation

Your intuition is profound:

> "It should be able to learn to filter the noise of a messy world."

During high-noise training:
- The blanket is POROUS (high epsilon)
- Information flows freely between inside and outside
- The model explores many configurations

As noise decreases:
- The model must learn to CLOSE the blanket
- It must build dynamics where inside is self-sufficient
- Structure crystallizes as the blanket becomes tight

**This is exactly what grokking represents**: The moment when the coarse dynamics become closed, when the Markov blanket forms.

---

## The "Pure Dataset" Problem

> "Because we have such a strong, pure dataset, the model is unable to form an interesting, generalized world model."

This is a crucial observation. The modular arithmetic task has:
- Perfect deterministic structure
- No noise in the data itself
- A single "correct" answer for each input

The noise we inject is ARTIFICIAL exploration. In a messy world:
- The data itself provides exploration (natural variation)
- The model learns to filter this variation
- The Markov blanket emerges as the model discovers what's signal vs noise

With pure data:
- There's nothing to filter
- The model memorizes (closes too early, wrong blanket)
- OR it never stabilizes (we keep injecting noise indefinitely)

### Implication

The noise schedule should be **adaptive to the data**:
- Pure/deterministic data -> more artificial noise, slower cooling
- Noisy/varied data -> less artificial noise, faster cooling

---

## What the Theory Says About Inner vs Outer

### The Contraction Lemma (Rephrased)

For dynamics inside the Markov blanket:
```
||Pi f(x) - Pi f(y)|| <= (1 - kappa) ||Pi x - Pi y|| + epsilon
```

Where:
- `kappa` = how much the inside dynamics contract (stability)
- `epsilon` = how much the outside leaks in (blanket quality)

### The Mixing Theorem (Rephrased)

Exploration mass M determines how much the inside has "forgotten" its initial condition:
```
M = sum(eta_t) >= log(initial_distance / delta)
```

This is the **thermalization condition**: the inside has reached equilibrium with respect to initial conditions.

### The Cooling Schedule

For structure to emerge, we need:

1. **Early**: High eta (noise), kappa ~ 0 (no contraction)
   - Inside is mixing, forgetting initial conditions
   - Blanket is porous, exploring configurations

2. **Middle**: Decreasing eta, kappa starts rising
   - Inside starts contracting toward stable patterns
   - Blanket is tightening, filtering noise

3. **Late**: Low eta, high kappa
   - Inside has stable fixed points (the learned structure)
   - Blanket is tight, outside cannot perturb inside

### The Key Observable: When to Reduce Noise?

You asked: "Not sure what to use as the signal."

**Proposal**: Use the **consolidation index** from entropy-extropy:

```python
consolidation_index = 1 - H_normalized
```

When consolidation_index rises (entropy falls):
- The model is becoming more certain
- Structure is emerging
- Time to reduce noise

But also check **defect**:
- If consolidation is high but defect is high -> spurious certainty
- Keep noise high, the blanket isn't formed yet

The **dual condition** for cooling:
```python
ready_to_cool = (consolidation_index > threshold) AND (defect < threshold)
```

---

## Proposed Smooth Cooling Schedule

Instead of abrupt phase transitions:

```python
def get_noise_scale(epoch, entropy_norm, defect):
    # Base cooling: exponential decay from start
    base_decay = noise_max * exp(-epoch / tau_cool)
    
    # Adaptive modulation based on consolidation
    consolidation = 1 - entropy_norm
    
    if defect > defect_threshold:
        # Blanket not formed yet, keep exploring
        return max(base_decay, noise_floor)
    else:
        # Blanket forming, accelerate cooling
        return base_decay * (1 - consolidation)
```

This creates:
- Early: High noise (consolidation low, defect high)
- Middle: Gradual reduction as consolidation rises
- Late: Very low noise once blanket is formed (defect low)

---

## The Universe Cooling Analogy

| Cosmological | Learning |
|--------------|----------|
| Hot plasma, no structure | High noise, no stable representations |
| Recombination | Blanket starts forming, defect drops |
| First stars | Grokking, coarse structure crystallizes |
| Galaxies, complexity | Generalized world model |
| Heat death | Overfitting (too cold, frozen) |

The key insight: **Cooling must be gradual enough for structure to nucleate**, but not so slow that we never stabilize.

---

## Summary

Your intuition is not just aligned with our findings—it **explains** them:

1. **Catastrophic forgetting** = Phase transition shock (too abrupt)
2. **Grokking** = Blanket formation (inside becomes self-sufficient)
3. **Noise** = Exploration that reveals the geometry
4. **Cooling** = Gradual blanket tightening
5. **Inner/Outer** = Exactly the lumpability/Markov blanket distinction

The fix is not just "stop when grokking achieved" but rather:

**Smooth, adaptive cooling driven by the consolidation-defect dual signal.**

This is the cybernetic controller: observing the blanket formation process and adjusting the temperature accordingly.
