# Math Analysis: Theory vs Practice Gaps

**Date**: February 4, 2026  
**Experiment**: Phase-6.1 with hybrid noise, effective_contract trigger

## Summary of Findings

The Phase-6.1 experiment achieved grokking at epoch 5247 (99.3% test accuracy) but then **catastrophically forgot** during quench phase (dropping to ~69%).

This reveals critical gaps between theory and implementation.

---

## Issue 1: kappa_contract = 0 During Heat Phase

### Observation
```
Heat phase (epochs 1-5000): kappa_contract ~ 0.000-0.002
Anneal phase (epochs 5000-5500): kappa_contract ~ 0.000-0.072  
Quench phase (epoch 5500+): kappa_contract = 0.393 (finally!)
```

### Theoretical Expectation
The Contraction Lemma says: `d_{t+1} <= (1 - kappa*eta) * d_t`

We expected to measure kappa from defect contraction.

### Why It's Zero During Heat

**Insight from diagnostics**: Under noise injection, defect **oscillates** rather than monotonically contracting.

```
Step 1: ratio = 1.0124 (expanding)
Step 2: ratio = 0.9965 (contracting)
Step 3: ratio = 1.0023 (expanding)
...
```

The block estimator `kappa = -log(d_{k+1}/d_k) / Eta` returns 0 when ratio >= 1.

**Root cause**: The Contraction Lemma assumes NO DISTURBANCE. During heat, we're actively injecting noise, which prevents monotonic contraction.

### Resolution
kappa_contract should only be measured/used during consolidation (anneal/quench), not during exploration (heat). The theory is correct; we were applying it to the wrong phase.

---

## Issue 2: Two Different Defects

### The Theory's Defect
The closure defect measures: `||Pi f(x) - Pi f Pi(x)||`

This is how well the coarse projection commutes with the dynamics.

### Our Implemented Defect  
We measure **weight tail energy**: `sqrt(sum(S[k:]^2) / sum(S^2))`

This measures how much of the weight matrix is in low-rank structure.

### Are They Related?
**Partially.** A low-rank weight matrix tends to produce coarse-grained dynamics, but:
- Weight tail energy can be low while closure defect is high (structured but wrong structure)
- Closure defect can be low while weight tail energy is moderate (correct structure distributed)

### Resolution
We should measure closure defect directly by sampling pairs (x, y) and computing:
```
defect = E[||Pi f(x) - Pi f(Pi(x))||] / E[||f(x)||]
```

---

## Issue 3: Catastrophic Forgetting During Quench

### Timeline
```
Epoch 5200: test = 98.8%
Epoch 5247: GROKKING (test >= 95%)
Epoch 5300: test = 99.3%  <- Peak
Epoch 5400: test = 96.3%  <- Starting to forget
Epoch 5500: test = 83.8%  <- Quench starts, WD=2.0
Epoch 5800: test = 69.1%  <- Catastrophic
```

### Root Cause
The anneal phase continued injecting noise (noise_floor = 0.01) even AFTER grokking was achieved at epoch 5247. Combined with aggressive WD ramping, this destabilized the solution.

### The Controller's Failure
The controller doesn't check if grokking has been achieved. It blindly follows the schedule:
1. Heat until M >= 500 (FORCE_MAX)
2. Anneal for 500 epochs with noise_floor
3. Quench with WD = 2.0

There's no feedback loop to say "we've achieved the goal, stop perturbing."

### Resolution: State-Driven Control
This is EXACTLY what the entropy-extropy dual controller should fix:
- When consolidation_index is high AND defect is low AND accuracy is high → STOP exploration
- The current controller uses fixed schedules, not observable-driven decisions

---

## Issue 4: The 1% Mixing Efficiency

### Theory
M_explore = log(1/delta) = log(10) = 2.3

### Practice  
Grokking required M_nominal = 500 (actually used ~511 at grokking)

### Efficiency
2.3 / 511 = 0.45% (even worse than previously estimated 1%)

### Why So Inefficient?

1. **kappa_tail ~ 0.5**: Only 50% of noise reaches tail subspace
   - M_effective_tail = 251 (still ~100x more than theory)

2. **Weight defect != Closure defect**: We're measuring the wrong thing

3. **Noise-gradient interference**: Gradient descent partially undoes noise

4. **The bound is for a DIFFERENT setting**: The mixing theorem is about convergence to equilibrium. Grokking is about finding a specific solution.

### Resolution
The exploration mass theorem may need to be reframed. Instead of "how much noise to mix," we should ask "how much noise to escape local minima and reach the grokking basin."

---

## Issue 5: kappa_tail is Stable but kappa_contract is Phase-Dependent

### Observation
```
kappa_tail (average) = 0.5026 (stable across all phases)
kappa_contract:
  - Heat: ~0.002
  - Anneal: ~0.02
  - Quench: ~0.39
```

### Interpretation
- **kappa_tail** is a GEOMETRIC property of the weight matrix (fixed by architecture)
- **kappa_contract** is a DYNAMIC property that depends on training phase

### Implication
M_effective = kappa * M_nominal should use:
- kappa_tail during heat (exploration efficiency)
- kappa_contract during quench (consolidation efficiency)

The controller should track BOTH and use them for different purposes.

---

## Proposed Fixes

### Fix 1: Observable-Driven Phase Transitions
Instead of fixed schedules:
```python
if entropy_normalized < 0.3 and test_accuracy > 0.95:
    phase = 'consolidate'  # Stop exploration immediately
```

### Fix 2: Measure Closure Defect Directly
```python
def compute_closure_defect(model, x):
    h = model.get_hidden(x)       # Full hidden representation
    h_proj = project_to_coarse(h)  # Project to top-k principal components
    h_lifted = lift_from_coarse(h_proj)  # Lift back to full space
    
    # How different is f(x) from f(project(x))?
    out_full = model.output_head(h)
    out_proj = model.output_head(h_lifted)
    return ||out_full - out_proj|| / ||out_full||
```

### Fix 3: Grokking-Aware Controller
```python
if grokking_achieved and current_phase == 'anneal':
    # Immediately stop noise, keep WD moderate
    noise_scale = 0.0
    weight_decay = 1.0  # Not too aggressive
```

### Fix 4: Separate Exploration and Consolidation Observables
- Use **kappa_tail** for exploration decisions (noise allocation)
- Use **kappa_contract** for consolidation decisions (WD ramping)
- Use **test accuracy** as ground truth for phase transitions

---

## Summary

| Issue | Symptom | Root Cause | Fix |
|-------|---------|------------|-----|
| kappa_contract = 0 | Not useful during heat | Noise prevents monotonic contraction | Use only during consolidation |
| Wrong defect | Tail energy != closure | Measuring weight structure, not dynamics | Implement closure defect |
| Catastrophic forgetting | 99% -> 69% | Fixed schedule ignores grokking | Observable-driven control |
| 1% efficiency | M = 500 vs M = 2.3 | Wrong setting for theorem | Reframe as basin escape |
| kappa phase-dependence | tail stable, contract varies | Different physical meanings | Use appropriately per phase |

---

## Next Steps

1. **Implement closure defect** measurement
2. **Add grokking-aware early stopping** in controller
3. **Re-run Phase-6.2** with tuned dual controller
4. **Compare** grokking epochs: fixed schedule vs state-driven
5. **Update theory** to distinguish exploration (kappa_tail) from consolidation (kappa_contract)
