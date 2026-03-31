# SGC Zero-Parameter Architecture

**Core Principle:** Every number in SGC is a measurement output. None are inputs.

---

## Derived Quantities (NOT Parameters)

### 1. Mode Count n
```
n = log(√N) / γ
```
- **γ** = spectral decay rate, computed from eigenspectrum
- **N** = data dimension
- Verified: CMB γ=0.9459 → n=4, matches empirical best

### 2. Phase Boundaries
- **Not** thresholds on trans_rate
- **Are** features of the c(trans_rate) curve
- Critical point = minimum of c
- Engine finds minimum by scanning, not by checking against 0.83

### 3. Grokking Detection
- **Not** a threshold on trans_rate
- **Is** detection of RG trajectory shape change:
  - Path to 2×2 fixed point collapses from many iterations to few
  - c diverges
  - This IS the phase transition signature

### 4. Domain Boundaries
- **Not** hardcoded ℓ_min, ℓ_max
- **Are** found by sliding-window defect gradient
- Boundary = where defect changes most rapidly
- Engine discovers from data

### 5. Inference Horizon
```
horizon = log(coupling_floor) / log(1 - δ)
```
- **δ** = measured lumpability defect
- **coupling_floor** = minimum coupling distinguishable from noise
- coupling_floor derived from bootstrap variance of c

---

## The Only Hardcoded Number

```python
SHUFFLE_GAP_SIGMA = 2.0
```

**Justification:** This is a statistical convention (≈ p < 0.05), not a physics parameter. It is:
- Universally defensible across domains
- Not domain-specific
- The equivalent of choosing a confidence level

---

## EGI Knowledge Store Architecture

For each relation, the store maintains:
1. **Current triplet corpus** — the observed (A, R, B) tuples
2. **Current RG trajectory** — the path through coupling space

The store does NOT maintain:
- Buckets with δ thresholds
- Hardcoded phase labels

### Phase Determination
Phase is **read from the trajectory**, not assigned by threshold:
- Trajectory shape reveals phase
- Convergence rate reveals stability
- c value reveals inference capacity

### Inference Horizon Computation
```python
def compute_horizon(delta: float, c_bootstrap_std: float) -> float:
    """
    Compute inference horizon from measured quantities.
    
    coupling_floor = minimum coupling distinguishable from noise
                   = derived from bootstrap variance of c
    """
    coupling_floor = 3.0 * c_bootstrap_std  # 3σ above noise
    if delta >= 1.0:
        return 0.0  # No inference possible
    return np.log(coupling_floor) / np.log(1.0 - delta)
```

---

## Anti-Pattern Detection

If you find yourself writing:
```python
if trans_rate > 0.83:  # WRONG
    phase = "ordered"
```

Stop. Ask: **What quantity does the data reveal that makes this threshold unnecessary?**

Correct pattern:
```python
# Scan c(trans_rate) curve, find minimum
c_values = [compute_c(tr) for tr in trans_rates]
critical_point = trans_rates[np.argmin(c_values)]
# Phase is determined by position relative to critical_point
```

---

## Why This Matters

**Classifiers** encode human assumptions as parameters.

**SGC** encodes one principle — minimize defect — and lets the data reveal its own structure.

This is what makes SGC a **physics discovery engine**, not a classifier.
