# Thermodynamic Grokking & The Lifshitz Signature

**Experiment ID**: THRML-001  
**Date**: February 6, 2026  
**Status**: Active Development  
**Principal Investigator**: SGC Research Team

---

## Executive Summary

This experiment tests whether "grokking" (sudden generalization in neural networks) is a **literal second-order phase transition** when implemented on thermodynamic hardware. We predict a measurable signature—a peak in specific heat—that aligns with the collapse of functional defect.

---

## 1. Core Hypothesis

### The Lifshitz Signature

**Claim**: Grokking on thermodynamic hardware manifests as a second-order phase transition with characteristic thermodynamic signatures.

**Observable**: Specific Heat
$$C_v = \frac{\text{Var}(E)}{T^2} = \beta^2 \cdot \text{Var}(E)$$

**Prediction**: The peak in $C_v$ will align perfectly with:
1. Collapse of Functional Defect ($\epsilon \to 0$)
2. Ridge Ratio crossing threshold ($R > 1$)
3. Van Hove singularity in density of states

**Physical Meaning**: The system maximizes energy fluctuations exactly when it "snaps" into the correct algebraic manifold. This is the thermodynamic signature of grokking.

---

## 2. Theoretical Foundation

### 2.1 SGC Theory Recap

From our prior work:
- **Functional Defect** $\epsilon$: Within-class variance / total variance
- **Ridge Ratio** $R$: Between-class energy / within-class energy
- **Grokking**: Phase transition where $\epsilon$ collapses and $R$ peaks

### 2.2 Statistical Mechanics Mapping

| SGC Concept | Stat Mech Equivalent |
|-------------|---------------------|
| Functional Defect $\epsilon$ | Order parameter |
| Ridge Ratio $R$ | Correlation length |
| Temperature $D$ | Inverse $\beta$ |
| Grokking epoch | Critical temperature $T_c$ |

### 2.3 Phase Transition Classification

We expect a **second-order (continuous) phase transition** because:
1. Order parameter ($\epsilon$) goes continuously to zero
2. Susceptibility (related to $R$) diverges
3. Specific heat shows a peak (not a discontinuity)

This is analogous to the **Ising model** at the Curie temperature.

---

## 3. Experimental Design

### 3.1 Task: Modular Addition

**Problem**: Learn the function $f(a, b) = (a + b) \mod p$

**Parameters**:
- Prime $p = 7$ (small for initial experiments)
- Dataset: All $p^2 = 49$ input pairs
- Split: 70% train, 30% test (following original grokking paper)

### 3.2 Spin Encoding

**Thermometer Code** (recommended):
```
Integer k in [0, p-1] --> p-1 spins: [+1]*k + [-1]*(p-1-k)

Example (p=7):
  0 --> [-1, -1, -1, -1, -1, -1]
  3 --> [+1, +1, +1, -1, -1, -1]
  6 --> [+1, +1, +1, +1, +1, +1]
```

**Why thermometer code**:
1. Natural ridge structure between adjacent values
2. Hamming distance ~ numerical distance
3. Local spin flips = small numerical changes

**Total spins per sample**: 3 * (p-1) = 18 spins for p=7

### 3.3 Energy Function

The IsingEBM energy encodes the problem:

$$E(s_a, s_b, s_c) = E_{correct}(s_a, s_b, s_c) + E_{structure}(s)$$

Where:
- $E_{correct}$: Low energy if $(a + b) \mod p = c$
- $E_{structure}$: Local biases ensuring valid thermometer codes

**Implementation**:
```python
def compute_energy(s_a, s_b, s_c, p):
    a = decode_thermometer(s_a)
    b = decode_thermometer(s_b)
    c = decode_thermometer(s_c)
    
    correct = (a + b) % p
    error = abs(c - correct)  # Or use mod distance
    
    E_correct = error * J_error  # Penalize wrong answers
    E_structure = structure_penalty(s_a, s_b, s_c)
    
    return E_correct + E_structure
```

### 3.4 THRML Implementation

```python
from thrml import SpinNode, Block, SamplingSchedule, sample_states
from thrml.models import IsingEBM, IsingSamplingProgram, hinton_init

# Create spin nodes for a, b, c
n_spins_per_var = p - 1
nodes_a = [SpinNode() for _ in range(n_spins_per_var)]
nodes_b = [SpinNode() for _ in range(n_spins_per_var)]
nodes_c = [SpinNode() for _ in range(n_spins_per_var)]
all_nodes = nodes_a + nodes_b + nodes_c

# Define energy via weights and biases
# (Detailed construction in implementation)
```

### 3.5 Control Protocol

Using the `BangBangController` from `sgc_controller.py`:

| Phase | Condition | Action |
|-------|-----------|--------|
| **EXPLORE** | $\epsilon > 0.5$ | $\beta = 0.5$ (high temp) |
| **TRANSITION** | $R > 1$ or $\epsilon < 0.5$ | $\beta = 1.0$ (critical) |
| **GROKKED** | $\epsilon < 0.15$ and $R > 5$ | $\beta = 3.0$ (low temp) |

### 3.6 Measurements

At each temperature step, measure:

1. **Energy Statistics**:
   - Mean energy $\langle E \rangle$
   - Variance $\text{Var}(E)$
   - Specific heat $C_v = \beta^2 \cdot \text{Var}(E)$

2. **SGC Metrics**:
   - Functional defect $\epsilon$
   - Ridge ratio $R$
   - (Optional) Van Hove density at zero energy

3. **Accuracy**:
   - Fraction of samples with correct $c = (a+b) \mod p$

4. **Critical Exponents** (advanced):
   - Binder cumulant $U_4 = 1 - \langle E^4 \rangle / (3 \langle E^2 \rangle^2)$
   - Correlation length from $R$

---

## 4. Predictions

### 4.1 Main Prediction: Cv Peak Alignment

```
            epsilon (functional defect)
            |
         1.0|----\
            |     \
         0.5|      \____
            |           \
         0.0|____________\___________
            |                        beta
            
            Cv (specific heat)
            |
            |        /\
            |       /  \
            |      /    \
            |_____/      \___________
            |                        beta
                   ^
                   |
            Critical beta_c
            (Cv peak aligns with epsilon collapse)
```

### 4.2 Quantitative Predictions

| Observable | Pre-Grok | At Transition | Post-Grok |
|------------|----------|---------------|-----------|
| $\epsilon$ | > 0.5 | ~ 0.2-0.3 | < 0.15 |
| $R$ | < 1 | ~ 1-2 | > 5 |
| $C_v$ | Low | **Peak** | Low |
| Accuracy | Random (1/p) | Improving | ~100% |

### 4.3 Null Hypothesis

If grokking is NOT a phase transition, we expect:
- No Cv peak (or peak at wrong location)
- No correlation between Cv and epsilon
- Gradual accuracy improvement without thermodynamic signature

---

## 5. Hardware Implications

### 5.1 The "Flat Ridge" Test

This experiment directly tests the flat ridge hardware hypothesis:

**Question**: Are continuous Riemannian manifolds necessary for grokking, or do discrete spins suffice?

**If successful**:
- Discrete bistable elements (spins/memristors) ARE sufficient
- No need for exotic curved-space computation
- Path to neuromorphic/thermodynamic AGI is validated

**If failed**:
- May need continuous variables
- Or need different encoding
- Revise hardware requirements

### 5.2 Z1 Chip Relevance

The Extropic Z1 chip implements exactly this architecture:
- Binary spin variables
- Sparse local connectivity
- Hardware Gibbs sampling
- Programmable temperature

A successful experiment here translates directly to Z1 implementation.

---

## 6. Implementation Plan

### Phase 1: Software Prototype (Current)

1. Implement spin encoding for modular addition
2. Create THRML-based energy function
3. Integrate BangBangController
4. Implement Cv measurement
5. Run experiment and collect data

### Phase 2: Analysis

1. Plot Cv vs beta
2. Plot epsilon vs beta
3. Check alignment of peaks
4. Compute critical exponents (if transition is clean)

### Phase 3: Validation

1. Vary p (try p = 5, 7, 11, 13)
2. Try multiplication task
3. Compare with PyTorch grokking (same task)
4. Check finite-size scaling

### Phase 4: Hardware Proposal

1. Document results for Extropic grant application
2. Specify Z1 requirements
3. Request early access

---

## 7. Code Organization

```
demos/
  thermodynamic_grokking.py     # Main experiment
  sgc_controller.py             # Controller (exists)
  sgc_thrml_demo.py             # THRML basics (exists)

docs/
  SGC_THRML_EXPERIMENT_PROPOSAL.md  # This document
  SGC_THRML_INTEGRATION.md          # Integration analysis (exists)
  SGC_CONTROL_ARCHITECTURE.md       # Controller spec (exists)

logs/
  thrml_grokking/
    run_YYYYMMDD_HHMMSS/
      metrics.json
      plots/
```

---

## 8. Success Criteria

### Minimum Success

- [ ] Cv peak observed at some beta_c
- [ ] epsilon decreases as beta increases past beta_c
- [ ] Accuracy reaches >90% at high beta

### Full Success

- [ ] Cv peak aligns with epsilon inflection point
- [ ] Ridge ratio R crosses 1 near beta_c
- [ ] Clear phase transition behavior (not gradual)
- [ ] Reproducible across random seeds

### Bonus

- [ ] Compute critical exponents
- [ ] Show universality (same exponents for different p)
- [ ] Demonstrate on multiplication task

---

## 9. Timeline

| Week | Milestone |
|------|-----------|
| 1 | Implement spin encoding and energy function |
| 1 | Integrate controller with THRML |
| 2 | Run initial experiments (p=7) |
| 2 | Analyze Cv vs epsilon alignment |
| 3 | Validate across different p values |
| 3 | Document results |
| 4 | Prepare Extropic grant proposal |

---

## 10. References

1. **Power et al. (2022)**: "Grokking: Generalization Beyond Overfitting on Small Algorithmic Datasets"
2. **Nanda et al. (2023)**: "Progress measures for grokking via mechanistic interpretability"
3. **Extropic (2025)**: "An efficient probabilistic hardware architecture for diffusion-like models" (arXiv:2510.23972)
4. **SGC Theory**: `docs/SGC_CANONICAL_GROKKING_THEORY.md`
5. **SGC Control**: `docs/SGC_CONTROL_ARCHITECTURE.md`

---

## Appendix A: Detailed Spin Encoding

### Thermometer Code

```python
def encode_thermometer(value: int, p: int) -> List[int]:
    """Encode integer [0, p-1] as thermometer code."""
    return [+1 if i < value else -1 for i in range(p - 1)]

def decode_thermometer(spins: List[int]) -> int:
    """Decode thermometer code to integer."""
    # Count +1 spins from the left
    count = 0
    for s in spins:
        if s == +1:
            count += 1
        else:
            break
    return count
```

### Structure Penalty

To ensure valid thermometer codes (no [-1, +1] patterns):

```python
def structure_penalty(spins: List[int], J_struct: float = 1.0) -> float:
    """Penalize invalid thermometer patterns."""
    penalty = 0.0
    for i in range(len(spins) - 1):
        if spins[i] == -1 and spins[i+1] == +1:
            penalty += J_struct
    return penalty
```

---

## Appendix B: Specific Heat Calculation

```python
def compute_specific_heat(energies: np.ndarray, beta: float) -> float:
    """
    Compute specific heat from energy samples.
    
    Cv = beta^2 * Var(E)
    
    In canonical ensemble: Cv = (1/kT^2) * Var(E)
    With beta = 1/kT, this gives Cv = beta^2 * Var(E)
    """
    return beta**2 * np.var(energies)

def compute_binder_cumulant(energies: np.ndarray) -> float:
    """
    Compute Binder cumulant for phase transition detection.
    
    U4 = 1 - <E^4> / (3 * <E^2>^2)
    
    Crosses universal value at critical point.
    """
    E2 = np.mean(energies**2)
    E4 = np.mean(energies**4)
    return 1.0 - E4 / (3.0 * E2**2 + 1e-10)
```

---

*"The thermodynamic computer doesn't just simulate intelligence—it IS intelligence, crystallizing from thermal noise."*
