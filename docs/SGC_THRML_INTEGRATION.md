# SGC-THRML Integration Analysis

**Date**: February 6, 2026  
**Version**: 1.0  
**Status**: Research Resource  
**Purpose**: Map SGC theory to Extropic's THRML library for thermodynamic AI development

---

## Executive Summary

**THRML** (Thermodynamic HypergRaphical Model Library) from Extropic is a JAX-based library for probabilistic graphical models designed to prototype algorithms for their upcoming thermodynamic hardware (TSUs - Thermodynamic Sampling Units).

**Key Finding**: THRML's architecture is **remarkably aligned** with SGC theory. The mapping is almost 1:1:

| SGC Concept | THRML Equivalent |
|-------------|------------------|
| Flat Torus with Ridges | Sparse PGM with energy barriers |
| Kramers Escape (temperature D) | Gibbs sampling with β (inverse temperature) |
| Functional Blanket (valley) | Basin of attraction / energy minimum |
| Ridge Ratio | Energy barrier between blocks |
| Adiabatic Invariant | Clamped blocks (frozen variables) |

---

## Part I: THRML Overview

### 1.1 What is THRML?

- **Library**: JAX-based, GPU-accelerated
- **Purpose**: Build and sample probabilistic graphical models (PGMs)
- **Focus**: Block Gibbs sampling, energy-based models (EBMs)
- **Hardware Target**: Extropic's Z1 chip (thermodynamic sampling unit)

### 1.2 Core Components

```python
from thrml import SpinNode, Block, SamplingSchedule, sample_states
from thrml.models import IsingEBM, IsingSamplingProgram, hinton_init
```

**Key abstractions**:
- **Node**: Random variable (SpinNode = binary ±1)
- **Block**: Group of nodes updated together
- **IsingEBM**: Energy function E = -½ Σ wᵢⱼ sᵢsⱼ - Σ bᵢsᵢ
- **SamplingSchedule**: Controls warmup, samples, steps per sample
- **sample_states()**: Run Gibbs sampling

### 1.3 The Ising Model Connection

THRML's core primitive is the **Boltzmann machine** (Ising model):

```
E(x) = -½ xᵀWx - bᵀx

P(x) ∝ exp(-βE(x))
```

Where:
- **x** ∈ {-1, +1}ⁿ: binary spin variables
- **W**: symmetric weight matrix (interactions)
- **b**: bias vector
- **β**: inverse temperature (1/kT)

---

## Part II: SGC-THRML Mapping

### 2.1 Functional Blanket → Energy Basin

**SGC**: A functional blanket is a subspace where dynamics commute with projection: [L, π] ≈ 0

**THRML**: An energy basin is a local minimum of E(x) where Gibbs sampling converges

**Mapping**:
```
SGC Functional Blanket ←→ THRML Energy Minimum

The "equivalence class" in SGC corresponds to all states x 
that minimize E(x) up to thermal fluctuations.
```

### 2.2 Ridge Ratio → Energy Barrier

**SGC**: Ridge Ratio R = E_between / E_within measures class boundary strength

**THRML**: Energy barrier ΔE between basins determines transition probability

**Mapping**:
```
SGC Ridge Ratio R ←→ THRML ΔE / kT

High R (sharp ridges) ←→ High ΔE (deep barrier)
Low R (smooth)        ←→ Low ΔE (shallow barrier)
```

### 2.3 Temperature D → Inverse β

**SGC**: Temperature D controls Kramers escape rate: τ ∝ exp(ΔV/D)

**THRML**: Inverse temperature β controls sampling sharpness: P(x) ∝ exp(-βE(x))

**Mapping**:
```
SGC Temperature D ←→ THRML 1/β

High D (exploration) ←→ Low β (high temperature, diffuse sampling)
Low D (consolidation) ←→ High β (low temperature, mode collapse)
```

### 2.4 Adiabatic Invariant → Clamped Blocks

**SGC**: Adiabatic invariant is a conserved quantity under slow parameter changes

**THRML**: Clamped blocks are nodes held fixed during sampling

**Mapping**:
```
SGC Frozen Subspace ←→ THRML clamped_blocks=[]

To protect Task A while learning Task B:
- SGC: Project gradients orthogonal to Task A subspace
- THRML: Clamp Task A blocks, sample only Task B blocks
```

### 2.5 Flat Torus Geometry → Sparse Local PGM

**SGC**: Grokked manifold is a flat torus (K ≈ 0) with ridges

**THRML**: Hardware PGMs are sparse, locally connected grids

**Mapping**:
```
SGC Flat Valley ←→ THRML Local interactions (short-range W)
SGC Ridge       ←→ THRML Negative coupling between blocks
SGC Torus       ←→ THRML Periodic boundary conditions
```

---

## Part III: Denoising Thermodynamic Models (DTMs)

### 3.1 What are DTMs?

DTMs are Extropic's key innovation: using EBMs as **denoising steps** rather than monolithic models.

**The Mixing-Expressivity Tradeoff (MET)**:
- Expressive EBMs are hard to sample (slow mixing)
- Easy-to-sample EBMs are not expressive enough

**DTM Solution**: Chain many simple EBMs to build complex distributions:
```
noise → EBM₁ → EBM₂ → ... → EBMₜ → data
```

Each EBM is simple (fast mixing), but the chain is expressive.

### 3.2 DTM-SGC Connection

**SGC Grokking** is analogous to a **single DTM step**:

| DTM Step | SGC Grokking Phase |
|----------|-------------------|
| Input xᵗ (noisy) | Pre-grok (memorization) |
| Energy ℰᶠ (forward) | Loss landscape V(θ) |
| Energy ℰᶿ (learned) | Functional blanket structure |
| Output xᵗ⁻¹ (denoised) | Post-grok (generalization) |

**Insight**: Grokking is a **single denoising step** that transforms a noisy memorization distribution into a clean generalization distribution.

### 3.3 DTM for Continual Learning

The DTM framework suggests a novel approach to continual learning:

```
Task A → DTM_A → Blanket_A
Task B → DTM_B → Blanket_B
...
```

Each task gets its own DTM (or block of the PGM), with **clamped interactions** preventing interference.

---

## Part IV: Implementation Plan

### 4.1 Phase 1: Install and Explore THRML

```bash
pip install thrml
```

**Experiments to run**:
1. Basic Ising sampling (verify installation)
2. Multi-basin energy landscape
3. Temperature annealing (simulated grokking)

### 4.2 Phase 2: SGC Metrics in THRML

Implement SGC observables in THRML:

```python
def compute_functional_defect_thrml(samples, class_labels):
    """
    Compute functional defect from THRML samples.
    
    Args:
        samples: Array of sampled states from THRML
        class_labels: Ground truth class for each sample
    
    Returns:
        epsilon: within-class variance / total variance
    """
    total_var = jnp.var(samples)
    within_var = sum(jnp.var(samples[labels == c]) 
                     for c in unique(labels)) / n_classes
    return within_var / (total_var + 1e-10)

def compute_ridge_ratio_thrml(model, samples, class_labels):
    """
    Compute ridge ratio from THRML model and samples.
    
    Uses the energy function to compute Dirichlet energy
    within and between classes.
    """
    E_within = 0
    E_between = 0
    for i, j in pairs:
        delta_E = model.energy(samples[i]) - model.energy(samples[j])
        if class_labels[i] == class_labels[j]:
            E_within += delta_E**2
        else:
            E_between += delta_E**2
    return E_between / (E_within + 1e-10)
```

### 4.3 Phase 3: SGC Controller for THRML

Adapt the SGC controller to modulate THRML's β (temperature):

```python
class SGCTHRMLController:
    """
    SGC controller for THRML sampling.
    
    Modulates inverse temperature β based on functional defect.
    """
    
    def __init__(self):
        self.beta_explore = 0.5    # Low β = high temp = exploration
        self.beta_grokked = 5.0    # High β = low temp = consolidation
        self.epsilon_threshold = 0.15
    
    def get_beta(self, epsilon, ridge_ratio):
        if epsilon > 0.5:
            return self.beta_explore
        elif epsilon < self.epsilon_threshold and ridge_ratio > 5:
            return self.beta_grokked
        else:
            # Linear interpolation
            t = (0.5 - epsilon) / (0.5 - self.epsilon_threshold)
            return self.beta_explore + t * (self.beta_grokked - self.beta_explore)
```

### 4.4 Phase 4: Grokking on THRML

Implement the modular arithmetic grokking task in THRML:

1. **Encode inputs**: Map (a, b) to binary spins
2. **Define energy**: E(x) encodes the addition table structure
3. **Train**: Use THRML's gradient computation for energy-based learning
4. **Monitor**: Track ε, R, β throughout training
5. **Validate**: Verify same grokking dynamics as PyTorch experiments

### 4.5 Phase 5: Continual Learning with Clamped Blocks

Test the adiabatic invariant hypothesis:

1. Train DTM on Task A (addition)
2. Clamp Task A blocks
3. Train DTM on Task B (multiplication) using unclamped blocks
4. Verify Task A is preserved (no catastrophic forgetting)

---

## Part V: Hardware Implications

### 5.1 Extropic Z1 Chip

Extropic is building the **Z1** thermodynamic sampling unit:
- **Architecture**: Sparse, locally connected Boltzmann machines
- **RNG**: All-transistor (no exotic components)
- **Efficiency**: ~10,000x more energy efficient than GPUs
- **Scale**: ~10⁶ sampling cells per 6x6 µm chip

### 5.2 SGC on Z1

SGC theory maps directly to Z1 capabilities:

| SGC Requirement | Z1 Implementation |
|-----------------|-------------------|
| Local temperature control | Per-node β tuning |
| Energy landscape | Programmable W, b |
| Gibbs sampling | Native hardware operation |
| Block freezing | Clamped blocks |
| Ridge detection | Energy difference measurement |

### 5.3 The Vision: SGC-Native Thermodynamic AI

```
┌─────────────────────────────────────────────────────────────┐
│               SGC-NATIVE THERMODYNAMIC AI                   │
├─────────────────────────────────────────────────────────────┤
│  Layer 3: SGC CONTROLLER                                    │
│  ├── Monitors: ε (defect), R (ridge ratio)                 │
│  ├── Actuates: β (temperature), clamped blocks             │
│  └── Phase: explore → transition → grokked                 │
├─────────────────────────────────────────────────────────────┤
│  Layer 2: THRML / DTM                                       │
│  ├── Models: IsingEBM, RBM, custom PGMs                    │
│  ├── Sampling: Block Gibbs                                  │
│  └── Training: Energy-based gradients                       │
├─────────────────────────────────────────────────────────────┤
│  Layer 1: EXTROPIC Z1 HARDWARE                             │
│  ├── Substrate: All-transistor thermodynamic RNG           │
│  ├── Topology: Sparse, locally connected grid              │
│  └── Efficiency: ~10,000x better than GPU                  │
└─────────────────────────────────────────────────────────────┘
```

---

## Part VI: Key Resources

### 6.1 GitHub Repository

**URL**: https://github.com/extropic-ai/thrml

**Contents**:
- `thrml/`: Core library
- `thrml/models/`: Pre-built models (Ising, RBM)
- Examples and documentation

### 6.2 Documentation

**URL**: https://docs.thrml.ai/en/latest/

### 6.3 Paper

**Title**: "An efficient probabilistic hardware architecture for diffusion-like models"  
**arXiv**: 2510.23972  
**Authors**: Jelinčič, Lockwood, Garlapati, Schillinger, Chuang, Verdon, McCourt

### 6.4 Company

**Extropic AI**: https://extropic.ai/
- Building thermodynamic computing hardware
- Research grants available for probabilistic computing
- Partnership opportunities for large probabilistic workloads

---

## Part VII: Next Steps

### Immediate Actions

1. **Install THRML**: `pip install thrml`
2. **Run basic examples**: Ising chain sampling
3. **Implement SGC metrics**: Functional defect, ridge ratio in JAX
4. **Create demo**: `sgc_thrml_demo.py` showing grokking dynamics

### Short-Term Goals

1. **Port grokking experiment**: Modular arithmetic on THRML
2. **Validate SGC-THRML mapping**: Confirm same dynamics
3. **Test continual learning**: Clamped blocks for memory protection

### Long-Term Vision

1. **Apply for Extropic research grant**: Propose SGC-native AI development
2. **Z1 early access**: Test SGC controller on real thermodynamic hardware
3. **Publish**: "SGC Theory for Thermodynamic AI"

---

## Conclusion

THRML provides the **ideal software substrate** for developing SGC-native AI:

1. **Native energy landscapes**: PGMs directly encode the "ridges and valleys" geometry
2. **Hardware path**: THRML code ports directly to Z1 thermodynamic chips
3. **Temperature control**: β parameter maps exactly to SGC temperature D
4. **Block structure**: Clamped blocks implement adiabatic invariant protection

**The synthesis is complete**: SGC theory + THRML library + Extropic hardware = the path to thermodynamic AGI.

---

## References

1. **THRML GitHub**: https://github.com/extropic-ai/thrml
2. **Extropic Paper**: arXiv:2510.23972 (Jelinčič et al., 2025)
3. **SGC Control Architecture**: `docs/SGC_CONTROL_ARCHITECTURE.md`
4. **SGC Canonical Theory**: `docs/SGC_CANONICAL_GROKKING_THEORY.md`

---

*"The thermodynamic computer doesn't simulate physics—it IS physics. SGC tells us what to compute; THRML tells us how."*
