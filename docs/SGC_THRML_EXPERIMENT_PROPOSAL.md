# Experiment Proposal: Thermodynamic Grokking & The Lifshitz Signature

**Date**: February 6, 2026
**Target**: Extropic Z1 Hardware (via `thrml` simulation)
**Theory**: Spectral Geometry of Consolidation (SGC)

## 1. Objective
To validate the **SGC Phase Transition Hypothesis** on a native thermodynamic substrate. We will demonstrate that "grokking" (generalization) in an Ising-based Energy Based Model (EBM) corresponds precisely to a thermodynamic **second-order phase transition**, characterized by a divergence in specific heat ($C_v$) and a collapse of the Functional Defect ($\epsilon$).

## 2. The Setup: Modular Addition on Spins

We will port the canonical "Modular Arithmetic" task ($a + b \equiv c \pmod p$) to the THRML Ising substrate.

*   **Representation**: Binary encoding of inputs $a, b$ and output $c$ into SpinNodes.
    *   Total Spins $N = 3 \times \lceil \log_2 p \rceil$.
*   **Model**: Fully connected `IsingEBM` (Boltzmann Machine).
    *   Energy: $E(s) = -\frac{1}{2} s^T W s - h^T s$
*   **Learning**: Contrastive Divergence (CD) or Persistent Contrastive Divergence (PCD).

## 3. SGC Integration

We will wrap the `thrml` simulation with the `sgc_controller` developed in the previous step.

### 3.1 The Mapping
| SGC Variable | THRML Parameter | Physical Meaning |
|--------------|-----------------|------------------|
| **Temperature** $D$ | `1.0 / beta` | Thermal noise in Gibbs sampling |
| **Functional Defect** $\epsilon$ | $\text{Var}(s_{\text{class}}) / \text{Var}(s_{\text{total}})$ | Consistency of spin states within algebraic classes |
| **Criticality** $\rho_0$ | Specific Heat $C_v = \text{Var}(E)/T^2$ | Fluctuations in energy (Thermodynamic Susceptibility) |
| **Plasticity Gate** $G$ | `clamped_blocks` | Fixed spin constraints |

### 3.2 The Controller Loop
The `BangBangController` will drive the annealing schedule:
1.  **EXPLORE** ($\beta \ll 1$): High temp sampling to find global structure.
2.  **TRANSITION** ($\beta \approx \beta_c$): Critical temp where Ridge Ratio $R > 1$.
3.  **GROKKED** ($\beta \gg 1$): Low temp "freezing" into the solution manifold.

## 4. Key Hypotheses

1.  **The Lifshitz Signature**: The epoch of grokking (test accuracy jump) will align perfectly with a peak in **Specific Heat** ($C_v$).
    *   *Why?* Grokking is the alignment of the internal energy landscape with the problem structure. This alignment maximizes fluctuations between competing basins before settling.
2.  **Adiabatic Protection**: Using `clamped_blocks` on the hidden units associated with "Task A" will allow learning "Task B" without forgetting, validating the hardware efficiency of SGC continual learning.

## 5. Implementation Plan (Pseudo-code)

```python
import thrml
from sgc_controller import BangBangController, SGCMetrics

# 1. Setup
ebm = thrml.IsingEBM(num_spins=18) # 6 bits each for a, b, c
controller = BangBangController()

# 2. Train Loop
for epoch in range(1000):
    # A. SGC Control Step
    metrics = measure_sgc_metrics(ebm, data)
    actions = controller.step(metrics.epsilon, metrics.ridge_ratio)
    
    # B. Apply Actuators
    beta = 1.0 / actions.temperature
    
    # C. Thermodynamic Update (The "Hardware" Step)
    # Clamp inputs, sample outputs
    samples = ebm.sample_states(beta=beta, clamped=inputs)
    
    # D. Hebbian Learning (Update W)
    # W += learning_rate * (data_stats - model_stats)
    ebm.update_weights(samples, data_samples)
    
    # E. Measure Heat Capacity
    energies = ebm.energy(samples)
    Cv = energies.var() / (actions.temperature**2)
    
    if Cv > threshold and metrics.epsilon < 0.15:
        print("LIFSHITZ TRANSITION DETECTED")
```

## 6. Impact

Success confirms that **SGC is not just a neural network theory, but a universal thermodynamic theory of learning.** It directly enables the programming of Extropic's Z1 chip using high-level control theory rather than manual annealing schedules.
