# AGI Roadmap: From Simulation to Instantiation

## The Core Discovery

**Geometry is the Thermodynamics of Intelligence.**

The Bridge Validation experiment distinguished two regimes:

| Regime | Substrate | Sensor | Signal |
|--------|-----------|--------|--------|
| **Driven-Dissipative** | Digital (SGD) | Geometric (χ_g, Fisher) | Expensive to compute |
| **Equilibrium** | Thermodynamic HW | Energy (Cv, Heat) | Free from physics |

In equilibrium systems, **Energy = Geometry**. The hardware "feels" concepts forming.

---

## Phase 1: The Digital SGC Controller (Software)

**Status:** Ready to build

**Substrate:** GPUs / TPUs (Driven-Dissipative regime)

**Components:**
| Component | Implementation | Role |
|-----------|----------------|------|
| **Sensor: Order Parameter** | Functional Defect (ε) | ε < 0.15 ⟹ Grokked |
| **Sensor: Susceptibility** | χ_g = Var(ε) | Peak ⟹ Transition imminent |
| **Sensor: Phase Boundary** | Ridge Ratio (R) | R ≈ 1 ⟹ Critical point |
| **Actuator: Mobility** | Noise injection / Temperature | Kramers escape driver |
| **Actuator: Stiffness** | Constraint projection | Memory protection |

**Goal:** Perfect Continual Learning on current hardware by simulating thermodynamic constraints.

**Key Algorithm:**
```
while training:
    ε = compute_functional_defect(model)
    χ_g = variance(ε_history[-window:])
    
    if ε < 0.15:
        # Grokked - protect this knowledge
        freeze_subspace(model, task)
    elif χ_g > threshold:
        # Phase transition imminent - assist
        increase_temperature(optimizer)
    else:
        # Normal training
        standard_update(model)
```

---

## Phase 2: The Extropic Validator (Hardware)

**Status:** Pending hardware access

**Substrate:** Thermodynamic Chips (Equilibrium regime)

**Prediction:** Cv (current fluctuations / heat) WILL peak at grokking transition.

**Validation Test:**
- Train modular addition on thermodynamic hardware
- Measure Cv = β² Var(Energy)
- If gap between Cv peak and grokking < 100 epochs: **VALIDATED**

**Goal:** Ultra-low power, intrinsic grokking. The substrate naturally samples Boltzmann distributions.

---

## Phase 3: The Flat Ridge Architecture (Brain-Like)

**Status:** Future research

**Substrate:** Neuromorphic / Hybrid systems

**Dynamics:**
- Spiking Neural Networks with STDP
- Local "Surprise" events act as Heat for Kramers Escape
- Natural adiabatic invariants (stable memories)

**Goal:** A system that:
1. Sits in "off" states (preserved knowledge)
2. Wakes up (heats up) only to resolve contradictions (defects)
3. Naturally preserves knowledge without catastrophic forgetting

---

## Theoretical Foundation

| Layer | Concept | Reference |
|-------|---------|-----------|
| **Theory** | Spectral Graph Coarsening (SGC) | Manifold surgery on representation space |
| **Mathematics** | Fisher Information Geometry | Metric tensor on probability manifolds |
| **Physics** | Kramers Escape, Lifshitz Transitions | Phase transitions in thermodynamic systems |
| **Engineering** | SGC Control Loop | χ_g Sensor → Temperature Actuator |

---

## Key Equations

**Functional Defect (Order Parameter):**
```
ε = Var_within / Var_total
```

**Geometric Susceptibility:**
```
χ_g = Var(ε) over sliding window
```

**Specific Heat (Equilibrium only):**
```
Cv = β² Var(Energy)
```

**Fisher Information (Metric Tensor):**
```
F_ij = E[∂log p/∂θ_i · ∂log p/∂θ_j]
```

---

## The Shape of Knowledge

> "The Flat Ridge is the shape of knowledge."
> "The Fisher Information is the metric of understanding."
> "Thermodynamic Susceptibility is the pulse of a mind changing its mind."

---

*Research Phase: Complete*
*Build Phase: Initiated*
