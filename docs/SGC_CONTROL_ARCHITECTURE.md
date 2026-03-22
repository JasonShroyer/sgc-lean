# SGC Control Architecture: From Theory to Thermodynamic Computing

**Date**: February 6, 2026  
**Version**: 1.0  
**Status**: Specification Document  
**Preceding Work**: `SGC_CANONICAL_GROKKING_THEORY.md`, Manifold Surgery Experiments

---

## Executive Summary

This document formalizes the **control-theoretic structure** that emerges from SGC theory. The key insight: SGC provides a complete **sensor-actuator-controller** framework for intelligent systems, where:

- **Sensors**: Intrinsic observables (functional defect ε, ridge ratio R, density@0)
- **Actuators**: Temperature D, cooling pressure λ, plasticity gates
- **Controller**: Phase-aware state machine driving the system through Kramers barriers

This architecture is **substrate-agnostic**: it can be implemented in software (PyTorch), neuromorphic hardware (SNNs), or thermodynamic computers. The mathematics is identical; only the efficiency changes.

---

## Part I: The SGC-Cybernetics Isomorphism

### 1.1 The Fundamental Mapping

| SGC Concept | Control Theory | Physical Realization |
|-------------|----------------|---------------------|
| Functional Defect ε | **Error Signal** | Within-class variance / total variance |
| Ridge Ratio R | **Order Parameter** | E_between / E_within (Dirichlet) |
| Density@0 | **Criticality Indicator** | Hessian eigenvalue density near zero |
| Temperature D | **Mobility Control** | Noise injection / mini-batch size |
| Weight Decay λ | **Cooling Pressure** | Regularization strength |
| Plasticity Gate | **Constraint Enforcement** | Subspace projection / freeze mask |

### 1.2 The Control Problem Statement

**Given**: A learning system with state θ(t) evolving on a loss landscape V(θ)

**Goal**: Drive the system from the **memorization basin** (high ε, R < 1) to the **generalization manifold** (low ε, R >> 1) while:
1. Minimizing transition time τ
2. Preserving previously learned functional blankets (continual learning)
3. Using only intrinsic observables (no test set)

**Constraint**: The generalization manifold is a **Flat Torus with Ridges**—topologically T², geometrically flat (K ≈ 0), with sharp energy barriers between equivalence classes.

---

## Part II: Sensor Specifications

### 2.1 Primary Sensors

#### Sensor 1: Functional Defect ε(t)

```
ε(t) = Var_within(h) / Var_total(h)

Where:
- h = hidden states for all inputs
- Var_within = average variance within each equivalence class
- Var_total = total variance across all hidden states
```

**Properties**:
- Range: [0, 1] (approximately)
- Pre-grok: ε ≈ 1.0 (no structure)
- Grokked: ε < 0.15 (equivalence learned)
- **Test-set-free**: Computed entirely from training representations

**Control Interpretation**: ε is the **regulation target**. The controller's job is to drive ε → 0.

#### Sensor 2: Ridge Ratio R(t)

```
R(t) = E_between(t) / E_within(t)

Where:
- E_between = Σ ||h_i - h_j||² for (i,j) in DIFFERENT classes
- E_within = Σ ||h_i - h_j||² for (i,j) in SAME class
```

**Properties**:
- Range: [0, ∞)
- Pre-grok: R < 1 (smooth everywhere)
- Transition: R crosses 1.0 (ridges forming)
- Grokked: R >> 1 (sharp boundaries)

**Control Interpretation**: R is the **phase indicator**. R > 1 signals "ridges have formed."

#### Sensor 3: Van Hove Density ρ₀(t)

```
ρ₀(t) = (1/N) Σ δ(λᵢ) ≈ histogram_density(eigenvalues, bin=0)

Where:
- λᵢ = eigenvalues of the Hessian ∇²V(θ)
```

**Properties**:
- Peaks at topological transition (Lifshitz point)
- Indicates "near-criticality"

**Control Interpretation**: ρ₀ is the **proximity-to-transition** sensor. High ρ₀ means "phase boundary is near."

### 2.2 Derived Sensors

| Sensor | Formula | Use |
|--------|---------|-----|
| ε̇(t) | dε/dt (finite difference) | Rate of learning |
| Ṙ(t) | dR/dt | Ridge formation rate |
| Class Separation | Fisher criterion on hidden states | Margin quality |
| Gradient Ratio | \|\|∇I\|\| / \|\|∇E\|\| | Information vs energy balance |

### 2.3 Sensor Fusion: Phase Classification

```python
def classify_phase(ε, R, ρ₀):
    """
    Phase classification using SGC observables.
    
    Returns: 'memorize' | 'transition' | 'grokked'
    """
    if ε > 0.5 and R < 1.0:
        return 'memorize'
    elif 0.15 < ε <= 0.5 or (R >= 1.0 and R < 5.0):
        return 'transition'
    elif ε <= 0.15 and R >= 5.0:
        return 'grokked'
    else:
        return 'transition'  # Ambiguous → assume transitioning
```

---

## Part III: Actuator Specifications

### 3.1 Temperature D (Mobility Control)

**Mathematical Role**: Controls Kramers escape rate
```
τ ∝ exp(ΔV / D)
```

**Implementation Options**:

| Substrate | D Implementation |
|-----------|------------------|
| SGD | Mini-batch noise (smaller batch = higher D) |
| Full-batch | Explicit noise injection: θ ← θ + √(2D)ξ |
| SNN | Spike stochasticity / membrane noise |
| Thermodynamic | Literal temperature of physical substrate |

**Control Range**: D ∈ [D_min, D_max] where:
- D_min ≈ 0 (deterministic, slow consolidation)
- D_max = O(ΔV) (enough to cross barriers in reasonable time)

### 3.2 Cooling Pressure λ (Regularization)

**Mathematical Role**: Drives system toward simpler solutions
```
V_effective(θ) = V_loss(θ) + λ ||θ||²
```

**Control Range**: λ ∈ [0, λ_max] where:
- λ = 0: No simplification pressure
- λ_max ≈ 1.0: Strong pressure (validated in grokking experiments)

### 3.3 Plasticity Gate G (Constraint Enforcement)

**Mathematical Role**: Enforces adiabatic invariant preservation
```
Δθ_safe = G · Δθ_raw

Where G is a projection operator:
- G = I (full plasticity)
- G = I - UU^T (orthogonal to protected subspace U)
- G = diag(mask) (binary freeze mask)
```

**Implementation Options**:

| Substrate | G Implementation |
|-----------|------------------|
| Software | Explicit matrix projection (expensive) |
| Software (approx) | Binary mask on gradients |
| SNN | Silence = no plasticity (STDP gated by activity) |
| Thermodynamic | Low local temperature = frozen degrees of freedom |

---

## Part IV: Controller Architectures

### 4.1 Architecture A: Bang-Bang Controller (Simplest)

A **three-phase state machine** with threshold-based switching.

```
┌─────────────────────────────────────────────────────────────────┐
│                     BANG-BANG CONTROLLER                        │
│                                                                 │
│   ┌──────────┐    R > 1     ┌────────────┐   ε < 0.15   ┌─────────┐
│   │ EXPLORE  │ ──────────▶ │ TRANSITION │ ──────────▶ │ GROKKED │
│   │  D=D_max │              │  D=D_mid   │              │  D=D_min│
│   │  λ=λ_low │              │  λ=λ_mid   │              │  λ=λ_max│
│   │  G=I     │              │  G=I       │              │  G=mask │
│   └──────────┘              └────────────┘              └─────────┘
│        ▲                          │                          │
│        │         ε > 0.5          │                          │
│        └──────────────────────────┘                          │
│                                                               │
│   Hysteresis: Once GROKKED, stay GROKKED unless ε > 0.3      │
└─────────────────────────────────────────────────────────────────┘
```

**Update Rules**:

```python
class BangBangController:
    def __init__(self):
        self.D_max = 1e-2   # High noise (e.g., batch_size=64)
        self.D_mid = 5e-3   # Medium noise
        self.D_min = 1e-4   # Low noise (e.g., batch_size=1024)
        self.λ_low = 0.1
        self.λ_mid = 0.5
        self.λ_max = 1.0
        self.ε_grok = 0.15
        self.ε_ungrok = 0.3  # Hysteresis
        self.R_ridge = 1.0
        self.state = 'explore'
        self.frozen_mask = None
    
    def step(self, ε, R, model):
        # State transitions
        if self.state == 'explore' and R > self.R_ridge:
            self.state = 'transition'
        elif self.state == 'transition' and ε < self.ε_grok:
            self.state = 'grokked'
            self.frozen_mask = self._compute_freeze_mask(model)
        elif self.state == 'grokked' and ε > self.ε_ungrok:
            self.state = 'transition'  # Lost it, re-explore
        
        # Output actuator settings
        if self.state == 'explore':
            return {'D': self.D_max, 'λ': self.λ_low, 'G': None}
        elif self.state == 'transition':
            return {'D': self.D_mid, 'λ': self.λ_mid, 'G': None}
        else:  # grokked
            return {'D': self.D_min, 'λ': self.λ_max, 'G': self.frozen_mask}
```

### 4.2 Architecture B: PID Controller on ε

A **continuous regulator** that smoothly modulates temperature.

```
┌─────────────────────────────────────────────────────────────────┐
│                       PID CONTROLLER                            │
│                                                                 │
│   Target: ε* = 0.10 (desired defect level)                     │
│                                                                 │
│   Error:  e(t) = ε(t) - ε*                                     │
│                                                                 │
│   Control Law:                                                  │
│   D(t) = D₀ + Kp·e(t) + Ki·∫e(τ)dτ + Kd·ė(t)                  │
│                                                                 │
│   Constraints:                                                  │
│   - D(t) ∈ [D_min, D_max]                                      │
│   - Anti-windup on integral term                                │
│                                                                 │
│   Auxiliary:                                                    │
│   - λ(t) = λ₀ - α·e(t)  (increase cooling as ε drops)         │
└─────────────────────────────────────────────────────────────────┘
```

**Update Rules**:

```python
class PIDController:
    def __init__(self):
        self.ε_target = 0.10
        self.Kp = 0.1      # Proportional gain
        self.Ki = 0.01     # Integral gain  
        self.Kd = 0.05     # Derivative gain
        self.D_0 = 5e-3    # Baseline temperature
        self.D_min = 1e-4
        self.D_max = 1e-2
        self.λ_0 = 0.5
        self.α = 0.5       # Cooling coupling
        self.integral = 0
        self.prev_ε = 1.0
    
    def step(self, ε, dt=1.0):
        e = ε - self.ε_target
        self.integral += e * dt
        self.integral = np.clip(self.integral, -10, 10)  # Anti-windup
        derivative = (ε - self.prev_ε) / dt
        self.prev_ε = ε
        
        # PID output
        D = self.D_0 + self.Kp * e + self.Ki * self.integral + self.Kd * derivative
        D = np.clip(D, self.D_min, self.D_max)
        
        # Coupled cooling
        λ = self.λ_0 - self.α * e
        λ = np.clip(λ, 0.1, 1.5)
        
        return {'D': D, 'λ': λ}
```

### 4.3 Architecture C: MPC with Phase Prediction

A **model-predictive controller** that uses ε̇, Ṙ to anticipate transitions.

```
┌─────────────────────────────────────────────────────────────────┐
│                    MPC CONTROLLER                               │
│                                                                 │
│   State: x = [ε, R, ρ₀]                                        │
│   Input: u = [D, λ]                                            │
│                                                                 │
│   Dynamics Model (simplified):                                  │
│   ε̇ ≈ -k₁·D·(ε - ε_eq) - k₂·λ·ε                               │
│   Ṙ ≈ k₃·(1 - ε)·(R_max - R)                                   │
│                                                                 │
│   Objective:                                                    │
│   min_{u(t:t+H)} ∫ [w₁·ε² + w₂·(R-R*)² + w₃·D²] dt            │
│                                                                 │
│   Constraints:                                                  │
│   - D ∈ [D_min, D_max]                                         │
│   - λ ∈ [λ_min, λ_max]                                         │
│   - ε monotonically decreasing (soft)                          │
└─────────────────────────────────────────────────────────────────┘
```

---

## Part V: The SGC Spiking Controller

### 5.1 Design Principle: "Default Off, Spike on Surprise"

The key insight from predictive coding and SGC:

> **A neuron should be silent when predictions match reality (low defect).**
> **Spikes occur when surprise/error is high (defect correction events).**

This naturally implements:
1. **Adiabatic invariance**: Silent neurons have frozen plasticity
2. **Local temperature control**: Spike bursts = local heat injection
3. **Energy efficiency**: No compute when nothing needs to change

### 5.2 Mathematical Specification

#### Variables (per neuron/unit i):

| Symbol | Meaning | Update |
|--------|---------|--------|
| xᵢ(t) | Membrane potential | Leaky integration of inputs |
| x̂ᵢ(t) | Local prediction | Exponential moving average |
| eᵢ(t) | Surprise/error | eᵢ = xᵢ - x̂ᵢ |
| sᵢ(t) | Spike output | sᵢ = H(eᵢ - θ_spike) |
| wᵢⱼ(t) | Synaptic weight | STDP with surprise gating |

#### Dynamics:

**1. Membrane Potential** (leaky integrate-and-fire):
```
τ_m · dxᵢ/dt = -xᵢ + Σⱼ wᵢⱼ·sⱼ + bᵢ + √(2Dᵢ)·ξᵢ(t)
```

**2. Prediction Update** (exponential smoothing):
```
τ_p · dx̂ᵢ/dt = -x̂ᵢ + xᵢ
```

**3. Surprise Signal**:
```
eᵢ(t) = |xᵢ(t) - x̂ᵢ(t)|
```

**4. Spike Generation** (threshold with reset):
```
if eᵢ > θ_spike:
    sᵢ ← 1
    xᵢ ← x_reset
else:
    sᵢ ← 0
```

**5. Local Temperature** (surprise-modulated):
```
Dᵢ(t) = D_base + D_gain · EMA(eᵢ(t))
```

**6. Plasticity Rule** (three-factor STDP):
```
Δwᵢⱼ = η · sᵢ · sⱼ · M(eᵢ)

Where M(e) is the modulatory factor:
- M(e) = 0 if e < θ_plastic (no learning when unsurprised)
- M(e) = e - θ_plastic if e ≥ θ_plastic (surprise-gated learning)
```

### 5.3 Mapping to SGC Observables

| SGC Observable | Spiking Realization |
|----------------|---------------------|
| Functional Defect ε | Population surprise: ε ≈ (1/N)Σeᵢ |
| Ridge Ratio R | Ratio of cross-class to within-class spike correlations |
| Temperature D | Local Dᵢ values (spike stochasticity) |
| Plasticity Gate G | M(eᵢ) factor in STDP rule |

### 5.4 The Complete SGC Spiking Controller

```python
class SGCSpikingController:
    """
    SGC-derived spiking neural controller.
    
    Implements:
    - Surprise-gated plasticity (adiabatic invariant preservation)
    - Local temperature modulation (Kramers escape control)
    - Intrinsic phase detection (no test set needed)
    """
    
    def __init__(self, n_neurons, n_classes):
        self.n = n_neurons
        self.n_classes = n_classes
        
        # Membrane dynamics
        self.tau_m = 20.0       # Membrane time constant (ms)
        self.tau_p = 100.0      # Prediction time constant
        self.x_reset = 0.0      # Reset potential
        
        # Spike generation
        self.theta_spike = 0.5  # Spike threshold
        
        # Plasticity
        self.eta = 0.01         # Learning rate
        self.theta_plastic = 0.2  # Plasticity threshold
        
        # Temperature control
        self.D_base = 0.01      # Baseline noise
        self.D_gain = 0.1       # Surprise→noise coupling
        self.D_max = 0.5        # Maximum noise
        
        # State
        self.x = np.zeros(n_neurons)      # Membrane potential
        self.x_hat = np.zeros(n_neurons)  # Prediction
        self.D = np.full(n_neurons, self.D_base)  # Local temperature
        self.W = np.random.randn(n_neurons, n_neurons) * 0.1  # Weights
        
        # Phase tracking
        self.phase = 'explore'
        self.epsilon_history = []
        self.R_history = []
    
    def compute_surprise(self):
        """Compute per-neuron surprise (error) signal."""
        return np.abs(self.x - self.x_hat)
    
    def compute_functional_defect(self, class_labels):
        """
        Compute population-level functional defect.
        Maps directly to SGC ε.
        """
        e = self.compute_surprise()
        total_var = np.var(e)
        
        within_var = 0
        for c in range(self.n_classes):
            mask = (class_labels == c)
            if mask.sum() > 1:
                within_var += np.var(e[mask]) * mask.sum()
        within_var /= len(class_labels)
        
        return within_var / (total_var + 1e-10)
    
    def compute_ridge_ratio(self, class_labels):
        """
        Compute ridge ratio from spike correlations.
        Maps directly to SGC R.
        """
        spikes = (self.compute_surprise() > self.theta_spike).astype(float)
        
        E_within = 0
        E_between = 0
        n_within = 0
        n_between = 0
        
        for i in range(len(spikes)):
            for j in range(i+1, len(spikes)):
                dist = (spikes[i] - spikes[j])**2
                if class_labels[i] == class_labels[j]:
                    E_within += dist
                    n_within += 1
                else:
                    E_between += dist
                    n_between += 1
        
        E_within = E_within / max(n_within, 1)
        E_between = E_between / max(n_between, 1)
        
        return E_between / (E_within + 1e-10)
    
    def update_temperature(self):
        """
        Update local temperature based on surprise.
        Implements Kramers escape rate control.
        """
        e = self.compute_surprise()
        # Exponential moving average of surprise
        self.D = self.D_base + self.D_gain * e
        self.D = np.clip(self.D, self.D_base, self.D_max)
    
    def step(self, inputs, class_labels, dt=1.0):
        """
        One time step of the SGC spiking controller.
        
        Args:
            inputs: External input to neurons
            class_labels: Class labels for each neuron (for defect computation)
            dt: Time step
        
        Returns:
            spikes: Binary spike vector
            metrics: Dict of SGC observables
        """
        # 1. Compute surprise BEFORE updating
        e = self.compute_surprise()
        
        # 2. Update local temperature
        self.update_temperature()
        
        # 3. Membrane dynamics with noise
        noise = np.sqrt(2 * self.D * dt) * np.random.randn(self.n)
        dx = (-self.x + self.W @ (e > self.theta_spike).astype(float) + inputs) / self.tau_m
        self.x += dx * dt + noise
        
        # 4. Update prediction (slower timescale)
        self.x_hat += (self.x - self.x_hat) * dt / self.tau_p
        
        # 5. Spike generation
        spikes = (e > self.theta_spike).astype(float)
        self.x[spikes > 0] = self.x_reset
        
        # 6. Surprise-gated plasticity
        modulator = np.maximum(0, e - self.theta_plastic)
        dW = self.eta * np.outer(spikes * modulator, spikes * modulator)
        self.W += dW
        
        # 7. Compute SGC observables
        epsilon = self.compute_functional_defect(class_labels)
        R = self.compute_ridge_ratio(class_labels)
        
        self.epsilon_history.append(epsilon)
        self.R_history.append(R)
        
        # 8. Update phase classification
        self._update_phase(epsilon, R)
        
        return spikes, {
            'epsilon': epsilon,
            'R': R,
            'mean_D': np.mean(self.D),
            'mean_surprise': np.mean(e),
            'spike_rate': np.mean(spikes),
            'phase': self.phase
        }
    
    def _update_phase(self, epsilon, R):
        """Phase classification with hysteresis."""
        if self.phase == 'explore':
            if R > 1.0:
                self.phase = 'transition'
        elif self.phase == 'transition':
            if epsilon < 0.15 and R > 5.0:
                self.phase = 'grokked'
            elif epsilon > 0.8 and R < 0.5:
                self.phase = 'explore'
        elif self.phase == 'grokked':
            if epsilon > 0.3:
                self.phase = 'transition'
```

---

## Part VI: The Thermodynamic Hardware Specification

### 6.1 Required Physical Primitives

Based on SGC theory, thermodynamic hardware must support:

| Primitive | Physical Realization | SGC Role |
|-----------|---------------------|----------|
| **Bistable Element** | Magnetic tunnel junction, memristor | Stores one bit of "ridge" (class boundary) |
| **Local Temperature** | Joule heating, laser spot | Kramers escape rate control |
| **Energy Minimizer** | Physical annealing, Hopfield dynamics | Finds flat valleys |
| **Coupling** | Resistive crossbar, synaptic connection | Implements Dirichlet energy |

### 6.2 The SGC Hardware Stack

```
┌─────────────────────────────────────────────────────────────────┐
│                    SGC HARDWARE STACK                           │
├─────────────────────────────────────────────────────────────────┤
│  Layer 4: CONTROLLER                                            │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │ SGC Controller (digital or analog)                       │   │
│  │ - Reads: ε, R, phase indicators                         │   │
│  │ - Writes: D(zone), λ, plasticity gates                  │   │
│  └─────────────────────────────────────────────────────────┘   │
├─────────────────────────────────────────────────────────────────┤
│  Layer 3: TEMPERATURE ZONES                                     │
│  ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐          │
│  │ Zone A   │ │ Zone B   │ │ Zone C   │ │ Zone D   │          │
│  │ D = 0.01 │ │ D = 0.5  │ │ D = 0.01 │ │ D = 0.3  │          │
│  │ (frozen) │ │ (plastic)│ │ (frozen) │ │ (active) │          │
│  └──────────┘ └──────────┘ └──────────┘ └──────────┘          │
├─────────────────────────────────────────────────────────────────┤
│  Layer 2: ENERGY LANDSCAPE                                      │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │ Hopfield-like energy function:                           │   │
│  │ E(x) = -½ xᵀWx + Σᵢ Vᵢ(xᵢ)                              │   │
│  │                                                          │   │
│  │ Valleys = Functional Blankets                            │   │
│  │ Ridges = Class Boundaries                                │   │
│  └─────────────────────────────────────────────────────────┘   │
├─────────────────────────────────────────────────────────────────┤
│  Layer 1: PHYSICAL SUBSTRATE                                    │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │ Crossbar array / Memristor grid / Neuromorphic chip      │   │
│  │ - Implements W matrix                                    │   │
│  │ - Native noise source (thermal)                          │   │
│  │ - Local Hebbian updates (STDP in hardware)              │   │
│  └─────────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────────┘
```

### 6.3 The "Flat Ridge" Simplification

**Critical insight from our experiments**: The manifold is **intrinsically flat** (Gauss K ≈ 0).

This dramatically simplifies the hardware requirements:

| If Curved (old assumption) | If Flat (SGC finding) |
|---------------------------|----------------------|
| Need Riemannian metric hardware | Euclidean/linear sufficient |
| Complex geodesic computation | Simple distance metrics |
| Curvature tensors | Just barriers/thresholds |

**Hardware implication**: We don't need exotic curved-space computers. Standard **analog crossbars** with **threshold nonlinearities** (for ridges) suffice.

---

## Part VII: Implementation Roadmap

### 7.1 Phase 1: Digital Proof of Concept

**Goal**: Validate SGC controller on modular arithmetic grokking

**Deliverables**:
1. `sgc_controller.py` - Bang-bang + PID controllers
2. `sgc_spiking_controller.py` - Full spiking implementation
3. `continual_learning_sgc.py` - Multi-task with freeze protection

**Success Criteria**:
- Controller achieves grokking 2x faster than baseline (D modulation)
- Continual learning with <5% forgetting (plasticity gating)

### 7.2 Phase 2: Neuromorphic Simulation

**Goal**: Validate on SNN simulator (Brian2, Norse, or Lava)

**Deliverables**:
1. SNN implementation of SGC controller
2. Benchmarks vs. rate-coded networks
3. Energy efficiency analysis

### 7.3 Phase 3: Hardware Specification

**Goal**: Produce chip-ready spec for thermodynamic SGC

**Deliverables**:
1. Formal hardware specification document
2. Simulation of physical noise effects
3. Partnership with neuromorphic hardware team

---

## Conclusion

SGC theory provides a **complete control architecture** for intelligent systems:

1. **Sensors**: ε, R, ρ₀ form a redundant, test-set-free observable suite
2. **Actuators**: D, λ, G are physically realizable controls
3. **Controller**: Phase-aware state machine with Kramers-optimal temperature scheduling
4. **Hardware**: Flat Ridge geometry enables simple analog implementation

The path from PyTorch to thermodynamic AGI is now mathematically specified.

---

## References

1. **SGC Canonical Theory**: `docs/SGC_CANONICAL_GROKKING_THEORY.md`
2. **Manifold Surgery Experiments**: `logs/manifold_surgery_fast/`
3. **Kramers (1940)**: "Brownian motion in a field of force"
4. **Hopfield (1982)**: "Neural networks and physical systems"
5. **Friston (2010)**: "The free-energy principle"
6. **Nanda et al. (2023)**: "Progress measures for grokking"

---

*"The mathematics of thought: sensors that see without tests, actuators that heat and freeze, controllers that grok on demand."*
