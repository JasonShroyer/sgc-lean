"""
SGC Controller: Cybernetic Control for Grokking and Continual Learning

This module implements the control architectures derived from SGC theory:
1. Bang-Bang Controller (three-phase state machine)
2. PID Controller on functional defect
3. SGC Spiking Controller (surprise-gated plasticity)

The controllers use ONLY intrinsic observables (no test set required):
- Functional Defect ε: within-class variance / total variance
- Ridge Ratio R: E_between / E_within (Dirichlet energy)
- Phase classification: memorize → transition → grokked

Usage:
    controller = BangBangController()
    for epoch in range(epochs):
        metrics = compute_sgc_metrics(model, dataloader)
        actions = controller.step(metrics['epsilon'], metrics['ridge_ratio'])
        apply_actions(optimizer, model, actions)

Author: SGC Research Team
Date: February 6, 2026
"""

import numpy as np
import torch
import torch.nn as nn
from typing import Dict, Tuple, Optional, List
from dataclasses import dataclass
from enum import Enum


class Phase(Enum):
    """SGC phase classification."""
    EXPLORE = "explore"
    TRANSITION = "transition"
    GROKKED = "grokked"


@dataclass
class ControlActions:
    """Actions output by the controller."""
    temperature: float      # D: noise level / effective batch size
    cooling: float          # λ: weight decay
    plasticity_mask: Optional[torch.Tensor] = None  # G: freeze mask
    phase: Phase = Phase.EXPLORE


class SGCMetrics:
    """Compute SGC observables from model and data."""
    
    @staticmethod
    def compute_functional_defect(
        hidden_states: torch.Tensor,
        labels: torch.Tensor,
        num_classes: int
    ) -> Tuple[float, float, float]:
        """
        Compute functional defect: within-class variance / total variance.
        
        This is the PRIMARY order parameter for grokking detection.
        ε < 0.15 indicates grokking (test-set-free detection).
        
        Returns:
            (functional_defect, class_separation, total_variance)
        """
        h = hidden_states.detach()
        total_var = torch.var(h).item()
        
        within_var = 0.0
        class_means = []
        
        for c in range(num_classes):
            mask = (labels == c)
            if mask.sum() > 1:
                class_h = h[mask]
                within_var += torch.var(class_h).item() * mask.sum().item()
                class_means.append(class_h.mean(dim=0))
        
        within_var /= len(labels)
        
        # Class separation (Fisher criterion)
        if len(class_means) > 1:
            class_means = torch.stack(class_means)
            between_var = torch.var(class_means).item()
            class_separation = between_var / (within_var + 1e-10)
        else:
            class_separation = 0.0
        
        functional_defect = within_var / (total_var + 1e-10)
        
        return functional_defect, class_separation, total_var
    
    @staticmethod
    def compute_ridge_ratio(
        hidden_states: torch.Tensor,
        labels: torch.Tensor,
        k_neighbors: int = 10
    ) -> float:
        """
        Compute Ridge Ratio: E_between / E_within (Dirichlet energy).
        
        R > 1 indicates ridge formation (class boundaries emerging).
        R >> 1 indicates sharp classification structure.
        
        Returns:
            ridge_ratio
        """
        h = hidden_states.detach()
        n = len(h)
        
        # Compute pairwise distances (sample for efficiency)
        if n > 500:
            idx = torch.randperm(n)[:500]
            h = h[idx]
            labels = labels[idx]
            n = 500
        
        # Compute k-nearest neighbors for each point
        dists = torch.cdist(h, h)
        
        E_within = 0.0
        E_between = 0.0
        n_within = 0
        n_between = 0
        
        for i in range(n):
            # Get k nearest neighbors
            _, neighbors = torch.topk(dists[i], k_neighbors + 1, largest=False)
            neighbors = neighbors[1:]  # Exclude self
            
            for j in neighbors:
                d_sq = dists[i, j].item() ** 2
                if labels[i] == labels[j]:
                    E_within += d_sq
                    n_within += 1
                else:
                    E_between += d_sq
                    n_between += 1
        
        E_within = E_within / max(n_within, 1)
        E_between = E_between / max(n_between, 1)
        
        return E_between / (E_within + 1e-10)
    
    @staticmethod
    def compute_all(
        model: nn.Module,
        dataloader: torch.utils.data.DataLoader,
        num_classes: int,
        device: str = 'cuda'
    ) -> Dict[str, float]:
        """Compute all SGC metrics."""
        model.eval()
        all_hidden = []
        all_labels = []
        
        with torch.no_grad():
            for batch in dataloader:
                if len(batch) == 2:
                    x, y = batch
                else:
                    x, y = batch[0], batch[1]
                x, y = x.to(device), y.to(device)
                
                # Get hidden states (assumes model has get_hidden method or we use penultimate layer)
                if hasattr(model, 'get_hidden'):
                    h = model.get_hidden(x)
                else:
                    # Hook the penultimate layer
                    h = x
                    for layer in list(model.children())[:-1]:
                        h = layer(h)
                
                all_hidden.append(h)
                all_labels.append(y)
        
        hidden = torch.cat(all_hidden, dim=0)
        labels = torch.cat(all_labels, dim=0)
        
        epsilon, class_sep, total_var = SGCMetrics.compute_functional_defect(
            hidden, labels, num_classes
        )
        ridge_ratio = SGCMetrics.compute_ridge_ratio(hidden, labels)
        
        return {
            'epsilon': epsilon,
            'ridge_ratio': ridge_ratio,
            'class_separation': class_sep,
            'total_variance': total_var
        }


class BangBangController:
    """
    Bang-Bang Controller: Three-phase state machine with threshold switching.
    
    Phases:
        EXPLORE: High temperature, low cooling (searching for structure)
        TRANSITION: Medium temperature (ridges forming)
        GROKKED: Low temperature, high cooling, plasticity protection
    
    Transitions:
        EXPLORE → TRANSITION: when R > R_ridge (ridges detected)
        TRANSITION → GROKKED: when ε < ε_grok (equivalence learned)
        GROKKED → TRANSITION: when ε > ε_ungrok (hysteresis, lost structure)
    """
    
    def __init__(
        self,
        # Temperature settings (effective noise level)
        D_explore: float = 0.02,      # High noise
        D_transition: float = 0.01,   # Medium noise
        D_grokked: float = 0.001,     # Low noise
        # Cooling settings (weight decay)
        lambda_explore: float = 0.1,
        lambda_transition: float = 0.5,
        lambda_grokked: float = 1.0,
        # Thresholds
        epsilon_grok: float = 0.15,   # Defect threshold for grokking
        epsilon_ungrok: float = 0.30, # Hysteresis threshold
        R_ridge: float = 1.0,         # Ridge ratio threshold
        R_strong: float = 5.0,        # Strong ridge threshold
    ):
        self.D = {
            Phase.EXPLORE: D_explore,
            Phase.TRANSITION: D_transition,
            Phase.GROKKED: D_grokked,
        }
        self.lambda_ = {
            Phase.EXPLORE: lambda_explore,
            Phase.TRANSITION: lambda_transition,
            Phase.GROKKED: lambda_grokked,
        }
        self.epsilon_grok = epsilon_grok
        self.epsilon_ungrok = epsilon_ungrok
        self.R_ridge = R_ridge
        self.R_strong = R_strong
        
        self.phase = Phase.EXPLORE
        self.frozen_params: Optional[Dict[str, torch.Tensor]] = None
        self.history: List[Dict] = []
    
    def step(self, epsilon: float, ridge_ratio: float, model: Optional[nn.Module] = None) -> ControlActions:
        """
        One step of the controller.
        
        Args:
            epsilon: Current functional defect
            ridge_ratio: Current ridge ratio
            model: Optional model for computing freeze mask
        
        Returns:
            ControlActions with temperature, cooling, and optional plasticity mask
        """
        old_phase = self.phase
        
        # Phase transitions
        if self.phase == Phase.EXPLORE:
            if ridge_ratio > self.R_ridge:
                self.phase = Phase.TRANSITION
                print(f"[SGC] Phase transition: EXPLORE -> TRANSITION (R={ridge_ratio:.2f} > {self.R_ridge})")
        
        elif self.phase == Phase.TRANSITION:
            if epsilon < self.epsilon_grok and ridge_ratio > self.R_strong:
                self.phase = Phase.GROKKED
                print(f"[SGC] Phase transition: TRANSITION -> GROKKED (eps={epsilon:.3f} < {self.epsilon_grok})")
                # Compute freeze mask if model provided
                if model is not None:
                    self.frozen_params = self._compute_freeze_snapshot(model)
            elif epsilon > 0.8 and ridge_ratio < 0.5:
                self.phase = Phase.EXPLORE
                print(f"[SGC] Phase transition: TRANSITION -> EXPLORE (structure lost)")
        
        elif self.phase == Phase.GROKKED:
            if epsilon > self.epsilon_ungrok:
                self.phase = Phase.TRANSITION
                print(f"[SGC] Phase transition: GROKKED -> TRANSITION (eps={epsilon:.3f} > {self.epsilon_ungrok})")
                self.frozen_params = None
        
        # Record history
        self.history.append({
            'epsilon': epsilon,
            'ridge_ratio': ridge_ratio,
            'phase': self.phase.value,
            'temperature': self.D[self.phase],
            'cooling': self.lambda_[self.phase],
        })
        
        return ControlActions(
            temperature=self.D[self.phase],
            cooling=self.lambda_[self.phase],
            plasticity_mask=None,  # Simplified: use frozen_params instead
            phase=self.phase,
        )
    
    def _compute_freeze_snapshot(self, model: nn.Module) -> Dict[str, torch.Tensor]:
        """Snapshot parameters for protection."""
        return {name: param.clone().detach() for name, param in model.named_parameters()}
    
    def apply_protection(self, model: nn.Module, alpha: float = 0.5):
        """
        Apply elastic protection toward frozen parameters.
        
        This implements the adiabatic invariant preservation:
        θ_new = θ_current - α * (θ_current - θ_frozen)
        """
        if self.frozen_params is None or self.phase != Phase.GROKKED:
            return
        
        with torch.no_grad():
            for name, param in model.named_parameters():
                if name in self.frozen_params:
                    drift = param - self.frozen_params[name]
                    param.sub_(alpha * drift)
    
    def get_optimizer_params(self, base_lr: float = 1e-3) -> Dict:
        """Get optimizer parameters based on current phase."""
        return {
            'lr': base_lr * self.D[self.phase] / self.D[Phase.EXPLORE],
            'weight_decay': self.lambda_[self.phase],
        }


class PIDController:
    """
    PID Controller on Functional Defect.
    
    Continuously regulates ε toward a target value by modulating temperature D.
    
    Control law:
        D(t) = D₀ + Kp·e(t) + Ki·∫e(τ)dτ + Kd·ė(t)
    
    Where e(t) = ε(t) - ε_target
    """
    
    def __init__(
        self,
        epsilon_target: float = 0.10,
        Kp: float = 0.1,           # Proportional gain
        Ki: float = 0.01,          # Integral gain
        Kd: float = 0.05,          # Derivative gain
        D_base: float = 0.01,      # Baseline temperature
        D_min: float = 0.001,
        D_max: float = 0.05,
        lambda_base: float = 0.5,
        alpha: float = 0.5,        # Cooling-error coupling
    ):
        self.epsilon_target = epsilon_target
        self.Kp = Kp
        self.Ki = Ki
        self.Kd = Kd
        self.D_base = D_base
        self.D_min = D_min
        self.D_max = D_max
        self.lambda_base = lambda_base
        self.alpha = alpha
        
        # State
        self.integral = 0.0
        self.prev_epsilon = 1.0
        self.history: List[Dict] = []
    
    def step(self, epsilon: float, dt: float = 1.0) -> ControlActions:
        """
        One step of PID control.
        
        Args:
            epsilon: Current functional defect
            dt: Time step (in epochs)
        
        Returns:
            ControlActions with computed temperature and cooling
        """
        # Error
        e = epsilon - self.epsilon_target
        
        # Integral with anti-windup
        self.integral += e * dt
        self.integral = np.clip(self.integral, -10.0, 10.0)
        
        # Derivative
        derivative = (epsilon - self.prev_epsilon) / dt
        self.prev_epsilon = epsilon
        
        # PID output
        D = self.D_base + self.Kp * e + self.Ki * self.integral + self.Kd * derivative
        D = np.clip(D, self.D_min, self.D_max)
        
        # Coupled cooling (increase cooling as ε drops)
        lambda_ = self.lambda_base - self.alpha * e
        lambda_ = np.clip(lambda_, 0.1, 1.5)
        
        # Phase classification for reporting
        if epsilon < 0.15:
            phase = Phase.GROKKED
        elif epsilon < 0.5:
            phase = Phase.TRANSITION
        else:
            phase = Phase.EXPLORE
        
        self.history.append({
            'epsilon': epsilon,
            'error': e,
            'integral': self.integral,
            'derivative': derivative,
            'temperature': D,
            'cooling': lambda_,
            'phase': phase.value,
        })
        
        return ControlActions(
            temperature=D,
            cooling=lambda_,
            phase=phase,
        )
    
    def reset(self):
        """Reset controller state."""
        self.integral = 0.0
        self.prev_epsilon = 1.0


class SGCSpikingUnit:
    """
    A single SGC spiking unit with surprise-gated plasticity.
    
    Implements:
    - Leaky integrate-and-fire dynamics
    - Local prediction and surprise computation
    - Surprise-modulated temperature
    - Three-factor plasticity rule
    """
    
    def __init__(
        self,
        n_inputs: int,
        tau_m: float = 20.0,        # Membrane time constant
        tau_p: float = 100.0,       # Prediction time constant
        theta_spike: float = 0.5,   # Spike threshold
        theta_plastic: float = 0.2, # Plasticity threshold
        D_base: float = 0.01,
        D_gain: float = 0.1,
        eta: float = 0.01,          # Learning rate
    ):
        self.n_inputs = n_inputs
        self.tau_m = tau_m
        self.tau_p = tau_p
        self.theta_spike = theta_spike
        self.theta_plastic = theta_plastic
        self.D_base = D_base
        self.D_gain = D_gain
        self.eta = eta
        
        # State
        self.x = 0.0                # Membrane potential
        self.x_hat = 0.0            # Prediction
        self.D = D_base             # Local temperature
        self.w = np.random.randn(n_inputs) * 0.1  # Weights
        
    def surprise(self) -> float:
        """Compute surprise (prediction error)."""
        return abs(self.x - self.x_hat)
    
    def step(self, inputs: np.ndarray, dt: float = 1.0) -> Tuple[bool, float]:
        """
        One time step.
        
        Args:
            inputs: Input spike train from presynaptic units
            dt: Time step
        
        Returns:
            (spike, surprise)
        """
        # Compute surprise BEFORE update
        e = self.surprise()
        
        # Update local temperature
        self.D = self.D_base + self.D_gain * e
        
        # Membrane dynamics with noise
        noise = np.sqrt(2 * self.D * dt) * np.random.randn()
        drive = np.dot(self.w, inputs)
        dx = (-self.x + drive) / self.tau_m
        self.x += dx * dt + noise
        
        # Update prediction (slower)
        self.x_hat += (self.x - self.x_hat) * dt / self.tau_p
        
        # Spike generation
        spike = e > self.theta_spike
        if spike:
            self.x = 0.0  # Reset
        
        # Surprise-gated plasticity
        if e > self.theta_plastic:
            modulator = e - self.theta_plastic
            self.w += self.eta * modulator * inputs
        
        return spike, e


class SGCSpikingNetwork:
    """
    Network of SGC spiking units implementing surprise-gated learning.
    
    This is the "default off, spike on surprise" architecture that naturally
    implements adiabatic invariant preservation and local temperature control.
    """
    
    def __init__(
        self,
        n_input: int,
        n_hidden: int,
        n_output: int,
        **unit_kwargs
    ):
        self.n_input = n_input
        self.n_hidden = n_hidden
        self.n_output = n_output
        
        # Create layers
        self.hidden = [SGCSpikingUnit(n_input, **unit_kwargs) for _ in range(n_hidden)]
        self.output = [SGCSpikingUnit(n_hidden, **unit_kwargs) for _ in range(n_output)]
        
        self.history: List[Dict] = []
    
    def forward(self, inputs: np.ndarray, dt: float = 1.0) -> Tuple[np.ndarray, Dict]:
        """
        Forward pass through network.
        
        Args:
            inputs: Input pattern
            dt: Time step
        
        Returns:
            (output_spikes, metrics)
        """
        # Hidden layer
        hidden_spikes = np.zeros(self.n_hidden)
        hidden_surprise = np.zeros(self.n_hidden)
        for i, unit in enumerate(self.hidden):
            spike, surprise = unit.step(inputs, dt)
            hidden_spikes[i] = float(spike)
            hidden_surprise[i] = surprise
        
        # Output layer
        output_spikes = np.zeros(self.n_output)
        output_surprise = np.zeros(self.n_output)
        for i, unit in enumerate(self.output):
            spike, surprise = unit.step(hidden_spikes, dt)
            output_spikes[i] = float(spike)
            output_surprise[i] = surprise
        
        # Compute metrics
        mean_D_hidden = np.mean([u.D for u in self.hidden])
        mean_D_output = np.mean([u.D for u in self.output])
        
        metrics = {
            'hidden_spike_rate': np.mean(hidden_spikes),
            'output_spike_rate': np.mean(output_spikes),
            'hidden_surprise': np.mean(hidden_surprise),
            'output_surprise': np.mean(output_surprise),
            'hidden_temperature': mean_D_hidden,
            'output_temperature': mean_D_output,
        }
        
        self.history.append(metrics)
        
        return output_spikes, metrics
    
    def compute_functional_defect(self, patterns: List[np.ndarray], labels: List[int]) -> float:
        """
        Compute functional defect over a set of patterns.
        """
        # Collect hidden activations
        activations = []
        for pattern in patterns:
            hidden_spikes = np.array([u.x for u in self.hidden])  # Use membrane potential
            activations.append(hidden_spikes)
        
        activations = np.array(activations)
        labels = np.array(labels)
        
        # Total variance
        total_var = np.var(activations)
        
        # Within-class variance
        within_var = 0.0
        unique_labels = np.unique(labels)
        for c in unique_labels:
            mask = labels == c
            if mask.sum() > 1:
                within_var += np.var(activations[mask]) * mask.sum()
        within_var /= len(labels)
        
        return within_var / (total_var + 1e-10)


def apply_temperature_to_optimizer(optimizer: torch.optim.Optimizer, D: float, base_lr: float = 1e-3):
    """
    Apply temperature control to optimizer.
    
    Maps temperature D to learning rate modulation.
    Higher D = more exploration = higher effective LR.
    """
    # Scale learning rate by temperature
    for param_group in optimizer.param_groups:
        param_group['lr'] = base_lr * (D / 0.01)  # Normalize to D=0.01 baseline


def apply_cooling_to_optimizer(optimizer: torch.optim.Optimizer, lambda_: float):
    """Apply cooling pressure (weight decay) to optimizer."""
    for param_group in optimizer.param_groups:
        param_group['weight_decay'] = lambda_


# =============================================================================
# Demo / Test
# =============================================================================

if __name__ == "__main__":
    print("=" * 60)
    print("SGC Controller Demo")
    print("=" * 60)
    
    # Test Bang-Bang Controller
    print("\n1. Bang-Bang Controller Simulation")
    print("-" * 40)
    
    controller = BangBangController()
    
    # Simulate a grokking trajectory
    trajectory = [
        (1.0, 0.5),   # Start: high defect, no ridges
        (0.9, 0.6),
        (0.8, 0.8),
        (0.7, 1.1),   # Ridge detected -> TRANSITION
        (0.5, 2.0),
        (0.3, 4.0),
        (0.15, 6.0),  # Grokked!
        (0.10, 8.0),
        (0.08, 10.0),
    ]
    
    for epsilon, R in trajectory:
        actions = controller.step(epsilon, R)
        print(f"eps={epsilon:.2f}, R={R:.1f} -> {actions.phase.value:12s} D={actions.temperature:.3f} wd={actions.cooling:.1f}")
    
    # Test PID Controller
    print("\n2. PID Controller Simulation")
    print("-" * 40)
    
    pid = PIDController(epsilon_target=0.10)
    
    for epsilon, _ in trajectory:
        actions = pid.step(epsilon)
        print(f"eps={epsilon:.2f} -> D={actions.temperature:.4f} wd={actions.cooling:.2f}")
    
    # Test Spiking Network
    print("\n3. SGC Spiking Network")
    print("-" * 40)
    
    net = SGCSpikingNetwork(n_input=10, n_hidden=20, n_output=5)
    
    # Run a few steps
    for t in range(5):
        inputs = np.random.randn(10)
        outputs, metrics = net.forward(inputs)
        print(f"t={t}: spike_rate={metrics['hidden_spike_rate']:.2f}, "
              f"surprise={metrics['hidden_surprise']:.3f}, "
              f"temp={metrics['hidden_temperature']:.4f}")
    
    print("\n" + "=" * 60)
    print("SGC Controller ready for integration with grokking experiments.")
    print("See docs/SGC_CONTROL_ARCHITECTURE.md for full specification.")
    print("=" * 60)
