"""
SGC Active Inference Controller: Unified Theory Implementation

This controller unifies:
1. SGC (defect, exploration mass, kappa)
2. Active Inference (free energy minimization, Markov blanket)
3. Continual Learning (stability-plasticity balance)
4. Smooth Cooling (gradual blanket formation)

The core principle:
- Monitor blanket quality (defect) and certainty (entropy)
- Adjust exploration/consolidation to minimize meta-free-energy
- Protect learned structure while allowing new learning

Author: SGC Research Team
Date: February 4, 2026
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
import numpy as np
import math
from dataclasses import dataclass, field
from typing import Tuple, List, Dict, Optional
from collections import deque


@dataclass
class ActiveInferenceState:
    """
    The observable state for active inference control.
    
    This captures the inner/outer world dynamics:
    - Inside: coarse representation (what the model "knows")
    - Blanket: the projection operator (what the model "attends to")
    - Outside: the tail/residual (what the model "ignores")
    """
    epoch: int = 0
    
    # Free Energy components (what we minimize)
    defect: float = 1.0              # Blanket leakage (prediction error)
    entropy: float = 1.0             # Uncertainty (complexity cost)
    free_energy: float = 2.0         # Combined (defect + entropy)
    
    # Velocities (rate of change)
    defect_velocity: float = 0.0
    entropy_velocity: float = 0.0
    free_energy_velocity: float = 0.0
    
    # Derived states
    consolidation: float = 0.0       # 1 - entropy (certainty)
    blanket_quality: float = 0.0     # 1 - defect (tightness)
    
    # Phase detection
    phase: str = 'explore'           # explore, crystallize, stable, recover
    blanket_closed: bool = False
    grokking_detected: bool = False
    
    # Accuracy (external validation, not used for control)
    train_acc: float = 0.0
    test_acc: float = 0.0


@dataclass
class ActiveInferenceController:
    """
    Controller that implements active inference for learning.
    
    The control loop:
    1. Observe: measure defect, entropy, their velocities
    2. Infer: estimate blanket quality and learning phase
    3. Act: adjust noise (exploration) and WD (consolidation)
    4. Learn: the model updates, changing the observations
    
    This creates a closed loop where the controller and model co-evolve.
    """
    
    # Temperature (exploration intensity)
    T_max: float = 0.15
    T_min: float = 0.001
    T_current: float = 0.15
    
    # Weight decay (consolidation pressure)
    wd_min: float = 0.1
    wd_max: float = 1.5
    wd_current: float = 0.1
    
    # Thresholds for phase detection
    defect_closure_threshold: float = 0.15
    consolidation_threshold: float = 0.5
    spurious_certainty_threshold: float = 0.2
    
    # Cooling parameters
    tau_explore: float = 5000.0      # Slow cooling during exploration
    tau_crystallize: float = 500.0   # Fast cooling during crystallization
    tau_recover: float = -500.0      # Negative = heating
    
    # State
    state: ActiveInferenceState = field(default_factory=ActiveInferenceState)
    state_history: List[ActiveInferenceState] = field(default_factory=list)
    
    # History for velocity computation
    defect_history: deque = field(default_factory=lambda: deque(maxlen=20))
    entropy_history: deque = field(default_factory=lambda: deque(maxlen=20))
    
    # EMAs
    defect_ema: float = 1.0
    entropy_ema: float = 1.0
    ema_alpha: float = 0.15
    
    # Detection events
    blanket_closure_epoch: int = -1
    grokking_epoch: int = -1
    
    # Exploration mass tracking
    M_nominal: float = 0.0
    
    def update(self, 
               epoch: int,
               defect: float,
               entropy_normalized: float,
               train_acc: float = 0.0,
               test_acc: float = 0.0) -> Tuple[float, float, str]:
        """
        Update controller with new observations.
        
        Args:
            epoch: Current epoch
            defect: Measured blanket leakage
            entropy_normalized: Normalized output entropy
            train_acc: Training accuracy (for logging only)
            test_acc: Test accuracy (for logging only)
        
        Returns:
            (noise_scale, weight_decay, phase_name)
        """
        # Update EMAs
        self.defect_ema = self.ema_alpha * defect + (1 - self.ema_alpha) * self.defect_ema
        self.entropy_ema = self.ema_alpha * entropy_normalized + (1 - self.ema_alpha) * self.entropy_ema
        
        # Store in history for velocity
        self.defect_history.append(defect)
        self.entropy_history.append(entropy_normalized)
        
        # Compute velocities
        defect_velocity = self._compute_velocity(self.defect_history)
        entropy_velocity = self._compute_velocity(self.entropy_history)
        
        # Compute free energy (simplified: defect + entropy)
        free_energy = self.defect_ema + self.entropy_ema
        free_energy_velocity = defect_velocity + entropy_velocity
        
        # Update state
        self.state = ActiveInferenceState(
            epoch=epoch,
            defect=self.defect_ema,
            entropy=self.entropy_ema,
            free_energy=free_energy,
            defect_velocity=defect_velocity,
            entropy_velocity=entropy_velocity,
            free_energy_velocity=free_energy_velocity,
            consolidation=1.0 - self.entropy_ema,
            blanket_quality=1.0 - self.defect_ema,
            train_acc=train_acc,
            test_acc=test_acc,
        )
        
        # Determine phase
        phase = self._determine_phase()
        self.state.phase = phase
        
        # Check for blanket closure
        if self.defect_ema < self.defect_closure_threshold:
            self.state.blanket_closed = True
            if self.blanket_closure_epoch < 0:
                self.blanket_closure_epoch = epoch
                print(f"\n*** BLANKET CLOSURE at epoch {epoch} ***")
                print(f"    defect = {self.defect_ema:.4f}")
        
        # Check for grokking (blanket closed + consolidated) - only once
        if (self.state.blanket_closed and 
            self.state.consolidation > self.consolidation_threshold and
            self.grokking_epoch < 0):  # Only detect once
            self.state.grokking_detected = True
            self.grokking_epoch = epoch
            print(f"\n*** GROKKING DETECTED (intrinsic) at epoch {epoch} ***")
            print(f"    defect = {self.defect_ema:.4f}")
            print(f"    consolidation = {self.state.consolidation:.3f}")
        elif self.grokking_epoch > 0:
            self.state.grokking_detected = True  # Keep flag set
        
        # Compute control outputs based on phase
        noise, wd = self._compute_control(phase)
        
        # Store history
        self.state_history.append(self.state)
        
        return noise, wd, phase
    
    def _compute_velocity(self, history: deque) -> float:
        """Compute velocity (rate of change) from history."""
        if len(history) < 2:
            return 0.0
        vals = list(history)
        return (vals[-1] - vals[0]) / len(vals)
    
    def _determine_phase(self) -> str:
        """Determine the current learning phase based on state."""
        
        # Already grokked - stay stable
        if self.state.grokking_detected:
            return 'stable'
        
        # Spurious certainty: confident but leaky blanket
        if (self.state.consolidation > self.consolidation_threshold and
            self.defect_ema > self.spurious_certainty_threshold):
            return 'recover'  # Need to re-explore
        
        # Blanket closing and consolidation rising - crystallizing
        if (self.state.defect_velocity < -0.001 and
            self.state.consolidation > 0.3):
            return 'crystallize'
        
        # Default: still exploring
        return 'explore'
    
    def _compute_control(self, phase: str) -> Tuple[float, float]:
        """Compute noise and WD based on phase."""
        
        if phase == 'stable':
            # Minimal perturbation, moderate consolidation
            noise = self.T_min
            wd = 1.0
        
        elif phase == 'recover':
            # Re-heat: increase exploration, reduce consolidation
            self.T_current = min(self.T_max, self.T_current * 1.3)
            noise = self.T_current
            wd = self.wd_min
        
        elif phase == 'crystallize':
            # Fast cooling: accelerate toward stability
            self.T_current = self._cool(self.tau_crystallize)
            noise = self.T_current
            wd = self._interpolate_wd()
        
        else:  # explore
            # Slow cooling: maintain exploration
            self.T_current = self._cool(self.tau_explore)
            noise = self.T_current
            wd = self.wd_min
        
        self.wd_current = wd
        return noise, wd
    
    def _cool(self, tau: float) -> float:
        """Apply exponential cooling/heating."""
        if tau > 0:
            # Cooling
            decay = math.exp(-1.0 / tau)
            new_T = self.T_min + (self.T_current - self.T_min) * decay
        else:
            # Heating (negative tau)
            growth = math.exp(1.0 / abs(tau))
            new_T = min(self.T_max, self.T_current * growth)
        return max(self.T_min, min(self.T_max, new_T))
    
    def _interpolate_wd(self) -> float:
        """Interpolate WD based on temperature."""
        t_norm = (self.T_current - self.T_min) / (self.T_max - self.T_min + 1e-10)
        return self.wd_min + (1 - t_norm) * (self.wd_max - self.wd_min)
    
    def inject_noise(self, model: nn.Module, noise_scale: float):
        """Inject noise into model parameters."""
        if noise_scale < 1e-6:
            return
        
        with torch.no_grad():
            for param in model.parameters():
                if param.dim() >= 2:
                    noise = torch.randn_like(param) * noise_scale
                    param.add_(noise)
        
        self.M_nominal += noise_scale
    
    def get_summary(self) -> Dict:
        """Get summary statistics."""
        return {
            'blanket_closure_epoch': self.blanket_closure_epoch,
            'grokking_epoch': self.grokking_epoch,
            'final_defect': self.state.defect,
            'final_entropy': self.state.entropy,
            'final_consolidation': self.state.consolidation,
            'final_temperature': self.T_current,
            'M_nominal': self.M_nominal,
            'history_length': len(self.state_history),
        }


# ═══════════════════════════════════════════════════════════════════════════════
# TEST
# ═══════════════════════════════════════════════════════════════════════════════

def test_active_inference_controller():
    """Test the active inference controller with simulated trajectory."""
    print("=" * 70)
    print("Testing Active Inference Controller")
    print("=" * 70)
    
    controller = ActiveInferenceController()
    
    np.random.seed(42)
    
    print(f"\n{'Epoch':>6} | {'Defect':>7} | {'Entropy':>7} | {'FE':>6} | {'Phase':>11} | {'Temp':>8} | {'WD':>5}")
    print("-" * 70)
    
    for epoch in range(1, 501):
        # Simulate trajectory
        if epoch < 200:
            defect = 0.5 + 0.1 * np.random.randn()
            entropy = 0.9 + 0.05 * np.random.randn()
        elif epoch < 350:
            defect = 0.5 - 0.002 * (epoch - 200) + 0.05 * np.random.randn()
            entropy = 0.9 - 0.002 * (epoch - 200) + 0.03 * np.random.randn()
        else:
            defect = max(0.05, 0.2 - 0.001 * (epoch - 350) + 0.02 * np.random.randn())
            entropy = max(0.1, 0.6 - 0.003 * (epoch - 350) + 0.02 * np.random.randn())
        
        defect = max(0.01, min(1.0, defect))
        entropy = max(0.01, min(1.0, entropy))
        
        noise, wd, phase = controller.update(epoch, defect, entropy)
        
        if epoch % 50 == 0 or epoch == 1:
            state = controller.state
            print(f"{epoch:6d} | {state.defect:7.4f} | {state.entropy:7.3f} | "
                  f"{state.free_energy:6.3f} | {phase:>11} | {noise:8.5f} | {wd:5.2f}")
    
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    summary = controller.get_summary()
    for k, v in summary.items():
        print(f"  {k}: {v}")


if __name__ == "__main__":
    test_active_inference_controller()
