"""
Smooth Cooling Controller: Universe Cooling Analogy

Instead of abrupt phase transitions, this implements gradual noise reduction
driven by observable signals (entropy, defect, consolidation).

The principle:
- Early: High noise fills geometric gaps, explores configuration space
- Middle: Noise gradually reduces as structure emerges (blanket forms)
- Late: Low noise allows world model to crystallize

The key insight: The world should come into focus as a persistent, predictable signal.
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
import numpy as np
import math
from dataclasses import dataclass, field
from typing import Tuple, List, Optional
from collections import deque


@dataclass
class CoolingState:
    """Observable state for cooling decisions."""
    epoch: int = 0
    
    # Entropy-extropy (uncertainty vs certainty)
    entropy: float = 1.0           # H(p) normalized
    entropy_velocity: float = 0.0  # dH/dt (KL divergence)
    consolidation: float = 0.0     # 1 - entropy (certainty)
    
    # Defect (blanket quality)
    defect: float = 1.0            # epsilon (inside-outside leakage)
    defect_velocity: float = 0.0   # d(defect)/dt
    
    # Accuracy (ground truth)
    train_acc: float = 0.0
    test_acc: float = 0.0
    
    # Derived signals
    blanket_forming: bool = False      # consolidation up + defect down
    spurious_certainty: bool = False   # consolidation up + defect stable
    exploration_needed: bool = True    # entropy high + defect high
    
    def update_signals(self):
        """Compute derived signals from raw observables."""
        # Blanket is forming when certainty rises AND defect falls
        self.blanket_forming = (
            self.consolidation > 0.4 and 
            self.defect < 0.2 and 
            self.defect_velocity < 0
        )
        
        # Spurious certainty: confident but wrong (blanket has holes)
        self.spurious_certainty = (
            self.consolidation > 0.5 and
            self.defect > 0.15
        )
        
        # Need more exploration when uncertain and blanket leaky
        self.exploration_needed = (
            self.entropy > 0.5 or
            self.defect > 0.3
        )


@dataclass  
class SmoothCoolingController:
    """
    Controller implementing gradual cooling with adaptive feedback.
    
    Key principles:
    1. Start hot (high noise) to explore geometric gaps
    2. Cool gradually as structure emerges (blanket forms)
    3. Accelerate cooling when defect drops (good blanket)
    4. Re-heat if spurious certainty detected (leaky blanket)
    """
    
    # Temperature bounds
    T_max: float = 0.15        # Maximum noise scale (hot)
    T_min: float = 0.001       # Minimum noise scale (cold)
    T_current: float = 0.15    # Current temperature
    
    # Cooling rate parameters
    tau_base: float = 2000.0   # Base cooling time constant
    tau_min: float = 500.0     # Minimum (fast cooling when blanket good)
    tau_max: float = 5000.0    # Maximum (slow cooling when exploring)
    
    # Weight decay (consolidation pressure)
    wd_min: float = 0.1
    wd_max: float = 1.5
    wd_current: float = 0.1
    
    # State tracking
    state: CoolingState = field(default_factory=CoolingState)
    temperature_history: List[Tuple[int, float]] = field(default_factory=list)
    
    # Grokking detection
    grokking_achieved: bool = False
    grokking_epoch: int = -1
    grokking_threshold: float = 0.95
    
    # EMA smoothing
    ema_alpha: float = 0.1
    prev_entropy: float = 1.0
    prev_defect: float = 1.0
    
    def update(self, 
               epoch: int,
               entropy_normalized: float,
               defect: float,
               train_acc: float,
               test_acc: float) -> Tuple[float, float, str]:
        """
        Update controller with new observations.
        
        Returns: (noise_scale, weight_decay, phase_name)
        """
        # Update velocities (rate of change)
        entropy_velocity = entropy_normalized - self.prev_entropy
        defect_velocity = defect - self.prev_defect
        
        # Update state
        self.state.epoch = epoch
        self.state.entropy = entropy_normalized
        self.state.entropy_velocity = entropy_velocity
        self.state.consolidation = 1.0 - entropy_normalized
        self.state.defect = defect
        self.state.defect_velocity = defect_velocity
        self.state.train_acc = train_acc
        self.state.test_acc = test_acc
        self.state.update_signals()
        
        # Store previous values
        self.prev_entropy = entropy_normalized
        self.prev_defect = defect
        
        # Check for grokking
        if test_acc >= self.grokking_threshold and not self.grokking_achieved:
            self.grokking_achieved = True
            self.grokking_epoch = epoch
            print(f"\n*** GROKKING at epoch {epoch} (test={test_acc*100:.1f}%) ***")
            print(f"    Freezing temperature at T={self.T_current:.4f}")
        
        # Determine phase and compute temperature
        if self.grokking_achieved:
            phase = 'frozen'
            # Keep current low temperature, don't perturb
            noise = self.T_current * 0.1  # Very low maintenance noise
            wd = 1.0  # Moderate consolidation
        
        elif self.state.spurious_certainty:
            phase = 'reheat'
            # Model is confident but wrong - need to explore more
            self.T_current = min(self.T_max, self.T_current * 1.5)
            noise = self.T_current
            wd = self.wd_min  # Reduce consolidation pressure
        
        elif self.state.blanket_forming:
            phase = 'crystallize'
            # Blanket is forming - accelerate cooling
            tau_effective = self.tau_min  # Fast cooling
            self.T_current = self._cool(tau_effective)
            noise = self.T_current
            # Increase WD as we cool
            wd = self._interpolate_wd()
        
        elif self.state.exploration_needed:
            phase = 'explore'
            # Still need to explore - slow cooling or maintain
            tau_effective = self.tau_max  # Slow cooling
            self.T_current = self._cool(tau_effective)
            noise = self.T_current
            wd = self.wd_min
        
        else:
            phase = 'cooling'
            # Normal cooling
            tau_effective = self.tau_base
            self.T_current = self._cool(tau_effective)
            noise = self.T_current
            wd = self._interpolate_wd()
        
        # Record history
        self.temperature_history.append((epoch, self.T_current))
        self.wd_current = wd
        
        return noise, wd, phase
    
    def _cool(self, tau: float) -> float:
        """Apply exponential cooling toward T_min."""
        # T(t+1) = T_min + (T(t) - T_min) * exp(-1/tau)
        decay = math.exp(-1.0 / tau)
        new_T = self.T_min + (self.T_current - self.T_min) * decay
        return max(self.T_min, new_T)
    
    def _interpolate_wd(self) -> float:
        """Interpolate WD based on temperature (cold = high WD)."""
        # Normalize temperature to [0, 1] range
        t_norm = (self.T_current - self.T_min) / (self.T_max - self.T_min + 1e-10)
        # Invert: high temp = low WD, low temp = high WD
        return self.wd_min + (1 - t_norm) * (self.wd_max - self.wd_min)
    
    def get_summary(self) -> dict:
        """Get summary statistics."""
        return {
            'final_temperature': self.T_current,
            'final_wd': self.wd_current,
            'grokking_epoch': self.grokking_epoch,
            'grokking_achieved': self.grokking_achieved,
            'temperature_history_len': len(self.temperature_history),
        }


def compute_entropy_from_logits(logits: torch.Tensor) -> float:
    """Compute normalized entropy from model output logits."""
    probs = F.softmax(logits, dim=-1)
    # Aggregate across batch
    mean_probs = probs.mean(dim=0)
    # Entropy
    H = -(mean_probs * torch.log(mean_probs + 1e-10)).sum().item()
    # Normalize by max entropy
    n_classes = logits.size(-1)
    H_max = math.log(n_classes)
    return H / H_max


def compute_defect_from_hidden(hidden: torch.Tensor, k: int = None) -> float:
    """
    Compute defect as inside-outside leakage.
    
    Defect = how much of the representation is in the tail (outside blanket).
    """
    # SVD of hidden representations
    _, S, _ = torch.linalg.svd(hidden, full_matrices=False)
    S2 = S ** 2
    total = S2.sum().item()
    
    if total < 1e-10:
        return 1.0
    
    # Auto-select k based on 90% energy
    if k is None:
        cumsum = torch.cumsum(S2, dim=0)
        k = (cumsum < 0.9 * total).sum().item() + 1
        k = max(1, min(k, len(S) - 1))
    
    # Defect = tail energy / total energy
    tail_energy = S2[k:].sum().item()
    return math.sqrt(tail_energy / total)


# ═══════════════════════════════════════════════════════════════════════════════
# TEST
# ═══════════════════════════════════════════════════════════════════════════════

def test_cooling_controller():
    """Test the smooth cooling controller with simulated data."""
    print("=" * 60)
    print("Testing Smooth Cooling Controller")
    print("=" * 60)
    
    controller = SmoothCoolingController()
    
    # Simulate training trajectory
    scenarios = [
        # (epoch, entropy, defect, train_acc, test_acc, expected_phase)
        (1, 0.99, 0.8, 0.02, 0.01, 'explore'),      # Early: uncertain, leaky blanket
        (500, 0.85, 0.5, 0.30, 0.05, 'explore'),    # Still exploring
        (1000, 0.70, 0.3, 0.60, 0.10, 'cooling'),   # Starting to cool
        (2000, 0.50, 0.15, 0.85, 0.30, 'crystallize'),  # Blanket forming
        (3000, 0.30, 0.08, 0.95, 0.70, 'crystallize'),  # Good blanket
        (4000, 0.15, 0.05, 0.99, 0.98, 'frozen'),   # Grokking achieved
    ]
    
    print(f"\n{'Epoch':>6} | {'Entropy':>7} | {'Defect':>6} | {'Test':>5} | {'Temp':>8} | {'WD':>5} | Phase")
    print("-" * 60)
    
    for epoch, entropy, defect, train_acc, test_acc, expected in scenarios:
        noise, wd, phase = controller.update(epoch, entropy, defect, train_acc, test_acc)
        print(f"{epoch:6d} | {entropy:7.3f} | {defect:6.3f} | {test_acc*100:5.1f}% | {noise:8.5f} | {wd:5.2f} | {phase}")
    
    print("\n" + "=" * 60)
    print("Smooth Cooling Controller Test Complete")
    print("=" * 60)
    
    summary = controller.get_summary()
    print(f"\nGrokking at epoch: {summary['grokking_epoch']}")
    print(f"Final temperature: {summary['final_temperature']:.6f}")


if __name__ == "__main__":
    test_cooling_controller()
