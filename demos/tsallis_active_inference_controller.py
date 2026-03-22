"""
Tsallis-Generalized Active Inference Controller

Upgrades the SGC controller to use q-generalized entropy for non-extensive regimes.

Key insight: During learning, the system exhibits complex, heavy-tailed dynamics
(long-range correlations, non-ergodic behavior). Shannon entropy assumes
extensivity which may not hold. Tsallis entropy S_q is designed for this.

The upgrade:
- Replace Shannon H(p) with Tsallis S_q(p)
- Replace KL velocity with q-divergence velocity
- Allow q to adapt: q > 1 during exploration, q -> 1 as system stabilizes

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


# ═══════════════════════════════════════════════════════════════════════════════
# TSALLIS ENTROPY FUNCTIONS
# ═══════════════════════════════════════════════════════════════════════════════

def tsallis_entropy(probs: torch.Tensor, q: float = 1.5) -> float:
    """
    Compute Tsallis entropy S_q(p) = (1 - sum(p_i^q)) / (q - 1)
    
    - q = 1: Shannon entropy (limit)
    - q > 1: sub-additive, emphasizes dominant states
    - q < 1: super-additive, emphasizes rare events
    """
    probs = probs.clamp(min=1e-10)
    if abs(q - 1.0) < 1e-6:
        return -(probs * torch.log(probs)).sum().item()
    return ((1 - (probs ** q).sum()) / (q - 1)).item()


def tsallis_entropy_normalized(probs: torch.Tensor, q: float = 1.5) -> float:
    """Normalized Tsallis entropy in [0, 1]."""
    n = probs.numel()
    S_q = tsallis_entropy(probs, q)
    if abs(q - 1.0) < 1e-6:
        S_q_max = math.log(n)
    else:
        S_q_max = (1 - n ** (1 - q)) / (q - 1)
    return S_q / (S_q_max + 1e-10)


def tsallis_divergence(p: torch.Tensor, r: torch.Tensor, q: float = 1.5) -> float:
    """
    Tsallis relative entropy (q-divergence).
    Reduces to KL divergence as q -> 1.
    """
    p = p.clamp(min=1e-10)
    r = r.clamp(min=1e-10)
    if abs(q - 1.0) < 1e-6:
        return (p * torch.log(p / r)).sum().item()
    return (((p ** q) * (r ** (1 - q))).sum() - 1) / (q - 1)


def estimate_q_from_tail(values: torch.Tensor, baseline_q: float = 1.5) -> float:
    """
    Estimate appropriate q from tail heaviness of a distribution.
    
    Heavy tails (high kurtosis) -> q > 1
    Light tails -> q closer to 1
    
    This allows the entropic index to adapt to the current regime.
    """
    if values.numel() < 10:
        return baseline_q
    
    # Compute excess kurtosis (0 for Gaussian)
    mean = values.mean()
    std = values.std() + 1e-10
    z = (values - mean) / std
    kurtosis = (z ** 4).mean().item() - 3  # Excess kurtosis
    
    # Map kurtosis to q: higher kurtosis -> higher q
    # Gaussian (kurtosis=0) -> q=1
    # Heavy tails (kurtosis>0) -> q>1
    q = 1.0 + 0.1 * max(0, min(5, kurtosis))  # Clamp to [1.0, 1.5]
    
    return q


# ═══════════════════════════════════════════════════════════════════════════════
# TSALLIS ACTIVE INFERENCE CONTROLLER
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class TsallisState:
    """Observable state with Tsallis-generalized entropy."""
    epoch: int = 0
    
    # Defect (blanket leakage)
    defect: float = 1.0
    closure_defect: float = 1.0  # Proper ||Pi g(h) - Pi g(Pi h)||
    defect_velocity: float = 0.0
    
    # Tsallis entropy
    q: float = 1.5                # Current entropic index
    S_q: float = 1.0              # Tsallis entropy
    S_q_normalized: float = 1.0   # Normalized to [0, 1]
    D_q_velocity: float = 0.0     # q-divergence velocity
    
    # Derived
    consolidation_q: float = 0.0  # 1 - S_q_normalized
    free_energy_q: float = 2.0    # defect + S_q_normalized
    
    # Phase detection
    phase: str = 'explore'
    blanket_closed: bool = False
    grokking_detected: bool = False


@dataclass 
class TsallisActiveInferenceController:
    """
    Controller using Tsallis-generalized entropy for non-extensive regimes.
    
    Key differences from Shannon-based controller:
    1. Uses S_q instead of H for uncertainty
    2. Uses D_q instead of KL for velocity
    3. Adapts q based on tail diagnostics (or anneals q -> 1)
    """
    
    # Temperature
    T_max: float = 0.15
    T_min: float = 0.001
    T_current: float = 0.15
    
    # Weight decay
    wd_min: float = 0.1
    wd_max: float = 1.5
    wd_current: float = 0.1
    
    # Tsallis parameter
    q_initial: float = 1.5        # Start with non-extensive
    q_stable: float = 1.0         # Anneal toward Shannon
    q_current: float = 1.5
    q_anneal_rate: float = 0.001  # How fast q -> 1
    adaptive_q: bool = False      # Learn q from tail diagnostics
    
    # Thresholds
    defect_closure_threshold: float = 0.15
    consolidation_threshold: float = 0.5
    spurious_certainty_threshold: float = 0.2
    
    # Cooling
    tau_explore: float = 5000.0
    tau_crystallize: float = 500.0
    
    # State
    state: TsallisState = field(default_factory=TsallisState)
    state_history: List[TsallisState] = field(default_factory=list)
    
    # History for velocities
    defect_history: deque = field(default_factory=lambda: deque(maxlen=20))
    prob_history: deque = field(default_factory=lambda: deque(maxlen=5))
    
    # EMAs
    defect_ema: float = 1.0
    S_q_ema: float = 1.0
    ema_alpha: float = 0.15
    
    # Detection events (with hysteresis)
    blanket_closure_epoch: int = -1
    grokking_epoch: int = -1
    last_print_epoch: int = -1
    closure_count: int = 0       # Consecutive epochs below threshold
    closure_required: int = 5    # Require N consecutive for detection
    
    # Exploration mass
    M_nominal: float = 0.0
    
    def update(self,
               epoch: int,
               defect: float,
               output_probs: torch.Tensor,
               closure_defect: Optional[float] = None,
               logit_gaps: Optional[torch.Tensor] = None) -> Tuple[float, float, str]:
        """
        Update controller with new observations.
        
        Args:
            epoch: Current epoch
            defect: Tail energy defect
            output_probs: Output probability distribution
            closure_defect: Proper closure defect (if computed)
            logit_gaps: Logit gaps for tail diagnostics (optional)
        
        Returns:
            (noise_scale, weight_decay, phase_name)
        """
        # Adapt q if requested
        if self.adaptive_q and logit_gaps is not None:
            self.q_current = estimate_q_from_tail(logit_gaps, self.q_initial)
        
        # Compute Tsallis entropy
        S_q = tsallis_entropy(output_probs, self.q_current)
        S_q_norm = tsallis_entropy_normalized(output_probs, self.q_current)
        
        # Compute q-divergence velocity
        if len(self.prob_history) > 0:
            prev_probs = self.prob_history[-1]
            D_q_velocity = tsallis_divergence(output_probs, prev_probs, self.q_current)
        else:
            D_q_velocity = 0.0
        
        self.prob_history.append(output_probs.detach().clone())
        
        # Update EMAs
        self.defect_ema = self.ema_alpha * defect + (1 - self.ema_alpha) * self.defect_ema
        self.S_q_ema = self.ema_alpha * S_q_norm + (1 - self.ema_alpha) * self.S_q_ema
        
        # Defect velocity
        self.defect_history.append(defect)
        defect_velocity = self._compute_velocity(self.defect_history)
        
        # Update state
        self.state = TsallisState(
            epoch=epoch,
            defect=self.defect_ema,
            closure_defect=closure_defect if closure_defect is not None else self.defect_ema,
            defect_velocity=defect_velocity,
            q=self.q_current,
            S_q=S_q,
            S_q_normalized=self.S_q_ema,
            D_q_velocity=D_q_velocity,
            consolidation_q=1.0 - self.S_q_ema,
            free_energy_q=self.defect_ema + self.S_q_ema,
        )
        
        # Determine phase
        phase = self._determine_phase()
        self.state.phase = phase
        
        # Check for blanket closure with hysteresis
        self._check_blanket_closure(epoch)
        
        # Check for grokking
        self._check_grokking(epoch)
        
        # Anneal q toward 1 during crystallization/stable
        if phase in ['crystallize', 'stable']:
            self.q_current = max(self.q_stable, 
                                 self.q_current - self.q_anneal_rate)
        
        # Compute control
        noise, wd = self._compute_control(phase)
        
        self.state_history.append(self.state)
        return noise, wd, phase
    
    def _compute_velocity(self, history: deque) -> float:
        if len(history) < 2:
            return 0.0
        vals = list(history)
        return (vals[-1] - vals[0]) / len(vals)
    
    def _check_blanket_closure(self, epoch: int):
        """Check blanket closure with hysteresis (require consecutive epochs)."""
        if self.defect_ema < self.defect_closure_threshold:
            self.closure_count += 1
            if self.closure_count >= self.closure_required:
                self.state.blanket_closed = True
                if self.blanket_closure_epoch < 0:
                    self.blanket_closure_epoch = epoch
                    if epoch != self.last_print_epoch:
                        print(f"\n*** BLANKET CLOSURE at epoch {epoch} ***")
                        print(f"    defect = {self.defect_ema:.4f}, q = {self.q_current:.3f}")
                        self.last_print_epoch = epoch
        else:
            # Hysteresis: require higher threshold to re-open
            if self.defect_ema > self.defect_closure_threshold * 1.5:
                self.closure_count = 0
                self.state.blanket_closed = False
    
    def _check_grokking(self, epoch: int):
        """Check for intrinsic grokking detection."""
        if (self.state.blanket_closed and
            self.state.consolidation_q > self.consolidation_threshold and
            self.grokking_epoch < 0):
            
            self.state.grokking_detected = True
            self.grokking_epoch = epoch
            if epoch != self.last_print_epoch:
                print(f"\n*** GROKKING DETECTED (intrinsic) at epoch {epoch} ***")
                print(f"    defect = {self.defect_ema:.4f}")
                print(f"    consolidation_q = {self.state.consolidation_q:.3f}")
                print(f"    q = {self.q_current:.3f}")
                self.last_print_epoch = epoch
        elif self.grokking_epoch > 0:
            self.state.grokking_detected = True
    
    def _determine_phase(self) -> str:
        if self.state.grokking_detected:
            return 'stable'
        
        # Spurious certainty
        if (self.state.consolidation_q > self.consolidation_threshold and
            self.defect_ema > self.spurious_certainty_threshold):
            return 'recover'
        
        # Crystallizing
        if (self.state.defect_velocity < -0.001 and
            self.state.consolidation_q > 0.3):
            return 'crystallize'
        
        return 'explore'
    
    def _compute_control(self, phase: str) -> Tuple[float, float]:
        if phase == 'stable':
            return self.T_min, 1.0
        elif phase == 'recover':
            self.T_current = min(self.T_max, self.T_current * 1.3)
            return self.T_current, self.wd_min
        elif phase == 'crystallize':
            self.T_current = self._cool(self.tau_crystallize)
            return self.T_current, self._interpolate_wd()
        else:  # explore
            self.T_current = self._cool(self.tau_explore)
            return self.T_current, self.wd_min
    
    def _cool(self, tau: float) -> float:
        decay = math.exp(-1.0 / tau)
        new_T = self.T_min + (self.T_current - self.T_min) * decay
        return max(self.T_min, min(self.T_max, new_T))
    
    def _interpolate_wd(self) -> float:
        t_norm = (self.T_current - self.T_min) / (self.T_max - self.T_min + 1e-10)
        return self.wd_min + (1 - t_norm) * (self.wd_max - self.wd_min)
    
    def inject_noise(self, model: nn.Module, noise_scale: float):
        if noise_scale < 1e-6:
            return
        with torch.no_grad():
            for param in model.parameters():
                if param.dim() >= 2:
                    param.add_(torch.randn_like(param) * noise_scale)
        self.M_nominal += noise_scale
    
    def get_summary(self) -> Dict:
        return {
            'blanket_closure_epoch': self.blanket_closure_epoch,
            'grokking_epoch': self.grokking_epoch,
            'final_defect': self.state.defect,
            'final_S_q': self.state.S_q_normalized,
            'final_q': self.q_current,
            'final_consolidation_q': self.state.consolidation_q,
            'M_nominal': self.M_nominal,
        }


# ═══════════════════════════════════════════════════════════════════════════════
# TEST
# ═══════════════════════════════════════════════════════════════════════════════

def test_tsallis_controller():
    """Test the Tsallis active inference controller."""
    print("=" * 70)
    print("Testing Tsallis Active Inference Controller")
    print("=" * 70)
    
    controller = TsallisActiveInferenceController()
    
    np.random.seed(42)
    torch.manual_seed(42)
    
    print(f"\n{'Epoch':>6} | {'Defect':>7} | {'S_q':>6} | {'q':>5} | {'Phase':>11} | {'Temp':>8}")
    print("-" * 65)
    
    n_classes = 97
    
    for epoch in range(1, 501):
        # Simulate trajectory
        if epoch < 200:
            defect = 0.5 + 0.1 * np.random.randn()
            # High entropy (near uniform)
            probs = torch.softmax(torch.randn(n_classes) * 0.5, dim=0)
        elif epoch < 350:
            defect = 0.5 - 0.002 * (epoch - 200) + 0.05 * np.random.randn()
            # Gradually sharpening
            logits = torch.randn(n_classes)
            logits[42] += 0.02 * (epoch - 200)  # One class becoming dominant
            probs = torch.softmax(logits, dim=0)
        else:
            defect = max(0.05, 0.2 - 0.001 * (epoch - 350) + 0.02 * np.random.randn())
            # Sharp (peaked) distribution
            logits = torch.randn(n_classes) * 0.1
            logits[42] = 5.0 + 0.01 * (epoch - 350)
            probs = torch.softmax(logits, dim=0)
        
        defect = max(0.01, min(1.0, defect))
        
        noise, wd, phase = controller.update(epoch, defect, probs)
        
        if epoch % 50 == 0 or epoch == 1:
            state = controller.state
            print(f"{epoch:6d} | {state.defect:7.4f} | {state.S_q_normalized:6.3f} | "
                  f"{state.q:5.3f} | {phase:>11} | {noise:8.5f}")
    
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    for k, v in controller.get_summary().items():
        print(f"  {k}: {v}")


if __name__ == "__main__":
    test_tsallis_controller()
