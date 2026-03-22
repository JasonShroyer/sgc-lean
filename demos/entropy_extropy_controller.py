"""
Entropy-Extropy Dual Controller for SGC Grokking

THEORETICAL FOUNDATION:
- Entropy H(p) = -Σ pᵢ log pᵢ measures UNCERTAINTY
- Extropy J(p) = Σ (1-pᵢ) log(1-pᵢ) measures CERTAINTY/CONSOLIDATION
- These are Bregman duals from convex-conjugate potentials

CONTROL IMPLICATIONS:
- High H + high dH/dt → allocate more exploration (noise, compute)
- Rising J + falling defect → safe to consolidate (increase WD)
- Rising J + stable/high defect → SPURIOUS CERTAINTY → re-open exploration

This replaces arbitrary schedules with observable-driven control.

Author: SGC Research Team
Date: February 2026
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
import numpy as np
import math
from dataclasses import dataclass, field
from typing import Tuple, List, Optional, Dict
from collections import deque


# ═══════════════════════════════════════════════════════════════════════════════
# ENTROPY AND EXTROPY COMPUTATIONS
# ═══════════════════════════════════════════════════════════════════════════════

def compute_entropy(probs: torch.Tensor, eps: float = 1e-10) -> float:
    """
    Compute Shannon entropy H(p) = -Σ pᵢ log pᵢ
    
    Args:
        probs: Probability distribution (softmax output), shape [batch, classes]
        eps: Small constant to avoid log(0)
    
    Returns:
        Average entropy over batch (in nats)
    """
    # Clamp to avoid log(0)
    probs = torch.clamp(probs, min=eps, max=1.0 - eps)
    entropy = -torch.sum(probs * torch.log(probs), dim=-1)
    return entropy.mean().item()


def compute_extropy(probs: torch.Tensor, eps: float = 1e-10) -> float:
    """
    Compute extropy J(p) = Σ (1-pᵢ) log(1-pᵢ)
    
    This is the "dual" to entropy - measures certainty/consolidation.
    When one class dominates (high certainty), extropy is high.
    When uniform (high uncertainty), extropy is low.
    
    Args:
        probs: Probability distribution, shape [batch, classes]
        eps: Small constant for numerical stability
    
    Returns:
        Average extropy over batch
    """
    # Clamp to avoid log(0)
    one_minus_p = torch.clamp(1.0 - probs, min=eps, max=1.0 - eps)
    extropy = torch.sum(one_minus_p * torch.log(one_minus_p), dim=-1)
    return extropy.mean().item()


def compute_normalized_entropy(probs: torch.Tensor, eps: float = 1e-10) -> float:
    """
    Compute entropy normalized by maximum entropy (uniform distribution).
    Returns value in [0, 1] where 0 = certain, 1 = maximally uncertain.
    """
    n_classes = probs.shape[-1]
    max_entropy = math.log(n_classes)
    entropy = compute_entropy(probs, eps)
    return entropy / max_entropy if max_entropy > 0 else 0.0


def compute_kl_velocity(probs_prev: torch.Tensor, probs_curr: torch.Tensor, 
                        eps: float = 1e-10) -> float:
    """
    Compute entropic velocity as KL divergence between consecutive states.
    
    D_KL(p_curr || p_prev) = Σ p_curr log(p_curr / p_prev)
    
    This measures how fast beliefs are changing in the entropic geometry.
    """
    probs_prev = torch.clamp(probs_prev, min=eps)
    probs_curr = torch.clamp(probs_curr, min=eps)
    kl = torch.sum(probs_curr * torch.log(probs_curr / probs_prev), dim=-1)
    return kl.mean().item()


def compute_l2_velocity(probs_prev: torch.Tensor, probs_curr: torch.Tensor) -> float:
    """
    Compute extropic velocity as squared L2 drift.
    
    E_2(p_t, p_{t+1}) = 0.5 ||p_{t+1} - p_t||_2^2
    
    This is the dual companion to KL velocity - measures change in
    the extropic (certainty) geometry.
    """
    diff = probs_curr - probs_prev
    l2_sq = 0.5 * torch.sum(diff ** 2, dim=-1)
    return l2_sq.mean().item()


# ═══════════════════════════════════════════════════════════════════════════════
# DUAL VITAL SIGNS TRACKER
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class DualVitalSigns:
    """
    Tracks entropy-extropy dual vital signs over training.
    
    The key insight: entropy alone is insufficient for control.
    We need BOTH axes of the Bregman dual geometry.
    """
    
    # Current state
    entropy: float = 0.0           # H(p): uncertainty
    extropy: float = 0.0           # J(p): certainty
    entropy_normalized: float = 0.0  # H(p) / H_max
    
    # Velocities (change per step)
    kl_velocity: float = 0.0       # Entropic motion
    l2_velocity: float = 0.0       # Extropic motion
    
    # Defect (from SGC)
    defect: float = 1.0            # Lumpability defect epsilon
    
    # Derived diagnostics
    consolidation_index: float = 0.0   # J / (J + H) - how consolidated
    spurious_certainty: bool = False   # High J but high defect
    exploration_needed: bool = False   # High H and high velocity
    
    # History for trend detection
    entropy_history: deque = field(default_factory=lambda: deque(maxlen=50))
    extropy_history: deque = field(default_factory=lambda: deque(maxlen=50))
    defect_history: deque = field(default_factory=lambda: deque(maxlen=50))
    kl_velocity_history: deque = field(default_factory=lambda: deque(maxlen=50))
    l2_velocity_history: deque = field(default_factory=lambda: deque(maxlen=50))
    
    # Previous probabilities for velocity computation
    prev_probs: Optional[torch.Tensor] = None
    
    def update(self, probs: torch.Tensor, defect: float, epoch: int):
        """Update all vital signs from new probability distribution."""
        
        # Compute current state
        self.entropy = compute_entropy(probs)
        self.extropy = compute_extropy(probs)
        self.entropy_normalized = compute_normalized_entropy(probs)
        self.defect = defect
        
        # Compute velocities if we have previous state
        if self.prev_probs is not None:
            self.kl_velocity = compute_kl_velocity(self.prev_probs, probs)
            self.l2_velocity = compute_l2_velocity(self.prev_probs, probs)
        else:
            self.kl_velocity = 0.0
            self.l2_velocity = 0.0
        
        # Compute derived diagnostics
        # Consolidation index: 1 - H_normalized (high when entropy is low)
        # This is simpler and more interpretable than using extropy directly
        self.consolidation_index = 1.0 - self.entropy_normalized
        
        # Detect spurious certainty: high certainty but high defect
        # This means "the model is confident but wrong"
        self.spurious_certainty = (
            self.consolidation_index > 0.5 and  # High certainty (low entropy)
            defect > 0.1                         # But poor closure
        )
        
        # Detect need for exploration: high uncertainty + motion
        self.exploration_needed = (
            self.entropy_normalized > 0.5 and  # High uncertainty
            self.kl_velocity > 0.001           # Some changes happening
        )
        
        # Store history
        self.entropy_history.append((epoch, self.entropy))
        self.extropy_history.append((epoch, self.extropy))
        self.defect_history.append((epoch, defect))
        self.kl_velocity_history.append((epoch, self.kl_velocity))
        self.l2_velocity_history.append((epoch, self.l2_velocity))
        
        # Update previous probs
        self.prev_probs = probs.detach().clone()
    
    def get_entropy_trend(self, window: int = 10) -> float:
        """Compute entropy trend over recent history. Positive = increasing."""
        if len(self.entropy_history) < window:
            return 0.0
        recent = [h for _, h in list(self.entropy_history)[-window:]]
        if len(recent) < 2:
            return 0.0
        return (recent[-1] - recent[0]) / window
    
    def get_extropy_trend(self, window: int = 10) -> float:
        """Compute extropy trend. Positive = increasing certainty."""
        if len(self.extropy_history) < window:
            return 0.0
        recent = [j for _, j in list(self.extropy_history)[-window:]]
        if len(recent) < 2:
            return 0.0
        return (recent[-1] - recent[0]) / window
    
    def get_defect_trend(self, window: int = 10) -> float:
        """Compute defect trend. Negative = improving closure."""
        if len(self.defect_history) < window:
            return 0.0
        recent = [d for _, d in list(self.defect_history)[-window:]]
        if len(recent) < 2:
            return 0.0
        return (recent[-1] - recent[0]) / window
    
    def get_summary(self) -> Dict:
        """Get summary of current state for logging."""
        return {
            'entropy': self.entropy,
            'extropy': self.extropy,
            'entropy_normalized': self.entropy_normalized,
            'consolidation_index': self.consolidation_index,
            'kl_velocity': self.kl_velocity,
            'l2_velocity': self.l2_velocity,
            'defect': self.defect,
            'spurious_certainty': self.spurious_certainty,
            'exploration_needed': self.exploration_needed,
            'entropy_trend': self.get_entropy_trend(),
            'extropy_trend': self.get_extropy_trend(),
            'defect_trend': self.get_defect_trend(),
        }


# ═══════════════════════════════════════════════════════════════════════════════
# DUAL CONTROLLER: (H, J, defect) -> (noise, WD, compute)
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class DualController:
    """
    A 3-rule controller that uses entropy-extropy duality for control.
    
    RULE 1 (Exploration): High H + high dH/dt -> increase noise
    RULE 2 (Consolidation): Rising J + falling defect -> increase WD
    RULE 3 (Recovery): Rising J + stable defect -> SPURIOUS -> re-explore
    
    This replaces arbitrary schedules with observable-driven control.
    """
    
    # Control bounds (TUNED: less aggressive exploration)
    noise_min: float = 0.01
    noise_max: float = 0.15       # Reduced from 0.2
    noise_baseline: float = 0.05  # Reduced from 0.1
    
    wd_min: float = 0.1
    wd_max: float = 2.0
    wd_baseline: float = 0.1
    
    # Thresholds for rules
    high_entropy_threshold: float = 0.7      # Normalized entropy
    high_velocity_threshold: float = 0.01    # KL velocity
    consolidation_threshold: float = 0.6     # Consolidation index
    defect_improvement_threshold: float = -0.001  # Negative = improving
    
    # Response gains
    exploration_gain: float = 2.0   # How strongly to respond to exploration need
    consolidation_gain: float = 2.0  # How strongly to ramp WD
    recovery_gain: float = 1.5       # How strongly to recover from spurious certainty
    
    # Current outputs
    current_noise: float = 0.1
    current_wd: float = 0.1
    
    # State
    in_consolidation: bool = False
    in_recovery: bool = False
    exploration_count: int = 0
    consolidation_count: int = 0
    recovery_count: int = 0
    
    def update(self, vitals: DualVitalSigns, exploration_mass: float, 
               M_explore: float) -> Tuple[float, float, str]:
        """
        Compute control outputs from vital signs.
        
        Args:
            vitals: Current entropy-extropy vital signs
            exploration_mass: Current M = Σ η_t
            M_explore: Target exploration mass for mixing
        
        Returns:
            (noise_scale, weight_decay, phase_name)
        """
        
        phase = "heat"
        noise = self.noise_baseline
        wd = self.wd_baseline
        
        # ─────────────────────────────────────────────────────────────────────
        # RULE 1: EXPLORATION
        # High entropy + high velocity -> the system is uncertain and changing
        # Response: Increase noise to maintain exploration
        # ─────────────────────────────────────────────────────────────────────
        
        if vitals.exploration_needed:
            self.exploration_count += 1
            noise_boost = self.exploration_gain * vitals.kl_velocity / self.high_velocity_threshold
            noise = min(self.noise_max, self.noise_baseline * (1 + noise_boost))
            phase = "explore"
        
        # ─────────────────────────────────────────────────────────────────────
        # RULE 2: CONSOLIDATION
        # Rising extropy + falling defect + sufficient M -> safe to consolidate
        # Response: Ramp WD, reduce noise
        # ─────────────────────────────────────────────────────────────────────
        
        defect_trend = vitals.get_defect_trend()
        extropy_trend = vitals.get_extropy_trend()
        
        consolidation_safe = (
            exploration_mass >= M_explore and          # Explored enough
            vitals.consolidation_index > self.consolidation_threshold and  # High certainty
            defect_trend < self.defect_improvement_threshold  # Closure improving
        )
        
        if consolidation_safe and not vitals.spurious_certainty:
            self.consolidation_count += 1
            self.in_consolidation = True
            
            # Ramp WD based on how good the closure is
            closure_quality = max(0, 1 - vitals.defect * 10)  # 0 at defect=0.1, 1 at defect=0
            wd = self.wd_baseline + (self.wd_max - self.wd_baseline) * closure_quality
            
            # Reduce noise as we consolidate
            noise = self.noise_min + (self.noise_baseline - self.noise_min) * (1 - closure_quality)
            phase = "consolidate"
        
        # ─────────────────────────────────────────────────────────────────────
        # RULE 3: RECOVERY FROM SPURIOUS CERTAINTY
        # High extropy but defect not improving -> false confidence
        # Response: Re-open exploration, reduce WD
        # ─────────────────────────────────────────────────────────────────────
        
        if vitals.spurious_certainty:
            self.recovery_count += 1
            self.in_recovery = True
            self.in_consolidation = False
            
            # Re-open exploration
            noise = min(self.noise_max, self.noise_baseline * self.recovery_gain)
            wd = self.wd_min
            phase = "recovery"
        else:
            self.in_recovery = False
        
        # Clamp to bounds
        self.current_noise = max(self.noise_min, min(self.noise_max, noise))
        self.current_wd = max(self.wd_min, min(self.wd_max, wd))
        
        return self.current_noise, self.current_wd, phase
    
    def get_summary(self) -> Dict:
        """Get controller state summary."""
        return {
            'current_noise': self.current_noise,
            'current_wd': self.current_wd,
            'in_consolidation': self.in_consolidation,
            'in_recovery': self.in_recovery,
            'exploration_count': self.exploration_count,
            'consolidation_count': self.consolidation_count,
            'recovery_count': self.recovery_count,
        }


# ═══════════════════════════════════════════════════════════════════════════════
# INTEGRATION WITH GROKKING EXPERIMENT
# ═══════════════════════════════════════════════════════════════════════════════

def sample_output_distribution(model: nn.Module, dataloader, device: str, 
                                n_samples: int = 100) -> torch.Tensor:
    """
    Sample output probability distributions from the model.
    
    Returns: Tensor of shape [n_samples, n_classes]
    """
    model.eval()
    all_probs = []
    
    with torch.no_grad():
        for batch_idx, (x, y) in enumerate(dataloader):
            if len(all_probs) >= n_samples:
                break
            x = x.to(device)
            logits = model(x)
            probs = F.softmax(logits, dim=-1)
            all_probs.append(probs)
    
    if len(all_probs) == 0:
        return torch.zeros(1, 97)  # Fallback
    
    all_probs = torch.cat(all_probs, dim=0)
    return all_probs[:n_samples]


# ═══════════════════════════════════════════════════════════════════════════════
# DEMONSTRATION / TESTING
# ═══════════════════════════════════════════════════════════════════════════════

def test_entropy_extropy():
    """Test entropy and extropy computations."""
    print("=" * 60)
    print("Testing Entropy-Extropy Computations")
    print("=" * 60)
    
    # Test 1: Uniform distribution (maximum entropy, minimum extropy magnitude)
    n_classes = 97
    uniform = torch.ones(1, n_classes) / n_classes
    H_uniform = compute_entropy(uniform)
    J_uniform = compute_extropy(uniform)
    H_norm = compute_normalized_entropy(uniform)
    
    print(f"\nUniform distribution (n={n_classes}):")
    print(f"  H(p) = {H_uniform:.4f} (theoretical max = {math.log(n_classes):.4f})")
    print(f"  J(p) = {J_uniform:.4f}")
    print(f"  H_normalized = {H_norm:.4f} (should be ~1.0)")
    
    # Test 2: Point mass (minimum entropy, high extropy magnitude)
    point_mass = torch.zeros(1, n_classes)
    point_mass[0, 0] = 1.0
    H_point = compute_entropy(point_mass)
    J_point = compute_extropy(point_mass)
    H_norm_point = compute_normalized_entropy(point_mass)
    
    print(f"\nPoint mass distribution:")
    print(f"  H(p) = {H_point:.4f} (should be ~0)")
    print(f"  J(p) = {J_point:.4f}")
    print(f"  H_normalized = {H_norm_point:.4f} (should be ~0)")
    
    # Test 3: Intermediate case
    mixed = torch.zeros(1, n_classes)
    mixed[0, :10] = 0.1  # 10 classes with 0.1 each
    H_mixed = compute_entropy(mixed)
    J_mixed = compute_extropy(mixed)
    
    print(f"\nMixed distribution (10 classes at 0.1):")
    print(f"  H(p) = {H_mixed:.4f}")
    print(f"  J(p) = {J_mixed:.4f}")
    
    # Test 4: Velocities
    print(f"\n" + "=" * 60)
    print("Testing Velocities")
    print("=" * 60)
    
    # Transition from uniform to more peaked
    p1 = torch.ones(10, n_classes) / n_classes
    p2 = torch.zeros(10, n_classes)
    p2[:, :20] = 0.05  # More peaked
    
    kl_vel = compute_kl_velocity(p1, p2)
    l2_vel = compute_l2_velocity(p1, p2)
    
    print(f"\nTransition uniform -> peaked:")
    print(f"  KL velocity (entropic) = {kl_vel:.6f}")
    print(f"  L2 velocity (extropic) = {l2_vel:.6f}")
    
    print("\n" + "=" * 60)
    print("Entropy-Extropy tests complete!")
    print("=" * 60)


def test_dual_controller():
    """Test the dual controller logic."""
    print("\n" + "=" * 60)
    print("Testing Dual Controller")
    print("=" * 60)
    
    vitals = DualVitalSigns()
    controller = DualController()
    
    # Simulate different scenarios
    n_classes = 97
    M_explore = 2.3
    
    # Scenario 1: High uncertainty (exploration needed)
    print("\nScenario 1: High uncertainty")
    probs = torch.ones(100, n_classes) / n_classes + torch.randn(100, n_classes) * 0.001
    probs = F.softmax(probs, dim=-1)
    vitals.update(probs, defect=0.5, epoch=1)
    
    # Add some velocity
    probs2 = probs + torch.randn_like(probs) * 0.1
    probs2 = F.softmax(probs2, dim=-1)
    vitals.update(probs2, defect=0.5, epoch=2)
    
    noise, wd, phase = controller.update(vitals, exploration_mass=1.0, M_explore=M_explore)
    print(f"  entropy_norm = {vitals.entropy_normalized:.3f}")
    print(f"  kl_velocity = {vitals.kl_velocity:.6f}")
    print(f"  exploration_needed = {vitals.exploration_needed}")
    print(f"  -> noise = {noise:.3f}, wd = {wd:.3f}, phase = {phase}")
    
    # Scenario 2: Consolidation (high certainty + good closure)
    print("\nScenario 2: Safe consolidation")
    confident = torch.zeros(100, n_classes)
    confident[:, 0] = 0.9
    confident[:, 1:10] = 0.01  # Small probability on other classes
    confident = F.softmax(confident * 10, dim=-1)
    
    # Build up history with improving defect
    for i in range(15):
        vitals.update(confident, defect=0.05 - i*0.003, epoch=10+i)
    
    noise, wd, phase = controller.update(vitals, exploration_mass=3.0, M_explore=M_explore)
    print(f"  consolidation_index = {vitals.consolidation_index:.3f}")
    print(f"  defect = {vitals.defect:.3f}")
    print(f"  defect_trend = {vitals.get_defect_trend():.6f}")
    print(f"  -> noise = {noise:.3f}, wd = {wd:.3f}, phase = {phase}")
    
    # Scenario 3: Spurious certainty (high confidence but bad closure)
    print("\nScenario 3: Spurious certainty (DANGER)")
    vitals2 = DualVitalSigns()
    controller2 = DualController()
    
    for i in range(15):
        vitals2.update(confident, defect=0.2, epoch=i)  # High defect!
    
    noise, wd, phase = controller2.update(vitals2, exploration_mass=3.0, M_explore=M_explore)
    print(f"  consolidation_index = {vitals2.consolidation_index:.3f}")
    print(f"  defect = {vitals2.defect:.3f}")
    print(f"  spurious_certainty = {vitals2.spurious_certainty}")
    print(f"  -> noise = {noise:.3f}, wd = {wd:.3f}, phase = {phase}")
    
    print("\n" + "=" * 60)
    print("Dual Controller tests complete!")
    print("=" * 60)


if __name__ == "__main__":
    test_entropy_extropy()
    test_dual_controller()
