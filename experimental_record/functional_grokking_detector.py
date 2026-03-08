"""
Functional Grokking Detector: Intrinsic Detection via Algebraic Blanket

This detector uses FUNCTIONAL DEFECT (within-class variance) instead of 
geometric defect (PCA closure) to detect grokking without test labels.

Key Insight: Grokking = algebraic phase transition where:
- Functional defect collapses (equivalence classes learned)
- Geometric defect increases (curved manifold, not flat subspace)
- Class separation explodes (Fisher's criterion spikes)

This provides an INTRINSIC signal for capability emergence at scale.

Author: SGC Research Team
Date: February 5, 2026
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple
from collections import deque
import math


@dataclass
class FunctionalDefectMetrics:
    """Comprehensive functional defect measurements."""
    functional_defect: float      # within-class / total variance (key metric)
    within_class_var: float       # raw within-class variance  
    between_class_var: float      # variance of class centroids
    total_var: float              # total variance
    class_separation: float       # between/within ratio (Fisher's criterion)
    num_classes: int              # number of equivalence classes


@dataclass 
class DetectorState:
    """State for the intrinsic grokking detector."""
    # History buffers
    func_defect_history: deque = field(default_factory=lambda: deque(maxlen=50))
    class_sep_history: deque = field(default_factory=lambda: deque(maxlen=50))
    
    # Smoothed values
    func_defect_ema: float = 1.0
    class_sep_ema: float = 0.0
    
    # Velocities (rate of change)
    func_defect_velocity: float = 0.0
    class_sep_velocity: float = 0.0
    
    # Detection state
    grokking_detected: bool = False
    grokking_epoch: int = -1
    pre_grokking_phase: bool = True
    transition_phase: bool = False
    
    # Latches to prevent repeated detection
    _detection_latch: bool = False


class FunctionalGrokkingDetector:
    """
    Intrinsic grokking detector based on functional defect (algebraic blanket).
    
    This detector works WITHOUT test labels by measuring whether the model
    has learned to map algebraically equivalent inputs to similar representations.
    
    Detection criteria:
    1. Functional defect drops below threshold (equivalence classes learned)
    2. Class separation exceeds threshold (classes distinguishable)
    3. Functional defect velocity is negative (still consolidating)
    
    Theory: Grokking is an algebraic phase transition where the model learns
    the symmetry group of the task. The functional blanket (equivalence classes)
    closes while the geometric blanket (PCA) may open.
    """
    
    def __init__(
        self,
        func_defect_threshold: float = 0.15,
        class_sep_threshold: float = 5.0,
        ema_alpha: float = 0.1,
        velocity_window: int = 5,
        hysteresis: float = 0.02,
    ):
        """
        Initialize the functional grokking detector.
        
        Args:
            func_defect_threshold: Functional defect below this = grokking
            class_sep_threshold: Class separation above this = grokking  
            ema_alpha: Smoothing factor for EMA
            velocity_window: Window for velocity computation
            hysteresis: Hysteresis band for stable detection
        """
        self.func_defect_threshold = func_defect_threshold
        self.class_sep_threshold = class_sep_threshold
        self.ema_alpha = ema_alpha
        self.velocity_window = velocity_window
        self.hysteresis = hysteresis
        
        self.state = DetectorState()
    
    def compute_functional_defect(
        self,
        hidden_states: torch.Tensor,
        targets: torch.Tensor,
        num_classes: int
    ) -> FunctionalDefectMetrics:
        """
        Compute functional defect: within-class variance across equivalence classes.
        
        For any task with discrete equivalence classes (e.g., modular arithmetic),
        this measures whether the model maps equivalent inputs to similar representations.
        
        Args:
            hidden_states: (N, D) hidden activations
            targets: (N,) target class labels (equivalence class indices)
            num_classes: Number of equivalence classes
        
        Returns:
            FunctionalDefectMetrics with all measurements
        """
        device = hidden_states.device
        N, D = hidden_states.shape
        
        # Total variance
        total_var = hidden_states.var(dim=0).mean().item()
        
        if total_var < 1e-10:
            return FunctionalDefectMetrics(
                functional_defect=0.0,
                within_class_var=0.0,
                between_class_var=0.0,
                total_var=total_var,
                class_separation=float('inf'),
                num_classes=num_classes
            )
        
        # Per-class statistics
        class_means = []
        class_vars = []
        class_counts = []
        
        for c in range(num_classes):
            mask = (targets == c)
            count = mask.sum().item()
            
            if count > 0:
                h_c = hidden_states[mask]
                mean_c = h_c.mean(dim=0)
                class_means.append(mean_c)
                class_counts.append(count)
                
                if count > 1:
                    var_c = h_c.var(dim=0).mean().item()
                else:
                    var_c = 0.0
                class_vars.append(var_c)
        
        if not class_means:
            return FunctionalDefectMetrics(
                functional_defect=1.0,
                within_class_var=total_var,
                between_class_var=0.0,
                total_var=total_var,
                class_separation=0.0,
                num_classes=num_classes
            )
        
        # Stack tensors
        class_means = torch.stack(class_means, dim=0)
        class_counts = torch.tensor(class_counts, dtype=torch.float, device=device)
        class_vars = torch.tensor(class_vars, device=device)
        
        # Within-class variance (weighted average)
        within_class_var = (class_vars * class_counts).sum() / class_counts.sum()
        
        # Between-class variance
        weighted_mean = (class_means * class_counts.unsqueeze(1)).sum(0) / class_counts.sum()
        deviations = class_means - weighted_mean.unsqueeze(0)
        between_class_var = ((deviations ** 2).mean(dim=1) * class_counts).sum() / class_counts.sum()
        
        # Metrics
        functional_defect = (within_class_var / (total_var + 1e-10)).item()
        class_separation = (between_class_var / (within_class_var + 1e-10)).item()
        
        return FunctionalDefectMetrics(
            functional_defect=functional_defect,
            within_class_var=within_class_var.item(),
            between_class_var=between_class_var.item(),
            total_var=total_var,
            class_separation=class_separation,
            num_classes=num_classes
        )
    
    def update(
        self,
        hidden_states: torch.Tensor,
        targets: torch.Tensor,
        num_classes: int,
        epoch: int
    ) -> Tuple[FunctionalDefectMetrics, Dict[str, any]]:
        """
        Update detector with new observations.
        
        Args:
            hidden_states: Current hidden activations
            targets: Target equivalence class labels
            num_classes: Number of equivalence classes
            epoch: Current epoch
        
        Returns:
            (metrics, detection_info)
        """
        # Compute metrics
        metrics = self.compute_functional_defect(hidden_states, targets, num_classes)
        
        # Update history
        self.state.func_defect_history.append(metrics.functional_defect)
        self.state.class_sep_history.append(metrics.class_separation)
        
        # Update EMA
        self.state.func_defect_ema = (
            self.ema_alpha * metrics.functional_defect + 
            (1 - self.ema_alpha) * self.state.func_defect_ema
        )
        self.state.class_sep_ema = (
            self.ema_alpha * metrics.class_separation +
            (1 - self.ema_alpha) * self.state.class_sep_ema
        )
        
        # Compute velocities
        if len(self.state.func_defect_history) >= self.velocity_window:
            recent = list(self.state.func_defect_history)[-self.velocity_window:]
            self.state.func_defect_velocity = (recent[-1] - recent[0]) / self.velocity_window
            
            recent_sep = list(self.state.class_sep_history)[-self.velocity_window:]
            self.state.class_sep_velocity = (recent_sep[-1] - recent_sep[0]) / self.velocity_window
        
        # Detection logic
        detection_info = self._detect_grokking(metrics, epoch)
        
        return metrics, detection_info
    
    def _detect_grokking(
        self,
        metrics: FunctionalDefectMetrics,
        epoch: int
    ) -> Dict[str, any]:
        """
        Detect grokking based on functional defect criteria.
        
        Grokking detected when:
        1. Functional defect < threshold (equivalence classes learned)
        2. Class separation > threshold (classes distinguishable)
        3. Not already detected (latch)
        """
        info = {
            'phase': 'unknown',
            'grokking_detected': False,
            'grokking_imminent': False,
            'confidence': 0.0,
        }
        
        func_d = self.state.func_defect_ema
        class_sep = self.state.class_sep_ema
        func_vel = self.state.func_defect_velocity
        
        # Phase detection
        if func_d > 0.8:
            info['phase'] = 'memorization'
            self.state.pre_grokking_phase = True
            self.state.transition_phase = False
            
        elif func_d > self.func_defect_threshold + self.hysteresis:
            info['phase'] = 'transition'
            self.state.pre_grokking_phase = False
            self.state.transition_phase = True
            
            # Check if grokking is imminent
            if func_vel < -0.01 and class_sep > self.class_sep_threshold * 0.5:
                info['grokking_imminent'] = True
                info['confidence'] = min(1.0, (self.func_defect_threshold - func_d) / 
                                         (func_d - self.func_defect_threshold) + 0.5)
        else:
            info['phase'] = 'grokked'
            self.state.transition_phase = False
        
        # Grokking detection (with hysteresis)
        grokking_condition = (
            func_d < self.func_defect_threshold - self.hysteresis and
            class_sep > self.class_sep_threshold and
            not self.state._detection_latch
        )
        
        if grokking_condition:
            self.state.grokking_detected = True
            self.state.grokking_epoch = epoch
            self.state._detection_latch = True
            info['grokking_detected'] = True
            info['confidence'] = 1.0
            print(f"\n{'='*60}")
            print(f"*** GROKKING DETECTED at epoch {epoch} ***")
            print(f"    Functional defect: {func_d:.4f} (threshold: {self.func_defect_threshold})")
            print(f"    Class separation:  {class_sep:.2f} (threshold: {self.class_sep_threshold})")
            print(f"    Velocity: {func_vel:.4f}/epoch")
            print(f"{'='*60}\n")
        
        return info
    
    def get_intrinsic_score(self) -> float:
        """
        Get an intrinsic "grokking score" in [0, 1].
        
        0 = no grokking (high functional defect, low class separation)
        1 = full grokking (low functional defect, high class separation)
        
        This can be used as a continuous capability indicator.
        """
        func_d = self.state.func_defect_ema
        class_sep = self.state.class_sep_ema
        
        # Functional defect contribution (inverted, so low = good)
        func_score = max(0, 1 - func_d / 0.5)  # Saturates at func_d = 0.5
        
        # Class separation contribution
        sep_score = min(1, class_sep / 10.0)  # Saturates at class_sep = 10
        
        # Combined score
        return 0.5 * func_score + 0.5 * sep_score
    
    def reset(self):
        """Reset detector state."""
        self.state = DetectorState()


class FunctionalActiveInferenceController:
    """
    Active inference controller using functional defect for grokking detection.
    
    Replaces geometric defect (PCA closure) with functional defect (algebraic blanket)
    for controlling noise injection, weight decay, and learning rate.
    
    Control logic:
    - High functional defect: Inject noise, encourage exploration
    - Transition phase: Gradual cooling
    - Low functional defect: Consolidate with weight decay
    """
    
    def __init__(
        self,
        base_noise: float = 0.1,
        base_weight_decay: float = 1.0,
        base_lr: float = 1e-3,
        num_classes: int = 97,
    ):
        self.base_noise = base_noise
        self.base_weight_decay = base_weight_decay
        self.base_lr = base_lr
        self.num_classes = num_classes
        
        self.detector = FunctionalGrokkingDetector()
        
        # Current control outputs
        self.noise_scale = base_noise
        self.weight_decay = base_weight_decay
        self.lr_scale = 1.0
    
    def update(
        self,
        hidden_states: torch.Tensor,
        targets: torch.Tensor,
        epoch: int
    ) -> Dict[str, float]:
        """
        Update controller and get control outputs.
        
        Args:
            hidden_states: Current hidden activations
            targets: Target equivalence class labels
            epoch: Current epoch
        
        Returns:
            Dict with noise_scale, weight_decay, lr_scale
        """
        metrics, info = self.detector.update(
            hidden_states, targets, self.num_classes, epoch
        )
        
        func_d = self.detector.state.func_defect_ema
        phase = info['phase']
        
        # Control logic based on phase
        if phase == 'memorization':
            # High exploration: inject noise, low weight decay
            self.noise_scale = self.base_noise * (1 + func_d)
            self.weight_decay = self.base_weight_decay * 0.5
            self.lr_scale = 1.0
            
        elif phase == 'transition':
            # Gradual cooling: reduce noise, increase weight decay
            progress = 1 - (func_d - 0.15) / (0.8 - 0.15)
            progress = max(0, min(1, progress))
            
            self.noise_scale = self.base_noise * (1 - 0.8 * progress)
            self.weight_decay = self.base_weight_decay * (0.5 + 0.5 * progress)
            self.lr_scale = 1.0 - 0.3 * progress
            
        else:  # grokked
            # Consolidation: minimal noise, high weight decay
            self.noise_scale = self.base_noise * 0.1
            self.weight_decay = self.base_weight_decay * 1.5
            self.lr_scale = 0.5
        
        return {
            'noise_scale': self.noise_scale,
            'weight_decay': self.weight_decay,
            'lr_scale': self.lr_scale,
            'phase': phase,
            'functional_defect': metrics.functional_defect,
            'class_separation': metrics.class_separation,
            'intrinsic_score': self.detector.get_intrinsic_score(),
        }


# =============================================================================
# TEST
# =============================================================================

def test_functional_detector():
    """Test the functional grokking detector on synthetic data."""
    print("\n" + "=" * 60)
    print("Testing Functional Grokking Detector")
    print("=" * 60)
    
    detector = FunctionalGrokkingDetector()
    num_classes = 10
    hidden_dim = 64
    
    # Simulate progression from memorization to grokking
    print("\nSimulating training progression...")
    print(f"{'Epoch':>6} | {'FuncD':>7} | {'ClassSep':>8} | {'Phase':<15} | {'Score':>5}")
    print("-" * 55)
    
    for epoch in range(1, 101):
        # Simulate functional defect decreasing over time
        if epoch < 30:
            # Memorization: high within-class variance
            func_d_target = 0.9 - 0.005 * epoch
        elif epoch < 60:
            # Transition: rapid decrease
            func_d_target = 0.75 - 0.015 * (epoch - 30)
        else:
            # Grokking: collapse to near zero
            func_d_target = 0.30 - 0.008 * (epoch - 60)
        
        func_d_target = max(0.02, func_d_target)
        
        # Create synthetic hidden states matching the target functional defect
        # Higher func_d = more within-class variance
        n_samples = 500
        targets = torch.randint(0, num_classes, (n_samples,))
        
        # Class centroids (spread out)
        centroids = torch.randn(num_classes, hidden_dim) * 2
        
        # Generate samples with controlled within-class variance
        hidden_states = []
        for i in range(n_samples):
            c = targets[i].item()
            noise_scale = func_d_target ** 0.5  # within-class std
            h = centroids[c] + torch.randn(hidden_dim) * noise_scale
            hidden_states.append(h)
        
        hidden_states = torch.stack(hidden_states)
        
        # Update detector
        metrics, info = detector.update(hidden_states, targets, num_classes, epoch)
        
        if epoch % 10 == 0 or info['grokking_detected']:
            score = detector.get_intrinsic_score()
            print(f"{epoch:6d} | {metrics.functional_defect:7.4f} | "
                  f"{metrics.class_separation:8.2f} | {info['phase']:<15} | {score:5.2f}")
    
    print("\n" + "=" * 60)
    print(f"Final state: grokking_detected = {detector.state.grokking_detected}")
    print(f"             grokking_epoch = {detector.state.grokking_epoch}")
    print("=" * 60)


if __name__ == "__main__":
    test_functional_detector()
