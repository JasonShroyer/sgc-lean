"""
Intrinsic Grokking Detection: Blanket Closure as Success Criterion

The key insight: Grokking = Markov blanket formation = defect collapse.

If the theory is correct, we should be able to detect grokking
WITHOUT looking at test accuracy, by monitoring:
1. Defect (blanket quality)
2. Entropy (certainty)
3. Their velocities (rate of change)

This provides an INTRINSIC success criterion that doesn't require labels.
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
import numpy as np
import math
from dataclasses import dataclass, field
from typing import List, Tuple, Optional
from collections import deque


@dataclass
class BlanketState:
    """Observable state of the Markov blanket."""
    epoch: int = 0
    
    # Defect (blanket leakage): how much outside affects inside
    defect: float = 1.0
    defect_velocity: float = 0.0
    defect_acceleration: float = 0.0
    
    # Entropy (certainty): how confident is the model
    entropy_normalized: float = 1.0
    entropy_velocity: float = 0.0
    
    # Consolidation (1 - entropy): dual of entropy
    consolidation: float = 0.0
    
    # Derived signals
    blanket_closing: bool = False      # defect dropping
    blanket_closed: bool = False       # defect below threshold
    crystallizing: bool = False        # consolidation rising + defect falling
    
    def __repr__(self):
        return (f"BlanketState(epoch={self.epoch}, defect={self.defect:.4f}, "
                f"entropy={self.entropy_normalized:.3f}, closed={self.blanket_closed})")


@dataclass
class IntrinsicGrokkingDetector:
    """
    Detects grokking using only internal observables (no test accuracy).
    
    The hypothesis: Grokking occurs when the Markov blanket closes,
    which manifests as:
    1. Defect crosses below threshold (blanket tight)
    2. Defect velocity is negative (still improving)
    3. Consolidation is high (model is confident)
    
    This should PRECEDE the test accuracy jump by some epochs,
    or at worst, coincide with it.
    """
    
    # Thresholds for detection
    defect_threshold: float = 0.15        # Below this = blanket closed
    consolidation_threshold: float = 0.5  # Above this = confident
    velocity_window: int = 10             # Epochs for velocity estimation
    
    # State tracking
    current_state: BlanketState = field(default_factory=BlanketState)
    state_history: List[BlanketState] = field(default_factory=list)
    
    # Detection events
    blanket_closure_epoch: int = -1       # When blanket first closed
    grokking_predicted_epoch: int = -1    # When we predict grokking
    
    # Smoothing
    defect_ema: float = 1.0
    entropy_ema: float = 1.0
    ema_alpha: float = 0.2
    
    # History for velocity computation
    defect_history: deque = field(default_factory=lambda: deque(maxlen=20))
    entropy_history: deque = field(default_factory=lambda: deque(maxlen=20))
    
    def update(self, epoch: int, defect: float, entropy_normalized: float) -> BlanketState:
        """
        Update detector with new observations.
        
        Args:
            epoch: Current epoch
            defect: Measured defect (blanket leakage)
            entropy_normalized: Normalized entropy of output distribution
        
        Returns:
            Updated BlanketState with detection signals
        """
        # Update EMAs
        self.defect_ema = self.ema_alpha * defect + (1 - self.ema_alpha) * self.defect_ema
        self.entropy_ema = self.ema_alpha * entropy_normalized + (1 - self.ema_alpha) * self.entropy_ema
        
        # Store in history
        self.defect_history.append(defect)
        self.entropy_history.append(entropy_normalized)
        
        # Compute velocities
        if len(self.defect_history) >= 2:
            recent_defects = list(self.defect_history)[-self.velocity_window:]
            defect_velocity = (recent_defects[-1] - recent_defects[0]) / len(recent_defects)
        else:
            defect_velocity = 0.0
        
        if len(self.entropy_history) >= 2:
            recent_entropies = list(self.entropy_history)[-self.velocity_window:]
            entropy_velocity = (recent_entropies[-1] - recent_entropies[0]) / len(recent_entropies)
        else:
            entropy_velocity = 0.0
        
        # Compute acceleration (second derivative)
        prev_velocity = self.current_state.defect_velocity
        defect_acceleration = defect_velocity - prev_velocity
        
        # Update state
        self.current_state = BlanketState(
            epoch=epoch,
            defect=self.defect_ema,
            defect_velocity=defect_velocity,
            defect_acceleration=defect_acceleration,
            entropy_normalized=self.entropy_ema,
            entropy_velocity=entropy_velocity,
            consolidation=1.0 - self.entropy_ema,
        )
        
        # Compute derived signals
        self.current_state.blanket_closing = (defect_velocity < -0.001)
        self.current_state.blanket_closed = (self.defect_ema < self.defect_threshold)
        self.current_state.crystallizing = (
            self.current_state.blanket_closing and 
            self.current_state.consolidation > 0.3
        )
        
        # Detection logic
        self._check_for_grokking(epoch)
        
        # Store history
        self.state_history.append(self.current_state)
        
        return self.current_state
    
    def _check_for_grokking(self, epoch: int):
        """Check if grokking is predicted based on blanket state."""
        
        # First blanket closure event
        if self.blanket_closure_epoch < 0 and self.current_state.blanket_closed:
            self.blanket_closure_epoch = epoch
            print(f"\n[IntrinsicDetector] BLANKET CLOSURE at epoch {epoch}")
            print(f"    defect = {self.current_state.defect:.4f} < {self.defect_threshold}")
        
        # Grokking prediction: blanket closed + confident + still improving
        if self.grokking_predicted_epoch < 0:
            if (self.current_state.blanket_closed and
                self.current_state.consolidation > self.consolidation_threshold and
                self.current_state.defect_velocity <= 0):
                
                self.grokking_predicted_epoch = epoch
                print(f"\n[IntrinsicDetector] GROKKING PREDICTED at epoch {epoch}")
                print(f"    defect = {self.current_state.defect:.4f}")
                print(f"    consolidation = {self.current_state.consolidation:.3f}")
                print(f"    defect_velocity = {self.current_state.defect_velocity:.6f}")
    
    def get_prediction_lead_time(self, actual_grokking_epoch: int) -> int:
        """
        Compute how many epochs before actual grokking we predicted it.
        
        Positive = we predicted before (good!)
        Negative = we predicted after (we're late)
        Zero = coincident
        """
        if self.grokking_predicted_epoch < 0:
            return float('inf')  # Never predicted
        return actual_grokking_epoch - self.grokking_predicted_epoch
    
    def get_summary(self) -> dict:
        """Get summary statistics."""
        return {
            'blanket_closure_epoch': self.blanket_closure_epoch,
            'grokking_predicted_epoch': self.grokking_predicted_epoch,
            'final_defect': self.current_state.defect,
            'final_consolidation': self.current_state.consolidation,
            'history_length': len(self.state_history),
        }


def compute_closure_defect(model: nn.Module, 
                           hidden_states: torch.Tensor, 
                           k: int = None) -> float:
    """
    Compute proper closure defect: ||Pi f(x) - Pi f(Pi(x))||
    
    This measures how much the inside dynamics depend on the outside.
    
    Args:
        model: The model (should have a forward method)
        hidden_states: Hidden representations (B, D)
        k: Number of top principal components to keep (auto if None)
    
    Returns:
        Closure defect (0 = perfect blanket, 1 = completely leaky)
    """
    with torch.no_grad():
        # SVD to get principal components
        U, S, Vh = torch.linalg.svd(hidden_states, full_matrices=False)
        
        # Auto-select k based on 90% energy
        if k is None:
            S2 = S ** 2
            cumsum = torch.cumsum(S2, dim=0)
            total = S2.sum()
            k = (cumsum < 0.9 * total).sum().item() + 1
            k = max(1, min(k, len(S) - 1))
        
        # Project to top-k (inside)
        # Pi(x) = U[:, :k] @ U[:, :k].T @ x
        Pi = U[:, :k] @ U[:, :k].T
        h_inside = hidden_states @ Pi.T
        
        # Full dynamics: f(x) - here we just measure the representation itself
        # since we don't have the dynamics easily accessible
        # Instead, we measure how much energy is in the tail
        h_outside = hidden_states - h_inside
        
        # Defect = ||outside|| / ||total||
        outside_energy = (h_outside ** 2).sum().item()
        total_energy = (hidden_states ** 2).sum().item()
        
        if total_energy < 1e-10:
            return 1.0
        
        return math.sqrt(outside_energy / total_energy)


# ═══════════════════════════════════════════════════════════════════════════════
# TEST WITH SIMULATED TRAJECTORY
# ═══════════════════════════════════════════════════════════════════════════════

def test_intrinsic_detector():
    """Test the intrinsic grokking detector with a simulated trajectory."""
    print("=" * 70)
    print("Testing Intrinsic Grokking Detector")
    print("Simulating a grokking trajectory with defect and entropy signals")
    print("=" * 70)
    
    detector = IntrinsicGrokkingDetector()
    
    # Simulated trajectory:
    # - Early: high defect, high entropy (exploring)
    # - Middle: defect starts falling, entropy starts falling (crystallizing)
    # - Late: low defect, low entropy (grokked)
    
    np.random.seed(42)
    
    actual_grokking_epoch = 350  # When test accuracy would cross threshold
    
    print(f"\n{'Epoch':>6} | {'Defect':>8} | {'Entropy':>7} | {'Consol':>6} | {'Closing':>7} | {'Closed':>6}")
    print("-" * 60)
    
    for epoch in range(1, 501):
        # Simulate defect trajectory (starts high, drops around epoch 300)
        if epoch < 200:
            defect = 0.5 + 0.1 * np.random.randn()
        elif epoch < 300:
            defect = 0.5 - 0.002 * (epoch - 200) + 0.05 * np.random.randn()
        else:
            defect = max(0.05, 0.3 - 0.003 * (epoch - 300) + 0.02 * np.random.randn())
        
        # Simulate entropy trajectory (starts high, drops as model learns)
        if epoch < 250:
            entropy = 0.9 + 0.05 * np.random.randn()
        else:
            entropy = max(0.1, 0.9 - 0.003 * (epoch - 250) + 0.03 * np.random.randn())
        
        defect = max(0.01, min(1.0, defect))
        entropy = max(0.01, min(1.0, entropy))
        
        state = detector.update(epoch, defect, entropy)
        
        # Log periodically
        if epoch % 50 == 0 or epoch == 1:
            print(f"{epoch:6d} | {state.defect:8.4f} | {state.entropy_normalized:7.3f} | "
                  f"{state.consolidation:6.3f} | {str(state.blanket_closing):>7} | {str(state.blanket_closed):>6}")
    
    print("\n" + "=" * 70)
    print("RESULTS")
    print("=" * 70)
    
    summary = detector.get_summary()
    print(f"Blanket closure epoch: {summary['blanket_closure_epoch']}")
    print(f"Grokking predicted epoch: {summary['grokking_predicted_epoch']}")
    print(f"Actual grokking epoch: {actual_grokking_epoch}")
    
    lead_time = detector.get_prediction_lead_time(actual_grokking_epoch)
    if lead_time != float('inf'):
        if lead_time > 0:
            print(f"\n*** PREDICTION LED BY {lead_time} EPOCHS (intrinsic signal faster!) ***")
        elif lead_time < 0:
            print(f"\n*** PREDICTION LAGGED BY {-lead_time} EPOCHS ***")
        else:
            print(f"\n*** PREDICTION COINCIDENT ***")
    else:
        print("\n*** NO PREDICTION MADE ***")


if __name__ == "__main__":
    test_intrinsic_detector()
