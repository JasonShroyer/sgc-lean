"""
SGC Integrated Controller: Sprint A Integration

Wires together three proven subsystems:
1. FunctionalGrokkingDetector (ε sensor) → detects grokking via functional defect
2. WaveletCoupledController (temperature actuator) → noise injection / weight decay
3. Stalk freeze mechanism → memory protection

This is INTEGRATION, not research. All subsystems are already validated.

See: reports/PHASE_1C_REPORT.md, reports/PHASE_2_FAILURE_ANALYSIS.md
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'demos'))

import torch
import torch.nn as nn
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple
from enum import Enum

from functional_grokking_detector import FunctionalGrokkingDetector, FunctionalDefectMetrics


class StalkPhase(Enum):
    """Phase of a stalk in the continual learning sequence."""
    HEATING = "heating"      # Exploring, high noise
    TRANSITION = "transition" # Grokking imminent
    GROKKED = "grokked"      # Learned, ready to freeze
    FROZEN = "frozen"        # Protected, no updates


@dataclass
class StalkState:
    """State of a single task's stalk."""
    task_id: str
    phase: StalkPhase = StalkPhase.HEATING
    detector: FunctionalGrokkingDetector = field(default_factory=FunctionalGrokkingDetector)
    frozen_params: Optional[Dict[str, torch.Tensor]] = None
    grokking_epoch: int = -1
    freeze_epoch: int = -1
    final_epsilon: float = 1.0  # also accessible as final_eps for compatibility
    final_accuracy: float = 0.0


@dataclass
class ControlOutput:
    """Output from SGCController.step()"""
    weight_decay: float
    noise_scale: float
    should_freeze: bool
    phase: StalkPhase
    epsilon: float  # functional defect
    class_separation: float


class SGCController:
    """
    Integrated SGC Controller for continual learning.
    
    Owns:
    - Per-task FunctionalGrokkingDetector instances
    - Global noise/temperature parameters
    - Freeze mechanism for memory protection
    
    Zero hardcoded thresholds - all derived from data:
    - Grokking detected when ε < bootstrap_variance * SHUFFLE_GAP_SIGMA
    - Freeze triggered when grokking detected
    """
    
    SHUFFLE_GAP_SIGMA = 2.0  # Only hardcoded constant (statistical convention)
    
    def __init__(
        self,
        base_noise: float = 0.1,
        base_weight_decay: float = 1.0,
        num_classes: int = 97,
    ):
        self.base_noise = base_noise
        self.base_weight_decay = base_weight_decay
        self.num_classes = num_classes
        
        self.stalks: Dict[str, StalkState] = {}
        self.active_task: Optional[str] = None
        self.history: List[Dict] = []
    
    def register_task(self, task_id: str):
        """Register a new task stalk."""
        self.stalks[task_id] = StalkState(task_id=task_id)
        self.active_task = task_id
        print(f"[SGCController] Registered task: {task_id}")
    
    def set_active_task(self, task_id: str):
        """Set the currently training task."""
        if task_id not in self.stalks:
            self.register_task(task_id)
        self.active_task = task_id
    
    def step(
        self,
        hidden_states: torch.Tensor,
        targets: torch.Tensor,
        epoch: int,
        accuracy: float = 0.0,
    ) -> ControlOutput:
        """
        One step of the integrated controller.
        
        Args:
            hidden_states: Hidden activations from model
            targets: Target labels (equivalence class indices)
            epoch: Current epoch
            accuracy: Current test accuracy (for logging)
        
        Returns:
            ControlOutput with weight_decay, noise_scale, freeze signal
        """
        if self.active_task is None:
            raise ValueError("No active task. Call register_task() first.")
        
        stalk = self.stalks[self.active_task]
        
        # Already frozen - no updates needed
        if stalk.phase == StalkPhase.FROZEN:
            return ControlOutput(
                weight_decay=0.0,
                noise_scale=0.0,
                should_freeze=False,
                phase=StalkPhase.FROZEN,
                epsilon=stalk.final_epsilon,
                class_separation=0.0,
            )
        
        # Update detector
        metrics, info = stalk.detector.update(
            hidden_states, targets, self.num_classes, epoch
        )
        
        # Phase determination from detector
        if info['grokking_detected'] and stalk.phase != StalkPhase.GROKKED:
            stalk.phase = StalkPhase.GROKKED
            stalk.grokking_epoch = epoch
            stalk.final_epsilon = metrics.functional_defect
            stalk.final_accuracy = accuracy
            print(f"[SGCController] Task {self.active_task} GROKKED at epoch {epoch}")
            print(f"    eps = {metrics.functional_defect:.4f}, accuracy = {accuracy:.1%}")
        elif info['phase'] == 'transition' and stalk.phase == StalkPhase.HEATING:
            stalk.phase = StalkPhase.TRANSITION
        
        # Control outputs based on phase
        if stalk.phase == StalkPhase.HEATING:
            weight_decay = self.base_weight_decay * 0.5
            noise_scale = self.base_noise
        elif stalk.phase == StalkPhase.TRANSITION:
            weight_decay = self.base_weight_decay
            noise_scale = self.base_noise * 0.5
        else:  # GROKKED
            weight_decay = self.base_weight_decay * 1.5
            noise_scale = self.base_noise * 0.1
        
        # Record history
        self.history.append({
            'task': self.active_task,
            'epoch': epoch,
            'eps': metrics.functional_defect,
            'class_sep': metrics.class_separation,
            'phase': stalk.phase.value,
            'accuracy': accuracy,
        })
        
        return ControlOutput(
            weight_decay=weight_decay,
            noise_scale=noise_scale,
            should_freeze=(stalk.phase == StalkPhase.GROKKED),
            phase=stalk.phase,
            epsilon=metrics.functional_defect,
            class_separation=metrics.class_separation,
        )
    
    def freeze_stalk(self, model: nn.Module, task_id: Optional[str] = None):
        """
        Freeze a task's stalk by snapshotting parameters.
        
        This implements the memory protection validated in Phase 2:
        "Task A remained at 100% accuracy throughout Task B training"
        """
        task_id = task_id or self.active_task
        if task_id not in self.stalks:
            raise ValueError(f"Unknown task: {task_id}")
        
        stalk = self.stalks[task_id]
        stalk.frozen_params = {
            name: param.clone().detach() 
            for name, param in model.named_parameters()
        }
        stalk.phase = StalkPhase.FROZEN
        stalk.freeze_epoch = self.history[-1]['epoch'] if self.history else 0
        
        print(f"[SGCController] Task {task_id} FROZEN")
        print(f"    Final eps = {stalk.final_epsilon:.4f}")
        print(f"    Final accuracy = {stalk.final_accuracy:.1%}")
    
    def apply_elastic_protection(self, model: nn.Module, alpha: float = 0.1):
        """
        Apply elastic weight consolidation toward frozen parameters.
        
        For each frozen stalk, pull current params toward frozen snapshot.
        This prevents catastrophic forgetting.
        """
        with torch.no_grad():
            for task_id, stalk in self.stalks.items():
                if stalk.phase == StalkPhase.FROZEN and stalk.frozen_params:
                    for name, param in model.named_parameters():
                        if name in stalk.frozen_params:
                            drift = param - stalk.frozen_params[name]
                            param.sub_(alpha * drift)
    
    def get_all_accuracies(self) -> Dict[str, float]:
        """Get final accuracies for all tasks."""
        return {
            task_id: stalk.final_accuracy 
            for task_id, stalk in self.stalks.items()
        }
    
    def summary(self) -> str:
        """Generate summary of all stalks."""
        lines = ["=" * 60, "  SGC Controller Summary", "=" * 60]
        for task_id, stalk in self.stalks.items():
            lines.append(f"\n  Task: {task_id}")
            lines.append(f"    Phase: {stalk.phase.value}")
            lines.append(f"    Grokking epoch: {stalk.grokking_epoch}")
            lines.append(f"    Freeze epoch: {stalk.freeze_epoch}")
            lines.append(f"    Final eps: {stalk.final_epsilon:.4f}")
            lines.append(f"    Final accuracy: {stalk.final_accuracy:.1%}")
        lines.append("=" * 60)
        return "\n".join(lines)


if __name__ == "__main__":
    # Quick smoke test
    print("SGC Integrated Controller - Smoke Test")
    
    controller = SGCController(num_classes=10)
    controller.register_task("test_task")
    
    # Simulate training progression
    for epoch in range(100):
        # Fake hidden states that improve over time
        n_samples = 100
        hidden_dim = 64
        targets = torch.randint(0, 10, (n_samples,))
        
        # Simulate improving class separation
        progress = epoch / 100
        noise_scale = 1.0 - 0.9 * progress
        centroids = torch.randn(10, hidden_dim) * 3
        hidden = torch.stack([
            centroids[t] + torch.randn(hidden_dim) * noise_scale
            for t in targets
        ])
        
        output = controller.step(hidden, targets, epoch, accuracy=progress)
        
        if epoch % 20 == 0:
            print(f"Epoch {epoch}: eps={output.epsilon:.3f}, phase={output.phase.value}")
    
    print(controller.summary())
