"""
SGC Integrated Controller: Full Control Loop with Constrained Updates
=======================================================================

Implements the complete SGC control loop including:
    - Wavelet noise injection
    - Thermal pump annealing
    - SGC metric monitoring
    - Constrained gradient updates (freeze grokked subspaces)

THEORETICAL FOUNDATION (from QuotientGenerator.lean):
    - constrained_update_orthogonal: gradient projected orthogonal to frozen subspaces
    - This preserves previous fixed points when training new tasks

Author: SGC Research Team
Date: March 31, 2026
"""

import torch
import torch.nn as nn
from typing import Dict, List, Optional, Tuple, Callable
from dataclasses import dataclass, field
from enum import Enum

from .wavelet_layer import WaveletNoiseInjector
from .thermal_pump import ThermalPump, ThermalSchedule, ThermalPhase
from .sgc_engine import SGCEngine, SGCMetrics


class ControllerPhase(Enum):
    """Controller operating phases."""
    EXPLORING = "exploring"     # Active training with noise injection
    GROKKING = "grokking"       # Near grokking, monitoring transition
    CONSOLIDATING = "consolidating"  # Post-grokking, freezing subspace
    FROZEN = "frozen"           # Task complete, subspace locked


@dataclass
class ConstrainedUpdate:
    """
    Constrained gradient update that preserves frozen subspaces.
    
    Implements constrained_update_orthogonal from QuotientGenerator.lean:
    The gradient is projected orthogonal to all previously frozen directions,
    ensuring that learning new tasks cannot damage existing fixed points.
    """
    
    frozen_subspaces: Dict[str, torch.Tensor] = field(default_factory=dict)
    # frozen_subspaces[task_name] = orthonormal basis of frozen directions
    
    def freeze_subspace(self, task_name: str, model: nn.Module, 
                        dataloader: torch.utils.data.DataLoader,
                        device: str = 'cuda', n_samples: int = 200):
        """
        Freeze the current gradient subspace for a task.
        
        Computes the principal gradient directions and stores them as
        the frozen subspace for this task.
        """
        model.eval()
        gradients = []
        
        n_collected = 0
        for x, y in dataloader:
            if n_collected >= n_samples:
                break
            x, y = x.to(device), y.to(device)
            
            for i in range(min(len(x), n_samples - n_collected)):
                model.zero_grad()
                logits = model(x[i:i+1])
                log_prob = torch.log_softmax(logits, dim=-1)
                loss = -log_prob[0, y[i]]
                loss.backward()
                
                g = []
                for p in model.parameters():
                    if p.grad is not None:
                        g.append(p.grad.flatten())
                if g:
                    gradients.append(torch.cat(g).detach())
                n_collected += 1
        
        model.train()
        
        if len(gradients) < 10:
            print(f"[ConstrainedUpdate] Warning: insufficient gradients for {task_name}")
            return
        
        G = torch.stack(gradients)
        
        # SVD to get principal directions
        try:
            U, S, Vh = torch.linalg.svd(G, full_matrices=False)
            
            # Keep directions with >1% of total energy
            S_squared = S ** 2
            total = S_squared.sum()
            cumsum = torch.cumsum(S_squared, dim=0)
            k = int((cumsum < 0.99 * total).sum().item()) + 1
            k = max(1, min(k, len(S), 50))  # Cap at 50 directions
            
            # Store orthonormal basis (rows of Vh)
            frozen_basis = Vh[:k].detach()
            self.frozen_subspaces[task_name] = frozen_basis
            
            print(f"[ConstrainedUpdate] Frozen {k} directions for task '{task_name}'")
            
        except Exception as e:
            print(f"[ConstrainedUpdate] SVD failed for {task_name}: {e}")
    
    def project_gradient_orthogonal(self, model: nn.Module):
        """
        Project current gradients orthogonal to all frozen subspaces.
        
        This implements constrained_update_orthogonal:
        g_constrained = g - Σ_task P_task @ g
        
        where P_task is the projection onto task's frozen subspace.
        """
        if not self.frozen_subspaces:
            return  # No constraints
        
        # Flatten current gradients
        grad_vec = []
        shapes = []
        for p in model.parameters():
            if p.grad is not None:
                shapes.append(p.grad.shape)
                grad_vec.append(p.grad.flatten())
            else:
                shapes.append(None)
                grad_vec.append(None)
        
        # Concatenate non-None gradients
        valid_grads = [g for g in grad_vec if g is not None]
        if not valid_grads:
            return
        
        g = torch.cat(valid_grads)
        device = g.device
        
        # Project out frozen directions
        for task_name, basis in self.frozen_subspaces.items():
            basis = basis.to(device)
            
            # Check dimension compatibility
            if basis.shape[1] != g.shape[0]:
                # Dimension mismatch - skip this subspace
                continue
            
            # g = g - basis.T @ basis @ g
            coeffs = basis @ g  # (k,)
            projection = basis.T @ coeffs  # (n,)
            g = g - projection
        
        # Reshape back to parameters
        idx = 0
        for p, shape in zip(model.parameters(), shapes):
            if shape is not None and p.grad is not None:
                numel = p.grad.numel()
                p.grad.data = g[idx:idx+numel].view(shape)
                idx += numel
    
    def get_frozen_dimension(self) -> int:
        """Get total dimension of frozen subspace."""
        return sum(basis.shape[0] for basis in self.frozen_subspaces.values())


@dataclass
class SGCIntegratedController:
    """
    Full SGC control loop integrating all components.
    
    Orchestrates:
    - Wavelet noise injection for accelerated exploration
    - Thermal pump for annealing schedule
    - SGC engine for metric computation
    - Constrained updates for multi-task preservation
    """
    
    # Components
    wavelet: WaveletNoiseInjector = field(default_factory=WaveletNoiseInjector)
    thermal: ThermalPump = field(default_factory=ThermalPump)
    engine: SGCEngine = field(default_factory=SGCEngine)
    constraint: ConstrainedUpdate = field(default_factory=ConstrainedUpdate)
    
    # Configuration
    grokking_threshold: float = 0.05     # ε threshold for grokking
    ridge_threshold: float = 2.0         # R threshold for stability
    noise_injection_interval: int = 1    # Inject noise every N steps
    measurement_interval: int = 10       # Measure metrics every N steps
    
    # State
    phase: ControllerPhase = ControllerPhase.EXPLORING
    step: int = 0
    current_task: str = ""
    grokked_tasks: List[str] = field(default_factory=list)
    
    # History
    metrics_history: List[Tuple[int, str, SGCMetrics]] = field(default_factory=list)
    phase_history: List[Tuple[int, ControllerPhase]] = field(default_factory=list)
    
    # Callbacks
    on_grokking: Optional[Callable[[str, SGCMetrics], None]] = None
    on_phase_change: Optional[Callable[[ControllerPhase, ControllerPhase], None]] = None
    
    def start_task(self, task_name: str):
        """Begin training a new task."""
        self.current_task = task_name
        self.phase = ControllerPhase.EXPLORING
        self.thermal.phase = ThermalPhase.HEAT
        self.thermal.heat_start_epoch = self.step
        self.thermal.chi_g_peak_detected = False
        
        print(f"\n{'='*60}")
        print(f"[SGCController] Starting task: {task_name}")
        print(f"[SGCController] Frozen dimensions: {self.constraint.get_frozen_dimension()}")
        print(f"{'='*60}\n")
    
    def step_update(self, model: nn.Module, loss: torch.Tensor,
                    dataloader: Optional[torch.utils.data.DataLoader] = None,
                    device: str = 'cuda') -> SGCMetrics:
        """
        Perform one step of the SGC control loop.
        
        Args:
            model: Neural network
            loss: Current loss tensor
            dataloader: Data loader for ridge ratio computation
            device: Computation device
            
        Returns:
            Current SGC metrics
        """
        self.step += 1
        prev_phase = self.phase
        
        # 1. Inject wavelet noise (during exploration)
        if self.phase == ControllerPhase.EXPLORING:
            if self.step % self.noise_injection_interval == 0:
                kappa_dict = self.wavelet.inject_noise(model)
                avg_kappa = sum(kappa_dict.values()) / len(kappa_dict) if kappa_dict else 0.01
                self.thermal.kappa = avg_kappa
        
        # 2. Apply constrained gradient update
        self.constraint.project_gradient_orthogonal(model)
        
        # 3. Measure SGC metrics
        if self.step % self.measurement_interval == 0:
            metrics = self.engine.measure(model, loss, dataloader, device)
            self.metrics_history.append((self.step, self.current_task, metrics))
            
            # 4. Update thermal pump
            self.thermal.update(
                epsilon=metrics.epsilon,
                chi_g=metrics.chi_g,
                ridge_ratio=metrics.ridge_ratio,
                kappa=self.thermal.kappa,
                grad_epsilon_norm=metrics.grad_norm
            )
            
            # 5. Check phase transitions
            self._update_phase(metrics, model, dataloader, device)
            
            # 6. Notify phase change
            if self.phase != prev_phase and self.on_phase_change:
                self.on_phase_change(prev_phase, self.phase)
            
            return metrics
        
        # Return last metrics if not measurement step
        if self.metrics_history:
            return self.metrics_history[-1][2]
        
        return SGCMetrics(
            epsilon=1.0, chi_g=0.0, ridge_ratio=100.0, k_coarse=1,
            spectral_gap=0.0, effective_rank=1.0, spectral_entropy=0.0,
            grad_norm=0.0, tail_energy=1.0, total_energy=1.0
        )
    
    def _update_phase(self, metrics: SGCMetrics, model: nn.Module,
                      dataloader: Optional[torch.utils.data.DataLoader],
                      device: str):
        """Update controller phase based on current metrics."""
        
        if self.phase == ControllerPhase.EXPLORING:
            # Check if approaching grokking
            if metrics.epsilon < self.grokking_threshold * 2:
                self.phase = ControllerPhase.GROKKING
                self.phase_history.append((self.step, self.phase))
                print(f"[SGCController] Phase: EXPLORING -> GROKKING at step {self.step}")
        
        elif self.phase == ControllerPhase.GROKKING:
            # Check if grokked
            if (metrics.epsilon < self.grokking_threshold and 
                metrics.ridge_ratio < self.ridge_threshold):
                
                self.phase = ControllerPhase.CONSOLIDATING
                self.phase_history.append((self.step, self.phase))
                print(f"[SGCController] Phase: GROKKING -> CONSOLIDATING at step {self.step}")
                print(f"[SGCController] GROKKING DETECTED: ε={metrics.epsilon:.4f}, R={metrics.ridge_ratio:.2f}")
                
                # Notify callback
                if self.on_grokking:
                    self.on_grokking(self.current_task, metrics)
            
            # Check if fell back
            elif metrics.epsilon > self.grokking_threshold * 3:
                self.phase = ControllerPhase.EXPLORING
                self.phase_history.append((self.step, self.phase))
                print(f"[SGCController] Phase: GROKKING -> EXPLORING (regression) at step {self.step}")
        
        elif self.phase == ControllerPhase.CONSOLIDATING:
            # Run thermal quench
            if self.thermal.phase == ThermalPhase.STABLE:
                # Freeze subspace and mark task complete
                if dataloader is not None:
                    self.constraint.freeze_subspace(
                        self.current_task, model, dataloader, device
                    )
                
                self.grokked_tasks.append(self.current_task)
                self.phase = ControllerPhase.FROZEN
                self.phase_history.append((self.step, self.phase))
                print(f"[SGCController] Phase: CONSOLIDATING -> FROZEN at step {self.step}")
                print(f"[SGCController] Task '{self.current_task}' complete!")
    
    def is_task_complete(self) -> bool:
        """Check if current task is complete (frozen)."""
        return self.phase == ControllerPhase.FROZEN
    
    def get_status(self) -> Dict:
        """Get current controller status."""
        return {
            'step': self.step,
            'phase': self.phase.value,
            'current_task': self.current_task,
            'grokked_tasks': self.grokked_tasks.copy(),
            'frozen_dimension': self.constraint.get_frozen_dimension(),
            'thermal': self.thermal.get_status(),
            'metrics': self.engine.current_metrics,
        }
    
    def get_weight_decay(self, base_wd: float = 1.0) -> float:
        """Get current weight decay based on thermal state."""
        return self.thermal.get_weight_decay(base_wd)
