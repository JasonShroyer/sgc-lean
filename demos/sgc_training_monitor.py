"""
SGC Training Monitor: Real-time visualization of SGC metrics during training.

This module provides:
1. SGCTrainer: Training wrapper with integrated SGC control loop
2. Real-time console dashboard showing ε, χ_g, R, phase, actions
3. TensorBoard integration for detailed logging
4. Automatic phase detection and controller intervention

Usage:
    trainer = SGCTrainer(model, train_loader, test_loader, num_classes)
    trainer.train(epochs=2000, measure_interval=25)

Author: SGC Research Team
Date: February 6, 2026
"""

import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import DataLoader, TensorDataset
from torch.utils.tensorboard import SummaryWriter
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple, Callable
from enum import Enum
import time
import os
from datetime import datetime

# Rich console for real-time display
try:
    from rich.console import Console
    from rich.table import Table
    from rich.live import Live
    from rich.panel import Panel
    from rich.progress import Progress, SpinnerColumn, BarColumn, TextColumn
    from rich.layout import Layout
    from rich.text import Text
    RICH_AVAILABLE = True
except ImportError:
    RICH_AVAILABLE = False
    print("Note: Install 'rich' for enhanced real-time display: pip install rich")


class Phase(Enum):
    """SGC phase classification."""
    EXPLORE = "EXPLORE"
    TRANSITION = "TRANSITION"
    GROKKED = "GROKKED"


@dataclass
class SGCState:
    """Current state of the SGC system."""
    epoch: int = 0
    
    # Accuracies
    train_acc: float = 0.0
    test_acc: float = 0.0
    train_loss: float = 0.0
    
    # Primary sensors
    epsilon: float = 1.0           # Functional defect (order parameter)
    chi_g: float = 0.0             # Geometric susceptibility (transition detector)
    ridge_ratio: float = 0.0       # Ridge formation indicator
    class_separation: float = 0.0  # Fisher criterion
    
    # Controller state
    phase: Phase = Phase.EXPLORE
    temperature: float = 0.01
    cooling: float = 0.5
    
    # Derived
    grokking_detected: bool = False
    grokking_epoch: int = -1
    chi_g_peak_epoch: int = -1
    chi_g_peak_value: float = 0.0


@dataclass
class SGCConfig:
    """Configuration for SGC training."""
    # Phase thresholds
    epsilon_grok: float = 0.15      # ε < this → GROKKED
    epsilon_transition: float = 0.5  # ε < this → TRANSITION
    chi_g_threshold: float = 0.01    # χ_g > this → transition imminent
    ridge_threshold: float = 1.0     # R > this → ridges forming
    
    # Controller parameters
    D_explore: float = 0.02         # High temperature (exploration)
    D_transition: float = 0.01      # Medium temperature
    D_grokked: float = 0.005        # Low temperature (consolidation)
    
    lambda_explore: float = 0.3     # Low cooling
    lambda_transition: float = 0.5  # Medium cooling
    lambda_grokked: float = 1.0     # High cooling (weight decay)
    
    # Susceptibility window
    chi_g_window: int = 20          # Window size for Var(ε)
    
    # Logging
    log_dir: str = "logs/sgc_training"
    use_tensorboard: bool = True


class GeometricSusceptibility:
    """
    Computes χ_g = Var(Functional Defect) over a sliding window.
    
    This is the validated geometric sensor that detects phase transitions
    in driven-dissipative systems (SGD). Peaks at grokking.
    """
    
    def __init__(self, window_size: int = 20):
        self.window_size = window_size
        self.epsilon_history: List[float] = []
        self.chi_g_history: List[float] = []
        self.peak_value: float = 0.0
        self.peak_epoch: int = -1
    
    def update(self, epsilon: float, epoch: int) -> float:
        """Update with new ε value and return current χ_g."""
        self.epsilon_history.append(epsilon)
        
        # Keep only recent history
        if len(self.epsilon_history) > self.window_size:
            self.epsilon_history = self.epsilon_history[-self.window_size:]
        
        # Compute variance
        if len(self.epsilon_history) > 1:
            chi_g = np.var(self.epsilon_history)
        else:
            chi_g = 0.0
        
        self.chi_g_history.append(chi_g)
        
        # Track peak
        if chi_g > self.peak_value:
            self.peak_value = chi_g
            self.peak_epoch = epoch
        
        return chi_g
    
    def is_transitioning(self, threshold: float = 0.01) -> bool:
        """Check if system is currently in high-susceptibility state."""
        if len(self.chi_g_history) < 2:
            return False
        
        # Current χ_g above threshold AND increasing
        current = self.chi_g_history[-1]
        previous = self.chi_g_history[-2]
        
        return current > threshold and current > previous


class SGCController:
    """
    SGC Control Loop for grokking optimization.
    
    Sensors:
        - ε (Functional Defect): Order parameter, ε < 0.15 → grokked
        - χ_g (Geometric Susceptibility): Transition detector, peaks at grokking
        - R (Ridge Ratio): Structure indicator
        - Fisher (Class Separation): Metric tensor divergence
    
    Actuators:
        - Temperature (D): Controls exploration vs exploitation
        - Cooling (λ): Weight decay, regularization pressure
        - Freeze: Memory protection for grokked tasks
    """
    
    def __init__(self, config: SGCConfig):
        self.config = config
        self.chi_g_sensor = GeometricSusceptibility(config.chi_g_window)
        self.phase = Phase.EXPLORE
        self.history: List[SGCState] = []
        
        # Frozen parameters for memory protection
        self.frozen_params: Optional[Dict[str, torch.Tensor]] = None
        
        # Phase transition tracking
        self.phase_transitions: List[Tuple[int, str, str]] = []
    
    def step(
        self,
        epoch: int,
        epsilon: float,
        ridge_ratio: float,
        class_separation: float,
        train_acc: float,
        test_acc: float,
        train_loss: float,
        model: Optional[nn.Module] = None
    ) -> SGCState:
        """
        One step of the control loop.
        
        Returns current state with computed actions.
        """
        # Update χ_g sensor
        chi_g = self.chi_g_sensor.update(epsilon, epoch)
        
        # Phase detection
        old_phase = self.phase
        self._update_phase(epsilon, ridge_ratio, chi_g)
        
        # Log phase transition
        if self.phase != old_phase:
            self.phase_transitions.append((epoch, old_phase.value, self.phase.value))
            if model is not None and self.phase == Phase.GROKKED:
                self._freeze_parameters(model)
        
        # Get control actions
        temperature, cooling = self._get_control_actions()
        
        # Build state
        state = SGCState(
            epoch=epoch,
            train_acc=train_acc,
            test_acc=test_acc,
            train_loss=train_loss,
            epsilon=epsilon,
            chi_g=chi_g,
            ridge_ratio=ridge_ratio,
            class_separation=class_separation,
            phase=self.phase,
            temperature=temperature,
            cooling=cooling,
            grokking_detected=self.phase == Phase.GROKKED,
            grokking_epoch=self._get_grokking_epoch(),
            chi_g_peak_epoch=self.chi_g_sensor.peak_epoch,
            chi_g_peak_value=self.chi_g_sensor.peak_value,
        )
        
        self.history.append(state)
        return state
    
    def _update_phase(self, epsilon: float, ridge_ratio: float, chi_g: float):
        """Update phase based on sensor readings."""
        cfg = self.config
        
        if self.phase == Phase.EXPLORE:
            # Transition to TRANSITION when ridges form or χ_g spikes
            if ridge_ratio > cfg.ridge_threshold or chi_g > cfg.chi_g_threshold:
                self.phase = Phase.TRANSITION
        
        elif self.phase == Phase.TRANSITION:
            # Transition to GROKKED when ε drops below threshold
            if epsilon < cfg.epsilon_grok:
                self.phase = Phase.GROKKED
            # Return to EXPLORE if structure lost
            elif epsilon > 0.8 and ridge_ratio < 0.5:
                self.phase = Phase.EXPLORE
        
        elif self.phase == Phase.GROKKED:
            # Return to TRANSITION if ε rises (catastrophic forgetting)
            if epsilon > cfg.epsilon_transition:
                self.phase = Phase.TRANSITION
                self.frozen_params = None  # Release protection
    
    def _get_control_actions(self) -> Tuple[float, float]:
        """Get temperature and cooling based on current phase."""
        cfg = self.config
        
        if self.phase == Phase.EXPLORE:
            return cfg.D_explore, cfg.lambda_explore
        elif self.phase == Phase.TRANSITION:
            return cfg.D_transition, cfg.lambda_transition
        else:  # GROKKED
            return cfg.D_grokked, cfg.lambda_grokked
    
    def _freeze_parameters(self, model: nn.Module):
        """Snapshot parameters for memory protection."""
        self.frozen_params = {
            name: param.clone().detach()
            for name, param in model.named_parameters()
        }
    
    def _get_grokking_epoch(self) -> int:
        """Get epoch when grokking was first detected."""
        for state in self.history:
            if state.grokking_detected:
                return state.epoch
        return -1
    
    def apply_to_optimizer(self, optimizer: torch.optim.Optimizer, base_lr: float):
        """Apply current control actions to optimizer."""
        temperature, cooling = self._get_control_actions()
        
        for param_group in optimizer.param_groups:
            # Scale LR by temperature (higher T = more exploration)
            param_group['lr'] = base_lr * (temperature / self.config.D_explore)
            param_group['weight_decay'] = cooling
    
    def apply_memory_protection(self, model: nn.Module, alpha: float = 0.3):
        """
        Apply elastic memory protection.
        
        Pulls parameters toward frozen snapshot to prevent forgetting.
        """
        if self.frozen_params is None or self.phase != Phase.GROKKED:
            return
        
        with torch.no_grad():
            for name, param in model.named_parameters():
                if name in self.frozen_params:
                    drift = param - self.frozen_params[name]
                    param.sub_(alpha * drift)


class RealTimeMonitor:
    """Real-time console display of SGC training metrics."""
    
    def __init__(self, use_rich: bool = True):
        self.use_rich = use_rich and RICH_AVAILABLE
        if self.use_rich:
            self.console = Console()
        self.start_time = time.time()
    
    def format_phase(self, phase: Phase) -> str:
        """Format phase with color."""
        if not self.use_rich:
            return phase.value
        
        colors = {
            Phase.EXPLORE: "yellow",
            Phase.TRANSITION: "cyan",
            Phase.GROKKED: "green",
        }
        return f"[{colors[phase]}]{phase.value}[/{colors[phase]}]"
    
    def display(self, state: SGCState, extra: Dict = None):
        """Display current state."""
        elapsed = time.time() - self.start_time
        
        if self.use_rich:
            self._display_rich(state, elapsed, extra)
        else:
            self._display_simple(state, elapsed, extra)
    
    def _display_simple(self, state: SGCState, elapsed: float, extra: Dict):
        """Simple console display."""
        phase_str = state.phase.value
        chi_marker = " <-chi" if state.chi_g == state.chi_g_peak_value and state.chi_g > 0.001 else ""
        grok_marker = " <-GROK" if state.grokking_detected and state.epoch == state.grokking_epoch else ""
        
        print(f"E{state.epoch:5d} | "
              f"Train:{state.train_acc:6.1%} Test:{state.test_acc:6.1%} | "
              f"eps:{state.epsilon:6.4f} chi_g:{state.chi_g:8.6f} R:{state.ridge_ratio:5.2f} | "
              f"{phase_str:10s} T:{state.temperature:.4f} wd:{state.cooling:.2f}"
              f"{chi_marker}{grok_marker}")
    
    def _display_rich(self, state: SGCState, elapsed: float, extra: Dict):
        """Rich console display with colors and formatting."""
        # Phase indicator with color
        phase_colors = {
            Phase.EXPLORE: "yellow",
            Phase.TRANSITION: "cyan", 
            Phase.GROKKED: "bright_green",
        }
        phase_color = phase_colors[state.phase]
        
        # ε color based on value
        if state.epsilon < 0.15:
            eps_color = "bright_green"
        elif state.epsilon < 0.5:
            eps_color = "cyan"
        else:
            eps_color = "yellow"
        
        # χ_g marker
        chi_marker = ""
        if state.chi_g == state.chi_g_peak_value and state.chi_g > 0.001:
            chi_marker = " [bright_red]<-chi_peak[/bright_red]"
        
        # Grokking marker
        grok_marker = ""
        if state.grokking_detected and state.epoch == state.grokking_epoch:
            grok_marker = " [bright_green bold]*** GROKKED ***[/bright_green bold]"
        
        # Build output line
        line = (
            f"[dim]E{state.epoch:5d}[/dim] | "
            f"Train:[bright_white]{state.train_acc:6.1%}[/bright_white] "
            f"Test:[bright_white]{state.test_acc:6.1%}[/bright_white] | "
            f"eps:[{eps_color}]{state.epsilon:6.4f}[/{eps_color}] "
            f"chi_g:{state.chi_g:8.6f}{chi_marker} "
            f"R:{state.ridge_ratio:5.2f} | "
            f"[{phase_color}]{state.phase.value:10s}[/{phase_color}] "
            f"[dim]T:{state.temperature:.4f} wd:{state.cooling:.2f}[/dim]"
            f"{grok_marker}"
        )
        
        self.console.print(line)
    
    def display_summary(self, controller: SGCController):
        """Display final summary."""
        if not controller.history:
            return
        
        final = controller.history[-1]
        
        if self.use_rich:
            self.console.print("\n" + "=" * 80)
            self.console.print("[bold]SGC TRAINING SUMMARY[/bold]")
            self.console.print("=" * 80)
            
            # Phase transitions
            if controller.phase_transitions:
                self.console.print("\n[bold]Phase Transitions:[/bold]")
                for epoch, from_phase, to_phase in controller.phase_transitions:
                    self.console.print(f"  Epoch {epoch}: {from_phase} -> {to_phase}")
            
            # Key metrics
            self.console.print(f"\n[bold]Final State:[/bold]")
            self.console.print(f"  Phase: {final.phase.value}")
            self.console.print(f"  eps (Functional Defect): {final.epsilon:.4f}")
            self.console.print(f"  Grokking Detected: {final.grokking_detected}")
            
            if final.grokking_detected:
                self.console.print(f"  Grokking Epoch: {final.grokking_epoch}")
            
            # χ_g analysis
            self.console.print(f"\n[bold]Geometric Susceptibility (chi_g):[/bold]")
            self.console.print(f"  Peak Value: {final.chi_g_peak_value:.6f}")
            self.console.print(f"  Peak Epoch: {final.chi_g_peak_epoch}")
            
            if final.grokking_detected and final.chi_g_peak_epoch > 0:
                gap = abs(final.chi_g_peak_epoch - final.grokking_epoch)
                aligned = gap < 150
                status = "[green]ALIGNED[/green]" if aligned else "[yellow]OFFSET[/yellow]"
                self.console.print(f"  Gap from Grokking: {gap} epochs {status}")
        else:
            print("\n" + "=" * 80)
            print("SGC TRAINING SUMMARY")
            print("=" * 80)
            print(f"Final Phase: {final.phase.value}")
            print(f"Grokking: {final.grokking_detected} (epoch {final.grokking_epoch})")
            print(f"χ_g Peak: {final.chi_g_peak_value:.6f} at epoch {final.chi_g_peak_epoch}")


class SGCTrainer:
    """
    Complete SGC training system with integrated control loop and monitoring.
    """
    
    def __init__(
        self,
        model: nn.Module,
        train_loader: DataLoader,
        test_loader: DataLoader,
        num_classes: int,
        config: SGCConfig = None,
        device: str = None,
        get_hidden_fn: Callable = None,
    ):
        self.model = model
        self.train_loader = train_loader
        self.test_loader = test_loader
        self.num_classes = num_classes
        self.config = config or SGCConfig()
        self.device = device or ('cuda' if torch.cuda.is_available() else 'cpu')
        self.get_hidden_fn = get_hidden_fn
        
        # Move model to device
        self.model.to(self.device)
        
        # Initialize controller and monitor
        self.controller = SGCController(self.config)
        self.monitor = RealTimeMonitor()
        
        # TensorBoard
        self.writer = None
        if self.config.use_tensorboard:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            log_path = os.path.join(self.config.log_dir, f"run_{timestamp}")
            os.makedirs(log_path, exist_ok=True)
            self.writer = SummaryWriter(log_path)
            print(f"TensorBoard logging to: {log_path}")
    
    def compute_metrics(self) -> Dict[str, float]:
        """Compute all SGC metrics from current model state."""
        self.model.eval()
        
        all_hidden = []
        all_labels = []
        
        with torch.no_grad():
            for batch in self.train_loader:
                if len(batch) == 3:  # (a, b, target) for modular arithmetic
                    inp_a, inp_b, target = batch
                    inp_a = inp_a.to(self.device)
                    inp_b = inp_b.to(self.device)
                    target = target.to(self.device)
                    
                    if self.get_hidden_fn:
                        hidden = self.get_hidden_fn(self.model, inp_a, inp_b)
                    elif hasattr(self.model, 'get_hidden'):
                        hidden = self.model.get_hidden(inp_a, inp_b)
                    else:
                        # Fallback: use model output logits
                        hidden = self.model(inp_a, inp_b)
                else:
                    x, target = batch[0].to(self.device), batch[1].to(self.device)
                    if hasattr(self.model, 'get_hidden'):
                        hidden = self.model.get_hidden(x)
                    else:
                        hidden = self.model(x)
                
                all_hidden.append(hidden)
                all_labels.append(target)
        
        hidden = torch.cat(all_hidden, dim=0)
        labels = torch.cat(all_labels, dim=0)
        
        # Compute functional defect
        epsilon, class_sep, total_var = self._compute_functional_defect(hidden, labels)
        
        # Compute ridge ratio
        ridge_ratio = self._compute_ridge_ratio(hidden, labels)
        
        return {
            'epsilon': epsilon,
            'class_separation': class_sep,
            'ridge_ratio': ridge_ratio,
            'total_variance': total_var,
        }
    
    def _compute_functional_defect(
        self, hidden: torch.Tensor, labels: torch.Tensor
    ) -> Tuple[float, float, float]:
        """
        Compute eps = within-class variance / total variance.
        
        Uses per-dimension variance aggregation for proper defect calculation.
        """
        h = hidden.detach().float()
        n_samples, n_features = h.shape
        
        # Total variance: mean of per-feature variances
        total_var = h.var(dim=0).mean().item()
        
        if total_var < 1e-10:
            return 1.0, 0.0, total_var
        
        # Within-class variance: weighted average of per-class variances
        within_var = 0.0
        class_means = []
        total_count = 0
        
        for c in range(self.num_classes):
            mask = (labels == c)
            count = mask.sum().item()
            if count > 1:
                class_h = h[mask]
                # Variance per feature, then mean across features
                class_var = class_h.var(dim=0).mean().item()
                within_var += class_var * count
                class_means.append(class_h.mean(dim=0))
                total_count += count
        
        if total_count > 0:
            within_var /= total_count
        
        # Between-class variance (class mean separation)
        if len(class_means) > 1:
            class_means_tensor = torch.stack(class_means)
            between_var = class_means_tensor.var(dim=0).mean().item()
            class_sep = between_var / (within_var + 1e-10)
        else:
            class_sep = 0.0
            between_var = 0.0
        
        # Functional defect: within / total
        epsilon = within_var / (total_var + 1e-10)
        
        return epsilon, class_sep, total_var
    
    def _compute_ridge_ratio(
        self, hidden: torch.Tensor, labels: torch.Tensor, k: int = 10
    ) -> float:
        """Compute R = E_between / E_within."""
        h = hidden.detach()
        n = len(h)
        
        # Sample for efficiency
        if n > 500:
            idx = torch.randperm(n)[:500]
            h = h[idx]
            labels = labels[idx]
            n = 500
        
        # Compute pairwise distances
        dists = torch.cdist(h, h)
        
        E_within = 0.0
        E_between = 0.0
        n_within = 0
        n_between = 0
        
        for i in range(min(n, 200)):  # Sample rows for speed
            _, neighbors = torch.topk(dists[i], min(k + 1, n), largest=False)
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
    
    def train_epoch(
        self, optimizer: torch.optim.Optimizer, loss_fn: nn.Module
    ) -> Tuple[float, float]:
        """Train one epoch, return (loss, accuracy)."""
        self.model.train()
        total_loss = 0.0
        correct = 0
        total = 0
        
        for batch in self.train_loader:
            if len(batch) == 3:
                inp_a, inp_b, target = batch
                inp_a = inp_a.to(self.device)
                inp_b = inp_b.to(self.device)
                target = target.to(self.device)
                
                optimizer.zero_grad()
                output = self.model(inp_a, inp_b)
                loss = loss_fn(output, target)
            else:
                x, target = batch[0].to(self.device), batch[1].to(self.device)
                optimizer.zero_grad()
                output = self.model(x)
                loss = loss_fn(output, target)
            
            loss.backward()
            optimizer.step()
            
            total_loss += loss.item() * len(target)
            correct += (output.argmax(dim=1) == target).sum().item()
            total += len(target)
        
        return total_loss / total, correct / total
    
    def evaluate(self, loss_fn: nn.Module) -> Tuple[float, float]:
        """Evaluate on test set, return (loss, accuracy)."""
        self.model.eval()
        total_loss = 0.0
        correct = 0
        total = 0
        
        with torch.no_grad():
            for batch in self.test_loader:
                if len(batch) == 3:
                    inp_a, inp_b, target = batch
                    inp_a = inp_a.to(self.device)
                    inp_b = inp_b.to(self.device)
                    target = target.to(self.device)
                    output = self.model(inp_a, inp_b)
                else:
                    x, target = batch[0].to(self.device), batch[1].to(self.device)
                    output = self.model(x)
                
                loss = loss_fn(output, target)
                total_loss += loss.item() * len(target)
                correct += (output.argmax(dim=1) == target).sum().item()
                total += len(target)
        
        return total_loss / total, correct / total
    
    def train(
        self,
        epochs: int = 2000,
        lr: float = 1e-3,
        weight_decay: float = 0.5,
        measure_interval: int = 25,
        apply_control: bool = True,
    ):
        """
        Full training loop with SGC control and monitoring.
        """
        optimizer = torch.optim.AdamW(
            self.model.parameters(),
            lr=lr,
            weight_decay=weight_decay
        )
        loss_fn = nn.CrossEntropyLoss()
        base_lr = lr
        
        # Header
        if RICH_AVAILABLE:
            self.monitor.console.print("\n" + "=" * 90)
            self.monitor.console.print("[bold]SGC TRAINING WITH REAL-TIME MONITORING[/bold]")
            self.monitor.console.print("=" * 90)
            self.monitor.console.print(f"Device: {self.device} | Epochs: {epochs} | Measure: every {measure_interval}")
            self.monitor.console.print(f"Control: {'ENABLED' if apply_control else 'DISABLED'}")
            self.monitor.console.print("-" * 90)
            self.monitor.console.print(
                "[dim]Epoch[/dim] | Train      Test    | "
                "eps     chi_g        R    | Phase      T     wd"
            )
            self.monitor.console.print("-" * 90)
        else:
            print("\n" + "=" * 90)
            print("SGC TRAINING WITH REAL-TIME MONITORING")
            print("=" * 90)
            print(f"Device: {self.device} | Epochs: {epochs}")
            print("-" * 90)
        
        for epoch in range(1, epochs + 1):
            # Train one epoch
            train_loss, train_acc = self.train_epoch(optimizer, loss_fn)
            
            # Measure SGC metrics at intervals
            if epoch % measure_interval == 0 or epoch == 1:
                # Evaluate
                test_loss, test_acc = self.evaluate(loss_fn)
                
                # Compute SGC metrics
                metrics = self.compute_metrics()
                
                # Controller step
                state = self.controller.step(
                    epoch=epoch,
                    epsilon=metrics['epsilon'],
                    ridge_ratio=metrics['ridge_ratio'],
                    class_separation=metrics['class_separation'],
                    train_acc=train_acc,
                    test_acc=test_acc,
                    train_loss=train_loss,
                    model=self.model if apply_control else None,
                )
                
                # Apply control actions
                if apply_control:
                    self.controller.apply_to_optimizer(optimizer, base_lr)
                    self.controller.apply_memory_protection(self.model)
                
                # Display
                self.monitor.display(state)
                
                # TensorBoard logging
                if self.writer:
                    self.writer.add_scalar('Accuracy/train', train_acc, epoch)
                    self.writer.add_scalar('Accuracy/test', test_acc, epoch)
                    self.writer.add_scalar('Loss/train', train_loss, epoch)
                    self.writer.add_scalar('SGC/epsilon', state.epsilon, epoch)
                    self.writer.add_scalar('SGC/chi_g', state.chi_g, epoch)
                    self.writer.add_scalar('SGC/ridge_ratio', state.ridge_ratio, epoch)
                    self.writer.add_scalar('SGC/class_separation', state.class_separation, epoch)
                    self.writer.add_scalar('Control/temperature', state.temperature, epoch)
                    self.writer.add_scalar('Control/cooling', state.cooling, epoch)
                    self.writer.add_scalar('Control/phase', 
                                          {'EXPLORE': 0, 'TRANSITION': 1, 'GROKKED': 2}[state.phase.value],
                                          epoch)
        
        # Summary
        self.monitor.display_summary(self.controller)
        
        if self.writer:
            self.writer.close()
        
        return self.controller.history


# =============================================================================
# Demo: Modular Addition with SGC Control
# =============================================================================

def create_modular_dataset(p: int = 97, train_frac: float = 0.5):
    """Create modular addition dataset."""
    all_pairs = [(a, b) for a in range(p) for b in range(p)]
    np.random.shuffle(all_pairs)
    
    n_train = int(len(all_pairs) * train_frac)
    train_pairs = all_pairs[:n_train]
    test_pairs = all_pairs[n_train:]
    
    def to_tensors(pairs, modulus):
        a = torch.tensor([pair[0] for pair in pairs], dtype=torch.long)
        b = torch.tensor([pair[1] for pair in pairs], dtype=torch.long)
        c = torch.tensor([(pair[0] + pair[1]) % modulus for pair in pairs], dtype=torch.long)
        return a, b, c
    
    train_a, train_b, train_c = to_tensors(train_pairs, p)
    test_a, test_b, test_c = to_tensors(test_pairs, p)
    
    return (train_a, train_b, train_c), (test_a, test_b, test_c)


class GrokMLP(nn.Module):
    """Simple MLP for modular arithmetic."""
    
    def __init__(self, p: int, embed_dim: int = 128, hidden_dim: int = 128):
        super().__init__()
        self.embed_a = nn.Embedding(p, embed_dim)
        self.embed_b = nn.Embedding(p, embed_dim)
        self.fc1 = nn.Linear(embed_dim * 2, hidden_dim)
        self.fc2 = nn.Linear(hidden_dim, hidden_dim)
        self.fc3 = nn.Linear(hidden_dim, p)
    
    def forward(self, a, b):
        ea = self.embed_a(a)
        eb = self.embed_b(b)
        x = torch.cat([ea, eb], dim=-1)
        x = F.relu(self.fc1(x))
        x = F.relu(self.fc2(x))
        return self.fc3(x)
    
    def get_hidden(self, a, b):
        ea = self.embed_a(a)
        eb = self.embed_b(b)
        x = torch.cat([ea, eb], dim=-1)
        x = F.relu(self.fc1(x))
        return F.relu(self.fc2(x))


def run_sgc_demo():
    """Run SGC training demo with real-time monitoring."""
    print("\n" + "=" * 80)
    print("SGC CONTROLLER PHASE 1 DEMO")
    print("Modular Addition with Geometric Susceptibility Monitoring")
    print("=" * 80)
    
    # Setup
    p = 97
    torch.manual_seed(42)
    np.random.seed(42)
    
    # Create dataset
    (train_a, train_b, train_c), (test_a, test_b, test_c) = create_modular_dataset(p)
    train_dataset = TensorDataset(train_a, train_b, train_c)
    test_dataset = TensorDataset(test_a, test_b, test_c)
    train_loader = DataLoader(train_dataset, batch_size=512, shuffle=True)
    test_loader = DataLoader(test_dataset, batch_size=512)
    
    # Create model
    model = GrokMLP(p, embed_dim=128, hidden_dim=128)
    
    # Configure SGC
    config = SGCConfig(
        epsilon_grok=0.15,
        epsilon_transition=0.5,
        chi_g_window=20,
        log_dir="logs/sgc_phase1_demo",
    )
    
    # Create trainer
    trainer = SGCTrainer(
        model=model,
        train_loader=train_loader,
        test_loader=test_loader,
        num_classes=p,
        config=config,
    )
    
    # Train with SGC control
    history = trainer.train(
        epochs=2000,
        lr=1e-3,
        weight_decay=0.5,
        measure_interval=25,
        apply_control=True,
    )
    
    return history


if __name__ == "__main__":
    run_sgc_demo()
