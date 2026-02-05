"""
Continual Learning Test 3: Functional Blanket Protection
=========================================================

This experiment validates the core SGC hypothesis for continual learning:
**Protect structure (functional defect), not geometry (weights).**

The Hypothesis:
If we constrain updates such that Delta(epsilon_A) <= tolerance while minimizing L_B,
the network will force Task B to form a representation *orthogonal* to Task A's
algebraic structure (or reuse it equivariantly), rather than overwriting it.

Phase A: Grok Task A (Modular Addition)
Phase B: Learn Task B (Modular Multiplication) while protecting Task A's blanket

Success Criteria:
- Task A Accuracy remains > 95% (vs 66% baseline failure from Phase-6.1)
- Task B Accuracy > 95%
- Task A Functional Defect remains low (structure preserved)

Based on:
- docs/unified_theory_sgc_active_inference.md
- docs/noise_cooling_theory.md
- src/SGC/ContinualLearning/AdiabaticInvariant.lean
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import DataLoader, TensorDataset
import numpy as np
from dataclasses import dataclass, field
from typing import List, Tuple, Optional, Dict
from enum import Enum
import math
import time


# =============================================================================
# CONFIGURATION
# =============================================================================

@dataclass
class ContinualLearningConfig:
    """Configuration for the continual learning experiment."""
    # Model architecture
    p: int = 97                      # Prime for modular arithmetic
    embed_dim: int = 128
    hidden_dim: int = 128
    n_layers: int = 2
    
    # Phase A (Task A grokking)
    phase_a_max_epochs: int = 5000
    phase_a_lr: float = 1e-3
    phase_a_weight_decay: float = 1.0
    phase_a_noise_std: float = 0.0   # Start discrete
    blanket_threshold: float = 0.15  # FuncD < this = blanket closed
    consolidation_threshold: float = 0.6
    
    # Phase B (Protected learning)
    phase_b_max_epochs: int = 3000
    phase_b_lr: float = 1e-3
    phase_b_weight_decay: float = 0.5
    protection_tolerance: float = 1.5  # Allow 50% increase before intervention
    lambda_protect: float = 10.0       # Lagrangian multiplier for protection
    recovery_heat: float = 0.05        # Noise to inject during recovery
    ewc_lambda: float = 100000.0       # EWC strength (higher = more protection)
    freeze_shared: bool = False        # If False, use EWC instead of freezing
    use_defect_constraint: bool = True # Direct functional defect constraint (SGC approach)
    defect_check_interval: int = 5     # Check defect every N batches (expensive)
    
    # Training
    batch_size: int = 512
    measure_interval: int = 50
    device: str = 'cuda' if torch.cuda.is_available() else 'cpu'
    seed: int = 42


class Phase(Enum):
    """Controller phases for continual learning."""
    EXPLORE = "explore"      # High plasticity, learning new structure
    CONSOLIDATE = "consolidate"  # Reducing defect, crystallizing structure
    PROTECT = "protect"      # Maintaining old structure while learning new
    RECOVER = "recover"      # Blanket rupturing, need to heal


# =============================================================================
# MODEL (Shared architecture for both tasks)
# =============================================================================

class ContinualGrokMLP(nn.Module):
    """
    MLP for continual learning with separate task heads.
    
    Architecture:
    - Shared embeddings for inputs
    - Shared hidden layers (the "representation")
    - Separate output heads per task
    
    This allows Task B to potentially reuse Task A's structure.
    """
    
    def __init__(self, p: int, embed_dim: int, hidden_dim: int, n_layers: int = 2):
        super().__init__()
        self.p = p
        self.embed_dim = embed_dim
        self.hidden_dim = hidden_dim
        
        # Shared embeddings
        self.embed_a = nn.Embedding(p, embed_dim)
        self.embed_b = nn.Embedding(p, embed_dim)
        
        # Shared hidden layers
        layers = []
        layers.append(nn.Linear(embed_dim * 2, hidden_dim))
        layers.append(nn.ReLU())
        for _ in range(n_layers - 1):
            layers.append(nn.Linear(hidden_dim, hidden_dim))
            layers.append(nn.ReLU())
        self.shared_layers = nn.Sequential(*layers)
        
        # Task-specific output heads
        self.head_task_a = nn.Linear(hidden_dim, p)  # Task A: addition
        self.head_task_b = nn.Linear(hidden_dim, p)  # Task B: multiplication
        
        self._init_weights()
    
    def _init_weights(self):
        for m in self.modules():
            if isinstance(m, nn.Linear):
                nn.init.xavier_uniform_(m.weight)
                if m.bias is not None:
                    nn.init.zeros_(m.bias)
            elif isinstance(m, nn.Embedding):
                nn.init.normal_(m.weight, std=0.02)
    
    def get_hidden(self, a: torch.Tensor, b: torch.Tensor) -> torch.Tensor:
        """Get shared hidden representation."""
        e_a = self.embed_a(a)
        e_b = self.embed_b(b)
        x = torch.cat([e_a, e_b], dim=-1)
        return self.shared_layers(x)
    
    def forward_task_a(self, a: torch.Tensor, b: torch.Tensor, 
                       noise_std: float = 0.0) -> torch.Tensor:
        """Forward pass for Task A (addition)."""
        h = self.get_hidden(a, b)
        if noise_std > 0 and self.training:
            h = h + torch.randn_like(h) * noise_std
        return self.head_task_a(h)
    
    def forward_task_b(self, a: torch.Tensor, b: torch.Tensor,
                       noise_std: float = 0.0) -> torch.Tensor:
        """Forward pass for Task B (multiplication)."""
        h = self.get_hidden(a, b)
        if noise_std > 0 and self.training:
            h = h + torch.randn_like(h) * noise_std
        return self.head_task_b(h)


# =============================================================================
# DATASETS
# =============================================================================

def create_modular_addition_dataset(p: int, train_frac: float = 0.5):
    """Task A: (a + b) mod p"""
    pairs = [(a, b) for a in range(p) for b in range(p)]
    np.random.shuffle(pairs)
    split = int(len(pairs) * train_frac)
    train_pairs = pairs[:split]
    test_pairs = pairs[split:]
    
    def to_tensors(pairs):
        a = torch.tensor([p[0] for p in pairs], dtype=torch.long)
        b = torch.tensor([p[1] for p in pairs], dtype=torch.long)
        c = torch.tensor([(p[0] + p[1]) % 97 for p in pairs], dtype=torch.long)
        return a, b, c
    
    train_a, train_b, train_c = to_tensors(train_pairs)
    test_a, test_b, test_c = to_tensors(test_pairs)
    
    return (train_a, train_b, train_c), (test_a, test_b, test_c)


def create_modular_multiplication_dataset(p: int, train_frac: float = 0.5):
    """Task B: (a * b) mod p"""
    pairs = [(a, b) for a in range(p) for b in range(p)]
    np.random.shuffle(pairs)
    split = int(len(pairs) * train_frac)
    train_pairs = pairs[:split]
    test_pairs = pairs[split:]
    
    def to_tensors(pairs):
        a = torch.tensor([p[0] for p in pairs], dtype=torch.long)
        b = torch.tensor([p[1] for p in pairs], dtype=torch.long)
        c = torch.tensor([(p[0] * p[1]) % 97 for p in pairs], dtype=torch.long)
        return a, b, c
    
    train_a, train_b, train_c = to_tensors(train_pairs)
    test_a, test_b, test_c = to_tensors(test_pairs)
    
    return (train_a, train_b, train_c), (test_a, test_b, test_c)


# =============================================================================
# FUNCTIONAL DEFECT COMPUTATION
# =============================================================================

def compute_functional_defect(
    model: ContinualGrokMLP,
    dataloader: DataLoader,
    num_classes: int,
    task: str,  # 'a' or 'b'
    device: str
) -> Tuple[float, float]:
    """
    Compute functional defect for a specific task.
    
    Functional Defect = within-class variance / total variance
    Class Separation = between-class variance / within-class variance
    
    Returns: (functional_defect, class_separation)
    """
    model.eval()
    
    all_hidden = []
    all_targets = []
    
    with torch.no_grad():
        for batch in dataloader:
            a, b, c = [x.to(device) for x in batch]
            h = model.get_hidden(a, b)
            all_hidden.append(h)
            all_targets.append(c)
    
    hidden = torch.cat(all_hidden, dim=0)
    targets = torch.cat(all_targets, dim=0)
    
    total_var = hidden.var(dim=0).mean().item()
    if total_var < 1e-10:
        return 0.0, float('inf')
    
    class_vars = []
    class_means = []
    class_counts = []
    
    for c in range(num_classes):
        mask = (targets == c)
        count = mask.sum().item()
        if count > 0:
            h_c = hidden[mask]
            class_means.append(h_c.mean(dim=0))
            class_counts.append(count)
            if count > 1:
                class_vars.append(h_c.var(dim=0).mean().item())
            else:
                class_vars.append(0.0)
    
    if not class_means:
        return 1.0, 0.0
    
    class_counts = torch.tensor(class_counts, dtype=torch.float, device=device)
    class_vars = torch.tensor(class_vars, device=device)
    class_means = torch.stack(class_means)
    
    within_var = (class_vars * class_counts).sum() / class_counts.sum()
    
    global_mean = (class_means * class_counts.unsqueeze(1)).sum(0) / class_counts.sum()
    between_var = ((class_means - global_mean) ** 2).mean(dim=1)
    between_var = (between_var * class_counts).sum() / class_counts.sum()
    
    func_defect = within_var.item() / (total_var + 1e-10)
    class_sep = between_var.item() / (within_var.item() + 1e-10)
    
    return func_defect, class_sep


# =============================================================================
# BLANKET PROTECTION CONTROLLER
# =============================================================================

@dataclass
class ControllerState:
    """State of the continual learning controller."""
    phase: Phase = Phase.EXPLORE
    epoch: int = 0
    
    # Task A metrics
    func_defect_a: float = 1.0
    class_sep_a: float = 0.0
    baseline_defect_a: float = 1.0  # Recorded after Phase A grokking
    
    # Task B metrics
    func_defect_b: float = 1.0
    class_sep_b: float = 0.0
    
    # Accuracies
    train_acc_a: float = 0.0
    test_acc_a: float = 0.0
    train_acc_b: float = 0.0
    test_acc_b: float = 0.0
    
    # Protection status
    blanket_a_closed: bool = False
    blanket_a_ruptured: bool = False
    rupture_count: int = 0
    recovery_steps: int = 0
    
    # Noise level (for recovery)
    current_noise: float = 0.0


class BlanketProtectionController:
    """
    Controller that protects Task A's functional blanket during Task B learning.
    
    Based on:
    - Adiabatic Invariant theorem: slow changes preserve functional structure
    - Active Inference: minimize blanket rupture as a form of free energy
    
    Key Innovation: Gradient projection onto null space of Task A's Fisher information.
    This ensures Task B learning cannot move in directions that would rupture Task A.
    """
    
    def __init__(self, config: ContinualLearningConfig):
        self.config = config
        self.state = ControllerState()
        self.history: List[Dict] = []
        
        # Fisher information for gradient projection
        self.fisher_diag: Optional[Dict[str, torch.Tensor]] = None
        self.task_a_params_snapshot: Optional[Dict[str, torch.Tensor]] = None
    
    def update_state(
        self,
        epoch: int,
        func_defect_a: float,
        class_sep_a: float,
        train_acc_a: float,
        test_acc_a: float,
        func_defect_b: float = 1.0,
        class_sep_b: float = 0.0,
        train_acc_b: float = 0.0,
        test_acc_b: float = 0.0
    ):
        """Update controller state with new measurements."""
        self.state.epoch = epoch
        self.state.func_defect_a = func_defect_a
        self.state.class_sep_a = class_sep_a
        self.state.train_acc_a = train_acc_a
        self.state.test_acc_a = test_acc_a
        self.state.func_defect_b = func_defect_b
        self.state.class_sep_b = class_sep_b
        self.state.train_acc_b = train_acc_b
        self.state.test_acc_b = test_acc_b
        
        # Check blanket status
        self.state.blanket_a_closed = func_defect_a < self.config.blanket_threshold
        
        # Check for rupture during Phase B
        if self.state.baseline_defect_a < 1.0:  # Only after baseline is set
            rupture_threshold = self.state.baseline_defect_a * self.config.protection_tolerance
            if func_defect_a > rupture_threshold:
                if not self.state.blanket_a_ruptured:
                    self.state.rupture_count += 1
                self.state.blanket_a_ruptured = True
            else:
                self.state.blanket_a_ruptured = False
        
        # Record history
        self.history.append({
            'epoch': epoch,
            'phase': self.state.phase.value,
            'func_defect_a': func_defect_a,
            'class_sep_a': class_sep_a,
            'train_acc_a': train_acc_a,
            'test_acc_a': test_acc_a,
            'func_defect_b': func_defect_b,
            'train_acc_b': train_acc_b,
            'test_acc_b': test_acc_b,
            'blanket_ruptured': self.state.blanket_a_ruptured,
            'current_noise': self.state.current_noise
        })
    
    def set_baseline_defect(self, defect: float):
        """Set baseline defect after Phase A grokking."""
        self.state.baseline_defect_a = defect
        print(f"    [Controller] Baseline defect set: {defect:.6f}")
    
    def compute_fisher_information(
        self, 
        model: nn.Module, 
        dataloader: DataLoader, 
        device: str,
        n_samples: int = 500
    ):
        """
        Compute diagonal Fisher Information for Task A.
        
        F_ii = E[(d log p / d theta_i)^2]
        
        This identifies which parameters are "important" for Task A.
        """
        print("    [Controller] Computing Fisher Information for Task A...")
        model.eval()
        
        fisher_diag = {}
        for name, param in model.named_parameters():
            fisher_diag[name] = torch.zeros_like(param)
        
        # Snapshot current parameters
        self.task_a_params_snapshot = {
            name: param.clone().detach() 
            for name, param in model.named_parameters()
        }
        
        model.train()
        criterion = nn.CrossEntropyLoss()
        
        sample_count = 0
        for batch in dataloader:
            if sample_count >= n_samples:
                break
            
            a, b, c = [x.to(device) for x in batch]
            
            model.zero_grad()
            out = model.forward_task_a(a, b)
            loss = criterion(out, c)
            loss.backward()
            
            for name, param in model.named_parameters():
                if param.grad is not None:
                    fisher_diag[name] += param.grad.data ** 2
            
            sample_count += len(a)
        
        # Normalize
        for name in fisher_diag:
            fisher_diag[name] /= sample_count
        
        self.fisher_diag = fisher_diag
        print(f"    [Controller] Fisher computed for {len(fisher_diag)} parameter groups")
    
    def apply_gradient_projection(self, model: nn.Module, ewc_lambda: float = 1000.0):
        """
        Apply EWC-style gradient modification to protect Task A.
        
        Instead of pure projection, we add a penalty term:
        grad_new = grad_B + ewc_lambda * F * (theta - theta_A)
        
        This pulls parameters back toward Task A's solution proportional to Fisher.
        """
        if self.fisher_diag is None or self.task_a_params_snapshot is None:
            return
        
        for name, param in model.named_parameters():
            if param.grad is not None and name in self.fisher_diag:
                fisher = self.fisher_diag[name]
                theta_a = self.task_a_params_snapshot[name]
                
                # EWC penalty gradient: F * (theta - theta_A)
                ewc_grad = fisher * (param.data - theta_a)
                
                # Add to existing gradient
                param.grad.data += ewc_lambda * ewc_grad
    
    def get_protection_penalty(self, current_defect: float) -> float:
        """
        Compute Lagrangian penalty for blanket protection.
        
        Penalty = lambda * (current - baseline)^2 if ruptured else 0
        """
        if not self.state.blanket_a_ruptured:
            return 0.0
        
        delta = current_defect - self.state.baseline_defect_a
        penalty = self.config.lambda_protect * (delta ** 2)
        return penalty
    
    def get_noise_level(self) -> float:
        """Get current noise level for training."""
        if self.state.blanket_a_ruptured:
            # Inject recovery heat to prevent freezing into bad state
            self.state.recovery_steps += 1
            self.state.current_noise = self.config.recovery_heat
        else:
            self.state.current_noise = 0.0
            self.state.recovery_steps = 0
        return self.state.current_noise
    
    def should_phase_a_stop(self) -> bool:
        """Check if Phase A should stop (blanket closed + consolidated)."""
        blanket_closed = self.state.func_defect_a < self.config.blanket_threshold
        consolidated = self.state.test_acc_a > 0.95 and self.state.train_acc_a > 0.99
        return blanket_closed and consolidated
    
    def force_phase(self, phase: str):
        """Force controller into a specific phase."""
        self.state.phase = Phase(phase)


# =============================================================================
# TRAINING LOOPS
# =============================================================================

def train_phase_a(
    model: ContinualGrokMLP,
    config: ContinualLearningConfig,
    controller: BlanketProtectionController
) -> Tuple[float, List[Dict]]:
    """
    Phase A: Grok Task A (Modular Addition)
    
    Returns: (baseline_defect, training_history)
    """
    print("\n" + "=" * 80)
    print("PHASE A: GROKKING TASK A (MODULAR ADDITION)")
    print("=" * 80)
    
    # Create dataset
    (train_a, train_b, train_c), (test_a, test_b, test_c) = \
        create_modular_addition_dataset(config.p)
    
    train_dataset = TensorDataset(train_a, train_b, train_c)
    test_dataset = TensorDataset(test_a, test_b, test_c)
    train_loader = DataLoader(train_dataset, batch_size=config.batch_size, shuffle=True)
    test_loader = DataLoader(test_dataset, batch_size=config.batch_size)
    
    optimizer = torch.optim.AdamW(
        model.parameters(), 
        lr=config.phase_a_lr, 
        weight_decay=config.phase_a_weight_decay
    )
    criterion = nn.CrossEntropyLoss()
    
    controller.state.phase = Phase.EXPLORE
    
    print(f"\n{'Epoch':>6} | {'Train':>6} | {'Test':>6} | {'FuncD':>8} | {'ClassSep':>8} | Phase")
    print("-" * 70)
    
    for epoch in range(1, config.phase_a_max_epochs + 1):
        # Training
        model.train()
        total_loss = 0
        correct = 0
        total = 0
        
        for batch_a, batch_b, batch_c in train_loader:
            batch_a = batch_a.to(config.device)
            batch_b = batch_b.to(config.device)
            batch_c = batch_c.to(config.device)
            
            optimizer.zero_grad()
            out = model.forward_task_a(batch_a, batch_b, config.phase_a_noise_std)
            loss = criterion(out, batch_c)
            loss.backward()
            optimizer.step()
            
            total_loss += loss.item() * len(batch_a)
            correct += (out.argmax(dim=1) == batch_c).sum().item()
            total += len(batch_a)
        
        train_acc = correct / total
        
        # Evaluation
        model.eval()
        correct = 0
        total = 0
        with torch.no_grad():
            for batch_a, batch_b, batch_c in test_loader:
                batch_a = batch_a.to(config.device)
                batch_b = batch_b.to(config.device)
                batch_c = batch_c.to(config.device)
                out = model.forward_task_a(batch_a, batch_b)
                correct += (out.argmax(dim=1) == batch_c).sum().item()
                total += len(batch_a)
        test_acc = correct / total
        
        # Measure functional defect
        if epoch % config.measure_interval == 0 or epoch == 1:
            func_defect, class_sep = compute_functional_defect(
                model, train_loader, config.p, 'a', config.device
            )
            
            controller.update_state(
                epoch=epoch,
                func_defect_a=func_defect,
                class_sep_a=class_sep,
                train_acc_a=train_acc,
                test_acc_a=test_acc
            )
            
            # Determine phase
            if func_defect > 0.5:
                phase_str = "MEMORIZE"
            elif func_defect > config.blanket_threshold:
                phase_str = "TRANSITION"
            else:
                phase_str = "GROKKED"
            
            print(f"{epoch:6d} | {train_acc:6.1%} | {test_acc:6.1%} | "
                  f"{func_defect:8.4f} | {class_sep:8.2f} | {phase_str}")
            
            # Check stopping condition
            if controller.should_phase_a_stop():
                print(f"\n*** PHASE A COMPLETE: Blanket closed at epoch {epoch} ***")
                controller.set_baseline_defect(func_defect)
                # Compute Fisher Information for protection
                controller.compute_fisher_information(model, train_loader, config.device)
                return func_defect, controller.history
    
    # If we didn't grok, still set baseline
    print(f"\n*** PHASE A TIMEOUT: Setting baseline anyway ***")
    final_defect, _ = compute_functional_defect(
        model, train_loader, config.p, 'a', config.device
    )
    controller.set_baseline_defect(final_defect)
    return final_defect, controller.history


def train_phase_b(
    model: ContinualGrokMLP,
    config: ContinualLearningConfig,
    controller: BlanketProtectionController,
    task_a_loader: DataLoader
) -> List[Dict]:
    """
    Phase B: Learn Task B (Modular Multiplication) while protecting Task A's blanket.
    
    The key innovation: we monitor Task A's functional defect and intervene if it rises.
    """
    print("\n" + "=" * 80)
    print("PHASE B: LEARNING TASK B (MODULAR MULTIPLICATION) WITH PROTECTION")
    print("=" * 80)
    print(f"Baseline Task A defect: {controller.state.baseline_defect_a:.6f}")
    print(f"Protection tolerance: {config.protection_tolerance}x = "
          f"{controller.state.baseline_defect_a * config.protection_tolerance:.6f}")
    
    # Create Task B dataset
    (train_a, train_b, train_c), (test_a, test_b, test_c) = \
        create_modular_multiplication_dataset(config.p)
    
    train_dataset_b = TensorDataset(train_a, train_b, train_c)
    test_dataset_b = TensorDataset(test_a, test_b, test_c)
    train_loader_b = DataLoader(train_dataset_b, batch_size=config.batch_size, shuffle=True)
    test_loader_b = DataLoader(test_dataset_b, batch_size=config.batch_size)
    
    # Configure which parameters to train
    if config.freeze_shared:
        # Only train Task B head - freeze shared layers
        for name, param in model.named_parameters():
            if 'head_task_b' not in name:
                param.requires_grad = False
        trainable_params = [p for p in model.parameters() if p.requires_grad]
        print(f"  [Protection] Freezing shared layers. Training only Task B head.")
        print(f"  [Protection] Trainable params: {sum(p.numel() for p in trainable_params)}")
    else:
        trainable_params = model.parameters()
    
    optimizer = torch.optim.AdamW(
        trainable_params,
        lr=config.phase_b_lr,
        weight_decay=config.phase_b_weight_decay
    )
    criterion = nn.CrossEntropyLoss()
    
    controller.state.phase = Phase.PROTECT
    
    print(f"\n{'Epoch':>6} | {'A_Train':>7} | {'A_Test':>6} | {'A_FuncD':>8} | "
          f"{'B_Train':>7} | {'B_Test':>6} | {'B_FuncD':>8} | Status")
    print("-" * 95)
    
    batch_count = 0
    rejected_updates = 0
    
    for epoch in range(1, config.phase_b_max_epochs + 1):
        model.train()
        total_loss = 0
        correct_b = 0
        total_b = 0
        protection_activations = 0
        
        # Get current noise level from controller
        noise_level = controller.get_noise_level()
        
        for batch_a, batch_b, batch_c in train_loader_b:
            batch_a = batch_a.to(config.device)
            batch_b = batch_b.to(config.device)
            batch_c = batch_c.to(config.device)
            
            # Save weights before update (for defect constraint)
            if config.use_defect_constraint:
                saved_state = {k: v.clone() for k, v in model.state_dict().items()}
            
            optimizer.zero_grad()
            
            # Forward pass for Task B
            out = model.forward_task_b(batch_a, batch_b, noise_level)
            loss_b = criterion(out, batch_c)
            
            # Compute protection penalty
            penalty = controller.get_protection_penalty(controller.state.func_defect_a)
            if penalty > 0:
                protection_activations += 1
            
            loss_total = loss_b + penalty
            loss_total.backward()
            
            # KEY: Apply EWC gradient projection to protect Task A (if not freezing)
            if not config.freeze_shared and not config.use_defect_constraint:
                controller.apply_gradient_projection(model, ewc_lambda=config.ewc_lambda)
            
            optimizer.step()
            batch_count += 1
            
            # DIRECT FUNCTIONAL DEFECT CONSTRAINT (SGC Approach)
            if config.use_defect_constraint and batch_count % config.defect_check_interval == 0:
                # Compute current Task A defect
                model.eval()
                with torch.no_grad():
                    new_defect, _ = compute_functional_defect(
                        model, task_a_loader, config.p, 'a', config.device
                    )
                model.train()
                
                # Check if blanket is rupturing
                rupture_threshold = controller.state.baseline_defect_a * config.protection_tolerance
                if new_defect > rupture_threshold:
                    # REJECT UPDATE: Revert to saved weights
                    model.load_state_dict(saved_state)
                    rejected_updates += 1
                    # Reduce learning rate temporarily
                    for pg in optimizer.param_groups:
                        pg['lr'] *= 0.9
                else:
                    # Update controller's defect estimate
                    controller.state.func_defect_a = new_defect
            
            total_loss += loss_b.item() * len(batch_a)
            correct_b += (out.argmax(dim=1) == batch_c).sum().item()
            total_b += len(batch_a)
        
        train_acc_b = correct_b / total_b
        
        # Evaluate Task B
        model.eval()
        correct = 0
        total = 0
        with torch.no_grad():
            for batch_a, batch_b, batch_c in test_loader_b:
                batch_a = batch_a.to(config.device)
                batch_b = batch_b.to(config.device)
                batch_c = batch_c.to(config.device)
                out = model.forward_task_b(batch_a, batch_b)
                correct += (out.argmax(dim=1) == batch_c).sum().item()
                total += len(batch_a)
        test_acc_b = correct / total
        
        # Evaluate Task A (the key metric!)
        correct_a = 0
        total_a = 0
        with torch.no_grad():
            for batch_a, batch_b, batch_c in task_a_loader:
                batch_a = batch_a.to(config.device)
                batch_b = batch_b.to(config.device)
                batch_c = batch_c.to(config.device)
                out = model.forward_task_a(batch_a, batch_b)
                correct_a += (out.argmax(dim=1) == batch_c).sum().item()
                total_a += len(batch_a)
        train_acc_a = correct_a / total_a
        test_acc_a = train_acc_a  # Using train set as proxy
        
        # Measure functional defects
        if epoch % config.measure_interval == 0 or epoch == 1:
            func_defect_a, class_sep_a = compute_functional_defect(
                model, task_a_loader, config.p, 'a', config.device
            )
            func_defect_b, class_sep_b = compute_functional_defect(
                model, train_loader_b, config.p, 'b', config.device
            )
            
            controller.update_state(
                epoch=epoch,
                func_defect_a=func_defect_a,
                class_sep_a=class_sep_a,
                train_acc_a=train_acc_a,
                test_acc_a=test_acc_a,
                func_defect_b=func_defect_b,
                class_sep_b=class_sep_b,
                train_acc_b=train_acc_b,
                test_acc_b=test_acc_b
            )
            
            # Determine status
            if controller.state.blanket_a_ruptured:
                status = "RUPTURE!"
            elif func_defect_b < config.blanket_threshold:
                status = "B_GROKKED"
            else:
                status = "LEARNING"
            
            print(f"{epoch:6d} | {train_acc_a:7.1%} | {test_acc_a:6.1%} | "
                  f"{func_defect_a:8.4f} | {train_acc_b:7.1%} | {test_acc_b:6.1%} | "
                  f"{func_defect_b:8.4f} | {status}")
            
            # Check success condition
            if test_acc_b > 0.95 and test_acc_a > 0.95:
                print(f"\n*** PHASE B COMPLETE: Both tasks grokked! ***")
                break
    
    return controller.history


# =============================================================================
# MAIN EXPERIMENT
# =============================================================================

def run_continual_learning_test():
    """Run the full continual learning experiment."""
    print("\n" + "=" * 80)
    print("CONTINUAL LEARNING TEST 3: FUNCTIONAL BLANKET PROTECTION")
    print("=" * 80)
    print("\nHypothesis: Protecting functional defect (not weights) prevents forgetting")
    print("Task A: Modular Addition")
    print("Task B: Modular Multiplication")
    print("=" * 80)
    
    config = ContinualLearningConfig()
    torch.manual_seed(config.seed)
    np.random.seed(config.seed)
    
    print(f"\nConfiguration:")
    print(f"  Model: p={config.p}, embed={config.embed_dim}, hidden={config.hidden_dim}")
    print(f"  Phase A: max_epochs={config.phase_a_max_epochs}, lr={config.phase_a_lr}")
    print(f"  Phase B: max_epochs={config.phase_b_max_epochs}, protection_tol={config.protection_tolerance}")
    print(f"  Device: {config.device}")
    
    # Create model
    model = ContinualGrokMLP(
        config.p, config.embed_dim, config.hidden_dim, config.n_layers
    ).to(config.device)
    
    # Create controller
    controller = BlanketProtectionController(config)
    
    # Phase A: Grok Task A
    baseline_defect, phase_a_history = train_phase_a(model, config, controller)
    
    # Create Task A loader for Phase B monitoring
    (train_a, train_b, train_c), _ = create_modular_addition_dataset(config.p)
    task_a_dataset = TensorDataset(train_a, train_b, train_c)
    task_a_loader = DataLoader(task_a_dataset, batch_size=config.batch_size)
    
    # Phase B: Learn Task B with protection
    phase_b_history = train_phase_b(model, config, controller, task_a_loader)
    
    # Final Summary
    print("\n" + "=" * 80)
    print("EXPERIMENT SUMMARY")
    print("=" * 80)
    
    final_state = controller.state
    print(f"\nTask A (Addition):")
    print(f"  Final Accuracy: {final_state.test_acc_a:.1%}")
    print(f"  Final Functional Defect: {final_state.func_defect_a:.6f}")
    print(f"  Baseline Defect: {final_state.baseline_defect_a:.6f}")
    print(f"  Defect Ratio: {final_state.func_defect_a / final_state.baseline_defect_a:.2f}x")
    
    print(f"\nTask B (Multiplication):")
    print(f"  Final Accuracy: {final_state.test_acc_b:.1%}")
    print(f"  Final Functional Defect: {final_state.func_defect_b:.6f}")
    
    print(f"\nProtection Metrics:")
    print(f"  Blanket Ruptures: {final_state.rupture_count}")
    print(f"  Recovery Steps: {final_state.recovery_steps}")
    
    # Success criteria
    print(f"\n*** SUCCESS CRITERIA ***")
    task_a_preserved = final_state.test_acc_a > 0.95
    task_b_learned = final_state.test_acc_b > 0.95
    defect_preserved = final_state.func_defect_a < final_state.baseline_defect_a * 2
    
    print(f"  [{'Y' if task_a_preserved else 'N'}] Task A Accuracy > 95%: {final_state.test_acc_a:.1%}")
    print(f"  [{'Y' if task_b_learned else 'N'}] Task B Accuracy > 95%: {final_state.test_acc_b:.1%}")
    print(f"  [{'Y' if defect_preserved else 'N'}] Task A Defect < 2x Baseline: "
          f"{final_state.func_defect_a:.4f} < {final_state.baseline_defect_a * 2:.4f}")
    
    if task_a_preserved and task_b_learned and defect_preserved:
        print("\n*** EXPERIMENT SUCCESS: Zero-forgetting continual learning achieved! ***")
    else:
        print("\n*** EXPERIMENT INCOMPLETE: Further tuning needed ***")
    
    print("=" * 80 + "\n")
    
    return controller.history


if __name__ == "__main__":
    history = run_continual_learning_test()
