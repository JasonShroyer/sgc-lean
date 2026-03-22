"""
SGC Phase-6.2: Entropy-Extropy Dual Controller for Grokking

This experiment tests whether state-driven control using the entropy-extropy
Bregman dual outperforms fixed schedules.

KEY HYPOTHESIS:
- Entropy H(p) measures uncertainty -> drives exploration
- Extropy J(p) / consolidation_index measures certainty -> drives consolidation  
- The dual (H, J, defect) provides better control than fixed schedules

CONTROL RULES:
1. EXPLORE: High H + high dH/dt -> boost noise
2. CONSOLIDATE: High certainty + falling defect -> ramp WD
3. RECOVER: High certainty + stable defect -> spurious certainty -> re-explore

Author: SGC Research Team
Date: February 2026
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
import torch.optim as optim
from torch.utils.data import DataLoader, Dataset
import numpy as np
import math
import argparse
import csv
from dataclasses import dataclass, field
from typing import Tuple, List, Dict, Optional
from collections import deque

# Import the dual controller
from entropy_extropy_controller import (
    DualVitalSigns, DualController,
    compute_entropy, compute_extropy, compute_normalized_entropy,
    compute_kl_velocity, compute_l2_velocity
)


# ═══════════════════════════════════════════════════════════════════════════════
# DATASET AND MODEL (same as Phase-6.1)
# ═══════════════════════════════════════════════════════════════════════════════

class ModularAdditionDataset(Dataset):
    def __init__(self, p: int = 97, train: bool = True, train_fraction: float = 0.3, seed: int = 42):
        self.p = p
        np.random.seed(seed)
        all_pairs = [(i, j) for i in range(p) for j in range(p)]
        np.random.shuffle(all_pairs)
        split = int(len(all_pairs) * train_fraction)
        self.pairs = all_pairs[:split] if train else all_pairs[split:]
        
    def __len__(self):
        return len(self.pairs)
    
    def __getitem__(self, idx):
        a, b = self.pairs[idx]
        x = torch.tensor([a, b], dtype=torch.long)
        y = torch.tensor((a + b) % self.p, dtype=torch.long)
        return x, y


class GrokMLP(nn.Module):
    def __init__(self, p: int = 97, hidden_dim: int = 128):
        super().__init__()
        self.p = p
        self.embed = nn.Embedding(p, hidden_dim)
        self.fc1 = nn.Linear(2 * hidden_dim, hidden_dim)
        self.fc2 = nn.Linear(hidden_dim, hidden_dim)
        self.fc3 = nn.Linear(hidden_dim, p)
        
    def forward(self, x):
        e = self.embed(x)
        e = e.view(e.size(0), -1)
        h = F.relu(self.fc1(e))
        h = F.relu(self.fc2(h))
        return self.fc3(h)
    
    def get_hidden(self, x):
        e = self.embed(x)
        e = e.view(e.size(0), -1)
        h = F.relu(self.fc1(e))
        return F.relu(self.fc2(h))


# ═══════════════════════════════════════════════════════════════════════════════
# DEFECT MEASUREMENT
# ═══════════════════════════════════════════════════════════════════════════════

def compute_hidden_defect(model: GrokMLP, dataloader: DataLoader, device: str) -> float:
    """Compute lumpability defect from hidden layer spectrum."""
    model.eval()
    all_hidden = []
    
    with torch.no_grad():
        for x, _ in dataloader:
            x = x.to(device)
            h = model.get_hidden(x)
            all_hidden.append(h)
            if len(all_hidden) * x.size(0) > 500:
                break
    
    if not all_hidden:
        return 1.0
    
    H = torch.cat(all_hidden, dim=0)
    
    # SVD-based defect: ratio of tail energy to total
    try:
        _, S, _ = torch.linalg.svd(H, full_matrices=False)
        S = S / (S.sum() + 1e-10)
        n = len(S)
        tail_start = n // 2
        tail_energy = S[tail_start:].sum().item()
        return tail_energy
    except:
        return 1.0


# ═══════════════════════════════════════════════════════════════════════════════
# PHASE-6.2 DUAL CONTROLLER WRAPPER
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class Phase62Controller:
    """
    Phase-6.2: Dual-controlled grokking using entropy-extropy.
    
    This wraps the DualController and DualVitalSigns for the grokking task.
    """
    
    # Target exploration mass
    delta: float = 0.1
    initial_distance: float = 1.0
    M_explore: float = field(init=False)
    
    # Noise injection
    noise_scale_base: float = 0.1
    tail_fraction: float = 0.5
    
    # Tracking
    M_nominal: float = 0.0
    injection_count: int = 0
    
    # Components
    vitals: DualVitalSigns = field(default_factory=DualVitalSigns)
    dual_ctrl: DualController = field(default_factory=DualController)
    
    # Phase tracking
    current_phase: str = 'heat'
    phase_history: List[Tuple[int, str]] = field(default_factory=list)
    
    # History for logging
    entropy_log: List[Tuple[int, float]] = field(default_factory=list)
    extropy_log: List[Tuple[int, float]] = field(default_factory=list)
    consolidation_log: List[Tuple[int, float]] = field(default_factory=list)
    
    def __post_init__(self):
        self.M_explore = math.log(self.initial_distance / self.delta)
        print(f"[Phase62Controller] Dual-Controlled Grokking")
        print(f"    M_explore = {self.M_explore:.4f}")
        print(f"    Control: entropy-extropy driven")
    
    def update(self, probs: torch.Tensor, defect: float, epoch: int) -> Tuple[float, float, str]:
        """
        Update controller with new observations.
        
        Args:
            probs: Output probability distribution [batch, classes]
            defect: Current lumpability defect
            epoch: Current epoch
        
        Returns:
            (noise_scale, weight_decay, phase_name)
        """
        # Update vital signs
        self.vitals.update(probs, defect, epoch)
        
        # Get control outputs
        noise, wd, phase = self.dual_ctrl.update(
            self.vitals, 
            self.M_nominal, 
            self.M_explore
        )
        
        # Track phase changes
        if phase != self.current_phase:
            self.phase_history.append((epoch, phase))
            print(f"\n*** PHASE CHANGE at epoch {epoch}: {self.current_phase} -> {phase} ***")
            print(f"    entropy_norm = {self.vitals.entropy_normalized:.3f}")
            print(f"    consolidation = {self.vitals.consolidation_index:.3f}")
            print(f"    defect = {defect:.4f}")
            print(f"    spurious_certainty = {self.vitals.spurious_certainty}")
            self.current_phase = phase
        
        # Log for analysis
        self.entropy_log.append((epoch, self.vitals.entropy))
        self.extropy_log.append((epoch, self.vitals.extropy))
        self.consolidation_log.append((epoch, self.vitals.consolidation_index))
        
        return noise, wd, phase
    
    def inject_noise(self, model: GrokMLP, device: str, noise_scale: float):
        """Inject noise and update mass tracking."""
        with torch.no_grad():
            for param in model.parameters():
                if param.dim() >= 2:
                    noise = torch.randn_like(param) * noise_scale
                    param.add_(noise)
        
        self.M_nominal += noise_scale
        self.injection_count += 1
    
    def get_summary(self) -> Dict:
        """Get summary for logging."""
        return {
            'M_nominal': self.M_nominal,
            'injection_count': self.injection_count,
            'entropy_final': self.vitals.entropy,
            'extropy_final': self.vitals.extropy,
            'consolidation_final': self.vitals.consolidation_index,
            'phase_changes': len(self.phase_history),
            'explore_count': self.dual_ctrl.exploration_count,
            'consolidate_count': self.dual_ctrl.consolidation_count,
            'recovery_count': self.dual_ctrl.recovery_count,
        }


# ═══════════════════════════════════════════════════════════════════════════════
# TRAINING LOOP
# ═══════════════════════════════════════════════════════════════════════════════

def train_phase62(
    model: GrokMLP,
    train_loader: DataLoader,
    test_loader: DataLoader,
    device: str,
    epochs: int = 8000,
    lr: float = 0.001,
    controller: Optional[Phase62Controller] = None,
    log_interval: int = 100,
    grokking_threshold: float = 0.95,
) -> Tuple[Dict, List[Dict]]:
    """Train with dual-controlled heat/consolidation."""
    
    if controller is None:
        controller = Phase62Controller()
    
    criterion = nn.CrossEntropyLoss()
    optimizer = optim.AdamW(model.parameters(), lr=lr, weight_decay=0.1)
    
    history = []
    grokking_epoch = -1
    
    print(f"\nTraining for {epochs} epochs with DUAL CONTROLLER...")
    print("-" * 70)
    
    for epoch in range(1, epochs + 1):
        # Training step
        model.train()
        total_loss = 0
        correct = 0
        total = 0
        
        for x, y in train_loader:
            x, y = x.to(device), y.to(device)
            optimizer.zero_grad()
            logits = model(x)
            loss = criterion(logits, y)
            loss.backward()
            optimizer.step()
            
            total_loss += loss.item()
            correct += (logits.argmax(dim=1) == y).sum().item()
            total += y.size(0)
        
        train_loss = total_loss / len(train_loader)
        train_acc = correct / total
        
        # Evaluation
        model.eval()
        test_correct = 0
        test_total = 0
        all_probs = []
        
        with torch.no_grad():
            for x, y in test_loader:
                x, y = x.to(device), y.to(device)
                logits = model(x)
                probs = F.softmax(logits, dim=-1)
                all_probs.append(probs)
                test_correct += (logits.argmax(dim=1) == y).sum().item()
                test_total += y.size(0)
        
        test_acc = test_correct / test_total
        all_probs = torch.cat(all_probs, dim=0)
        
        # Compute defect
        defect = compute_hidden_defect(model, train_loader, device)
        
        # Update controller with current state
        noise_scale, wd, phase = controller.update(all_probs, defect, epoch)
        
        # Update optimizer weight decay
        for param_group in optimizer.param_groups:
            param_group['weight_decay'] = wd
        
        # Inject noise based on controller output
        if phase in ['heat', 'explore', 'recovery']:
            controller.inject_noise(model, device, noise_scale)
        
        # Logging
        if epoch % log_interval == 0 or epoch == 1:
            print(f"Epoch {epoch:5d}: loss={train_loss:.4f}, train={train_acc*100:.1f}%, "
                  f"test={test_acc*100:.1f}% | H={controller.vitals.entropy_normalized:.2f}, "
                  f"C={controller.vitals.consolidation_index:.2f}, "
                  f"d={defect:.3f} | {phase}")
            
            history.append({
                'epoch': epoch,
                'train_loss': train_loss,
                'train_acc': train_acc,
                'test_acc': test_acc,
                'entropy': controller.vitals.entropy,
                'extropy': controller.vitals.extropy,
                'entropy_normalized': controller.vitals.entropy_normalized,
                'consolidation_index': controller.vitals.consolidation_index,
                'kl_velocity': controller.vitals.kl_velocity,
                'l2_velocity': controller.vitals.l2_velocity,
                'defect': defect,
                'noise_scale': noise_scale,
                'weight_decay': wd,
                'phase': phase,
                'M_nominal': controller.M_nominal,
                'spurious_certainty': controller.vitals.spurious_certainty,
            })
        
        # Check for grokking
        if test_acc >= grokking_threshold and grokking_epoch < 0:
            grokking_epoch = epoch
            print(f"\n*** GROKKING ACHIEVED at epoch {epoch}! ***")
            print(f"    Phase: {phase}")
            print(f"    M_nominal: {controller.M_nominal:.2f}")
            print(f"    Consolidation index: {controller.vitals.consolidation_index:.3f}")
    
    summary = controller.get_summary()
    summary['grokking_epoch'] = grokking_epoch
    summary['final_test_acc'] = test_acc
    
    return summary, history


# ═══════════════════════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════════════════════

def main():
    parser = argparse.ArgumentParser(description='Phase-6.2: Dual-Controlled Grokking')
    parser.add_argument('--epochs', type=int, default=8000)
    parser.add_argument('--p', type=int, default=97)
    parser.add_argument('--hidden_dim', type=int, default=128)
    parser.add_argument('--lr', type=float, default=0.001)
    parser.add_argument('--batch_size', type=int, default=32)
    parser.add_argument('--seed', type=int, default=42)
    parser.add_argument('--log_interval', type=int, default=100)
    
    args = parser.parse_args()
    
    # Setup
    torch.manual_seed(args.seed)
    np.random.seed(args.seed)
    device = 'cuda' if torch.cuda.is_available() else 'cpu'
    
    print("=" * 70)
    print("SGC PHASE-6.2: ENTROPY-EXTROPY DUAL CONTROLLER")
    print("State-driven control replaces fixed schedules")
    print("=" * 70)
    
    if torch.cuda.is_available():
        print(f"GPU: {torch.cuda.get_device_name(0)}")
    
    # Create datasets
    train_dataset = ModularAdditionDataset(args.p, train=True, seed=args.seed)
    test_dataset = ModularAdditionDataset(args.p, train=False, seed=args.seed)
    
    train_loader = DataLoader(train_dataset, batch_size=args.batch_size, shuffle=True)
    test_loader = DataLoader(test_dataset, batch_size=args.batch_size, shuffle=False)
    
    print(f"\nDataset: {len(train_dataset)} train, {len(test_dataset)} test")
    
    # Create model
    model = GrokMLP(p=args.p, hidden_dim=args.hidden_dim).to(device)
    print(f"Model parameters: {sum(p.numel() for p in model.parameters()):,}")
    
    # Create controller
    controller = Phase62Controller()
    
    # Train
    summary, history = train_phase62(
        model, train_loader, test_loader, device,
        epochs=args.epochs,
        lr=args.lr,
        controller=controller,
        log_interval=args.log_interval,
    )
    
    # Report
    print("\n" + "=" * 70)
    print("PHASE-6.2 RESULTS")
    print("=" * 70)
    print(f"Grokking epoch: {summary['grokking_epoch']}")
    print(f"Final test accuracy: {summary['final_test_acc']*100:.1f}%")
    print(f"Total noise injections: {summary['injection_count']}")
    print(f"Final M_nominal: {summary['M_nominal']:.2f}")
    print(f"\nController activity:")
    print(f"  Exploration phases: {summary['explore_count']}")
    print(f"  Consolidation phases: {summary['consolidate_count']}")
    print(f"  Recovery phases: {summary['recovery_count']}")
    print(f"  Phase changes: {summary['phase_changes']}")
    
    # Save history
    csv_file = f"phase62_dual_{args.seed}.csv"
    with open(csv_file, 'w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=history[0].keys())
        writer.writeheader()
        writer.writerows(history)
    print(f"\nHistory saved to {csv_file}")


if __name__ == "__main__":
    main()
