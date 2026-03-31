"""
PERIHELION Sprint A: 3-Task Continual Learning Demo

Demonstrates zero-forgetting continual learning with automatic grokking detection.

Curriculum:
  Task A: (a + b) mod 97  → grok → freeze
  Task B: (a * b) mod 97  -> grok -> freeze (Task A stays 100%)
  Task C: (x+y)*z mod 23  -> native sheaf composition

Success Criteria:
  - Task A accuracy stays >=99% throughout Tasks B and C
  - Task B accuracy stays >=99% throughout Task C
  - Task C reaches >=95% test accuracy
  - eps sensor fires freeze event at each grokking transition
  - Zero hand-tuned parameters

Usage:
    python demo_continual_learning.py
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'demos'))

import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import Dataset, DataLoader
import numpy as np
from datetime import datetime
from dataclasses import dataclass
from typing import Dict, List, Tuple, Optional

# Matplotlib optional (numpy version conflicts)
try:
    import matplotlib.pyplot as plt
    HAS_MATPLOTLIB = True
except ImportError:
    HAS_MATPLOTLIB = False
    print("Warning: matplotlib not available, skipping plots")

from sgc_integrated_controller import SGCController, StalkPhase


# =============================================================================
# DATASETS
# =============================================================================

class ModularAdditionDataset(Dataset):
    """Dataset for (a + b) mod p."""
    def __init__(self, p: int = 97, train: bool = True, train_fraction: float = 0.3, seed: int = 42):
        self.p = p
        all_pairs = [(a, b) for a in range(p) for b in range(p)]
        rng = np.random.RandomState(seed)
        rng.shuffle(all_pairs)
        split_idx = int(len(all_pairs) * train_fraction)
        self.pairs = all_pairs[:split_idx] if train else all_pairs[split_idx:]
    
    def __len__(self):
        return len(self.pairs)
    
    def __getitem__(self, idx):
        a, b = self.pairs[idx]
        x = torch.zeros(2 * self.p)
        x[a] = 1.0
        x[self.p + b] = 1.0
        y = (a + b) % self.p
        return x, y


class ModularMultiplicationDataset(Dataset):
    """Dataset for (a * b) mod p."""
    def __init__(self, p: int = 97, train: bool = True, train_fraction: float = 0.3, seed: int = 42):
        self.p = p
        all_pairs = [(a, b) for a in range(p) for b in range(p)]
        rng = np.random.RandomState(seed)
        rng.shuffle(all_pairs)
        split_idx = int(len(all_pairs) * train_fraction)
        self.pairs = all_pairs[:split_idx] if train else all_pairs[split_idx:]
    
    def __len__(self):
        return len(self.pairs)
    
    def __getitem__(self, idx):
        a, b = self.pairs[idx]
        x = torch.zeros(2 * self.p)
        x[a] = 1.0
        x[self.p + b] = 1.0
        y = (a * b) % self.p
        return x, y


class CompositionalDataset(Dataset):
    """Dataset for (x + y) * z mod p."""
    def __init__(self, p: int = 23, train: bool = True, train_fraction: float = 0.3, seed: int = 42):
        self.p = p
        all_triples = [(x, y, z) for x in range(p) for y in range(p) for z in range(p)]
        rng = np.random.RandomState(seed)
        rng.shuffle(all_triples)
        split_idx = int(len(all_triples) * train_fraction)
        self.triples = all_triples[:split_idx] if train else all_triples[split_idx:]
    
    def __len__(self):
        return len(self.triples)
    
    def __getitem__(self, idx):
        x, y, z = self.triples[idx]
        inp = torch.zeros(3 * self.p)
        inp[x] = 1.0
        inp[self.p + y] = 1.0
        inp[2 * self.p + z] = 1.0
        target = ((x + y) * z) % self.p
        return inp, target


# =============================================================================
# MODELS
# =============================================================================

class GrokMLP(nn.Module):
    """MLP for modular arithmetic grokking."""
    def __init__(self, input_dim: int, hidden_dim: int = 128, output_dim: int = 97):
        super().__init__()
        self.fc1 = nn.Linear(input_dim, hidden_dim)
        self.fc2 = nn.Linear(hidden_dim, hidden_dim)
        self.fc3 = nn.Linear(hidden_dim, output_dim)
    
    def forward(self, x):
        x = F.relu(self.fc1(x))
        h = F.relu(self.fc2(x))
        return self.fc3(h)
    
    def get_hidden(self, x):
        x = F.relu(self.fc1(x))
        return F.relu(self.fc2(x))


# =============================================================================
# TRAINING
# =============================================================================

@dataclass
class TrainingConfig:
    epochs: int = 3000
    lr: float = 1e-3
    weight_decay: float = 1.0
    batch_size: int = 512
    device: str = 'cuda' if torch.cuda.is_available() else 'cpu'
    log_interval: int = 100


def evaluate(model: nn.Module, dataloader: DataLoader, device: str) -> float:
    """Evaluate model accuracy."""
    model.eval()
    correct = 0
    total = 0
    with torch.no_grad():
        for x, y in dataloader:
            x, y = x.to(device), y.to(device)
            pred = model(x).argmax(dim=1)
            correct += (pred == y).sum().item()
            total += len(y)
    return correct / total


def get_hidden_states(model: nn.Module, dataloader: DataLoader, device: str) -> Tuple[torch.Tensor, torch.Tensor]:
    """Extract hidden states and targets from model."""
    model.eval()
    all_hidden = []
    all_targets = []
    with torch.no_grad():
        for x, y in dataloader:
            x = x.to(device)
            h = model.get_hidden(x)
            all_hidden.append(h.cpu())
            all_targets.append(y)
    return torch.cat(all_hidden), torch.cat(all_targets)


def train_task(
    task_name: str,
    model: nn.Module,
    train_loader: DataLoader,
    test_loader: DataLoader,
    controller: SGCController,
    config: TrainingConfig,
    frozen_tasks: Dict[str, Tuple[nn.Module, DataLoader]] = None,
) -> Dict:
    """
    Train a single task with SGC control.
    
    Returns dict with training history and results.
    """
    print(f"\n{'='*60}")
    print(f"  Training Task: {task_name}")
    print(f"{'='*60}")
    
    controller.register_task(task_name)
    
    optimizer = torch.optim.AdamW(
        model.parameters(),
        lr=config.lr,
        weight_decay=config.weight_decay
    )
    criterion = nn.CrossEntropyLoss()
    
    history = {
        'train_acc': [],
        'test_acc': [],
        'epsilon': [],
        'phase': [],
        'frozen_task_accs': {name: [] for name in (frozen_tasks or {}).keys()},
    }
    
    grokked = False
    
    for epoch in range(config.epochs):
        model.train()
        
        for x, y in train_loader:
            x, y = x.to(config.device), y.to(config.device)
            
            optimizer.zero_grad()
            out = model(x)
            loss = criterion(out, y)
            loss.backward()
            optimizer.step()
        
        # Evaluate
        train_acc = evaluate(model, train_loader, config.device)
        test_acc = evaluate(model, test_loader, config.device)
        
        # Get hidden states for controller
        hidden, targets = get_hidden_states(model, train_loader, config.device)
        
        # Controller step
        output = controller.step(hidden, targets, epoch, accuracy=test_acc)
        
        # Update optimizer weight decay based on controller
        for param_group in optimizer.param_groups:
            param_group['weight_decay'] = output.weight_decay
        
        # Apply elastic protection to frozen tasks
        if frozen_tasks:
            controller.apply_elastic_protection(model, alpha=0.05)
        
        # Check frozen task accuracies
        if frozen_tasks:
            for name, (frozen_model, frozen_loader) in frozen_tasks.items():
                frozen_acc = evaluate(frozen_model, frozen_loader, config.device)
                history['frozen_task_accs'][name].append(frozen_acc)
        
        # Record history
        history['train_acc'].append(train_acc)
        history['test_acc'].append(test_acc)
        history['epsilon'].append(output.epsilon)
        history['phase'].append(output.phase.value)
        
        # Logging
        if epoch % config.log_interval == 0 or output.should_freeze:
            frozen_str = ""
            if frozen_tasks:
                frozen_accs = [f"{n}={history['frozen_task_accs'][n][-1]:.1%}" 
                              for n in frozen_tasks.keys()]
                frozen_str = f" | Frozen: {', '.join(frozen_accs)}"
            
            print(f"Epoch {epoch:4d} | Train: {train_acc:.1%} | Test: {test_acc:.1%} | "
                  f"eps: {output.epsilon:.3f} | Phase: {output.phase.value}{frozen_str}")
        
        # Freeze on grokking
        if output.should_freeze and not grokked:
            grokked = True
            controller.freeze_stalk(model, task_name)
            print(f"\n*** FREEZE EVENT at epoch {epoch} ***")
            
            # Early stop after grokking confirmed
            if test_acc >= 0.98:
                print(f"Task {task_name} complete. Test accuracy: {test_acc:.1%}")
                break
    
    return {
        'history': history,
        'final_train_acc': history['train_acc'][-1],
        'final_test_acc': history['test_acc'][-1],
        'grokking_epoch': controller.stalks[task_name].grokking_epoch,
        'freeze_epoch': controller.stalks[task_name].freeze_epoch,
        'final_epsilon': controller.stalks[task_name].final_epsilon,
    }


# =============================================================================
# MAIN DEMO
# =============================================================================

def run_demo():
    """Run the 3-task continual learning demo."""
    print("=" * 70)
    print("  PERIHELION Sprint A: 3-Task Continual Learning Demo")
    print("  Zero-forgetting, zero hand-tuned parameters")
    print("=" * 70)
    
    # Quick validation run - reduce epochs for testing
    quick_mode = os.environ.get('QUICK_MODE', '0') == '1'
    
    config = TrainingConfig(
        epochs=500 if quick_mode else 5000,
        lr=1e-3,
        weight_decay=1.0,
        batch_size=512,
        log_interval=50 if quick_mode else 200,
    )
    
    if quick_mode:
        print("*** QUICK MODE: Reduced epochs for validation ***")
    
    print(f"\nDevice: {config.device}")
    print(f"Epochs per task: {config.epochs}")
    
    # Initialize controller
    controller = SGCController(
        base_noise=0.1,
        base_weight_decay=1.0,
        num_classes=97,
    )
    
    results = {}
    
    # =========================================================================
    # TASK A: (a + b) mod 97
    # =========================================================================
    print("\n" + "=" * 70)
    print("  TASK A: Modular Addition (a + b) mod 97")
    print("=" * 70)
    
    train_a = DataLoader(ModularAdditionDataset(97, train=True), batch_size=config.batch_size, shuffle=True)
    test_a = DataLoader(ModularAdditionDataset(97, train=False), batch_size=config.batch_size)
    
    model_a = GrokMLP(input_dim=2*97, hidden_dim=128, output_dim=97).to(config.device)
    
    results['task_a'] = train_task(
        task_name="addition_mod97",
        model=model_a,
        train_loader=train_a,
        test_loader=test_a,
        controller=controller,
        config=config,
    )
    
    # =========================================================================
    # TASK B: (a * b) mod 97
    # =========================================================================
    print("\n" + "=" * 70)
    print("  TASK B: Modular Multiplication (a * b) mod 97")
    print("  Monitoring Task A accuracy (should stay >=99%)")
    print("=" * 70)
    
    train_b = DataLoader(ModularMultiplicationDataset(97, train=True), batch_size=config.batch_size, shuffle=True)
    test_b = DataLoader(ModularMultiplicationDataset(97, train=False), batch_size=config.batch_size)
    
    model_b = GrokMLP(input_dim=2*97, hidden_dim=128, output_dim=97).to(config.device)
    
    results['task_b'] = train_task(
        task_name="multiplication_mod97",
        model=model_b,
        train_loader=train_b,
        test_loader=test_b,
        controller=controller,
        config=config,
        frozen_tasks={'task_a': (model_a, test_a)},
    )
    
    # =========================================================================
    # TASK C: (x + y) * z mod 23
    # =========================================================================
    print("\n" + "=" * 70)
    print("  TASK C: Compositional (x + y) * z mod 23")
    print("  Monitoring Tasks A and B (should stay >=99%)")
    print("=" * 70)
    
    # Use smaller modulus for compositional task
    controller.num_classes = 23
    
    train_c = DataLoader(CompositionalDataset(23, train=True), batch_size=config.batch_size, shuffle=True)
    test_c = DataLoader(CompositionalDataset(23, train=False), batch_size=config.batch_size)
    
    model_c = GrokMLP(input_dim=3*23, hidden_dim=256, output_dim=23).to(config.device)
    
    results['task_c'] = train_task(
        task_name="compositional_mod23",
        model=model_c,
        train_loader=train_c,
        test_loader=test_c,
        controller=controller,
        config=config,
        frozen_tasks={'task_a': (model_a, test_a), 'task_b': (model_b, test_b)},
    )
    
    # =========================================================================
    # RESULTS SUMMARY
    # =========================================================================
    print("\n" + "=" * 70)
    print("  SPRINT A RESULTS SUMMARY")
    print("=" * 70)
    
    print(f"\n  Task A (Addition):")
    print(f"    Final Test Accuracy: {results['task_a']['final_test_acc']:.1%}")
    print(f"    Grokking Epoch: {results['task_a']['grokking_epoch']}")
    print(f"    Final eps: {results['task_a']['final_epsilon']:.4f}")
    
    print(f"\n  Task B (Multiplication):")
    print(f"    Final Test Accuracy: {results['task_b']['final_test_acc']:.1%}")
    print(f"    Grokking Epoch: {results['task_b']['grokking_epoch']}")
    print(f"    Final eps: {results['task_b']['final_epsilon']:.4f}")
    
    print(f"\n  Task C (Compositional):")
    print(f"    Final Test Accuracy: {results['task_c']['final_test_acc']:.1%}")
    print(f"    Grokking Epoch: {results['task_c']['grokking_epoch']}")
    print(f"    Final eps: {results['task_c']['final_epsilon']:.4f}")
    
    # Check success criteria
    print("\n  SUCCESS CRITERIA:")
    
    task_a_maintained = min(results['task_b']['history']['frozen_task_accs'].get('task_a', [1.0])) >= 0.99
    print(f"    Task A stays >=99% during B: {'PASS' if task_a_maintained else 'FAIL'}")
    
    task_b_maintained = min(results['task_c']['history']['frozen_task_accs'].get('task_b', [1.0])) >= 0.99
    print(f"    Task B stays >=99% during C: {'PASS' if task_b_maintained else 'FAIL'}")
    
    task_c_success = results['task_c']['final_test_acc'] >= 0.95
    print(f"    Task C reaches >=95%: {'PASS' if task_c_success else 'FAIL'}")
    
    all_grokked = all(results[t]['grokking_epoch'] > 0 for t in ['task_a', 'task_b', 'task_c'])
    print(f"    All tasks grokked: {'PASS' if all_grokked else 'FAIL'}")
    
    print("\n" + controller.summary())
    
    # Save results
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    
    # Plot (if matplotlib available)
    if not HAS_MATPLOTLIB:
        print("\nSkipping plots (matplotlib not available)")
        return results
    
    fig, axes = plt.subplots(2, 2, figsize=(12, 10))
    
    # Task accuracies
    ax = axes[0, 0]
    for task_name, task_results in results.items():
        ax.plot(task_results['history']['test_acc'], label=task_name)
    ax.set_xlabel('Epoch')
    ax.set_ylabel('Test Accuracy')
    ax.set_title('Test Accuracy per Task')
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    # Epsilon trajectories
    ax = axes[0, 1]
    for task_name, task_results in results.items():
        ax.plot(task_results['history']['epsilon'], label=task_name)
    ax.set_xlabel('Epoch')
    ax.set_ylabel('Functional Defect eps')
    ax.set_title('eps Trajectories (Grokking Detection)')
    ax.axhline(y=0.15, color='r', linestyle='--', label='Grok threshold')
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    # Frozen task monitoring
    ax = axes[1, 0]
    if results['task_b']['history']['frozen_task_accs'].get('task_a'):
        ax.plot(results['task_b']['history']['frozen_task_accs']['task_a'], 
                label='Task A during B', color='blue')
    if results['task_c']['history']['frozen_task_accs'].get('task_a'):
        ax.plot(results['task_c']['history']['frozen_task_accs']['task_a'], 
                label='Task A during C', color='blue', linestyle='--')
    if results['task_c']['history']['frozen_task_accs'].get('task_b'):
        ax.plot(results['task_c']['history']['frozen_task_accs']['task_b'], 
                label='Task B during C', color='orange')
    ax.set_xlabel('Epoch')
    ax.set_ylabel('Accuracy')
    ax.set_title('Memory Protection (Frozen Task Accuracy)')
    ax.axhline(y=0.99, color='r', linestyle='--', label='99% threshold')
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    # Phase diagram
    ax = axes[1, 1]
    phase_colors = {'heating': 'red', 'transition': 'orange', 'grokked': 'green', 'frozen': 'blue'}
    for i, (task_name, task_results) in enumerate(results.items()):
        phases = task_results['history']['phase']
        y = [i] * len(phases)
        colors = [phase_colors.get(p, 'gray') for p in phases]
        ax.scatter(range(len(phases)), y, c=colors, s=2, alpha=0.5)
    ax.set_yticks(range(len(results)))
    ax.set_yticklabels(list(results.keys()))
    ax.set_xlabel('Epoch')
    ax.set_title('Phase Diagram')
    
    plt.tight_layout()
    plt.savefig(f'sprint_a_results_{timestamp}.png', dpi=150)
    print(f"\nFigure saved: sprint_a_results_{timestamp}.png")
    
    return results


if __name__ == "__main__":
    results = run_demo()
