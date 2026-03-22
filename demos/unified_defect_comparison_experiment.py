"""
Unified Defect Comparison Experiment

The critical experiment to confirm the theory:
Compare (A) tail-energy defect, (B) layerwise closure defect ||Pi g(h) - Pi g(Pi h)||,
and (C) entropy/consolidation transition times against test accuracy jump.

Theory prediction:
- Closure defect should lead or coincide with grokking
- Tail defect may lag (it's a proxy, not the true blanket)
- Entropy/consolidation may lag (it's a consequence, not a cause)

A/B test:
- Discrete one-hot inputs (baseline)
- Dequantized/noisy float inputs (richer universe)

Author: SGC Research Team
Date: February 4, 2026
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
import torch.optim as optim
from torch.utils.data import DataLoader
import numpy as np
import math
import time
from dataclasses import dataclass, field
from typing import Dict, List, Tuple, Optional
from collections import deque

from analog_modular_arithmetic import (
    AnalogModularConfig,
    AnalogModularDataset, 
    AnalogGrokMLP,
    compute_layerwise_closure_defect,
    compute_tsallis_entropy_normalized,
)


@dataclass
class ExperimentConfig:
    """Configuration for comparison experiment."""
    # Model
    hidden_dim: int = 128
    num_layers: int = 2
    
    # Training
    epochs: int = 5000
    batch_size: int = 512
    lr: float = 1e-3
    weight_decay: float = 1.0
    
    # Modular arithmetic
    p: int = 97
    operation: str = 'add'
    train_fraction: float = 0.3
    
    # Analog settings (for A/B test)
    use_analog: bool = False
    input_noise_std: float = 0.1
    use_phase_encoding: bool = False
    use_soft_targets: bool = False
    target_concentration: float = 10.0
    
    # Logging
    log_interval: int = 100
    seed: int = 42


@dataclass
class DefectMetrics:
    """All defect metrics at a given epoch."""
    epoch: int
    
    # Accuracy (external validation)
    train_acc: float
    test_acc: float
    train_loss: float
    
    # Defect metrics
    tail_defect: float         # SVD tail energy ratio
    closure_defect: float      # ||Pi g(h) - Pi g(Pi h)|| / ||g(h)||
    
    # Entropy metrics (Tsallis q=1.5)
    S_q: float                 # Tsallis entropy
    consolidation: float       # 1 - S_q_normalized
    
    # Derived
    k_coarse: int              # Dimension of coarse subspace
    
    def to_dict(self) -> Dict:
        return {
            'epoch': self.epoch,
            'train_acc': self.train_acc,
            'test_acc': self.test_acc,
            'train_loss': self.train_loss,
            'tail_defect': self.tail_defect,
            'closure_defect': self.closure_defect,
            'S_q': self.S_q,
            'consolidation': self.consolidation,
            'k_coarse': self.k_coarse,
        }


def compute_tail_defect(hidden_states: torch.Tensor, k: Optional[int] = None) -> Tuple[float, int]:
    """
    Compute tail energy defect from hidden states.
    
    This measures whether the representation is low-dimensional,
    but NOT whether the dynamics are self-consistent.
    """
    with torch.no_grad():
        U, S, Vh = torch.linalg.svd(hidden_states, full_matrices=False)
        S2 = S ** 2
        total = S2.sum()
        
        if k is None:
            cumsum = torch.cumsum(S2, dim=0)
            k = (cumsum < 0.9 * total).sum().item() + 1
            k = max(1, min(k, len(S) - 1))
        
        tail_energy = S2[k:].sum()
        defect = math.sqrt((tail_energy / (total + 1e-10)).item())
        
        return defect, k


def compute_all_metrics(
    model: AnalogGrokMLP,
    train_loader: DataLoader,
    test_loader: DataLoader,
    device: str,
    epoch: int,
    q: float = 1.5
) -> DefectMetrics:
    """Compute all metrics for a given epoch."""
    model.eval()
    
    # Collect hidden states and outputs
    all_hidden = []
    all_logits = []
    train_correct = 0
    train_total = 0
    train_loss_sum = 0.0
    
    criterion = nn.CrossEntropyLoss()
    
    with torch.no_grad():
        for x, y in train_loader:
            x, y = x.to(device), y.to(device)
            
            # Handle soft targets
            if y.dim() > 1:
                y_hard = y.argmax(dim=-1)
            else:
                y_hard = y
            
            logits = model(x)
            h = model._hidden_activations
            
            all_hidden.append(h)
            all_logits.append(logits)
            
            loss = criterion(logits, y_hard)
            train_loss_sum += loss.item() * x.size(0)
            
            pred = logits.argmax(dim=-1)
            train_correct += (pred == y_hard).sum().item()
            train_total += x.size(0)
            
            if len(all_hidden) * x.size(0) > 1000:
                break
    
    # Concatenate
    H = torch.cat(all_hidden, dim=0)
    logits_all = torch.cat(all_logits, dim=0)
    
    # Train metrics
    train_acc = train_correct / train_total
    train_loss = train_loss_sum / train_total
    
    # Test accuracy
    test_correct = 0
    test_total = 0
    with torch.no_grad():
        for x, y in test_loader:
            x, y = x.to(device), y.to(device)
            if y.dim() > 1:
                y = y.argmax(dim=-1)
            logits = model(x)
            pred = logits.argmax(dim=-1)
            test_correct += (pred == y).sum().item()
            test_total += x.size(0)
    test_acc = test_correct / test_total
    
    # Tail defect
    tail_defect, k = compute_tail_defect(H)
    
    # Closure defect
    closure_result = compute_layerwise_closure_defect(model, H, k=k, return_components=True)
    closure_defect = closure_result['closure_defect']
    
    # Entropy (average over samples)
    probs = F.softmax(logits_all, dim=-1).mean(dim=0)  # Average distribution
    S_q = compute_tsallis_entropy_normalized(probs, q)
    consolidation = 1.0 - S_q
    
    return DefectMetrics(
        epoch=epoch,
        train_acc=train_acc,
        test_acc=test_acc,
        train_loss=train_loss,
        tail_defect=tail_defect,
        closure_defect=closure_defect,
        S_q=S_q,
        consolidation=consolidation,
        k_coarse=k,
    )


def find_transition_epoch(metrics_history: List[DefectMetrics], 
                          field: str, 
                          threshold: float,
                          direction: str = 'below') -> int:
    """Find first epoch where a metric crosses a threshold."""
    for m in metrics_history:
        val = getattr(m, field)
        if direction == 'below' and val < threshold:
            return m.epoch
        elif direction == 'above' and val > threshold:
            return m.epoch
    return -1


def run_experiment(config: ExperimentConfig) -> Tuple[List[DefectMetrics], Dict]:
    """Run a single experiment with given configuration."""
    
    torch.manual_seed(config.seed)
    np.random.seed(config.seed)
    
    device = 'cuda' if torch.cuda.is_available() else 'cpu'
    
    # Create dataset
    mod_config = AnalogModularConfig(
        p=config.p,
        operation=config.operation,
        input_noise_std=config.input_noise_std if config.use_analog else 0.0,
        use_phase_encoding=config.use_phase_encoding,
        phase_noise_std=0.05 if config.use_phase_encoding else 0.0,
        use_soft_targets=config.use_soft_targets,
        target_concentration=config.target_concentration,
        train_fraction=config.train_fraction,
        seed=config.seed,
    )
    
    train_dataset = AnalogModularDataset(mod_config, split='train')
    test_dataset = AnalogModularDataset(mod_config, split='test')
    
    train_loader = DataLoader(train_dataset, batch_size=config.batch_size, shuffle=True)
    test_loader = DataLoader(test_dataset, batch_size=config.batch_size, shuffle=False)
    
    # Determine input dimension
    x_sample, _ = train_dataset[0]
    input_dim = x_sample.shape[0]
    
    # Create model
    model = AnalogGrokMLP(
        input_dim=input_dim,
        hidden_dim=config.hidden_dim,
        output_dim=config.p,
        num_layers=config.num_layers
    ).to(device)
    
    optimizer = optim.AdamW(model.parameters(), lr=config.lr, weight_decay=config.weight_decay)
    
    # Loss function
    if config.use_soft_targets:
        criterion = nn.KLDivLoss(reduction='batchmean')
    else:
        criterion = nn.CrossEntropyLoss()
    
    # Training loop
    metrics_history = []
    grokking_epoch = -1
    
    print(f"\n{'='*80}")
    print(f"Experiment: {'ANALOG' if config.use_analog else 'DISCRETE'}")
    print(f"{'='*80}")
    print(f"\n{'Epoch':>6} | {'Train':>6} | {'Test':>6} | {'TailD':>7} | {'CloseD':>7} | {'Consol':>6} | {'k':>3}")
    print("-" * 65)
    
    for epoch in range(1, config.epochs + 1):
        # Train
        model.train()
        for x, y in train_loader:
            x, y = x.to(device), y.to(device)
            
            optimizer.zero_grad()
            logits = model(x)
            
            if config.use_soft_targets:
                log_probs = F.log_softmax(logits, dim=-1)
                loss = criterion(log_probs, y)
            else:
                loss = criterion(logits, y)
            
            loss.backward()
            optimizer.step()
        
        # Log metrics periodically
        if epoch % config.log_interval == 0 or epoch == 1:
            metrics = compute_all_metrics(model, train_loader, test_loader, device, epoch)
            metrics_history.append(metrics)
            
            # Check for grokking
            if grokking_epoch < 0 and metrics.test_acc > 0.95:
                grokking_epoch = epoch
                print(f"\n*** GROKKING at epoch {epoch}! ***\n")
            
            print(f"{epoch:6d} | {metrics.train_acc*100:5.1f}% | {metrics.test_acc*100:5.1f}% | "
                  f"{metrics.tail_defect:7.4f} | {metrics.closure_defect:7.4f} | "
                  f"{metrics.consolidation:6.3f} | {metrics.k_coarse:3d}")
        
        # Early stopping if grokked and stable
        if grokking_epoch > 0 and epoch > grokking_epoch + 500:
            print(f"\nEarly stopping: grokked at {grokking_epoch}, now at {epoch}")
            break
    
    # Find transition epochs
    tail_transition = find_transition_epoch(metrics_history, 'tail_defect', 0.15, 'below')
    closure_transition = find_transition_epoch(metrics_history, 'closure_defect', 0.15, 'below')
    consol_transition = find_transition_epoch(metrics_history, 'consolidation', 0.5, 'above')
    
    summary = {
        'grokking_epoch': grokking_epoch,
        'tail_defect_transition': tail_transition,
        'closure_defect_transition': closure_transition,
        'consolidation_transition': consol_transition,
        'final_test_acc': metrics_history[-1].test_acc if metrics_history else 0,
        'final_tail_defect': metrics_history[-1].tail_defect if metrics_history else 1,
        'final_closure_defect': metrics_history[-1].closure_defect if metrics_history else 1,
    }
    
    return metrics_history, summary


def run_ab_test():
    """Run A/B comparison: discrete vs analog inputs."""
    
    print("\n" + "=" * 80)
    print("A/B TEST: DISCRETE vs ANALOG INPUTS")
    print("=" * 80)
    
    # Discrete baseline
    config_discrete = ExperimentConfig(
        use_analog=False,
        epochs=3000,
        log_interval=100,
    )
    
    # Analog (noisy floats)
    config_analog = ExperimentConfig(
        use_analog=True,
        input_noise_std=0.1,
        epochs=3000,
        log_interval=100,
    )
    
    print("\n[A] DISCRETE INPUTS (baseline)")
    history_discrete, summary_discrete = run_experiment(config_discrete)
    
    print("\n[B] ANALOG INPUTS (noisy floats)")
    history_analog, summary_analog = run_experiment(config_analog)
    
    # Compare results
    print("\n" + "=" * 80)
    print("COMPARISON RESULTS")
    print("=" * 80)
    
    print("\n{:30} | {:>15} | {:>15}".format("Metric", "DISCRETE", "ANALOG"))
    print("-" * 65)
    
    for key in summary_discrete.keys():
        val_d = summary_discrete[key]
        val_a = summary_analog[key]
        if isinstance(val_d, float):
            print(f"{key:30} | {val_d:15.4f} | {val_a:15.4f}")
        else:
            print(f"{key:30} | {val_d:15} | {val_a:15}")
    
    # Analysis
    print("\n" + "=" * 80)
    print("ANALYSIS")
    print("=" * 80)
    
    grok_d = summary_discrete['grokking_epoch']
    grok_a = summary_analog['grokking_epoch']
    tail_d = summary_discrete['tail_defect_transition']
    tail_a = summary_analog['tail_defect_transition']
    close_d = summary_discrete['closure_defect_transition']
    close_a = summary_analog['closure_defect_transition']
    consol_d = summary_discrete['consolidation_transition']
    consol_a = summary_analog['consolidation_transition']
    
    print("\nDISCRETE:")
    if grok_d > 0:
        print(f"  Grokking at epoch {grok_d}")
        if tail_d > 0:
            print(f"  Tail defect transition at {tail_d} (lead: {grok_d - tail_d})")
        if close_d > 0:
            print(f"  Closure defect transition at {close_d} (lead: {grok_d - close_d})")
        if consol_d > 0:
            print(f"  Consolidation transition at {consol_d} (lead: {grok_d - consol_d})")
    else:
        print("  Did not grok")
    
    print("\nANALOG:")
    if grok_a > 0:
        print(f"  Grokking at epoch {grok_a}")
        if tail_a > 0:
            print(f"  Tail defect transition at {tail_a} (lead: {grok_a - tail_a})")
        if close_a > 0:
            print(f"  Closure defect transition at {close_a} (lead: {grok_a - close_a})")
        if consol_a > 0:
            print(f"  Consolidation transition at {consol_a} (lead: {grok_a - consol_a})")
    else:
        print("  Did not grok")
    
    print("\nTHEORY PREDICTION CHECK:")
    print("  - Closure defect should lead or coincide with grokking")
    print("  - Analog inputs should show smoother crystallization window")
    
    return summary_discrete, summary_analog


if __name__ == "__main__":
    run_ab_test()
