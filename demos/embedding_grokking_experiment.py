"""
Embedding-Based Grokking Experiment with Closure Defect Tracking

This uses the proper architecture (learned embeddings) that can actually grok.
Compares tail defect vs closure defect vs test accuracy transitions.

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
from dataclasses import dataclass
from typing import Dict, List, Tuple, Optional

from analog_modular_arithmetic import (
    EmbeddingGrokMLP,
    EmbeddingModularDataset,
    compute_tsallis_entropy_normalized,
)


def compute_closure_defect_embedding(
    model: EmbeddingGrokMLP,
    hidden_states: torch.Tensor,
    k: Optional[int] = None
) -> Tuple[float, float, int]:
    """
    Compute both tail defect and closure defect for embedding model.
    
    Returns: (tail_defect, closure_defect, k)
    """
    with torch.no_grad():
        B, D = hidden_states.shape
        
        # SVD
        U, S, Vh = torch.linalg.svd(hidden_states, full_matrices=False)
        S2 = S ** 2
        total = S2.sum()
        
        # Auto k
        if k is None:
            cumsum = torch.cumsum(S2, dim=0)
            k = (cumsum < 0.9 * total).sum().item() + 1
            k = max(1, min(k, D - 1))
        
        # Tail defect
        tail_energy = S2[k:].sum()
        tail_defect = math.sqrt((tail_energy / (total + 1e-10)).item())
        
        # Closure defect: ||g(h) - g(Pi(h))|| / ||g(h)||
        Pi_basis = Vh[:k].T
        h_coarse_coords = hidden_states @ Pi_basis
        h_coarse = h_coarse_coords @ Pi_basis.T
        
        g_h = model.get_output_from_hidden(hidden_states)
        g_Pi_h = model.get_output_from_hidden(h_coarse)
        
        diff = g_h - g_Pi_h
        diff_norm = torch.norm(diff, dim=-1).mean()
        g_h_norm = torch.norm(g_h, dim=-1).mean() + 1e-10
        
        closure_defect = (diff_norm / g_h_norm).item()
        
        return tail_defect, closure_defect, k


@dataclass
class Metrics:
    epoch: int
    train_acc: float
    test_acc: float
    train_loss: float
    tail_defect: float
    closure_defect: float
    entropy: float
    consolidation: float
    k: int


def run_grokking_experiment(
    p: int = 97,
    operation: str = 'add',
    embed_dim: int = 128,
    hidden_dim: int = 128,
    num_layers: int = 2,
    embed_noise: float = 0.0,  # For analog experiment
    train_fraction: float = 0.3,
    epochs: int = 10000,
    batch_size: int = 512,
    lr: float = 1e-3,
    weight_decay: float = 1.0,
    log_interval: int = 100,
    seed: int = 42,
    label: str = "Experiment"
) -> Tuple[List[Metrics], Dict]:
    """Run a grokking experiment with full metric tracking."""
    
    torch.manual_seed(seed)
    np.random.seed(seed)
    
    device = 'cuda' if torch.cuda.is_available() else 'cpu'
    
    # Dataset
    train_ds = EmbeddingModularDataset(p, operation, train_fraction, 'train', seed)
    test_ds = EmbeddingModularDataset(p, operation, train_fraction, 'test', seed)
    
    train_loader = DataLoader(train_ds, batch_size=batch_size, shuffle=True)
    test_loader = DataLoader(test_ds, batch_size=batch_size, shuffle=False)
    
    # Model
    model = EmbeddingGrokMLP(
        vocab_size=p,
        embed_dim=embed_dim,
        hidden_dim=hidden_dim,
        output_dim=p,
        num_layers=num_layers,
        embed_noise=embed_noise
    ).to(device)
    
    optimizer = optim.AdamW(model.parameters(), lr=lr, weight_decay=weight_decay)
    criterion = nn.CrossEntropyLoss()
    
    history = []
    grokking_epoch = -1
    
    print(f"\n{'='*80}")
    print(f"{label} (embed_noise={embed_noise})")
    print(f"{'='*80}")
    print(f"\n{'Ep':>6} | {'Train':>6} | {'Test':>6} | {'Loss':>7} | {'TailD':>6} | {'CloseD':>6} | {'Consol':>6}")
    print("-" * 70)
    
    for epoch in range(1, epochs + 1):
        # Train
        model.train()
        for a, b, y in train_loader:
            a, b, y = a.to(device), b.to(device), y.to(device)
            optimizer.zero_grad()
            logits = model(a, b)
            loss = criterion(logits, y)
            loss.backward()
            optimizer.step()
        
        # Evaluate periodically
        if epoch % log_interval == 0 or epoch == 1:
            model.eval()
            
            # Collect hidden states
            all_hidden = []
            all_logits = []
            train_correct, train_total, train_loss_sum = 0, 0, 0.0
            
            with torch.no_grad():
                for a, b, y in train_loader:
                    a, b, y = a.to(device), b.to(device), y.to(device)
                    logits = model(a, b)
                    h = model._hidden_activations
                    
                    all_hidden.append(h)
                    all_logits.append(logits)
                    
                    loss = criterion(logits, y)
                    train_loss_sum += loss.item() * a.size(0)
                    train_correct += (logits.argmax(-1) == y).sum().item()
                    train_total += a.size(0)
                    
                    if len(all_hidden) * a.size(0) > 1000:
                        break
            
            H = torch.cat(all_hidden, dim=0)
            logits_all = torch.cat(all_logits, dim=0)
            
            train_acc = train_correct / train_total
            train_loss = train_loss_sum / train_total
            
            # Test accuracy
            test_correct, test_total = 0, 0
            with torch.no_grad():
                for a, b, y in test_loader:
                    a, b, y = a.to(device), b.to(device), y.to(device)
                    logits = model(a, b)
                    test_correct += (logits.argmax(-1) == y).sum().item()
                    test_total += a.size(0)
            test_acc = test_correct / test_total
            
            # Defects
            tail_d, close_d, k = compute_closure_defect_embedding(model, H)
            
            # Entropy
            probs = F.softmax(logits_all, dim=-1).mean(dim=0)
            entropy = compute_tsallis_entropy_normalized(probs, q=1.5)
            consolidation = 1.0 - entropy
            
            m = Metrics(
                epoch=epoch,
                train_acc=train_acc,
                test_acc=test_acc,
                train_loss=train_loss,
                tail_defect=tail_d,
                closure_defect=close_d,
                entropy=entropy,
                consolidation=consolidation,
                k=k
            )
            history.append(m)
            
            # Check grokking
            if grokking_epoch < 0 and test_acc > 0.95:
                grokking_epoch = epoch
                print(f"\n*** GROKKING at epoch {epoch}! ***\n")
            
            print(f"{epoch:6d} | {train_acc*100:5.1f}% | {test_acc*100:5.1f}% | "
                  f"{train_loss:7.4f} | {tail_d:6.3f} | {close_d:6.3f} | {consolidation:6.3f}")
        
        # Early stopping
        if grokking_epoch > 0 and epoch > grokking_epoch + 1000:
            print(f"\nEarly stopping at {epoch}")
            break
    
    # Find transitions
    def find_transition(field, threshold, direction='below'):
        for m in history:
            val = getattr(m, field)
            if direction == 'below' and val < threshold:
                return m.epoch
            if direction == 'above' and val > threshold:
                return m.epoch
        return -1
    
    summary = {
        'grokking_epoch': grokking_epoch,
        'tail_transition': find_transition('tail_defect', 0.15, 'below'),
        'closure_transition': find_transition('closure_defect', 0.15, 'below'),
        'consol_transition': find_transition('consolidation', 0.5, 'above'),
        'final_test_acc': history[-1].test_acc if history else 0,
        'final_tail_defect': history[-1].tail_defect if history else 1,
        'final_closure_defect': history[-1].closure_defect if history else 1,
    }
    
    return history, summary


def main():
    """Run A/B test: no noise vs embedding noise."""
    
    print("\n" + "=" * 80)
    print("A/B TEST: DISCRETE EMBEDDINGS vs NOISY EMBEDDINGS")
    print("=" * 80)
    
    # A: No noise (baseline)
    hist_a, sum_a = run_grokking_experiment(
        embed_noise=0.0,
        epochs=5000,
        log_interval=100,
        label="[A] DISCRETE EMBEDDINGS"
    )
    
    # B: With embedding noise
    hist_b, sum_b = run_grokking_experiment(
        embed_noise=0.1,
        epochs=5000,
        log_interval=100,
        label="[B] NOISY EMBEDDINGS (0.1)"
    )
    
    # Compare
    print("\n" + "=" * 80)
    print("COMPARISON")
    print("=" * 80)
    
    print(f"\n{'Metric':<30} | {'DISCRETE':>12} | {'NOISY':>12}")
    print("-" * 60)
    for key in sum_a.keys():
        va, vb = sum_a[key], sum_b[key]
        if isinstance(va, float):
            print(f"{key:<30} | {va:12.4f} | {vb:12.4f}")
        else:
            print(f"{key:<30} | {va:12} | {vb:12}")
    
    # Analysis
    print("\n" + "=" * 80)
    print("ANALYSIS")
    print("=" * 80)
    
    for label, s in [("DISCRETE", sum_a), ("NOISY", sum_b)]:
        print(f"\n{label}:")
        grok = s['grokking_epoch']
        if grok > 0:
            print(f"  Grokked at epoch {grok}")
            tail = s['tail_transition']
            close = s['closure_transition']
            consol = s['consol_transition']
            
            if tail > 0:
                lead = grok - tail
                print(f"  Tail defect < 0.15 at {tail} (lead: {lead:+d})")
            if close > 0:
                lead = grok - close
                print(f"  Closure defect < 0.15 at {close} (lead: {lead:+d})")
            if consol > 0:
                lead = grok - consol
                print(f"  Consolidation > 0.5 at {consol} (lead: {lead:+d})")
        else:
            print("  Did not grok")
    
    print("\n" + "=" * 80)
    print("THEORY PREDICTION:")
    print("  Closure defect transition should LEAD or COINCIDE with grokking")
    print("  Tail defect may lag (it's a proxy)")
    print("  Embedding noise should enable smoother crystallization")
    print("=" * 80)


if __name__ == "__main__":
    main()
