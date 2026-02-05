"""
Functional Defect Experiment: Validating the Functional vs Geometric Blanket Theory

Key Hypothesis: Grokking is an ALGEBRAIC phase transition, not geometric compression.
- Geometric Defect (PCA-based): INCREASES during grokking (model learns curved manifold)
- Functional Defect (within-class variance): COLLAPSES to zero at grokking

The Functional Blanket measures whether the model respects equivalence classes:
For modular addition (a+b) mod p = r, all pairs (a,b) summing to r are functionally identical.

Author: SGC Research Team
Date: February 5, 2026
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
import torch.optim as optim
from torch.utils.data import DataLoader
import numpy as np
import math
from dataclasses import dataclass, field
from typing import Dict, List, Tuple, Optional
from collections import defaultdict

from analog_modular_arithmetic import (
    EmbeddingGrokMLP,
    EmbeddingModularDataset,
    compute_tsallis_entropy_normalized,
)


# =============================================================================
# FUNCTIONAL DEFECT: The Key Measurement
# =============================================================================

def compute_functional_defect(
    hidden_states: torch.Tensor,
    targets: torch.Tensor,
    p: int,
    return_per_class: bool = False
) -> Tuple[float, float, Optional[torch.Tensor]]:
    """
    Compute the Functional Defect: within-class variance across algebraic equivalence classes.
    
    For modular addition (a+b) mod p = r:
    - Group all hidden states h(a,b) by their target residue r
    - Compute variance of h within each group
    - Average across all p residue classes
    - Normalize by total variance
    
    Args:
        hidden_states: (N, D) tensor of hidden activations
        targets: (N,) tensor of target residue classes (0 to p-1)
        p: modulus
        return_per_class: if True, return per-class variances
    
    Returns:
        (functional_defect, total_variance, per_class_variances if requested)
    
    Theory Prediction:
        - Functional defect -> 0 at grokking (model learns equivalence classes)
        - Total variance may remain high (geometric defect increases)
    """
    device = hidden_states.device
    N, D = hidden_states.shape
    
    # Total variance (for normalization)
    total_var = hidden_states.var(dim=0).mean().item()
    
    if total_var < 1e-10:
        return 0.0, total_var, None
    
    # Per-class variances
    class_variances = []
    class_counts = []
    
    for r in range(p):
        mask = (targets == r)
        count = mask.sum().item()
        
        if count > 1:
            h_r = hidden_states[mask]  # All hidden states for residue class r
            # Variance within this equivalence class
            var_r = h_r.var(dim=0).mean().item()
            class_variances.append(var_r)
            class_counts.append(count)
        elif count == 1:
            class_variances.append(0.0)  # Single sample = no variance
            class_counts.append(count)
    
    if not class_variances:
        return 1.0, total_var, None
    
    # Weighted average by class count
    class_variances = torch.tensor(class_variances, device=device)
    class_counts = torch.tensor(class_counts, dtype=torch.float, device=device)
    
    # Mean within-class variance
    within_class_var = (class_variances * class_counts).sum() / class_counts.sum()
    
    # Functional defect = within-class variance / total variance
    # This is 0 when all points in each class collapse to the same representation
    functional_defect = (within_class_var / total_var).item()
    
    if return_per_class:
        return functional_defect, total_var, class_variances
    return functional_defect, total_var, None


def compute_functional_defect_detailed(
    hidden_states: torch.Tensor,
    targets: torch.Tensor,
    p: int
) -> Dict[str, float]:
    """
    Detailed functional defect analysis with multiple metrics.
    
    Returns dict with:
        - functional_defect: normalized within-class variance
        - within_class_var: raw within-class variance
        - between_class_var: variance of class centroids
        - total_var: total variance
        - class_separation: between_class_var / within_class_var (higher = better separation)
    """
    device = hidden_states.device
    N, D = hidden_states.shape
    
    total_var = hidden_states.var(dim=0).mean().item()
    global_mean = hidden_states.mean(dim=0)
    
    # Collect per-class statistics
    class_means = []
    class_vars = []
    class_counts = []
    
    for r in range(p):
        mask = (targets == r)
        count = mask.sum().item()
        
        if count > 0:
            h_r = hidden_states[mask]
            mean_r = h_r.mean(dim=0)
            class_means.append(mean_r)
            class_counts.append(count)
            
            if count > 1:
                var_r = h_r.var(dim=0).mean().item()
            else:
                var_r = 0.0
            class_vars.append(var_r)
    
    if not class_means:
        return {
            'functional_defect': 1.0,
            'within_class_var': total_var,
            'between_class_var': 0.0,
            'total_var': total_var,
            'class_separation': 0.0
        }
    
    # Stack class means
    class_means = torch.stack(class_means, dim=0)  # (num_classes, D)
    class_counts = torch.tensor(class_counts, dtype=torch.float, device=device)
    class_vars = torch.tensor(class_vars, device=device)
    
    # Within-class variance (weighted average)
    within_class_var = (class_vars * class_counts).sum() / class_counts.sum()
    
    # Between-class variance (variance of class centroids)
    # Weighted by class counts
    weighted_mean = (class_means * class_counts.unsqueeze(1)).sum(0) / class_counts.sum()
    deviations = class_means - weighted_mean.unsqueeze(0)
    between_class_var = ((deviations ** 2).mean(dim=1) * class_counts).sum() / class_counts.sum()
    
    # Functional defect
    functional_defect = (within_class_var / (total_var + 1e-10)).item()
    
    # Class separation ratio (like Fisher's criterion)
    class_separation = (between_class_var / (within_class_var + 1e-10)).item()
    
    return {
        'functional_defect': functional_defect,
        'within_class_var': within_class_var.item(),
        'between_class_var': between_class_var.item(),
        'total_var': total_var,
        'class_separation': class_separation
    }


# =============================================================================
# RELATIVE EXTROPY: Dual to Entropy
# =============================================================================

def compute_relative_extropy(probs: torch.Tensor, prior: Optional[torch.Tensor] = None) -> float:
    """
    Compute relative extropy J(p || π).
    
    Extropy is the Bregman dual to entropy:
    J(p || π) = Σ_i π_i * p_i² 
    
    For uniform prior π_i = 1/n:
    J(p || uniform) = (1/n) * Σ_i p_i² = ||p||² / n
    
    This measures "certainty" or "consolidation" - high when probability is concentrated.
    
    Args:
        probs: probability distribution (sums to 1)
        prior: reference distribution (default: uniform)
    
    Returns:
        Relative extropy value
    """
    n = probs.shape[-1]
    
    if prior is None:
        # Uniform prior
        prior = torch.ones_like(probs) / n
    
    # J(p || π) = Σ π_i p_i²
    extropy = (prior * probs ** 2).sum(dim=-1)
    
    if extropy.dim() > 0:
        return extropy.mean().item()
    return extropy.item()


def compute_extropy_normalized(probs: torch.Tensor) -> float:
    """
    Normalized extropy in [0, 1].
    
    For uniform distribution p_i = 1/n: J = 1/n (minimum certainty)
    For delta distribution p_i = δ_ij: J = 1/n (maximum certainty... wait)
    
    Actually, let's use a cleaner normalization:
    Certainty = ||p||² which ranges from 1/n (uniform) to 1 (delta)
    Normalized certainty = (||p||² - 1/n) / (1 - 1/n)
    """
    n = probs.shape[-1]
    p_squared = (probs ** 2).sum(dim=-1)
    
    min_val = 1.0 / n  # uniform
    max_val = 1.0      # delta
    
    normalized = (p_squared - min_val) / (max_val - min_val + 1e-10)
    
    if normalized.dim() > 0:
        return normalized.mean().item()
    return normalized.item()


# =============================================================================
# GEOMETRIC DEFECT (for comparison)
# =============================================================================

def compute_geometric_defect(
    hidden_states: torch.Tensor,
    model: EmbeddingGrokMLP,
    k: Optional[int] = None
) -> Tuple[float, float, int]:
    """
    Compute geometric (PCA-based) defects:
    - Tail defect: energy in tail singular values
    - Closure defect: ||g(h) - g(Π h)|| / ||g(h)||
    
    Returns: (tail_defect, closure_defect, k)
    """
    with torch.no_grad():
        B, D = hidden_states.shape
        
        # SVD
        U, S, Vh = torch.linalg.svd(hidden_states, full_matrices=False)
        S2 = S ** 2
        total = S2.sum()
        
        if k is None:
            cumsum = torch.cumsum(S2, dim=0)
            k = (cumsum < 0.9 * total).sum().item() + 1
            k = max(1, min(k, D - 1))
        
        # Tail defect
        tail_energy = S2[k:].sum()
        tail_defect = math.sqrt((tail_energy / (total + 1e-10)).item())
        
        # Closure defect
        Pi_basis = Vh[:k].T
        h_coarse = hidden_states @ Pi_basis @ Pi_basis.T
        
        g_h = model.get_output_from_hidden(hidden_states)
        g_Pi_h = model.get_output_from_hidden(h_coarse)
        
        diff_norm = torch.norm(g_h - g_Pi_h, dim=-1).mean()
        g_h_norm = torch.norm(g_h, dim=-1).mean() + 1e-10
        closure_defect = (diff_norm / g_h_norm).item()
        
        return tail_defect, closure_defect, k


# =============================================================================
# MAIN EXPERIMENT
# =============================================================================

@dataclass
class ExperimentMetrics:
    epoch: int
    train_acc: float
    test_acc: float
    train_loss: float
    
    # Functional defect (THE KEY METRIC)
    functional_defect: float
    within_class_var: float
    between_class_var: float
    class_separation: float
    
    # Geometric defects (for comparison)
    tail_defect: float
    closure_defect: float
    
    # Entropy/Extropy
    entropy: float
    extropy: float
    consolidation: float
    
    k: int


def run_functional_defect_experiment(
    p: int = 97,
    operation: str = 'add',
    embed_dim: int = 128,
    hidden_dim: int = 128,
    num_layers: int = 2,
    embed_noise: float = 0.0,
    train_fraction: float = 0.3,
    epochs: int = 5000,
    batch_size: int = 512,
    lr: float = 1e-3,
    weight_decay: float = 1.0,
    log_interval: int = 50,
    seed: int = 42,
    label: str = "Experiment"
) -> Tuple[List[ExperimentMetrics], Dict]:
    """
    Run grokking experiment with functional defect tracking.
    
    Key measurements:
    1. Functional defect (within-class variance) - predicted to collapse at grokking
    2. Geometric defect (closure defect) - predicted to INCREASE at grokking
    3. Class separation (between/within ratio) - predicted to spike at grokking
    """
    
    torch.manual_seed(seed)
    np.random.seed(seed)
    
    device = 'cuda' if torch.cuda.is_available() else 'cpu'
    
    # Dataset
    train_ds = EmbeddingModularDataset(p, operation, train_fraction, 'train', seed)
    test_ds = EmbeddingModularDataset(p, operation, train_fraction, 'test', seed)
    
    train_loader = DataLoader(train_ds, batch_size=batch_size, shuffle=True)
    test_loader = DataLoader(test_ds, batch_size=batch_size, shuffle=False)
    
    # Full dataset loaders for defect computation
    full_train_loader = DataLoader(train_ds, batch_size=len(train_ds), shuffle=False)
    
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
    functional_collapse_epoch = -1
    
    print(f"\n{'='*100}")
    print(f"{label}")
    print(f"{'='*100}")
    print(f"\n{'Ep':>5} | {'Train':>6} | {'Test':>6} | {'FuncD':>7} | {'CloseD':>7} | "
          f"{'ClassSep':>8} | {'Extropy':>7} | {'Status':<20}")
    print("-" * 100)
    
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
        
        # Evaluate
        if epoch % log_interval == 0 or epoch == 1:
            model.eval()
            
            # Get ALL training hidden states for proper defect computation
            with torch.no_grad():
                for a, b, y in full_train_loader:
                    a, b, y = a.to(device), b.to(device), y.to(device)
                    logits = model(a, b)
                    hidden_states = model._hidden_activations
                    targets = y
                    break
            
            # Functional defect (THE KEY MEASUREMENT)
            func_detailed = compute_functional_defect_detailed(hidden_states, targets, p)
            
            # Geometric defect
            tail_d, close_d, k = compute_geometric_defect(hidden_states, model)
            
            # Entropy/Extropy
            probs = F.softmax(logits, dim=-1).mean(dim=0)
            entropy = compute_tsallis_entropy_normalized(probs, q=1.0)  # Shannon for simplicity
            extropy = compute_extropy_normalized(probs)
            consolidation = 1.0 - entropy
            
            # Accuracies
            train_correct = (logits.argmax(-1) == targets).sum().item()
            train_acc = train_correct / len(targets)
            train_loss = criterion(logits, targets).item()
            
            test_correct, test_total = 0, 0
            with torch.no_grad():
                for a, b, y in test_loader:
                    a, b, y = a.to(device), b.to(device), y.to(device)
                    logits = model(a, b)
                    test_correct += (logits.argmax(-1) == y).sum().item()
                    test_total += y.size(0)
            test_acc = test_correct / test_total
            
            m = ExperimentMetrics(
                epoch=epoch,
                train_acc=train_acc,
                test_acc=test_acc,
                train_loss=train_loss,
                functional_defect=func_detailed['functional_defect'],
                within_class_var=func_detailed['within_class_var'],
                between_class_var=func_detailed['between_class_var'],
                class_separation=func_detailed['class_separation'],
                tail_defect=tail_d,
                closure_defect=close_d,
                entropy=entropy,
                extropy=extropy,
                consolidation=consolidation,
                k=k
            )
            history.append(m)
            
            # Check transitions
            status = ""
            
            # Grokking detection
            if grokking_epoch < 0 and test_acc > 0.95:
                grokking_epoch = epoch
                status = "*** GROKKING! ***"
            
            # Functional defect collapse detection
            if functional_collapse_epoch < 0 and func_detailed['functional_defect'] < 0.1:
                functional_collapse_epoch = epoch
                if status:
                    status += " + FuncD collapse"
                else:
                    status = "FuncD < 0.1"
            
            print(f"{epoch:5d} | {train_acc*100:5.1f}% | {test_acc*100:5.1f}% | "
                  f"{func_detailed['functional_defect']:7.4f} | {close_d:7.4f} | "
                  f"{func_detailed['class_separation']:8.2f} | {extropy:7.4f} | {status}")
        
        # Early stopping after grokking
        if grokking_epoch > 0 and epoch > grokking_epoch + 500:
            print(f"\nEarly stopping at epoch {epoch}")
            break
    
    # Summary
    summary = {
        'grokking_epoch': grokking_epoch,
        'functional_collapse_epoch': functional_collapse_epoch,
        'final_test_acc': history[-1].test_acc if history else 0,
        'final_functional_defect': history[-1].functional_defect if history else 1,
        'final_closure_defect': history[-1].closure_defect if history else 1,
        'final_class_separation': history[-1].class_separation if history else 0,
    }
    
    return history, summary


def main():
    """Run the critical experiment to validate Functional vs Geometric Blanket theory."""
    
    print("\n" + "=" * 100)
    print("FUNCTIONAL DEFECT EXPERIMENT: Validating the Algebraic Phase Transition Theory")
    print("=" * 100)
    print("\nHypothesis:")
    print("  - Functional Defect (within-class variance) -> 0 at grokking")
    print("  - Geometric Defect (closure defect) INCREASES at grokking")
    print("  - Class Separation (between/within ratio) spikes at grokking")
    print("=" * 100)
    
    # Run with discrete embeddings
    hist_discrete, sum_discrete = run_functional_defect_experiment(
        embed_noise=0.0,
        epochs=3000,
        log_interval=50,
        label="[A] DISCRETE EMBEDDINGS (baseline)"
    )
    
    # Run with noisy embeddings (analog world)
    hist_noisy, sum_noisy = run_functional_defect_experiment(
        embed_noise=0.1,
        epochs=3000,
        log_interval=50,
        label="[B] NOISY EMBEDDINGS (analog world)"
    )
    
    # Comparison
    print("\n" + "=" * 100)
    print("COMPARISON: DISCRETE vs ANALOG")
    print("=" * 100)
    
    print(f"\n{'Metric':<35} | {'DISCRETE':>15} | {'ANALOG':>15}")
    print("-" * 70)
    for key in sum_discrete.keys():
        vd, vn = sum_discrete[key], sum_noisy[key]
        if isinstance(vd, float):
            print(f"{key:<35} | {vd:15.4f} | {vn:15.4f}")
        else:
            print(f"{key:<35} | {vd:>15} | {vn:>15}")
    
    # Analysis
    print("\n" + "=" * 100)
    print("THEORY VALIDATION")
    print("=" * 100)
    
    for label, hist, summ in [("DISCRETE", hist_discrete, sum_discrete), 
                               ("ANALOG", hist_noisy, sum_noisy)]:
        print(f"\n{label}:")
        grok = summ['grokking_epoch']
        func_collapse = summ['functional_collapse_epoch']
        
        if grok > 0:
            print(f"  Grokked at epoch {grok}")
            
            # Find metrics at grokking
            grok_metrics = None
            pre_grok_metrics = None
            for m in hist:
                if m.epoch <= grok:
                    if m.epoch == grok or (grok_metrics is None):
                        grok_metrics = m
                    if m.epoch < grok - 100:
                        pre_grok_metrics = m
            
            if pre_grok_metrics and grok_metrics:
                print(f"\n  Pre-grokking (epoch {pre_grok_metrics.epoch}):")
                print(f"    Functional defect: {pre_grok_metrics.functional_defect:.4f}")
                print(f"    Closure defect:    {pre_grok_metrics.closure_defect:.4f}")
                print(f"    Class separation:  {pre_grok_metrics.class_separation:.2f}")
                
                print(f"\n  At grokking (epoch {grok_metrics.epoch}):")
                print(f"    Functional defect: {grok_metrics.functional_defect:.4f}")
                print(f"    Closure defect:    {grok_metrics.closure_defect:.4f}")
                print(f"    Class separation:  {grok_metrics.class_separation:.2f}")
                
                # Validate theory
                func_decreased = grok_metrics.functional_defect < pre_grok_metrics.functional_defect
                close_increased = grok_metrics.closure_defect > pre_grok_metrics.closure_defect
                sep_increased = grok_metrics.class_separation > pre_grok_metrics.class_separation
                
                print(f"\n  Theory Predictions:")
                print(f"    [{'YES' if func_decreased else 'NO'}] Functional defect decreased: {func_decreased} "
                      f"({pre_grok_metrics.functional_defect:.4f} -> {grok_metrics.functional_defect:.4f})")
                print(f"    [{'YES' if close_increased else 'NO'}] Closure defect increased: {close_increased} "
                      f"({pre_grok_metrics.closure_defect:.4f} -> {grok_metrics.closure_defect:.4f})")
                print(f"    [{'YES' if sep_increased else 'NO'}] Class separation increased: {sep_increased} "
                      f"({pre_grok_metrics.class_separation:.2f} -> {grok_metrics.class_separation:.2f})")
            
            if func_collapse > 0:
                lead = grok - func_collapse
                print(f"\n  Functional defect collapsed at epoch {func_collapse} (lead: {lead:+d} epochs)")
        else:
            print("  Did not grok")
    
    print("\n" + "=" * 100)
    print("CONCLUSION")
    print("=" * 100)
    print("""
If the theory is correct:
  1. Functional defect should DROP at grokking (algebraic structure learned)
  2. Geometric/closure defect should INCREASE (curved manifold, not flat subspace)
  3. Class separation should SPIKE (equivalence classes become distinguishable)
  4. Analog world should grok faster (noise forces robust structure learning)

This validates: GROKKING = ALGEBRAIC PHASE TRANSITION, not geometric compression.
The Markov blanket is FUNCTIONAL (respecting symmetry group), not GEOMETRIC (PCA subspace).
""")


if __name__ == "__main__":
    main()
