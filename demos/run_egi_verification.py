#!/usr/bin/env python3
"""
EGI Fixed Point Verification Demo
===================================

This script demonstrates Sprint B: verifying that a grokked system satisfies
the IsEGIFixedPoint condition from QuotientGenerator.lean.

USAGE:
    python run_egi_verification.py --task modular_add --prime 97
    python run_egi_verification.py --checkpoint checkpoints/grokked_model.pt

WHAT THIS TESTS:
    After grokking (functional defect < 0.05), we measure:
    1. Full eigenspectrum of network transition operator
    2. Full eigenspectrum of quotient generator
    3. Whether Rayleigh sets match (strong spectral equivalence)
    4. Tsallis q-value at the grokking transition

SUCCESS CRITERION:
    Strong spectral equivalence with correlation > 0.95 and
    max eigenvalue deviation < 1% across top-k modes.

Author: SGC Research Team
Date: March 31, 2026
"""

import torch
import torch.nn as nn
import torch.optim as optim
import numpy as np
import argparse
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass
import json

from rayleigh_measurement import (
    RayleighMeasurement,
    SpectralEquivalenceResult,
    PartitionData,
    measure_egi_fixed_point,
    print_egi_report
)


# ============================================================================
# 1. GROKKING TASK DEFINITIONS
# ============================================================================

def generate_modular_data(prime: int, operation: str = 'add'):
    """Generate modular arithmetic dataset."""
    x_data = []
    y_data = []
    
    for a in range(prime):
        for b in range(prime):
            if operation == 'add':
                c = (a + b) % prime
            elif operation == 'mul':
                c = (a * b) % prime
            elif operation == 'sub':
                c = (a - b) % prime
            else:
                raise ValueError(f"Unknown operation: {operation}")
            
            x_data.append([a, b])
            y_data.append(c)
    
    x = torch.tensor(x_data, dtype=torch.long)
    y = torch.tensor(y_data, dtype=torch.long)
    
    return x, y


class GrokkingtNet(nn.Module):
    """Simple MLP for modular arithmetic grokking."""
    
    def __init__(self, prime: int, embed_dim: int = 128, hidden_dim: int = 256):
        super().__init__()
        self.prime = prime
        self.embed_dim = embed_dim
        
        self.embed = nn.Embedding(prime, embed_dim)
        self.fc1 = nn.Linear(2 * embed_dim, hidden_dim)
        self.fc2 = nn.Linear(hidden_dim, hidden_dim)
        self.fc3 = nn.Linear(hidden_dim, prime)
        
    def forward(self, x):
        # x: (batch, 2) with values in [0, prime)
        a_embed = self.embed(x[:, 0])
        b_embed = self.embed(x[:, 1])
        combined = torch.cat([a_embed, b_embed], dim=-1)
        
        h = torch.relu(self.fc1(combined))
        h = torch.relu(self.fc2(h))
        logits = self.fc3(h)
        
        return logits


# ============================================================================
# 2. TRAINING WITH SGC METRICS
# ============================================================================

@dataclass
class TrainingMetrics:
    """Metrics tracked during grokking training."""
    step: int
    train_loss: float
    train_acc: float
    test_acc: float
    functional_defect: float
    spectral_gap: float
    is_grokked: bool


def train_until_grokking(
    model: nn.Module,
    train_loader: torch.utils.data.DataLoader,
    test_loader: torch.utils.data.DataLoader,
    device: str = 'cuda',
    max_steps: int = 100000,
    grokking_threshold: float = 0.95,
    defect_threshold: float = 0.05,
    log_interval: int = 100
) -> List[TrainingMetrics]:
    """
    Train model until grokking is detected.
    
    Grokking is detected when:
    1. Test accuracy > grokking_threshold (0.95)
    2. Functional defect < defect_threshold (0.05)
    """
    model.to(device)
    optimizer = optim.AdamW(model.parameters(), lr=1e-3, weight_decay=0.1)
    criterion = nn.CrossEntropyLoss()
    
    metrics_history = []
    step = 0
    is_grokked = False
    
    print("Training until grokking...")
    print("-" * 60)
    
    while step < max_steps and not is_grokked:
        model.train()
        
        for x, y in train_loader:
            x, y = x.to(device), y.to(device)
            
            optimizer.zero_grad()
            logits = model(x)
            loss = criterion(logits, y)
            loss.backward()
            optimizer.step()
            
            step += 1
            
            if step % log_interval == 0:
                # Evaluate
                train_acc = compute_accuracy(model, train_loader, device)
                test_acc = compute_accuracy(model, test_loader, device)
                
                # Compute functional defect (simplified: 1 - test_acc as proxy)
                functional_defect = 1.0 - test_acc
                
                # Compute spectral gap (placeholder)
                spectral_gap = estimate_spectral_gap(model, test_loader, device)
                
                # Check grokking
                is_grokked = (test_acc > grokking_threshold and 
                              functional_defect < defect_threshold)
                
                metrics = TrainingMetrics(
                    step=step,
                    train_loss=loss.item(),
                    train_acc=train_acc,
                    test_acc=test_acc,
                    functional_defect=functional_defect,
                    spectral_gap=spectral_gap,
                    is_grokked=is_grokked
                )
                metrics_history.append(metrics)
                
                print(f"Step {step:6d} | Train: {train_acc:.3f} | Test: {test_acc:.3f} | "
                      f"Defect: {functional_defect:.4f} | Gap: {spectral_gap:.4f}")
                
                if is_grokked:
                    print("\n" + "="*60)
                    print("GROKKING DETECTED!")
                    print("="*60)
                    break
            
            if step >= max_steps:
                break
    
    return metrics_history


def compute_accuracy(model, dataloader, device):
    """Compute classification accuracy."""
    model.eval()
    correct = 0
    total = 0
    
    with torch.no_grad():
        for x, y in dataloader:
            x, y = x.to(device), y.to(device)
            logits = model(x)
            preds = logits.argmax(dim=-1)
            correct += (preds == y).sum().item()
            total += len(y)
    
    return correct / total if total > 0 else 0.0


def estimate_spectral_gap(model, dataloader, device, n_samples=100):
    """Estimate spectral gap from gradient structure."""
    model.eval()
    gradients = []
    
    for x, y in dataloader:
        if len(gradients) >= n_samples:
            break
        x, y = x.to(device), y.to(device)
        
        for i in range(min(len(x), n_samples - len(gradients))):
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
                gradients.append(torch.cat(g).cpu())
    
    if len(gradients) < 10:
        return 0.0
    
    G = torch.stack(gradients)
    _, S, _ = torch.linalg.svd(G, full_matrices=False)
    
    if len(S) >= 2:
        return (S[0] - S[1]).item() / (S[0].item() + 1e-10)
    return 0.0


# ============================================================================
# 3. SGC PARTITION EXTRACTION
# ============================================================================

def extract_sgc_partition(
    model: nn.Module,
    dataloader: torch.utils.data.DataLoader,
    device: str,
    n_clusters: int = 10
) -> PartitionData:
    """
    Extract partition from trained model's learned representations.
    
    Uses simple quantile-based clustering on activation norms to define blocks.
    (Avoids sklearn dependency issues)
    """
    model.eval()
    
    # Hook to capture hidden layer activations
    activation_buffer = []
    def hook_fn(module, input, output):
        activation_buffer.append(output.detach())
    
    # Find second-to-last linear layer (hidden representations)
    linear_layers = []
    for name, module in model.named_modules():
        if isinstance(module, nn.Linear):
            linear_layers.append((name, module))
    
    if len(linear_layers) < 2:
        # Fallback: trivial partition
        return PartitionData(
            n_blocks=n_clusters,
            block_assignment=np.arange(n_clusters) % n_clusters,
            block_sizes=np.ones(n_clusters, dtype=int)
        )
    
    target_layer = linear_layers[-2][1]  # Second-to-last
    hook = target_layer.register_forward_hook(hook_fn)
    
    try:
        with torch.no_grad():
            for x, _ in dataloader:
                x = x.to(device)
                _ = model(x)
                if len(activation_buffer) > 10:
                    break
        
        all_acts = torch.cat(activation_buffer, dim=0).cpu().numpy()
    finally:
        hook.remove()
    
    # Simple quantile-based clustering (avoids sklearn)
    n_samples = min(len(all_acts), 1000)
    acts = all_acts[:n_samples]
    
    # Use activation norm for clustering
    norms = np.linalg.norm(acts, axis=1)
    
    # Quantile-based assignment
    n_clusters = min(n_clusters, n_samples)
    quantiles = np.percentile(norms, np.linspace(0, 100, n_clusters + 1))
    labels = np.digitize(norms, quantiles[1:-1])
    
    # Truncate to n_states
    n_states = min(50, n_samples)
    block_assignment = labels[:n_states]
    n_blocks = len(np.unique(block_assignment))
    block_sizes = np.array([np.sum(block_assignment == i) for i in range(n_blocks)])
    
    return PartitionData(
        n_blocks=n_blocks,
        block_assignment=block_assignment,
        block_sizes=block_sizes
    )


# ============================================================================
# 4. MAIN EGI VERIFICATION
# ============================================================================

def run_egi_verification(
    model: nn.Module,
    test_loader: torch.utils.data.DataLoader,
    device: str = 'cuda',
    top_k: int = 10,
    tolerance: float = 0.01
) -> SpectralEquivalenceResult:
    """
    Run full EGI fixed point verification.
    
    This is the main Sprint B verification function.
    """
    print("\n" + "="*60)
    print("RUNNING EGI FIXED POINT VERIFICATION")
    print("="*60)
    
    # Extract partition from model
    print("\nExtracting SGC partition from learned representations...")
    partition = extract_sgc_partition(model, test_loader, device)
    print(f"Partition: {partition.n_blocks} blocks")
    
    # Create measurement
    print("\nComputing Rayleigh sets...")
    measurement = RayleighMeasurement(
        model=model,
        dataloader=test_loader,
        partition=partition,
        device=device,
        n_states=min(50, partition.n_blocks * 5),
        extraction_method='activation_covariance'
    )
    
    # Measure spectral equivalence
    print(f"\nTesting spectral equivalence (top-{top_k}, tolerance={tolerance*100:.1f}%)...")
    result = measurement.measure_spectral_equivalence(
        top_k=top_k,
        tolerance=tolerance
    )
    
    # Print report
    print_egi_report(result)
    
    return result


def save_verification_results(
    result: SpectralEquivalenceResult,
    metrics_history: List[TrainingMetrics],
    output_path: Path
):
    """Save verification results to JSON."""
    output = {
        'timestamp': datetime.now().isoformat(),
        'is_egi_fixed_point': bool(result.is_strong_equivalent),
        'equivalence_type': result.equivalence_type.value,
        'eigenvalue_correlation': float(result.eigenvalue_correlation),
        'rayleigh_set_overlap': float(result.rayleigh_set_overlap),
        'max_eigenvalue_deviation': float(result.max_eigenvalue_deviation),
        'gap_network': float(result.gap_network),
        'gap_quotient': float(result.gap_quotient),
        'gap_relative_error': float(result.gap_relative_error),
        'tsallis_q': float(result.tsallis_q),
        'is_at_lifshitz': bool(result.is_at_lifshitz),
        'training_steps': int(metrics_history[-1].step) if metrics_history else 0,
        'final_test_acc': float(metrics_history[-1].test_acc) if metrics_history else 0,
        'final_defect': float(metrics_history[-1].functional_defect) if metrics_history else 1.0
    }
    
    with open(output_path, 'w') as f:
        json.dump(output, f, indent=2)
    
    print(f"\nResults saved to {output_path}")


# ============================================================================
# 5. MAIN
# ============================================================================

def main():
    parser = argparse.ArgumentParser(description='EGI Fixed Point Verification')
    parser.add_argument('--task', type=str, default='modular_add',
                        choices=['modular_add', 'modular_mul', 'modular_sub'])
    parser.add_argument('--prime', type=int, default=97)
    parser.add_argument('--checkpoint', type=str, default=None,
                        help='Path to pre-trained checkpoint')
    parser.add_argument('--max_steps', type=int, default=50000)
    parser.add_argument('--top_k', type=int, default=10,
                        help='Number of top eigenvalues to compare')
    parser.add_argument('--tolerance', type=float, default=0.01,
                        help='Tolerance for eigenvalue equality (1%)')
    parser.add_argument('--output', type=str, default='egi_verification_result.json')
    parser.add_argument('--device', type=str, default='cuda' if torch.cuda.is_available() else 'cpu')
    
    args = parser.parse_args()
    
    print("="*60)
    print("EGI FIXED POINT VERIFICATION - Sprint B")
    print("="*60)
    print(f"Task: {args.task}")
    print(f"Prime: {args.prime}")
    print(f"Device: {args.device}")
    print(f"Top-k: {args.top_k}")
    print(f"Tolerance: {args.tolerance*100:.1f}%")
    
    # Generate data
    print("\nGenerating data...")
    operation = args.task.split('_')[1]  # 'add', 'mul', or 'sub'
    x, y = generate_modular_data(args.prime, operation)
    
    # Train/test split
    n = len(x)
    perm = torch.randperm(n)
    train_size = int(0.7 * n)
    
    train_x, train_y = x[perm[:train_size]], y[perm[:train_size]]
    test_x, test_y = x[perm[train_size:]], y[perm[train_size:]]
    
    train_dataset = torch.utils.data.TensorDataset(train_x, train_y)
    test_dataset = torch.utils.data.TensorDataset(test_x, test_y)
    
    train_loader = torch.utils.data.DataLoader(train_dataset, batch_size=64, shuffle=True)
    test_loader = torch.utils.data.DataLoader(test_dataset, batch_size=64, shuffle=False)
    
    # Create or load model
    model = GrokkingtNet(args.prime)
    
    if args.checkpoint:
        print(f"\nLoading checkpoint: {args.checkpoint}")
        model.load_state_dict(torch.load(args.checkpoint, map_location=args.device))
        metrics_history = []
    else:
        # Train until grokking
        metrics_history = train_until_grokking(
            model, train_loader, test_loader,
            device=args.device,
            max_steps=args.max_steps
        )
    
    # Verify EGI fixed point
    result = run_egi_verification(
        model, test_loader,
        device=args.device,
        top_k=args.top_k,
        tolerance=args.tolerance
    )
    
    # Save results
    save_verification_results(
        result, metrics_history,
        Path(args.output)
    )
    
    # Final verdict
    print("\n" + "="*60)
    if result.is_strong_equivalent:
        print("VERDICT: IsEGIFixedPoint SATISFIED")
        print("The system has reached genuine self-referential understanding.")
    else:
        print(f"VERDICT: IsEGIFixedPoint NOT SATISFIED ({result.equivalence_type.value})")
        if result.is_weak_equivalent:
            print("System satisfies WEAK equivalence (gap-matching only).")
            print("This is the Tanaka drift regime - lottery consensus, not understanding.")
        else:
            print("System does not satisfy spectral equivalence at all.")
    print("="*60)
    
    return result


if __name__ == "__main__":
    main()
