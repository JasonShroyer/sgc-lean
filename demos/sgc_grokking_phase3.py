#!/usr/bin/env python3
"""
SGC Phase-3: Causal Validation of Bulk Crystallization (SGC-RG)

Phase-2 revealed inside-out "bulk crystallization": hidden layer shows dominant
compression (eff-rank 35→20, entropy 3.71→3.39) while input converges to global
and output diverges.

Phase-3 objective: PROVE CAUSALITY (not just correlation) and test generality.

HYPOTHESES (falsifiable):
  H1: Bulk crystallization is causal - enforcing low-rank hidden structure 
      should systematically change grokking time.
  H2: Task structure sets required bulk rank - critical rank varies with 
      task complexity (add vs mul).
  H3: Output entropy-production spike is early-warning marker - reproducible
      precursor aligned with onset of hidden compression.

EXPERIMENTAL SUITES:
  A: Task generality (multiplication baseline)
  B: Architectural causality (factorized hidden rank sweep)
  C: Intervention causality (rank shock)

Author: SGC Research Team
Date: February 2026
"""

import argparse
import csv
import os
from dataclasses import dataclass, field
from datetime import datetime
from typing import Dict, List, Optional, Tuple

import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F
from scipy import stats
from torch.utils.data import Dataset, DataLoader
from torch.utils.tensorboard import SummaryWriter


# ═══════════════════════════════════════════════════════════════════════════════
# DATASETS: Multi-task support
# ═══════════════════════════════════════════════════════════════════════════════

class ModularAdditionDataset(Dataset):
    """Dataset for (a + b) mod p task."""
    
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
    """Dataset for (a * b) mod p task.
    
    Note: Multiplication mod prime is more structured (group theory) but
    may require longer training. Excludes pairs with a=0 or b=0 to focus
    on the multiplicative group structure.
    """
    
    def __init__(self, p: int = 97, train: bool = True, train_fraction: float = 0.3, 
                 seed: int = 42, exclude_zero: bool = True):
        self.p = p
        
        if exclude_zero:
            all_pairs = [(a, b) for a in range(1, p) for b in range(1, p)]
        else:
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


# ═══════════════════════════════════════════════════════════════════════════════
# ARCHITECTURE: FactorizedLinear and GrokMLP with rank constraints
# ═══════════════════════════════════════════════════════════════════════════════

class FactorizedLinear(nn.Module):
    """Low-rank linear layer: y = A @ (B @ x) + bias
    
    Parameters:
        A: (out_features, rank)
        B: (rank, in_features)
    
    This enforces rank-r constraint on the weight matrix W = A @ B.
    Used to test H1: whether bulk compression is causal for grokking.
    """
    
    def __init__(self, in_features: int, out_features: int, rank: int, bias: bool = True):
        super().__init__()
        self.in_features = in_features
        self.out_features = out_features
        self.rank = rank
        
        # Initialize with scaled random values
        self.A = nn.Parameter(torch.randn(out_features, rank) / np.sqrt(rank))
        self.B = nn.Parameter(torch.randn(rank, in_features) / np.sqrt(in_features))
        
        if bias:
            self.bias = nn.Parameter(torch.zeros(out_features))
        else:
            self.register_parameter('bias', None)
    
    def forward(self, x: torch.Tensor) -> torch.Tensor:
        # y = A @ (B @ x) + bias
        out = F.linear(x, self.B)  # (batch, rank)
        out = F.linear(out, self.A)  # (batch, out_features)
        if self.bias is not None:
            out = out + self.bias
        return out
    
    def get_effective_weight(self) -> torch.Tensor:
        """Return the effective weight matrix W = A @ B for analysis."""
        return self.A @ self.B


class GrokMLP(nn.Module):
    """MLP for grokking experiments with optional factorized hidden layer.
    
    Architecture: input -> hidden1 -> hidden2 -> output
    If hidden_rank is specified, the hidden1->hidden2 layer is factorized.
    """
    
    def __init__(self, p: int = 97, hidden_dim: int = 128, hidden_rank: Optional[int] = None):
        super().__init__()
        self.p = p
        self.hidden_dim = hidden_dim
        self.hidden_rank = hidden_rank
        
        # Input layer: 2p -> hidden
        self.input_layer = nn.Linear(2 * p, hidden_dim)
        
        # Hidden layer: hidden -> hidden (optionally factorized)
        if hidden_rank is not None:
            self.hidden_layer = FactorizedLinear(hidden_dim, hidden_dim, hidden_rank)
            self.is_factorized = True
        else:
            self.hidden_layer = nn.Linear(hidden_dim, hidden_dim)
            self.is_factorized = False
        
        # Output layer: hidden -> p
        self.output_layer = nn.Linear(hidden_dim, p)
    
    def forward(self, x: torch.Tensor) -> torch.Tensor:
        x = F.relu(self.input_layer(x))
        x = F.relu(self.hidden_layer(x))
        return self.output_layer(x)
    
    def get_layer_weights(self) -> Dict[str, torch.Tensor]:
        """Return weight matrices for each layer (for spectral analysis)."""
        weights = {
            'input': self.input_layer.weight.data,
            'output': self.output_layer.weight.data,
        }
        
        if self.is_factorized:
            weights['hidden_1'] = self.hidden_layer.get_effective_weight()
        else:
            weights['hidden_1'] = self.hidden_layer.weight.data
        
        return weights


# ═══════════════════════════════════════════════════════════════════════════════
# RANK SHOCK INTERVENTION
# ═══════════════════════════════════════════════════════════════════════════════

def apply_rank_shock(model: GrokMLP, target_rank: int, device: str = 'cuda') -> Dict[str, float]:
    """Apply rank shock to hidden layer: truncate SVD to target_rank.
    
    This tests H1 via intervention: if bulk compression is causal, forcing
    low-rank structure mid-training should affect grokking dynamics.
    
    Returns dict with pre/post effective rank for logging.
    """
    if model.is_factorized:
        raise ValueError("Cannot apply rank shock to already-factorized layer")
    
    with torch.no_grad():
        W = model.hidden_layer.weight.data
        
        # Compute SVD
        U, S, Vh = torch.linalg.svd(W, full_matrices=False)
        
        # Compute pre-shock effective rank
        p = S ** 2 / (S ** 2).sum()
        pre_eff_rank = torch.exp(-torch.sum(p * torch.log(p + 1e-10))).item()
        
        # Truncate to target_rank
        S_truncated = S.clone()
        S_truncated[target_rank:] = 0
        
        # Reconstruct
        W_lowrank = U @ torch.diag(S_truncated) @ Vh
        model.hidden_layer.weight.data = W_lowrank
        
        # Compute post-shock effective rank
        p_post = S_truncated ** 2 / (S_truncated ** 2 + 1e-10).sum()
        p_post = p_post[:target_rank]  # Only non-zero
        post_eff_rank = torch.exp(-torch.sum(p_post * torch.log(p_post + 1e-10))).item()
    
    return {
        'pre_shock_eff_rank': pre_eff_rank,
        'post_shock_eff_rank': post_eff_rank,
        'target_rank': target_rank,
        'energy_retained': (S_truncated ** 2).sum().item() / (S ** 2).sum().item()
    }


# ═══════════════════════════════════════════════════════════════════════════════
# SPECTRAL ANALYSIS (from Phase-2, with additions)
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class LayerSpectrum:
    """Spectral data for a single layer."""
    name: str
    eigenvalues: torch.Tensor
    effective_rank: float
    spectral_entropy: float
    top_eigenvalue: float
    spectral_decay: float  # lambda_1 / lambda_k ratio


@dataclass
class SpectralTomography:
    """Full spectral tomography across all layers."""
    layer_spectra: Dict[str, LayerSpectrum]
    global_spectrum: LayerSpectrum
    holographic_deficit: Dict[str, float]  # D_JS(global || layer)
    pairwise_deficit: Dict[str, float]  # D_JS between layer pairs
    entropy_production: Dict[str, float]  # dH/dt
    bulk_compression_ratio: float  # EffRank_hidden / EffRank_input
    entropy_gap: float  # Entropy_input - Entropy_hidden
    is_valid: bool = True


def compute_spectral_entropy(eigenvalues: torch.Tensor) -> float:
    """Compute spectral entropy H = -sum(p_i * log(p_i))."""
    eigenvalues = eigenvalues[eigenvalues > 1e-10]
    if len(eigenvalues) == 0:
        return 0.0
    p = eigenvalues / eigenvalues.sum()
    return -torch.sum(p * torch.log(p)).item()


def compute_effective_rank(eigenvalues: torch.Tensor) -> float:
    """Compute effective rank via participation ratio."""
    eigenvalues = eigenvalues[eigenvalues > 1e-10]
    if len(eigenvalues) == 0:
        return 0.0
    p = eigenvalues / eigenvalues.sum()
    return torch.exp(-torch.sum(p * torch.log(p + 1e-10))).item()


def compute_js_divergence(p: torch.Tensor, q: torch.Tensor) -> float:
    """Compute Jensen-Shannon divergence between two distributions."""
    p = p[p > 1e-10]
    q = q[q > 1e-10]
    
    min_len = min(len(p), len(q))
    if min_len == 0:
        return 0.0
    
    p = p[:min_len]
    q = q[:min_len]
    
    # Normalize
    p = p / p.sum()
    q = q / q.sum()
    
    # Mixture
    m = 0.5 * (p + q)
    
    # KL divergences
    kl_pm = torch.sum(p * torch.log(p / m + 1e-10))
    kl_qm = torch.sum(q * torch.log(q / m + 1e-10))
    
    return (0.5 * (kl_pm + kl_qm)).item()


def compute_layer_spectrum(weight: torch.Tensor, name: str) -> LayerSpectrum:
    """Compute spectral statistics for a single layer weight matrix."""
    # SVD to get singular values (proxy for Fisher eigenvalues)
    _, S, _ = torch.linalg.svd(weight, full_matrices=False)
    eigenvalues = S ** 2  # Squared singular values
    
    eff_rank = compute_effective_rank(eigenvalues)
    entropy = compute_spectral_entropy(eigenvalues)
    top_eig = eigenvalues[0].item() if len(eigenvalues) > 0 else 0.0
    
    # Spectral decay: ratio of top to 10th eigenvalue
    k = min(10, len(eigenvalues))
    decay = (eigenvalues[0] / eigenvalues[k-1]).item() if k > 1 and eigenvalues[k-1] > 1e-10 else 1.0
    
    return LayerSpectrum(
        name=name,
        eigenvalues=eigenvalues,
        effective_rank=eff_rank,
        spectral_entropy=entropy,
        top_eigenvalue=top_eig,
        spectral_decay=decay
    )


def compute_spectral_tomography(
    model: GrokMLP,
    prev_tomography: Optional[SpectralTomography] = None
) -> SpectralTomography:
    """Compute full spectral tomography with bulk crystallization metrics."""
    
    weights = model.get_layer_weights()
    layer_spectra = {}
    
    # Compute per-layer spectra
    for name, W in weights.items():
        layer_spectra[name] = compute_layer_spectrum(W, name)
    
    # Compute global spectrum (concatenate all weights, compute SVD)
    all_weights = torch.cat([W.flatten() for W in weights.values()])
    # Reshape to approximate matrix for SVD
    n = int(np.sqrt(len(all_weights)))
    global_matrix = all_weights[:n*n].reshape(n, n)
    global_spectrum = compute_layer_spectrum(global_matrix, 'global')
    
    # Holographic deficit: D_JS(global || layer)
    holographic_deficit = {}
    for name, layer_spec in layer_spectra.items():
        holographic_deficit[name] = compute_js_divergence(
            global_spectrum.eigenvalues, layer_spec.eigenvalues
        )
    
    # Pairwise deficit between layers
    pairwise_deficit = {}
    layer_names = list(layer_spectra.keys())
    for i, name1 in enumerate(layer_names):
        for name2 in layer_names[i+1:]:
            key = f"{name1}_vs_{name2}"
            pairwise_deficit[key] = compute_js_divergence(
                layer_spectra[name1].eigenvalues,
                layer_spectra[name2].eigenvalues
            )
    
    # Entropy production (if we have previous tomography)
    entropy_production = {}
    if prev_tomography is not None:
        for name, layer_spec in layer_spectra.items():
            if name in prev_tomography.layer_spectra:
                prev_entropy = prev_tomography.layer_spectra[name].spectral_entropy
                entropy_production[name] = layer_spec.spectral_entropy - prev_entropy
        entropy_production['global'] = global_spectrum.spectral_entropy - prev_tomography.global_spectrum.spectral_entropy
    
    # Bulk crystallization metrics
    hidden_eff_rank = layer_spectra['hidden_1'].effective_rank
    input_eff_rank = layer_spectra['input'].effective_rank
    bulk_compression_ratio = hidden_eff_rank / (input_eff_rank + 1e-10)
    
    input_entropy = layer_spectra['input'].spectral_entropy
    hidden_entropy = layer_spectra['hidden_1'].spectral_entropy
    entropy_gap = input_entropy - hidden_entropy
    
    return SpectralTomography(
        layer_spectra=layer_spectra,
        global_spectrum=global_spectrum,
        holographic_deficit=holographic_deficit,
        pairwise_deficit=pairwise_deficit,
        entropy_production=entropy_production,
        bulk_compression_ratio=bulk_compression_ratio,
        entropy_gap=entropy_gap,
        is_valid=True
    )


# ═══════════════════════════════════════════════════════════════════════════════
# EVENT DETECTION
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class EventTracker:
    """Track key events during training."""
    initial_hidden_eff_rank: float = 0.0
    rank_collapse_threshold: float = 0.7  # Fraction of initial rank
    
    epoch_first_rank_collapse: int = -1
    epoch_entropy_prod_peak: Dict[str, int] = field(default_factory=dict)
    max_entropy_prod: Dict[str, float] = field(default_factory=dict)
    grokking_epoch: int = -1
    grokking_threshold: float = 0.99
    
    def update(self, epoch: int, tomography: SpectralTomography, test_acc: float):
        """Update event tracking with current epoch data."""
        
        # Initialize on first call
        if self.initial_hidden_eff_rank == 0.0:
            self.initial_hidden_eff_rank = tomography.layer_spectra['hidden_1'].effective_rank
        
        # Check for rank collapse
        current_eff_rank = tomography.layer_spectra['hidden_1'].effective_rank
        if (self.epoch_first_rank_collapse < 0 and 
            current_eff_rank < self.rank_collapse_threshold * self.initial_hidden_eff_rank):
            self.epoch_first_rank_collapse = epoch
        
        # Track entropy production peaks
        for name, delta in tomography.entropy_production.items():
            abs_delta = abs(delta)
            if name not in self.max_entropy_prod or abs_delta > self.max_entropy_prod[name]:
                self.max_entropy_prod[name] = abs_delta
                self.epoch_entropy_prod_peak[name] = epoch
        
        # Check for grokking
        if self.grokking_epoch < 0 and test_acc >= self.grokking_threshold:
            self.grokking_epoch = epoch
    
    def to_dict(self) -> Dict:
        return {
            'initial_hidden_eff_rank': self.initial_hidden_eff_rank,
            'epoch_first_rank_collapse': self.epoch_first_rank_collapse,
            'grokking_epoch': self.grokking_epoch,
            **{f'epoch_entropy_peak_{k}': v for k, v in self.epoch_entropy_prod_peak.items()},
            **{f'max_entropy_prod_{k}': v for k, v in self.max_entropy_prod.items()},
        }


# ═══════════════════════════════════════════════════════════════════════════════
# CSV LOGGING
# ═══════════════════════════════════════════════════════════════════════════════

class CSVLogger:
    """Log metrics to CSV for meta-analysis."""
    
    def __init__(self, filepath: str):
        self.filepath = filepath
        self.rows = []
        self.fieldnames = set()
    
    def log(self, epoch: int, metrics: Dict):
        """Log a row of metrics."""
        row = {'epoch': epoch, **metrics}
        self.rows.append(row)
        self.fieldnames.update(row.keys())
    
    def save(self):
        """Write all rows to CSV."""
        if not self.rows:
            return
        
        # Sort fieldnames for consistent output
        fieldnames = sorted(self.fieldnames)
        
        with open(self.filepath, 'w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames, extrasaction='ignore')
            writer.writeheader()
            for row in self.rows:
                # Fill missing fields with empty string
                complete_row = {k: row.get(k, '') for k in fieldnames}
                writer.writerow(complete_row)


# ═══════════════════════════════════════════════════════════════════════════════
# TRAINING LOOP
# ═══════════════════════════════════════════════════════════════════════════════

def train_phase3(
    model: GrokMLP,
    train_loader: DataLoader,
    test_loader: DataLoader,
    epochs: int = 15000,
    lr: float = 1e-3,
    weight_decay: float = 1.0,
    device: str = 'cuda',
    tomography_interval: int = 100,
    high_res_start: int = 5000,
    high_res_end: int = 10000,
    high_res_interval: int = 25,
    log_dir: str = 'logs/phase3',
    csv_path: str = None,
    rank_shock_epoch: int = -1,
    rank_shock_r: int = 20,
    grokking_threshold: float = 0.99,
) -> Tuple[Dict, EventTracker]:
    """
    Phase-3 training loop with spectral tomography and event detection.
    
    Predictions (H1 - Bulk crystallization is causal):
    - r=20 factorized should reduce grokking epoch vs full-rank
    - r=10 likely fails or severely delays grokking (under-capacity)
    
    Predictions (H3 - Early warning):
    - Output entropy-production peak should precede grokking
    """
    
    model = model.to(device)
    optimizer = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=weight_decay)
    criterion = nn.CrossEntropyLoss()
    
    # Setup logging
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    run_dir = os.path.join(log_dir, f"run_{timestamp}")
    os.makedirs(run_dir, exist_ok=True)
    writer = SummaryWriter(run_dir)
    
    if csv_path is None:
        csv_path = os.path.join(run_dir, "metrics.csv")
    csv_logger = CSVLogger(csv_path)
    
    # Tracking
    event_tracker = EventTracker(grokking_threshold=grokking_threshold)
    prev_tomography = None
    history = {'train_loss': [], 'train_acc': [], 'test_acc': [], 'epochs': []}
    rank_shock_applied = False
    
    print(f"Training for {epochs} epochs...")
    print(f"Factorized: {model.is_factorized}, Hidden rank: {model.hidden_rank}")
    print(f"Rank shock: epoch={rank_shock_epoch}, r={rank_shock_r}")
    print("-" * 70)
    
    for epoch in range(1, epochs + 1):
        # === RANK SHOCK INTERVENTION ===
        if rank_shock_epoch > 0 and epoch == rank_shock_epoch and not rank_shock_applied:
            print(f"\n*** APPLYING RANK SHOCK at epoch {epoch} ***")
            shock_info = apply_rank_shock(model, rank_shock_r, device)
            print(f"  Pre-shock eff-rank: {shock_info['pre_shock_eff_rank']:.2f}")
            print(f"  Post-shock eff-rank: {shock_info['post_shock_eff_rank']:.2f}")
            print(f"  Energy retained: {shock_info['energy_retained']:.4f}")
            writer.add_scalar('Intervention/PreShockEffRank', shock_info['pre_shock_eff_rank'], epoch)
            writer.add_scalar('Intervention/PostShockEffRank', shock_info['post_shock_eff_rank'], epoch)
            writer.add_scalar('Intervention/EnergyRetained', shock_info['energy_retained'], epoch)
            rank_shock_applied = True
        
        # === TRAINING STEP ===
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
            
            total_loss += loss.item() * x.size(0)
            correct += (logits.argmax(dim=1) == y).sum().item()
            total += x.size(0)
        
        train_loss = total_loss / total
        train_acc = correct / total
        
        # === EVALUATION ===
        model.eval()
        test_correct = 0
        test_total = 0
        with torch.no_grad():
            for x, y in test_loader:
                x, y = x.to(device), y.to(device)
                logits = model(x)
                test_correct += (logits.argmax(dim=1) == y).sum().item()
                test_total += x.size(0)
        test_acc = test_correct / test_total
        
        # Record history
        history['train_loss'].append(train_loss)
        history['train_acc'].append(train_acc)
        history['test_acc'].append(test_acc)
        history['epochs'].append(epoch)
        
        # Basic logging
        writer.add_scalar('Performance/TrainLoss', train_loss, epoch)
        writer.add_scalar('Performance/TrainAcc', train_acc * 100, epoch)
        writer.add_scalar('Performance/TestAcc', test_acc * 100, epoch)
        
        # === SPECTRAL TOMOGRAPHY ===
        # Determine if we should compute tomography this epoch
        in_high_res = high_res_start <= epoch <= high_res_end
        interval = high_res_interval if in_high_res else tomography_interval
        
        if epoch % interval == 0 or epoch == 1:
            tomography = compute_spectral_tomography(model, prev_tomography)
            event_tracker.update(epoch, tomography, test_acc)
            
            # Log per-layer metrics
            for name, layer_spec in tomography.layer_spectra.items():
                writer.add_scalar(f'Tomography/EffRank/{name}', layer_spec.effective_rank, epoch)
                writer.add_scalar(f'Tomography/Entropy/{name}', layer_spec.spectral_entropy, epoch)
                writer.add_scalar(f'Tomography/TopEig/{name}', layer_spec.top_eigenvalue, epoch)
            
            # Global
            writer.add_scalar('Tomography/EffRank/global', tomography.global_spectrum.effective_rank, epoch)
            writer.add_scalar('Tomography/Entropy/global', tomography.global_spectrum.spectral_entropy, epoch)
            
            # Holographic deficit
            for name, deficit in tomography.holographic_deficit.items():
                writer.add_scalar(f'Tomography/HolographicDeficit/{name}', deficit, epoch)
            
            # Pairwise deficit
            for name, deficit in tomography.pairwise_deficit.items():
                writer.add_scalar(f'Tomography/PairwiseDeficit/{name}', deficit, epoch)
            
            # Entropy production
            for name, delta in tomography.entropy_production.items():
                writer.add_scalar(f'Tomography/EntropyProduction/{name}', delta, epoch)
            
            # Bulk crystallization metrics
            writer.add_scalar('BulkCrystallization/CompressionRatio', tomography.bulk_compression_ratio, epoch)
            writer.add_scalar('BulkCrystallization/EntropyGap', tomography.entropy_gap, epoch)
            
            # CSV logging
            csv_row = {
                'train_loss': train_loss,
                'train_acc': train_acc,
                'test_acc': test_acc,
                'global_eff_rank': tomography.global_spectrum.effective_rank,
                'global_entropy': tomography.global_spectrum.spectral_entropy,
                'bulk_compression_ratio': tomography.bulk_compression_ratio,
                'entropy_gap': tomography.entropy_gap,
            }
            for name, layer_spec in tomography.layer_spectra.items():
                csv_row[f'{name}_eff_rank'] = layer_spec.effective_rank
                csv_row[f'{name}_entropy'] = layer_spec.spectral_entropy
            for name, deficit in tomography.holographic_deficit.items():
                csv_row[f'deficit_{name}'] = deficit
            for name, delta in tomography.entropy_production.items():
                csv_row[f'entropy_prod_{name}'] = delta
            
            csv_logger.log(epoch, csv_row)
            prev_tomography = tomography
        
        # Console output
        if epoch % 500 == 0 or epoch == 1:
            msg = f"Epoch {epoch:5d}: loss={train_loss:.4f}, train={train_acc*100:.1f}%, test={test_acc*100:.1f}%"
            if prev_tomography:
                h_rank = prev_tomography.layer_spectra['hidden_1'].effective_rank
                msg += f" | hidden_rank={h_rank:.1f}"
            print(msg)
        
        # Early stopping on grokking
        if test_acc >= grokking_threshold:
            print(f"\n*** GROKKING ACHIEVED at epoch {epoch}! ***")
            break
    
    # Save CSV
    csv_logger.save()
    print(f"\nMetrics saved to {csv_path}")
    
    # Log final events
    events = event_tracker.to_dict()
    print(f"\nEvent Summary:")
    print(f"  Initial hidden eff-rank: {events['initial_hidden_eff_rank']:.2f}")
    print(f"  First rank collapse (70%): epoch {events['epoch_first_rank_collapse']}")
    print(f"  Grokking epoch: {events['grokking_epoch']}")
    for name in ['input', 'hidden_1', 'output', 'global']:
        if f'epoch_entropy_peak_{name}' in events:
            print(f"  Entropy prod peak ({name}): epoch {events[f'epoch_entropy_peak_{name}']}")
    
    writer.close()
    return history, event_tracker


# ═══════════════════════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════════════════════

def main():
    parser = argparse.ArgumentParser(description="SGC Phase-3: Causal Validation of Bulk Crystallization")
    
    # Task selection
    parser.add_argument('--task', type=str, default='add', choices=['add', 'mul'],
                        help='Task: add (modular addition) or mul (modular multiplication)')
    parser.add_argument('--p', type=int, default=97, help='Prime for modular arithmetic')
    
    # Architecture
    parser.add_argument('--hidden_dim', type=int, default=128, help='MLP hidden dimension')
    parser.add_argument('--hidden_rank', type=int, default=None,
                        help='Factorized hidden layer rank (None = full rank). '
                             'H1 prediction: r=20 should accelerate grokking, r=10 may fail.')
    
    # Training
    parser.add_argument('--epochs', type=int, default=15000, help='Max training epochs')
    parser.add_argument('--lr', type=float, default=1e-3, help='Learning rate')
    parser.add_argument('--weight_decay', type=float, default=1.0, help='Weight decay')
    parser.add_argument('--train_fraction', type=float, default=0.3, help='Fraction for training')
    parser.add_argument('--batch_size', type=int, default=512, help='Batch size')
    parser.add_argument('--grokking_threshold', type=float, default=0.99, help='Test acc for grokking')
    
    # Rank shock intervention
    parser.add_argument('--rank_shock_epoch', type=int, default=-1,
                        help='Epoch to apply rank shock (-1 = disabled). '
                             'H1 test: shock at 5000 or 7500 should affect grokking.')
    parser.add_argument('--rank_shock_r', type=int, default=20, help='Target rank for shock')
    
    # Logging
    parser.add_argument('--tomography_interval', type=int, default=100, help='Tomography interval')
    parser.add_argument('--high_res_start', type=int, default=5000, help='High-res window start')
    parser.add_argument('--high_res_end', type=int, default=10000, help='High-res window end')
    parser.add_argument('--high_res_interval', type=int, default=25, help='High-res interval')
    parser.add_argument('--log_dir', type=str, default='logs/phase3', help='TensorBoard log directory')
    
    # Misc
    parser.add_argument('--device', type=str, default='cuda' if torch.cuda.is_available() else 'cpu')
    parser.add_argument('--seed', type=int, default=42)
    
    args = parser.parse_args()
    
    print("=" * 70)
    print("SGC PHASE-3: CAUSAL VALIDATION OF BULK CRYSTALLIZATION")
    print("=" * 70)
    
    # GPU info
    if torch.cuda.is_available():
        gpu_name = torch.cuda.get_device_name(0)
        print(f"\nGPU: {gpu_name}")
        args.device = 'cuda'
    else:
        print("\nWARNING: No GPU detected")
    
    print(f"\nConfiguration:")
    print(f"  Task: {args.task} mod {args.p}")
    print(f"  Hidden dim: {args.hidden_dim}, Hidden rank: {args.hidden_rank or 'full'}")
    print(f"  Epochs: {args.epochs}, LR: {args.lr}, WD: {args.weight_decay}")
    print(f"  Rank shock: epoch={args.rank_shock_epoch}, r={args.rank_shock_r}")
    print(f"  Seed: {args.seed}")
    print()
    
    # Set seed
    torch.manual_seed(args.seed)
    np.random.seed(args.seed)
    
    # Create datasets
    if args.task == 'add':
        train_dataset = ModularAdditionDataset(args.p, train=True, train_fraction=args.train_fraction, seed=args.seed)
        test_dataset = ModularAdditionDataset(args.p, train=False, train_fraction=args.train_fraction, seed=args.seed)
    elif args.task == 'mul':
        train_dataset = ModularMultiplicationDataset(args.p, train=True, train_fraction=args.train_fraction, seed=args.seed)
        test_dataset = ModularMultiplicationDataset(args.p, train=False, train_fraction=args.train_fraction, seed=args.seed)
    
    print(f"Dataset: {len(train_dataset)} train, {len(test_dataset)} test")
    
    train_loader = DataLoader(train_dataset, batch_size=args.batch_size, shuffle=True)
    test_loader = DataLoader(test_dataset, batch_size=args.batch_size, shuffle=False)
    
    # Create model
    model = GrokMLP(args.p, args.hidden_dim, hidden_rank=args.hidden_rank)
    n_params = sum(p.numel() for p in model.parameters())
    print(f"Model parameters: {n_params:,}")
    print()
    
    # Train
    history, events = train_phase3(
        model, train_loader, test_loader,
        epochs=args.epochs,
        lr=args.lr,
        weight_decay=args.weight_decay,
        device=args.device,
        tomography_interval=args.tomography_interval,
        high_res_start=args.high_res_start,
        high_res_end=args.high_res_end,
        high_res_interval=args.high_res_interval,
        log_dir=args.log_dir,
        rank_shock_epoch=args.rank_shock_epoch,
        rank_shock_r=args.rank_shock_r,
        grokking_threshold=args.grokking_threshold,
    )
    
    print("\n" + "=" * 70)
    print("EXPERIMENT COMPLETE")
    print("=" * 70)


if __name__ == "__main__":
    main()
