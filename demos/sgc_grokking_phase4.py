#!/usr/bin/env python3
"""
SGC Phase-4: THRML-Prototype Interventions for Grokking
========================================================

Phase-3 discovered: Grokking requires the PROCESS of compression, not just low rank.
Factorized layers collapse immediately and never generalize.

Phase-4 objective: Test adaptive interventions that could translate to THRML/SNN:
  (A) Rank shock at different epochs (5000 vs 7500) - causal timing test
  (B) Annealed heat/quench - THRML-style β(t) scheduling prototype

KEY INSIGHT: Heat/quench uses spectral entropy as the trigger signal, making this
a closed-loop control system where the "thermodynamic state" drives scheduling.

PREDICTIONS:
  - Rank shock at epoch 5000 (pre-compression): Likely PREVENTS grokking
  - Rank shock at epoch 7500 (during compression): Could accelerate OR break
  - Heat/quench: Should accelerate grokking by explicit exploration→consolidation

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
# DATASETS: Multi-task support (from Phase-3)
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
    """Dataset for (a * b) mod p task (excludes zero for group structure)."""
    
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
# ARCHITECTURE
# ═══════════════════════════════════════════════════════════════════════════════

class GrokMLP(nn.Module):
    """MLP for grokking experiments (full rank only for Phase-4)."""
    
    def __init__(self, p: int = 97, hidden_dim: int = 128):
        super().__init__()
        self.p = p
        self.hidden_dim = hidden_dim
        
        self.input_layer = nn.Linear(2 * p, hidden_dim)
        self.hidden_layer = nn.Linear(hidden_dim, hidden_dim)
        self.output_layer = nn.Linear(hidden_dim, p)
    
    def forward(self, x: torch.Tensor) -> torch.Tensor:
        x = F.relu(self.input_layer(x))
        x = F.relu(self.hidden_layer(x))
        return self.output_layer(x)
    
    def get_layer_weights(self) -> Dict[str, torch.Tensor]:
        """Return weight matrices for each layer."""
        return {
            'input': self.input_layer.weight.data,
            'hidden_1': self.hidden_layer.weight.data,
            'output': self.output_layer.weight.data,
        }


# ═══════════════════════════════════════════════════════════════════════════════
# RANK SHOCK INTERVENTION
# ═══════════════════════════════════════════════════════════════════════════════

def apply_rank_shock(model: GrokMLP, target_rank: int, device: str = 'cuda') -> Dict[str, float]:
    """Apply rank shock to hidden layer: truncate SVD to target_rank."""
    with torch.no_grad():
        W = model.hidden_layer.weight.data
        
        U, S, Vh = torch.linalg.svd(W, full_matrices=False)
        
        # Pre-shock effective rank
        p = S ** 2 / (S ** 2).sum()
        pre_eff_rank = torch.exp(-torch.sum(p * torch.log(p + 1e-10))).item()
        
        # Truncate
        S_truncated = S.clone()
        S_truncated[target_rank:] = 0
        
        # Reconstruct
        W_lowrank = U @ torch.diag(S_truncated) @ Vh
        model.hidden_layer.weight.data = W_lowrank
        
        # Post-shock effective rank
        p_post = S_truncated ** 2 / (S_truncated ** 2 + 1e-10).sum()
        p_post = p_post[:target_rank]
        post_eff_rank = torch.exp(-torch.sum(p_post * torch.log(p_post + 1e-10))).item()
    
    return {
        'pre_shock_eff_rank': pre_eff_rank,
        'post_shock_eff_rank': post_eff_rank,
        'target_rank': target_rank,
        'energy_retained': (S_truncated ** 2).sum().item() / (S ** 2).sum().item()
    }


# ═══════════════════════════════════════════════════════════════════════════════
# HEAT/QUENCH CONTROLLER (THRML PROTOTYPE)
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class HeatQuenchController:
    """
    THRML-style temperature controller for grokking.
    
    Uses hidden-layer spectral entropy as the "temperature" signal.
    Heat phase: Low weight decay + noise injection (exploration)
    Quench phase: High weight decay (consolidation)
    
    Transition trigger: Entropy drops below threshold OR fixed epoch schedule.
    """
    
    # Weight decay bounds
    wd_heat: float = 0.1  # Low WD during heat phase
    wd_quench: float = 2.0  # High WD during quench phase
    wd_baseline: float = 1.0  # Normal WD
    
    # Noise injection during heat
    noise_scale: float = 0.01  # Isotropic noise magnitude
    
    # Trigger mode
    trigger_mode: str = 'entropy'  # 'entropy', 'epoch', or 'hybrid'
    
    # Entropy-based trigger
    entropy_heat_threshold: float = 3.8  # Start heat if entropy > this
    entropy_quench_threshold: float = 3.2  # Quench if entropy < this
    
    # Epoch-based trigger (backup)
    heat_start_epoch: int = 1000
    heat_end_epoch: int = 3000
    quench_start_epoch: int = 5000
    
    # State tracking
    current_phase: str = 'baseline'  # 'heat', 'quench', or 'baseline'
    phase_history: List[Tuple[int, str]] = field(default_factory=list)
    
    def get_weight_decay(self, epoch: int, hidden_entropy: float) -> Tuple[float, str]:
        """Determine current weight decay based on phase."""
        prev_phase = self.current_phase
        
        if self.trigger_mode == 'entropy':
            # Pure entropy-triggered
            if hidden_entropy > self.entropy_heat_threshold:
                self.current_phase = 'heat'
            elif hidden_entropy < self.entropy_quench_threshold:
                self.current_phase = 'quench'
            else:
                self.current_phase = 'baseline'
                
        elif self.trigger_mode == 'epoch':
            # Fixed schedule
            if self.heat_start_epoch <= epoch < self.heat_end_epoch:
                self.current_phase = 'heat'
            elif epoch >= self.quench_start_epoch:
                self.current_phase = 'quench'
            else:
                self.current_phase = 'baseline'
                
        elif self.trigger_mode == 'hybrid':
            # Epoch triggers, entropy confirms
            if self.heat_start_epoch <= epoch < self.heat_end_epoch and hidden_entropy > self.entropy_heat_threshold * 0.9:
                self.current_phase = 'heat'
            elif epoch >= self.quench_start_epoch or hidden_entropy < self.entropy_quench_threshold:
                self.current_phase = 'quench'
            else:
                self.current_phase = 'baseline'
        
        # Track phase transitions
        if self.current_phase != prev_phase:
            self.phase_history.append((epoch, self.current_phase))
        
        # Return weight decay
        if self.current_phase == 'heat':
            return self.wd_heat, self.current_phase
        elif self.current_phase == 'quench':
            return self.wd_quench, self.current_phase
        else:
            return self.wd_baseline, self.current_phase
    
    def inject_noise(self, model: GrokMLP, device: str = 'cuda'):
        """Inject isotropic noise during heat phase."""
        if self.current_phase != 'heat':
            return
        
        with torch.no_grad():
            for param in model.parameters():
                noise = torch.randn_like(param) * self.noise_scale
                param.add_(noise)
    
    def get_summary(self) -> Dict:
        return {
            'trigger_mode': self.trigger_mode,
            'phase_transitions': len(self.phase_history),
            'phases': self.phase_history[-5:] if self.phase_history else [],
        }


# ═══════════════════════════════════════════════════════════════════════════════
# SPECTRAL ANALYSIS
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class LayerSpectrum:
    name: str
    eigenvalues: torch.Tensor
    effective_rank: float
    spectral_entropy: float
    top_eigenvalue: float
    spectral_decay: float


@dataclass
class SpectralTomography:
    layer_spectra: Dict[str, LayerSpectrum]
    global_spectrum: LayerSpectrum
    holographic_deficit: Dict[str, float]
    pairwise_deficit: Dict[str, float]
    entropy_production: Dict[str, float]
    bulk_compression_ratio: float
    entropy_gap: float
    is_valid: bool = True


def compute_spectral_entropy(eigenvalues: torch.Tensor) -> float:
    eigenvalues = eigenvalues[eigenvalues > 1e-10]
    if len(eigenvalues) == 0:
        return 0.0
    p = eigenvalues / eigenvalues.sum()
    return -torch.sum(p * torch.log(p)).item()


def compute_effective_rank(eigenvalues: torch.Tensor) -> float:
    eigenvalues = eigenvalues[eigenvalues > 1e-10]
    if len(eigenvalues) == 0:
        return 0.0
    p = eigenvalues / eigenvalues.sum()
    return torch.exp(-torch.sum(p * torch.log(p + 1e-10))).item()


def compute_js_divergence(p: torch.Tensor, q: torch.Tensor) -> float:
    p = p[p > 1e-10]
    q = q[q > 1e-10]
    
    min_len = min(len(p), len(q))
    if min_len == 0:
        return 0.0
    
    p = p[:min_len]
    q = q[:min_len]
    
    p = p / p.sum()
    q = q / q.sum()
    m = 0.5 * (p + q)
    
    kl_pm = torch.sum(p * torch.log(p / m + 1e-10))
    kl_qm = torch.sum(q * torch.log(q / m + 1e-10))
    
    return (0.5 * (kl_pm + kl_qm)).item()


def compute_layer_spectrum(weight: torch.Tensor, name: str) -> LayerSpectrum:
    _, S, _ = torch.linalg.svd(weight, full_matrices=False)
    eigenvalues = S ** 2
    
    eff_rank = compute_effective_rank(eigenvalues)
    entropy = compute_spectral_entropy(eigenvalues)
    top_eig = eigenvalues[0].item() if len(eigenvalues) > 0 else 0.0
    
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
    weights = model.get_layer_weights()
    layer_spectra = {}
    
    for name, W in weights.items():
        layer_spectra[name] = compute_layer_spectrum(W, name)
    
    # Global spectrum
    all_weights = torch.cat([W.flatten() for W in weights.values()])
    n = int(np.sqrt(len(all_weights)))
    global_matrix = all_weights[:n*n].reshape(n, n)
    global_spectrum = compute_layer_spectrum(global_matrix, 'global')
    
    # Holographic deficit
    holographic_deficit = {}
    for name, layer_spec in layer_spectra.items():
        holographic_deficit[name] = compute_js_divergence(
            global_spectrum.eigenvalues, layer_spec.eigenvalues
        )
    
    # Pairwise deficit
    pairwise_deficit = {}
    layer_names = list(layer_spectra.keys())
    for i, name1 in enumerate(layer_names):
        for name2 in layer_names[i+1:]:
            key = f"{name1}_vs_{name2}"
            pairwise_deficit[key] = compute_js_divergence(
                layer_spectra[name1].eigenvalues,
                layer_spectra[name2].eigenvalues
            )
    
    # Entropy production
    entropy_production = {}
    if prev_tomography is not None:
        for name, layer_spec in layer_spectra.items():
            if name in prev_tomography.layer_spectra:
                prev_entropy = prev_tomography.layer_spectra[name].spectral_entropy
                entropy_production[name] = layer_spec.spectral_entropy - prev_entropy
        entropy_production['global'] = global_spectrum.spectral_entropy - prev_tomography.global_spectrum.spectral_entropy
    
    # Bulk metrics
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
    initial_hidden_eff_rank: float = 0.0
    rank_collapse_threshold: float = 0.7
    
    epoch_first_rank_collapse: int = -1
    epoch_entropy_prod_peak: Dict[str, int] = field(default_factory=dict)
    max_entropy_prod: Dict[str, float] = field(default_factory=dict)
    grokking_epoch: int = -1
    grokking_threshold: float = 0.99
    
    def update(self, epoch: int, tomography: SpectralTomography, test_acc: float):
        if self.initial_hidden_eff_rank == 0.0:
            self.initial_hidden_eff_rank = tomography.layer_spectra['hidden_1'].effective_rank
        
        current_eff_rank = tomography.layer_spectra['hidden_1'].effective_rank
        if (self.epoch_first_rank_collapse < 0 and 
            current_eff_rank < self.rank_collapse_threshold * self.initial_hidden_eff_rank):
            self.epoch_first_rank_collapse = epoch
        
        for name, delta in tomography.entropy_production.items():
            abs_delta = abs(delta)
            if name not in self.max_entropy_prod or abs_delta > self.max_entropy_prod[name]:
                self.max_entropy_prod[name] = abs_delta
                self.epoch_entropy_prod_peak[name] = epoch
        
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
    def __init__(self, filepath: str):
        self.filepath = filepath
        self.rows = []
        self.fieldnames = set()
    
    def log(self, epoch: int, metrics: Dict):
        row = {'epoch': epoch, **metrics}
        self.rows.append(row)
        self.fieldnames.update(row.keys())
    
    def save(self):
        if not self.rows:
            return
        
        fieldnames = sorted(self.fieldnames)
        
        with open(self.filepath, 'w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames, extrasaction='ignore')
            writer.writeheader()
            for row in self.rows:
                complete_row = {k: row.get(k, '') for k in fieldnames}
                writer.writerow(complete_row)


# ═══════════════════════════════════════════════════════════════════════════════
# TRAINING LOOP
# ═══════════════════════════════════════════════════════════════════════════════

def train_phase4(
    model: GrokMLP,
    train_loader: DataLoader,
    test_loader: DataLoader,
    epochs: int = 15000,
    lr: float = 1e-3,
    weight_decay: float = 1.0,
    device: str = 'cuda',
    tomography_interval: int = 100,
    high_res_start: int = 4000,
    high_res_end: int = 10000,
    high_res_interval: int = 25,
    log_dir: str = 'logs/phase4',
    csv_path: str = None,
    rank_shock_epoch: int = -1,
    rank_shock_r: int = 20,
    grokking_threshold: float = 0.99,
    heat_quench_controller: Optional[HeatQuenchController] = None,
) -> Tuple[Dict, EventTracker]:
    """
    Phase-4 training loop with rank shock and heat/quench interventions.
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
    
    # Heat/quench state
    hq_enabled = heat_quench_controller is not None
    current_hidden_entropy = 4.0  # Initial estimate
    
    print(f"Training for {epochs} epochs...")
    print(f"Rank shock: epoch={rank_shock_epoch}, r={rank_shock_r}")
    print(f"Heat/Quench: {'ENABLED (' + heat_quench_controller.trigger_mode + ')' if hq_enabled else 'DISABLED'}")
    print("-" * 70)
    
    for epoch in range(1, epochs + 1):
        # === HEAT/QUENCH CONTROL ===
        if hq_enabled:
            new_wd, phase = heat_quench_controller.get_weight_decay(epoch, current_hidden_entropy)
            
            # Update optimizer weight decay
            for param_group in optimizer.param_groups:
                param_group['weight_decay'] = new_wd
            
            # Inject noise during heat phase
            if phase == 'heat':
                heat_quench_controller.inject_noise(model, device)
            
            writer.add_scalar('HeatQuench/WeightDecay', new_wd, epoch)
            writer.add_scalar('HeatQuench/Phase', {'baseline': 0, 'heat': 1, 'quench': 2}[phase], epoch)
        
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
        in_high_res = high_res_start <= epoch <= high_res_end
        interval = high_res_interval if in_high_res else tomography_interval
        
        if epoch % interval == 0 or epoch == 1:
            tomography = compute_spectral_tomography(model, prev_tomography)
            event_tracker.update(epoch, tomography, test_acc)
            
            # Update entropy for heat/quench controller
            current_hidden_entropy = tomography.layer_spectra['hidden_1'].spectral_entropy
            
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
            
            if hq_enabled:
                csv_row['hq_phase'] = heat_quench_controller.current_phase
                csv_row['hq_wd'] = new_wd
            
            csv_logger.log(epoch, csv_row)
            prev_tomography = tomography
        
        # Console output
        if epoch % 500 == 0 or epoch == 1:
            msg = f"Epoch {epoch:5d}: loss={train_loss:.4f}, train={train_acc*100:.1f}%, test={test_acc*100:.1f}%"
            if prev_tomography:
                h_rank = prev_tomography.layer_spectra['hidden_1'].effective_rank
                msg += f" | h_rank={h_rank:.1f}"
            if hq_enabled:
                msg += f" | phase={heat_quench_controller.current_phase}"
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
    
    if hq_enabled:
        hq_summary = heat_quench_controller.get_summary()
        print(f"\nHeat/Quench Summary:")
        print(f"  Trigger mode: {hq_summary['trigger_mode']}")
        print(f"  Phase transitions: {hq_summary['phase_transitions']}")
        for epoch, phase in hq_summary['phases']:
            print(f"    Epoch {epoch}: -> {phase}")
    
    writer.close()
    return history, event_tracker


# ═══════════════════════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════════════════════

def main():
    parser = argparse.ArgumentParser(description="SGC Phase-4: THRML-Prototype Interventions")
    
    # Task
    parser.add_argument('--task', type=str, default='add', choices=['add', 'mul'])
    parser.add_argument('--p', type=int, default=97)
    
    # Architecture
    parser.add_argument('--hidden_dim', type=int, default=128)
    
    # Training
    parser.add_argument('--epochs', type=int, default=15000)
    parser.add_argument('--lr', type=float, default=1e-3)
    parser.add_argument('--weight_decay', type=float, default=1.0)
    parser.add_argument('--train_fraction', type=float, default=0.3)
    parser.add_argument('--batch_size', type=int, default=512)
    parser.add_argument('--grokking_threshold', type=float, default=0.99)
    
    # Rank shock
    parser.add_argument('--rank_shock_epoch', type=int, default=-1)
    parser.add_argument('--rank_shock_r', type=int, default=20)
    
    # Heat/Quench
    parser.add_argument('--heat_quench', action='store_true', help='Enable heat/quench control')
    parser.add_argument('--hq_trigger', type=str, default='entropy', choices=['entropy', 'epoch', 'hybrid'])
    parser.add_argument('--hq_wd_heat', type=float, default=0.1)
    parser.add_argument('--hq_wd_quench', type=float, default=2.0)
    parser.add_argument('--hq_noise_scale', type=float, default=0.01)
    parser.add_argument('--hq_entropy_heat', type=float, default=3.8)
    parser.add_argument('--hq_entropy_quench', type=float, default=3.2)
    parser.add_argument('--hq_heat_start', type=int, default=1000)
    parser.add_argument('--hq_heat_end', type=int, default=3000)
    parser.add_argument('--hq_quench_start', type=int, default=5000)
    
    # Logging
    parser.add_argument('--tomography_interval', type=int, default=100)
    parser.add_argument('--high_res_start', type=int, default=4000)
    parser.add_argument('--high_res_end', type=int, default=10000)
    parser.add_argument('--high_res_interval', type=int, default=25)
    parser.add_argument('--log_dir', type=str, default='logs/phase4')
    
    # Misc
    parser.add_argument('--device', type=str, default='cuda' if torch.cuda.is_available() else 'cpu')
    parser.add_argument('--seed', type=int, default=42)
    
    args = parser.parse_args()
    
    print("=" * 70)
    print("SGC PHASE-4: THRML-PROTOTYPE INTERVENTIONS")
    print("=" * 70)
    
    if torch.cuda.is_available():
        gpu_name = torch.cuda.get_device_name(0)
        print(f"\nGPU: {gpu_name}")
        args.device = 'cuda'
    else:
        print("\nWARNING: No GPU detected")
    
    print(f"\nConfiguration:")
    print(f"  Task: {args.task} mod {args.p}")
    print(f"  Hidden dim: {args.hidden_dim}")
    print(f"  Epochs: {args.epochs}, LR: {args.lr}, WD: {args.weight_decay}")
    print(f"  Rank shock: epoch={args.rank_shock_epoch}, r={args.rank_shock_r}")
    print(f"  Heat/Quench: {'ENABLED' if args.heat_quench else 'DISABLED'}")
    if args.heat_quench:
        print(f"    Trigger: {args.hq_trigger}")
        print(f"    WD heat={args.hq_wd_heat}, quench={args.hq_wd_quench}")
        print(f"    Entropy thresholds: heat>{args.hq_entropy_heat}, quench<{args.hq_entropy_quench}")
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
    model = GrokMLP(args.p, args.hidden_dim)
    n_params = sum(p.numel() for p in model.parameters())
    print(f"Model parameters: {n_params:,}")
    print()
    
    # Heat/Quench controller
    hq_controller = None
    if args.heat_quench:
        hq_controller = HeatQuenchController(
            wd_heat=args.hq_wd_heat,
            wd_quench=args.hq_wd_quench,
            wd_baseline=args.weight_decay,
            noise_scale=args.hq_noise_scale,
            trigger_mode=args.hq_trigger,
            entropy_heat_threshold=args.hq_entropy_heat,
            entropy_quench_threshold=args.hq_entropy_quench,
            heat_start_epoch=args.hq_heat_start,
            heat_end_epoch=args.hq_heat_end,
            quench_start_epoch=args.hq_quench_start,
        )
    
    # Train
    history, events = train_phase4(
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
        heat_quench_controller=hq_controller,
    )
    
    print("\n" + "=" * 70)
    print("EXPERIMENT COMPLETE")
    print("=" * 70)


if __name__ == "__main__":
    main()
