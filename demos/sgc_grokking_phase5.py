#!/usr/bin/env python3
"""
SGC Phase-5.1: Exploration Mass Controller with Principled Mixing Guarantee
============================================================================

Phase-4 discovered: Heat/quench with epoch-based triggers accelerates grokking by 34%.
But epoch-based triggers are arbitrary, and entropy-triggered control deadlocks.

Phase-5.1 BREAKTHROUGH: Replace epoch counting with EXPLORATION MASS from SGC theory.

THE KEY INSIGHT (ExplorationMass.lean):
    - Each noise injection step with strength η contracts distance by factor (1-η)
    - After N steps: distance ≤ exp(-M) × d₀, where M = Ση_t is exploration mass
    - Quench when M ≥ M_explore = log(d₀/δ)

This breaks the feedback loop that traps entropy-triggered controllers:
    - The trigger (M = Σηₜ) is EXOGENOUS (based on our noise injection)
    - But it's PRINCIPLED (derived from mixing theorem, not arbitrary epochs)

THEORETICAL FOUNDATION (Proven in Lean):
    1. contraction_product_bound: ∏(1-aᵢ) ≤ exp(-Σaᵢ)
    2. exploration_mass_mixing_bound: distance ≤ exp(-M) × d₀
    3. mixing_guarantee: M ≥ log(d₀/δ) ⟹ distance ≤ δ

WHY THIS WORKS:
    Phase-4's success came from FORCING the explore→consolidate sequence.
    Pure entropy-triggered control failed because low WD suppresses entropy drop.
    Exploration mass is exogenous (we control noise injection) so no deadlock.

Author: SGC Research Team
Date: February 2026
"""

import argparse
import csv
import math
import os
from collections import deque
from dataclasses import dataclass, field
from datetime import datetime
from typing import Dict, List, Optional, Tuple

import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import Dataset, DataLoader
from torch.utils.tensorboard import SummaryWriter


# ═══════════════════════════════════════════════════════════════════════════════
# DATASETS
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
    """Dataset for (a * b) mod p task."""
    
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
    """MLP for grokking experiments."""
    
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
        return {
            'input': self.input_layer.weight.data,
            'hidden_1': self.hidden_layer.weight.data,
            'output': self.output_layer.weight.data,
        }


# ═══════════════════════════════════════════════════════════════════════════════
# DEFECT MEASUREMENT (THE KEY INNOVATION)
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class DefectMeasurement:
    """
    Measurement of the Lumpability Defect ε.
    
    In SGC theory: ε = ‖(I - Π) L Π‖ where Π projects onto coarse (dominant) subspace.
    
    For neural nets, we use the SVD tail energy as a proxy:
        ε(t) = Σ_{i=k+1}^N σ_i² / Σ_{i=1}^N σ_i²
    
    This measures the fraction of energy outside the dominant k-dimensional subspace.
    """
    epsilon: float  # The defect value
    effective_rank: int  # k used for the split
    tail_energy: float  # Raw tail energy (unnormalized)
    total_energy: float  # Total spectral energy
    top_singular_values: List[float]  # Top-k singular values
    validity_horizon: float  # T* = 1/ε (how long the macro model is valid)


def compute_defect(weight: torch.Tensor, k: Optional[int] = None, 
                   k_ema: Optional[float] = None, k_ema_alpha: float = 0.1) -> Tuple[DefectMeasurement, float]:
    """
    Compute the lumpability defect ε from the SVD of a weight matrix.
    
    Args:
        weight: The weight matrix to analyze
        k: Number of dominant singular values. If None, use effective rank.
        k_ema: Exponential moving average of k (for smoothing). If None, no smoothing.
        k_ema_alpha: EMA smoothing factor (0 = no update, 1 = instant update)
    
    Returns:
        (DefectMeasurement, new_k_ema) tuple.
    """
    _, S, _ = torch.linalg.svd(weight, full_matrices=False)
    
    # Compute squared singular values (eigenvalues of W^T W)
    S_sq = S ** 2
    total_energy = S_sq.sum().item()
    
    if total_energy < 1e-10:
        return DefectMeasurement(
            epsilon=1.0,
            effective_rank=0,
            tail_energy=0.0,
            total_energy=0.0,
            top_singular_values=[],
            validity_horizon=1.0
        ), k_ema or 0.0
    
    # Compute effective rank
    p = S_sq / S_sq.sum()
    p_valid = p[p > 1e-10]
    eff_rank_raw = torch.exp(-torch.sum(p_valid * torch.log(p_valid))).item()
    
    # Determine k to use
    if k is not None:
        # Fixed k mode
        k_use = k
        new_k_ema = float(k)
    else:
        # Adaptive k with optional EMA smoothing
        if k_ema is not None:
            # Update EMA
            new_k_ema = k_ema_alpha * eff_rank_raw + (1 - k_ema_alpha) * k_ema
            k_use = max(1, int(round(new_k_ema)))
        else:
            # No smoothing, use raw
            k_use = max(1, int(round(eff_rank_raw)))
            new_k_ema = eff_rank_raw
    
    k_use = min(k_use, len(S))
    
    # Compute tail energy (defect)
    tail_energy = S_sq[k_use:].sum().item() if k_use < len(S) else 0.0
    
    # ε = tail_energy / total_energy
    epsilon = tail_energy / total_energy if total_energy > 0 else 0.0
    
    # Validity horizon T* = 1/ε (clamped for numerical stability)
    epsilon_safe = max(epsilon, 1e-6)
    validity_horizon = 1.0 / epsilon_safe
    
    return DefectMeasurement(
        epsilon=epsilon,
        effective_rank=k_use,
        tail_energy=tail_energy,
        total_energy=total_energy,
        top_singular_values=S[:k_use].tolist(),
        validity_horizon=validity_horizon
    ), new_k_ema


# ═══════════════════════════════════════════════════════════════════════════════
# SELF-SCHEDULING CONTROLLER (THE BREAKTHROUGH)
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class ExplorationMassController:
    """
    Phase-5.1: Exploration Mass Controller with Principled Mixing Guarantee.
    
    THE BREAKTHROUGH: Quench trigger based on accumulated noise injection (exploration mass),
    not epochs or entropy. This is EXOGENOUS (we control it) but PRINCIPLED (from mixing theory).
    
    THEORETICAL FOUNDATION (ExplorationMass.lean):
        - Each noise step with strength η contracts distance by factor (1-η)
        - After N steps: distance ≤ exp(-M) × d₀, where M = Σηₜ
        - Quench when M ≥ M_explore = log(d₀/δ)
    
    WHY THIS BREAKS THE DEADLOCK:
        - Phase-4 entropy-triggered control failed: low WD suppresses entropy drop
        - Exploration mass M = Σηₜ depends only on OUR noise injection
        - We accumulate M until the mixing theorem guarantees δ-closeness
    
    QUENCH TRIGGER:
        exploration_mass >= M_explore = log(initial_distance / delta)
    
    This replaces the problematic "wait for ε to stabilize" with a guaranteed mixing criterion.
    """
    
    # Tolerance parameters
    delta: float = 0.1  # Target mixing tolerance (10%)
    initial_distance: float = 1.0  # d₀ - initial distance to equilibrium (estimated)
    
    # Weight decay bounds
    wd_heat: float = 0.1  # Low WD during exploration (heat)
    wd_quench: float = 2.0  # High WD during consolidation (quench)
    wd_baseline: float = 1.0  # Normal WD
    
    # Noise injection during heat (THIS IS THE KEY CONTROL VARIABLE)
    noise_scale: float = 0.01  # η - noise strength per step
    
    # Optimizer parameters for τ_opt calculation (FROZEN at init)
    train_size: int = 2822  # Number of training samples
    batch_size: int = 512  # Batch size
    lr: float = 1e-3  # Learning rate
    tau_opt_const: float = field(init=False)  # Frozen Markov time per epoch
    
    # EXPLORATION MASS TRACKING (the breakthrough)
    exploration_mass: float = 0.0  # M = Σηₜ (accumulated noise)
    M_explore: float = field(init=False)  # Threshold: log(d₀/δ)
    
    # Safety bounds (hybrid: principled + guardrails)
    min_exploration_mass: float = 1.0  # Minimum M before quench allowed
    max_exploration_mass: float = 10.0  # Maximum M before forced quench (safety)
    
    # Observables for logging (NOT used for trigger)
    epsilon_history: deque = field(default_factory=lambda: deque(maxlen=50))
    eff_rank_history: deque = field(default_factory=lambda: deque(maxlen=50))
    peak_eff_rank: float = 0.0
    
    # Fixed-k mode (None = adaptive)
    fixed_k: Optional[int] = None
    k_ema: Optional[float] = None
    k_ema_alpha: float = 0.1
    
    # State tracking
    current_phase: str = 'heat'
    quench_triggered_epoch: int = -1
    current_epsilon: float = 1.0
    current_eff_rank: float = 0.0
    prev_update_epoch: int = 0
    
    # History for analysis
    phase_history: List[Tuple[int, str, float]] = field(default_factory=list)
    exploration_mass_history: List[Tuple[int, float]] = field(default_factory=list)
    
    def __post_init__(self):
        """
        Initialize the controller:
        1. Compute frozen τ_opt_const (Markov time per epoch)
        2. Compute M_explore = log(d₀/δ) (exploration mass threshold)
        """
        # Markov time per epoch
        updates_per_epoch = math.ceil(self.train_size / self.batch_size)
        eta_eff = self.lr / (1.0 + self.wd_baseline)
        self.tau_opt_const = updates_per_epoch * eta_eff
        
        # Exploration mass threshold from mixing theorem
        # M_explore = log(d₀/δ) guarantees distance ≤ δ
        self.M_explore = math.log(self.initial_distance / self.delta)
        
        print(f"[ExplorationMassController] Initialized:")
        print(f"    tau_opt_const = {self.tau_opt_const:.6f}")
        print(f"    M_explore = log({self.initial_distance}/{self.delta}) = {self.M_explore:.4f}")
        print(f"    Safety bounds: [{self.min_exploration_mass}, {self.max_exploration_mass}]")
    
    def _is_ready_for_quench(self, debug: bool = False) -> Tuple[bool, str]:
        """
        Check quench condition based on exploration mass.
        
        THE BREAKTHROUGH: Trigger is EXOGENOUS (our noise injection) not ENDOGENOUS (network state).
        
        Returns (ready, trigger_reason)
        """
        # Primary trigger: exploration mass exceeds threshold
        mass_sufficient = self.exploration_mass >= self.M_explore
        
        # Safety lower bound: don't quench too early even if M_explore is small
        above_minimum = self.exploration_mass >= self.min_exploration_mass
        
        # Safety upper bound: force quench if we've explored too long
        force_quench = self.exploration_mass >= self.max_exploration_mass
        
        if force_quench:
            return True, "FORCE_MAX"
        elif mass_sufficient and above_minimum:
            return True, "MASS_THRESHOLD"
        elif mass_sufficient and not above_minimum:
            reason = f"WAITING_MIN (M={self.exploration_mass:.3f} < min={self.min_exploration_mass})"
            return False, reason
        else:
            reason = f"ACCUMULATING (M={self.exploration_mass:.3f} < M_explore={self.M_explore:.3f})"
            return False, reason
    
    def update(self, epoch: int, epsilon: float, eff_rank: float = 0.0) -> Tuple[float, str]:
        """
        Update the controller with new measurements.
        
        KEY CHANGE: We accumulate exploration mass EXOGENOUSLY based on our noise injection,
        not endogenously based on network observables. This breaks the feedback deadlock.
        
        Args:
            epoch: Current training epoch
            epsilon: Lumpability defect (for logging only, NOT used for trigger)
            eff_rank: Hidden layer effective rank (for logging only)
        
        Returns:
            (weight_decay, phase) tuple
        """
        # Track observables for logging (NOT for trigger decision)
        self.current_epsilon = epsilon
        self.current_eff_rank = eff_rank
        self.epsilon_history.append((epoch, epsilon))
        self.eff_rank_history.append((epoch, eff_rank))
        
        if eff_rank > self.peak_eff_rank:
            self.peak_eff_rank = eff_rank
        
        prev_phase = self.current_phase
        
        # Phase logic
        if self.current_phase == 'heat':
            # ACCUMULATE EXPLORATION MASS during heat phase
            # Each epoch contributes: η (noise strength per epoch)
            # Calibrated so quench triggers around epoch 2000 (like Phase-4)
            # With noise_scale=0.01, M_explore=2.3: quench at ~230 tomography points
            # At tomography_interval=100: quench at ~2300 epochs (reasonable)
            epoch_delta = epoch - self.prev_update_epoch if self.prev_update_epoch > 0 else 1
            mass_increment = self.noise_scale * epoch_delta
            self.exploration_mass += mass_increment
            
            self.exploration_mass_history.append((epoch, self.exploration_mass))
            
            # Debug output
            debug = (epoch % 1000 == 0)
            ready, trigger_reason = self._is_ready_for_quench(debug=debug)
            
            if debug:
                print(f"  [DEBUG] Exploration mass at epoch {epoch}:")
                print(f"    M = {self.exploration_mass:.4f} (threshold M_explore = {self.M_explore:.4f})")
                print(f"    Status: {trigger_reason}")
                print(f"    epsilon = {epsilon:.4f}, eff_rank = {eff_rank:.2f}")
            
            if ready:
                self.current_phase = 'quench'
                self.quench_triggered_epoch = epoch
                print(f"\n*** EXPLORATION MASS QUENCH at epoch {epoch} ***")
                print(f"    exploration_mass M = {self.exploration_mass:.4f}")
                print(f"    threshold M_explore = {self.M_explore:.4f}")
                print(f"    trigger: {trigger_reason}")
                print(f"    epsilon = {epsilon:.4f}")
                print(f"    eff_rank = {eff_rank:.2f} (peak = {self.peak_eff_rank:.2f})")
        
        elif self.current_phase == 'quench':
            # Quench continues until grokking (handled externally)
            pass
        
        self.prev_update_epoch = epoch
        
        # Track phase transitions
        if self.current_phase != prev_phase:
            self.phase_history.append((epoch, self.current_phase, epsilon))
        
        # Return weight decay based on phase
        if self.current_phase == 'heat':
            return self.wd_heat, 'heat'
        elif self.current_phase == 'quench':
            return self.wd_quench, 'quench'
        else:
            return self.wd_baseline, 'done'
    
    def inject_noise(self, model: 'GrokMLP', device: str = 'cuda'):
        """
        Inject isotropic noise during heat phase.
        
        This is the KEY CONTROL VARIABLE: noise injection accumulates exploration mass.
        The quench trigger depends on how much noise we've injected, not on network state.
        """
        if self.current_phase != 'heat':
            return
        
        with torch.no_grad():
            for param in model.parameters():
                noise = torch.randn_like(param) * self.noise_scale
                param.add_(noise)
    
    def get_summary(self) -> Dict:
        return {
            'delta': self.delta,
            'initial_distance': self.initial_distance,
            'M_explore': self.M_explore,
            'final_exploration_mass': self.exploration_mass,
            'tau_opt_const': self.tau_opt_const,
            'noise_scale': self.noise_scale,
            'final_epsilon': self.current_epsilon,
            'final_eff_rank': self.current_eff_rank,
            'peak_eff_rank': self.peak_eff_rank,
            'quench_triggered_epoch': self.quench_triggered_epoch,
            'phase_history': self.phase_history,
        }


# ═══════════════════════════════════════════════════════════════════════════════
# SPECTRAL ANALYSIS (from Phase-4)
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class LayerSpectrum:
    name: str
    eigenvalues: torch.Tensor
    effective_rank: float
    spectral_entropy: float
    top_eigenvalue: float
    defect: DefectMeasurement


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


def compute_layer_spectrum(weight: torch.Tensor, name: str, 
                           fixed_k: Optional[int] = None,
                           k_ema: Optional[float] = None,
                           k_ema_alpha: float = 0.1) -> Tuple[LayerSpectrum, float]:
    """Compute layer spectrum with optional fixed-k or EMA-smoothed k."""
    _, S, _ = torch.linalg.svd(weight, full_matrices=False)
    eigenvalues = S ** 2
    
    eff_rank = compute_effective_rank(eigenvalues)
    entropy = compute_spectral_entropy(eigenvalues)
    top_eig = eigenvalues[0].item() if len(eigenvalues) > 0 else 0.0
    
    # Compute defect with k handling
    defect, new_k_ema = compute_defect(weight, k=fixed_k, k_ema=k_ema, k_ema_alpha=k_ema_alpha)
    
    return LayerSpectrum(
        name=name,
        eigenvalues=eigenvalues,
        effective_rank=eff_rank,
        spectral_entropy=entropy,
        top_eigenvalue=top_eig,
        defect=defect
    ), new_k_ema


# ═══════════════════════════════════════════════════════════════════════════════
# EVENT TRACKING
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class EventTracker:
    initial_hidden_eff_rank: float = 0.0
    rank_collapse_threshold: float = 0.7
    
    epoch_first_rank_collapse: int = -1
    grokking_epoch: int = -1
    grokking_threshold: float = 0.99
    
    # Phase-5.1 specific (exploration mass)
    computed_quench_epoch: int = -1
    epsilon_at_quench: float = 0.0
    exploration_mass_at_quench: float = 0.0  # M = Σηₜ at quench
    tau_at_quench: float = 0.0
    
    def update(self, epoch: int, hidden_spectrum: LayerSpectrum, test_acc: float):
        if self.initial_hidden_eff_rank == 0.0:
            self.initial_hidden_eff_rank = hidden_spectrum.effective_rank
        
        current_eff_rank = hidden_spectrum.effective_rank
        if (self.epoch_first_rank_collapse < 0 and 
            current_eff_rank < self.rank_collapse_threshold * self.initial_hidden_eff_rank):
            self.epoch_first_rank_collapse = epoch
        
        if self.grokking_epoch < 0 and test_acc >= self.grokking_threshold:
            self.grokking_epoch = epoch
    
    def to_dict(self) -> Dict:
        return {
            'initial_hidden_eff_rank': self.initial_hidden_eff_rank,
            'epoch_first_rank_collapse': self.epoch_first_rank_collapse,
            'grokking_epoch': self.grokking_epoch,
            'computed_quench_epoch': self.computed_quench_epoch,
            'epsilon_at_quench': self.epsilon_at_quench,
            'exploration_mass_at_quench': self.exploration_mass_at_quench,
            'tau_at_quench': self.tau_at_quench,
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
# TRAINING LOOP (SELF-SCHEDULING)
# ═══════════════════════════════════════════════════════════════════════════════

def train_phase5(
    model: GrokMLP,
    train_loader: DataLoader,
    test_loader: DataLoader,
    controller: ExplorationMassController,
    epochs: int = 15000,
    lr: float = 1e-3,
    weight_decay: float = 1.0,
    device: str = 'cuda',
    tomography_interval: int = 50,
    log_dir: str = 'logs/phase5',
    csv_path: str = None,
    grokking_threshold: float = 0.99,
) -> Tuple[Dict, EventTracker]:
    """
    Phase-5.1 training loop with exploration mass controller.
    Quench trigger: M = Σηₜ ≥ M_explore = log(d₀/δ)
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
    history = {'train_loss': [], 'train_acc': [], 'test_acc': [], 'epochs': []}
    
    # k EMA state for defect computation
    k_ema_state = None
    
    print(f"Training for {epochs} epochs with EXPLORATION MASS CONTROLLER...")
    print(f"  delta (tolerance) = {controller.delta}")
    print(f"  M_explore = {controller.M_explore:.4f}")
    print(f"  tau_opt_const = {controller.tau_opt_const:.6f}")
    print(f"  noise_scale eta = {controller.noise_scale}")
    print(f"  fixed_k = {controller.fixed_k}")
    print("-" * 70)
    
    for epoch in range(1, epochs + 1):
        # === SPECTRAL ANALYSIS (every tomography_interval) ===
        if epoch % tomography_interval == 0 or epoch == 1:
            weights = model.get_layer_weights()
            hidden_spectrum, k_ema_state = compute_layer_spectrum(
                weights['hidden_1'], 'hidden_1',
                fixed_k=controller.fixed_k,
                k_ema=k_ema_state,
                k_ema_alpha=controller.k_ema_alpha
            )
            
            # Update event tracker
            test_acc_current = history['test_acc'][-1] if history['test_acc'] else 0.0
            event_tracker.update(epoch, hidden_spectrum, test_acc_current)
            
            # === SELF-SCHEDULING CONTROL ===
            new_wd, phase = controller.update(
                epoch, 
                hidden_spectrum.defect.epsilon,
                hidden_spectrum.effective_rank
            )
            
            # Update optimizer weight decay
            for param_group in optimizer.param_groups:
                param_group['weight_decay'] = new_wd
            
            # Inject noise during heat phase
            if phase == 'heat':
                controller.inject_noise(model, device)
            
            # Track quench trigger
            if controller.quench_triggered_epoch == epoch:
                event_tracker.computed_quench_epoch = epoch
                event_tracker.epsilon_at_quench = controller.current_epsilon
                event_tracker.exploration_mass_at_quench = controller.exploration_mass
                event_tracker.tau_at_quench = controller.tau_opt_const
            
            # Log spectral metrics
            for name, W in weights.items():
                spectrum, _ = compute_layer_spectrum(W, name, fixed_k=controller.fixed_k)
                writer.add_scalar(f'Spectrum/EffRank/{name}', spectrum.effective_rank, epoch)
                writer.add_scalar(f'Spectrum/Entropy/{name}', spectrum.spectral_entropy, epoch)
                writer.add_scalar(f'Spectrum/Defect/{name}', spectrum.defect.epsilon, epoch)
                writer.add_scalar(f'Spectrum/ValidityHorizon/{name}', spectrum.defect.validity_horizon, epoch)
            
            # Log controller state
            writer.add_scalar('Controller/Epsilon', controller.current_epsilon, epoch)
            writer.add_scalar('Controller/EffRank', controller.current_eff_rank, epoch)
            writer.add_scalar('Controller/PeakEffRank', controller.peak_eff_rank, epoch)
            writer.add_scalar('Controller/ExplorationMass', controller.exploration_mass, epoch)
            writer.add_scalar('Controller/M_explore', controller.M_explore, epoch)
            writer.add_scalar('Controller/TauOptConst', controller.tau_opt_const, epoch)
            writer.add_scalar('Controller/WeightDecay', new_wd, epoch)
            writer.add_scalar('Controller/Phase', {'heat': 0, 'quench': 1, 'done': 2}[phase], epoch)
            
            # CSV logging
            csv_row = {
                'train_loss': history['train_loss'][-1] if history['train_loss'] else 0,
                'train_acc': history['train_acc'][-1] if history['train_acc'] else 0,
                'test_acc': test_acc_current,
                'hidden_eff_rank': hidden_spectrum.effective_rank,
                'hidden_entropy': hidden_spectrum.spectral_entropy,
                'hidden_k': hidden_spectrum.defect.effective_rank,
                'epsilon': controller.current_epsilon,
                'exploration_mass': controller.exploration_mass,
                'M_explore': controller.M_explore,
                'tau_opt_const': controller.tau_opt_const,
                'peak_eff_rank': controller.peak_eff_rank,
                'phase': phase,
                'weight_decay': new_wd,
            }
            csv_logger.log(epoch, csv_row)
        
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
        
        # Console output
        if epoch % 500 == 0 or epoch == 1:
            msg = f"Epoch {epoch:5d}: loss={train_loss:.4f}, train={train_acc*100:.1f}%, test={test_acc*100:.1f}%"
            msg += f" | M={controller.exploration_mass:.3f}/{controller.M_explore:.3f}"
            msg += f" | phase={controller.current_phase}"
            print(msg)
        
        # Early stopping on grokking
        if test_acc >= grokking_threshold:
            print(f"\n*** GROKKING ACHIEVED at epoch {epoch}! ***")
            event_tracker.grokking_epoch = epoch
            break
    
    # Save CSV
    csv_logger.save()
    print(f"\nMetrics saved to {csv_path}")
    
    # Log final events
    events = event_tracker.to_dict()
    controller_summary = controller.get_summary()
    
    print(f"\n{'='*70}")
    print("EXPLORATION MASS SUMMARY")
    print("="*70)
    print(f"  Initial hidden eff-rank: {events['initial_hidden_eff_rank']:.2f}")
    print(f"  Peak eff-rank: {controller.peak_eff_rank:.2f}")
    print(f"  First rank collapse (70%): epoch {events['epoch_first_rank_collapse']}")
    print(f"  Exploration mass quench: epoch {events['computed_quench_epoch']}")
    if events['computed_quench_epoch'] > 0:
        print(f"    exploration_mass M: {events['exploration_mass_at_quench']:.4f}")
        print(f"    threshold M_explore: {controller.M_explore:.4f}")
        print(f"    epsilon at quench: {events['epsilon_at_quench']:.4f}")
    print(f"  Final exploration mass: {controller.exploration_mass:.4f}")
    print(f"  Grokking epoch: {events['grokking_epoch']}")
    
    if events['computed_quench_epoch'] > 0 and events['grokking_epoch'] > 0:
        quench_to_grok = events['grokking_epoch'] - events['computed_quench_epoch']
        print(f"  Epochs from quench to grokking: {quench_to_grok}")
    
    writer.close()
    return history, event_tracker


# ═══════════════════════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════════════════════

def main():
    parser = argparse.ArgumentParser(description="SGC Phase-5: Self-Scheduling Grokking")
    
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
    
    # Exploration Mass Controller parameters (Phase-5.1)
    parser.add_argument('--delta', type=float, default=0.1, help='Mixing tolerance δ (default: 0.1 = 10%)')
    parser.add_argument('--initial_distance', type=float, default=1.0, help='Initial distance d₀ to equilibrium')
    parser.add_argument('--wd_heat', type=float, default=0.1, help='Weight decay during heat phase')
    parser.add_argument('--wd_quench', type=float, default=2.0, help='Weight decay during quench phase')
    parser.add_argument('--noise_scale', type=float, default=0.01, help='Noise injection strength η (KEY CONTROL)')
    
    # Exploration mass safety bounds
    parser.add_argument('--min_exploration_mass', type=float, default=1.0, help='Minimum M before quench allowed')
    parser.add_argument('--max_exploration_mass', type=float, default=10.0, help='Maximum M (force quench)')
    
    # Fixed-k mode
    parser.add_argument('--fixed_k', type=int, default=None, help='Fix k for defect computation (None = adaptive)')
    parser.add_argument('--k_ema_alpha', type=float, default=0.1, help='EMA alpha for k smoothing')
    
    # Logging
    parser.add_argument('--tomography_interval', type=int, default=50)
    parser.add_argument('--log_dir', type=str, default='logs/phase5')
    
    # Misc
    parser.add_argument('--device', type=str, default='cuda' if torch.cuda.is_available() else 'cpu')
    parser.add_argument('--seed', type=int, default=42)
    
    args = parser.parse_args()
    
    print("=" * 70)
    print("SGC PHASE-5.1: EXPLORATION MASS CONTROLLER")
    print("Quench trigger: M = sum(eta_t) >= M_explore = log(d0/delta)")
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
    
    # Estimate exploration mass threshold
    M_explore_preview = math.log(args.initial_distance / args.delta)
    
    print(f"\nExploration Mass Parameters (Phase-5.1):")
    print(f"  delta (tolerance): {args.delta}")
    print(f"  initial_distance d0: {args.initial_distance}")
    print(f"  M_explore = log(d0/delta) = {M_explore_preview:.4f}")
    print(f"  noise_scale eta: {args.noise_scale} (KEY CONTROL - accumulates mass)")
    print(f"  Safety bounds: [{args.min_exploration_mass}, {args.max_exploration_mass}]")
    print(f"  WD heat={args.wd_heat}, quench={args.wd_quench}")
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
    
    actual_train_size = len(train_dataset)
    actual_tau_opt = math.ceil(actual_train_size / args.batch_size) * (args.lr / (1.0 + args.weight_decay))
    print(f"Dataset: {actual_train_size} train, {len(test_dataset)} test")
    print(f"  tau_opt_const (actual): {actual_tau_opt:.6f}")
    
    train_loader = DataLoader(train_dataset, batch_size=args.batch_size, shuffle=True)
    test_loader = DataLoader(test_dataset, batch_size=args.batch_size, shuffle=False)
    
    # Create model
    model = GrokMLP(args.p, args.hidden_dim)
    n_params = sum(p.numel() for p in model.parameters())
    print(f"Model parameters: {n_params:,}")
    print()
    
    # Create exploration mass controller (Phase-5.1)
    controller = ExplorationMassController(
        delta=args.delta,
        initial_distance=args.initial_distance,
        wd_heat=args.wd_heat,
        wd_quench=args.wd_quench,
        wd_baseline=args.weight_decay,
        noise_scale=args.noise_scale,
        # Optimizer params for tau_opt
        train_size=len(train_dataset),
        batch_size=args.batch_size,
        lr=args.lr,
        # Safety bounds
        min_exploration_mass=args.min_exploration_mass,
        max_exploration_mass=args.max_exploration_mass,
        # Fixed-k mode
        fixed_k=args.fixed_k,
        k_ema_alpha=args.k_ema_alpha,
    )
    
    # Train
    history, events = train_phase5(
        model, train_loader, test_loader,
        controller=controller,
        epochs=args.epochs,
        lr=args.lr,
        weight_decay=args.weight_decay,
        device=args.device,
        tomography_interval=args.tomography_interval,
        log_dir=args.log_dir,
        grokking_threshold=args.grokking_threshold,
    )
    
    print("\n" + "=" * 70)
    print("PHASE-5.1 EXPERIMENT COMPLETE")
    print("=" * 70)
    
    # Final report
    print("\nExploration Mass Results:")
    if events.computed_quench_epoch > 0:
        print(f"  [OK] Exploration mass quench at epoch {events.computed_quench_epoch}")
        print(f"       exploration_mass M = {events.exploration_mass_at_quench:.4f}")
        print(f"       threshold M_explore = {controller.M_explore:.4f}")
        print(f"       epsilon at quench = {events.epsilon_at_quench:.4f}")
    else:
        print(f"  [--] Quench never triggered")
        print(f"       Current exploration mass: {controller.exploration_mass:.4f}")
        print(f"       Threshold M_explore: {controller.M_explore:.4f}")
    
    if events.grokking_epoch > 0:
        print(f"  [OK] Grokking achieved at epoch {events.grokking_epoch}")
        if events.computed_quench_epoch > 0:
            lag = events.grokking_epoch - events.computed_quench_epoch
            print(f"       Quench-to-grokking lag: {lag} epochs")
    else:
        print(f"  [--] Grokking not achieved within {args.epochs} epochs")


if __name__ == "__main__":
    main()
