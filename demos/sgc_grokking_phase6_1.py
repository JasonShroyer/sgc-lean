#!/usr/bin/env python3
"""
SGC Phase-6.1: Corrected Wavelet-Coupled Exploration Mass Controller
=====================================================================

CRITICAL FIXES from Phase-6:
1. Noise injection EVERY EPOCH during heat (not just tomography epochs)
2. Mass accounting matches actual injection frequency
3. κ_tail (spectral proxy) vs κ_contract (actual contraction) separated
4. Isotropic κ properly measured, not hard-coded
5. Hybrid noise mode: λ-scheduled wavelet+isotropic mix for rank preservation
6. Soft anneal phase: WD ramp instead of step change
7. Frame tightness audit removed (was computing condition number, not frame bound)

THEORETICAL ALIGNMENT:
- κ_contract = clip((d_t - d_{t+1}) / (η_t × d_t), 0, 1)
  This is the coupling coefficient that appears in the Lean theorem:
  d_{t+1} ≤ (1 - κ_t η_t) d_t

- κ_tail = ||noise in tail||² / ||noise||²
  This is a spectral proxy for coupling efficiency

The Lean guarantee holds if we trigger on Σ κ_contract_t η_t ≥ log(d₀/δ)

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
# DEFECT MEASUREMENT (distance d_t for κ_contract)
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class DefectMeasurement:
    """Measurement of the Lumpability Defect epsilon."""
    epsilon: float
    k_coarse: int
    tail_energy: float
    total_energy: float


def compute_defect(weight_matrix: torch.Tensor, k: Optional[int] = None) -> DefectMeasurement:
    """Compute lumpability defect using SVD tail energy."""
    W = weight_matrix.detach().cpu().float()
    
    try:
        U, S, Vh = torch.linalg.svd(W, full_matrices=False)
    except Exception:
        return DefectMeasurement(epsilon=1.0, k_coarse=1, tail_energy=1.0, total_energy=1.0)
    
    S_squared = S ** 2
    total_energy = S_squared.sum().item()
    
    if total_energy < 1e-10:
        return DefectMeasurement(epsilon=1.0, k_coarse=1, tail_energy=0.0, total_energy=total_energy)
    
    if k is None:
        cumsum = torch.cumsum(S_squared, dim=0)
        threshold = 0.95 * total_energy
        k = int((cumsum < threshold).sum().item()) + 1
        k = max(1, min(k, len(S)))
    
    tail_energy = S_squared[k:].sum().item() if k < len(S) else 0.0
    epsilon = math.sqrt(tail_energy / total_energy) if total_energy > 0 else 0.0
    
    return DefectMeasurement(
        epsilon=epsilon,
        k_coarse=k,
        tail_energy=tail_energy,
        total_energy=total_energy
    )


def compute_effective_rank(weight_matrix: torch.Tensor) -> float:
    """Compute effective rank from singular value entropy."""
    W = weight_matrix.detach().cpu().float()
    
    try:
        S = torch.linalg.svdvals(W)
    except Exception:
        return 1.0
    
    S_squared = S ** 2
    total = S_squared.sum().item()
    
    if total < 1e-10:
        return 1.0
    
    p = S_squared / total
    p = p[p > 1e-10]
    
    if len(p) == 0:
        return 1.0
    
    entropy = -(p * torch.log(p)).sum().item()
    return math.exp(entropy)


def compute_spectral_entropy(weight_matrix: torch.Tensor) -> float:
    """Compute spectral entropy."""
    W = weight_matrix.detach().cpu().float()
    
    try:
        S = torch.linalg.svdvals(W)
    except Exception:
        return 0.0
    
    S_squared = S ** 2
    total = S_squared.sum().item()
    
    if total < 1e-10:
        return 0.0
    
    p = S_squared / total
    p = p[p > 1e-10]
    
    return -(p * torch.log(p)).sum().item()


# ═══════════════════════════════════════════════════════════════════════════════
# HERMITE-GAUSSIAN WAVELET SHAPING
# ═══════════════════════════════════════════════════════════════════════════════

def hermite_gaussian_weight(u: np.ndarray, a: float = 1.0, b: float = 1.0) -> np.ndarray:
    """
    Hermite-Gaussian wavelet weight function: psi(u) = C × u^a × exp(-b × u^2)
    """
    u_shifted = u + 0.01
    weights = (u_shifted ** a) * np.exp(-b * u_shifted ** 2)
    
    norm = np.sqrt(np.sum(weights ** 2))
    if norm > 1e-10:
        weights = weights / norm
    
    return weights


def compute_spectral_coupling_tail(noise_projection: torch.Tensor, tail_mask: torch.Tensor) -> float:
    """
    Compute κ_tail: fraction of noise energy in tail subspace.
    
    κ_tail = ||noise in tail||² / ||noise||²
    
    This is a spectral PROXY, not the contraction coupling from the theorem.
    """
    noise_energy = (noise_projection ** 2).sum().item()
    if noise_energy < 1e-10:
        return 0.0
    
    tail_energy = ((noise_projection * tail_mask) ** 2).sum().item()
    return tail_energy / noise_energy


# ═══════════════════════════════════════════════════════════════════════════════
# PHASE-6.1: CORRECTED WAVELET-COUPLED CONTROLLER
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class CorrectedWaveletController:
    """
    Phase-6.1 Controller with critical fixes:
    
    1. Per-epoch noise injection (not just tomography epochs)
    2. Separate κ_tail (proxy) from κ_contract (theorem-aligned)
    3. Hybrid noise mode with λ schedule
    4. Soft anneal phase with WD ramp
    5. Rank floor monitoring
    """
    
    # Mixing parameters
    delta: float = 0.1
    initial_distance: float = 1.0
    
    # Weight decay schedule
    wd_heat: float = 0.1
    wd_quench: float = 2.0
    wd_baseline: float = 1.0
    
    # Anneal parameters (soft quench)
    anneal_epochs: int = 500
    noise_floor: float = 0.01  # Minimum noise during anneal (not hard-off)
    
    # Noise injection
    noise_scale: float = 0.1
    noise_mode: str = 'hybrid'  # 'isotropic', 'wavelet', 'hybrid'
    
    # Hybrid mode parameters
    lambda_start: float = 0.2   # Start with 80% isotropic, 20% wavelet
    lambda_end: float = 0.8     # End with 20% isotropic, 80% wavelet
    current_lambda: float = 0.2
    
    # Wavelet parameters
    wavelet_a: float = 1.0
    wavelet_b: float = 2.0
    tail_fraction: float = 0.5
    
    # Rank floor (from Phase-5.1 findings)
    rank_floor_fraction: float = 0.6  # Maintain at least 60% of peak rank
    rank_violations: int = 0
    
    # Optimizer info
    train_size: int = 2822
    batch_size: int = 32
    lr: float = 0.001
    
    # Computed constants
    tau_opt_const: float = field(init=False)
    M_explore: float = field(init=False)
    
    # EXPLORATION MASS TRACKING
    M_nominal: float = 0.0          # Σ η_t (actual injections)
    M_effective_tail: float = 0.0   # Σ κ_tail × η_t
    M_effective_contract: float = 0.0  # Σ κ_contract × η_t (theorem-aligned)
    
    # Coupling coefficients
    kappa_tail: float = 0.01        # Spectral proxy
    kappa_contract: float = 0.01    # Contraction-based (from ε change)
    kappa_tail_history: List[float] = field(default_factory=list)
    kappa_contract_history: List[float] = field(default_factory=list)
    
    # EMA tracking
    kappa_tail_ema: float = 0.01
    kappa_contract_ema: float = 0.01
    kappa_ema_alpha: float = 0.1
    
    # Trigger mode
    trigger_mode: str = 'effective_contract'  # 'nominal', 'effective_tail', 'effective_contract', 'calibrated'
    calibrated_kappa: float = 0.01
    
    # Safety bounds
    min_exploration_mass: float = 1.0
    max_exploration_mass: float = 500.0
    
    # Observables
    epsilon_history: deque = field(default_factory=lambda: deque(maxlen=100))
    eff_rank_history: deque = field(default_factory=lambda: deque(maxlen=100))
    peak_eff_rank: float = 0.0
    
    # Previous epsilon for κ_contract calculation
    prev_epsilon: float = 1.0
    
    # BLOCK COUPLING: accumulate η between tomography measurements
    eta_mass_since_tomo: float = 0.0  # Σ η_t since last tomography
    d_min: float = 1e-6  # Floor to avoid division noise
    
    # State
    current_phase: str = 'heat'  # 'heat', 'anneal', 'quench', 'stable'
    anneal_start_epoch: int = -1
    quench_triggered_epoch: int = -1
    current_epsilon: float = 1.0
    current_eff_rank: float = 0.0
    injection_count: int = 0  # Track actual injections
    
    # Grokking-aware early stopping
    grokking_achieved: bool = False
    grokking_epoch: int = -1
    grokking_threshold: float = 0.95  # Test accuracy threshold
    
    # History
    phase_history: List[Tuple[int, str, float]] = field(default_factory=list)
    mass_history: List[Tuple[int, float, float, float, float]] = field(default_factory=list)
    
    def __post_init__(self):
        updates_per_epoch = math.ceil(self.train_size / self.batch_size)
        eta_eff = self.lr / (1.0 + self.wd_baseline)
        self.tau_opt_const = updates_per_epoch * eta_eff
        
        self.M_explore = math.log(self.initial_distance / self.delta)
        
        print(f"[CorrectedWaveletController] Phase-6.1 Initialized:")
        print(f"    M_explore = log({self.initial_distance}/{self.delta}) = {self.M_explore:.4f}")
        print(f"    Noise mode: {self.noise_mode}")
        if self.noise_mode == 'hybrid':
            print(f"    Lambda schedule: {self.lambda_start} -> {self.lambda_end}")
        print(f"    Trigger mode: {self.trigger_mode}")
        print(f"    Anneal epochs: {self.anneal_epochs}")
        print(f"    Noise floor during anneal: {self.noise_floor}")
        print(f"    Rank floor: {self.rank_floor_fraction * 100:.0f}% of peak")
    
    def _get_trigger_threshold(self) -> float:
        if self.trigger_mode == 'nominal':
            return self.min_exploration_mass
        elif self.trigger_mode == 'effective_tail':
            return self.M_explore
        elif self.trigger_mode == 'effective_contract':
            return self.M_explore
        elif self.trigger_mode == 'calibrated':
            return self.M_explore / self.calibrated_kappa
        else:
            return self.M_explore
    
    def _get_current_mass(self) -> float:
        if self.trigger_mode == 'nominal':
            return self.M_nominal
        elif self.trigger_mode == 'effective_tail':
            return self.M_effective_tail
        elif self.trigger_mode == 'effective_contract':
            return self.M_effective_contract
        elif self.trigger_mode == 'calibrated':
            return self.M_nominal
        else:
            return self.M_effective_contract
    
    def _is_ready_for_quench(self) -> Tuple[bool, str]:
        current_mass = self._get_current_mass()
        threshold = self._get_trigger_threshold()
        
        force_quench = self.M_nominal >= self.max_exploration_mass
        mass_sufficient = current_mass >= threshold
        above_minimum = self.M_nominal >= self.min_exploration_mass
        
        if force_quench:
            return True, "FORCE_MAX"
        elif mass_sufficient and above_minimum:
            return True, f"MASS_THRESHOLD (M={current_mass:.3f} >= {threshold:.3f})"
        else:
            return False, f"ACCUMULATING (M={current_mass:.3f} < {threshold:.3f})"
    
    def _compute_kappa_contract_block(self, epsilon: float) -> float:
        """
        Compute κ_contract using BLOCK/INTERVAL estimator.
        
        FIXED: Uses cumulative η over tomography interval, not single-step η.
        
        From theorem: d_{t+1} ≤ (1 - κη) d_t
        Over block: d_{k+1} ≈ exp(-κ × Η_k) × d_k
        
        Log-ratio estimator (more stable):
        κ_block = clip(-log(d_{k+1}/d_k) / Η_k, 0, 1)
        
        where Η_k = Σ η_t over the tomography interval.
        """
        d_prev = max(self.prev_epsilon, self.d_min)
        d_curr = max(epsilon, self.d_min)
        Eta_k = self.eta_mass_since_tomo
        
        if Eta_k < 1e-10:
            return 0.0
        
        # Log-ratio estimator (handles non-monotonicity better)
        ratio = d_curr / d_prev
        if ratio >= 1.0:
            # No contraction (distance increased or stayed same)
            return 0.0
        
        # κ = -log(ratio) / Η_k
        kappa = -math.log(ratio) / Eta_k
        
        # Clip to [0, 1] as required by theorem
        return max(0.0, min(1.0, kappa))
    
    def _update_lambda_schedule(self, epoch: int, heat_epochs: int):
        """Update λ for hybrid noise mixing."""
        if heat_epochs <= 0:
            self.current_lambda = self.lambda_start
            return
        
        # Linear schedule from lambda_start to lambda_end over heat phase
        progress = min(1.0, epoch / max(1, heat_epochs))
        self.current_lambda = self.lambda_start + progress * (self.lambda_end - self.lambda_start)
    
    def _get_anneal_progress(self, epoch: int) -> float:
        """Get progress through anneal phase (0 to 1)."""
        if self.anneal_start_epoch < 0:
            return 0.0
        elapsed = epoch - self.anneal_start_epoch
        return min(1.0, elapsed / max(1, self.anneal_epochs))
    
    def _get_anneal_wd(self, epoch: int) -> float:
        """Get weight decay during anneal (linear ramp)."""
        progress = self._get_anneal_progress(epoch)
        return self.wd_heat + progress * (self.wd_quench - self.wd_heat)
    
    def _get_anneal_noise_scale(self, epoch: int) -> float:
        """Get noise scale during anneal (exponential decay to floor)."""
        progress = self._get_anneal_progress(epoch)
        # Exponential decay: η_0 × exp(-3 × progress) but floored
        scale = self.noise_scale * math.exp(-3.0 * progress)
        return max(self.noise_floor, scale)
    
    def update(self, epoch: int, epsilon: float, eff_rank: float = 0.0) -> Tuple[float, str]:
        """Update controller with new measurements (called every tomography epoch)."""
        self.current_epsilon = epsilon
        self.current_eff_rank = eff_rank
        self.epsilon_history.append((epoch, epsilon))
        self.eff_rank_history.append((epoch, eff_rank))
        
        if eff_rank > self.peak_eff_rank:
            self.peak_eff_rank = eff_rank
        
        # Check rank floor violation
        if self.peak_eff_rank > 0 and eff_rank < self.rank_floor_fraction * self.peak_eff_rank:
            self.rank_violations += 1
        
        prev_phase = self.current_phase
        
        if self.current_phase == 'heat':
            ready, trigger_reason = self._is_ready_for_quench()
            
            if ready:
                # Enter ANNEAL phase (not immediate quench)
                self.current_phase = 'anneal'
                self.anneal_start_epoch = epoch
                print(f"\n*** ENTERING ANNEAL at epoch {epoch} ***")
                print(f"    M_nominal = {self.M_nominal:.4f}")
                print(f"    M_effective_tail = {self.M_effective_tail:.4f}")
                print(f"    M_effective_contract = {self.M_effective_contract:.4f}")
                print(f"    kappa_tail (avg) = {np.mean(self.kappa_tail_history) if self.kappa_tail_history else 0:.4f}")
                print(f"    kappa_contract (avg) = {np.mean(self.kappa_contract_history) if self.kappa_contract_history else 0:.4f}")
                print(f"    trigger: {trigger_reason}")
                print(f"    Ramping WD: {self.wd_heat} -> {self.wd_quench} over {self.anneal_epochs} epochs")
        
        elif self.current_phase == 'anneal':
            # Check if grokking achieved - if so, skip to stable phase
            if self.grokking_achieved:
                self.current_phase = 'stable'
                print(f"\n*** STABLE at epoch {epoch} (grokking achieved, stopping perturbation) ***")
            else:
                progress = self._get_anneal_progress(epoch)
                if progress >= 1.0:
                    self.current_phase = 'quench'
                    self.quench_triggered_epoch = epoch
                    print(f"\n*** QUENCH at epoch {epoch} (anneal complete) ***")
        
        self.prev_epsilon = epsilon
        
        if self.current_phase != prev_phase:
            self.phase_history.append((epoch, self.current_phase, epsilon))
        
        # Return appropriate WD
        if self.current_phase == 'heat':
            return self.wd_heat, 'heat'
        elif self.current_phase == 'anneal':
            return self._get_anneal_wd(epoch), 'anneal'
        elif self.current_phase == 'stable':
            return 1.0, 'stable'  # Moderate WD, no noise
        else:
            return self.wd_quench, 'quench'
    
    def signal_grokking(self, epoch: int, test_acc: float):
        """Signal that grokking has been achieved. Controller will transition to stable phase."""
        if not self.grokking_achieved and test_acc >= self.grokking_threshold:
            self.grokking_achieved = True
            self.grokking_epoch = epoch
            print(f"\n*** GROKKING SIGNALED at epoch {epoch} (test_acc={test_acc*100:.1f}%) ***")
    
    def inject_noise(self, model: 'GrokMLP', device: str, epoch: int, heat_epochs_estimate: int = 2000):
        """
        Inject noise during heat/anneal phases.
        
        CRITICAL: This should be called EVERY EPOCH during heat, not just tomography epochs!
        """
        if self.current_phase in ['quench', 'stable']:
            return  # No noise injection in quench or stable phases
        
        # Determine effective noise scale
        if self.current_phase == 'anneal':
            effective_noise_scale = self._get_anneal_noise_scale(epoch)
        else:
            effective_noise_scale = self.noise_scale
        
        # Update lambda schedule for hybrid mode
        if self.noise_mode == 'hybrid':
            self._update_lambda_schedule(epoch, heat_epochs_estimate)
        
        # Inject based on mode
        if self.noise_mode == 'isotropic':
            kappa_tail = self._inject_isotropic_noise(model, device, effective_noise_scale)
        elif self.noise_mode == 'wavelet':
            kappa_tail = self._inject_wavelet_noise(model, device, effective_noise_scale)
        elif self.noise_mode == 'hybrid':
            kappa_tail = self._inject_hybrid_noise(model, device, effective_noise_scale)
        else:
            kappa_tail = self._inject_isotropic_noise(model, device, effective_noise_scale)
        
        # Track injection
        self.injection_count += 1
        self.kappa_tail = kappa_tail
        
        # Update mass (actual injection)
        self.M_nominal += effective_noise_scale
        self.M_effective_tail += kappa_tail * effective_noise_scale
        
        # Accumulate eta for block kappa_contract calculation
        self.eta_mass_since_tomo += effective_noise_scale
        self.kappa_tail_history.append(kappa_tail)
        
        # Update EMA
        self.kappa_tail_ema = self.kappa_ema_alpha * kappa_tail + (1 - self.kappa_ema_alpha) * self.kappa_tail_ema
    
    def update_kappa_contract(self, new_epsilon: float):
        """
        Update κ_contract based on observed ε contraction over tomography interval.
        
        FIXED: Uses block estimator with cumulative Η_k, not single-step η.
        Call this AFTER tomography measures new epsilon.
        """
        # Use block estimator with accumulated eta
        kappa_c = self._compute_kappa_contract_block(new_epsilon)
        self.kappa_contract = kappa_c
        self.kappa_contract_history.append(kappa_c)
        
        # Update effective mass using accumulated eta for this block
        self.M_effective_contract += kappa_c * self.eta_mass_since_tomo
        
        # Update EMA
        self.kappa_contract_ema = self.kappa_ema_alpha * kappa_c + (1 - self.kappa_ema_alpha) * self.kappa_contract_ema
        
        # Reset accumulator and update prev_epsilon for next block
        self.prev_epsilon = new_epsilon
        self.eta_mass_since_tomo = 0.0
    
    def _inject_isotropic_noise(self, model: 'GrokMLP', device: str, noise_scale: float) -> float:
        """
        Inject isotropic noise and measure actual κ_tail.
        
        FIXED: Uses full Frobenius norm in SVD basis, not just diagonal entries.
        For a layer with SVD W = UΣV^T and noise N, compute C = U^T N V.
        Tail energy = ||C[i >= i_0, :]||_F^2 where i_0 = floor((1-tail_fraction)*n).
        """
        total_kappa = 0.0
        n_layers = 0
        
        with torch.no_grad():
            for name, param in model.named_parameters():
                noise = torch.randn_like(param) * noise_scale
                param.add_(noise)
                
                if param.dim() == 2:
                    # Measure how much noise lands in tail subspace
                    try:
                        U, S, Vh = torch.linalg.svd(param.data, full_matrices=False)
                        n_sv = len(S)
                        tail_start = int(n_sv * (1 - self.tail_fraction))
                        
                        # Project noise to SVD basis: C = U^T @ N @ V
                        # Note: Vh is V^T, so V = Vh^T
                        C = U.T @ noise @ Vh.T
                        
                        # FIXED: Use FULL Frobenius norm, not just diagonal
                        # Total energy = ||C||_F^2
                        total_energy = (C ** 2).sum().item()
                        
                        # Tail energy = ||C[tail_start:, :]||_F^2 (rows corresponding to tail singular values)
                        tail_energy = (C[tail_start:, :] ** 2).sum().item()
                        
                        if total_energy > 1e-10:
                            layer_kappa = tail_energy / total_energy
                            total_kappa += layer_kappa
                            n_layers += 1
                    except Exception:
                        pass
        
        # For isotropic noise, κ_tail should theoretically be ~tail_fraction
        # But we measure it directly when possible
        if n_layers > 0:
            return total_kappa / n_layers
        else:
            return self.tail_fraction  # Fallback to theoretical value
    
    def _inject_wavelet_noise(self, model: 'GrokMLP', device: str, noise_scale: float) -> float:
        """Inject wavelet-shaped noise in SVD space."""
        total_kappa = 0.0
        n_layers = 0
        
        with torch.no_grad():
            for name, param in model.named_parameters():
                if param.dim() != 2:
                    noise = torch.randn_like(param) * noise_scale
                    param.add_(noise)
                    continue
                
                W = param.data
                try:
                    U, S, Vh = torch.linalg.svd(W, full_matrices=False)
                except Exception:
                    noise = torch.randn_like(param) * noise_scale
                    param.add_(noise)
                    continue
                
                n_sv = len(S)
                
                # Hermite-Gaussian weights
                u = np.linspace(0, 1, n_sv)
                weights = hermite_gaussian_weight(u, self.wavelet_a, self.wavelet_b)
                weights_tensor = torch.from_numpy(weights).float().to(device)
                
                # Generate noise in SVD space
                Z = torch.randn(n_sv, device=device) * weights_tensor * noise_scale
                
                # Reconstruct: ΔW = U @ diag(Z) @ Vh
                delta_W = (U * Z.unsqueeze(0)) @ Vh
                param.add_(delta_W)
                
                # Compute κ_tail
                tail_start = int(n_sv * (1 - self.tail_fraction))
                tail_mask = torch.zeros(n_sv, device=device)
                tail_mask[tail_start:] = 1.0
                
                layer_kappa = compute_spectral_coupling_tail(Z, tail_mask)
                total_kappa += layer_kappa
                n_layers += 1
        
        return total_kappa / n_layers if n_layers > 0 else 0.5
    
    def _inject_hybrid_noise(self, model: 'GrokMLP', device: str, noise_scale: float) -> float:
        """
        Inject hybrid noise: sqrt(λ) × wavelet + sqrt(1-λ) × isotropic
        
        This preserves rank (isotropic) while improving coupling (wavelet).
        """
        lam = self.current_lambda
        wavelet_scale = math.sqrt(lam) * noise_scale
        iso_scale = math.sqrt(1 - lam) * noise_scale
        
        total_kappa = 0.0
        n_layers = 0
        
        with torch.no_grad():
            for name, param in model.named_parameters():
                if param.dim() != 2:
                    # 1D params: just isotropic
                    noise = torch.randn_like(param) * noise_scale
                    param.add_(noise)
                    continue
                
                W = param.data
                try:
                    U, S, Vh = torch.linalg.svd(W, full_matrices=False)
                except Exception:
                    noise = torch.randn_like(param) * noise_scale
                    param.add_(noise)
                    continue
                
                n_sv = len(S)
                
                # Isotropic component (in weight space)
                noise_iso = torch.randn_like(param) * iso_scale
                
                # Wavelet component (in SVD space)
                u = np.linspace(0, 1, n_sv)
                weights = hermite_gaussian_weight(u, self.wavelet_a, self.wavelet_b)
                weights_tensor = torch.from_numpy(weights).float().to(device)
                
                Z_wavelet = torch.randn(n_sv, device=device) * weights_tensor * wavelet_scale
                noise_wavelet = (U * Z_wavelet.unsqueeze(0)) @ Vh
                
                # Combined noise
                total_noise = noise_iso + noise_wavelet
                param.add_(total_noise)
                
                # Compute combined κ_tail
                try:
                    # Project total noise to SVD space
                    noise_svd_coeffs = torch.diag(U.T @ total_noise @ Vh.T)
                    
                    tail_start = int(n_sv * (1 - self.tail_fraction))
                    tail_mask = torch.zeros(n_sv, device=device)
                    tail_mask[tail_start:] = 1.0
                    
                    layer_kappa = compute_spectral_coupling_tail(noise_svd_coeffs, tail_mask)
                    total_kappa += layer_kappa
                    n_layers += 1
                except Exception:
                    pass
        
        return total_kappa / n_layers if n_layers > 0 else lam * 0.6 + (1 - lam) * self.tail_fraction
    
    def get_summary(self) -> Dict:
        return {
            'delta': self.delta,
            'initial_distance': self.initial_distance,
            'M_explore': self.M_explore,
            'M_nominal_final': self.M_nominal,
            'M_effective_tail_final': self.M_effective_tail,
            'M_effective_contract_final': self.M_effective_contract,
            'kappa_tail_average': np.mean(self.kappa_tail_history) if self.kappa_tail_history else 0.0,
            'kappa_contract_average': np.mean(self.kappa_contract_history) if self.kappa_contract_history else 0.0,
            'noise_mode': self.noise_mode,
            'trigger_mode': self.trigger_mode,
            'injection_count': self.injection_count,
            'rank_violations': self.rank_violations,
            'peak_eff_rank': self.peak_eff_rank,
            'anneal_start_epoch': self.anneal_start_epoch,
            'quench_triggered_epoch': self.quench_triggered_epoch,
            'phase_history': self.phase_history,
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
    defect: DefectMeasurement


def analyze_layer_spectrum(name: str, weight_matrix: torch.Tensor, k: Optional[int] = None) -> LayerSpectrum:
    W = weight_matrix.detach().cpu().float()
    
    try:
        S = torch.linalg.svdvals(W)
    except Exception:
        return LayerSpectrum(
            name=name,
            eigenvalues=torch.tensor([1.0]),
            effective_rank=1.0,
            spectral_entropy=0.0,
            top_eigenvalue=1.0,
            defect=DefectMeasurement(epsilon=1.0, k_coarse=1, tail_energy=1.0, total_energy=1.0)
        )
    
    return LayerSpectrum(
        name=name,
        eigenvalues=S,
        effective_rank=compute_effective_rank(W),
        spectral_entropy=compute_spectral_entropy(W),
        top_eigenvalue=S[0].item() if len(S) > 0 else 0.0,
        defect=compute_defect(W, k)
    )


# ═══════════════════════════════════════════════════════════════════════════════
# EVENT TRACKING
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class EventTracker:
    initial_eff_rank: float = 0.0
    peak_eff_rank: float = 0.0
    first_rank_collapse_epoch: int = -1
    rank_collapse_threshold: float = 0.7
    anneal_epoch: int = -1
    quench_epoch: int = -1
    M_nominal_at_anneal: float = 0.0
    M_effective_tail_at_anneal: float = 0.0
    M_effective_contract_at_anneal: float = 0.0
    epsilon_at_anneal: float = 0.0
    grokking_epoch: int = -1


# ═══════════════════════════════════════════════════════════════════════════════
# CSV LOGGING
# ═══════════════════════════════════════════════════════════════════════════════

class CSVLogger:
    def __init__(self, filepath: str):
        self.filepath = filepath
        self.file = None
        self.writer = None
        
    def __enter__(self):
        self.file = open(self.filepath, 'w', newline='')
        return self
        
    def __exit__(self, *args):
        if self.file:
            self.file.close()
    
    def write_header(self, fieldnames: List[str]):
        self.writer = csv.DictWriter(self.file, fieldnames=fieldnames)
        self.writer.writeheader()
    
    def write_row(self, row: Dict):
        if self.writer:
            self.writer.writerow(row)
            self.file.flush()


# ═══════════════════════════════════════════════════════════════════════════════
# TRAINING FUNCTION
# ═══════════════════════════════════════════════════════════════════════════════

def train_phase6_1(
    model: GrokMLP,
    train_loader: DataLoader,
    test_loader: DataLoader,
    controller: CorrectedWaveletController,
    optimizer: torch.optim.AdamW,
    epochs: int,
    device: str,
    writer: SummaryWriter,
    csv_logger: CSVLogger,
    grokking_threshold: float = 0.99,
    tomography_interval: int = 100,
) -> Tuple[Dict, EventTracker]:
    """Train with Phase-6.1 corrected controller."""
    
    model.to(device)
    criterion = nn.CrossEntropyLoss()
    
    tracker = EventTracker()
    
    # CSV header - note separation of kappa_tail and kappa_contract
    csv_fields = [
        'epoch', 'train_loss', 'train_acc', 'test_acc',
        'epsilon', 'hidden_eff_rank', 'hidden_entropy', 'hidden_k',
        'M_explore', 'M_nominal', 'M_eff_tail', 'M_eff_contract',
        'kappa_tail', 'kappa_contract', 'lambda_hybrid',
        'peak_eff_rank', 'rank_violations', 'phase', 'weight_decay',
        'injection_count'
    ]
    csv_logger.write_header(csv_fields)
    
    # Estimate heat epochs for lambda schedule
    heat_epochs_estimate = int(controller.M_explore / controller.calibrated_kappa / controller.noise_scale)
    
    prev_epsilon = 1.0  # For κ_contract calculation
    
    for epoch in range(1, epochs + 1):
        # Training step
        model.train()
        train_loss = 0.0
        train_correct = 0
        train_total = 0
        
        for x, y in train_loader:
            x, y = x.to(device), y.to(device)
            
            optimizer.zero_grad()
            out = model(x)
            loss = criterion(out, y)
            loss.backward()
            optimizer.step()
            
            train_loss += loss.item() * x.size(0)
            train_correct += (out.argmax(dim=1) == y).sum().item()
            train_total += x.size(0)
        
        train_loss /= train_total
        train_acc = train_correct / train_total
        
        # CRITICAL FIX: Inject noise EVERY EPOCH during heat/anneal
        if controller.current_phase in ['heat', 'anneal']:
            controller.inject_noise(model, device, epoch, heat_epochs_estimate)
        
        # Test accuracy
        model.eval()
        test_correct = 0
        test_total = 0
        
        with torch.no_grad():
            for x, y in test_loader:
                x, y = x.to(device), y.to(device)
                out = model(x)
                test_correct += (out.argmax(dim=1) == y).sum().item()
                test_total += x.size(0)
        
        test_acc = test_correct / test_total
        
        # Spectral analysis at intervals
        if epoch % tomography_interval == 0 or epoch == 1:
            weights = model.get_layer_weights()
            hidden_spectrum = analyze_layer_spectrum('hidden_1', weights['hidden_1'])
            
            # Track initial effective rank
            if epoch == 1:
                tracker.initial_eff_rank = hidden_spectrum.effective_rank
                tracker.peak_eff_rank = hidden_spectrum.effective_rank
            
            if hidden_spectrum.effective_rank > tracker.peak_eff_rank:
                tracker.peak_eff_rank = hidden_spectrum.effective_rank
            
            # Track rank collapse
            if (tracker.first_rank_collapse_epoch < 0 and 
                hidden_spectrum.effective_rank < tracker.rank_collapse_threshold * tracker.peak_eff_rank):
                tracker.first_rank_collapse_epoch = epoch
            
            # Update κ_contract based on observed epsilon change (uses accumulated eta)
            if controller.current_phase in ['heat', 'anneal']:
                controller.update_kappa_contract(hidden_spectrum.defect.epsilon)
            
            # Update controller
            new_wd, phase = controller.update(
                epoch,
                hidden_spectrum.defect.epsilon,
                hidden_spectrum.effective_rank
            )
            
            # Update optimizer weight decay
            for param_group in optimizer.param_groups:
                param_group['weight_decay'] = new_wd
            
            # Track anneal/quench events
            if controller.anneal_start_epoch == epoch:
                tracker.anneal_epoch = epoch
                tracker.M_nominal_at_anneal = controller.M_nominal
                tracker.M_effective_tail_at_anneal = controller.M_effective_tail
                tracker.M_effective_contract_at_anneal = controller.M_effective_contract
                tracker.epsilon_at_anneal = hidden_spectrum.defect.epsilon
            
            if controller.quench_triggered_epoch == epoch:
                tracker.quench_epoch = epoch
            
            # TensorBoard logging
            writer.add_scalar('Loss/train', train_loss, epoch)
            writer.add_scalar('Accuracy/train', train_acc, epoch)
            writer.add_scalar('Accuracy/test', test_acc, epoch)
            writer.add_scalar('Spectral/epsilon', hidden_spectrum.defect.epsilon, epoch)
            writer.add_scalar('Spectral/effective_rank', hidden_spectrum.effective_rank, epoch)
            writer.add_scalar('Controller/M_nominal', controller.M_nominal, epoch)
            writer.add_scalar('Controller/M_eff_tail', controller.M_effective_tail, epoch)
            writer.add_scalar('Controller/M_eff_contract', controller.M_effective_contract, epoch)
            writer.add_scalar('Controller/kappa_tail', controller.kappa_tail, epoch)
            writer.add_scalar('Controller/kappa_contract', controller.kappa_contract, epoch)
            writer.add_scalar('Controller/lambda', controller.current_lambda, epoch)
            writer.add_scalar('Controller/weight_decay', new_wd, epoch)
            
            # CSV logging
            csv_logger.write_row({
                'epoch': epoch,
                'train_loss': train_loss,
                'train_acc': train_acc,
                'test_acc': test_acc,
                'epsilon': hidden_spectrum.defect.epsilon,
                'hidden_eff_rank': hidden_spectrum.effective_rank,
                'hidden_entropy': hidden_spectrum.spectral_entropy,
                'hidden_k': hidden_spectrum.defect.k_coarse,
                'M_explore': controller.M_explore,
                'M_nominal': controller.M_nominal,
                'M_eff_tail': controller.M_effective_tail,
                'M_eff_contract': controller.M_effective_contract,
                'kappa_tail': controller.kappa_tail,
                'kappa_contract': controller.kappa_contract,
                'lambda_hybrid': controller.current_lambda,
                'peak_eff_rank': tracker.peak_eff_rank,
                'rank_violations': controller.rank_violations,
                'phase': phase,
                'weight_decay': new_wd,
                'injection_count': controller.injection_count,
            })
            
            # Console output
            print(f"Epoch {epoch:5d}: loss={train_loss:.4f}, train={train_acc*100:.1f}%, "
                  f"test={test_acc*100:.1f}% | M={controller.M_nominal:.1f}, "
                  f"k_t={controller.kappa_tail:.3f}, k_c={controller.kappa_contract:.3f} | {phase}")
        
        # Check for grokking and signal to controller
        if test_acc >= grokking_threshold and tracker.grokking_epoch < 0:
            tracker.grokking_epoch = epoch
            controller.signal_grokking(epoch, test_acc)
            print(f"\n*** GROKKING ACHIEVED at epoch {epoch}! ***\n")
    
    return controller.get_summary(), tracker


# ═══════════════════════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════════════════════

def main():
    parser = argparse.ArgumentParser(description='SGC Phase-6.1: Corrected Wavelet-Coupled Controller')
    
    # Task
    parser.add_argument('--task', type=str, default='add', choices=['add', 'mult'])
    parser.add_argument('--p', type=int, default=97)
    
    # Model
    parser.add_argument('--hidden_dim', type=int, default=128)
    
    # Training
    parser.add_argument('--epochs', type=int, default=10000)
    parser.add_argument('--batch_size', type=int, default=32)
    parser.add_argument('--lr', type=float, default=1e-3)
    parser.add_argument('--weight_decay', type=float, default=1.0)
    
    # Phase-6.1 parameters
    parser.add_argument('--delta', type=float, default=0.1)
    parser.add_argument('--initial_distance', type=float, default=1.0)
    parser.add_argument('--noise_scale', type=float, default=0.1)
    parser.add_argument('--noise_mode', type=str, default='hybrid',
                        choices=['isotropic', 'wavelet', 'hybrid'])
    parser.add_argument('--trigger_mode', type=str, default='effective_contract',
                        choices=['nominal', 'effective_tail', 'effective_contract', 'calibrated'])
    parser.add_argument('--calibrated_kappa', type=float, default=0.01)
    
    # Hybrid parameters
    parser.add_argument('--lambda_start', type=float, default=0.2)
    parser.add_argument('--lambda_end', type=float, default=0.8)
    
    # Wavelet parameters
    parser.add_argument('--wavelet_a', type=float, default=1.0)
    parser.add_argument('--wavelet_b', type=float, default=2.0)
    parser.add_argument('--tail_fraction', type=float, default=0.5)
    
    # Anneal parameters
    parser.add_argument('--anneal_epochs', type=int, default=500)
    parser.add_argument('--noise_floor', type=float, default=0.01)
    
    # Weight decay schedule
    parser.add_argument('--wd_heat', type=float, default=0.1)
    parser.add_argument('--wd_quench', type=float, default=2.0)
    
    # Safety
    parser.add_argument('--min_exploration_mass', type=float, default=1.0)
    parser.add_argument('--max_exploration_mass', type=float, default=500.0)
    parser.add_argument('--rank_floor_fraction', type=float, default=0.6)
    
    # Logging
    parser.add_argument('--tomography_interval', type=int, default=100)
    parser.add_argument('--grokking_threshold', type=float, default=0.99)
    parser.add_argument('--seed', type=int, default=42)
    
    args = parser.parse_args()
    
    # Setup
    torch.manual_seed(args.seed)
    np.random.seed(args.seed)
    device = 'cuda' if torch.cuda.is_available() else 'cpu'
    
    print("=" * 70)
    print("SGC PHASE-6.1: CORRECTED WAVELET-COUPLED CONTROLLER")
    print("FIXES: per-epoch injection, kappa_tail vs kappa_contract, hybrid noise, soft anneal")
    print("=" * 70)
    print()
    
    if torch.cuda.is_available():
        print(f"GPU: {torch.cuda.get_device_name(0)}")
    
    # Create datasets
    train_dataset = ModularAdditionDataset(args.p, train=True, seed=args.seed)
    test_dataset = ModularAdditionDataset(args.p, train=False, seed=args.seed)
    
    train_loader = DataLoader(train_dataset, batch_size=args.batch_size, shuffle=True)
    test_loader = DataLoader(test_dataset, batch_size=args.batch_size)
    
    print(f"\nConfiguration:")
    print(f"  Task: {args.task} mod {args.p}")
    print(f"  Hidden dim: {args.hidden_dim}")
    print(f"  Epochs: {args.epochs}, LR: {args.lr}, WD: {args.weight_decay}")
    
    M_explore = math.log(args.initial_distance / args.delta)
    print(f"\nPhase-6.1 Parameters:")
    print(f"  M_explore = log({args.initial_distance}/{args.delta}) = {M_explore:.4f}")
    print(f"  noise_mode: {args.noise_mode}")
    if args.noise_mode == 'hybrid':
        print(f"  lambda schedule: {args.lambda_start} -> {args.lambda_end}")
    print(f"  trigger_mode: {args.trigger_mode}")
    print(f"  anneal_epochs: {args.anneal_epochs}")
    print(f"  noise_floor: {args.noise_floor}")
    print(f"  WD schedule: heat={args.wd_heat}, quench={args.wd_quench}")
    print(f"  rank_floor: {args.rank_floor_fraction * 100:.0f}% of peak")
    print(f"  Seed: {args.seed}")
    
    print(f"\nDataset: {len(train_dataset)} train, {len(test_dataset)} test")
    
    # Create model
    model = GrokMLP(args.p, args.hidden_dim)
    print(f"Model parameters: {sum(p.numel() for p in model.parameters()):,}")
    
    # Create controller
    controller = CorrectedWaveletController(
        delta=args.delta,
        initial_distance=args.initial_distance,
        wd_heat=args.wd_heat,
        wd_quench=args.wd_quench,
        wd_baseline=args.weight_decay,
        noise_scale=args.noise_scale,
        noise_mode=args.noise_mode,
        lambda_start=args.lambda_start,
        lambda_end=args.lambda_end,
        wavelet_a=args.wavelet_a,
        wavelet_b=args.wavelet_b,
        tail_fraction=args.tail_fraction,
        anneal_epochs=args.anneal_epochs,
        noise_floor=args.noise_floor,
        train_size=len(train_dataset),
        batch_size=args.batch_size,
        lr=args.lr,
        trigger_mode=args.trigger_mode,
        calibrated_kappa=args.calibrated_kappa,
        min_exploration_mass=args.min_exploration_mass,
        max_exploration_mass=args.max_exploration_mass,
        rank_floor_fraction=args.rank_floor_fraction,
    )
    
    # Create optimizer
    optimizer = torch.optim.AdamW(model.parameters(), lr=args.lr, weight_decay=args.weight_decay)
    
    # Setup logging
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    log_dir = f'logs/phase6_1/run_{timestamp}'
    os.makedirs(log_dir, exist_ok=True)
    
    writer = SummaryWriter(log_dir)
    
    # Train
    print(f"\nTraining for {args.epochs} epochs with CORRECTED WAVELET CONTROLLER...")
    print(f"  noise_mode = {args.noise_mode}")
    print(f"  trigger_mode = {args.trigger_mode}")
    print("-" * 70)
    
    with CSVLogger(f'{log_dir}/metrics.csv') as csv_logger:
        summary, tracker = train_phase6_1(
            model=model,
            train_loader=train_loader,
            test_loader=test_loader,
            controller=controller,
            optimizer=optimizer,
            epochs=args.epochs,
            device=device,
            writer=writer,
            csv_logger=csv_logger,
            grokking_threshold=args.grokking_threshold,
            tomography_interval=args.tomography_interval,
        )
    
    writer.close()
    
    print(f"\nMetrics saved to {log_dir}/metrics.csv")
    
    # Print summary
    print("\n" + "=" * 70)
    print("PHASE-6.1 CORRECTED CONTROLLER SUMMARY")
    print("=" * 70)
    print(f"  Initial hidden eff-rank: {tracker.initial_eff_rank:.2f}")
    print(f"  Peak eff-rank: {tracker.peak_eff_rank:.2f}")
    print(f"  First rank collapse (70%): epoch {tracker.first_rank_collapse_epoch}")
    print(f"  Anneal epoch: {tracker.anneal_epoch}")
    if tracker.anneal_epoch > 0:
        print(f"    M_nominal at anneal: {tracker.M_nominal_at_anneal:.4f}")
        print(f"    M_eff_tail at anneal: {tracker.M_effective_tail_at_anneal:.4f}")
        print(f"    M_eff_contract at anneal: {tracker.M_effective_contract_at_anneal:.4f}")
    print(f"  Quench epoch: {tracker.quench_epoch}")
    print(f"  Total noise injections: {summary['injection_count']}")
    print(f"  Rank floor violations: {summary['rank_violations']}")
    print(f"  Final M_nominal: {summary['M_nominal_final']:.4f}")
    print(f"  Average kappa_tail: {summary['kappa_tail_average']:.4f}")
    print(f"  Average kappa_contract: {summary['kappa_contract_average']:.4f}")
    print(f"  Grokking epoch: {tracker.grokking_epoch}")
    
    if tracker.anneal_epoch > 0 and tracker.grokking_epoch > 0:
        print(f"  Epochs from anneal to grokking: {tracker.grokking_epoch - tracker.anneal_epoch}")
    
    print("\n" + "=" * 70)
    print("PHASE-6.1 EXPERIMENT COMPLETE")
    print("=" * 70)


if __name__ == '__main__':
    main()
