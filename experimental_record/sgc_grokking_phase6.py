#!/usr/bin/env python3
"""
SGC Phase-6: Wavelet-Coupled Exploration Mass Controller
=========================================================

Phase-5.1 discovered: Exploration mass M = Σηₜ provides a principled quench trigger,
but required M ≈ 200 vs theoretical M_explore ≈ 2.3 (87× gap).

Phase-6 BREAKTHROUGH: The gap reveals κ ≈ 0.01 coupling efficiency—only 1% of 
injected noise couples to the loss-relevant subspace.

THE KEY INSIGHT (ExplorationMassCoupled.lean):
    - Effective exploration mass: M_eff = Σ κₜηₜ (coupling-weighted)
    - With coupling efficiency κ: threshold becomes M ≥ (1/κ) × log(d₀/δ)
    - The 87× gap IS the coupling coefficient: κ = 2.3/200 ≈ 0.01

WAVELET-SHAPED NOISE (the innovation):
    - Replace isotropic noise with SVD-spectrally-shaped noise
    - Target high-rank (tail) singular components that maintain representation capacity
    - This "spectral matching" should increase κ, reducing total M needed

THEORETICAL FOUNDATION (Proven in Lean):
    1. coupled_contraction_product_bound: ∏(1-κᵢηᵢ) ≤ exp(-Σκᵢηᵢ)
    2. coupled_mixing_bound: distance ≤ exp(-M_eff) × d₀  
    3. inefficient_mixing_threshold: M ≥ (1/κ) × log(d₀/δ)
    4. controller_correctness_constant_alpha: executable safety guarantee

EXPERIMENTAL DESIGN:
    A) Baseline: isotropic noise, trigger on M = Σηₜ
    B) κ-only: isotropic noise, trigger on M_eff = Σκₜηₜ  
    C) Wavelet-coupled: spectral noise, trigger on M_eff

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
# DATASETS (same as Phase-5)
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
# ARCHITECTURE (same as Phase-5)
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
# DEFECT MEASUREMENT
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
    
    This shapes noise injection to target specific spectral bands.
    
    Args:
        u: Normalized scale coordinates (0 to 1, where 0 = largest singular value)
        a: Power parameter (a=0 for Gaussian, a>0 shifts weight toward higher scales)
        b: Decay parameter (larger b = more localized in scale)
    
    Returns:
        Weights for each scale
    """
    # Shift u to avoid singularity at 0 for a > 0
    u_shifted = u + 0.01
    weights = (u_shifted ** a) * np.exp(-b * u_shifted ** 2)
    
    # Normalize to unit energy
    norm = np.sqrt(np.sum(weights ** 2))
    if norm > 1e-10:
        weights = weights / norm
    
    return weights


def compute_spectral_coupling(noise_projection: torch.Tensor, tail_mask: torch.Tensor) -> float:
    """
    Compute coupling coefficient kappa: fraction of noise energy in relevant subspace.
    
    kappa = ||noise in tail||^2 / ||noise||^2
    
    For rank-preservation, "relevant" = tail (high-rank) components.
    """
    noise_energy = (noise_projection ** 2).sum().item()
    if noise_energy < 1e-10:
        return 0.0
    
    tail_energy = ((noise_projection * tail_mask) ** 2).sum().item()
    return tail_energy / noise_energy


# ═══════════════════════════════════════════════════════════════════════════════
# PHASE-6: WAVELET-COUPLED EXPLORATION MASS CONTROLLER
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class WaveletCoupledController:
    """
    Phase-6 Controller: Wavelet-coupled exploration mass with kappa tracking.
    
    KEY INNOVATIONS:
    1. Track effective mass M_eff = Σ κₜηₜ (coupling-weighted)
    2. Wavelet-shaped noise injection targeting high-rank components
    3. Frame tightness audit for measurement transparency
    
    THEORETICAL FOUNDATION (ExplorationMassCoupled.lean):
    - coupled_mixing_bound: distance ≤ exp(-M_eff) × d₀
    - inefficient_mixing_threshold: M ≥ (1/κ) × log(d₀/δ)
    """
    
    # Mixing parameters
    delta: float = 0.1          # Target tolerance
    initial_distance: float = 1.0   # d₀
    
    # Weight decay schedule
    wd_heat: float = 0.1
    wd_quench: float = 2.0
    wd_baseline: float = 1.0
    
    # Noise injection
    noise_scale: float = 0.1    # Base noise strength η
    noise_mode: str = 'wavelet'  # 'isotropic', 'wavelet', 'tail_only'
    
    # Wavelet parameters (Hermite-Gaussian)
    wavelet_a: float = 1.0      # Power parameter (higher = more tail-weighted)
    wavelet_b: float = 2.0      # Decay parameter
    tail_fraction: float = 0.5  # Fraction of spectrum considered "tail"
    
    # Optimizer info (for tau_opt)
    train_size: int = 2822
    batch_size: int = 32
    lr: float = 0.001
    
    # Computed constants
    tau_opt_const: float = field(init=False)
    M_explore: float = field(init=False)  # Uncoupled threshold
    
    # EXPLORATION MASS TRACKING
    M_nominal: float = 0.0      # Nominal mass: Σηₜ
    M_effective: float = 0.0    # Effective mass: Σκₜηₜ
    kappa_history: List[float] = field(default_factory=list)
    kappa_ema: float = 0.01     # EMA of coupling coefficient
    kappa_ema_alpha: float = 0.1
    
    # Trigger mode
    trigger_mode: str = 'effective'  # 'nominal', 'effective', 'calibrated'
    calibrated_kappa: float = 0.01   # Constant κ for calibrated mode
    
    # Safety bounds
    min_exploration_mass: float = 1.0
    max_exploration_mass: float = 500.0
    
    # Observables for logging
    epsilon_history: deque = field(default_factory=lambda: deque(maxlen=50))
    eff_rank_history: deque = field(default_factory=lambda: deque(maxlen=50))
    peak_eff_rank: float = 0.0
    
    # Frame audit
    frame_tightness_ratio: float = 1.0  # B/A ratio (1.0 = tight frame)
    audit_tolerance: float = 0.1
    
    # State
    current_phase: str = 'heat'
    quench_triggered_epoch: int = -1
    current_epsilon: float = 1.0
    current_eff_rank: float = 0.0
    current_kappa: float = 0.01
    prev_update_epoch: int = 0
    
    # History
    phase_history: List[Tuple[int, str, float]] = field(default_factory=list)
    mass_history: List[Tuple[int, float, float, float]] = field(default_factory=list)  # (epoch, M_nom, M_eff, kappa)
    
    # Cached SVD for noise shaping
    _cached_U: Optional[torch.Tensor] = None
    _cached_S: Optional[torch.Tensor] = None
    _cached_Vh: Optional[torch.Tensor] = None
    
    def __post_init__(self):
        """Initialize controller constants."""
        # Markov time per epoch
        updates_per_epoch = math.ceil(self.train_size / self.batch_size)
        eta_eff = self.lr / (1.0 + self.wd_baseline)
        self.tau_opt_const = updates_per_epoch * eta_eff
        
        # Uncoupled exploration mass threshold
        self.M_explore = math.log(self.initial_distance / self.delta)
        
        print(f"[WaveletCoupledController] Initialized:")
        print(f"    tau_opt_const = {self.tau_opt_const:.6f}")
        print(f"    M_explore (uncoupled) = log({self.initial_distance}/{self.delta}) = {self.M_explore:.4f}")
        print(f"    Calibrated threshold (kappa={self.calibrated_kappa:.3f}): {self.M_explore / self.calibrated_kappa:.1f}")
        print(f"    Noise mode: {self.noise_mode}")
        print(f"    Trigger mode: {self.trigger_mode}")
        print(f"    Safety bounds: [{self.min_exploration_mass}, {self.max_exploration_mass}]")
    
    def _get_trigger_threshold(self) -> float:
        """Get the exploration mass threshold based on trigger mode."""
        if self.trigger_mode == 'nominal':
            # Phase-5.1 style: fixed threshold on nominal mass
            return self.min_exploration_mass
        elif self.trigger_mode == 'effective':
            # Phase-6 style: threshold on effective mass
            return self.M_explore
        elif self.trigger_mode == 'calibrated':
            # Use fixed calibrated kappa
            return self.M_explore / self.calibrated_kappa
        else:
            return self.M_explore
    
    def _get_current_mass(self) -> float:
        """Get the relevant exploration mass for trigger comparison."""
        if self.trigger_mode == 'nominal':
            return self.M_nominal
        elif self.trigger_mode == 'effective':
            return self.M_effective
        elif self.trigger_mode == 'calibrated':
            return self.M_nominal  # Compare nominal to calibrated threshold
        else:
            return self.M_effective
    
    def _is_ready_for_quench(self, debug: bool = False) -> Tuple[bool, str]:
        """Check quench condition based on exploration mass."""
        current_mass = self._get_current_mass()
        threshold = self._get_trigger_threshold()
        
        # Safety upper bound on nominal mass
        force_quench = self.M_nominal >= self.max_exploration_mass
        
        # Primary trigger
        mass_sufficient = current_mass >= threshold
        
        # Safety lower bound
        above_minimum = self.M_nominal >= self.min_exploration_mass
        
        if force_quench:
            return True, "FORCE_MAX"
        elif mass_sufficient and above_minimum:
            return True, f"MASS_THRESHOLD (M={current_mass:.3f} >= {threshold:.3f})"
        elif mass_sufficient and not above_minimum:
            return False, f"WAITING_MIN (M_nom={self.M_nominal:.3f} < min={self.min_exploration_mass})"
        else:
            return False, f"ACCUMULATING (M={current_mass:.3f} < {threshold:.3f}, kappa={self.current_kappa:.4f})"
    
    def update(self, epoch: int, epsilon: float, eff_rank: float = 0.0) -> Tuple[float, str]:
        """Update controller with new measurements."""
        # Track observables
        self.current_epsilon = epsilon
        self.current_eff_rank = eff_rank
        self.epsilon_history.append((epoch, epsilon))
        self.eff_rank_history.append((epoch, eff_rank))
        
        if eff_rank > self.peak_eff_rank:
            self.peak_eff_rank = eff_rank
        
        prev_phase = self.current_phase
        
        if self.current_phase == 'heat':
            # Accumulate exploration mass
            epoch_delta = epoch - self.prev_update_epoch if self.prev_update_epoch > 0 else 1
            
            # Nominal mass: η × Δepoch
            mass_increment_nominal = self.noise_scale * epoch_delta
            self.M_nominal += mass_increment_nominal
            
            # Effective mass: κ × η × Δepoch
            mass_increment_effective = self.current_kappa * self.noise_scale * epoch_delta
            self.M_effective += mass_increment_effective
            
            # Update kappa EMA
            self.kappa_ema = self.kappa_ema_alpha * self.current_kappa + (1 - self.kappa_ema_alpha) * self.kappa_ema
            self.kappa_history.append(self.current_kappa)
            
            # Track history
            self.mass_history.append((epoch, self.M_nominal, self.M_effective, self.current_kappa))
            
            # Debug output
            debug = (epoch % 1000 == 0)
            ready, trigger_reason = self._is_ready_for_quench(debug=debug)
            
            if debug:
                print(f"  [DEBUG] Epoch {epoch}:")
                print(f"    M_nominal = {self.M_nominal:.4f}, M_effective = {self.M_effective:.4f}")
                print(f"    kappa = {self.current_kappa:.4f} (EMA = {self.kappa_ema:.4f})")
                print(f"    Status: {trigger_reason}")
                print(f"    epsilon = {epsilon:.4f}, eff_rank = {eff_rank:.2f}")
            
            if ready:
                self.current_phase = 'quench'
                self.quench_triggered_epoch = epoch
                print(f"\n*** WAVELET-COUPLED QUENCH at epoch {epoch} ***")
                print(f"    M_nominal = {self.M_nominal:.4f}")
                print(f"    M_effective = {self.M_effective:.4f}")
                print(f"    kappa (average) = {np.mean(self.kappa_history):.4f}")
                print(f"    trigger: {trigger_reason}")
                print(f"    eff_rank = {eff_rank:.2f} (peak = {self.peak_eff_rank:.2f})")
        
        self.prev_update_epoch = epoch
        
        if self.current_phase != prev_phase:
            self.phase_history.append((epoch, self.current_phase, epsilon))
        
        if self.current_phase == 'heat':
            return self.wd_heat, 'heat'
        elif self.current_phase == 'quench':
            return self.wd_quench, 'quench'
        else:
            return self.wd_baseline, 'done'
    
    def inject_noise(self, model: 'GrokMLP', device: str = 'cuda'):
        """
        Inject noise during heat phase with optional spectral shaping.
        
        Noise modes:
        - 'isotropic': Standard white noise (Phase-5.1 style)
        - 'wavelet': Hermite-Gaussian weighted in SVD space
        - 'tail_only': Inject only into tail (high-index) singular components
        """
        if self.current_phase != 'heat':
            return
        
        if self.noise_mode == 'isotropic':
            self._inject_isotropic_noise(model, device)
        elif self.noise_mode == 'wavelet':
            self._inject_wavelet_noise(model, device)
        elif self.noise_mode == 'tail_only':
            self._inject_tail_noise(model, device)
        else:
            self._inject_isotropic_noise(model, device)
    
    def _inject_isotropic_noise(self, model: 'GrokMLP', device: str):
        """Inject isotropic (white) noise to all parameters."""
        with torch.no_grad():
            for param in model.parameters():
                noise = torch.randn_like(param) * self.noise_scale
                param.add_(noise)
        
        # Estimate kappa for isotropic noise (typically ~0.01)
        # For isotropic noise, kappa ≈ tail_fraction (fraction in "relevant" subspace)
        self.current_kappa = self.tail_fraction
    
    def _inject_wavelet_noise(self, model: 'GrokMLP', device: str):
        """
        Inject Hermite-Gaussian weighted noise in SVD space.
        
        This shapes noise to target specific spectral bands, increasing coupling
        to the high-rank (tail) components that maintain representation capacity.
        """
        with torch.no_grad():
            total_kappa = 0.0
            n_layers = 0
            
            for name, param in model.named_parameters():
                if param.dim() != 2:
                    # For bias and other 1D params, use isotropic noise
                    noise = torch.randn_like(param) * self.noise_scale
                    param.add_(noise)
                    continue
                
                # Compute SVD
                W = param.data
                try:
                    U, S, Vh = torch.linalg.svd(W, full_matrices=False)
                except Exception:
                    noise = torch.randn_like(param) * self.noise_scale
                    param.add_(noise)
                    continue
                
                n_sv = len(S)
                
                # Compute Hermite-Gaussian weights
                u = np.linspace(0, 1, n_sv)
                weights = hermite_gaussian_weight(u, self.wavelet_a, self.wavelet_b)
                weights_tensor = torch.from_numpy(weights).float().to(device)
                
                # Generate noise in SVD space
                # Z is random coefficients, shaped by wavelet weights
                Z = torch.randn(n_sv, device=device) * weights_tensor * self.noise_scale
                
                # Reconstruct noise in weight space: ΔW = U @ diag(Z) @ Vh
                # For efficiency, use outer product form
                noise_coeffs = Z.unsqueeze(1)  # (n_sv, 1)
                delta_W = (U * noise_coeffs.T) @ Vh
                
                param.add_(delta_W)
                
                # Compute coupling coefficient for this layer
                tail_start = int(n_sv * (1 - self.tail_fraction))
                tail_mask = torch.zeros(n_sv, device=device)
                tail_mask[tail_start:] = 1.0
                
                layer_kappa = compute_spectral_coupling(Z, tail_mask)
                total_kappa += layer_kappa
                n_layers += 1
            
            # Average kappa across layers
            self.current_kappa = total_kappa / n_layers if n_layers > 0 else 0.01
    
    def _inject_tail_noise(self, model: 'GrokMLP', device: str):
        """Inject noise only into tail (high-index) singular components."""
        with torch.no_grad():
            total_kappa = 0.0
            n_layers = 0
            
            for name, param in model.named_parameters():
                if param.dim() != 2:
                    continue
                
                W = param.data
                try:
                    U, S, Vh = torch.linalg.svd(W, full_matrices=False)
                except Exception:
                    continue
                
                n_sv = len(S)
                tail_start = int(n_sv * (1 - self.tail_fraction))
                
                # Generate noise only in tail components
                Z = torch.zeros(n_sv, device=device)
                Z[tail_start:] = torch.randn(n_sv - tail_start, device=device) * self.noise_scale
                
                # Reconstruct
                noise_coeffs = Z.unsqueeze(1)
                delta_W = (U * noise_coeffs.T) @ Vh
                
                param.add_(delta_W)
                
                # Kappa is ~1.0 for tail-only noise
                layer_kappa = 1.0 if tail_start < n_sv else 0.0
                total_kappa += layer_kappa
                n_layers += 1
            
            self.current_kappa = total_kappa / n_layers if n_layers > 0 else 0.5
    
    def audit_frame_tightness(self, model: 'GrokMLP', device: str) -> Tuple[float, bool]:
        """
        Audit frame tightness for measurement transparency.
        
        For a tight frame: A‖f‖² ≤ Σ‖ψⱼf‖² ≤ B‖f‖²
        Tightness ratio = B/A (1.0 = perfectly tight)
        
        Returns (tightness_ratio, passed_audit)
        """
        # Simplified audit: check singular value spread
        W = model.hidden_layer.weight.data
        try:
            S = torch.linalg.svdvals(W)
        except Exception:
            return 1.0, True
        
        S_max = S[0].item()
        S_min = S[-1].item() if S[-1].item() > 1e-10 else 1e-10
        
        # Frame condition number as proxy for tightness
        self.frame_tightness_ratio = S_max / S_min
        
        # Audit passes if ratio is within tolerance of "near-tight"
        passed = self.frame_tightness_ratio < (1.0 / self.audit_tolerance)
        
        return self.frame_tightness_ratio, passed
    
    def get_summary(self) -> Dict:
        return {
            'delta': self.delta,
            'initial_distance': self.initial_distance,
            'M_explore': self.M_explore,
            'M_nominal_final': self.M_nominal,
            'M_effective_final': self.M_effective,
            'kappa_average': np.mean(self.kappa_history) if self.kappa_history else 0.0,
            'kappa_final': self.current_kappa,
            'noise_mode': self.noise_mode,
            'trigger_mode': self.trigger_mode,
            'tau_opt_const': self.tau_opt_const,
            'noise_scale': self.noise_scale,
            'final_epsilon': self.current_epsilon,
            'final_eff_rank': self.current_eff_rank,
            'peak_eff_rank': self.peak_eff_rank,
            'quench_triggered_epoch': self.quench_triggered_epoch,
            'phase_history': self.phase_history,
            'frame_tightness': self.frame_tightness_ratio,
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
    """Compute spectral properties of a weight matrix."""
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
    """Track key events during training."""
    initial_eff_rank: float = 0.0
    peak_eff_rank: float = 0.0
    first_rank_collapse_epoch: int = -1
    rank_collapse_threshold: float = 0.7
    quench_epoch: int = -1
    M_nominal_at_quench: float = 0.0
    M_effective_at_quench: float = 0.0
    kappa_at_quench: float = 0.0
    epsilon_at_quench: float = 0.0
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

def train_phase6(
    model: GrokMLP,
    train_loader: DataLoader,
    test_loader: DataLoader,
    controller: WaveletCoupledController,
    optimizer: torch.optim.AdamW,
    epochs: int,
    device: str,
    writer: SummaryWriter,
    csv_logger: CSVLogger,
    grokking_threshold: float = 0.99,
    tomography_interval: int = 100,
) -> Tuple[Dict, EventTracker]:
    """Train with Phase-6 wavelet-coupled exploration mass controller."""
    
    model.to(device)
    criterion = nn.CrossEntropyLoss()
    
    tracker = EventTracker()
    
    # CSV header
    csv_fields = [
        'epoch', 'train_loss', 'train_acc', 'test_acc',
        'epsilon', 'hidden_eff_rank', 'hidden_entropy', 'hidden_k',
        'M_explore', 'M_nominal', 'M_effective', 'kappa',
        'tau_opt_const', 'peak_eff_rank', 'phase', 'weight_decay',
        'frame_tightness'
    ]
    csv_logger.write_header(csv_fields)
    
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
            hidden_spectrum = analyze_layer_spectrum(
                'hidden_1', weights['hidden_1'],
                k=controller.fixed_k if hasattr(controller, 'fixed_k') else None
            )
            
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
            
            # Update controller
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
            
            # Frame tightness audit
            frame_ratio, audit_passed = controller.audit_frame_tightness(model, device)
            
            # Track quench event
            if controller.quench_triggered_epoch == epoch:
                tracker.quench_epoch = epoch
                tracker.M_nominal_at_quench = controller.M_nominal
                tracker.M_effective_at_quench = controller.M_effective
                tracker.kappa_at_quench = controller.current_kappa
                tracker.epsilon_at_quench = hidden_spectrum.defect.epsilon
            
            # TensorBoard logging
            writer.add_scalar('Loss/train', train_loss, epoch)
            writer.add_scalar('Accuracy/train', train_acc, epoch)
            writer.add_scalar('Accuracy/test', test_acc, epoch)
            writer.add_scalar('Spectral/epsilon', hidden_spectrum.defect.epsilon, epoch)
            writer.add_scalar('Spectral/effective_rank', hidden_spectrum.effective_rank, epoch)
            writer.add_scalar('Spectral/entropy', hidden_spectrum.spectral_entropy, epoch)
            writer.add_scalar('Controller/M_nominal', controller.M_nominal, epoch)
            writer.add_scalar('Controller/M_effective', controller.M_effective, epoch)
            writer.add_scalar('Controller/kappa', controller.current_kappa, epoch)
            writer.add_scalar('Controller/kappa_ema', controller.kappa_ema, epoch)
            writer.add_scalar('Controller/frame_tightness', frame_ratio, epoch)
            
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
                'M_effective': controller.M_effective,
                'kappa': controller.current_kappa,
                'tau_opt_const': controller.tau_opt_const,
                'peak_eff_rank': tracker.peak_eff_rank,
                'phase': phase,
                'weight_decay': new_wd,
                'frame_tightness': frame_ratio,
            })
            
            # Console output
            phase_str = f"phase={phase}"
            print(f"Epoch {epoch:5d}: loss={train_loss:.4f}, train={train_acc*100:.1f}%, "
                  f"test={test_acc*100:.1f}% | M_nom={controller.M_nominal:.3f}, "
                  f"M_eff={controller.M_effective:.3f}, kappa={controller.current_kappa:.4f} | {phase_str}")
        
        # Check for grokking
        if test_acc >= grokking_threshold and tracker.grokking_epoch < 0:
            tracker.grokking_epoch = epoch
            print(f"\n*** GROKKING ACHIEVED at epoch {epoch}! ***\n")
    
    return controller.get_summary(), tracker


# ═══════════════════════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════════════════════

def main():
    parser = argparse.ArgumentParser(description='SGC Phase-6: Wavelet-Coupled Exploration Mass')
    
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
    
    # Phase-6 parameters
    parser.add_argument('--delta', type=float, default=0.1, help='Mixing tolerance')
    parser.add_argument('--initial_distance', type=float, default=1.0, help='d0')
    parser.add_argument('--noise_scale', type=float, default=0.1, help='Base noise strength')
    parser.add_argument('--noise_mode', type=str, default='wavelet',
                        choices=['isotropic', 'wavelet', 'tail_only'])
    parser.add_argument('--trigger_mode', type=str, default='calibrated',
                        choices=['nominal', 'effective', 'calibrated'])
    parser.add_argument('--calibrated_kappa', type=float, default=0.01,
                        help='Fixed kappa for calibrated trigger mode')
    
    # Wavelet parameters
    parser.add_argument('--wavelet_a', type=float, default=1.0)
    parser.add_argument('--wavelet_b', type=float, default=2.0)
    parser.add_argument('--tail_fraction', type=float, default=0.5)
    
    # Weight decay schedule
    parser.add_argument('--wd_heat', type=float, default=0.1)
    parser.add_argument('--wd_quench', type=float, default=2.0)
    
    # Safety bounds
    parser.add_argument('--min_exploration_mass', type=float, default=1.0)
    parser.add_argument('--max_exploration_mass', type=float, default=500.0)
    
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
    print("SGC PHASE-6: WAVELET-COUPLED EXPLORATION MASS CONTROLLER")
    print("Quench trigger: M_eff = sum(kappa_t * eta_t) with spectral matching")
    print("=" * 70)
    print()
    
    if torch.cuda.is_available():
        print(f"GPU: {torch.cuda.get_device_name(0)}")
    
    # Create datasets
    if args.task == 'add':
        train_dataset = ModularAdditionDataset(args.p, train=True, seed=args.seed)
        test_dataset = ModularAdditionDataset(args.p, train=False, seed=args.seed)
    else:
        from sgc_grokking_phase5 import ModularMultiplicationDataset
        train_dataset = ModularMultiplicationDataset(args.p, train=True, seed=args.seed)
        test_dataset = ModularMultiplicationDataset(args.p, train=False, seed=args.seed)
    
    train_loader = DataLoader(train_dataset, batch_size=args.batch_size, shuffle=True)
    test_loader = DataLoader(test_dataset, batch_size=args.batch_size)
    
    print(f"\nConfiguration:")
    print(f"  Task: {args.task} mod {args.p}")
    print(f"  Hidden dim: {args.hidden_dim}")
    print(f"  Epochs: {args.epochs}, LR: {args.lr}, WD: {args.weight_decay}")
    
    print(f"\nPhase-6 Parameters:")
    print(f"  delta (tolerance): {args.delta}")
    print(f"  initial_distance d0: {args.initial_distance}")
    M_explore = math.log(args.initial_distance / args.delta)
    print(f"  M_explore = log(d0/delta) = {M_explore:.4f}")
    print(f"  noise_scale eta: {args.noise_scale}")
    print(f"  noise_mode: {args.noise_mode}")
    print(f"  trigger_mode: {args.trigger_mode}")
    if args.trigger_mode == 'calibrated':
        print(f"  calibrated_kappa: {args.calibrated_kappa}")
        print(f"  Calibrated threshold: {M_explore / args.calibrated_kappa:.1f}")
    print(f"  Safety bounds: [{args.min_exploration_mass}, {args.max_exploration_mass}]")
    print(f"  WD heat={args.wd_heat}, quench={args.wd_quench}")
    print(f"  Seed: {args.seed}")
    
    print(f"\nDataset: {len(train_dataset)} train, {len(test_dataset)} test")
    
    # Create model
    model = GrokMLP(args.p, args.hidden_dim)
    print(f"Model parameters: {sum(p.numel() for p in model.parameters()):,}")
    
    # Create controller
    controller = WaveletCoupledController(
        delta=args.delta,
        initial_distance=args.initial_distance,
        wd_heat=args.wd_heat,
        wd_quench=args.wd_quench,
        wd_baseline=args.weight_decay,
        noise_scale=args.noise_scale,
        noise_mode=args.noise_mode,
        wavelet_a=args.wavelet_a,
        wavelet_b=args.wavelet_b,
        tail_fraction=args.tail_fraction,
        train_size=len(train_dataset),
        batch_size=args.batch_size,
        lr=args.lr,
        trigger_mode=args.trigger_mode,
        calibrated_kappa=args.calibrated_kappa,
        min_exploration_mass=args.min_exploration_mass,
        max_exploration_mass=args.max_exploration_mass,
    )
    
    # Create optimizer
    optimizer = torch.optim.AdamW(model.parameters(), lr=args.lr, weight_decay=args.weight_decay)
    
    # Setup logging
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    log_dir = f'logs/phase6/run_{timestamp}'
    os.makedirs(log_dir, exist_ok=True)
    
    writer = SummaryWriter(log_dir)
    
    # Train
    print(f"\nTraining for {args.epochs} epochs with WAVELET-COUPLED CONTROLLER...")
    print(f"  noise_mode = {args.noise_mode}")
    print(f"  trigger_mode = {args.trigger_mode}")
    print("-" * 70)
    
    with CSVLogger(f'{log_dir}/metrics.csv') as csv_logger:
        summary, tracker = train_phase6(
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
    print("WAVELET-COUPLED EXPLORATION MASS SUMMARY")
    print("=" * 70)
    print(f"  Initial hidden eff-rank: {tracker.initial_eff_rank:.2f}")
    print(f"  Peak eff-rank: {tracker.peak_eff_rank:.2f}")
    print(f"  First rank collapse (70%): epoch {tracker.first_rank_collapse_epoch}")
    print(f"  Quench epoch: {tracker.quench_epoch}")
    if tracker.quench_epoch > 0:
        print(f"    M_nominal at quench: {tracker.M_nominal_at_quench:.4f}")
        print(f"    M_effective at quench: {tracker.M_effective_at_quench:.4f}")
        print(f"    kappa at quench: {tracker.kappa_at_quench:.4f}")
        print(f"    epsilon at quench: {tracker.epsilon_at_quench:.4f}")
    print(f"  Final M_nominal: {summary['M_nominal_final']:.4f}")
    print(f"  Final M_effective: {summary['M_effective_final']:.4f}")
    print(f"  Average kappa: {summary['kappa_average']:.4f}")
    print(f"  Grokking epoch: {tracker.grokking_epoch}")
    if tracker.quench_epoch > 0 and tracker.grokking_epoch > 0:
        print(f"  Epochs from quench to grokking: {tracker.grokking_epoch - tracker.quench_epoch}")
    
    print("\n" + "=" * 70)
    print("PHASE-6 EXPERIMENT COMPLETE")
    print("=" * 70)
    
    # Final report
    print("\nWavelet-Coupled Results:")
    if tracker.quench_epoch > 0:
        print(f"  [OK] Quench at epoch {tracker.quench_epoch}")
        print(f"       noise_mode = {args.noise_mode}")
        print(f"       M_nominal = {tracker.M_nominal_at_quench:.4f}")
        print(f"       M_effective = {tracker.M_effective_at_quench:.4f}")
        print(f"       kappa = {tracker.kappa_at_quench:.4f}")
    else:
        print(f"  [--] No quench within {args.epochs} epochs")
    
    if tracker.grokking_epoch > 0:
        print(f"  [OK] Grokking achieved at epoch {tracker.grokking_epoch}")
        if tracker.quench_epoch > 0:
            print(f"       Quench-to-grokking lag: {tracker.grokking_epoch - tracker.quench_epoch} epochs")
    else:
        print(f"  [--] Grokking not achieved within {args.epochs} epochs")


if __name__ == '__main__':
    main()
