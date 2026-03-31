"""
SGC Engine: Core Defect and Susceptibility Computation
========================================================

Provides the primary sensor interface for SGC measurements:
    - ε (defect): Lumpability defect from SVD tail energy
    - χ_g (susceptibility): Gradient susceptibility near phase transition
    - R (ridge ratio): Stability indicator for fixed point detection

THEORETICAL FOUNDATION (from FunctionalBlanket.lean):
    - defect = ||L - P L P||_op / ||L||_op (operator norm)
    - In practice: defect ≈ √(tail_energy / total_energy) from SVD

Author: SGC Research Team
Date: March 31, 2026
"""

import math
import torch
import torch.nn as nn
from typing import Dict, List, Optional, Tuple
from dataclasses import dataclass, field
from collections import deque


@dataclass
class SGCMetrics:
    """Container for SGC measurements."""
    epsilon: float              # Lumpability defect
    chi_g: float                # Gradient susceptibility
    ridge_ratio: float          # Ridge ratio R (stability indicator)
    k_coarse: int               # Effective rank (coarse-graining dimension)
    spectral_gap: float         # Gap between λ₁ and λ₂
    effective_rank: float       # Participation ratio
    spectral_entropy: float     # Spectral entropy
    grad_norm: float            # ||∇L||
    tail_energy: float          # Energy in spectral tail
    total_energy: float         # Total spectral energy


@dataclass
class DefectMeasurement:
    """Measurement of the Lumpability Defect epsilon."""
    epsilon: float
    k_coarse: int
    tail_energy: float
    total_energy: float


class SGCEngine:
    """
    Core SGC measurement engine.
    
    Provides continuous monitoring of defect, susceptibility, and stability
    metrics for a neural network during training.
    """
    
    def __init__(self, 
                 energy_threshold: float = 0.95,
                 history_length: int = 100,
                 susceptibility_window: int = 20):
        """
        Initialize SGC engine.
        
        Args:
            energy_threshold: Fraction of energy for rank determination (0.95 = 95%)
            history_length: Length of metric history for trend analysis
            susceptibility_window: Window for susceptibility computation
        """
        self.energy_threshold = energy_threshold
        self.history_length = history_length
        self.susceptibility_window = susceptibility_window
        
        # History tracking
        self.epsilon_history: deque = deque(maxlen=history_length)
        self.chi_g_history: deque = deque(maxlen=history_length)
        self.ridge_ratio_history: deque = deque(maxlen=history_length)
        self.grad_history: deque = deque(maxlen=susceptibility_window)
        
        # Current measurements
        self.current_metrics: Optional[SGCMetrics] = None
        self.step_count = 0
    
    def compute_defect(self, weight_matrix: torch.Tensor, 
                       k: Optional[int] = None) -> DefectMeasurement:
        """
        Compute lumpability defect using SVD tail energy.
        
        defect = √(tail_energy / total_energy)
        
        where tail = singular values beyond the k-th (95% energy threshold).
        """
        W = weight_matrix.detach().cpu().float()
        
        try:
            U, S, Vh = torch.linalg.svd(W, full_matrices=False)
        except Exception:
            return DefectMeasurement(epsilon=1.0, k_coarse=1, 
                                     tail_energy=1.0, total_energy=1.0)
        
        S_squared = S ** 2
        total_energy = S_squared.sum().item()
        
        if total_energy < 1e-10:
            return DefectMeasurement(epsilon=1.0, k_coarse=1, 
                                     tail_energy=0.0, total_energy=total_energy)
        
        if k is None:
            cumsum = torch.cumsum(S_squared, dim=0)
            threshold = self.energy_threshold * total_energy
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
    
    def compute_effective_rank(self, weight_matrix: torch.Tensor) -> float:
        """
        Compute effective rank from singular value entropy.
        
        d_eff = exp(H) where H = -Σ p_i log(p_i) and p_i = σ_i² / Σσ_j²
        """
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
    
    def compute_spectral_gap(self, weight_matrix: torch.Tensor) -> float:
        """
        Compute spectral gap: (σ₁ - σ₂) / σ₁
        
        Large gap indicates well-separated principal components.
        """
        W = weight_matrix.detach().cpu().float()
        
        try:
            S = torch.linalg.svdvals(W)
        except Exception:
            return 0.0
        
        if len(S) < 2:
            return 0.0
        
        if S[0].item() < 1e-10:
            return 0.0
        
        return (S[0] - S[1]).item() / S[0].item()
    
    def compute_susceptibility(self, model: nn.Module, 
                               loss: Optional[torch.Tensor] = None) -> float:
        """
        Compute gradient susceptibility χ_g.
        
        χ_g measures how sensitive the gradient is to small perturbations,
        which peaks at phase transitions (grokking).
        
        χ_g = Var(||∇L||) / E[||∇L||]² over recent history
        
        Note: This uses existing gradients from the model (after backward has been called).
        """
        # Use existing gradients (don't call backward again)
        grad_norm = 0.0
        for p in model.parameters():
            if p.grad is not None:
                grad_norm += p.grad.data.norm(2).item() ** 2
        grad_norm = math.sqrt(grad_norm)
        
        if grad_norm < 1e-10:
            # No gradients available
            return 0.0
        
        self.grad_history.append(grad_norm)
        
        if len(self.grad_history) < 5:
            return 0.0
        
        grads = list(self.grad_history)
        mean = sum(grads) / len(grads)
        
        if mean < 1e-10:
            return 0.0
        
        variance = sum((g - mean) ** 2 for g in grads) / len(grads)
        chi_g = variance / (mean ** 2)
        
        return chi_g
    
    def compute_ridge_ratio(self, model: nn.Module,
                            dataloader: torch.utils.data.DataLoader,
                            device: str = 'cuda',
                            n_samples: int = 100) -> float:
        """
        Compute ridge ratio R = λ_max(H) / λ_min(H).
        
        R ≈ 1 indicates a well-conditioned Hessian, signaling stable fixed point.
        R >> 1 indicates ill-conditioning (still exploring).
        
        Uses gradient covariance as Hessian proxy.
        """
        model.eval()
        gradients = []
        
        n_collected = 0
        for x, y in dataloader:
            if n_collected >= n_samples:
                break
            x, y = x.to(device), y.to(device)
            
            for i in range(min(len(x), n_samples - n_collected)):
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
                    gradients.append(torch.cat(g).detach().cpu())
                n_collected += 1
        
        model.train()
        
        if len(gradients) < 10:
            return 100.0  # High ratio = unstable
        
        G = torch.stack(gradients)
        
        try:
            S = torch.linalg.svdvals(G)
            if len(S) < 2:
                return 100.0
            
            lambda_max = S[0].item() ** 2
            # Use median instead of min for stability
            lambda_med = S[len(S)//2].item() ** 2
            
            if lambda_med < 1e-10:
                return 100.0
            
            return lambda_max / lambda_med
        except Exception:
            return 100.0
    
    def measure(self, model: nn.Module,
                loss: Optional[torch.Tensor] = None,
                dataloader: Optional[torch.utils.data.DataLoader] = None,
                device: str = 'cuda',
                target_layer: str = 'hidden') -> SGCMetrics:
        """
        Compute all SGC metrics for current model state.
        
        Args:
            model: Neural network
            loss: Current loss tensor (for susceptibility)
            dataloader: Data loader (for ridge ratio)
            device: Computation device
            target_layer: Layer name pattern for defect computation
            
        Returns:
            SGCMetrics with all measurements
        """
        self.step_count += 1
        
        # Find target weight matrix
        target_weight = None
        for name, param in model.named_parameters():
            if target_layer in name and 'weight' in name:
                target_weight = param
                break
        
        if target_weight is None:
            # Fallback: use first weight matrix found
            for name, param in model.named_parameters():
                if 'weight' in name and len(param.shape) == 2:
                    target_weight = param
                    break
        
        if target_weight is None:
            return SGCMetrics(
                epsilon=1.0, chi_g=0.0, ridge_ratio=100.0, k_coarse=1,
                spectral_gap=0.0, effective_rank=1.0, spectral_entropy=0.0,
                grad_norm=0.0, tail_energy=1.0, total_energy=1.0
            )
        
        # Compute defect
        defect = self.compute_defect(target_weight)
        
        # Compute effective rank and gap
        eff_rank = self.compute_effective_rank(target_weight)
        spectral_gap = self.compute_spectral_gap(target_weight)
        
        # Spectral entropy
        W = target_weight.detach().cpu().float()
        try:
            S = torch.linalg.svdvals(W)
            S_squared = S ** 2
            total = S_squared.sum().item()
            if total > 1e-10:
                p = S_squared / total
                p = p[p > 1e-10]
                spectral_entropy = -(p * torch.log(p)).sum().item()
            else:
                spectral_entropy = 0.0
        except Exception:
            spectral_entropy = 0.0
        
        # Susceptibility (if loss provided)
        if loss is not None:
            chi_g = self.compute_susceptibility(model, loss)
            grad_norm = self.grad_history[-1] if self.grad_history else 0.0
        else:
            chi_g = 0.0
            grad_norm = 0.0
        
        # Ridge ratio (if dataloader provided)
        if dataloader is not None:
            ridge_ratio = self.compute_ridge_ratio(model, dataloader, device)
        else:
            ridge_ratio = 100.0
        
        metrics = SGCMetrics(
            epsilon=defect.epsilon,
            chi_g=chi_g,
            ridge_ratio=ridge_ratio,
            k_coarse=defect.k_coarse,
            spectral_gap=spectral_gap,
            effective_rank=eff_rank,
            spectral_entropy=spectral_entropy,
            grad_norm=grad_norm,
            tail_energy=defect.tail_energy,
            total_energy=defect.total_energy
        )
        
        # Track history
        self.epsilon_history.append(defect.epsilon)
        self.chi_g_history.append(chi_g)
        self.ridge_ratio_history.append(ridge_ratio)
        
        self.current_metrics = metrics
        return metrics
    
    def is_grokked(self, epsilon_threshold: float = 0.05,
                   ridge_threshold: float = 2.0) -> bool:
        """
        Check if system has grokked (reached stable fixed point).
        
        Grokking criteria:
        1. ε < threshold (low defect)
        2. R ≈ 1 (well-conditioned, stable)
        """
        if self.current_metrics is None:
            return False
        
        return (self.current_metrics.epsilon < epsilon_threshold and
                self.current_metrics.ridge_ratio < ridge_threshold)
    
    def get_trends(self) -> Dict[str, float]:
        """
        Compute trends in key metrics.
        
        Returns:
            Dict with slopes of ε, χ_g, R over recent history
        """
        def slope(history):
            if len(history) < 10:
                return 0.0
            recent = list(history)[-10:]
            x = list(range(len(recent)))
            x_mean = sum(x) / len(x)
            y_mean = sum(recent) / len(recent)
            
            num = sum((xi - x_mean) * (yi - y_mean) for xi, yi in zip(x, recent))
            den = sum((xi - x_mean) ** 2 for xi in x)
            
            return num / den if den > 0 else 0.0
        
        return {
            'epsilon_slope': slope(self.epsilon_history),
            'chi_g_slope': slope(self.chi_g_history),
            'ridge_ratio_slope': slope(self.ridge_ratio_history),
        }
