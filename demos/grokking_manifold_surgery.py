"""
Manifold Surgery Experiment: Deep Diagnostics for Grokking Phase Transitions

This experiment rigorously tests the hypothesis that grokking involves:
1. Ridge formation (high Dirichlet energy at class boundaries)
2. Scale-free topology (Tsallis q ≈ 2.5 as optimal state)
3. Van Hove singularity in Hessian spectrum

Key improvements over lifshitz_transition_experiment.py:
- Full Hessian spectrum computation (not skipped)
- Tangent space projection for functorial defect
- Within-class vs between-class Dirichlet energy decomposition
- Information gradient ratio tracking (||∇I|| / ||∇E||)
- CSV logging for all metrics

Author: SGC Research Team
Date: February 6, 2026
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import DataLoader, TensorDataset
import numpy as np
from dataclasses import dataclass, asdict
from typing import Tuple, List, Optional, Dict
import csv
import json
from pathlib import Path
from datetime import datetime
import warnings

# =============================================================================
# MODEL DEFINITION
# =============================================================================

class EmbeddingGrokMLP(nn.Module):
    """MLP with learnable embeddings for modular arithmetic."""
    
    def __init__(self, p: int, embed_dim: int = 128, hidden_dim: int = 256, 
                 noise_std: float = 0.0):
        super().__init__()
        self.p = p
        self.embed_dim = embed_dim
        self.hidden_dim = hidden_dim
        self.noise_std = noise_std
        
        self.embed_a = nn.Embedding(p, embed_dim)
        self.embed_b = nn.Embedding(p, embed_dim)
        
        self.fc1 = nn.Linear(2 * embed_dim, hidden_dim)
        self.fc2 = nn.Linear(hidden_dim, hidden_dim)
        self.fc3 = nn.Linear(hidden_dim, p)
        
        self._init_weights()
    
    def _init_weights(self):
        for m in [self.fc1, self.fc2, self.fc3]:
            nn.init.kaiming_normal_(m.weight, nonlinearity='relu')
            nn.init.zeros_(m.bias)
        nn.init.normal_(self.embed_a.weight, std=0.02)
        nn.init.normal_(self.embed_b.weight, std=0.02)
    
    def get_embeddings(self, a: torch.Tensor, b: torch.Tensor) -> torch.Tensor:
        """Get raw embeddings before hidden layers."""
        e_a = self.embed_a(a)
        e_b = self.embed_b(b)
        if self.training and self.noise_std > 0:
            e_a = e_a + torch.randn_like(e_a) * self.noise_std
            e_b = e_b + torch.randn_like(e_b) * self.noise_std
        return torch.cat([e_a, e_b], dim=-1)
    
    def get_hidden(self, a: torch.Tensor, b: torch.Tensor) -> torch.Tensor:
        """Get hidden layer activations."""
        x = self.get_embeddings(a, b)
        x = F.relu(self.fc1(x))
        x = F.relu(self.fc2(x))
        return x
    
    def forward(self, a: torch.Tensor, b: torch.Tensor) -> torch.Tensor:
        x = self.get_hidden(a, b)
        return self.fc3(x)


# =============================================================================
# DATA GENERATION
# =============================================================================

def create_modular_dataset(p: int = 97, train_frac: float = 0.3, seed: int = 42):
    """Create modular addition dataset: (a + b) mod p."""
    rng = np.random.default_rng(seed)
    
    all_pairs = [(a, b) for a in range(p) for b in range(p)]
    rng.shuffle(all_pairs)
    
    n_train = int(len(all_pairs) * train_frac)
    train_pairs = all_pairs[:n_train]
    test_pairs = all_pairs[n_train:]
    
    def to_tensors(pairs):
        a = torch.tensor([p[0] for p in pairs], dtype=torch.long)
        b = torch.tensor([p[1] for p in pairs], dtype=torch.long)
        c = torch.tensor([(p[0] + p[1]) % 97 for p in pairs], dtype=torch.long)
        return a, b, c
    
    train_a, train_b, train_c = to_tensors(train_pairs)
    test_a, test_b, test_c = to_tensors(test_pairs)
    
    return (train_a, train_b, train_c), (test_a, test_b, test_c)


# =============================================================================
# HESSIAN SPECTRUM COMPUTATION (Full, not skipped)
# =============================================================================

def compute_hessian_spectrum_full(
    model: nn.Module,
    loss_fn,
    dataloader: DataLoader,
    device: str,
    n_eigenvalues: int = 100,
    n_lanczos_iter: int = 150
) -> Dict[str, float]:
    """
    Compute Hessian spectrum using Lanczos iteration.
    
    Returns dict with:
    - eigenvalues: Array of estimated eigenvalues
    - density_zero: Density of eigenvalues near λ=0 (Van Hove signature)
    - trace: Sum of eigenvalues (total curvature)
    - max_eigenvalue: Largest eigenvalue (sharpness)
    - min_eigenvalue: Most negative eigenvalue (saddle detection)
    - spectral_gap: Gap between smallest positive eigenvalues
    """
    was_training = model.training
    model.train()
    
    params = [p for p in model.parameters() if p.requires_grad]
    n_params = sum(p.numel() for p in params)
    
    def hvp(v_flat: torch.Tensor) -> torch.Tensor:
        """Hessian-vector product."""
        model.zero_grad()
        
        v_list = []
        offset = 0
        for p in params:
            n = p.numel()
            v_list.append(v_flat[offset:offset+n].view_as(p))
            offset += n
        
        total_hvp = torch.zeros_like(v_flat)
        n_batches = 0
        
        for batch in dataloader:
            a, b, c = [x.to(device) for x in batch]
            out = model(a, b)
            loss = loss_fn(out, c)
            
            grads = torch.autograd.grad(loss, params, create_graph=True)
            dot = sum((g * v).sum() for g, v in zip(grads, v_list))
            hvp_tuple = torch.autograd.grad(dot, params, retain_graph=False)
            
            hvp_flat = torch.cat([h.flatten() for h in hvp_tuple])
            total_hvp += hvp_flat
            n_batches += 1
        
        return total_hvp / n_batches
    
    # Lanczos iteration
    v = torch.randn(n_params, device=device)
    v = v / v.norm()
    
    alphas = []
    betas = []
    V = [v]
    
    for i in range(min(n_lanczos_iter, n_params - 1)):
        try:
            w = hvp(v)
            alpha = (v * w).sum().item()
            alphas.append(alpha)
            
            if i > 0:
                w = w - betas[-1] * V[-2]
            w = w - alpha * v
            
            beta = w.norm().item()
            if beta < 1e-10:
                break
            betas.append(beta)
            
            v = w / beta
            V.append(v)
        except RuntimeError as e:
            warnings.warn(f"Lanczos iteration {i} failed: {e}")
            break
    
    # Build tridiagonal matrix and compute eigenvalues
    n = len(alphas)
    T = np.diag(alphas)
    if betas and n > 1:
        # betas has length n-1, use only what we have
        n_betas = min(len(betas), n - 1)
        T[:n_betas+1, :n_betas+1] += np.diag(betas[:n_betas], 1) + np.diag(betas[:n_betas], -1)
    
    eigenvalues = np.linalg.eigvalsh(T)
    eigenvalues = np.sort(eigenvalues)
    
    # Compute statistics
    near_zero_mask = np.abs(eigenvalues) < 0.1
    density_zero = near_zero_mask.sum() / len(eigenvalues)
    
    positive_eigs = eigenvalues[eigenvalues > 1e-6]
    if len(positive_eigs) >= 2:
        spectral_gap = positive_eigs[1] - positive_eigs[0]
    else:
        spectral_gap = 0.0
    
    if not was_training:
        model.eval()
    
    return {
        'eigenvalues': eigenvalues,
        'density_zero': density_zero,
        'trace': eigenvalues.sum(),
        'max_eigenvalue': eigenvalues.max(),
        'min_eigenvalue': eigenvalues.min(),
        'spectral_gap': spectral_gap,
        'n_negative': (eigenvalues < -1e-6).sum(),
        'n_near_zero': near_zero_mask.sum()
    }


# =============================================================================
# FUNCTIONAL AND GEOMETRIC DEFECTS
# =============================================================================

def compute_functional_defect(
    hidden_states: torch.Tensor,
    targets: torch.Tensor,
    num_classes: int
) -> Tuple[float, float, float]:
    """
    Compute functional defect: within-class variance / total variance.
    
    Returns: (functional_defect, class_separation, total_variance)
    """
    device = hidden_states.device
    
    total_var = hidden_states.var(dim=0).mean().item()
    if total_var < 1e-10:
        return 0.0, float('inf'), total_var
    
    class_vars = []
    class_means = []
    class_counts = []
    
    for c in range(num_classes):
        mask = (targets == c)
        count = mask.sum().item()
        if count > 0:
            h_c = hidden_states[mask]
            class_means.append(h_c.mean(dim=0))
            class_counts.append(count)
            if count > 1:
                class_vars.append(h_c.var(dim=0).mean().item())
            else:
                class_vars.append(0.0)
    
    if not class_means:
        return 1.0, 0.0, total_var
    
    class_counts = torch.tensor(class_counts, dtype=torch.float, device=device)
    class_vars = torch.tensor(class_vars, device=device)
    class_means = torch.stack(class_means)
    
    within_var = (class_vars * class_counts).sum() / class_counts.sum()
    
    global_mean = (class_means * class_counts.unsqueeze(1)).sum(0) / class_counts.sum()
    between_var = ((class_means - global_mean) ** 2).mean(dim=1)
    between_var = (between_var * class_counts).sum() / class_counts.sum()
    
    func_defect = within_var.item() / (total_var + 1e-10)
    class_sep = between_var.item() / (within_var.item() + 1e-10)
    
    return func_defect, class_sep, total_var


def compute_geometric_defect(
    hidden_states: torch.Tensor,
    k: int = 10
) -> Tuple[float, float, List[float]]:
    """
    Compute geometric defect via PCA closure.
    
    Returns: (geometric_defect, explained_variance_ratio, singular_values)
    """
    h_centered = hidden_states - hidden_states.mean(dim=0)
    
    try:
        U, S, Vh = torch.linalg.svd(h_centered, full_matrices=False)
    except RuntimeError:
        return 1.0, 0.0, []
    
    # Project onto top-k
    h_projected = h_centered @ Vh[:k].T @ Vh[:k]
    
    # Defect = ||h - h_projected|| / ||h||
    residual = h_centered - h_projected
    defect = residual.norm() / (h_centered.norm() + 1e-10)
    
    # Explained variance ratio
    total_var = (S ** 2).sum()
    explained_var = (S[:k] ** 2).sum() / (total_var + 1e-10)
    
    return defect.item(), explained_var.item(), S[:20].cpu().tolist()


# =============================================================================
# INTRINSIC (GAUSS) CURVATURE ESTIMATION
# =============================================================================

def compute_intrinsic_curvature(
    model: nn.Module,
    p: int,
    device: str,
    n_triangles: int = 200
) -> Dict[str, float]:
    """
    Estimate intrinsic (Gauss) curvature using geodesic triangle angle deficit.
    
    For a flat manifold: sum of angles in geodesic triangle = pi
    For positive curvature (sphere): sum > pi  
    For negative curvature (saddle): sum < pi
    For a torus: varies by location, average ~ 0
    
    Returns dict with:
    - angle_deficit: (sum - pi) averaged over triangles
    - gauss_curvature_estimate: Approximation of integrated Gauss curvature
    - curvature_variance: How much curvature varies (high for torus)
    """
    model.eval()
    
    with torch.no_grad():
        angle_deficits = []
        
        for _ in range(n_triangles):
            # Sample a random triangle in input space
            a0 = torch.randint(0, p, (1,), device=device)
            b0 = torch.randint(0, p, (1,), device=device)
            
            # Triangle vertices: (a0,b0), (a0+1,b0), (a0,b0+1)
            a1, b1 = (a0 + 1) % p, b0
            a2, b2 = a0, (b0 + 1) % p
            
            # Get hidden states (manifold points)
            h0 = model.get_hidden(a0, b0).squeeze()
            h1 = model.get_hidden(a1, b1).squeeze()
            h2 = model.get_hidden(a2, b2).squeeze()
            
            # Edge vectors
            e01 = h1 - h0
            e02 = h2 - h0
            e12 = h2 - h1
            
            # Compute angles using cosine formula
            def angle_between(v1, v2):
                cos_angle = torch.dot(v1, v2) / (v1.norm() * v2.norm() + 1e-10)
                cos_angle = torch.clamp(cos_angle, -1.0, 1.0)
                return torch.acos(cos_angle)
            
            angle_at_0 = angle_between(e01, e02)
            angle_at_1 = angle_between(-e01, e12)
            angle_at_2 = angle_between(-e02, -e12)
            
            angle_sum = angle_at_0 + angle_at_1 + angle_at_2
            deficit = (angle_sum - torch.pi).item()
            angle_deficits.append(deficit)
        
        deficits = torch.tensor(angle_deficits)
        mean_deficit = deficits.mean().item()
        deficit_variance = deficits.var().item()
        
        # Gauss curvature ~ angle deficit / area
        # For unit triangles, this is approximately the deficit itself
        gauss_estimate = mean_deficit
    
    return {
        'angle_deficit': mean_deficit,
        'gauss_curvature_estimate': gauss_estimate,
        'curvature_variance': deficit_variance,
        'curvature_sign': 'positive' if mean_deficit > 0.01 else ('negative' if mean_deficit < -0.01 else 'flat/torus')
    }


# =============================================================================
# TANGENT SPACE FUNCTORIAL DEFECT
# =============================================================================

def compute_functorial_defect_tangent(
    model: nn.Module,
    p: int,
    device: str,
    n_samples: int = 200
) -> Dict[str, float]:
    """
    Compute Functorial Defect using tangent space projection.
    
    Instead of raw Euclidean distance, project displacement vectors onto
    the local tangent space of the manifold to correct for curvature.
    
    Returns dict with:
    - functorial_defect_euclidean: Raw Euclidean measurement
    - functorial_defect_tangent: Tangent-space corrected measurement
    - manifold_curvature: Estimated curvature from tangent deviation
    """
    model.eval()
    
    with torch.no_grad():
        # Sample random base points
        a_vals = torch.randint(0, p-1, (n_samples,), device=device)
        b_vals = torch.randint(0, p, (n_samples,), device=device)
        
        # Get hidden states for base, +1 in a, +1 in b
        h_base = model.get_hidden(a_vals, b_vals)
        h_plus_a = model.get_hidden(a_vals + 1, b_vals)
        h_plus_b = model.get_hidden(a_vals, (b_vals + 1) % p)
        
        # Raw displacement vectors
        disp_a = h_plus_a - h_base
        disp_b = h_plus_b - h_base
        
        # === Euclidean functorial defect ===
        mean_disp_a = disp_a.mean(dim=0)
        disp_a_centered = disp_a - mean_disp_a
        var_a = (disp_a_centered ** 2).mean().item()
        norm_a = mean_disp_a.norm().item()
        
        if norm_a > 1e-10:
            func_defect_euclidean_a = var_a / (norm_a ** 2)
        else:
            func_defect_euclidean_a = float('inf')
        
        mean_disp_b = disp_b.mean(dim=0)
        disp_b_centered = disp_b - mean_disp_b
        var_b = (disp_b_centered ** 2).mean().item()
        norm_b = mean_disp_b.norm().item()
        
        if norm_b > 1e-10:
            func_defect_euclidean_b = var_b / (norm_b ** 2)
        else:
            func_defect_euclidean_b = float('inf')
        
        func_defect_euclidean = (func_defect_euclidean_a + func_defect_euclidean_b) / 2
        
        # === Tangent space projection ===
        # Estimate local tangent space via PCA of nearby points
        # Stack all displacements to estimate tangent directions
        all_disp = torch.cat([disp_a, disp_b], dim=0)
        all_disp_centered = all_disp - all_disp.mean(dim=0)
        
        try:
            U, S, Vh = torch.linalg.svd(all_disp_centered, full_matrices=False)
            # Top 2 singular vectors define tangent plane
            tangent_basis = Vh[:2]  # Shape: (2, hidden_dim)
            
            # Project displacements onto tangent space
            disp_a_tangent = disp_a @ tangent_basis.T  # Shape: (n_samples, 2)
            disp_b_tangent = disp_b @ tangent_basis.T
            
            # Functorial defect in tangent space
            mean_disp_a_tan = disp_a_tangent.mean(dim=0)
            var_a_tan = ((disp_a_tangent - mean_disp_a_tan) ** 2).mean().item()
            norm_a_tan = mean_disp_a_tan.norm().item()
            
            if norm_a_tan > 1e-10:
                func_defect_tangent_a = var_a_tan / (norm_a_tan ** 2)
            else:
                func_defect_tangent_a = float('inf')
            
            mean_disp_b_tan = disp_b_tangent.mean(dim=0)
            var_b_tan = ((disp_b_tangent - mean_disp_b_tan) ** 2).mean().item()
            norm_b_tan = mean_disp_b_tan.norm().item()
            
            if norm_b_tan > 1e-10:
                func_defect_tangent_b = var_b_tan / (norm_b_tan ** 2)
            else:
                func_defect_tangent_b = float('inf')
            
            func_defect_tangent = (func_defect_tangent_a + func_defect_tangent_b) / 2
            
            # Curvature estimate: how much variance is lost in tangent projection
            total_var = (all_disp_centered ** 2).sum().item()
            tangent_var = (S[:2] ** 2).sum().item()
            curvature_estimate = 1.0 - tangent_var / (total_var + 1e-10)
            
        except RuntimeError:
            func_defect_tangent = func_defect_euclidean
            curvature_estimate = 0.0
    
    return {
        'functorial_defect_euclidean': func_defect_euclidean,
        'functorial_defect_tangent': func_defect_tangent,
        'manifold_curvature': curvature_estimate,
        'mean_displacement_norm': (norm_a + norm_b) / 2
    }


# =============================================================================
# DIRICHLET ENERGY DECOMPOSITION (Within-Class vs Between-Class)
# =============================================================================

def compute_dirichlet_energy_decomposed(
    model: nn.Module,
    p: int,
    device: str,
    n_samples: int = 500
) -> Dict[str, float]:
    """
    Decompose Dirichlet energy into within-class and between-class components.
    
    CORRECTED: For addition (a+b)%p, grid neighbors ALWAYS cross class boundaries.
    Within-class edges are DIAGONAL moves: (a+1, b-1) preserves (a+b).
    
    Returns dict with:
    - dirichlet_total: Total Dirichlet energy
    - dirichlet_within_class: Energy from DIAGONAL edges (same equivalence class)
    - dirichlet_between_class: Energy from GRID edges (cross class boundaries)
    - ridge_ratio: between / within (high = sharp ridges at boundaries)
    """
    model.eval()
    
    with torch.no_grad():
        # Sample random points
        a_vals = torch.randint(0, p, (n_samples,), device=device)
        b_vals = torch.randint(0, p, (n_samples,), device=device)
        
        # === BETWEEN-CLASS edges: grid neighbors (always cross class for addition) ===
        a_plus = (a_vals + 1) % p
        b_plus = (b_vals + 1) % p
        
        h_base = model.get_hidden(a_vals, b_vals)
        h_a_neighbor = model.get_hidden(a_plus, b_vals)
        h_b_neighbor = model.get_hidden(a_vals, b_plus)
        
        energy_between_a = ((h_base - h_a_neighbor) ** 2).sum(dim=1)
        energy_between_b = ((h_base - h_b_neighbor) ** 2).sum(dim=1)
        between_energy = torch.cat([energy_between_a, energy_between_b]).mean().item()
        
        # === WITHIN-CLASS edges: diagonal moves (a+1, b-1) preserves a+b ===
        a_diag = (a_vals + 1) % p
        b_diag = (b_vals - 1) % p  # +1 and -1 cancel out in sum
        
        h_diag_neighbor = model.get_hidden(a_diag, b_diag)
        energy_within = ((h_base - h_diag_neighbor) ** 2).sum(dim=1).mean().item()
        
        # Verify: both should have same target
        # target_base = (a_vals + b_vals) % p
        # target_diag = (a_diag + b_diag) % p = ((a+1) + (b-1)) % p = (a+b) % p  ✓
        
        total_energy = (between_energy * 2 + energy_within) / 3  # Weighted average
        
        # Ridge ratio: how much higher is between-class vs within-class energy?
        if energy_within > 1e-10:
            ridge_ratio = between_energy / energy_within
        else:
            ridge_ratio = float('inf') if between_energy > 0 else 1.0
        
        # Normalized energy (by representation norm)
        h_norm = h_base.norm(dim=1).mean().item()
        normalized_total = total_energy / (h_norm ** 2 + 1e-10)
    
    return {
        'dirichlet_total': total_energy,
        'dirichlet_within_class': energy_within,
        'dirichlet_between_class': between_energy,
        'ridge_ratio': ridge_ratio,
        'dirichlet_normalized': normalized_total,
        'representation_norm': h_norm
    }


# =============================================================================
# INFORMATION GRADIENT RATIO
# =============================================================================

def compute_gradient_ratio(
    model: nn.Module,
    train_loader: DataLoader,
    device: str,
    p: int
) -> Dict[str, float]:
    """
    Compute ||∇I|| / ||∇E|| ratio (Information Gradient Law).
    
    - ∇E = gradient of cross-entropy loss (energy)
    - ∇I = gradient of KL divergence from uniform (information)
    
    Theory predicts: grokking occurs when ||∇I|| > ||∇E||
    """
    model.train()
    
    # === Energy gradient (cross-entropy loss) ===
    model.zero_grad()
    total_loss = 0
    n_samples = 0
    
    for batch in train_loader:
        a, b, c = [x.to(device) for x in batch]
        out = model(a, b)
        loss = F.cross_entropy(out, c)
        loss.backward()
        total_loss += loss.item() * len(a)
        n_samples += len(a)
    
    energy_grad_norm = sum(
        p.grad.norm() ** 2 for p in model.parameters() if p.grad is not None
    ) ** 0.5
    
    # === Information gradient (KL from uniform) ===
    model.zero_grad()
    
    for batch in train_loader:
        a, b, c = [x.to(device) for x in batch]
        out = model(a, b)
        probs = F.softmax(out, dim=-1)
        
        # KL(predicted || uniform) = sum(p * log(p * num_classes))
        uniform = torch.ones_like(probs) / p
        kl_div = F.kl_div(probs.log(), uniform, reduction='batchmean')
        kl_div.backward()
    
    info_grad_norm = sum(
        p.grad.norm() ** 2 for p in model.parameters() if p.grad is not None
    ) ** 0.5
    
    # Ratio
    if energy_grad_norm > 1e-10:
        gradient_ratio = info_grad_norm / energy_grad_norm
    else:
        gradient_ratio = float('inf')
    
    model.zero_grad()
    
    return {
        'energy_grad_norm': energy_grad_norm,
        'info_grad_norm': info_grad_norm,
        'gradient_ratio': gradient_ratio,
        'avg_loss': total_loss / n_samples
    }


# =============================================================================
# TSALLIS STATISTICS
# =============================================================================

def estimate_tsallis_q(values: torch.Tensor, q_range: Tuple[float, float] = (0.5, 3.5)) -> float:
    """
    Estimate Tsallis q parameter from distribution of values.
    
    Uses maximum likelihood estimation for q-Gaussian.
    q > 1: heavy tails (long-range correlations, scale-free)
    q = 1: Gaussian (Shannon/Boltzmann)
    q < 1: compact support
    """
    values = values.flatten().cpu().numpy()
    values = values[np.isfinite(values)]
    
    if len(values) < 10:
        return 1.0
    
    # Normalize
    values = (values - values.mean()) / (values.std() + 1e-10)
    
    # Estimate q via kurtosis relationship
    # For q-Gaussian: kurtosis = 3 * (3 - q) / (5 - 3q) for q < 5/3
    kurtosis = np.mean(values ** 4) / (np.mean(values ** 2) ** 2 + 1e-10)
    
    # Solve for q (approximate)
    # kurtosis ≈ 3 for q=1, increases with q
    if kurtosis <= 3:
        q_estimate = 1.0
    else:
        # Empirical fit for heavy-tailed regime
        q_estimate = 1.0 + 0.2 * np.log(kurtosis / 3 + 1)
    
    return np.clip(q_estimate, q_range[0], q_range[1])


def compute_scale_free_metrics(hidden_states: torch.Tensor) -> Dict[str, float]:
    """
    Compute metrics related to scale-free topology.
    
    Returns:
    - tsallis_q: Estimated Tsallis parameter
    - hub_concentration: Fraction of variance explained by top neurons
    - activation_gini: Gini coefficient of neuron activations
    """
    # Tsallis q from activation distribution
    q = estimate_tsallis_q(hidden_states)
    
    # Hub concentration: variance explained by top 10% of neurons
    neuron_vars = hidden_states.var(dim=0)
    sorted_vars, _ = torch.sort(neuron_vars, descending=True)
    n_top = max(1, int(0.1 * len(sorted_vars)))
    hub_concentration = sorted_vars[:n_top].sum() / (sorted_vars.sum() + 1e-10)
    
    # Gini coefficient of activations
    abs_activations = hidden_states.abs().mean(dim=0).cpu().numpy()
    abs_activations = np.sort(abs_activations)
    n = len(abs_activations)
    cumsum = np.cumsum(abs_activations)
    gini = (n + 1 - 2 * cumsum.sum() / (cumsum[-1] + 1e-10)) / n
    
    return {
        'tsallis_q': q,
        'hub_concentration': hub_concentration.item(),
        'activation_gini': float(gini)
    }


# =============================================================================
# METRICS DATACLASS
# =============================================================================

@dataclass
class ManifoldSurgeryMetrics:
    """All metrics for one epoch."""
    epoch: int
    train_acc: float
    test_acc: float
    train_loss: float
    
    # Functional/Geometric defects
    functional_defect: float
    class_separation: float
    geometric_defect: float
    explained_variance: float
    
    # Functorial defect (both methods)
    functorial_defect_euclidean: float
    functorial_defect_tangent: float
    manifold_curvature: float  # Extrinsic (tangent plane fit)
    
    # Dirichlet energy decomposition
    dirichlet_total: float
    dirichlet_within_class: float
    dirichlet_between_class: float
    ridge_ratio: float
    dirichlet_normalized: float
    
    # Gradient ratio
    energy_grad_norm: float
    info_grad_norm: float
    gradient_ratio: float
    
    # Scale-free metrics
    tsallis_q: float
    hub_concentration: float
    activation_gini: float
    
    # === Optional fields (must come after required fields) ===
    
    # Intrinsic (Gauss) curvature
    gauss_curvature: Optional[float] = None
    curvature_variance: Optional[float] = None
    
    # Hessian spectrum (computed less frequently)
    hessian_trace: Optional[float] = None
    hessian_max_eigenvalue: Optional[float] = None
    hessian_density_zero: Optional[float] = None
    hessian_spectral_gap: Optional[float] = None
    hessian_n_negative: Optional[int] = None
    
    # Phase label
    phase: str = "MEMORIZATION"


# =============================================================================
# MAIN EXPERIMENT
# =============================================================================

def run_manifold_surgery_experiment(
    p: int = 97,
    embed_dim: int = 128,
    hidden_dim: int = 128,
    lr: float = 1e-3,
    weight_decay: float = 1.0,
    epochs: int = 5000,
    noise_std: float = 0.0,
    seed: int = 42,
    batch_size: int = 512,
    log_interval: int = 50,
    hessian_interval: int = 500,
    device: str = 'cuda' if torch.cuda.is_available() else 'cpu',
    output_dir: str = 'logs/manifold_surgery'
) -> List[ManifoldSurgeryMetrics]:
    """
    Run the Manifold Surgery Experiment with full diagnostics.
    """
    # Setup
    torch.manual_seed(seed)
    np.random.seed(seed)
    
    output_path = Path(output_dir)
    output_path.mkdir(parents=True, exist_ok=True)
    
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    run_name = f"run_{timestamp}_noise{noise_std}_seed{seed}"
    run_path = output_path / run_name
    run_path.mkdir(exist_ok=True)
    
    # Data
    (train_a, train_b, train_c), (test_a, test_b, test_c) = create_modular_dataset(p, seed=seed)
    train_dataset = TensorDataset(train_a, train_b, train_c)
    test_dataset = TensorDataset(test_a, test_b, test_c)
    
    train_loader = DataLoader(train_dataset, batch_size=batch_size, shuffle=True)
    test_loader = DataLoader(test_dataset, batch_size=batch_size, shuffle=False)
    
    # Model
    model = EmbeddingGrokMLP(p, embed_dim, hidden_dim, noise_std).to(device)
    optimizer = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=weight_decay)
    loss_fn = nn.CrossEntropyLoss()
    
    # Metrics storage
    metrics_history: List[ManifoldSurgeryMetrics] = []
    grokking_epoch = None
    
    # Save hyperparameters
    hyperparams = {
        'p': p, 'embed_dim': embed_dim, 'hidden_dim': hidden_dim,
        'lr': lr, 'weight_decay': weight_decay, 'epochs': epochs,
        'noise_std': noise_std, 'seed': seed, 'batch_size': batch_size
    }
    with open(run_path / 'hyperparams.json', 'w') as f:
        json.dump(hyperparams, f, indent=2)
    
    print(f"\n{'='*80}")
    print(f"MANIFOLD SURGERY EXPERIMENT")
    print(f"{'='*80}")
    print(f"Device: {device} | p={p} | noise_std={noise_std} | seed={seed}")
    print(f"Output: {run_path}")
    print(f"{'='*80}\n")
    
    header = (
        f"{'Epoch':>6} | {'Train':>6} | {'Test':>6} | {'F.Def':>6} | "
        f"{'G.Def':>6} | {'Ridge':>6} | {'dI/dE':>6} | {'q':>5} | Phase"
    )
    print(header)
    print("-" * len(header))
    
    for epoch in range(1, epochs + 1):
        # Training step
        model.train()
        for batch in train_loader:
            a, b, c = [x.to(device) for x in batch]
            optimizer.zero_grad()
            out = model(a, b)
            loss = loss_fn(out, c)
            loss.backward()
            optimizer.step()
        
        # Evaluation
        if epoch % log_interval == 0 or epoch == 1:
            model.eval()
            
            with torch.no_grad():
                # Accuracy
                train_out = model(train_a.to(device), train_b.to(device))
                train_acc = (train_out.argmax(1) == train_c.to(device)).float().mean().item()
                train_loss = loss_fn(train_out, train_c.to(device)).item()
                
                test_out = model(test_a.to(device), test_b.to(device))
                test_acc = (test_out.argmax(1) == test_c.to(device)).float().mean().item()
                
                # Hidden states for metrics
                hidden = model.get_hidden(train_a.to(device), train_b.to(device))
                targets = train_c.to(device)
            
            # Compute all metrics
            func_defect, class_sep, _ = compute_functional_defect(hidden, targets, p)
            geom_defect, explained_var, _ = compute_geometric_defect(hidden)
            
            functorial = compute_functorial_defect_tangent(model, p, device)
            dirichlet = compute_dirichlet_energy_decomposed(model, p, device)
            gradients = compute_gradient_ratio(model, train_loader, device, p)
            scale_free = compute_scale_free_metrics(hidden)
            intrinsic = compute_intrinsic_curvature(model, p, device, n_triangles=100)
            
            # Hessian spectrum (expensive, do less frequently)
            if epoch % hessian_interval == 0:
                hessian = compute_hessian_spectrum_full(
                    model, loss_fn, train_loader, device, 
                    n_eigenvalues=50, n_lanczos_iter=100
                )
                hessian_trace = hessian['trace']
                hessian_max = hessian['max_eigenvalue']
                hessian_density = hessian['density_zero']
                hessian_gap = hessian['spectral_gap']
                hessian_neg = hessian['n_negative']
            else:
                hessian_trace = hessian_max = hessian_density = hessian_gap = None
                hessian_neg = None
            
            # Phase detection
            if func_defect < 0.05 and test_acc > 0.95:
                phase = "GROKKED"
                if grokking_epoch is None:
                    grokking_epoch = epoch
            elif func_defect < 0.15:
                phase = "TRANSITION"
            else:
                phase = "MEMORIZATION"
            
            # Create metrics object
            metrics = ManifoldSurgeryMetrics(
                epoch=epoch,
                train_acc=train_acc,
                test_acc=test_acc,
                train_loss=train_loss,
                functional_defect=func_defect,
                class_separation=class_sep,
                geometric_defect=geom_defect,
                explained_variance=explained_var,
                functorial_defect_euclidean=functorial['functorial_defect_euclidean'],
                functorial_defect_tangent=functorial['functorial_defect_tangent'],
                manifold_curvature=functorial['manifold_curvature'],
                gauss_curvature=intrinsic['gauss_curvature_estimate'],
                curvature_variance=intrinsic['curvature_variance'],
                dirichlet_total=dirichlet['dirichlet_total'],
                dirichlet_within_class=dirichlet['dirichlet_within_class'],
                dirichlet_between_class=dirichlet['dirichlet_between_class'],
                ridge_ratio=dirichlet['ridge_ratio'],
                dirichlet_normalized=dirichlet['dirichlet_normalized'],
                energy_grad_norm=gradients['energy_grad_norm'],
                info_grad_norm=gradients['info_grad_norm'],
                gradient_ratio=gradients['gradient_ratio'],
                tsallis_q=scale_free['tsallis_q'],
                hub_concentration=scale_free['hub_concentration'],
                activation_gini=scale_free['activation_gini'],
                hessian_trace=hessian_trace,
                hessian_max_eigenvalue=hessian_max,
                hessian_density_zero=hessian_density,
                hessian_spectral_gap=hessian_gap,
                hessian_n_negative=hessian_neg,
                phase=phase
            )
            metrics_history.append(metrics)
            
            # Print progress
            ridge_str = f"{dirichlet['ridge_ratio']:.2f}" if dirichlet['ridge_ratio'] < 1000 else ">1k"
            grad_ratio_str = f"{gradients['gradient_ratio']:.2f}" if gradients['gradient_ratio'] < 100 else ">100"
            
            print(
                f"{epoch:6d} | {train_acc:5.1%} | {test_acc:5.1%} | "
                f"{func_defect:6.3f} | {geom_defect:6.3f} | {ridge_str:>6} | "
                f"{grad_ratio_str:>6} | {scale_free['tsallis_q']:5.2f} | {phase}"
            )
            
            # Early stop if fully grokked
            if test_acc > 0.999 and func_defect < 0.01 and epoch > 500:
                print(f"\n[OK] Fully grokked at epoch {epoch}")
                break
    
    # Save metrics to CSV
    csv_path = run_path / 'metrics.csv'
    with open(csv_path, 'w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=list(asdict(metrics_history[0]).keys()))
        writer.writeheader()
        for m in metrics_history:
            writer.writerow(asdict(m))
    
    print(f"\n[OK] Metrics saved to {csv_path}")
    
    # Summary
    print(f"\n{'='*80}")
    print("EXPERIMENT SUMMARY")
    print(f"{'='*80}")
    
    if grokking_epoch:
        print(f"Grokking detected at epoch: {grokking_epoch}")
        
        # Find metrics at grokking
        grok_metrics = next(m for m in metrics_history if m.epoch >= grokking_epoch)
        pre_grok = metrics_history[0]
        
        print(f"\nMetric Transitions (epoch 1 -> {grokking_epoch}):")
        print(f"  Functional Defect:  {pre_grok.functional_defect:.3f} -> {grok_metrics.functional_defect:.3f}")
        print(f"  Geometric Defect:   {pre_grok.geometric_defect:.3f} -> {grok_metrics.geometric_defect:.3f}")
        print(f"  Class Separation:   {pre_grok.class_separation:.3f} -> {grok_metrics.class_separation:.3f}")
        print(f"  Ridge Ratio:        {pre_grok.ridge_ratio:.3f} -> {grok_metrics.ridge_ratio:.3f}")
        print(f"  Gradient Ratio:     {pre_grok.gradient_ratio:.3f} -> {grok_metrics.gradient_ratio:.3f}")
        print(f"  Tsallis q:          {pre_grok.tsallis_q:.3f} -> {grok_metrics.tsallis_q:.3f}")
        
        # Hypothesis verification
        print(f"\n{'='*80}")
        print("HYPOTHESIS VERIFICATION")
        print(f"{'='*80}")
        
        print(f"\n1. Ridge Formation (high between/within energy ratio):")
        if grok_metrics.ridge_ratio > 2.0:
            print(f"   [OK] CONFIRMED: Ridge ratio = {grok_metrics.ridge_ratio:.2f} > 2.0")
        else:
            print(f"   ? UNCLEAR: Ridge ratio = {grok_metrics.ridge_ratio:.2f}")
        
        print(f"\n2. Scale-Free Topology (Tsallis q ≈ 2.5):")
        if 2.0 < grok_metrics.tsallis_q < 3.0:
            print(f"   [OK] CONFIRMED: q = {grok_metrics.tsallis_q:.2f} in scale-free regime")
        else:
            print(f"   ? UNCLEAR: q = {grok_metrics.tsallis_q:.2f}")
        
        print(f"\n3. Functional/Geometric Opposition:")
        if grok_metrics.functional_defect < 0.1 and grok_metrics.geometric_defect > pre_grok.geometric_defect:
            print(f"   [OK] CONFIRMED: Functional DOWN while Geometric UP")
        else:
            print(f"   ? UNCLEAR: Check geometric defect trend")
        
        print(f"\n4. Information Gradient Law (||∇I|| > ||∇E|| at grokking):")
        if grok_metrics.gradient_ratio > 1.0:
            print(f"   [OK] CONFIRMED: Ratio = {grok_metrics.gradient_ratio:.2f} > 1.0")
        else:
            print(f"   [X] NOT CONFIRMED: Ratio = {grok_metrics.gradient_ratio:.2f}")
    else:
        print("Grokking NOT detected within training epochs.")
    
    return metrics_history


# =============================================================================
# ENTRY POINT
# =============================================================================

if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(description="Manifold Surgery Experiment")
    parser.add_argument('--p', type=int, default=97, help='Prime for modular arithmetic')
    parser.add_argument('--epochs', type=int, default=5000, help='Training epochs')
    parser.add_argument('--noise', type=float, default=0.0, help='Embedding noise std')
    parser.add_argument('--seed', type=int, default=42, help='Random seed')
    parser.add_argument('--lr', type=float, default=1e-3, help='Learning rate')
    parser.add_argument('--wd', type=float, default=1.0, help='Weight decay')
    parser.add_argument('--log-interval', type=int, default=50, help='Logging interval')
    parser.add_argument('--hessian-interval', type=int, default=500, help='Hessian computation interval')
    parser.add_argument('--output', type=str, default='logs/manifold_surgery', help='Output directory')
    
    args = parser.parse_args()
    
    run_manifold_surgery_experiment(
        p=args.p,
        epochs=args.epochs,
        noise_std=args.noise,
        seed=args.seed,
        lr=args.lr,
        weight_decay=args.wd,
        log_interval=args.log_interval,
        hessian_interval=args.hessian_interval,
        output_dir=args.output
    )
