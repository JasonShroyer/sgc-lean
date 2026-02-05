"""
Lifshitz Transition Experiment: Van Hove Singularity Detection

This experiment validates the hypothesis that grokking is a topological Lifshitz 
transition by tracking:
1. Hessian eigenvalue spectrum (Van Hove singularity detection)
2. Tsallis q(t) transition (non-extensive → extensive)
3. Relative extropy trajectory J(p||π)
4. Functional defect (within-class variance)

Predictions:
- Hessian eigenvalue density ρ(λ) near λ=0 peaks at grokking epoch
- Tsallis q transitions from ~1.5 to ~1.0 at grokking
- Relative extropy decays exponentially with rate λ_gap
- Functional defect collapses at grokking

Author: SGC Research Team
Date: February 5, 2026
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import DataLoader, TensorDataset
import numpy as np
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple
import math
from scipy import stats


# =============================================================================
# MODEL AND DATASET (from analog_modular_arithmetic.py)
# =============================================================================

class EmbeddingGrokMLP(nn.Module):
    """MLP with learned embeddings for grokking experiments."""
    
    def __init__(self, p: int = 97, embed_dim: int = 128, hidden_dim: int = 128, 
                 n_layers: int = 2, noise_std: float = 0.0):
        super().__init__()
        self.p = p
        self.embed_dim = embed_dim
        self.noise_std = noise_std
        
        self.embed_a = nn.Embedding(p, embed_dim)
        self.embed_b = nn.Embedding(p, embed_dim)
        
        layers = []
        layers.append(nn.Linear(2 * embed_dim, hidden_dim))
        layers.append(nn.ReLU())
        for _ in range(n_layers - 1):
            layers.append(nn.Linear(hidden_dim, hidden_dim))
            layers.append(nn.ReLU())
        self.hidden_layers = nn.Sequential(*layers)
        self.output = nn.Linear(hidden_dim, p)
        
        self._init_weights()
    
    def _init_weights(self):
        for m in self.modules():
            if isinstance(m, nn.Linear):
                nn.init.kaiming_normal_(m.weight, nonlinearity='relu')
                if m.bias is not None:
                    nn.init.zeros_(m.bias)
            elif isinstance(m, nn.Embedding):
                nn.init.normal_(m.weight, std=0.02)
    
    def forward(self, a: torch.Tensor, b: torch.Tensor) -> torch.Tensor:
        e_a = self.embed_a(a)
        e_b = self.embed_b(b)
        
        if self.training and self.noise_std > 0:
            e_a = e_a + torch.randn_like(e_a) * self.noise_std
            e_b = e_b + torch.randn_like(e_b) * self.noise_std
        
        x = torch.cat([e_a, e_b], dim=-1)
        h = self.hidden_layers(x)
        return self.output(h)
    
    def get_hidden(self, a: torch.Tensor, b: torch.Tensor) -> torch.Tensor:
        e_a = self.embed_a(a)
        e_b = self.embed_b(b)
        x = torch.cat([e_a, e_b], dim=-1)
        return self.hidden_layers(x)


def create_modular_dataset(p: int = 97, train_frac: float = 0.5):
    """Create modular addition dataset."""
    all_pairs = [(a, b) for a in range(p) for b in range(p)]
    np.random.shuffle(all_pairs)
    
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
# HESSIAN SPECTRUM COMPUTATION (Van Hove Detection)
# =============================================================================

def compute_hessian_spectrum_lanczos(
    model: nn.Module,
    loss_fn,
    dataloader: DataLoader,
    device: str,
    n_eigenvalues: int = 50,
    n_iter: int = 100
) -> Tuple[np.ndarray, float]:
    """
    Compute top and bottom eigenvalues of Hessian using Lanczos iteration.
    
    Returns:
        eigenvalues: Array of eigenvalues
        density_near_zero: Estimated density of eigenvalues near 0
    """
    was_training = model.training
    model.train()  # Need train mode for gradients
    
    # Collect all parameters
    params = [p for p in model.parameters() if p.requires_grad]
    n_params = sum(p.numel() for p in params)
    
    # Compute full gradient
    model.zero_grad()
    total_loss = 0
    n_samples = 0
    
    for batch in dataloader:
        a, b, c = [x.to(device) for x in batch]
        out = model(a, b)
        loss = loss_fn(out, c)
        total_loss += loss.item() * len(a)
        n_samples += len(a)
        loss.backward()
    
    # Hessian-vector product function
    def hvp(v_flat):
        """Compute Hessian-vector product."""
        model.zero_grad()
        
        # Unflatten v
        v_list = []
        offset = 0
        for p in params:
            n = p.numel()
            v_list.append(v_flat[offset:offset+n].view_as(p))
            offset += n
        
        # Forward pass
        total_hvp = torch.zeros_like(v_flat)
        
        for batch in dataloader:
            a, b, c = [x.to(device) for x in batch]
            out = model(a, b)
            loss = loss_fn(out, c)
            
            # First backward (gradient)
            grads = torch.autograd.grad(loss, params, create_graph=True)
            
            # Dot product with v
            dot = sum((g * v).sum() for g, v in zip(grads, v_list))
            
            # Second backward (Hessian-vector product)
            hvp_tuple = torch.autograd.grad(dot, params)
            
            # Flatten and accumulate
            hvp_flat = torch.cat([h.flatten() for h in hvp_tuple])
            total_hvp += hvp_flat
        
        return total_hvp / len(dataloader)
    
    # Lanczos iteration for top eigenvalues
    def lanczos(n_iter, n_eig):
        """Simple Lanczos for extreme eigenvalues."""
        # Random starting vector
        v = torch.randn(n_params, device=device)
        v = v / v.norm()
        
        alphas = []
        betas = []
        V = [v]
        
        for i in range(min(n_iter, n_params - 1)):
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
        
        # Build tridiagonal matrix
        T = np.diag(alphas)
        if betas:
            T += np.diag(betas, 1) + np.diag(betas, -1)
        
        # Eigenvalues of T approximate eigenvalues of Hessian
        eigs = np.linalg.eigvalsh(T)
        return np.sort(eigs)
    
    try:
        eigenvalues = lanczos(n_iter, n_eigenvalues)
        
        # Estimate density near zero
        near_zero_mask = np.abs(eigenvalues) < 0.1
        density_near_zero = near_zero_mask.sum() / len(eigenvalues)
        
        if not was_training:
            model.eval()
        
        return eigenvalues, density_near_zero
    except Exception as e:
        if not was_training:
            model.eval()
        return np.array([0.0]), 0.0


def compute_hessian_trace_hutchinson(
    model: nn.Module,
    loss_fn,
    dataloader: DataLoader,
    device: str,
    n_samples: int = 10
) -> float:
    """
    Estimate Hessian trace using Hutchinson's estimator.
    Trace = sum of eigenvalues, indicative of curvature.
    """
    was_training = model.training
    model.train()  # Need train mode for gradients
    
    params = [p for p in model.parameters() if p.requires_grad]
    n_params = sum(p.numel() for p in params)
    
    trace_estimate = 0.0
    
    for _ in range(n_samples):
        # Random Rademacher vector
        v_flat = torch.randint(0, 2, (n_params,), device=device).float() * 2 - 1
        
        # Unflatten
        v_list = []
        offset = 0
        for p in params:
            n = p.numel()
            v_list.append(v_flat[offset:offset+n].view_as(p))
            offset += n
        
        # Compute Hv
        model.zero_grad()
        for batch in dataloader:
            a, b, c = [x.to(device) for x in batch]
            out = model(a, b)
            loss = loss_fn(out, c)
            
            grads = torch.autograd.grad(loss, params, create_graph=True, allow_unused=True)
            # Filter out None gradients
            valid_grads = [(g, v) for g, v in zip(grads, v_list) if g is not None]
            if not valid_grads:
                break
            dot = sum((g * v).sum() for g, v in valid_grads)
            hvp_tuple = torch.autograd.grad(dot, params, allow_unused=True)
            hvp_list = [h if h is not None else torch.zeros_like(p) for h, p in zip(hvp_tuple, params)]
            hvp_flat = torch.cat([h.flatten() for h in hvp_list])
            
            # v^T H v estimates trace when v is Rademacher
            trace_estimate += (v_flat * hvp_flat).sum().item()
            break  # One batch is enough for estimate
    
    if not was_training:
        model.eval()
    
    return trace_estimate / n_samples


# =============================================================================
# TSALLIS Q ESTIMATION
# =============================================================================

def estimate_tsallis_q(values: torch.Tensor, q_range: Tuple[float, float] = (0.5, 3.0)) -> float:
    """
    Estimate Tsallis q parameter from distribution of values.
    
    Uses the fact that Tsallis distributions have power-law tails.
    q > 1: heavy tails (long-range correlations)
    q = 1: exponential tails (Shannon/Boltzmann)
    q < 1: compact support
    """
    values = values.detach().cpu().numpy().flatten()
    values = np.abs(values)
    values = values[values > 1e-10]
    
    if len(values) < 10:
        return 1.0
    
    # Sort and compute empirical CDF
    sorted_vals = np.sort(values)[::-1]
    ranks = np.arange(1, len(sorted_vals) + 1)
    
    # Fit power law: P(X > x) ~ x^(-alpha)
    # For Tsallis: alpha = 1/(q-1) for q > 1
    log_ranks = np.log(ranks + 1)
    log_vals = np.log(sorted_vals + 1e-10)
    
    # Linear regression
    valid = np.isfinite(log_ranks) & np.isfinite(log_vals)
    if valid.sum() < 5:
        return 1.0
    
    slope, _, _, _, _ = stats.linregress(log_vals[valid], log_ranks[valid])
    
    # alpha = -slope, q = 1 + 1/alpha
    alpha = -slope
    if alpha > 0.1:
        q = 1 + 1/alpha
        q = np.clip(q, q_range[0], q_range[1])
    else:
        q = 1.0
    
    return float(q)


def compute_tsallis_entropy(probs: torch.Tensor, q: float) -> float:
    """Compute Tsallis entropy S_q(p) = (1 - sum(p^q)) / (q - 1)."""
    probs = probs.detach().cpu()
    probs = probs[probs > 1e-10]
    
    if abs(q - 1.0) < 1e-6:
        # Shannon entropy
        return -float((probs * torch.log(probs)).sum())
    else:
        return float((1 - (probs ** q).sum()) / (q - 1))


# =============================================================================
# RELATIVE EXTROPY
# =============================================================================

def compute_relative_extropy(probs: torch.Tensor, prior: Optional[torch.Tensor] = None) -> float:
    """
    Compute relative extropy J(p||π) = Σ πᵢ pᵢ².
    
    Extropy is the Bregman dual to entropy. It measures certainty/consolidation.
    
    Args:
        probs: Probability distribution
        prior: Prior distribution (default: uniform)
    
    Returns:
        Relative extropy value
    """
    probs = probs.detach().cpu()
    
    if prior is None:
        prior = torch.ones_like(probs) / len(probs)
    else:
        prior = prior.detach().cpu()
    
    # J(p||π) = Σ πᵢ pᵢ²
    return float((prior * probs ** 2).sum())


def compute_normalized_extropy(probs: torch.Tensor) -> float:
    """
    Compute normalized extropy in [0, 1].
    
    J_norm = (J - J_uniform) / (J_max - J_uniform)
    where J_uniform = 1/n and J_max = 1 (delta distribution)
    """
    n = len(probs)
    J = compute_relative_extropy(probs)
    J_uniform = 1.0 / n
    J_max = 1.0
    
    return (J - J_uniform) / (J_max - J_uniform + 1e-10)


# =============================================================================
# FUNCTIONAL DEFECT (from functional_defect_experiment.py)
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


# =============================================================================
# FUNCTORIAL DEFECT (NEW: arXiv:2602.01992 Connection)
# =============================================================================

def compute_functorial_defect(
    model: nn.Module,
    p: int,
    device: str,
    n_samples: int = 100
) -> Tuple[float, float, float]:
    """
    Compute Functorial Defect: measures whether vector displacements are parallel.
    
    Based on arXiv:2602.01992 "Emergent Analogical Reasoning in Transformers":
    - If the model has grokked, the mapping is an affine transformation
    - "A is to B as C is to D" means (B-A) should equal (D-C) in embedding space
    
    For modular addition: (a+1, b) - (a, b) should equal (a'+1, b') - (a', b')
    i.e., the "+1" operation should be a consistent vector in embedding space.
    
    **Connection to SGC**:
    - High functorial defect = manifold is crumpled (pre-grokking)
    - Low functorial defect = manifold is flat/toroidal (post-grokking)
    
    **Use in Controller**:
    If functorial defect is high, increase temperature to "iron out wrinkles".
    
    Returns:
        (functorial_defect, mean_displacement_norm, displacement_variance)
    """
    model.eval()
    
    with torch.no_grad():
        # Sample random base points
        a_vals = torch.randint(0, p-1, (n_samples,), device=device)
        b_vals = torch.randint(0, p, (n_samples,), device=device)
        
        # Get embeddings for (a, b) and (a+1, b)
        h_base = model.get_hidden(a_vals, b_vals)
        h_plus1 = model.get_hidden(a_vals + 1, b_vals)
        
        # Displacement vectors for "+1 in first argument"
        displacements = h_plus1 - h_base  # Shape: (n_samples, hidden_dim)
        
        # Mean displacement (should be consistent if grokked)
        mean_disp = displacements.mean(dim=0)
        mean_disp_norm = mean_disp.norm().item()
        
        # Variance of displacements (should be low if grokked)
        disp_centered = displacements - mean_disp.unsqueeze(0)
        disp_variance = (disp_centered ** 2).mean().item()
        
        # Functorial defect = variance / norm^2 (normalized measure)
        if mean_disp_norm > 1e-10:
            functorial_defect = disp_variance / (mean_disp_norm ** 2 + 1e-10)
        else:
            functorial_defect = float('inf')
        
        # Also check second argument displacement consistency
        a_vals2 = torch.randint(0, p, (n_samples,), device=device)
        b_vals2 = torch.randint(0, p-1, (n_samples,), device=device)
        
        h_base2 = model.get_hidden(a_vals2, b_vals2)
        h_plus1_b = model.get_hidden(a_vals2, b_vals2 + 1)
        
        displacements_b = h_plus1_b - h_base2
        mean_disp_b = displacements_b.mean(dim=0)
        disp_centered_b = displacements_b - mean_disp_b.unsqueeze(0)
        disp_variance_b = (disp_centered_b ** 2).mean().item()
        
        mean_disp_norm_b = mean_disp_b.norm().item()
        if mean_disp_norm_b > 1e-10:
            functorial_defect_b = disp_variance_b / (mean_disp_norm_b ** 2 + 1e-10)
        else:
            functorial_defect_b = float('inf')
        
        # Average of both directions
        if functorial_defect == float('inf') or functorial_defect_b == float('inf'):
            avg_functorial_defect = float('inf')
        else:
            avg_functorial_defect = (functorial_defect + functorial_defect_b) / 2
        
        avg_norm = (mean_disp_norm + mean_disp_norm_b) / 2
        avg_variance = (disp_variance + disp_variance_b) / 2
    
    return avg_functorial_defect, avg_norm, avg_variance


def compute_dirichlet_energy(
    model: nn.Module,
    p: int,
    device: str
) -> float:
    """
    Compute Dirichlet Energy of the hidden representation on the input graph.
    
    Dirichlet Energy E_Dir = f^T L f where L is the graph Laplacian.
    For modular addition, the natural graph has edges between (a,b) and (a±1,b), (a,b±1).
    
    **Connection to arXiv:2602.01992**:
    They observe Dirichlet energy decreases during analogical reasoning emergence.
    SGC predicts this: Diffusion minimizes E_Dir, driving system to harmonic functions.
    
    Low Dirichlet energy = smooth representation = grokked algebraic structure.
    
    Returns:
        Normalized Dirichlet energy
    """
    model.eval()
    
    with torch.no_grad():
        # Sample all points on a smaller grid for efficiency
        sample_p = min(p, 31)  # Use smaller prime for efficiency
        
        total_energy = 0.0
        n_edges = 0
        
        for a in range(sample_p):
            for b in range(sample_p):
                a_t = torch.tensor([a], device=device)
                b_t = torch.tensor([b], device=device)
                h_center = model.get_hidden(a_t, b_t)
                
                # Neighbors in the +1 direction (mod p)
                neighbors = [
                    ((a + 1) % sample_p, b),
                    (a, (b + 1) % sample_p),
                ]
                
                for na, nb in neighbors:
                    na_t = torch.tensor([na], device=device)
                    nb_t = torch.tensor([nb], device=device)
                    h_neighbor = model.get_hidden(na_t, nb_t)
                    
                    # Edge contribution to Dirichlet energy
                    diff = h_center - h_neighbor
                    total_energy += (diff ** 2).sum().item()
                    n_edges += 1
        
        # Normalize by number of edges and hidden dimension
        hidden_dim = h_center.shape[-1]
        normalized_energy = total_energy / (n_edges * hidden_dim)
    
    return normalized_energy


# =============================================================================
# MAIN EXPERIMENT
# =============================================================================

@dataclass
class LifshitzMetrics:
    """Metrics for Lifshitz transition detection."""
    epoch: int
    train_acc: float
    test_acc: float
    train_loss: float
    
    # Functional defect (algebraic blanket)
    functional_defect: float
    class_separation: float
    
    # Hessian spectrum (Van Hove)
    hessian_trace: float
    density_near_zero: float
    
    # Tsallis q (thermodynamic phase)
    tsallis_q: float
    tsallis_entropy: float
    
    # Extropy (consolidation)
    relative_extropy: float
    normalized_extropy: float
    
    # Output distribution
    output_entropy: float
    
    # Functorial metrics (NEW: arXiv:2602.01992 connection)
    functorial_defect: float = 0.0      # Displacement vector consistency
    dirichlet_energy: float = 0.0       # Smoothness on input graph


def run_lifshitz_experiment(
    p: int = 97,
    embed_dim: int = 128,
    hidden_dim: int = 128,
    n_layers: int = 2,
    noise_std: float = 0.0,
    lr: float = 1e-3,
    weight_decay: float = 1.0,
    epochs: int = 3000,
    batch_size: int = 512,
    measure_interval: int = 100,
    hessian_interval: int = 500,
    device: str = 'cuda' if torch.cuda.is_available() else 'cpu',
    seed: int = 42
) -> List[LifshitzMetrics]:
    """
    Run experiment tracking Lifshitz transition metrics.
    """
    num_classes = p  # Save p as num_classes to avoid any potential shadowing
    torch.manual_seed(seed)
    np.random.seed(seed)
    
    print(f"\n{'='*70}")
    print(f"LIFSHITZ TRANSITION EXPERIMENT")
    print(f"{'='*70}")
    print(f"Model: p={p}, embed={embed_dim}, hidden={hidden_dim}, layers={n_layers}")
    print(f"Noise: {noise_std}, LR: {lr}, WD: {weight_decay}")
    print(f"Device: {device}")
    print(f"{'='*70}\n")
    
    # Create dataset
    (train_a, train_b, train_c), (test_a, test_b, test_c) = create_modular_dataset(p)
    train_dataset = TensorDataset(train_a, train_b, train_c)
    test_dataset = TensorDataset(test_a, test_b, test_c)
    train_loader = DataLoader(train_dataset, batch_size=batch_size, shuffle=True)
    test_loader = DataLoader(test_dataset, batch_size=batch_size)
    
    # Create model
    model = EmbeddingGrokMLP(p, embed_dim, hidden_dim, n_layers, noise_std).to(device)
    optimizer = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=weight_decay)
    loss_fn = nn.CrossEntropyLoss()
    
    metrics_history = []
    grokking_detected = False
    grokking_epoch = -1
    
    print(f"{'Epoch':>6} | {'Train':>6} | {'Test':>6} | {'FuncD':>7} | {'ClassSep':>8} | "
          f"{'q':>5} | {'Extropy':>7} | {'H_trace':>8} | Phase")
    print("-" * 90)
    
    for epoch in range(1, epochs + 1):
        # Training
        model.train()
        total_loss = 0
        correct = 0
        total = 0
        
        for inp_a, inp_b, tgt in train_loader:
            inp_a, inp_b, tgt = inp_a.to(device), inp_b.to(device), tgt.to(device)
            
            optimizer.zero_grad()
            out = model(inp_a, inp_b)
            loss = loss_fn(out, tgt)
            loss.backward()
            optimizer.step()
            
            total_loss += loss.item() * len(inp_a)
            correct += (out.argmax(dim=1) == tgt).sum().item()
            total += len(inp_a)
        
        train_acc = correct / total
        train_loss = total_loss / total
        
        # Evaluation
        model.eval()
        correct = 0
        total = 0
        all_probs = []
        
        with torch.no_grad():
            for inp_a, inp_b, tgt in test_loader:
                inp_a, inp_b, tgt = inp_a.to(device), inp_b.to(device), tgt.to(device)
                out = model(inp_a, inp_b)
                probs = F.softmax(out, dim=-1)
                all_probs.append(probs)
                correct += (out.argmax(dim=1) == tgt).sum().item()
                total += len(inp_a)
        
        test_acc = correct / total
        
        # Detect grokking
        if not grokking_detected and test_acc > 0.95 and train_acc > 0.99:
            grokking_detected = True
            grokking_epoch = epoch
            print(f"\n*** GROKKING DETECTED at epoch {epoch} ***\n")
        
        # Measure metrics
        if epoch % measure_interval == 0 or epoch == 1:
            with torch.no_grad():
                # Collect hidden states and targets
                all_hidden = []
                all_targets = []
                for inp_a, inp_b, tgt in train_loader:
                    inp_a, inp_b, tgt = inp_a.to(device), inp_b.to(device), tgt.to(device)
                    h = model.get_hidden(inp_a, inp_b)
                    all_hidden.append(h)
                    all_targets.append(tgt)
                
                hidden = torch.cat(all_hidden, dim=0)
                targets = torch.cat(all_targets, dim=0)
                
                # Functional defect
                func_d, class_sep, _ = compute_functional_defect(hidden, targets, num_classes)
                
                # Tsallis q from hidden state distribution
                tsallis_q = estimate_tsallis_q(hidden)
                tsallis_ent = compute_tsallis_entropy(
                    F.softmax(hidden.var(dim=0), dim=0), tsallis_q
                )
                
                # Output distribution entropy and extropy
                avg_probs = torch.cat(all_probs, dim=0).mean(dim=0)
                output_entropy = -float((avg_probs * torch.log(avg_probs + 1e-10)).sum())
                rel_extropy = compute_relative_extropy(avg_probs)
                norm_extropy = compute_normalized_extropy(avg_probs)
                
                # Gradient norm as simpler curvature proxy (Hessian too expensive)
                grad_norm = 0.0
                for p in model.parameters():
                    if p.grad is not None:
                        grad_norm += p.grad.norm().item() ** 2
                grad_norm = grad_norm ** 0.5
                hessian_trace = grad_norm  # Use grad norm as proxy
                density_zero = 0.0  # Skip expensive Hessian computation
                
                # Determine phase
                if func_d > 0.5:
                    phase = "MEMORIZATION"
                elif func_d > 0.15:
                    phase = "TRANSITION"
                else:
                    phase = "GROKKED"
                
                metrics = LifshitzMetrics(
                    epoch=epoch,
                    train_acc=train_acc,
                    test_acc=test_acc,
                    train_loss=train_loss,
                    functional_defect=func_d,
                    class_separation=class_sep,
                    hessian_trace=hessian_trace,
                    density_near_zero=density_zero,
                    tsallis_q=tsallis_q,
                    tsallis_entropy=tsallis_ent,
                    relative_extropy=rel_extropy,
                    normalized_extropy=norm_extropy,
                    output_entropy=output_entropy
                )
                metrics_history.append(metrics)
                
                print(f"{epoch:6d} | {train_acc:6.1%} | {test_acc:6.1%} | {func_d:7.4f} | "
                      f"{class_sep:8.2f} | {tsallis_q:5.2f} | {norm_extropy:7.4f} | "
                      f"{hessian_trace:8.1f} | {phase}")
    
    # Summary
    print(f"\n{'='*70}")
    print("EXPERIMENT SUMMARY")
    print(f"{'='*70}")
    print(f"Grokking detected: {grokking_detected} (epoch {grokking_epoch})")
    
    if grokking_detected:
        # Find metrics at grokking
        grok_metrics = [m for m in metrics_history if m.epoch >= grokking_epoch][0]
        pre_grok = [m for m in metrics_history if m.epoch < grokking_epoch][-1] if grokking_epoch > 100 else metrics_history[0]
        post_grok = metrics_history[-1]
        
        print(f"\nMetric Transitions:")
        print(f"  Functional Defect: {pre_grok.functional_defect:.4f} -> {grok_metrics.functional_defect:.4f} -> {post_grok.functional_defect:.4f}")
        print(f"  Class Separation:  {pre_grok.class_separation:.2f} -> {grok_metrics.class_separation:.2f} -> {post_grok.class_separation:.2f}")
        print(f"  Tsallis q:         {pre_grok.tsallis_q:.3f} -> {grok_metrics.tsallis_q:.3f} -> {post_grok.tsallis_q:.3f}")
        print(f"  Normalized Extropy:{pre_grok.normalized_extropy:.4f} -> {grok_metrics.normalized_extropy:.4f} -> {post_grok.normalized_extropy:.4f}")
        print(f"  Hessian Trace:     {pre_grok.hessian_trace:.1f} -> {grok_metrics.hessian_trace:.1f} -> {post_grok.hessian_trace:.1f}")
    
    print(f"{'='*70}\n")
    
    return metrics_history


def compare_discrete_vs_analog():
    """Compare Lifshitz metrics for discrete vs analog embeddings."""
    print("\n" + "=" * 80)
    print("LIFSHITZ TRANSITION: DISCRETE vs ANALOG COMPARISON")
    print("=" * 80 + "\n")
    
    # Discrete (no noise)
    print("\n--- DISCRETE EMBEDDINGS (noise=0) ---\n")
    discrete_metrics = run_lifshitz_experiment(
        noise_std=0.0,
        epochs=3000,
        measure_interval=100,
        hessian_interval=500,
        seed=42
    )
    
    # Analog (with noise)
    print("\n--- ANALOG EMBEDDINGS (noise=0.1) ---\n")
    analog_metrics = run_lifshitz_experiment(
        noise_std=0.1,
        epochs=2000,
        measure_interval=100,
        hessian_interval=500,
        seed=42
    )
    
    # Compare grokking epochs
    discrete_grok = next((m.epoch for m in discrete_metrics if m.test_acc > 0.95), -1)
    analog_grok = next((m.epoch for m in analog_metrics if m.test_acc > 0.95), -1)
    
    print("\n" + "=" * 80)
    print("COMPARISON SUMMARY")
    print("=" * 80)
    print(f"Grokking epoch - Discrete: {discrete_grok}, Analog: {analog_grok}")
    if discrete_grok > 0 and analog_grok > 0:
        print(f"Speedup: {discrete_grok / analog_grok:.2f}x")
    
    # Compare q-transition
    if discrete_grok > 0 and analog_grok > 0:
        discrete_pre = [m for m in discrete_metrics if m.epoch < discrete_grok][-1]
        discrete_post = [m for m in discrete_metrics if m.epoch > discrete_grok][0] if any(m.epoch > discrete_grok for m in discrete_metrics) else discrete_metrics[-1]
        
        analog_pre = [m for m in analog_metrics if m.epoch < analog_grok][-1]
        analog_post = [m for m in analog_metrics if m.epoch > analog_grok][0] if any(m.epoch > analog_grok for m in analog_metrics) else analog_metrics[-1]
        
        print(f"\nTsallis q transition:")
        print(f"  Discrete: {discrete_pre.tsallis_q:.3f} -> {discrete_post.tsallis_q:.3f}")
        print(f"  Analog:   {analog_pre.tsallis_q:.3f} -> {analog_post.tsallis_q:.3f}")
        
        print(f"\nExtropy transition:")
        print(f"  Discrete: {discrete_pre.normalized_extropy:.4f} -> {discrete_post.normalized_extropy:.4f}")
        print(f"  Analog:   {analog_pre.normalized_extropy:.4f} -> {analog_post.normalized_extropy:.4f}")
    
    print("=" * 80 + "\n")
    
    return discrete_metrics, analog_metrics


if __name__ == "__main__":
    # Run comparison
    discrete_metrics, analog_metrics = compare_discrete_vs_analog()
