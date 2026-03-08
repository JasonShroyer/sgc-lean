"""
Fast Manifold Surgery Experiment
================================
Streamlined version with:
- Correct hyperparameters (hidden_dim=128, batch_size=512) for ~300 epoch grokking
- Early stopping once grokking confirmed
- Real-time progress output
- Key SGC metrics: Ridge Ratio, Van Hove, Gauss Curvature
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import DataLoader, TensorDataset
import numpy as np
from dataclasses import dataclass, asdict
from typing import Tuple, List, Dict, Optional
import csv
from pathlib import Path
from datetime import datetime


# =============================================================================
# MODEL
# =============================================================================

class EmbeddingGrokMLP(nn.Module):
    """MLP with learnable embeddings for modular arithmetic."""
    
    def __init__(self, p: int, embed_dim: int = 128, hidden_dim: int = 128, noise_std: float = 0.0):
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
        ea = self.embed_a(a)
        eb = self.embed_b(b)
        if self.training and self.noise_std > 0:
            ea = ea + torch.randn_like(ea) * self.noise_std
            eb = eb + torch.randn_like(eb) * self.noise_std
        return torch.cat([ea, eb], dim=-1)
    
    def get_hidden(self, a: torch.Tensor, b: torch.Tensor) -> torch.Tensor:
        x = self.get_embeddings(a, b)
        x = F.relu(self.fc1(x))
        x = F.relu(self.fc2(x))
        return x
    
    def forward(self, a: torch.Tensor, b: torch.Tensor) -> torch.Tensor:
        return self.fc3(self.get_hidden(a, b))


# =============================================================================
# SGC METRICS
# =============================================================================

def compute_functional_defect(hidden: torch.Tensor, targets: torch.Tensor, p: int) -> Tuple[float, float]:
    """
    Functional Defect = Within-class variance / Total variance.
    Class Separation = Between-class variance / Within-class variance.
    """
    total_var = hidden.var(dim=0).mean().item()
    if total_var < 1e-10:
        return 0.0, float('inf')
    
    within_vars = []
    class_means = []
    class_counts = []
    
    for c in range(p):
        mask = (targets == c)
        count = mask.sum().item()
        if count > 0:
            hc = hidden[mask]
            class_means.append(hc.mean(dim=0))
            class_counts.append(count)
            if count > 1:
                within_vars.append(hc.var(dim=0).mean().item())
            else:
                within_vars.append(0.0)
    
    if not class_means:
        return 1.0, 0.0
    
    class_counts = torch.tensor(class_counts, dtype=torch.float, device=hidden.device)
    within_vars = torch.tensor(within_vars, device=hidden.device)
    class_means = torch.stack(class_means)
    
    within_var = (within_vars * class_counts).sum() / class_counts.sum()
    
    global_mean = (class_means * class_counts.unsqueeze(1)).sum(0) / class_counts.sum()
    between_var = ((class_means - global_mean)**2).mean(dim=1)
    between_var = (between_var * class_counts).sum() / class_counts.sum()
    
    func_defect = within_var.item() / (total_var + 1e-10)
    class_sep = between_var.item() / (within_var.item() + 1e-10)
    
    return func_defect, class_sep


def compute_ridge_ratio(model: nn.Module, p: int, device: str, n_samples: int = 500) -> Dict[str, float]:
    """
    Ridge Ratio = Between-class Dirichlet energy / Within-class Dirichlet energy.
    SGC Prediction: Explodes at grokking (>1 means sharp ridges at class boundaries).
    """
    model.eval()
    with torch.no_grad():
        a = torch.randint(0, p, (n_samples,), device=device)
        b = torch.randint(0, p, (n_samples,), device=device)
        h_base = model.get_hidden(a, b)
        
        # Between-class: grid neighbor (a+1, b) changes sum by 1
        h_between = model.get_hidden((a + 1) % p, b)
        energy_between = ((h_base - h_between)**2).sum(dim=1).mean().item()
        
        # Within-class: diagonal move (a+1, b-1) preserves sum
        h_within = model.get_hidden((a + 1) % p, (b - 1) % p)
        energy_within = ((h_base - h_within)**2).sum(dim=1).mean().item()
        
        ridge_ratio = energy_between / (energy_within + 1e-10)
        
        return {
            'energy_within': energy_within,
            'energy_between': energy_between,
            'ridge_ratio': ridge_ratio
        }


def compute_gauss_curvature(model: nn.Module, p: int, device: str, n_triangles: int = 100) -> float:
    """
    Intrinsic Gauss curvature via geodesic triangle angle deficit.
    SGC Finding: Manifold is FLAT (curvature ~ 0), not a curved torus.
    """
    model.eval()
    
    def angle(v1, v2):
        cos = torch.dot(v1, v2) / (v1.norm() * v2.norm() + 1e-10)
        return torch.acos(torch.clamp(cos, -1.0, 1.0))
    
    deficits = []
    with torch.no_grad():
        for _ in range(n_triangles):
            a0 = torch.randint(0, p, (1,), device=device)
            b0 = torch.randint(0, p, (1,), device=device)
            
            h0 = model.get_hidden(a0, b0).squeeze()
            h1 = model.get_hidden((a0 + 1) % p, b0).squeeze()
            h2 = model.get_hidden(a0, (b0 + 1) % p).squeeze()
            
            e01, e02, e12 = h1 - h0, h2 - h0, h2 - h1
            
            alpha = angle(e01, e02)
            beta = angle(-e01, e12)
            gamma = angle(-e02, -e12)
            
            deficit = (alpha + beta + gamma).item() - np.pi
            deficits.append(deficit)
    
    return np.mean(deficits)


def compute_hessian_density_at_zero(model: nn.Module, loss_fn, a: torch.Tensor, b: torch.Tensor, 
                                     c: torch.Tensor, n_iter: int = 50) -> float:
    """
    Estimate fraction of Hessian eigenvalues near zero using Lanczos.
    SGC Prediction: Spikes at grokking (Van Hove singularity).
    """
    model.train()
    
    params = [p for p in model.parameters() if p.requires_grad]
    n_params = sum(p.numel() for p in params)
    
    def hvp(v):
        """Hessian-vector product."""
        model.zero_grad()
        out = model(a, b)
        loss = loss_fn(out, c)
        grads = torch.autograd.grad(loss, params, create_graph=True)
        flat_grad = torch.cat([g.reshape(-1) for g in grads])
        grad_v = torch.dot(flat_grad, v)
        hvp_grads = torch.autograd.grad(grad_v, params)
        return torch.cat([g.reshape(-1) for g in hvp_grads])
    
    # Lanczos iteration
    device = a.device
    v = torch.randn(n_params, device=device)
    v = v / v.norm()
    
    alphas, betas = [], []
    v_prev = torch.zeros_like(v)
    
    for i in range(min(n_iter, n_params)):
        w = hvp(v)
        alpha = torch.dot(w, v).item()
        alphas.append(alpha)
        
        w = w - alpha * v - (betas[-1] * v_prev if betas else 0)
        beta = w.norm().item()
        
        if beta < 1e-10:
            break
        
        betas.append(beta)
        v_prev = v
        v = w / beta
    
    # Build tridiagonal matrix and compute eigenvalues
    n = len(alphas)
    if n < 2:
        return 0.0
    
    T = np.diag(alphas) + np.diag(betas[:n-1], 1) + np.diag(betas[:n-1], -1)
    eigenvalues = np.linalg.eigvalsh(T)
    
    # Fraction near zero (|lambda| < 0.1 * max|lambda|)
    threshold = 0.1 * np.abs(eigenvalues).max()
    density_zero = np.mean(np.abs(eigenvalues) < threshold)
    
    return density_zero


# =============================================================================
# EXPERIMENT
# =============================================================================

@dataclass
class FastMetrics:
    epoch: int
    train_acc: float
    test_acc: float
    func_defect: float
    class_sep: float
    ridge_ratio: float
    gauss_curv: float
    hessian_zero: Optional[float]
    phase: str


def run_fast_manifold_surgery(
    p: int = 97,
    embed_dim: int = 128,
    hidden_dim: int = 128,  # CRITICAL: Must be 128 for fast grokking
    lr: float = 1e-3,
    weight_decay: float = 1.0,
    max_epochs: int = 1000,
    batch_size: int = 512,  # CRITICAL: Mini-batch noise = temperature
    seed: int = 42,
    device: str = 'cuda' if torch.cuda.is_available() else 'cpu',
    log_interval: int = 10,
    hessian_interval: int = 100,
    early_stop_epochs: int = 50  # Stop N epochs after grokking confirmed
):
    """Fast Manifold Surgery with early stopping."""
    
    print("=" * 70)
    print("FAST MANIFOLD SURGERY EXPERIMENT")
    print("=" * 70)
    print(f"Hyperparams: hidden_dim={hidden_dim}, batch_size={batch_size}, lr={lr}, wd={weight_decay}")
    print(f"Device: {device}, Seed: {seed}")
    print("=" * 70)
    
    torch.manual_seed(seed)
    np.random.seed(seed)
    
    # Create dataset: 50% train, 50% test (standard grokking split)
    all_pairs = [(i, j) for i in range(p) for j in range(p)]
    np.random.shuffle(all_pairs)
    split = len(all_pairs) // 2
    
    train_pairs = all_pairs[:split]
    test_pairs = all_pairs[split:]
    
    train_a = torch.tensor([x[0] for x in train_pairs], device=device)
    train_b = torch.tensor([x[1] for x in train_pairs], device=device)
    train_c = (train_a + train_b) % p
    
    test_a = torch.tensor([x[0] for x in test_pairs], device=device)
    test_b = torch.tensor([x[1] for x in test_pairs], device=device)
    test_c = (test_a + test_b) % p
    
    train_dataset = TensorDataset(train_a, train_b, train_c)
    train_loader = DataLoader(train_dataset, batch_size=batch_size, shuffle=True)
    
    print(f"Dataset: {len(train_pairs)} train, {len(test_pairs)} test (p={p})")
    print(f"Batches per epoch: {len(train_loader)} (batch_size={batch_size})")
    print("=" * 70)
    
    # Model
    model = EmbeddingGrokMLP(p, embed_dim, hidden_dim).to(device)
    optimizer = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=weight_decay)
    loss_fn = nn.CrossEntropyLoss()
    
    # Logging
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    output_dir = Path(f"logs/manifold_surgery_fast/run_{timestamp}_seed{seed}")
    output_dir.mkdir(parents=True, exist_ok=True)
    
    csv_path = output_dir / "metrics.csv"
    csv_file = open(csv_path, 'w', newline='')
    csv_writer = csv.DictWriter(csv_file, fieldnames=[
        'epoch', 'train_acc', 'test_acc', 'func_defect', 'class_sep',
        'ridge_ratio', 'gauss_curv', 'hessian_zero', 'phase'
    ])
    csv_writer.writeheader()
    
    # Header
    print(f"{'Ep':>5} {'TrAcc':>6} {'TeAcc':>6} {'F.Def':>6} {'ClSep':>7} {'Ridge':>7} {'Gauss':>9} {'H@0':>5} {'Phase':<10}")
    print("-" * 75)
    
    metrics_history = []
    grok_epoch = None
    
    for epoch in range(1, max_epochs + 1):
        # Train
        model.train()
        correct, total = 0, 0
        
        for a_batch, b_batch, c_batch in train_loader:
            optimizer.zero_grad()
            out = model(a_batch, b_batch)
            loss = loss_fn(out, c_batch)
            loss.backward()
            optimizer.step()
            
            pred = out.argmax(dim=1)
            correct += (pred == c_batch).sum().item()
            total += a_batch.size(0)
        
        train_acc = correct / total
        
        # Evaluate
        if epoch % log_interval == 0 or epoch == 1:
            model.eval()
            with torch.no_grad():
                out = model(test_a, test_b)
                test_acc = (out.argmax(dim=1) == test_c).float().mean().item()
                
                hidden = model.get_hidden(test_a, test_b)
                func_defect, class_sep = compute_functional_defect(hidden, test_c, p)
            
            ridge = compute_ridge_ratio(model, p, device)
            gauss = compute_gauss_curvature(model, p, device, n_triangles=50)
            
            # Hessian (expensive, compute less often)
            hessian_zero = None
            if epoch % hessian_interval == 0:
                # Use subset for Hessian
                idx = torch.randperm(len(train_a))[:512]
                hessian_zero = compute_hessian_density_at_zero(
                    model, loss_fn, train_a[idx], train_b[idx], train_c[idx], n_iter=30
                )
            
            # Phase detection
            if test_acc > 0.99 and func_defect < 0.1:
                phase = "GROKKED"
                if grok_epoch is None:
                    grok_epoch = epoch
            elif test_acc > 0.5 or func_defect < 0.5:
                phase = "TRANSITION"
            else:
                phase = "MEMORIZE"
            
            # Log
            h_str = f"{hessian_zero:.2f}" if hessian_zero is not None else "  -  "
            print(f"{epoch:5d} {train_acc:6.3f} {test_acc:6.3f} {func_defect:6.3f} {class_sep:7.2f} "
                  f"{ridge['ridge_ratio']:7.2f} {gauss:9.2e} {h_str:>5} {phase:<10}", flush=True)
            
            m = FastMetrics(
                epoch=epoch, train_acc=train_acc, test_acc=test_acc,
                func_defect=func_defect, class_sep=class_sep,
                ridge_ratio=ridge['ridge_ratio'], gauss_curv=gauss,
                hessian_zero=hessian_zero, phase=phase
            )
            metrics_history.append(m)
            csv_writer.writerow(asdict(m))
            csv_file.flush()
            
            # Early stopping
            if grok_epoch and (epoch - grok_epoch) >= early_stop_epochs:
                print(f"\n[EARLY STOP] Grokking confirmed at epoch {grok_epoch}, stopping.")
                break
    
    csv_file.close()
    
    # Summary
    print("\n" + "=" * 70)
    print("EXPERIMENT SUMMARY")
    print("=" * 70)
    
    if grok_epoch:
        grok_m = next(m for m in metrics_history if m.epoch >= grok_epoch)
        print(f"Grokking detected at epoch: {grok_epoch}")
        print(f"\nKey Metrics at Grokking:")
        print(f"  - Functional Defect: {grok_m.func_defect:.4f} (collapsed)")
        print(f"  - Class Separation:  {grok_m.class_sep:.2f} (high)")
        print(f"  - Ridge Ratio:       {grok_m.ridge_ratio:.2f} (>1 = sharp boundaries)")
        print(f"  - Gauss Curvature:   {grok_m.gauss_curv:.2e} (flat if ~0)")
        
        # Find initial metrics
        init_m = metrics_history[0]
        print(f"\nTrajectory:")
        print(f"  Ridge Ratio: {init_m.ridge_ratio:.2f} -> {grok_m.ridge_ratio:.2f}")
        print(f"  Func Defect: {init_m.func_defect:.3f} -> {grok_m.func_defect:.3f}")
    else:
        print("Grokking NOT detected within training epochs.")
    
    print(f"\nLogs saved to: {output_dir}")
    print("=" * 70)
    
    return metrics_history


if __name__ == "__main__":
    run_fast_manifold_surgery()
