#!/usr/bin/env python3
"""
SGC-Grounded Iterative Spectral Refinement (ISR) Sudoku Experiment

A rigorous empirical test of the ISR hypothesis using SGC renormalization formalism:
the learned recursion succeeds by driving a coarse-grained closure condition,
operationalized as collapse of a leakage/vertical-defect proxy under a
partition-defined conditional-expectation projector Π̂.

## Lean Theory Reference
- src/SGC/Renormalization/Approximate.lean: CoarseProjector and leakage-defect perspective
  - CoarseProjector: Π = lift ∘ Q, weighted conditional expectation onto partition blocks
  - DefectOperator: D = (I - Π) ∘ L ∘ Π, the "leakage" from coarse subspace
- ARCHITECTURE.md: "observational physics" and explicit weight pattern

## Hypotheses
- H1 (Closure): ε_t → 0 is necessary for solving
- H2 (Mechanism): η_t peaks during active computation, then collapses
- H3 (Support): Rank(z_t) remains high even as entropy(y_t) drops

Usage:
    python iterative_spectral_refinement.py --generate --num_puzzles 10000 --epochs 100

Author: SGC Project | License: Apache 2.0
"""

import argparse, json, os, time
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Tuple
import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import DataLoader, Dataset
from torch.utils.tensorboard import SummaryWriter
from tqdm import tqdm

try:
    import matplotlib.pyplot as plt
    MATPLOTLIB_AVAILABLE = True
except ImportError:
    MATPLOTLIB_AVAILABLE = False

# ═══════════════════════════════════════════════════════════════════════════════
# CONFIGURATION
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class ISRConfig:
    hidden_dim: int = 128
    num_layers: int = 2
    T_steps: int = 30
    max_params: int = 100_000
    batch_size: int = 64
    learning_rate: float = 1e-3
    epochs: int = 100
    data_path: Optional[str] = None
    generate: bool = False
    num_puzzles: int = 10000
    seed: int = 42
    log_dir: str = "logs/isr"
    log_interval: int = 100
    snapshot_interval: int = 5
    eta_mode: str = "hutchinson"
    eta_probes: int = 4
    eta_batch_subsample: int = 8
    weights_mode: str = "entropy"

# ═══════════════════════════════════════════════════════════════════════════════
# SUDOKU DATASET
# ═══════════════════════════════════════════════════════════════════════════════

class SudokuDataset(Dataset):
    def __init__(self, puzzles: np.ndarray, solutions: np.ndarray):
        self.puzzles = torch.tensor(puzzles, dtype=torch.long)
        self.solutions = torch.tensor(solutions, dtype=torch.long)
    
    def __len__(self): return len(self.puzzles)
    def __getitem__(self, idx): return self.puzzles[idx], self.solutions[idx]
    
    @staticmethod
    def generate_puzzles(num_puzzles: int, seed: int = 42, 
                         min_clues: int = 17, max_clues: int = 35) -> Tuple[np.ndarray, np.ndarray]:
        np.random.seed(seed)
        puzzles, solutions = [], []
        
        def is_valid(grid, row, col, num):
            if num in grid[row]: return False
            if num in grid[:, col]: return False
            br, bc = 3 * (row // 3), 3 * (col // 3)
            if num in grid[br:br+3, bc:bc+3]: return False
            return True
        
        def solve(grid):
            for i in range(9):
                for j in range(9):
                    if grid[i, j] == 0:
                        nums = list(range(1, 10))
                        np.random.shuffle(nums)
                        for num in nums:
                            if is_valid(grid, i, j, num):
                                grid[i, j] = num
                                if solve(grid): return True
                                grid[i, j] = 0
                        return False
            return True
        
        for _ in tqdm(range(num_puzzles), desc="Generating puzzles"):
            grid = np.zeros((9, 9), dtype=np.int64)
            solve(grid)
            solution = grid.copy()
            num_clues = np.random.randint(min_clues, max_clues + 1)
            cells = list(range(81))
            np.random.shuffle(cells)
            puzzle = solution.copy()
            for idx in cells[:81 - num_clues]:
                puzzle[idx // 9, idx % 9] = 0
            puzzles.append(puzzle.flatten())
            solutions.append(solution.flatten())
        return np.array(puzzles), np.array(solutions)

# ═══════════════════════════════════════════════════════════════════════════════
# ISR SOLVER MODEL (< 100k params)
# ═══════════════════════════════════════════════════════════════════════════════

class ISRSolver(nn.Module):
    def __init__(self, hidden_dim: int = 128, num_layers: int = 2):
        super().__init__()
        self.hidden_dim = hidden_dim
        self.input_dim = 19  # 10 (puzzle) + 9 (y logits)
        
        layers = []
        in_dim = self.input_dim + hidden_dim
        for _ in range(num_layers):
            layers.extend([nn.Linear(in_dim, hidden_dim), nn.LayerNorm(hidden_dim), nn.GELU()])
            in_dim = hidden_dim
        self.core = nn.Sequential(*layers)
        self.y_head = nn.Linear(hidden_dim, 9)
        self.z_head = nn.Linear(hidden_dim, hidden_dim)
        self.z_init = nn.Parameter(torch.randn(hidden_dim) * 0.01)
        
        total = sum(p.numel() for p in self.parameters() if p.requires_grad)
        print(f"[ISRSolver] Parameters: {total:,}")
    
    def encode_puzzle(self, puzzle): return F.one_hot(puzzle, num_classes=10).float()
    
    def forward_step(self, y_t, z_t, x_enc):
        combined = torch.cat([x_enc, y_t, z_t], dim=-1)
        h = self.core(combined.view(-1, combined.shape[-1])).view(y_t.shape[0], 81, self.hidden_dim)
        return self.y_head(h), self.z_head(h)
    
    def forward(self, puzzle, T=30, return_trajectory=False):
        batch_size, device = puzzle.shape[0], puzzle.device
        x_enc = self.encode_puzzle(puzzle)
        y_t = torch.zeros(batch_size, 81, 9, device=device)
        z_t = self.z_init.unsqueeze(0).unsqueeze(0).expand(batch_size, 81, -1)
        
        y_traj, z_traj = [y_t], [z_t] if return_trajectory else (None, None)
        for _ in range(T):
            y_t, z_t = self.forward_step(y_t, z_t, x_enc)
            if return_trajectory: y_traj.append(y_t); z_traj.append(z_t)
        
        result = {'y_final': y_t, 'z_final': z_t}
        if return_trajectory:
            result['y_traj'] = torch.stack(y_traj, dim=0)
            result['z_traj'] = torch.stack(z_traj, dim=0)
        return result
    
    def compute_loss(self, y_final, solution, puzzle):
        mask = (puzzle == 0).float().view(-1)
        target = (solution - 1).view(-1)
        ce = F.cross_entropy(y_final.view(-1, 9), target, reduction='none')
        return (ce * mask).sum() / (mask.sum() + 1e-8)
    
    def compute_accuracy(self, y_final, solution, puzzle):
        pred = y_final.argmax(dim=-1) + 1
        pred = torch.where(puzzle > 0, puzzle, pred)
        mask = (puzzle == 0)
        cell_acc = ((pred == solution) & mask).float().sum() / (mask.float().sum() + 1e-8)
        solved_acc = (pred == solution).all(dim=-1).float().mean()
        return {'cell_acc': cell_acc.item(), 'solved_acc': solved_acc.item()}

# ═══════════════════════════════════════════════════════════════════════════════
# SGC ANALYZER - Implements Π̂ (empirical conditional expectation)
# Reference: src/SGC/Renormalization/Approximate.lean (CoarseProjector)
# ═══════════════════════════════════════════════════════════════════════════════

class SGCAnalyzer:
    """
    (Π̂ f)_j = Σ_{k∈B_j} w_k f_k / Σ_{k∈B_j} w_k
    where B_j = {k : Hash(argmax(y_k)) = Hash(argmax(y_j))}
    and w_k = exp(-H(y_k)) (entropy-based weight)
    """
    def __init__(self, config: ISRConfig, device: torch.device):
        self.config = config
        self.device = device
    
    def compute_partition_hash(self, y):
        pred = y.argmax(dim=-1).cpu().numpy()
        return torch.tensor([hash(tuple(p.tolist())) for p in pred], device=self.device, dtype=torch.long)
    
    def compute_weights(self, y):
        if self.config.weights_mode == "uniform":
            return torch.ones(y.shape[0], device=self.device)
        probs = F.softmax(y, dim=-1)
        cell_entropy = -(probs * F.log_softmax(y, dim=-1)).sum(dim=-1).mean(dim=-1)
        return torch.exp(-cell_entropy)
    
    def compute_conditional_expectation(self, f, hashes, weights):
        batch_size, f_flat = f.shape[0], f.view(f.shape[0], -1)
        result = torch.zeros_like(f_flat)
        
        for h in torch.unique(hashes):
            mask = (hashes == h)
            indices = torch.where(mask)[0]
            if len(indices) == 1:
                result[indices[0]] = f_flat[indices[0]]
            else:
                w = weights[indices].unsqueeze(1)
                avg = (w * f_flat[indices]).sum(dim=0) / (w.sum() + 1e-8)
                result[indices] = avg.unsqueeze(0).expand(len(indices), -1)
        return result.view(f.shape)
    
    def compute_leakage(self, z_next, y_t):
        hashes = self.compute_partition_hash(y_t)
        weights = self.compute_weights(y_t)
        z_flat = z_next.view(z_next.shape[0], -1)
        pi_z = self.compute_conditional_expectation(z_flat, hashes, weights)
        leakage = torch.norm(z_flat - pi_z, p='fro', dim=-1)
        
        unique = torch.unique(hashes)
        singletons = sum(1 for h in unique if (hashes == h).sum() == 1)
        return {'per_sample': leakage, 'mean': leakage.mean(), 'singleton_ratio': singletons / len(unique)}
    
    def compute_non_normality_hutchinson(self, model, y_t, z_t, x_enc):
        batch_size = min(z_t.shape[0], self.config.eta_batch_subsample)
        indices = torch.randperm(z_t.shape[0], device=z_t.device)[:batch_size]
        y_t, z_t, x_enc = y_t[indices], z_t[indices], x_enc[indices]
        
        eta_sq = []
        for _ in range(self.config.eta_probes):
            v = (torch.randint(0, 2, z_t.shape, device=z_t.device).float() * 2 - 1)
            
            def fwd(z): _, zn = model.forward_step(y_t, z, x_enc); return zn
            
            z_p = z_t.clone().requires_grad_(True)
            with torch.enable_grad():
                zn = fwd(z_p)
                Jv = torch.autograd.grad(zn, z_p, grad_outputs=v, retain_graph=True)[0]
                JTv = torch.autograd.grad((zn * v).sum(), z_p, retain_graph=True)[0]
            
            z_p2 = z_t.clone().requires_grad_(True)
            with torch.enable_grad():
                zn2 = fwd(z_p2)
                JJTv = torch.autograd.grad(zn2, z_p2, grad_outputs=JTv, retain_graph=True)[0]
                JTJv = torch.autograd.grad((zn2 * Jv).sum(), z_p2)[0]
            
            eta_sq.append(((JJTv - JTJv) ** 2).sum())
        return torch.sqrt(torch.stack(eta_sq).mean() + 1e-8)
    
    def compute_effective_rank(self, z):
        z_flat = z.view(z.shape[0], -1)
        z_c = z_flat - z_flat.mean(dim=0, keepdim=True)
        s = torch.linalg.svdvals(z_c)
        s_norm = s / (s.sum() + 1e-8)
        return torch.exp(-(s_norm * torch.log(s_norm + 1e-8)).sum()).item()
    
    def compute_y_entropy(self, y):
        probs = F.softmax(y, dim=-1)
        return -(probs * F.log_softmax(y, dim=-1)).sum(dim=-1).mean().item()

# ═══════════════════════════════════════════════════════════════════════════════
# VISUALIZER
# ═══════════════════════════════════════════════════════════════════════════════

class Visualizer:
    def __init__(self, config: ISRConfig):
        self.config = config
        self.log_dir = Path(config.log_dir)
        self.log_dir.mkdir(parents=True, exist_ok=True)
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        self.writer = SummaryWriter(str(self.log_dir / f"run_{ts}"))
        self.plots_dir = self.log_dir / "plots"
        self.plots_dir.mkdir(exist_ok=True)
        self.history = {'loss': [], 'solved_acc': [], 'leakage': [], 'eta': [], 'rank': []}
        self.trajectories = []
    
    def log_scalars(self, step, metrics):
        for k, v in metrics.items():
            self.writer.add_scalar(k, v, step)
    
    def log_histogram(self, step, name, values):
        self.writer.add_histogram(name, values.cpu().numpy(), step)
    
    def save_snapshot(self, epoch, leakage_traj, eta_traj, solved_mask):
        if not MATPLOTLIB_AVAILABLE: return
        fig, axes = plt.subplots(1, 2, figsize=(12, 4))
        T = leakage_traj.shape[0]
        for i in range(min(leakage_traj.shape[1], 20)):
            axes[0].plot(range(T), leakage_traj[:, i], 
                        color='green' if solved_mask[i] else 'red', alpha=0.3, lw=0.5)
        axes[0].set_xlabel('Step t'); axes[0].set_ylabel('Leakage ε_t')
        axes[0].set_title(f'Leakage (Epoch {epoch})'); axes[0].set_yscale('log')
        axes[1].plot(range(len(eta_traj)), eta_traj, 'b-', lw=2)
        axes[1].set_xlabel('Step t'); axes[1].set_ylabel('η_t')
        axes[1].set_title('Non-Normality')
        plt.tight_layout()
        plt.savefig(self.plots_dir / f'snapshot_e{epoch:04d}.png', dpi=150)
        plt.close()
    
    def generate_posthoc_plots(self):
        if not MATPLOTLIB_AVAILABLE or not self.trajectories: return
        fig, axes = plt.subplots(2, 2, figsize=(12, 10))
        solved = [d['solved'] for d in self.trajectories]
        leak = [np.mean(d['leakage'][-5:]) for d in self.trajectories]
        axes[0,0].scatter([l for l, s in zip(leak, solved) if s], [1]*sum(solved), c='g', alpha=0.5)
        axes[0,0].scatter([l for l, s in zip(leak, solved) if not s], [0]*(len(solved)-sum(solved)), c='r', alpha=0.5)
        axes[0,0].set_xlabel('Final Leakage'); axes[0,0].set_ylabel('Solved'); axes[0,0].set_title('H1: Closure')
        for d in self.trajectories[:50]:
            c = 'g' if d['solved'] else 'r'
            axes[0,1].plot(d['leakage'], c=c, alpha=0.3, lw=0.5)
            axes[1,0].plot(d['eta'], c=c, alpha=0.3, lw=0.5)
        axes[0,1].set_yscale('log'); axes[0,1].set_title('Leakage Trajectories')
        axes[1,0].set_title('η Trajectories (H2: Hump)')
        axes[1,1].plot(self.history['loss'], 'b-', label='Loss')
        ax2 = axes[1,1].twinx()
        ax2.plot(self.history['solved_acc'], 'g-', label='Solved')
        axes[1,1].set_title('Training Progress')
        plt.tight_layout()
        plt.savefig(self.plots_dir / 'posthoc.png', dpi=200)
        plt.close()
    
    def save_summary(self, config, metrics):
        with open(self.log_dir / 'summary.json', 'w') as f:
            json.dump({'config': vars(config), 'metrics': metrics, 'ts': datetime.now().isoformat()}, f, indent=2)
    
    def close(self): self.writer.close()

# ═══════════════════════════════════════════════════════════════════════════════
# TRAINING
# ═══════════════════════════════════════════════════════════════════════════════

def train_epoch(model, loader, opt, analyzer, viz, epoch, step, cfg, device):
    model.train()
    pbar = tqdm(loader, desc=f"Epoch {epoch}")
    for puzzles, solutions in pbar:
        puzzles, solutions = puzzles.to(device), solutions.to(device)
        result = model(puzzles, T=cfg.T_steps, return_trajectory=True)
        loss = model.compute_loss(result['y_final'], solutions, puzzles)
        opt.zero_grad(); loss.backward()
        torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
        opt.step()
        
        acc = model.compute_accuracy(result['y_final'], solutions, puzzles)
        
        if step % cfg.log_interval == 0:
            with torch.no_grad():
                y_traj, z_traj = result['y_traj'], result['z_traj']
                leaks = [analyzer.compute_leakage(z_traj[t+1], y_traj[t])['mean'].item() for t in range(cfg.T_steps)]
                avg_leak = np.mean(leaks)
                x_enc = model.encode_puzzle(puzzles)
                eta = analyzer.compute_non_normality_hutchinson(model, y_traj[cfg.T_steps//2], z_traj[cfg.T_steps//2], x_enc).item()
                rank = analyzer.compute_effective_rank(z_traj[-1])
            
            pbar.set_postfix(Loss=f'{loss.item():.4f}', Acc=f'{acc["solved_acc"]*100:.1f}%', 
                            Leak=f'{avg_leak:.4f}', η=f'{eta:.2f}', Rank=f'{rank:.1f}')
            viz.log_scalars(step, {'Loss/train': loss.item(), 'Acc/solved': acc['solved_acc'],
                                   'SGC/Leakage': avg_leak, 'SGC/Eta': eta, 'SGC/Rank': rank})
            viz.history['loss'].append(loss.item())
            viz.history['solved_acc'].append(acc['solved_acc'])
        step += 1
    return step

def validate(model, loader, analyzer, viz, epoch, cfg, device):
    model.eval()
    puzzles, solutions = next(iter(loader))
    puzzles, solutions = puzzles.to(device), solutions.to(device)
    with torch.no_grad():
        result = model(puzzles, T=cfg.T_steps, return_trajectory=True)
        y_traj, z_traj = result['y_traj'], result['z_traj']
        leakage_traj = np.array([[analyzer.compute_leakage(z_traj[t+1], y_traj[t])['per_sample'][i].item() 
                                  for i in range(puzzles.shape[0])] for t in range(cfg.T_steps)]).T
        x_enc = model.encode_puzzle(puzzles)
        eta_traj = [analyzer.compute_non_normality_hutchinson(model, y_traj[t], z_traj[t], x_enc).item() 
                    for t in range(0, cfg.T_steps, 3)]
        eta_full = np.interp(np.arange(cfg.T_steps), np.arange(0, cfg.T_steps, 3), eta_traj)
        pred = result['y_final'].argmax(dim=-1) + 1
        pred = torch.where(puzzles > 0, puzzles, pred)
        solved = (pred == solutions).all(dim=-1).cpu().numpy()
        viz.save_snapshot(epoch, leakage_traj.T, eta_full, solved)
        for i in range(min(10, puzzles.shape[0])):
            viz.trajectories.append({'solved': bool(solved[i]), 'leakage': leakage_traj[i].tolist(),
                                     'eta': eta_full.tolist()})

def main():
    parser = argparse.ArgumentParser(description='SGC-Grounded ISR Sudoku')
    parser.add_argument('--data_path', type=str, default=None)
    parser.add_argument('--generate', action='store_true')
    parser.add_argument('--num_puzzles', type=int, default=10000)
    parser.add_argument('--seed', type=int, default=42)
    parser.add_argument('--hidden_dim', type=int, default=128)
    parser.add_argument('--num_layers', type=int, default=2)
    parser.add_argument('--T_steps', type=int, default=30)
    parser.add_argument('--batch_size', type=int, default=64)
    parser.add_argument('--lr', type=float, default=1e-3)
    parser.add_argument('--epochs', type=int, default=100)
    parser.add_argument('--log_dir', type=str, default='logs/isr')
    parser.add_argument('--log_interval', type=int, default=100)
    parser.add_argument('--eta_mode', type=str, default='hutchinson', choices=['full', 'hutchinson'])
    parser.add_argument('--eta_probes', type=int, default=4)
    parser.add_argument('--eta_batch_subsample', type=int, default=8)
    parser.add_argument('--weights', type=str, default='entropy', choices=['entropy', 'uniform'])
    args = parser.parse_args()
    
    cfg = ISRConfig(hidden_dim=args.hidden_dim, num_layers=args.num_layers, T_steps=args.T_steps,
                    batch_size=args.batch_size, learning_rate=args.lr, epochs=args.epochs,
                    data_path=args.data_path, generate=args.generate, num_puzzles=args.num_puzzles,
                    seed=args.seed, log_dir=args.log_dir, log_interval=args.log_interval,
                    eta_mode=args.eta_mode, eta_probes=args.eta_probes, 
                    eta_batch_subsample=args.eta_batch_subsample, weights_mode=args.weights)
    
    device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
    print(f"[ISR] Device: {device}")
    torch.manual_seed(cfg.seed); np.random.seed(cfg.seed)
    
    print("[ISR] Loading data...")
    if cfg.generate or cfg.data_path is None:
        puzzles, solutions = SudokuDataset.generate_puzzles(cfg.num_puzzles, cfg.seed)
    else:
        with open(cfg.data_path) as f:
            lines = [l.strip().split(',') for l in f if ',' in l]
        puzzles = np.array([[int(c.replace('.','0')) for c in l[0]] for l in lines if len(l[0])==81])
        solutions = np.array([[int(c) for c in l[1]] for l in lines if len(l[1])==81])
    
    n = int(0.9 * len(puzzles))
    train_loader = DataLoader(SudokuDataset(puzzles[:n], solutions[:n]), batch_size=cfg.batch_size, shuffle=True)
    val_loader = DataLoader(SudokuDataset(puzzles[n:], solutions[n:]), batch_size=cfg.batch_size)
    print(f"[ISR] Train: {n}, Val: {len(puzzles)-n}")
    
    model = ISRSolver(cfg.hidden_dim, cfg.num_layers).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=cfg.learning_rate)
    sched = torch.optim.lr_scheduler.CosineAnnealingLR(opt, T_max=cfg.epochs)
    analyzer = SGCAnalyzer(cfg, device)
    viz = Visualizer(cfg)
    
    print("[ISR] Training...")
    step = 0
    for epoch in range(1, cfg.epochs + 1):
        step = train_epoch(model, train_loader, opt, analyzer, viz, epoch, step, cfg, device)
        sched.step()
        if epoch % cfg.snapshot_interval == 0:
            validate(model, val_loader, analyzer, viz, epoch, cfg, device)
    
    viz.generate_posthoc_plots()
    viz.save_summary(cfg, {'final_loss': viz.history['loss'][-1] if viz.history['loss'] else 0,
                           'final_acc': viz.history['solved_acc'][-1] if viz.history['solved_acc'] else 0})
    viz.close()
    print(f"[ISR] Done. Logs: {cfg.log_dir}")

if __name__ == "__main__":
    main()
