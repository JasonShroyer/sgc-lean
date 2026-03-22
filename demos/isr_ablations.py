#!/usr/bin/env python3
"""
ISR Ablation Study: Disentangling Topology vs Geometry
=====================================================

Two micro-ablations to isolate what caused the 0% → 80% jump:

1. TOPOLOGY-ONLY: Same row/col/box structure but replace additive logits 
   with concat→MLP (Euclidean mixing). Tests if Fisher-correct geometry matters.

2. SCRAMBLED-TOPOLOGY: Keep additive logits but randomize the constraint graph.
   Tests if Sudoku-specific structure matters.

Run: python demos/isr_ablations.py --ablation topology_only --epochs 20
     python demos/isr_ablations.py --ablation scrambled --epochs 20
"""

import argparse
import torch
import torch.nn as nn
import torch.nn.functional as F
from typing import Dict, Tuple
import numpy as np
from pathlib import Path
from tqdm import tqdm

# Import from main experiment
from iterative_spectral_refinement import (
    ISRConfig, SudokuDataset, SGCAnalyzer, Visualizer,
    SudokuSolver, FisherAxialBlock
)


class TopologyOnlyBlock(nn.Module):
    """ABLATION: Same row/col/box topology but Euclidean (concat→MLP) mixing.
    
    This tests: Is the Fisher-correct log-linear composition essential,
    or is just having the right topology sufficient?
    """
    def __init__(self, hidden_dim: int = 64):
        super().__init__()
        self.hidden_dim = hidden_dim
        
        # Same topology as FisherAxialBlock, but different composition
        self.row_net = nn.Sequential(
            nn.Linear(hidden_dim * 9, hidden_dim),
            nn.GELU(),
        )
        self.col_net = nn.Sequential(
            nn.Linear(hidden_dim * 9, hidden_dim),
            nn.GELU(),
        )
        self.box_net = nn.Sequential(
            nn.Linear(hidden_dim * 9, hidden_dim),
            nn.GELU(),
        )
        
        # EUCLIDEAN mixing: concatenate then MLP (NOT additive)
        self.mixer = nn.Sequential(
            nn.Linear(hidden_dim * 4, hidden_dim * 2),  # 4 = original + row + col + box
            nn.GELU(),
            nn.Linear(hidden_dim * 2, hidden_dim)
        )
    
    def forward(self, z: torch.Tensor) -> torch.Tensor:
        """z: (B, 81, D) -> (B, 81, D)"""
        B, _, D = z.shape
        z_grid = z.view(B, 9, 9, D)
        
        # Same topology gathering as Fisher block
        row_context = z_grid.reshape(B, 9, 9 * D)
        row_feat = self.row_net(row_context).unsqueeze(2).expand(-1, -1, 9, -1)
        
        col_context = z_grid.permute(0, 2, 1, 3).reshape(B, 9, 9 * D)
        col_feat = self.col_net(col_context).unsqueeze(1).expand(-1, 9, -1, -1)
        
        z_boxes = z_grid.view(B, 3, 3, 3, 3, D)
        z_boxes = z_boxes.permute(0, 1, 3, 2, 4, 5).reshape(B, 9, 9 * D)
        box_feat = self.box_net(z_boxes).view(B, 3, 3, D)
        box_feat = box_feat.unsqueeze(3).unsqueeze(5).expand(-1, -1, -1, 3, -1, 3).reshape(B, 9, 9, D)
        
        # EUCLIDEAN MIXING: Concatenate all features then MLP
        # This is the "wrong" way according to Fisher-Rao theory
        combined = torch.cat([z_grid, row_feat, col_feat, box_feat], dim=-1)
        z_new = self.mixer(combined)
        
        return z_new.view(B, 81, D)


class ScrambledBlock(nn.Module):
    """ABLATION: Fisher-correct additive updates but RANDOM topology.
    
    This tests: Is Sudoku-specific structure essential,
    or would any message-passing graph work?
    """
    def __init__(self, hidden_dim: int = 64):
        super().__init__()
        self.hidden_dim = hidden_dim
        
        # Three random groupings (NOT row/col/box aligned)
        # Each cell is assigned to 3 random groups of 9
        self.register_buffer('group1', self._make_random_groups())
        self.register_buffer('group2', self._make_random_groups())
        self.register_buffer('group3', self._make_random_groups())
        
        self.net1 = nn.Sequential(nn.Linear(hidden_dim * 9, hidden_dim), nn.GELU(), nn.Linear(hidden_dim, hidden_dim))
        self.net2 = nn.Sequential(nn.Linear(hidden_dim * 9, hidden_dim), nn.GELU(), nn.Linear(hidden_dim, hidden_dim))
        self.net3 = nn.Sequential(nn.Linear(hidden_dim * 9, hidden_dim), nn.GELU(), nn.Linear(hidden_dim, hidden_dim))
        
        self.alpha = nn.Parameter(torch.tensor(0.1))
    
    def _make_random_groups(self) -> torch.Tensor:
        """Create random assignment of 81 cells into 9 groups of 9."""
        perm = torch.randperm(81)
        groups = perm.view(9, 9)  # [9 groups, 9 cells each]
        return groups
    
    def _gather_groups(self, z: torch.Tensor, groups: torch.Tensor, net: nn.Module) -> torch.Tensor:
        """Gather cells by random groups, process, scatter back."""
        B, _, D = z.shape
        updates = torch.zeros_like(z)
        
        for g in range(9):
            cell_indices = groups[g]  # [9]
            group_z = z[:, cell_indices, :]  # [B, 9, D]
            group_flat = group_z.reshape(B, 9 * D)
            group_update = net(group_flat)  # [B, D]
            # Broadcast update to all cells in group
            updates[:, cell_indices, :] = group_update.unsqueeze(1).expand(-1, 9, -1)
        
        return updates
    
    def forward(self, z: torch.Tensor) -> torch.Tensor:
        # Fisher-correct: ADDITIVE updates
        delta1 = self._gather_groups(z, self.group1, self.net1)
        delta2 = self._gather_groups(z, self.group2, self.net2)
        delta3 = self._gather_groups(z, self.group3, self.net3)
        
        # Same composition rule as Fisher block
        return z + self.alpha * (delta1 + delta2 + delta3)


class AblationSolver(nn.Module):
    """ISR Solver with configurable block type for ablations."""
    
    def __init__(self, hidden_dim: int = 32, num_blocks: int = 2, block_type: str = 'fisher'):
        super().__init__()
        self.hidden_dim = hidden_dim
        self.block_type = block_type
        
        self.clue_embed = nn.Embedding(10, hidden_dim)
        
        # Select block type
        if block_type == 'fisher':
            self.blocks = nn.ModuleList([FisherAxialBlock(hidden_dim) for _ in range(num_blocks)])
        elif block_type == 'topology_only':
            self.blocks = nn.ModuleList([TopologyOnlyBlock(hidden_dim) for _ in range(num_blocks)])
        elif block_type == 'scrambled':
            self.blocks = nn.ModuleList([ScrambledBlock(hidden_dim) for _ in range(num_blocks)])
        else:
            raise ValueError(f"Unknown block_type: {block_type}")
        
        self.to_logits = nn.Linear(hidden_dim, 9)
        self.z_init = nn.Parameter(torch.randn(hidden_dim) * 0.01)
        
        total = sum(p.numel() for p in self.parameters() if p.requires_grad)
        print(f"[AblationSolver] {block_type}, Parameters: {total:,}")
    
    def encode_puzzle(self, puzzle: torch.Tensor) -> torch.Tensor:
        return self.clue_embed(puzzle)
    
    def forward_step(self, z_t: torch.Tensor, x_enc: torch.Tensor) -> Tuple[torch.Tensor, torch.Tensor]:
        z_combined = z_t + x_enc
        for block in self.blocks:
            z_combined = block(z_combined)
        y_t = self.to_logits(z_combined)
        return y_t, z_combined
    
    def forward(self, puzzle: torch.Tensor, T: int = 30, return_trajectory: bool = False):
        batch_size, device = puzzle.shape[0], puzzle.device
        x_enc = self.encode_puzzle(puzzle)
        z_t = self.z_init.unsqueeze(0).unsqueeze(0).expand(batch_size, 81, -1).clone()
        y_t = self.to_logits(z_t + x_enc)
        
        y_traj, z_traj = [y_t], [z_t] if return_trajectory else (None, None)
        
        for _ in range(T):
            y_t, z_t = self.forward_step(z_t, x_enc)
            if return_trajectory:
                y_traj.append(y_t)
                z_traj.append(z_t)
        
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


def run_ablation(args):
    device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
    print(f"[Ablation: {args.ablation}] Device: {device}")
    
    # Generate small dataset for quick ablation
    cfg = ISRConfig()
    cfg.num_puzzles = args.num_puzzles
    cfg.batch_size = args.batch_size
    cfg.T_steps = 30
    
    print(f"[Ablation] Generating {args.num_puzzles} puzzles...")
    puzzles, solutions, _ = SudokuDataset.generate_puzzles(
        args.num_puzzles, 
        min_clues=45, max_clues=55, 
        require_unique=True
    )
    
    # Split
    split = int(0.9 * len(puzzles))
    train_ds = SudokuDataset(puzzles[:split], solutions[:split])
    val_ds = SudokuDataset(puzzles[split:], solutions[split:])
    train_loader = torch.utils.data.DataLoader(train_ds, batch_size=args.batch_size, shuffle=True)
    
    # Model
    model = AblationSolver(hidden_dim=32, num_blocks=2, block_type=args.ablation).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=1e-3)
    
    # Training
    results = {'epochs': [], 'loss': [], 'cell_acc': [], 'solved_acc': []}
    
    for epoch in range(1, args.epochs + 1):
        model.train()
        epoch_loss, epoch_cell_acc, epoch_solved_acc = [], [], []
        
        pbar = tqdm(train_loader, desc=f"[{args.ablation}] Epoch {epoch}")
        for puzzles_batch, solutions_batch in pbar:
            puzzles_batch = puzzles_batch.to(device)
            solutions_batch = solutions_batch.to(device)
            
            result = model(puzzles_batch, T=cfg.T_steps)
            loss = model.compute_loss(result['y_final'], solutions_batch, puzzles_batch)
            
            opt.zero_grad()
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
            opt.step()
            
            acc = model.compute_accuracy(result['y_final'], solutions_batch, puzzles_batch)
            epoch_loss.append(loss.item())
            epoch_cell_acc.append(acc['cell_acc'])
            epoch_solved_acc.append(acc['solved_acc'])
            
            pbar.set_postfix(Loss=f'{loss.item():.4f}', Cell=f'{acc["cell_acc"]*100:.1f}%', 
                            Solved=f'{acc["solved_acc"]*100:.1f}%')
        
        avg_loss = np.mean(epoch_loss)
        avg_cell = np.mean(epoch_cell_acc)
        avg_solved = np.mean(epoch_solved_acc)
        
        results['epochs'].append(epoch)
        results['loss'].append(avg_loss)
        results['cell_acc'].append(avg_cell)
        results['solved_acc'].append(avg_solved)
        
        print(f"[{args.ablation}] Epoch {epoch}: Loss={avg_loss:.4f}, Cell={avg_cell*100:.1f}%, Solved={avg_solved*100:.1f}%")
    
    # Save results
    import json
    output_path = Path(f"logs/ablation_{args.ablation}.json")
    output_path.parent.mkdir(exist_ok=True)
    with open(output_path, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"[Ablation] Results saved to {output_path}")
    
    return results


def main():
    parser = argparse.ArgumentParser(description='ISR Ablation Study')
    parser.add_argument('--ablation', type=str, required=True, 
                        choices=['fisher', 'topology_only', 'scrambled'],
                        help='Ablation type: fisher (baseline), topology_only, scrambled')
    parser.add_argument('--epochs', type=int, default=20, help='Number of epochs')
    parser.add_argument('--num_puzzles', type=int, default=1000, help='Number of puzzles')
    parser.add_argument('--batch_size', type=int, default=32, help='Batch size')
    args = parser.parse_args()
    
    run_ablation(args)


if __name__ == '__main__':
    main()
