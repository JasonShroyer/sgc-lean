"""
Adaptive Polarity Sheaf Network v5: Iterative Collapse (Wavefunction Collapse)

THEORY (from SGC.Renormalization.Approximate):
- "Solve all at once" = NP-hard spin glass problem
- "Iterative Collapse" = Renormalization (integrate out degrees of freedom)

THE PHYSICS:
- Each collapse: State space 9^N → 9^(N-1)
- Symmetry breaking: First collapse breaks the hardest symmetry
- Avalanche effect: One collapse triggers chain of obvious moves

THE ALGORITHM (Wavefunction Collapse):
1. Run diffusion to relax the field (soft probabilities)
2. Find cell with LOWEST ENTROPY (highest confidence)
3. COLLAPSE it (write in pen - becomes hard clue)
4. Propagate constraints through diffusion
5. Repeat until solved or stuck

This is how humans solve Sudoku - and it's the only way SGC can theoretically scale.
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import DataLoader, TensorDataset
from torch.utils.tensorboard import SummaryWriter
from dataclasses import dataclass
from typing import List, Tuple, Dict, Optional
import numpy as np
from datetime import datetime
import os


@dataclass
class IterativeCollapseConfig:
    """Configuration for Iterative Collapse SGC."""
    
    stalk_dim: int = 64
    num_cells: int = 81
    num_digits: int = 9
    
    # Diffusion parameters
    diffusion_steps: int = 8  # Steps per collapse iteration
    diffusion_dt: float = 0.1
    
    # Collapse parameters
    collapse_threshold: float = 0.5  # Entropy threshold for "confident enough"
    max_collapses: int = 81  # Maximum collapses per puzzle
    min_confidence: float = 0.8  # Min probability to collapse
    
    # Polarity (learnable)
    polarity_init: float = 0.0  # Start neutral
    
    # Training
    epochs: int = 300
    batch_size: int = 32
    lr: float = 1e-3
    polarity_lr: float = 0.05
    restriction_lr: float = 1e-3
    weight_decay: float = 0.01
    
    log_interval: int = 10
    log_dir: str = "logs/adaptive_polarity_v5"


def build_sudoku_graph() -> Tuple[List[Tuple[int, int]], Dict[str, List[int]]]:
    """Build Sudoku constraint graph."""
    edges = []
    edge_types = {'row': [], 'col': [], 'box': []}
    
    def cell_idx(r, c):
        return r * 9 + c
    
    edge_idx = 0
    
    for r in range(9):
        for c1 in range(9):
            for c2 in range(c1 + 1, 9):
                edges.append((cell_idx(r, c1), cell_idx(r, c2)))
                edge_types['row'].append(edge_idx)
                edge_idx += 1
    
    for c in range(9):
        for r1 in range(9):
            for r2 in range(r1 + 1, 9):
                edges.append((cell_idx(r1, c), cell_idx(r2, c)))
                edge_types['col'].append(edge_idx)
                edge_idx += 1
    
    for box_r in range(3):
        for box_c in range(3):
            cells = []
            for dr in range(3):
                for dc in range(3):
                    cells.append(cell_idx(box_r * 3 + dr, box_c * 3 + dc))
            for i in range(len(cells)):
                for j in range(i + 1, len(cells)):
                    edges.append((cells[i], cells[j]))
                    edge_types['box'].append(edge_idx)
                    edge_idx += 1
    
    return edges, edge_types


class SheafDiffusionV5(nn.Module):
    """Sheaf diffusion with reactive repulsion for constraint propagation."""
    
    def __init__(self, edges: List[Tuple[int, int]], edge_types: Dict[str, List[int]],
                 stalk_dim: int, polarity_init: float):
        super().__init__()
        
        self.num_edges = len(edges)
        self.stalk_dim = stalk_dim
        
        src_idx = torch.tensor([e[0] for e in edges], dtype=torch.long)
        dst_idx = torch.tensor([e[1] for e in edges], dtype=torch.long)
        self.register_buffer('src_idx', src_idx)
        self.register_buffer('dst_idx', dst_idx)
        
        type_idx = torch.zeros(len(edges), dtype=torch.long)
        for t, (name, indices) in enumerate(edge_types.items()):
            for idx in indices:
                type_idx[idx] = t
        self.register_buffer('type_idx', type_idx)
        
        self.restriction_weights = nn.ParameterList([
            nn.Parameter(torch.eye(stalk_dim) + 0.1 * torch.randn(stalk_dim, stalk_dim))
            for _ in range(3)
        ])
        
        self.polarity_logit = nn.Parameter(torch.ones(3) * polarity_init)
    
    def get_mixture_weight(self) -> torch.Tensor:
        return torch.sigmoid(self.polarity_logit)
    
    def compute_energies(self, logits: torch.Tensor) -> Tuple[torch.Tensor, torch.Tensor]:
        """Compute constraint energies."""
        probs = F.softmax(logits, dim=-1)
        
        src_probs = probs[:, self.src_idx, :]
        dst_probs = probs[:, self.dst_idx, :]
        
        # Repulsive energy: overlap (should be 0 for valid solution)
        overlap = (src_probs * dst_probs).sum(dim=-1)
        
        g = self.get_mixture_weight()
        g_per_edge = g[self.type_idx]
        
        # Energy per edge type
        per_type_energy = torch.zeros(3, device=logits.device)
        overlap_mean = overlap.mean(dim=0)
        
        for t in range(3):
            mask = (self.type_idx == t)
            if mask.any():
                per_type_energy[t] = overlap_mean[mask].mean()
        
        return per_type_energy, g
    
    def apply_restriction(self, stalks: torch.Tensor) -> torch.Tensor:
        src_stalks = stalks[:, self.src_idx, :]
        
        restricted = torch.zeros_like(src_stalks)
        for t in range(3):
            mask = (self.type_idx == t)
            if mask.any():
                W = self.restriction_weights[t]
                restricted[:, mask, :] = torch.einsum('bed,df->bef', 
                                                       src_stalks[:, mask, :], W)
        
        return restricted
    
    def diffuse(self, stalks: torch.Tensor, logits: torch.Tensor,
                dt: float, clue_mask: torch.Tensor) -> torch.Tensor:
        """
        Reactive repulsion diffusion.
        Only push when there's actual overlap (collision).
        """
        batch_size, num_cells, stalk_dim = stalks.shape
        
        probs = F.softmax(logits, dim=-1)
        
        src_probs = probs[:, self.src_idx, :]
        dst_probs = probs[:, self.dst_idx, :]
        dst_stalks = stalks[:, self.dst_idx, :]
        
        g = self.get_mixture_weight()
        g_per_edge = g[self.type_idx].view(1, -1, 1)
        
        restricted_src = self.apply_restriction(stalks)
        
        restricted_dst_for_src = torch.zeros_like(dst_stalks)
        for t in range(3):
            mask = (self.type_idx == t)
            if mask.any():
                W = self.restriction_weights[t]
                restricted_dst_for_src[:, mask, :] = torch.einsum('bed,df->bef',
                                                                   dst_stalks[:, mask, :], W)
        
        # Attractive flow
        attr_flow_to_dst = restricted_src - dst_stalks
        attr_flow_to_src = restricted_dst_for_src - stalks[:, self.src_idx, :]
        
        # REACTIVE Repulsive flow - scaled by OVERLAP
        overlap = (src_probs * dst_probs).sum(dim=-1, keepdim=True)
        repl_flow_to_dst = -overlap * (restricted_src - dst_stalks)
        repl_flow_to_src = -overlap * (restricted_dst_for_src - stalks[:, self.src_idx, :])
        
        # Mix flows
        flow_to_dst = g_per_edge * attr_flow_to_dst + (1 - g_per_edge) * repl_flow_to_dst
        flow_to_src = g_per_edge * attr_flow_to_src + (1 - g_per_edge) * repl_flow_to_src
        
        # Aggregate
        drift = torch.zeros_like(stalks)
        drift.scatter_add_(1, self.dst_idx.view(1, -1, 1).expand(batch_size, -1, stalk_dim),
                          dt * flow_to_dst)
        drift.scatter_add_(1, self.src_idx.view(1, -1, 1).expand(batch_size, -1, stalk_dim),
                          dt * flow_to_src)
        
        # Update
        new_stalks = stalks + drift
        
        # Clue clamping - CRITICAL for collapse propagation
        clue_mask_expanded = clue_mask.unsqueeze(-1)
        new_stalks = torch.where(clue_mask_expanded, stalks, new_stalks)
        
        return new_stalks


class IterativeCollapseAgent(nn.Module):
    """
    SGC Entity with Wavefunction Collapse.
    
    The key insight: Don't solve all at once. Navigate the solution tree
    by collapsing one cell at a time, like writing in pen.
    """
    
    def __init__(self, config: IterativeCollapseConfig,
                 edges: List[Tuple[int, int]], edge_types: Dict[str, List[int]]):
        super().__init__()
        self.config = config
        
        self.embed = nn.Embedding(10, config.stalk_dim)
        
        self.cell_mlp = nn.Sequential(
            nn.Linear(config.stalk_dim, config.stalk_dim * 2),
            nn.ReLU(),
            nn.Linear(config.stalk_dim * 2, config.stalk_dim),
        )
        
        self.diffusion = SheafDiffusionV5(
            edges, edge_types, config.stalk_dim, config.polarity_init
        )
        
        self.output_head = nn.Linear(config.stalk_dim, config.num_digits)
    
    def compute_entropy(self, logits: torch.Tensor) -> torch.Tensor:
        """Compute entropy per cell."""
        probs = F.softmax(logits, dim=-1)
        log_probs = F.log_softmax(logits, dim=-1)
        entropy = -(probs * log_probs).sum(dim=-1)  # (batch, 81)
        return entropy
    
    def forward_single_pass(self, puzzles: torch.Tensor, clue_mask: torch.Tensor) -> torch.Tensor:
        """Single forward pass with diffusion."""
        stalks = self.embed(puzzles)
        stalks = stalks + self.cell_mlp(stalks)
        
        for step in range(self.config.diffusion_steps):
            logits = self.output_head(stalks)
            stalks = self.diffusion.diffuse(stalks, logits, self.config.diffusion_dt, clue_mask)
            stalks = stalks + 0.1 * self.cell_mlp(stalks)
        
        logits = self.output_head(stalks)
        return logits
    
    def forward(self, puzzles: torch.Tensor, solutions: Optional[torch.Tensor] = None,
                collapse_mode: bool = False):
        """
        Forward with optional iterative collapse.
        
        collapse_mode=False: Standard forward (for training)
        collapse_mode=True: Iterative collapse (for inference)
        """
        batch_size = puzzles.shape[0]
        device = puzzles.device
        
        # Working copy of puzzles (will be modified during collapse)
        working_puzzles = puzzles.clone()
        clue_mask = (working_puzzles > 0)
        
        if not collapse_mode:
            # Standard forward for training
            logits = self.forward_single_pass(working_puzzles, clue_mask)
            
            per_type_energy, g = self.diffusion.compute_energies(logits)
            total_energy = per_type_energy.sum()
            
            return logits, total_energy, per_type_energy, g
        
        else:
            # ITERATIVE COLLAPSE for inference
            collapse_count = 0
            collapse_history = []
            
            for iteration in range(self.config.max_collapses):
                # 1. Run diffusion to relax the field
                logits = self.forward_single_pass(working_puzzles, clue_mask)
                probs = F.softmax(logits, dim=-1)
                
                # 2. Compute entropy per cell
                entropy = self.compute_entropy(logits)  # (batch, 81)
                
                # 3. Find candidates: low entropy AND not yet fixed
                unfixed_mask = ~clue_mask  # (batch, 81)
                
                if not unfixed_mask.any():
                    break  # All cells fixed
                
                # Mask fixed cells with high entropy so they're not selected
                entropy_masked = entropy.clone()
                entropy_masked[clue_mask] = float('inf')
                
                # 4. Find the LOWEST entropy unfixed cell per batch
                min_entropy, min_idx = entropy_masked.min(dim=1)  # (batch,)
                max_prob = probs.gather(1, min_idx.unsqueeze(1).unsqueeze(2).expand(-1, -1, 9))
                max_prob = max_prob.squeeze(1).max(dim=-1)[0]  # (batch,)
                
                # 5. Check if confident enough to collapse
                should_collapse = (min_entropy < self.config.collapse_threshold) & \
                                 (max_prob > self.config.min_confidence)
                
                if not should_collapse.any():
                    break  # No cells confident enough
                
                # 6. COLLAPSE: Write in pen
                best_digit = probs.argmax(dim=-1)  # (batch, 81)
                
                for b in range(batch_size):
                    if should_collapse[b]:
                        cell = min_idx[b].item()
                        digit = best_digit[b, cell].item()
                        
                        # Write in pen (1-indexed for puzzle format)
                        working_puzzles[b, cell] = digit + 1
                        clue_mask[b, cell] = True
                        
                        collapse_count += 1
                        collapse_history.append((b, cell, digit))
                
                # Early termination if batch is done
                if clue_mask.all():
                    break
            
            # Final logits after all collapses
            final_logits = self.forward_single_pass(working_puzzles, clue_mask)
            per_type_energy, g = self.diffusion.compute_energies(final_logits)
            
            return final_logits, working_puzzles, collapse_count, collapse_history, g


def evaluate_with_collapse(model, test_loader, device):
    """Evaluate using iterative collapse."""
    model.eval()
    
    total_correct = 0
    total_cells = 0
    total_collapses = 0
    total_puzzles = 0
    
    with torch.no_grad():
        for batch in test_loader:
            puzzles, solutions = [x.to(device) for x in batch]
            
            # Use collapse mode
            final_logits, final_puzzles, collapse_count, history, g = model(
                puzzles, collapse_mode=True
            )
            
            # Convert final_puzzles back to 0-indexed predictions
            preds = final_puzzles - 1  # Now 0-8
            preds = torch.clamp(preds, 0, 8)  # Handle any edge cases
            
            # For cells that weren't collapsed, use logits
            not_collapsed = (puzzles == 0) & (final_puzzles == 0)
            if not_collapsed.any():
                logit_preds = final_logits.argmax(dim=-1)
                preds = torch.where(not_collapsed, logit_preds, preds)
            
            # Count correct
            unknown = (puzzles == 0)
            correct = ((preds == solutions) & unknown).sum().item()
            total_correct += correct
            total_cells += unknown.sum().item()
            total_collapses += collapse_count
            total_puzzles += puzzles.shape[0]
    
    accuracy = total_correct / max(total_cells, 1)
    avg_collapses = total_collapses / max(total_puzzles, 1)
    
    return accuracy, avg_collapses


def run_test():
    """Test v5 with Iterative Collapse."""
    from baby_agi_sudoku import generate_puzzles_with_clues
    
    device = "cuda" if torch.cuda.is_available() else "cpu"
    config = IterativeCollapseConfig()
    edges, edge_types = build_sudoku_graph()
    
    model = IterativeCollapseAgent(config, edges, edge_types).to(device)
    
    # Generate data
    train_puzzles, train_solutions = generate_puzzles_with_clues(1000, 35, seed=42)
    test_puzzles, test_solutions = generate_puzzles_with_clues(200, 35, seed=1042)
    
    train_dataset = TensorDataset(
        torch.tensor(train_puzzles, dtype=torch.long),
        torch.tensor(train_solutions - 1, dtype=torch.long),
    )
    test_dataset = TensorDataset(
        torch.tensor(test_puzzles, dtype=torch.long),
        torch.tensor(test_solutions - 1, dtype=torch.long),
    )
    
    train_loader = DataLoader(train_dataset, batch_size=config.batch_size, shuffle=True, drop_last=True)
    test_loader = DataLoader(test_dataset, batch_size=config.batch_size)
    
    # Optimizer
    polarity_params = [model.diffusion.polarity_logit]
    restriction_params = list(model.diffusion.restriction_weights.parameters())
    other_params = [p for p in model.parameters() 
                   if id(p) not in {id(model.diffusion.polarity_logit)} 
                   and id(p) not in {id(w) for w in model.diffusion.restriction_weights}]
    
    optimizer = torch.optim.AdamW([
        {'params': other_params, 'lr': config.lr, 'weight_decay': config.weight_decay},
        {'params': polarity_params, 'lr': config.polarity_lr, 'weight_decay': 0.0},
        {'params': restriction_params, 'lr': config.restriction_lr, 'weight_decay': 0.001},
    ])
    
    scheduler = torch.optim.lr_scheduler.CosineAnnealingLR(optimizer, T_max=config.epochs)
    
    # Logging
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_path = f"{config.log_dir}/run_{timestamp}"
    os.makedirs(log_path, exist_ok=True)
    writer = SummaryWriter(log_path)
    
    print("=" * 130)
    print("ADAPTIVE POLARITY v5: Iterative Collapse (Wavefunction Collapse)")
    print("=" * 130)
    print(f"Device: {device}")
    print(f"Parameters: {sum(p.numel() for p in model.parameters()):,}")
    print(f"Collapse threshold: {config.collapse_threshold}")
    print(f"Min confidence: {config.min_confidence}")
    print(f"TensorBoard: {log_path}")
    print("=" * 130)
    print()
    print("Theory (from SGC.Renormalization.Approximate):")
    print("  1. Relax field (diffusion)")
    print("  2. Find lowest entropy cell")
    print("  3. COLLAPSE (write in pen)")
    print("  4. Propagate constraints")
    print("  5. Repeat -> Solution")
    print()
    
    print("-" * 130)
    print(f" {'Ep':>4} | {'Train':>6} | {'Test':>6} | {'Collapse':>8} | "
          f"{'g_row':>6} | {'g_col':>6} | {'g_box':>6} | "
          f"{'Energy':>7} | Status")
    print("-" * 130)
    
    best_acc = 0.0
    
    for epoch in range(config.epochs):
        model.train()
        train_correct = 0
        train_total = 0
        epoch_energy = 0.0
        
        for batch in train_loader:
            puzzles, solutions = [x.to(device) for x in batch]
            
            optimizer.zero_grad()
            
            # Standard forward for training (no collapse)
            logits, energy, per_type_energy, g = model(puzzles, solutions, collapse_mode=False)
            
            # Task loss
            loss_ce = F.cross_entropy(
                logits.view(-1, 9),
                solutions.view(-1),
                reduction='none'
            ).view(puzzles.shape[0], 81)
            
            unknown_mask = (puzzles == 0).float()
            loss_ce = (loss_ce * unknown_mask).sum() / unknown_mask.sum()
            
            # Total loss: task + constraint energy
            loss = loss_ce + 0.5 * energy
            
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
            optimizer.step()
            
            epoch_energy += energy.item()
            
            with torch.no_grad():
                preds = logits.argmax(dim=-1)
                unknown = (puzzles == 0)
                train_correct += ((preds == solutions) & unknown).sum().item()
                train_total += unknown.sum().item()
        
        scheduler.step()
        
        # Evaluate with collapse
        if epoch % config.log_interval == 0:
            test_acc, avg_collapses = evaluate_with_collapse(model, test_loader, device)
            train_acc = train_correct / max(train_total, 1)
            
            g = model.diffusion.get_mixture_weight().detach().cpu()
            avg_energy = epoch_energy / len(train_loader)
            
            status = ""
            if test_acc > best_acc:
                best_acc = test_acc
                status = "BEST"
            if test_acc > 0.95:
                status += " SOLVED!"
            elif test_acc > 0.85:
                status += " CRYSTALLIZING"
            elif avg_collapses > 20:
                status += " COLLAPSING"
            elif g.max() < 0.3:
                status += " REPULSION"
            
            print(f" {epoch:>4} | {train_acc*100:>5.1f}% | {test_acc*100:>5.1f}% | "
                  f"{avg_collapses:>8.1f} | "
                  f"{g[0]:>6.3f} | {g[1]:>6.3f} | {g[2]:>6.3f} | "
                  f"{avg_energy:>7.3f} | {status}")
            
            writer.add_scalar("test/acc", test_acc, epoch)
            writer.add_scalar("train/acc", train_acc, epoch)
            writer.add_scalar("collapse/avg_count", avg_collapses, epoch)
            writer.add_scalar("polarity/g_row", g[0], epoch)
            writer.add_scalar("polarity/g_col", g[1], epoch)
            writer.add_scalar("polarity/g_box", g[2], epoch)
            writer.add_scalar("energy/total", avg_energy, epoch)
    
    # Final evaluation
    final_acc, final_collapses = evaluate_with_collapse(model, test_loader, device)
    final_g = model.diffusion.get_mixture_weight().detach().cpu()
    
    print("=" * 130)
    print(f"FINAL: Acc={final_acc*100:.1f}%, Collapses={final_collapses:.1f}, "
          f"g=[{final_g[0]:.3f}, {final_g[1]:.3f}, {final_g[2]:.3f}]")
    
    if final_acc > 0.95:
        print("SUCCESS: ITERATIVE COLLAPSE ACHIEVED SOLUTION!")
    elif final_acc > 0.80:
        print("GOOD: Significant crystallization via collapse.")
    elif final_g.max() < 0.3:
        print("REPULSION discovered - collapse mechanism working.")
    else:
        print("Check collapse threshold or diffusion steps.")
    print("=" * 130)
    
    writer.close()
    return model


if __name__ == "__main__":
    model = run_test()
