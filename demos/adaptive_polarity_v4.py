"""
Adaptive Polarity Sheaf Network v4: Entropy Stabilizer

THEORY (from SGC.Bridge.Quantum):
- The "Void Trap" occurred because Hard Sphere repulsion pushed stalks into
  the orthogonal complement of the Code Subspace (valid digit states).
- We need a STABILIZER HAMILTONIAN to keep stalks on valid digits.

THE FIX:
- H = H_interaction + H_stabilizer
- H_interaction: Reactive repulsion (v2 style) - only push when overlap exists
- H_stabilizer: Entropy penalty - makes high-entropy states energetically unfavorable

Entropy as Stabilizer:
- V_stab(p) = -sum(p * log(p))  (Negative Entropy)
- Low Energy: One-hot vectors (Pure Digits)
- High Energy: Uniform distributions (The Void)

This creates "gravity" around valid digits. Repulsion pushes cells apart,
but the Stabilizer forces them to land on valid digits, not float in the void.
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
class AdaptivePolarityConfigV4:
    """Configuration for v4 with Entropy Stabilizer."""
    
    stalk_dim: int = 64
    num_cells: int = 81
    num_digits: int = 9
    diffusion_steps: int = 12  # Standard horizon
    diffusion_dt: float = 0.08
    
    # Homeostatic Control
    tau: float = 0.25
    ema_alpha: float = 0.95
    precision_floor: float = 0.01
    
    # Langevin Dynamics
    noise_scale: float = 0.3  # Moderate noise
    min_temp: float = 0.01
    
    # Polarity (learnable)
    polarity_init: float = 0.0  # Start neutral, let it learn
    
    # ENTROPY STABILIZER - The Key Addition
    entropy_weight: float = 0.1  # Weight for entropy penalty
    
    # Training
    epochs: int = 500
    batch_size: int = 32
    lr: float = 1e-3
    polarity_lr: float = 0.03
    restriction_lr: float = 1e-3
    weight_decay: float = 0.01
    
    log_interval: int = 10
    log_dir: str = "logs/adaptive_polarity_v4"


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


class VectorizedSheafDiffusionV4(nn.Module):
    """Sheaf diffusion with REACTIVE repulsion (v2 style) + Langevin noise."""
    
    def __init__(self, edges: List[Tuple[int, int]], edge_types: Dict[str, List[int]],
                 stalk_dim: int, polarity_init: float, noise_scale: float):
        super().__init__()
        
        self.num_edges = len(edges)
        self.stalk_dim = stalk_dim
        self.noise_scale = noise_scale
        
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
    
    def compute_energies(self, logits: torch.Tensor
                        ) -> Tuple[torch.Tensor, torch.Tensor, torch.Tensor, torch.Tensor]:
        """Compute constraint energies."""
        probs = F.softmax(logits, dim=-1)
        
        src_probs = probs[:, self.src_idx, :]
        dst_probs = probs[:, self.dst_idx, :]
        
        attractive = ((src_probs - dst_probs) ** 2).sum(dim=-1)
        repulsive = (src_probs * dst_probs).sum(dim=-1)
        
        g = self.get_mixture_weight()
        g_per_edge = g[self.type_idx]
        
        combined = g_per_edge * attractive + (1 - g_per_edge) * repulsive
        
        combined_mean = combined.mean(dim=0)
        attractive_mean = attractive.mean(dim=0)
        repulsive_mean = repulsive.mean(dim=0)
        
        per_type_energy = torch.zeros(3, device=logits.device)
        per_type_attractive = torch.zeros(3, device=logits.device)
        per_type_repulsive = torch.zeros(3, device=logits.device)
        
        for t in range(3):
            mask = (self.type_idx == t)
            if mask.any():
                per_type_energy[t] = combined_mean[mask].mean()
                per_type_attractive[t] = attractive_mean[mask].mean()
                per_type_repulsive[t] = repulsive_mean[mask].mean()
        
        return per_type_energy, per_type_attractive, per_type_repulsive, g
    
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
                precision: torch.Tensor, dt: float,
                clue_mask: torch.Tensor, temperature: torch.Tensor) -> torch.Tensor:
        """
        Langevin diffusion with REACTIVE repulsion (v2 style).
        
        Key difference from v3: Repulsion is scaled by OVERLAP.
        This prevents pushing stalks into the void.
        """
        batch_size, num_cells, stalk_dim = stalks.shape
        
        probs = F.softmax(logits, dim=-1)
        
        src_probs = probs[:, self.src_idx, :]
        dst_probs = probs[:, self.dst_idx, :]
        dst_stalks = stalks[:, self.dst_idx, :]
        
        g = self.get_mixture_weight()
        g_per_edge = g[self.type_idx].view(1, -1, 1)
        prec_per_edge = precision[self.type_idx].view(1, -1, 1)
        
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
        
        # REACTIVE Repulsive flow (v2 style) - scaled by OVERLAP
        # This is the key: only push when there's actual collision
        overlap = (src_probs * dst_probs).sum(dim=-1, keepdim=True)
        repl_flow_to_dst = -overlap * (restricted_src - dst_stalks)
        repl_flow_to_src = -overlap * (restricted_dst_for_src - stalks[:, self.src_idx, :])
        
        # Mix flows
        flow_to_dst = prec_per_edge * (g_per_edge * attr_flow_to_dst + (1 - g_per_edge) * repl_flow_to_dst)
        flow_to_src = prec_per_edge * (g_per_edge * attr_flow_to_src + (1 - g_per_edge) * repl_flow_to_src)
        
        # DRIFT
        drift = torch.zeros_like(stalks)
        drift.scatter_add_(1, self.dst_idx.view(1, -1, 1).expand(batch_size, -1, stalk_dim),
                          dt * flow_to_dst)
        drift.scatter_add_(1, self.src_idx.view(1, -1, 1).expand(batch_size, -1, stalk_dim),
                          dt * flow_to_src)
        
        # THERMAL NOISE (Langevin)
        temp = temperature.detach()
        if temp.numel() == 1:
            temp = temp.view(1, 1, 1).expand(batch_size, 1, 1)
        else:
            temp = temp.view(batch_size, 1, 1)
        
        noise_std = self.noise_scale * torch.sqrt(2 * temp * dt + 1e-8)
        thermal_noise = noise_std * torch.randn_like(stalks)
        
        # Update
        new_stalks = stalks + drift + thermal_noise
        
        # Clue clamping
        clue_mask_expanded = clue_mask.unsqueeze(-1)
        new_stalks = torch.where(clue_mask_expanded, stalks, new_stalks)
        
        return new_stalks


class HomeostaticControllerV4(nn.Module):
    """Homeostatic controller for temperature regulation."""
    
    def __init__(self, num_edge_types: int, tau: float, ema_alpha: float,
                 precision_floor: float = 0.01, min_temp: float = 0.01):
        super().__init__()
        self.tau = tau
        self.ema_alpha = ema_alpha
        self.precision_floor = precision_floor
        self.min_temp = min_temp
        
        self.log_precision_prior = nn.Parameter(torch.ones(num_edge_types) * 0.3)
        
        self.register_buffer('constraint_ema', torch.ones(num_edge_types) * 0.5)
        self.register_buffer('task_pain_ema', torch.ones(1) * 1.0)
        self.register_buffer('step_count', torch.zeros(1))
    
    def update_ema(self, constraint_energy: torch.Tensor, task_pain: torch.Tensor):
        with torch.no_grad():
            self.constraint_ema = self.ema_alpha * self.constraint_ema + (1 - self.ema_alpha) * constraint_energy
            self.task_pain_ema = self.ema_alpha * self.task_pain_ema + (1 - self.ema_alpha) * task_pain
            self.step_count += 1
    
    def get_effective_precision(self) -> Tuple[torch.Tensor, torch.Tensor]:
        log_prec = torch.clamp(self.log_precision_prior, -2.0, 2.0)
        prior = torch.exp(log_prec)
        
        arousal = self.get_arousal()
        effective = prior * (1 - arousal.mean())
        effective = torch.clamp(effective, min=self.precision_floor)
        
        return prior, effective
    
    def get_arousal(self) -> torch.Tensor:
        pain_weight = max(0.1, 1.0 - self.step_count.item() / 2000)
        combined = self.constraint_ema.mean() + pain_weight * self.task_pain_ema
        return torch.sigmoid((combined - self.tau) / max(self.tau, 0.1))
    
    def get_temperature(self) -> torch.Tensor:
        arousal = self.get_arousal()
        return torch.clamp(arousal, min=self.min_temp)
    
    def complexity_loss(self) -> torch.Tensor:
        return 0.5 * (self.log_precision_prior ** 2).sum()


class AdaptivePolarityAgentV4(nn.Module):
    """
    v4: Reactive Repulsion + Entropy Stabilizer
    
    The key insight from SGC.Bridge.Quantum:
    - H = H_interaction + H_stabilizer
    - H_interaction: Sheaf Laplacian (reactive repulsion)
    - H_stabilizer: Entropy penalty (keeps stalks on valid digits)
    """
    
    def __init__(self, config: AdaptivePolarityConfigV4, 
                 edges: List[Tuple[int, int]], edge_types: Dict[str, List[int]]):
        super().__init__()
        self.config = config
        
        self.embed = nn.Embedding(10, config.stalk_dim)
        
        self.cell_mlp = nn.Sequential(
            nn.Linear(config.stalk_dim, config.stalk_dim * 2),
            nn.ReLU(),
            nn.Linear(config.stalk_dim * 2, config.stalk_dim),
        )
        
        self.diffusion = VectorizedSheafDiffusionV4(
            edges, edge_types, config.stalk_dim, 
            config.polarity_init, config.noise_scale
        )
        
        self.controller = HomeostaticControllerV4(
            num_edge_types=3,
            tau=config.tau,
            ema_alpha=config.ema_alpha,
            precision_floor=config.precision_floor,
            min_temp=config.min_temp
        )
        
        self.output_head = nn.Linear(config.stalk_dim, config.num_digits)
    
    def compute_entropy(self, logits: torch.Tensor, mask: torch.Tensor) -> torch.Tensor:
        """
        Compute entropy of predictions.
        
        E_entropy = -sum(p * log(p))
        
        High entropy = uniform distribution = "Void" = BAD
        Low entropy = sharp prediction = valid digit = GOOD
        """
        probs = F.softmax(logits, dim=-1)
        log_probs = F.log_softmax(logits, dim=-1)
        
        # Entropy per cell: -sum(p * log(p))
        entropy_per_cell = -(probs * log_probs).sum(dim=-1)  # (batch, 81)
        
        # Average entropy over unknown cells only
        if mask.sum() > 0:
            entropy = (entropy_per_cell * mask).sum() / mask.sum()
        else:
            entropy = entropy_per_cell.mean()
        
        return entropy
    
    def forward(self, puzzles: torch.Tensor, solutions: Optional[torch.Tensor] = None):
        batch_size = puzzles.shape[0]
        device = puzzles.device
        
        clue_mask = (puzzles > 0)
        unknown_mask = (puzzles == 0).float()
        
        stalks = self.embed(puzzles)
        stalks = stalks + self.cell_mlp(stalks)
        
        prior_prec, effective_prec = self.controller.get_effective_precision()
        temperature = self.controller.get_temperature()
        
        # Langevin diffusion with reactive repulsion
        for step in range(self.config.diffusion_steps):
            logits = self.output_head(stalks)
            stalks = self.diffusion.diffuse(stalks, logits, effective_prec, 
                                            self.config.diffusion_dt, clue_mask, temperature)
            stalks = stalks + 0.1 * self.cell_mlp(stalks)
        
        logits = self.output_head(stalks)
        
        per_type_energy, attr_energy, repl_energy, mixture_weight = self.diffusion.compute_energies(logits)
        
        # ENTROPY STABILIZER - The Key Addition
        entropy = self.compute_entropy(logits, unknown_mask)
        
        task_pain = torch.tensor(0.0, device=device)
        if solutions is not None:
            if unknown_mask.sum() > 0:
                task_loss = F.cross_entropy(
                    logits.view(-1, 9),
                    solutions.view(-1),
                    reduction='none'
                ).view(batch_size, 81)
                task_pain = (task_loss * unknown_mask).sum() / unknown_mask.sum()
        
        self.controller.update_ema(per_type_energy.detach(), task_pain.detach())
        
        total_energy = per_type_energy.sum()
        complexity = 0.1 * self.controller.complexity_loss()
        arousal = self.controller.get_arousal()
        
        return logits, total_energy, complexity, per_type_energy, arousal, mixture_weight, temperature, entropy


def run_test():
    """Test v4 with Entropy Stabilizer."""
    from baby_agi_sudoku import generate_puzzles_with_clues
    
    device = "cuda" if torch.cuda.is_available() else "cpu"
    config = AdaptivePolarityConfigV4()
    edges, edge_types = build_sudoku_graph()
    
    model = AdaptivePolarityAgentV4(config, edges, edge_types).to(device)
    
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
    
    print("=" * 120)
    print("ADAPTIVE POLARITY v4: Reactive Repulsion + Entropy Stabilizer")
    print("=" * 120)
    print(f"Device: {device}")
    print(f"Parameters: {sum(p.numel() for p in model.parameters()):,}")
    print(f"Initial g: {model.diffusion.get_mixture_weight().detach().cpu().numpy()}")
    print(f"Entropy Weight: {config.entropy_weight}")
    print(f"TensorBoard: {log_path}")
    print("=" * 120)
    print()
    print("Theory (from SGC.Bridge.Quantum):")
    print("  H = H_interaction + H_stabilizer")
    print("  H_interaction: Reactive repulsion (push when overlap)")
    print("  H_stabilizer: Entropy penalty (gravity toward valid digits)")
    print()
    
    print("-" * 130)
    print(f" {'Ep':>4} | {'Train':>6} | {'Test':>6} | {'Pain':>5} | "
          f"{'g_row':>6} | {'g_col':>6} | {'g_box':>6} | "
          f"{'Temp':>5} | {'Entropy':>7} | Status")
    print("-" * 130)
    
    best_acc = 0.0
    
    for epoch in range(config.epochs):
        model.train()
        train_correct = 0
        train_total = 0
        
        for batch in train_loader:
            puzzles, solutions = [x.to(device) for x in batch]
            
            optimizer.zero_grad()
            
            logits, energy, complexity, per_type_energy, arousal, g, temp, entropy = model(puzzles, solutions)
            
            loss_ce = F.cross_entropy(
                logits.view(-1, 9),
                solutions.view(-1),
                reduction='none'
            ).view(puzzles.shape[0], 81)
            
            unknown_mask = (puzzles == 0).float()
            loss_ce = (loss_ce * unknown_mask).sum() / unknown_mask.sum()
            
            # THE KEY: Add entropy stabilizer to loss
            # This creates "gravity" around valid digits
            loss = loss_ce + 0.5 * energy + complexity + config.entropy_weight * entropy
            
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
            optimizer.step()
            
            with torch.no_grad():
                preds = logits.argmax(dim=-1)
                unknown = (puzzles == 0)
                train_correct += ((preds == solutions) & unknown).sum().item()
                train_total += unknown.sum().item()
        
        scheduler.step()
        
        # Evaluate
        if epoch % config.log_interval == 0:
            model.eval()
            correct = 0
            total = 0
            test_entropy = 0.0
            with torch.no_grad():
                for batch in test_loader:
                    puzzles, solutions = [x.to(device) for x in batch]
                    logits, *_, entropy = model(puzzles)
                    preds = logits.argmax(dim=-1)
                    unknown = (puzzles == 0)
                    correct += ((preds == solutions) & unknown).sum().item()
                    total += unknown.sum().item()
                    test_entropy += entropy.item()
            
            test_acc = correct / max(total, 1)
            train_acc = train_correct / max(train_total, 1)
            test_entropy /= len(test_loader)
            
            g = model.diffusion.get_mixture_weight().detach().cpu()
            arousal_val = model.controller.get_arousal().item()
            temp_val = model.controller.get_temperature().item()
            pain = model.controller.task_pain_ema.item()
            
            status = ""
            if test_acc > best_acc:
                best_acc = test_acc
                status = "BEST"
            if test_acc > 0.90:
                status += " GROKKING!"
            elif test_acc > 0.70:
                status += " CRYSTALLIZING"
            elif g.max() < 0.3:
                status += " REPULSION"
            
            print(f" {epoch:>4} | {train_acc*100:>5.1f}% | {test_acc*100:>5.1f}% | {pain:>5.2f} | "
                  f"{g[0]:>6.3f} | {g[1]:>6.3f} | {g[2]:>6.3f} | "
                  f"{temp_val:>5.3f} | {test_entropy:>7.3f} | {status}")
            
            writer.add_scalar("test/acc", test_acc, epoch)
            writer.add_scalar("train/acc", train_acc, epoch)
            writer.add_scalar("polarity/g_row", g[0], epoch)
            writer.add_scalar("polarity/g_col", g[1], epoch)
            writer.add_scalar("polarity/g_box", g[2], epoch)
            writer.add_scalar("thermo/temperature", temp_val, epoch)
            writer.add_scalar("thermo/arousal", arousal_val, epoch)
            writer.add_scalar("thermo/pain", pain, epoch)
            writer.add_scalar("entropy/test", test_entropy, epoch)
    
    # Summary
    final_g = model.diffusion.get_mixture_weight().detach().cpu()
    print("=" * 120)
    print(f"FINAL: Best Acc={best_acc*100:.1f}%, g=[{final_g[0]:.3f}, {final_g[1]:.3f}, {final_g[2]:.3f}]")
    if best_acc > 0.90:
        print("SUCCESS: GROKKING ACHIEVED with Entropy Stabilizer!")
    elif best_acc > 0.70:
        print("GOOD: Crystallization in progress.")
    elif final_g.max() < 0.3:
        print("REPULSION DISCOVERED - entropy stabilizer guiding to valid digits.")
    else:
        print("Check hyperparameters.")
    print("=" * 120)
    
    writer.close()
    return model


if __name__ == "__main__":
    model = run_test()
