"""
Adaptive Polarity Sheaf Network

This module implements the "Sign-Switching Controller" that allows the agent
to automatically detect whether constraints should be ATTRACTIVE or REPULSIVE.

Key Innovation:
- Each edge type has a learnable polarity σ ∈ ℝ (soft sign via tanh)
- σ > 0: Attractive (minimize difference) - e.g., modular arithmetic
- σ < 0: Repulsive (maximize difference) - e.g., Sudoku constraints
- The polarity is learned via gradient descent on the TASK loss

This makes the agent "Energy-Agnostic" - it senses the gradient of the task
and aligns its internal physics to match, without hard-coding constraint types.

Theory: "Constraint Types are Latent Variables"
- Equality constraints (x = y) → σ = +1 (Attractive)
- Inequality constraints (x ≠ y) → σ = -1 (Repulsive)
- The agent meta-learns which type reduces global surprise
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import DataLoader, TensorDataset
from torch.utils.tensorboard import SummaryWriter
from dataclasses import dataclass, field
from typing import List, Tuple, Dict, Optional
import numpy as np
from datetime import datetime
import os


@dataclass
class AdaptivePolarityConfig:
    """Configuration for Adaptive Polarity Sheaf Network."""
    
    # Architecture
    stalk_dim: int = 64
    num_cells: int = 81  # Sudoku grid size
    num_digits: int = 9
    diffusion_steps: int = 10
    diffusion_dt: float = 0.1
    
    # Homeostatic Control
    tau: float = 0.5  # Arousal setpoint
    ema_alpha: float = 0.95
    precision_floor: float = 0.01
    
    # Polarity Learning
    polarity_lr: float = 0.1  # Separate LR for polarity parameters
    polarity_init: float = 0.0  # Start neutral (neither attractive nor repulsive)
    
    # Training
    epochs: int = 500
    batch_size: int = 32
    lr: float = 1e-3
    weight_decay: float = 0.1
    
    # Logging
    log_interval: int = 10
    log_dir: str = "logs/adaptive_polarity"


class AdaptivePolarityDiffusion(nn.Module):
    """
    Sheaf diffusion with LEARNABLE constraint polarity.
    
    The polarity σ determines whether the constraint is:
    - Attractive (σ > 0): Minimize ||R(x_u) - x_v||²
    - Repulsive (σ < 0): Maximize ||R(x_u) - x_v||² (or minimize overlap)
    
    The polarity is learned via backprop through the task loss.
    """
    
    def __init__(self, stalk_dim: int, edges: List[Tuple[int, int]], 
                 edge_types: Dict[str, List[int]], polarity_init: float = 0.0):
        super().__init__()
        self.stalk_dim = stalk_dim
        self.num_edges = len(edges)
        self.num_edge_types = 3  # row, col, box
        
        # Precompute edge indices
        src_indices = torch.tensor([e[0] for e in edges], dtype=torch.long)
        dst_indices = torch.tensor([e[1] for e in edges], dtype=torch.long)
        self.register_buffer('src_idx', src_indices)
        self.register_buffer('dst_idx', dst_indices)
        
        # Edge type indices
        type_idx = torch.zeros(len(edges), dtype=torch.long)
        for i in edge_types['row']:
            type_idx[i] = 0
        for i in edge_types['col']:
            type_idx[i] = 1
        for i in edge_types['box']:
            type_idx[i] = 2
        self.register_buffer('type_idx', type_idx)
        
        # Restriction maps per edge type
        self.restriction_weights = nn.ParameterList([
            nn.Parameter(torch.eye(stalk_dim) + 0.1 * torch.randn(stalk_dim, stalk_dim))
            for _ in range(3)
        ])
        
        # LEARNABLE POLARITY per edge type
        # Initialized to 0 (neutral) - will learn to be +1 (attractive) or -1 (repulsive)
        # Using raw parameter, apply tanh to get soft sign in [-1, 1]
        self.polarity_logit = nn.Parameter(torch.ones(3) * polarity_init)
    
    def get_polarity(self) -> torch.Tensor:
        """Get effective polarity via tanh (soft sign in [-1, 1])."""
        return torch.tanh(self.polarity_logit)
    
    def compute_energies(self, stalks: torch.Tensor, 
                         logits: Optional[torch.Tensor] = None
                         ) -> Tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
        """
        Compute constraint energies with ADAPTIVE polarity.
        
        The energy formulation adapts based on learned polarity:
        - σ > 0: Standard sheaf energy (attractive)
        - σ < 0: Exclusion energy (repulsive)
        
        We use a soft interpolation between the two based on σ.
        
        Returns:
            per_edge_energy: (num_edges,)
            per_type_energy: (3,)
            polarity: (3,) current polarity values
        """
        batch_size = stalks.shape[0]
        polarity = self.get_polarity()
        
        # Gather stalks
        src_stalks = stalks[:, self.src_idx, :]
        dst_stalks = stalks[:, self.dst_idx, :]
        
        # Compute ATTRACTIVE energy (standard sheaf)
        restricted = torch.zeros_like(src_stalks)
        for t in range(3):
            mask = (self.type_idx == t)
            if mask.any():
                restricted[:, mask, :] = torch.einsum(
                    'bed,dd->bed', 
                    src_stalks[:, mask, :], 
                    self.restriction_weights[t]
                )
        attractive_energy = ((restricted - dst_stalks) ** 2).mean(dim=-1)  # (batch, num_edges)
        
        # Compute REPULSIVE energy (exclusion via probability overlap)
        if logits is not None:
            probs = F.softmax(logits, dim=-1)
            src_probs = probs[:, self.src_idx, :]
            dst_probs = probs[:, self.dst_idx, :]
            # Overlap: high when same prediction, low when different
            repulsive_energy = (src_probs * dst_probs).sum(dim=-1)  # (batch, num_edges)
        else:
            # Fallback: use negative of attractive (less principled)
            repulsive_energy = -attractive_energy + 1.0
        
        # Combine based on polarity (soft interpolation)
        # σ = +1: use attractive, σ = -1: use repulsive
        # E = (1+σ)/2 * E_attr + (1-σ)/2 * E_repl
        polarity_per_edge = polarity[self.type_idx].unsqueeze(0)  # (1, num_edges)
        combined_energy = (
            (1 + polarity_per_edge) / 2 * attractive_energy +
            (1 - polarity_per_edge) / 2 * repulsive_energy
        )
        
        # Mean over batch
        per_edge_energy = combined_energy.mean(dim=0)  # (num_edges,)
        
        # Aggregate by type
        per_type_energy = torch.zeros(3, device=stalks.device)
        for t in range(3):
            mask = (self.type_idx == t)
            if mask.any():
                per_type_energy[t] = per_edge_energy[mask].mean()
        
        return per_edge_energy, per_type_energy, polarity
    
    def diffuse(self, stalks: torch.Tensor, precision: torch.Tensor,
                dt: float) -> torch.Tensor:
        """
        Diffusion step with polarity-aware dynamics.
        
        For attractive edges: flow towards agreement
        For repulsive edges: flow towards disagreement (orthogonalization)
        """
        batch_size, num_cells, stalk_dim = stalks.shape
        polarity = self.get_polarity()
        
        # Gather stalks
        src_stalks = stalks[:, self.src_idx, :]
        dst_stalks = stalks[:, self.dst_idx, :]
        
        # Apply restriction maps
        restricted_src = torch.zeros_like(src_stalks)
        restricted_dst = torch.zeros_like(dst_stalks)
        
        for t in range(3):
            mask = (self.type_idx == t)
            if mask.any():
                W = self.restriction_weights[t]
                restricted_src[:, mask, :] = torch.einsum('bed,dd->bed', src_stalks[:, mask, :], W)
                restricted_dst[:, mask, :] = torch.einsum('bed,dd->bed', dst_stalks[:, mask, :], W)
        
        # Compute flows with polarity-aware direction
        # σ > 0: Move towards agreement (standard diffusion)
        # σ < 0: Move towards disagreement (anti-diffusion / orthogonalization)
        polarity_per_edge = polarity[self.type_idx].view(1, -1, 1)
        precision_per_edge = precision[self.type_idx].view(1, -1, 1)
        
        # Standard flow (attractive)
        flow_to_dst = precision_per_edge * polarity_per_edge * (restricted_src - dst_stalks)
        flow_to_src = precision_per_edge * polarity_per_edge * (restricted_dst - src_stalks)
        
        # Scatter-add flows
        delta = torch.zeros_like(stalks)
        delta.scatter_add_(1, self.dst_idx.view(1, -1, 1).expand(batch_size, -1, stalk_dim), 
                          dt * flow_to_dst)
        delta.scatter_add_(1, self.src_idx.view(1, -1, 1).expand(batch_size, -1, stalk_dim), 
                          dt * flow_to_src)
        
        return stalks + delta


class AdaptivePolarityController(nn.Module):
    """
    Homeostatic controller with polarity awareness.
    
    Tracks energy and arousal, and provides diagnostics for polarity learning.
    """
    
    def __init__(self, num_edge_types: int, tau: float, ema_alpha: float,
                 precision_floor: float = 0.01):
        super().__init__()
        self.tau = tau
        self.ema_alpha = ema_alpha
        self.precision_floor = precision_floor
        
        # Learned precision prior
        self.log_precision_prior = nn.Parameter(torch.ones(num_edge_types) * 0.5)
        
        # EMA tracking
        self.register_buffer('energy_ema', torch.ones(num_edge_types))
        self.register_buffer('task_pain_ema', torch.zeros(1))
    
    def update_ema(self, energies: torch.Tensor, task_pain: Optional[torch.Tensor] = None):
        """Update EMA with current energies and task pain."""
        with torch.no_grad():
            if task_pain is not None:
                pain_per_type = task_pain.expand_as(energies)
                total_energy = energies + pain_per_type
                self.task_pain_ema = self.ema_alpha * self.task_pain_ema + (1 - self.ema_alpha) * task_pain
            else:
                total_energy = energies
            
            self.energy_ema = self.ema_alpha * self.energy_ema + (1 - self.ema_alpha) * total_energy
    
    def get_effective_precision(self) -> Tuple[torch.Tensor, torch.Tensor]:
        """Get prior and effective precision."""
        log_prec_clamped = torch.clamp(self.log_precision_prior, min=-2.0, max=2.0)
        prior = torch.exp(log_prec_clamped)
        
        arousal = torch.sigmoid((self.energy_ema - self.tau) / self.tau)
        effective = prior * (1 - arousal)
        effective = torch.clamp(effective, min=self.precision_floor)
        
        return prior, effective
    
    def get_arousal(self) -> torch.Tensor:
        """Get current arousal levels."""
        return torch.sigmoid((self.energy_ema - self.tau) / self.tau)
    
    def complexity_loss(self) -> torch.Tensor:
        """Quadratic penalty on precision."""
        return 0.5 * (self.log_precision_prior ** 2).sum()


class AdaptivePolaritySudokuAgent(nn.Module):
    """
    Sudoku agent with ADAPTIVE constraint polarity.
    
    This agent can automatically discover whether constraints are:
    - Attractive (cells should agree) → learns σ > 0
    - Repulsive (cells should differ) → learns σ < 0
    
    For Sudoku, it should learn σ < 0 for all edge types without hard-coding.
    """
    
    def __init__(self, config: AdaptivePolarityConfig, edges: List[Tuple[int, int]],
                 edge_types: Dict[str, List[int]]):
        super().__init__()
        self.config = config
        self.edges = edges
        self.edge_types = edge_types
        
        # Embedding
        self.embed = nn.Embedding(10, config.stalk_dim)
        
        # Cell MLP
        self.cell_mlp = nn.Sequential(
            nn.Linear(config.stalk_dim, config.stalk_dim * 2),
            nn.GELU(),
            nn.Linear(config.stalk_dim * 2, config.stalk_dim),
        )
        
        # Adaptive polarity diffusion
        self.diffusion = AdaptivePolarityDiffusion(
            stalk_dim=config.stalk_dim,
            edges=edges,
            edge_types=edge_types,
            polarity_init=config.polarity_init,
        )
        
        # Homeostatic controller
        self.controller = AdaptivePolarityController(
            num_edge_types=3,
            tau=config.tau,
            ema_alpha=config.ema_alpha,
            precision_floor=config.precision_floor,
        )
        
        # Output head
        self.output_head = nn.Linear(config.stalk_dim, config.num_digits)
    
    def forward(self, puzzles: torch.Tensor, solutions: Optional[torch.Tensor] = None
                ) -> Tuple[torch.Tensor, torch.Tensor, torch.Tensor, torch.Tensor, torch.Tensor, torch.Tensor]:
        """
        Forward pass with adaptive polarity.
        
        Returns:
            logits, energy, complexity, per_type_energy, arousal, polarity
        """
        batch_size = puzzles.shape[0]
        
        # Embed
        stalks = self.embed(puzzles)
        stalks = stalks + self.cell_mlp(stalks)
        
        # Get precision
        prior_prec, effective_prec = self.controller.get_effective_precision()
        
        # Diffuse
        for step in range(self.config.diffusion_steps):
            stalks = self.diffusion.diffuse(stalks, effective_prec, self.config.diffusion_dt)
            stalks = stalks + 0.1 * self.cell_mlp(stalks)
        
        # Output
        logits = self.output_head(stalks)
        
        # Compute energy with polarity
        per_edge_energy, per_type_energy, polarity = self.diffusion.compute_energies(stalks, logits)
        
        # Task pain
        task_pain = None
        if solutions is not None:
            unknown_mask = (puzzles == 0).float()
            if unknown_mask.sum() > 0:
                task_loss = F.cross_entropy(
                    logits.view(-1, 9),
                    solutions.view(-1),
                    reduction='none'
                ).view(batch_size, 81)
                task_pain = (task_loss * unknown_mask).sum() / unknown_mask.sum()
        
        # Update controller
        self.controller.update_ema(per_type_energy.detach(),
                                   task_pain.detach() if task_pain is not None else None)
        
        # Outputs
        total_energy = per_type_energy.sum()
        complexity = 0.1 * self.controller.complexity_loss()
        arousal = self.controller.get_arousal()
        
        return logits, total_energy, complexity, per_type_energy, arousal, polarity


def build_sudoku_graph() -> Tuple[List[Tuple[int, int]], Dict[str, List[int]]]:
    """Build Sudoku constraint graph."""
    edges = []
    edge_types = {'row': [], 'col': [], 'box': []}
    
    def cell_idx(r, c):
        return r * 9 + c
    
    edge_idx = 0
    
    # Row constraints
    for r in range(9):
        for c1 in range(9):
            for c2 in range(c1 + 1, 9):
                edges.append((cell_idx(r, c1), cell_idx(r, c2)))
                edge_types['row'].append(edge_idx)
                edge_idx += 1
    
    # Column constraints
    for c in range(9):
        for r1 in range(9):
            for r2 in range(r1 + 1, 9):
                edges.append((cell_idx(r1, c), cell_idx(r2, c)))
                edge_types['col'].append(edge_idx)
                edge_idx += 1
    
    # Box constraints
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


if __name__ == "__main__":
    # Test the adaptive polarity mechanism
    print("=" * 80)
    print("ADAPTIVE POLARITY SHEAF NETWORK")
    print("=" * 80)
    
    edges, edge_types = build_sudoku_graph()
    config = AdaptivePolarityConfig()
    
    model = AdaptivePolaritySudokuAgent(config, edges, edge_types)
    print(f"Parameters: {sum(p.numel() for p in model.parameters()):,}")
    print(f"Edges: {len(edges)}")
    print(f"Initial Polarity: {model.diffusion.get_polarity().detach().numpy()}")
    print()
    print("The polarity should learn to be NEGATIVE for Sudoku (repulsive constraints)")
    print("without any hard-coding. The gradient from task loss will drive the learning.")
