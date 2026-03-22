"""
Homeostatic Sudoku Agent: SGC-Native Constraint Satisfaction
=============================================================

A minimal, principled implementation of the "Cybernetic Sheaf" architecture
for Sudoku, applying all lessons from the Cellular Sheaf experiments.

Key Design Decisions (from experimental evidence):
1. FIXED TOPOLOGY - 81 nodes, ~810 edges. We learn restriction maps, not structure.
2. QUADRATIC PRIOR PENALTY - Prevents precision collapse (Active Inference v2 lesson).
3. TAU MATCHED TO ENERGY - tau=5.0 worked for p=23; we'll calibrate for Sudoku.
4. SCAFFOLDING - Supervised hints early, then free training.
5. EMA SMOOTHING - alpha=0.95 prevents arousal oscillation.
6. BOUNDED ITERATIONS - Fixed T steps, not self-terminating (gradient stability).
7. "MELTED" HARD EDGES ARE OK - High arousal on constraint edges is a feature.

Architecture:
- Stalks: μ ∈ R^9 (belief logits), γ_prior ∈ R (learned precision)
- Edges: Row/Col/Box constraints with learned restriction maps
- Dynamics: Sheaf Laplacian diffusion modulated by arousal
- Control: Homeostatic precision = γ_prior * sigmoid(tau - EMA_energy)

Date: 2026-02-07
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import DataLoader, TensorDataset
from torch.utils.tensorboard import SummaryWriter
import numpy as np
from dataclasses import dataclass, field
from typing import Tuple, List, Optional, Dict
from datetime import datetime
import os

from sudoku_data_utils import load_or_generate


@dataclass
class SudokuConfig:
    """Configuration for Homeostatic Sudoku Agent."""
    # Architecture
    stalk_dim: int = 64          # Hidden dimension per cell
    num_digits: int = 9          # Output classes (digits 1-9)
    diffusion_steps: int = 15    # Bounded iteration count
    diffusion_dt: float = 0.1    # Time step for diffusion
    
    # Homeostatic Control (calibrated from experiments)
    tau: float = 2.0             # Arousal setpoint (will calibrate)
    ema_alpha: float = 0.95      # EMA smoothing for energy tracking
    precision_floor: float = 0.01  # Minimum precision to prevent collapse
    precision_penalty: float = 0.1   # Quadratic prior penalty weight (increased for Sudoku)
    
    # Training
    epochs: int = 2000
    batch_size: int = 64
    lr: float = 1e-3
    precision_lr: float = 1e-2   # Separate LR for precision params
    weight_decay: float = 0.1
    scaffold_epochs: int = 300   # Supervised scaffolding phase
    scaffold_hint_ratio: float = 0.3  # Fraction of cells given as hints
    
    # Data
    train_puzzles: int = 5000
    test_puzzles: int = 1000
    min_clues: int = 25
    max_clues: int = 35
    seed: int = 42
    
    # Logging
    log_dir: str = "logs/sudoku_homeostatic"
    log_interval: int = 25


def build_sudoku_graph() -> Tuple[List[Tuple[int, int]], Dict[str, List[int]]]:
    """
    Build the Sudoku constraint graph.
    
    Returns:
        edges: List of (i, j) pairs where cells i and j share a constraint
        edge_types: Dict mapping 'row', 'col', 'box' to edge indices
    """
    edges = []
    edge_types = {'row': [], 'col': [], 'box': []}
    
    def cell_idx(r, c):
        return r * 9 + c
    
    # Row constraints: cells in same row must differ
    for r in range(9):
        for c1 in range(9):
            for c2 in range(c1 + 1, 9):
                edges.append((cell_idx(r, c1), cell_idx(r, c2)))
                edge_types['row'].append(len(edges) - 1)
    
    # Column constraints: cells in same column must differ
    for c in range(9):
        for r1 in range(9):
            for r2 in range(r1 + 1, 9):
                edges.append((cell_idx(r1, c), cell_idx(r2, c)))
                edge_types['col'].append(len(edges) - 1)
    
    # Box constraints: cells in same 3x3 box must differ
    for box_r in range(3):
        for box_c in range(3):
            cells = []
            for dr in range(3):
                for dc in range(3):
                    cells.append(cell_idx(box_r * 3 + dr, box_c * 3 + dc))
            for i, c1 in enumerate(cells):
                for c2 in cells[i + 1:]:
                    # Check if this edge already exists (row/col overlap)
                    edge = (min(c1, c2), max(c1, c2))
                    if edge not in [(min(e[0], e[1]), max(e[0], e[1])) for e in edges]:
                        edges.append((c1, c2))
                        edge_types['box'].append(len(edges) - 1)
    
    return edges, edge_types


class RestrictionMap(nn.Module):
    """Learned restriction map between adjacent cells."""
    
    def __init__(self, dim: int):
        super().__init__()
        # Simple linear map (could be MLP, but start minimal)
        self.weight = nn.Parameter(torch.eye(dim) + 0.01 * torch.randn(dim, dim))
    
    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return F.linear(x, self.weight)


class VectorizedSheafDiffusion(nn.Module):
    """Vectorized sheaf diffusion layer for efficiency."""
    
    def __init__(self, stalk_dim: int, edges: List[Tuple[int, int]], 
                 edge_types: Dict[str, List[int]]):
        super().__init__()
        self.stalk_dim = stalk_dim
        self.num_edges = len(edges)
        
        # Precompute edge indices for vectorized operations
        src_indices = torch.tensor([e[0] for e in edges], dtype=torch.long)
        dst_indices = torch.tensor([e[1] for e in edges], dtype=torch.long)
        self.register_buffer('src_idx', src_indices)
        self.register_buffer('dst_idx', dst_indices)
        
        # Edge type indices (0=row, 1=col, 2=box)
        type_idx = torch.zeros(len(edges), dtype=torch.long)
        for i in edge_types['row']:
            type_idx[i] = 0
        for i in edge_types['col']:
            type_idx[i] = 1
        for i in edge_types['box']:
            type_idx[i] = 2
        self.register_buffer('type_idx', type_idx)
        
        # One restriction map per edge type
        # CRITICAL: Initialize with STRONG identity + noise to ensure connectivity
        # This is the "innate topology" - the genome that knows Sudoku structure
        self.restriction_weights = nn.ParameterList([
            nn.Parameter(torch.eye(stalk_dim) + 0.1 * torch.randn(stalk_dim, stalk_dim))
            for _ in range(3)
        ])
    
    def compute_energies(self, stalks: torch.Tensor, 
                         logits: Optional[torch.Tensor] = None) -> Tuple[torch.Tensor, torch.Tensor]:
        """
        Compute constraint energies efficiently.
        
        CRITICAL FIX: For Sudoku, we use EXCLUSION energy (REPULSIVE).
        Standard sheaf energy is ATTRACTIVE (minimize difference).
        Sudoku constraints require REPULSIVE (cells must DIFFER).
        
        We use softmax exclusion: E = sum_d p_u(d) * p_v(d)
        This is HIGH when cells predict same digit, LOW when different.
        Minimizing this encourages different predictions.
        
        Args:
            stalks: (batch, 81, stalk_dim)
            logits: Optional (batch, 81, 9) - if provided, use exclusion energy
        
        Returns:
            per_edge_energy: (num_edges,) mean energy per edge
            per_type_energy: (3,) mean energy per type
        """
        batch_size = stalks.shape[0]
        
        if logits is not None:
            # EXCLUSION ENERGY: Penalize when adjacent cells predict same digit
            # probs: (batch, 81, 9)
            probs = F.softmax(logits, dim=-1)
            
            # Gather probabilities for edge endpoints
            src_probs = probs[:, self.src_idx, :]  # (batch, num_edges, 9)
            dst_probs = probs[:, self.dst_idx, :]
            
            # Exclusion energy: dot product of probability distributions
            # High when cells predict same digit, low when different
            edge_energy = (src_probs * dst_probs).sum(dim=-1).mean(dim=0)  # (num_edges,)
        else:
            # Fallback to stalk-based energy (for compatibility)
            src_stalks = stalks[:, self.src_idx, :]
            dst_stalks = stalks[:, self.dst_idx, :]
            
            # Apply restriction maps per edge type
            restricted = torch.zeros_like(src_stalks)
            for t in range(3):
                mask = (self.type_idx == t)
                if mask.any():
                    restricted[:, mask, :] = torch.einsum(
                        'bed,dd->bed', 
                        src_stalks[:, mask, :], 
                        self.restriction_weights[t]
                    )
            
            edge_energy = ((restricted - dst_stalks) ** 2).mean(dim=(0, 2))
        
        # Aggregate by type
        per_type_energy = torch.zeros(3, device=stalks.device)
        for t in range(3):
            mask = (self.type_idx == t)
            if mask.any():
                per_type_energy[t] = edge_energy[mask].mean()
        
        return edge_energy, per_type_energy
    
    def diffuse(self, stalks: torch.Tensor, precision: torch.Tensor, 
                dt: float) -> torch.Tensor:
        """
        One diffusion step with precision weighting.
        
        Args:
            stalks: (batch, 81, stalk_dim)
            precision: (3,) precision per edge type
            dt: time step
        """
        batch_size, num_cells, stalk_dim = stalks.shape
        
        # Gather stalks
        src_stalks = stalks[:, self.src_idx, :]  # (batch, num_edges, stalk_dim)
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
        
        # Compute flows with precision weighting
        # Flow to dst: precision * (restricted_src - dst)
        # Flow to src: precision * (restricted_dst - src)
        precision_expanded = precision[self.type_idx].view(1, -1, 1)  # (1, num_edges, 1)
        
        flow_to_dst = precision_expanded * (restricted_src - dst_stalks)
        flow_to_src = precision_expanded * (restricted_dst - src_stalks)
        
        # Scatter-add the flows back to stalks
        delta = torch.zeros_like(stalks)
        delta.scatter_add_(1, self.dst_idx.view(1, -1, 1).expand(batch_size, -1, stalk_dim), 
                          dt * flow_to_dst)
        delta.scatter_add_(1, self.src_idx.view(1, -1, 1).expand(batch_size, -1, stalk_dim), 
                          dt * flow_to_src)
        
        return stalks + delta


class HomeostaticPrecisionController(nn.Module):
    """
    Homeostatic precision controller for edge-wise attention.
    
    Implements: γ_eff = γ_prior * sigmoid(tau - EMA_energy)
    
    - γ_prior: Learned "geometry" (slow, structural)
    - arousal: Computed from energy EMA (fast, reactive)
    - γ_eff: Effective precision used in diffusion
    
    KEY FIX: Couples EXTERNAL task loss ("pain") to internal energy.
    This ensures "being wrong feels hot" even if sheaf energy is low.
    """
    
    def __init__(self, num_edge_types: int, tau: float, ema_alpha: float, 
                 precision_floor: float = 0.01, pain_weight: float = 1.0):
        super().__init__()
        self.tau = tau
        self.ema_alpha = ema_alpha
        self.precision_floor = precision_floor
        self.pain_weight = pain_weight  # Weight for external task loss
        
        # Learned prior precision per edge type (row, col, box)
        # Initialize slightly positive to ensure initial connectivity
        self.log_precision_prior = nn.Parameter(torch.ones(num_edge_types) * 0.5)
        
        # EMA of TOTAL energy (sheaf + task pain) per edge type
        self.register_buffer('energy_ema', torch.ones(num_edge_types))
        
        # Track task pain separately for diagnostics
        self.register_buffer('task_pain_ema', torch.zeros(1))
    
    def update_ema(self, sheaf_energies: torch.Tensor, task_pain: Optional[torch.Tensor] = None):
        """
        Update EMA with current energies.
        
        Args:
            sheaf_energies: (num_edge_types,) internal constraint violation
            task_pain: scalar external task loss (cross-entropy)
        """
        with torch.no_grad():
            # Combine internal sheaf energy with external task pain
            if task_pain is not None:
                # Broadcast task pain to all edge types
                pain_per_type = self.pain_weight * task_pain.expand_as(sheaf_energies)
                total_energy = sheaf_energies + pain_per_type
                self.task_pain_ema = self.ema_alpha * self.task_pain_ema + (1 - self.ema_alpha) * task_pain
            else:
                total_energy = sheaf_energies
            
            self.energy_ema = self.ema_alpha * self.energy_ema + (1 - self.ema_alpha) * total_energy
    
    def get_effective_precision(self) -> Tuple[torch.Tensor, torch.Tensor]:
        """
        Compute effective precision from prior and arousal.
        
        Returns:
            prior_precision: The learned structural precision
            effective_precision: Prior modulated by arousal
        """
        # Clamp log_precision to prevent explosion (lesson from Sudoku experiment)
        log_prec_clamped = torch.clamp(self.log_precision_prior, min=-2.0, max=2.0)
        prior = torch.exp(log_prec_clamped)  # Range: [0.14, 7.4]
        
        # Arousal: high when energy > tau, low when energy < tau
        arousal = torch.sigmoid((self.energy_ema - self.tau) / self.tau)
        
        # Effective precision: prior * (1 - arousal), with floor
        effective = prior * (1 - arousal)
        effective = torch.clamp(effective, min=self.precision_floor)
        
        return prior, effective
    
    def get_arousal(self) -> torch.Tensor:
        """Get current arousal levels."""
        return torch.sigmoid((self.energy_ema - self.tau) / self.tau)
    
    def complexity_loss(self) -> torch.Tensor:
        """Quadratic penalty to keep precision near 1 (neutral prior)."""
        return 0.5 * (self.log_precision_prior ** 2).sum()


class HomeostaticSudokuAgent(nn.Module):
    """
    The Cybernetic Sudoku Agent.
    
    A Sheaf Neural Network where:
    - Nodes are the 81 cells
    - Edges are the Sudoku constraints (row/col/box)
    - Dynamics are precision-weighted Laplacian diffusion
    - Control is homeostatic arousal based on constraint energy
    
    Uses vectorized operations for efficiency (no per-edge Python loops).
    """
    
    def __init__(self, config: SudokuConfig):
        super().__init__()
        self.config = config
        
        # Build constraint graph
        self.edges, self.edge_types = build_sudoku_graph()
        self.num_edges = len(self.edges)
        self.num_edge_types = 3  # row, col, box
        
        # Input embedding: digit (0-9) -> stalk_dim
        # 0 = unknown, 1-9 = digits
        self.embed = nn.Embedding(10, config.stalk_dim)
        
        # Per-cell MLP to process stalk state
        self.cell_mlp = nn.Sequential(
            nn.Linear(config.stalk_dim, config.stalk_dim * 2),
            nn.GELU(),
            nn.Linear(config.stalk_dim * 2, config.stalk_dim),
        )
        
        # Vectorized sheaf diffusion (efficient!)
        self.sheaf_diffusion = VectorizedSheafDiffusion(
            stalk_dim=config.stalk_dim,
            edges=self.edges,
            edge_types=self.edge_types,
        )
        
        # Homeostatic precision controller
        self.precision_controller = HomeostaticPrecisionController(
            num_edge_types=self.num_edge_types,
            tau=config.tau,
            ema_alpha=config.ema_alpha,
            precision_floor=config.precision_floor,
        )
        
        # Output head: stalk_dim -> 9 (digit logits)
        self.output_head = nn.Linear(config.stalk_dim, config.num_digits)
    
    def forward(self, puzzles: torch.Tensor, 
                scaffold_hints: Optional[torch.Tensor] = None,
                solutions: Optional[torch.Tensor] = None
                ) -> Tuple[torch.Tensor, torch.Tensor, torch.Tensor, torch.Tensor, torch.Tensor]:
        """
        Forward pass with homeostatic diffusion.
        
        Args:
            puzzles: (batch, 81) tensor of digits 0-9 (0 = unknown)
            scaffold_hints: Optional (batch, 81) tensor of hint digits during scaffolding
            solutions: Optional (batch, 81) tensor of 0-indexed solutions for task pain
        
        Returns:
            logits: (batch, 81, 9) digit predictions
            total_energy: Scalar constraint violation energy
            complexity: Scalar precision penalty
            per_type_energy: (3,) energy per constraint type
            arousal: (3,) arousal per constraint type
        """
        batch_size = puzzles.shape[0]
        device = puzzles.device
        
        # Initialize stalks from puzzle
        stalks = self.embed(puzzles)  # (batch, 81, stalk_dim)
        
        # If scaffolding, mix in hint information
        if scaffold_hints is not None:
            hint_embed = self.embed(scaffold_hints)
            # Blend where hints are provided
            hint_mask = (scaffold_hints > 0).unsqueeze(-1).float()
            stalks = stalks * (1 - hint_mask) + hint_embed * hint_mask
        
        # Process through cell MLP
        stalks = stalks + self.cell_mlp(stalks)
        
        # Get effective precision
        prior_prec, effective_prec = self.precision_controller.get_effective_precision()
        
        # Run diffusion steps (vectorized!)
        for step in range(self.config.diffusion_steps):
            stalks = self.sheaf_diffusion.diffuse(stalks, effective_prec, self.config.diffusion_dt)
            stalks = stalks + 0.1 * self.cell_mlp(stalks)  # Residual update
        
        # Output logits
        logits = self.output_head(stalks)  # (batch, 81, 9)
        
        # Compute EXCLUSION energy using logits (REPULSIVE constraint)
        # This penalizes adjacent cells predicting the same digit
        per_edge_energy, per_type_energy = self.sheaf_diffusion.compute_energies(stalks, logits)
        
        # Compute task pain (external signal) if solutions provided
        # KEY FIX: "Being wrong should feel hot"
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
        
        # Update EMA with sheaf energy + task pain
        self.precision_controller.update_ema(per_type_energy.detach(), 
                                              task_pain.detach() if task_pain is not None else None)
        
        # Total energy (for loss)
        total_energy = per_type_energy.sum()
        
        # Complexity penalty
        complexity = self.config.precision_penalty * self.precision_controller.complexity_loss()
        
        # Current arousal
        arousal = self.precision_controller.get_arousal()
        
        return logits, total_energy, complexity, per_type_energy, arousal


def create_sudoku_datasets(config: SudokuConfig) -> Tuple[TensorDataset, TensorDataset]:
    """Create train and test datasets."""
    # Load/generate puzzles
    train_puzzles, train_solutions = load_or_generate(
        n=config.train_puzzles,
        min_clues=config.min_clues,
        max_clues=config.max_clues,
        seed=config.seed,
        split='train'
    )
    
    test_puzzles, test_solutions = load_or_generate(
        n=config.test_puzzles,
        min_clues=config.min_clues,
        max_clues=config.max_clues,
        seed=config.seed + 1000,
        split='test'
    )
    
    # Convert to tensors (solutions are 1-9, we need 0-8 for cross_entropy)
    train_dataset = TensorDataset(
        torch.tensor(train_puzzles, dtype=torch.long),
        torch.tensor(train_solutions - 1, dtype=torch.long),  # 0-8 for CE
    )
    
    test_dataset = TensorDataset(
        torch.tensor(test_puzzles, dtype=torch.long),
        torch.tensor(test_solutions - 1, dtype=torch.long),
    )
    
    return train_dataset, test_dataset


def generate_scaffold_hints(puzzles: torch.Tensor, solutions: torch.Tensor, 
                            hint_ratio: float) -> torch.Tensor:
    """Generate scaffold hints by revealing some solution cells.
    
    Args:
        puzzles: (batch, 81) with values 0-9 (0=unknown, 1-9=digits)
        solutions: (batch, 81) with values 1-9 (actual digits, NOT 0-indexed)
        hint_ratio: fraction of unknown cells to reveal
    """
    batch_size = puzzles.shape[0]
    device = puzzles.device
    
    hints = puzzles.clone()
    
    for b in range(batch_size):
        # Find unknown cells
        unknown_mask = puzzles[b] == 0
        unknown_indices = torch.where(unknown_mask)[0]
        
        if len(unknown_indices) > 0:
            # Reveal some of them
            num_hints = int(len(unknown_indices) * hint_ratio)
            if num_hints > 0:
                perm = torch.randperm(len(unknown_indices), device=device)[:num_hints]
                reveal_indices = unknown_indices[perm]
                hints[b, reveal_indices] = solutions[b, reveal_indices]  # Already 1-9
    
    return hints


def evaluate(model: HomeostaticSudokuAgent, loader: DataLoader, 
             device: str) -> Tuple[float, float, float]:
    """
    Evaluate model on dataset.
    
    Returns:
        cell_accuracy: Fraction of cells correctly predicted
        puzzle_accuracy: Fraction of puzzles fully solved
        mean_energy: Mean constraint energy
    """
    model.eval()
    
    total_cells = 0
    correct_cells = 0
    total_puzzles = 0
    solved_puzzles = 0
    total_energy = 0.0
    
    with torch.no_grad():
        for batch in loader:
            puzzles, solutions = [x.to(device) for x in batch]
            
            logits, energy, _, _, _ = model(puzzles)
            
            # Predictions (0-8)
            preds = logits.argmax(dim=-1)
            
            # Only count unknown cells
            unknown_mask = puzzles == 0
            
            correct = (preds == solutions) & unknown_mask
            correct_cells += correct.sum().item()
            total_cells += unknown_mask.sum().item()
            
            # Puzzle-level accuracy
            puzzle_correct = (correct == unknown_mask).all(dim=1)
            solved_puzzles += puzzle_correct.sum().item()
            total_puzzles += puzzles.shape[0]
            
            total_energy += energy.item()
    
    cell_acc = correct_cells / max(total_cells, 1)
    puzzle_acc = solved_puzzles / max(total_puzzles, 1)
    mean_energy = total_energy / len(loader)
    
    return cell_acc, puzzle_acc, mean_energy


def run_sudoku_experiment(config: Optional[SudokuConfig] = None):
    """Main training loop for Homeostatic Sudoku Agent."""
    if config is None:
        config = SudokuConfig()
    
    # Setup
    device = 'cuda' if torch.cuda.is_available() else 'cpu'
    torch.manual_seed(config.seed)
    np.random.seed(config.seed)
    
    # Create datasets
    print("Loading/generating Sudoku puzzles...")
    train_dataset, test_dataset = create_sudoku_datasets(config)
    train_loader = DataLoader(train_dataset, batch_size=config.batch_size, shuffle=True)
    test_loader = DataLoader(test_dataset, batch_size=config.batch_size)
    
    # Create model
    model = HomeostaticSudokuAgent(config).to(device)
    num_params = sum(p.numel() for p in model.parameters())
    
    # Separate optimizers for main params and precision params
    main_params = [p for n, p in model.named_parameters() if 'log_precision' not in n]
    precision_params = [model.precision_controller.log_precision_prior]
    
    optimizer = torch.optim.AdamW([
        {'params': main_params, 'lr': config.lr, 'weight_decay': config.weight_decay},
        {'params': precision_params, 'lr': config.precision_lr, 'weight_decay': 0.0},
    ])
    
    # Scheduler
    scheduler = torch.optim.lr_scheduler.CosineAnnealingLR(
        optimizer, T_max=config.epochs, eta_min=config.lr / 10
    )
    
    # Logging
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_dir = f"{config.log_dir}/run_{timestamp}"
    writer = SummaryWriter(log_dir)
    
    # Print header
    print("=" * 100)
    print("HOMEOSTATIC SUDOKU AGENT")
    print("=" * 100)
    print(f"Device: {device}")
    print(f"Parameters: {num_params:,}")
    print(f"Edges: {model.num_edges} (Row: {len(model.edge_types['row'])}, "
          f"Col: {len(model.edge_types['col'])}, Box: {len(model.edge_types['box'])})")
    print(f"Config: tau={config.tau}, ema_alpha={config.ema_alpha}, "
          f"scaffold_epochs={config.scaffold_epochs}")
    print(f"TensorBoard: {log_dir}")
    print("=" * 100)
    
    print("\n" + "-" * 120)
    print(f"{'Epoch':>6} | {'Train':>7} | {'Test':>7} | {'Puzzle':>7} | "
          f"{'Energy':>7} | {'g_row':>6} | {'g_col':>6} | {'g_box':>6} | "
          f"{'a_row':>6} | {'a_col':>6} | {'a_box':>6} | Phase")
    print("-" * 120)
    
    best_puzzle_acc = 0.0
    grok_epoch = None
    
    for epoch in range(config.epochs):
        model.train()
        
        # Determine phase
        if epoch < config.scaffold_epochs:
            phase = "scaffold"
            scaffold_factor = 1.0 - epoch / config.scaffold_epochs
        else:
            phase = "free"
            scaffold_factor = 0.0
        
        epoch_loss = 0.0
        epoch_energy = 0.0
        
        for batch in train_loader:
            puzzles, solutions = [x.to(device) for x in batch]
            
            # Generate scaffold hints if in scaffold phase
            if scaffold_factor > 0:
                hints = generate_scaffold_hints(
                    puzzles, solutions + 1,  # solutions are 0-8, need 1-9 for hints
                    hint_ratio=config.scaffold_hint_ratio * scaffold_factor
                )
            else:
                hints = None
            
            optimizer.zero_grad()
            
            # Pass solutions to model for task pain feedback
            logits, energy, complexity, per_type_energy, arousal = model(puzzles, hints, solutions)
            
            # Task loss: cross-entropy on unknown cells
            # logits: (batch, 81, 9), solutions: (batch, 81)
            loss_ce = F.cross_entropy(
                logits.view(-1, 9),
                solutions.view(-1),
                reduction='none'
            ).view(puzzles.shape[0], 81)
            
            # Mask to only count unknown cells
            unknown_mask = (puzzles == 0).float()
            loss_ce = (loss_ce * unknown_mask).sum() / unknown_mask.sum()
            
            # Total loss
            # CRITICAL: Exclusion energy is now REPULSIVE (penalizes same predictions)
            # Use stronger weight (1.0) to enforce Sudoku constraints
            loss = loss_ce + 1.0 * energy + complexity
            
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
            optimizer.step()
            
            epoch_loss += loss.item()
            epoch_energy += energy.item()
        
        scheduler.step()
        
        # Evaluate
        if epoch % config.log_interval == 0 or epoch == config.epochs - 1:
            train_cell_acc, train_puzzle_acc, _ = evaluate(model, train_loader, device)
            test_cell_acc, test_puzzle_acc, test_energy = evaluate(model, test_loader, device)
            
            # Get precision and arousal
            with torch.no_grad():
                prior_prec, eff_prec = model.precision_controller.get_effective_precision()
                arousal = model.precision_controller.get_arousal()
            
            # Check for grokking
            is_best = test_puzzle_acc > best_puzzle_acc
            if is_best:
                best_puzzle_acc = test_puzzle_acc
            
            grokked = test_puzzle_acc > 0.95
            if grokked and grok_epoch is None:
                grok_epoch = epoch
            
            # Status string
            status = phase
            if scaffold_factor > 0:
                status += f"({scaffold_factor:.2f})"
            if grokked:
                status = "*** GROKKED ***"
            elif is_best:
                status += " (best)"
            
            # Print
            print(f"{epoch:6} | {train_cell_acc:6.1%} | {test_cell_acc:6.1%} | {test_puzzle_acc:6.1%} | "
                  f"{test_energy:7.2f} | {prior_prec[0]:6.2f} | {prior_prec[1]:6.2f} | {prior_prec[2]:6.2f} | "
                  f"{arousal[0]:6.2f} | {arousal[1]:6.2f} | {arousal[2]:6.2f} | {status}")
            
            # TensorBoard
            writer.add_scalar('Accuracy/train_cell', train_cell_acc, epoch)
            writer.add_scalar('Accuracy/test_cell', test_cell_acc, epoch)
            writer.add_scalar('Accuracy/test_puzzle', test_puzzle_acc, epoch)
            writer.add_scalar('Energy/total', test_energy, epoch)
            writer.add_scalar('Precision/row', prior_prec[0].item(), epoch)
            writer.add_scalar('Precision/col', prior_prec[1].item(), epoch)
            writer.add_scalar('Precision/box', prior_prec[2].item(), epoch)
            writer.add_scalar('Arousal/row', arousal[0].item(), epoch)
            writer.add_scalar('Arousal/col', arousal[1].item(), epoch)
            writer.add_scalar('Arousal/box', arousal[2].item(), epoch)
            
            # Early stopping if grokked
            if grokked and epoch >= config.scaffold_epochs + 100:
                print(f"\n>>> Early stopping: Grokked at epoch {grok_epoch} <<<")
                break
    
    # Final summary
    print("\n" + "=" * 100)
    print("RESULTS")
    print("=" * 100)
    if grok_epoch is not None:
        print(f"  GROKKED at epoch {grok_epoch}")
    else:
        print(f"  Did not grok (best puzzle acc: {best_puzzle_acc:.1%})")
    
    with torch.no_grad():
        prior_prec, eff_prec = model.precision_controller.get_effective_precision()
        arousal = model.precision_controller.get_arousal()
        ema = model.precision_controller.energy_ema
    
    print(f"\n  Final State:")
    print(f"    Prior Precision: [row={prior_prec[0]:.3f}, col={prior_prec[1]:.3f}, box={prior_prec[2]:.3f}]")
    print(f"    Effective Prec:  [row={eff_prec[0]:.3f}, col={eff_prec[1]:.3f}, box={eff_prec[2]:.3f}]")
    print(f"    Arousal:         [row={arousal[0]:.3f}, col={arousal[1]:.3f}, box={arousal[2]:.3f}]")
    print(f"    Energy EMA:      [row={ema[0]:.3f}, col={ema[1]:.3f}, box={ema[2]:.3f}]")
    print("=" * 100)
    
    writer.close()
    
    return model, grok_epoch


if __name__ == "__main__":
    # Fast config for initial testing
    # tau calibrated to match actual energy scale (~0.05-0.1)
    config = SudokuConfig(
        epochs=500,
        train_puzzles=1000,
        test_puzzles=200,
        batch_size=32,
        diffusion_steps=8,
        scaffold_epochs=100,
        tau=0.1,              # Calibrated to energy scale
        log_interval=10,
    )
    
    model, grok_epoch = run_sudoku_experiment(config)
