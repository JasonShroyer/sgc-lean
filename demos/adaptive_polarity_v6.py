"""
Adaptive Polarity Sheaf Network v6: The Confidence Homeostat

THEORY (Ashby's Law of Requisite Variety):
- To control a system with 9^81 states, the controller needs matching variety
- "Pen" (single state) has insufficient variety
- "Pencil" (superposition + temporal depth) restores Requisite Variety

THE THREE LAYERS:
1. Pen   - Hard facts (clues + finalized answers) - IMMUTABLE
2. Pencil - Tentative hypotheses with confidence alpha in [0,1]
3. Field  - Continuous belief state (probabilities)

THE CONFIDENCE DYNAMICS:
- New mark: alpha = 0.1 (faint)
- Low stress: alpha += eta (harden)
- High stress: alpha -= delta (fade)
- alpha < 0: ERASE (backtrack)
- alpha > 0.95: CRYSTALLIZE to Pen

THE COST FUNCTION (Lyapunov):
J = E_conflict + F_uncertainty + lambda * C_metabolic

This transforms from OPTIMIZATION to NAVIGATION with cybernetic control.
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
class ConfidenceHomeostatConfig:
    """Configuration for v6 Confidence Homeostat."""
    
    stalk_dim: int = 64
    num_cells: int = 81
    num_digits: int = 9
    
    # Diffusion
    diffusion_steps: int = 5  # Steps per cognitive cycle
    diffusion_dt: float = 0.1
    
    # Confidence dynamics
    initial_confidence: float = 0.1  # New pencil marks start faint
    harden_rate: float = 0.15  # Rate of confidence increase (low stress)
    fade_rate: float = 0.2  # Rate of confidence decrease (high stress)
    crystallize_threshold: float = 0.95  # When to promote to Pen
    erase_threshold: float = 0.0  # When to erase pencil mark
    
    # Stress thresholds (relaxed for learning)
    low_stress_threshold: float = 0.2  # Below this, mark hardens
    high_stress_threshold: float = 0.5  # Above this, mark fades
    write_threshold: float = 0.4  # Min probability to write pencil mark (lower for exploration)
    
    # Cognitive cycles (bounded rationality)
    max_cycles: int = 4  # Only 4 full cycles - finite resources
    
    # Physics-informed costs (Landauer's principle)
    # Erasing information costs kT*ln(2) per bit
    # Writing a digit = log2(9) ≈ 3.17 bits
    # Erasing must dissipate this information + recognize error
    write_cost: float = 1.0  # Base cost of state transition
    erase_cost: float = 2.0  # Landauer: erasing costs MORE than writing
    think_cost: float = 0.1  # Cost per diffusion step (metabolic)
    
    # Polarity
    polarity_init: float = 0.0
    
    # Training
    epochs: int = 300
    batch_size: int = 32
    lr: float = 1e-3
    polarity_lr: float = 0.05
    weight_decay: float = 0.01
    
    log_interval: int = 10
    log_dir: str = "logs/adaptive_polarity_v6"


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


class SudokuState:
    """
    The three-layer state representation.
    
    - pen: Hard facts (0 = unknown, 1-9 = digit)
    - pencil: Tentative marks (0 = no mark, 1-9 = digit)
    - confidence: How "hard" is each pencil mark (0.0 to 1.0)
    - age: How many cycles has each mark survived
    """
    
    def __init__(self, puzzles: torch.Tensor):
        batch_size = puzzles.shape[0]
        device = puzzles.device
        
        # Pen layer: original clues (immutable)
        self.pen = puzzles.clone()
        
        # Pencil layer: our guesses (0 = no guess)
        self.pencil = torch.zeros_like(puzzles)
        
        # Confidence: how sure are we of each pencil mark
        self.confidence = torch.zeros(batch_size, 81, device=device)
        
        # Age: how long has each mark survived
        self.age = torch.zeros(batch_size, 81, device=device, dtype=torch.long)
    
    def get_effective_board(self) -> torch.Tensor:
        """Get the board as seen by the network (pen + confident pencil)."""
        # Pen takes priority, then pencil
        board = self.pen.clone()
        pencil_mask = (self.pen == 0) & (self.pencil > 0)
        board[pencil_mask] = self.pencil[pencil_mask]
        return board
    
    def get_fixed_mask(self, confidence_threshold: float = 0.5) -> torch.Tensor:
        """Get mask of cells that should be treated as fixed."""
        pen_fixed = (self.pen > 0)
        pencil_fixed = (self.pencil > 0) & (self.confidence > confidence_threshold)
        return pen_fixed | pencil_fixed
    
    def write_pencil(self, cell_mask: torch.Tensor, digits: torch.Tensor, 
                     initial_confidence: float):
        """Write new pencil marks."""
        # Only write where pen is empty and no existing pencil
        writeable = (self.pen == 0) & (self.pencil == 0) & cell_mask
        
        self.pencil[writeable] = digits[writeable]
        self.confidence[writeable] = initial_confidence
        self.age[writeable] = 0
    
    def update_confidence(self, stress: torch.Tensor, config: ConfidenceHomeostatConfig):
        """Update confidence based on local stress."""
        has_pencil = (self.pencil > 0)
        
        # Low stress -> harden
        low_stress = (stress < config.low_stress_threshold) & has_pencil
        self.confidence[low_stress] += config.harden_rate
        
        # High stress -> fade
        high_stress = (stress > config.high_stress_threshold) & has_pencil
        self.confidence[high_stress] -= config.fade_rate
        
        # Clamp confidence
        self.confidence = torch.clamp(self.confidence, 0.0, 1.0)
        
        # Increment age for surviving marks
        self.age[has_pencil] += 1
    
    def erase_faded(self, threshold: float = 0.0) -> int:
        """Erase pencil marks that have faded below threshold."""
        to_erase = (self.pencil > 0) & (self.confidence <= threshold)
        erased_count = to_erase.sum().item()
        
        self.pencil[to_erase] = 0
        self.confidence[to_erase] = 0.0
        self.age[to_erase] = 0
        
        return erased_count
    
    def crystallize_confident(self, threshold: float = 0.95) -> int:
        """Promote highly confident pencil marks to pen."""
        to_crystallize = (self.pencil > 0) & (self.confidence >= threshold)
        crystallized_count = to_crystallize.sum().item()
        
        self.pen[to_crystallize] = self.pencil[to_crystallize]
        self.pencil[to_crystallize] = 0
        self.confidence[to_crystallize] = 0.0
        self.age[to_crystallize] = 0
        
        return crystallized_count


class SheafDiffusionV6(nn.Module):
    """Sheaf diffusion with stress computation."""
    
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
    
    def compute_cell_stress(self, logits: torch.Tensor) -> torch.Tensor:
        """
        Compute stress (conflict energy) per cell.
        
        Stress = sum of overlap with all neighbors.
        High stress means the cell's prediction conflicts with neighbors.
        """
        probs = F.softmax(logits, dim=-1)
        batch_size = probs.shape[0]
        
        src_probs = probs[:, self.src_idx, :]
        dst_probs = probs[:, self.dst_idx, :]
        
        # Overlap per edge
        overlap = (src_probs * dst_probs).sum(dim=-1)  # (batch, num_edges)
        
        # Aggregate to cells
        cell_stress = torch.zeros(batch_size, 81, device=logits.device)
        cell_stress.scatter_add_(1, self.src_idx.unsqueeze(0).expand(batch_size, -1), overlap)
        cell_stress.scatter_add_(1, self.dst_idx.unsqueeze(0).expand(batch_size, -1), overlap)
        
        # Normalize by number of neighbors (~20 per cell)
        cell_stress = cell_stress / 20.0
        
        return cell_stress
    
    def compute_total_energy(self, logits: torch.Tensor) -> torch.Tensor:
        """Compute total constraint energy."""
        probs = F.softmax(logits, dim=-1)
        
        src_probs = probs[:, self.src_idx, :]
        dst_probs = probs[:, self.dst_idx, :]
        
        overlap = (src_probs * dst_probs).sum(dim=-1)
        return overlap.mean()
    
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
                dt: float, fixed_mask: torch.Tensor) -> torch.Tensor:
        """Reactive repulsion diffusion."""
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
        
        # Reactive repulsive flow
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
        
        # Fixed cell clamping
        fixed_mask_expanded = fixed_mask.unsqueeze(-1)
        new_stalks = torch.where(fixed_mask_expanded, stalks, new_stalks)
        
        return new_stalks


class ConfidenceHomeostat(nn.Module):
    """
    The SGC Homeostat: A cybernetic controller for Sudoku.
    
    Sense -> Think -> Act cycle with confidence-based pencil marks.
    """
    
    def __init__(self, config: ConfidenceHomeostatConfig,
                 edges: List[Tuple[int, int]], edge_types: Dict[str, List[int]]):
        super().__init__()
        self.config = config
        
        self.embed = nn.Embedding(10, config.stalk_dim)
        
        self.cell_mlp = nn.Sequential(
            nn.Linear(config.stalk_dim, config.stalk_dim * 2),
            nn.ReLU(),
            nn.Linear(config.stalk_dim * 2, config.stalk_dim),
        )
        
        self.diffusion = SheafDiffusionV6(
            edges, edge_types, config.stalk_dim, config.polarity_init
        )
        
        self.output_head = nn.Linear(config.stalk_dim, config.num_digits)
    
    def sense(self, state: SudokuState) -> Tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
        """
        Phase A: Perception
        
        Returns: stalks, logits, stress
        """
        board = state.get_effective_board()
        fixed_mask = state.get_fixed_mask(confidence_threshold=0.5)
        
        stalks = self.embed(board)
        stalks = stalks + self.cell_mlp(stalks)
        
        # Quick diffusion to propagate information
        for _ in range(self.config.diffusion_steps):
            logits = self.output_head(stalks)
            stalks = self.diffusion.diffuse(stalks, logits, self.config.diffusion_dt, fixed_mask)
            stalks = stalks + 0.1 * self.cell_mlp(stalks)
        
        logits = self.output_head(stalks)
        stress = self.diffusion.compute_cell_stress(logits)
        
        return stalks, logits, stress
    
    def think_and_act(self, state: SudokuState, logits: torch.Tensor, stress: torch.Tensor):
        """
        Phase B+C: Simulation and Commitment
        
        - Write new pencil marks where confident
        - Update confidence based on stress
        - Erase faded marks
        - Crystallize confident marks
        """
        config = self.config
        probs = F.softmax(logits, dim=-1)
        max_probs, best_digits = probs.max(dim=-1)  # (batch, 81)
        best_digits = best_digits + 1  # Convert to 1-9
        
        # 1. UPDATE existing pencil marks based on stress
        state.update_confidence(stress, config)
        
        # 2. ERASE faded marks (backtracking!)
        erased = state.erase_faded(config.erase_threshold)
        
        # 3. CRYSTALLIZE confident marks (promote to pen)
        crystallized = state.crystallize_confident(config.crystallize_threshold)
        
        # 4. WRITE new pencil marks where:
        #    - Cell is empty (no pen, no pencil)
        #    - High probability (confident prediction)
        #    - Low stress (not in conflict)
        writeable = (state.pen == 0) & (state.pencil == 0)
        confident = (max_probs > config.write_threshold)
        low_stress = (stress < config.high_stress_threshold)
        
        write_mask = writeable & confident & low_stress
        state.write_pencil(write_mask, best_digits, config.initial_confidence)
        written = write_mask.sum().item()
        
        return written, erased, crystallized
    
    def cognitive_cycle(self, state: SudokuState) -> Dict:
        """Run one complete Sense -> Think -> Act cycle."""
        stalks, logits, stress = self.sense(state)
        written, erased, crystallized = self.think_and_act(state, logits, stress)
        
        return {
            'logits': logits,
            'stress': stress,
            'written': written,
            'erased': erased,
            'crystallized': crystallized,
            'mean_stress': stress.mean().item(),
        }
    
    def solve(self, puzzles: torch.Tensor, max_cycles: Optional[int] = None) -> Tuple[SudokuState, Dict]:
        """
        Solve puzzles using the cognitive loop.
        
        Physics-informed: Each action has a cost derived from Landauer's principle.
        Limited to max_cycles (bounded rationality).
        
        Returns: final state, statistics
        """
        if max_cycles is None:
            max_cycles = self.config.max_cycles
        
        state = SudokuState(puzzles)
        config = self.config
        
        stats = {
            'total_written': 0,
            'total_erased': 0,
            'total_crystallized': 0,
            'cycles_used': 0,
            'total_energy': 0.0,  # Physics-informed energy expenditure
        }
        
        for cycle in range(max_cycles):
            # SENSE: Get feedback from Sudoku world
            stalks, logits, stress = self.sense(state)
            
            # Accumulate thinking cost
            stats['total_energy'] += config.think_cost * config.diffusion_steps
            
            # THINK & ACT: Make decisions based on world feedback
            written, erased, crystallized = self.think_and_act(state, logits, stress)
            
            # Accumulate action costs (Landauer-informed)
            stats['total_energy'] += written * config.write_cost
            stats['total_energy'] += erased * config.erase_cost  # Erasing costs MORE
            
            stats['total_written'] += written
            stats['total_erased'] += erased
            stats['total_crystallized'] += crystallized
            stats['cycles_used'] += 1
            
            # Check if solved (all cells filled)
            unsolved = (state.pen == 0) & (state.pencil == 0)
            if not unsolved.any():
                break
        
        # Final sense for evaluation
        _, final_logits, _ = self.sense(state)
        stats['final_logits'] = final_logits
        
        return state, stats
    
    def forward(self, puzzles: torch.Tensor, solutions: Optional[torch.Tensor] = None):
        """
        Forward pass for training.
        
        During training, we run the cognitive loop and compute loss on final state.
        """
        state, stats = self.solve(puzzles)
        
        logits = stats['final_logits']
        energy = self.diffusion.compute_total_energy(logits)
        
        return logits, energy, state, stats


def evaluate(model, test_loader, device):
    """Evaluate using the cognitive loop."""
    model.eval()
    
    total_correct = 0
    total_cells = 0
    total_crystallized = 0
    total_erased = 0
    total_cycles = 0
    total_puzzles = 0
    
    with torch.no_grad():
        for batch in test_loader:
            puzzles, solutions = [x.to(device) for x in batch]
            
            state, stats = model.solve(puzzles)
            
            # Get predictions from final state
            final_board = state.get_effective_board()
            preds = final_board - 1  # Convert to 0-8
            preds = torch.clamp(preds, 0, 8)
            
            # For cells still empty, use logits
            still_empty = (final_board == 0)
            if still_empty.any():
                logit_preds = stats['final_logits'].argmax(dim=-1)
                preds[still_empty] = logit_preds[still_empty]
            
            # Count correct
            unknown = (puzzles == 0)
            correct = ((preds == solutions) & unknown).sum().item()
            total_correct += correct
            total_cells += unknown.sum().item()
            
            total_crystallized += stats['total_crystallized']
            total_erased += stats['total_erased']
            total_cycles += stats['cycles_used']
            total_puzzles += puzzles.shape[0]
    
    accuracy = total_correct / max(total_cells, 1)
    avg_crystallized = total_crystallized / max(total_puzzles, 1)
    avg_erased = total_erased / max(total_puzzles, 1)
    avg_cycles = total_cycles / max(total_puzzles, 1)
    
    return accuracy, avg_crystallized, avg_erased, avg_cycles


def run_test():
    """Test v6 Confidence Homeostat."""
    from baby_agi_sudoku import generate_puzzles_with_clues
    
    device = "cuda" if torch.cuda.is_available() else "cpu"
    config = ConfidenceHomeostatConfig()
    edges, edge_types = build_sudoku_graph()
    
    model = ConfidenceHomeostat(config, edges, edge_types).to(device)
    
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
        {'params': restriction_params, 'lr': 1e-3, 'weight_decay': 0.001},
    ])
    
    scheduler = torch.optim.lr_scheduler.CosineAnnealingLR(optimizer, T_max=config.epochs)
    
    # Logging
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_path = f"{config.log_dir}/run_{timestamp}"
    os.makedirs(log_path, exist_ok=True)
    writer = SummaryWriter(log_path)
    
    print("=" * 140)
    print("ADAPTIVE POLARITY v6: The Confidence Homeostat")
    print("=" * 140)
    print(f"Device: {device}")
    print(f"Parameters: {sum(p.numel() for p in model.parameters()):,}")
    print(f"Max cycles: {config.max_cycles}")
    print(f"Crystallize threshold: {config.crystallize_threshold}")
    print(f"TensorBoard: {log_path}")
    print("=" * 140)
    print()
    print("Theory (Ashby's Law of Requisite Variety):")
    print("  Pen (fact) + Pencil (hypothesis) + Field (belief)")
    print("  Confidence hardens on low stress, fades on high stress")
    print("  BACKTRACKING enabled via pencil erasure")
    print()
    
    print("-" * 140)
    print(f" {'Ep':>4} | {'Train':>6} | {'Test':>6} | {'Cryst':>6} | {'Erased':>6} | "
          f"{'Cycles':>6} | {'g_row':>6} | {'g_col':>6} | {'g_box':>6} | Status")
    print("-" * 140)
    
    best_acc = 0.0
    
    for epoch in range(config.epochs):
        model.train()
        train_correct = 0
        train_total = 0
        
        for batch in train_loader:
            puzzles, solutions = [x.to(device) for x in batch]
            
            optimizer.zero_grad()
            
            logits, energy, state, stats = model(puzzles, solutions)
            
            # Task loss on final predictions
            loss_ce = F.cross_entropy(
                logits.view(-1, 9),
                solutions.view(-1),
                reduction='none'
            ).view(puzzles.shape[0], 81)
            
            unknown_mask = (puzzles == 0).float()
            loss_ce = (loss_ce * unknown_mask).sum() / unknown_mask.sum()
            
            # Total loss (physics-informed)
            total_energy_cost = stats['total_energy']
            loss = loss_ce + 0.5 * energy + 0.01 * total_energy_cost
            
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
            test_acc, avg_cryst, avg_erased, avg_cycles = evaluate(model, test_loader, device)
            train_acc = train_correct / max(train_total, 1)
            
            g = model.diffusion.get_mixture_weight().detach().cpu()
            
            status = ""
            if test_acc > best_acc:
                best_acc = test_acc
                status = "BEST"
            if test_acc > 0.95:
                status += " SOLVED!"
            elif test_acc > 0.90:
                status += " CRYSTALLIZING"
            elif avg_erased > 5:
                status += " BACKTRACKING"
            elif g.max() < 0.3:
                status += " REPULSION"
            
            print(f" {epoch:>4} | {train_acc*100:>5.1f}% | {test_acc*100:>5.1f}% | "
                  f"{avg_cryst:>6.1f} | {avg_erased:>6.1f} | {avg_cycles:>6.1f} | "
                  f"{g[0]:>6.3f} | {g[1]:>6.3f} | {g[2]:>6.3f} | {status}")
            
            writer.add_scalar("test/acc", test_acc, epoch)
            writer.add_scalar("train/acc", train_acc, epoch)
            writer.add_scalar("homeostat/crystallized", avg_cryst, epoch)
            writer.add_scalar("homeostat/erased", avg_erased, epoch)
            writer.add_scalar("homeostat/cycles", avg_cycles, epoch)
            writer.add_scalar("polarity/g_row", g[0], epoch)
            writer.add_scalar("polarity/g_col", g[1], epoch)
            writer.add_scalar("polarity/g_box", g[2], epoch)
    
    # Final evaluation
    final_acc, final_cryst, final_erased, final_cycles = evaluate(model, test_loader, device)
    final_g = model.diffusion.get_mixture_weight().detach().cpu()
    
    print("=" * 140)
    print(f"FINAL: Acc={final_acc*100:.1f}%, Crystallized={final_cryst:.1f}, "
          f"Erased={final_erased:.1f}, Cycles={final_cycles:.1f}")
    print(f"       g=[{final_g[0]:.3f}, {final_g[1]:.3f}, {final_g[2]:.3f}]")
    
    if final_acc > 0.95:
        print("SUCCESS: HOMEOSTAT ACHIEVED FULL SOLUTION!")
    elif final_acc > 0.90:
        print("EXCELLENT: High crystallization with backtracking.")
    elif final_erased > 5:
        print("PROGRESS: Backtracking mechanism active.")
    else:
        print("Check thresholds or cycle count.")
    print("=" * 140)
    
    writer.close()
    return model


if __name__ == "__main__":
    model = run_test()
