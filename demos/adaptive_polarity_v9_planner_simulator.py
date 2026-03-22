"""
Adaptive Polarity Sheaf Network v9: The Planner-Simulator

THEORY (Open System Thermodynamics / Active Inference):

This is the fully realized SGC architecture, equivalent to:
- Generative Flow Networks (GFlowNets)
- Energy-Based Models (EBMs)
- Active Inference

But grounded in thermodynamic physics, not just probability theory.

THE THREE PILLARS:

1. TERRITORY (Physics):
   - The Sheaf Diffusion process
   - Ground truth of constraint satisfaction
   - Expensive to run (8-step lookahead)
   - Outputs: TrueDefectField (81 values)

2. MAP (Simulator / World Model):
   - Neural network that PREDICTS the outcome of Physics
   - Input: (Board, PencilMark candidate)
   - Output: PredictedDefectField (81 values) - full energy landscape
   - Loss: MSE(PredictedDefect, TrueDefect)
   - This is NOT a reward estimator - it's a physics simulator

3. PLANNER (Policy):
   - Navigates the MAP to find low-energy states
   - Action = argmin(PredictedDefect) over candidate cells/digits
   - No separate policy network needed - just optimization on Simulator output
   - Flows down the gradient of predicted energy

THE ACTIVE INFERENCE OBJECTIVE:

min_φ D_KL(Q_φ(s') || P_physics(s'|s,a))   [Map Learning - minimize Surprise]
min_π E_{s'~Q_φ}[E(s')]                      [Planning - minimize Expected Energy]

WHY THIS IS THERMODYNAMICALLY CORRECT:
- Simulator minimizes Variational Free Energy (belief ↔ reality alignment)
- Planner minimizes Expected Free Energy (reality ↔ constraints alignment)
- No arbitrary reward - the "loss" is purely predictive accuracy
- The agent doesn't "game" a reward - it learns to mirror physics
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import DataLoader, TensorDataset
from torch.utils.tensorboard import SummaryWriter
from dataclasses import dataclass, field
from typing import List, Tuple, Dict, Optional
from collections import deque
import numpy as np
from datetime import datetime
import sys
import random


@dataclass
class PlannerSimulatorConfig:
    """Configuration for the Open System Planner-Simulator."""
    
    stalk_dim: int = 64
    num_cells: int = 81
    num_digits: int = 9
    
    # Physics (Territory)
    diffusion_steps: int = 5
    diffusion_dt: float = 0.1
    lookahead_steps: int = 8  # For computing TrueDefect
    
    # Simulator (Map)
    simulator_hidden: int = 128
    
    # Replay Buffer for Grounding
    buffer_size: int = 10000
    grounding_freq: int = 4  # Run physics every N actions
    simulator_batch: int = 64  # Batch size for Simulator training
    simulator_updates: int = 2  # Updates per grounding
    
    # Confidence dynamics
    alpha_grow_rate: float = 0.15
    alpha_decay_rate: float = 0.25
    crystallize_threshold: float = 0.90
    evaporate_threshold: float = 0.0
    
    # Defect thresholds for decisions
    low_defect_threshold: float = 0.0  # Below this = good
    high_defect_threshold: float = 0.01  # Above this = bad
    
    # Cognitive cycles
    max_cycles: int = 4
    
    # Polarity
    polarity_init: float = -0.5
    
    # Training
    epochs: int = 100
    batch_size: int = 32
    lr: float = 1e-3
    simulator_lr: float = 1e-3
    polarity_lr: float = 0.05
    weight_decay: float = 0.01
    
    # Logging
    log_interval: int = 1
    log_dir: str = "logs/adaptive_polarity_v9"


def build_sudoku_graph() -> Tuple[List[Tuple[int, int]], Dict[str, List[int]]]:
    """Build Sudoku constraint graph."""
    edges = []
    edge_types = {'row': [], 'col': [], 'box': []}
    edge_idx = 0
    
    for r in range(9):
        for c1 in range(9):
            for c2 in range(c1 + 1, 9):
                edges.append((r * 9 + c1, r * 9 + c2))
                edge_types['row'].append(edge_idx)
                edge_idx += 1
    
    for c in range(9):
        for r1 in range(9):
            for r2 in range(r1 + 1, 9):
                edges.append((r1 * 9 + c, r2 * 9 + c))
                edge_types['col'].append(edge_idx)
                edge_idx += 1
    
    for box_r in range(3):
        for box_c in range(3):
            cells = [(box_r*3+dr)*9 + box_c*3+dc for dr in range(3) for dc in range(3)]
            for i in range(len(cells)):
                for j in range(i + 1, len(cells)):
                    edges.append((cells[i], cells[j]))
                    edge_types['box'].append(edge_idx)
                    edge_idx += 1
    
    return edges, edge_types


class SudokuState:
    """Three-Layer State: Pen, Pencil, Alpha."""
    
    def __init__(self, puzzles: torch.Tensor, solutions: Optional[torch.Tensor] = None):
        B, N = puzzles.shape
        device = puzzles.device
        
        self.pen = puzzles.clone()
        self.pencil = torch.zeros(B, N, dtype=torch.long, device=device)
        self.alpha = torch.zeros(B, N, device=device)
        self.solutions = solutions
    
    def get_effective_board(self) -> torch.Tensor:
        board = self.pen.clone().long()
        mask = (self.pen == 0) & (self.pencil > 0)
        board[mask] = self.pencil[mask]
        return board
    
    def get_fixed_mask(self) -> torch.Tensor:
        return (self.pen > 0) | ((self.pencil > 0) & (self.alpha > 0.5))
    
    def get_empty_cells(self) -> torch.Tensor:
        """Get mask of cells that are empty (no pen, no pencil)."""
        return (self.pen == 0) & (self.pencil == 0)


class ReplayBuffer:
    """
    Experience buffer for grounding the Simulator.
    
    Stores (state_features, action, true_defect) tuples.
    """
    
    def __init__(self, capacity: int):
        self.buffer = deque(maxlen=capacity)
    
    def push(self, state_features: torch.Tensor, cell_idx: int, digit: int, 
             true_defect: torch.Tensor):
        """Store a grounding experience."""
        self.buffer.append({
            'state_features': state_features.detach().cpu(),
            'cell_idx': cell_idx,
            'digit': digit,
            'true_defect': true_defect.detach().cpu()
        })
    
    def sample(self, batch_size: int) -> List[Dict]:
        """Sample a batch of experiences."""
        return random.sample(list(self.buffer), min(batch_size, len(self.buffer)))
    
    def __len__(self):
        return len(self.buffer)


class SheafDiffusion(nn.Module):
    """Sheaf diffusion - THE PHYSICS (Territory)."""
    
    def __init__(self, edges, edge_types, stalk_dim, polarity_init):
        super().__init__()
        self.stalk_dim = stalk_dim
        
        src = torch.tensor([e[0] for e in edges], dtype=torch.long)
        dst = torch.tensor([e[1] for e in edges], dtype=torch.long)
        self.register_buffer('src', src)
        self.register_buffer('dst', dst)
        
        type_idx = torch.zeros(len(edges), dtype=torch.long)
        for t, (_, indices) in enumerate(edge_types.items()):
            for idx in indices:
                type_idx[idx] = t
        self.register_buffer('type_idx', type_idx)
        
        self.W = nn.ParameterList([
            nn.Parameter(torch.eye(stalk_dim) + 0.1 * torch.randn(stalk_dim, stalk_dim))
            for _ in range(3)
        ])
        self.polarity = nn.Parameter(torch.ones(3) * polarity_init)
    
    def get_g(self):
        return torch.sigmoid(self.polarity)
    
    def compute_local_conflict(self, logits: torch.Tensor) -> torch.Tensor:
        """Compute conflict energy per cell."""
        probs = F.softmax(logits, dim=-1)
        B = probs.shape[0]
        
        src_probs = probs[:, self.src, :]
        dst_probs = probs[:, self.dst, :]
        overlap = (src_probs * dst_probs).sum(dim=-1)
        
        conflict = torch.zeros(B, 81, device=logits.device)
        conflict.scatter_add_(1, self.src.unsqueeze(0).expand(B, -1), overlap)
        conflict.scatter_add_(1, self.dst.unsqueeze(0).expand(B, -1), overlap)
        
        conflict = conflict / 20.0
        return conflict
    
    def diffuse(self, stalks, logits, dt, fixed_mask):
        B, N, D = stalks.shape
        probs = F.softmax(logits, dim=-1)
        
        g = self.get_g()[self.type_idx].view(1, -1, 1)
        
        src_s = stalks[:, self.src, :]
        dst_s = stalks[:, self.dst, :]
        
        overlap = (probs[:, self.src, :] * probs[:, self.dst, :]).sum(-1, keepdim=True)
        diff = src_s - dst_s
        
        attr_flow = diff
        repl_flow = -overlap * diff
        
        flow_to_dst = g * attr_flow + (1 - g) * repl_flow
        flow_to_src = -flow_to_dst
        
        drift = torch.zeros_like(stalks)
        drift.scatter_add_(1, self.dst.view(1,-1,1).expand(B,-1,D), dt * flow_to_dst)
        drift.scatter_add_(1, self.src.view(1,-1,1).expand(B,-1,D), dt * flow_to_src)
        
        new_stalks = stalks + drift
        new_stalks = torch.where(fixed_mask.unsqueeze(-1), stalks, new_stalks)
        
        return new_stalks


class WorldSimulator(nn.Module):
    """
    THE MAP: Predicts the energy landscape without running physics.
    
    Input: State features (stalks) + proposed action (cell, digit)
    Output: Predicted defect field (81 values)
    
    This is a generative model of physics, NOT a reward estimator.
    """
    
    def __init__(self, stalk_dim: int, hidden_dim: int):
        super().__init__()
        
        # Encode the state
        self.state_encoder = nn.Sequential(
            nn.Linear(stalk_dim, hidden_dim),
            nn.ReLU(),
            nn.Linear(hidden_dim, hidden_dim),
        )
        
        # Action embedding (digit 1-9)
        self.digit_embed = nn.Embedding(10, hidden_dim)
        
        # Predict defect field
        self.predictor = nn.Sequential(
            nn.Linear(hidden_dim * 2, hidden_dim),
            nn.ReLU(),
            nn.Linear(hidden_dim, hidden_dim),
            nn.ReLU(),
            nn.Linear(hidden_dim, 1)  # Predict defect per cell
        )
    
    def forward(self, stalks: torch.Tensor, candidate_cells: torch.Tensor, 
                candidate_digits: torch.Tensor) -> torch.Tensor:
        """
        Predict defect for candidate actions.
        
        Args:
            stalks: (B, 81, stalk_dim) - current state features
            candidate_cells: (B, K) - candidate cell indices
            candidate_digits: (B, K) - candidate digits for each cell
        
        Returns:
            predicted_defect: (B, K) - predicted defect for each candidate
        """
        B, N, D = stalks.shape
        K = candidate_cells.shape[1]
        
        # Encode state at candidate cells
        # Gather stalks for candidate cells: (B, K, stalk_dim)
        candidate_stalks = torch.gather(
            stalks, 1, 
            candidate_cells.unsqueeze(-1).expand(-1, -1, D)
        )
        state_features = self.state_encoder(candidate_stalks)  # (B, K, hidden)
        
        # Encode candidate digits
        digit_features = self.digit_embed(candidate_digits)  # (B, K, hidden)
        
        # Combine and predict
        combined = torch.cat([state_features, digit_features], dim=-1)  # (B, K, hidden*2)
        predicted_defect = self.predictor(combined).squeeze(-1)  # (B, K)
        
        return predicted_defect
    
    def predict_for_all_digits(self, stalks: torch.Tensor, cell_idx: int) -> torch.Tensor:
        """
        Predict defect for all 9 digits at a specific cell.
        
        Used by Planner to select best digit.
        """
        B = stalks.shape[0]
        device = stalks.device
        
        # All 9 digits as candidates
        candidate_cells = torch.full((B, 9), cell_idx, device=device, dtype=torch.long)
        candidate_digits = torch.arange(1, 10, device=device).unsqueeze(0).expand(B, -1)
        
        return self(stalks, candidate_cells, candidate_digits)


class PlannerSimulatorAgent(nn.Module):
    """
    The Open System Agent with Planner-Simulator architecture.
    
    - Physics (Territory): Sheaf Diffusion - expensive ground truth
    - Simulator (Map): WorldSimulator - fast prediction of energy landscape
    - Planner: argmin over Simulator predictions - no separate network
    """
    
    def __init__(self, config: PlannerSimulatorConfig, edges, edge_types):
        super().__init__()
        self.config = config
        
        # Shared encoder (used by both Physics and Simulator)
        self.embed = nn.Embedding(10, config.stalk_dim)
        self.mlp = nn.Sequential(
            nn.Linear(config.stalk_dim, config.stalk_dim * 2),
            nn.ReLU(),
            nn.Linear(config.stalk_dim * 2, config.stalk_dim),
        )
        self.head = nn.Linear(config.stalk_dim, 9)
        
        # Physics (Territory)
        self.diffusion = SheafDiffusion(edges, edge_types, config.stalk_dim, config.polarity_init)
        
        # Simulator (Map) - learns to predict physics
        self.simulator = WorldSimulator(config.stalk_dim, config.simulator_hidden)
        
        # Replay buffer for grounding
        self.replay_buffer = ReplayBuffer(config.buffer_size)
        
        # Monitoring
        self.stats = {
            'simulator_loss': [],
            'grounding_count': 0,
            'planning_count': 0,
            'crystallizations': 0,
            'evaporations': 0,
        }
    
    def reset_stats(self):
        self.stats = {
            'simulator_loss': [],
            'grounding_count': 0,
            'planning_count': 0,
            'crystallizations': 0,
            'evaporations': 0,
        }
    
    def _run_diffusion(self, state: SudokuState, steps: int) -> Tuple[torch.Tensor, torch.Tensor]:
        """Run physics diffusion."""
        board = state.get_effective_board()
        stalks = self.embed(board)
        stalks = stalks + self.mlp(stalks)
        
        fixed_mask = state.get_fixed_mask()
        
        for _ in range(steps):
            logits = self.head(stalks)
            stalks = self.diffusion.diffuse(stalks, logits, self.config.diffusion_dt, fixed_mask)
            stalks = stalks + 0.1 * self.mlp(stalks)
        
        logits = self.head(stalks)
        return stalks, logits
    
    def get_state_features(self, state: SudokuState) -> Tuple[torch.Tensor, torch.Tensor]:
        """Get current state features (stalks, logits) via diffusion."""
        return self._run_diffusion(state, self.config.diffusion_steps)
    
    @torch.no_grad()
    def compute_true_defect(self, state: SudokuState, conflict_before: torch.Tensor) -> torch.Tensor:
        """
        THE PHYSICS: Run expensive lookahead to get ground truth defect.
        """
        _, logits_after = self._run_diffusion(
            state, 
            self.config.diffusion_steps + self.config.lookahead_steps
        )
        conflict_after = self.diffusion.compute_local_conflict(logits_after)
        return conflict_after - conflict_before
    
    def plan_action(self, stalks: torch.Tensor, state: SudokuState) -> Tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
        """
        THE PLANNER: Select best action using Simulator predictions.
        
        No separate policy network - just argmin over predicted defects.
        
        Returns: (best_cells, best_digits, predicted_defects)
        """
        B = stalks.shape[0]
        device = stalks.device
        config = self.config
        
        empty = state.get_empty_cells()  # (B, 81)
        
        best_cells = torch.zeros(B, dtype=torch.long, device=device)
        best_digits = torch.zeros(B, dtype=torch.long, device=device)
        best_defects = torch.full((B,), float('inf'), device=device)
        
        # For each empty cell, predict defect for all digits
        for cell_idx in range(81):
            cell_empty = empty[:, cell_idx]  # (B,)
            if not cell_empty.any():
                continue
            
            # Predict defect for all 9 digits at this cell
            predicted = self.simulator.predict_for_all_digits(stalks, cell_idx)  # (B, 9)
            
            # Find best digit for this cell
            min_defect, min_digit_idx = predicted.min(dim=1)  # (B,)
            min_digit = min_digit_idx + 1  # Convert to 1-9
            
            # Update best if this cell is better
            better = cell_empty & (min_defect < best_defects)
            best_cells[better] = cell_idx
            best_digits[better] = min_digit[better]
            best_defects[better] = min_defect[better]
        
        self.stats['planning_count'] += B
        
        return best_cells, best_digits, best_defects
    
    def ground_simulator(self, state: SudokuState, stalks: torch.Tensor,
                         cell_idx: int, digit: int, conflict_before: torch.Tensor):
        """
        GROUNDING: Run physics and store experience for Simulator training.
        """
        # Create temporary state with the proposed action
        temp_state = SudokuState(state.pen.clone(), state.solutions)
        temp_state.pencil = state.pencil.clone()
        temp_state.alpha = state.alpha.clone()
        temp_state.pencil[:, cell_idx] = digit
        temp_state.alpha[:, cell_idx] = 0.5
        
        # Run physics to get true defect
        true_defect = self.compute_true_defect(temp_state, conflict_before)
        
        # Store in replay buffer
        for b in range(stalks.shape[0]):
            self.replay_buffer.push(
                stalks[b],
                cell_idx,
                digit,
                true_defect[b, cell_idx]
            )
        
        self.stats['grounding_count'] += 1
        
        return true_defect[:, cell_idx]
    
    def train_simulator(self, optimizer):
        """
        Update Simulator using replay buffer.
        """
        if len(self.replay_buffer) < self.config.simulator_batch:
            return 0.0
        
        total_loss = 0.0
        
        for _ in range(self.config.simulator_updates):
            batch = self.replay_buffer.sample(self.config.simulator_batch)
            
            # Prepare batch
            device = next(self.parameters()).device
            batch_size = len(batch)
            
            # state_features: each is (81, stalk_dim), stack to (batch, 81, stalk_dim)
            state_features = torch.stack([b['state_features'] for b in batch]).to(device)
            cell_indices = torch.tensor([b['cell_idx'] for b in batch], dtype=torch.long).to(device)
            digits = torch.tensor([b['digit'] for b in batch], dtype=torch.long).to(device)
            true_defects = torch.tensor([b['true_defect'] for b in batch], dtype=torch.float).to(device)
            
            # Predict - need (B, K) format where K=1 candidate per sample
            predicted = self.simulator(
                state_features,  # (batch, 81, stalk_dim)
                cell_indices.unsqueeze(-1),  # (batch, 1)
                digits.unsqueeze(-1)  # (batch, 1)
            ).squeeze(-1)  # (batch,)
            
            # MSE loss - align Map with Territory
            loss = F.mse_loss(predicted, true_defects)
            
            optimizer.zero_grad()
            loss.backward()
            optimizer.step()
            
            total_loss += loss.item()
            self.stats['simulator_loss'].append(loss.item())
        
        return total_loss / self.config.simulator_updates
    
    def solve_cycle(self, state: SudokuState, step_count: int, 
                    simulator_optimizer=None) -> Tuple[torch.Tensor, Dict]:
        """
        One cycle of the Planner-Simulator loop.
        """
        config = self.config
        stats = {'written': 0, 'evaporated': 0, 'crystallized': 0}
        
        # Get current state features
        stalks, logits = self.get_state_features(state)
        conflict = self.diffusion.compute_local_conflict(logits)
        
        # === PLANNER: Select action using Simulator ===
        best_cells, best_digits, predicted_defects = self.plan_action(stalks, state)
        
        # === GROUNDING: Occasionally run physics to train Simulator ===
        if step_count % config.grounding_freq == 0 and simulator_optimizer is not None:
            # Ground the most uncertain prediction
            for b in range(stalks.shape[0]):
                if state.get_empty_cells()[b].any():
                    cell = best_cells[b].item()
                    digit = best_digits[b].item()
                    if digit > 0:  # Valid action
                        self.ground_simulator(
                            state, stalks[b:b+1], cell, digit, conflict[b:b+1]
                        )
            
            # Train simulator
            self.train_simulator(simulator_optimizer)
        
        # === EXECUTE ACTION ===
        # Write pencil marks for best predicted cells
        for b in range(stalks.shape[0]):
            if best_digits[b] > 0:  # Valid action found
                cell = best_cells[b].item()
                if state.get_empty_cells()[b, cell]:  # Cell still empty
                    state.pencil[b, cell] = best_digits[b]
                    state.alpha[b, cell] = 0.1
                    stats['written'] += 1
        
        # === UPDATE CONFIDENCE based on predicted defect ===
        has_pencil = (state.pencil > 0)
        
        # For cells with pencil, predict their defect
        for b in range(stalks.shape[0]):
            pencil_cells = has_pencil[b].nonzero(as_tuple=True)[0]
            for cell in pencil_cells:
                cell_idx = cell.item()
                digit = state.pencil[b, cell_idx].item()
                
                # Get predicted defect for this cell/digit
                pred = self.simulator.predict_for_all_digits(stalks[b:b+1], cell_idx)
                pred_defect = pred[0, digit - 1].item()
                
                # Update alpha based on predicted defect
                if pred_defect < config.low_defect_threshold:
                    state.alpha[b, cell_idx] += config.alpha_grow_rate
                elif pred_defect > config.high_defect_threshold:
                    state.alpha[b, cell_idx] -= config.alpha_decay_rate
                else:
                    state.alpha[b, cell_idx] += config.alpha_grow_rate * 0.1
        
        state.alpha = torch.clamp(state.alpha, -0.5, 1.0)
        
        # Phase transitions
        evaporate_mask = (state.alpha < config.evaporate_threshold) & has_pencil
        if evaporate_mask.any():
            state.pencil[evaporate_mask] = 0
            state.alpha[evaporate_mask] = 0.0
            stats['evaporated'] = evaporate_mask.sum().item()
            self.stats['evaporations'] += stats['evaporated']
        
        crystallize_mask = (state.alpha > config.crystallize_threshold) & (state.pencil > 0)
        if crystallize_mask.any():
            state.pen[crystallize_mask] = state.pencil[crystallize_mask]
            state.pencil[crystallize_mask] = 0
            state.alpha[crystallize_mask] = 0.0
            stats['crystallized'] = crystallize_mask.sum().item()
            self.stats['crystallizations'] += stats['crystallized']
        
        return logits, stats
    
    def forward(self, puzzles: torch.Tensor, solutions: Optional[torch.Tensor] = None,
                simulator_optimizer=None) -> Tuple[torch.Tensor, Dict]:
        """Forward pass through Planner-Simulator."""
        state = SudokuState(puzzles, solutions)
        
        agg_stats = {'cycles': 0}
        
        for cycle in range(self.config.max_cycles):
            logits, stats = self.solve_cycle(state, cycle, simulator_optimizer)
            agg_stats['cycles'] += 1
            
            if (state.pen > 0).all():
                break
        
        return logits, agg_stats


# === DATA GENERATION ===

def generate_puzzles(n: int, clues: int = 30) -> Tuple[torch.Tensor, torch.Tensor]:
    """Generate n Sudoku puzzles."""
    
    def make_solution():
        base = np.array([
            [1,2,3,4,5,6,7,8,9],
            [4,5,6,7,8,9,1,2,3],
            [7,8,9,1,2,3,4,5,6],
            [2,3,4,5,6,7,8,9,1],
            [5,6,7,8,9,1,2,3,4],
            [8,9,1,2,3,4,5,6,7],
            [3,4,5,6,7,8,9,1,2],
            [6,7,8,9,1,2,3,4,5],
            [9,1,2,3,4,5,6,7,8]
        ])
        
        for _ in range(20):
            op = np.random.randint(4)
            if op == 0:
                r1, r2 = np.random.choice(3, 2, replace=False)
                band = np.random.randint(3)
                base[[band*3+r1, band*3+r2]] = base[[band*3+r2, band*3+r1]]
            elif op == 1:
                c1, c2 = np.random.choice(3, 2, replace=False)
                stack = np.random.randint(3)
                base[:, [stack*3+c1, stack*3+c2]] = base[:, [stack*3+c2, stack*3+c1]]
            elif op == 2:
                b1, b2 = np.random.choice(3, 2, replace=False)
                base[[b1*3, b1*3+1, b1*3+2, b2*3, b2*3+1, b2*3+2]] = \
                    base[[b2*3, b2*3+1, b2*3+2, b1*3, b1*3+1, b1*3+2]]
            else:
                s1, s2 = np.random.choice(3, 2, replace=False)
                base[:, [s1*3, s1*3+1, s1*3+2, s2*3, s2*3+1, s2*3+2]] = \
                    base[:, [s2*3, s2*3+1, s2*3+2, s1*3, s1*3+1, s1*3+2]]
        
        perm = np.random.permutation(9) + 1
        return perm[base - 1]
    
    puzzles = []
    solutions = []
    
    for _ in range(n):
        sol = make_solution()
        puzzle = sol.copy()
        
        remove = 81 - clues
        indices = np.random.choice(81, remove, replace=False)
        puzzle.flat[indices] = 0
        
        puzzles.append(puzzle.flatten())
        solutions.append(sol.flatten())
    
    return torch.tensor(np.array(puzzles), dtype=torch.long), torch.tensor(np.array(solutions), dtype=torch.long)


# === TRAINING ===

def train_epoch(model: PlannerSimulatorAgent, loader: DataLoader, 
                main_optimizer, simulator_optimizer, device) -> Dict:
    """Train one epoch."""
    model.train()
    total_loss = 0
    total_correct = 0
    total_cells = 0
    
    for puzzles, solutions in loader:
        puzzles = puzzles.to(device)
        solutions = solutions.to(device)
        
        main_optimizer.zero_grad()
        
        logits, stats = model(puzzles, solutions, simulator_optimizer)
        
        # Main loss: cross-entropy
        loss = F.cross_entropy(
            logits.view(-1, 9),
            (solutions - 1).view(-1)
        )
        
        loss.backward()
        main_optimizer.step()
        
        total_loss += loss.item() * puzzles.size(0)
        
        preds = logits.argmax(dim=-1) + 1
        total_correct += (preds == solutions).sum().item()
        total_cells += solutions.numel()
    
    return {
        'loss': total_loss / len(loader.dataset),
        'accuracy': total_correct / total_cells
    }


def evaluate(model: PlannerSimulatorAgent, loader: DataLoader, device) -> Dict:
    """Evaluate on test set."""
    model.eval()
    total_correct = 0
    total_cells = 0
    puzzle_correct = 0
    total_puzzles = 0
    
    with torch.no_grad():
        for puzzles, solutions in loader:
            puzzles = puzzles.to(device)
            solutions = solutions.to(device)
            
            logits, _ = model(puzzles, solutions, simulator_optimizer=None)
            
            preds = logits.argmax(dim=-1) + 1
            total_correct += (preds == solutions).sum().item()
            total_cells += solutions.numel()
            
            puzzle_correct += (preds == solutions).all(dim=1).sum().item()
            total_puzzles += puzzles.size(0)
    
    return {
        'cell_accuracy': total_correct / total_cells,
        'puzzle_accuracy': puzzle_correct / total_puzzles,
    }


def run_simulator_test(model: PlannerSimulatorAgent, device):
    """
    Test if Simulator can predict physics accurately.
    """
    print("\n" + "="*60)
    print("SIMULATOR TEST: Can the Map predict the Territory?")
    print("="*60)
    
    model.eval()
    
    puzzles, solutions = generate_puzzles(1, clues=35)
    puzzles = puzzles.to(device)
    solutions = solutions.to(device)
    
    state = SudokuState(puzzles, solutions)
    
    empty_cells = state.get_empty_cells()[0].nonzero(as_tuple=True)[0]
    if len(empty_cells) == 0:
        print("No empty cells!")
        return False
    
    test_cell = empty_cells[0].item()
    correct_digit = solutions[0, test_cell].item()
    wrong_digit = (correct_digit % 9) + 1
    
    print(f"\nTest cell: {test_cell}")
    print(f"Correct digit: {correct_digit}")
    print(f"Wrong digit: {wrong_digit}")
    
    # Get state features
    with torch.no_grad():
        stalks, logits = model.get_state_features(state)
        conflict = model.diffusion.compute_local_conflict(logits)
    
    # Test CORRECT digit
    print("\n--- Correct Digit ---")
    state_correct = SudokuState(puzzles.clone(), solutions)
    state_correct.pencil[0, test_cell] = correct_digit
    state_correct.alpha[0, test_cell] = 0.5
    
    with torch.no_grad():
        # Simulator prediction
        pred_correct = model.simulator.predict_for_all_digits(stalks, test_cell)
        pred_correct_val = pred_correct[0, correct_digit - 1].item()
        
        # True physics
        true_correct = model.compute_true_defect(state_correct, conflict)
        true_correct_val = true_correct[0, test_cell].item()
        
        print(f"  Simulator prediction: {pred_correct_val:.4f}")
        print(f"  True physics:         {true_correct_val:.4f}")
    
    # Test WRONG digit
    print("\n--- Wrong Digit ---")
    state_wrong = SudokuState(puzzles.clone(), solutions)
    state_wrong.pencil[0, test_cell] = wrong_digit
    state_wrong.alpha[0, test_cell] = 0.5
    
    with torch.no_grad():
        pred_wrong_val = pred_correct[0, wrong_digit - 1].item()
        
        true_wrong = model.compute_true_defect(state_wrong, conflict)
        true_wrong_val = true_wrong[0, test_cell].item()
        
        print(f"  Simulator prediction: {pred_wrong_val:.4f}")
        print(f"  True physics:         {true_wrong_val:.4f}")
    
    print("\n--- Verification ---")
    
    physics_ok = true_correct_val < true_wrong_val
    simulator_ok = pred_correct_val < pred_wrong_val
    
    print(f"Physics:   {'[PASS]' if physics_ok else '[FAIL]'} correct={true_correct_val:.4f} vs wrong={true_wrong_val:.4f}")
    print(f"Simulator: {'[PASS]' if simulator_ok else '[FAIL]'} correct={pred_correct_val:.4f} vs wrong={pred_wrong_val:.4f}")
    
    if simulator_ok:
        print("\n[SUCCESS] Simulator has learned to mirror physics!")
    else:
        print("\n[TRAINING NEEDED] Simulator hasn't learned yet.")
    
    print("="*60)
    return simulator_ok


def main():
    print("="*70)
    print("Adaptive Polarity v9: The Planner-Simulator")
    print("="*70)
    print("\nOpen System Thermodynamics / Active Inference")
    print("- Territory (Physics): Sheaf Diffusion - expensive ground truth")
    print("- Map (Simulator): Predicts energy landscape - fast approximation")
    print("- Planner: argmin over Simulator - flows down predicted gradient")
    print("="*70)
    
    device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
    print(f"\nDevice: {device}")
    
    config = PlannerSimulatorConfig()
    edges, edge_types = build_sudoku_graph()
    
    model = PlannerSimulatorAgent(config, edges, edge_types).to(device)
    
    # TensorBoard
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_dir = f"{config.log_dir}/{timestamp}"
    writer = SummaryWriter(log_dir)
    print(f"\nTensorBoard logs: {log_dir}")
    print(f"  Run: tensorboard --logdir={config.log_dir}")
    
    # Initial test
    print("\n[Initial Simulator Test - Before Training]")
    run_simulator_test(model, device)
    
    # Generate data
    print("\nGenerating training data...")
    train_puzzles, train_solutions = generate_puzzles(1000, clues=30)
    test_puzzles, test_solutions = generate_puzzles(200, clues=30)
    
    train_loader = DataLoader(
        TensorDataset(train_puzzles, train_solutions),
        batch_size=config.batch_size, shuffle=True
    )
    test_loader = DataLoader(
        TensorDataset(test_puzzles, test_solutions),
        batch_size=config.batch_size
    )
    
    # Optimizers
    main_params = [p for n, p in model.named_parameters() if 'simulator' not in n]
    
    main_optimizer = torch.optim.AdamW([
        {'params': [p for n, p in model.named_parameters() 
                   if 'simulator' not in n and 'polarity' not in n]},
        {'params': model.diffusion.polarity, 'lr': config.polarity_lr}
    ], lr=config.lr, weight_decay=config.weight_decay)
    
    simulator_optimizer = torch.optim.AdamW(
        model.simulator.parameters(), 
        lr=config.simulator_lr
    )
    
    # Training
    print("\n" + "="*70)
    print("TRAINING")
    print("="*70)
    print(f"{'Epoch':>5} | {'Loss':>7} | {'Train':>6} | {'Test':>6} | {'Puzzle':>6} | "
          f"{'g_row':>5} {'g_col':>5} {'g_box':>5} | {'SimLoss':>7} | {'Best':>6}")
    print("-"*95)
    sys.stdout.flush()
    
    best_acc = 0
    
    for epoch in range(config.epochs):
        train_metrics = train_epoch(model, train_loader, main_optimizer, simulator_optimizer, device)
        test_metrics = evaluate(model, test_loader, device)
        
        g = model.diffusion.get_g().detach().cpu()
        
        sim_loss = np.mean(model.stats['simulator_loss']) if model.stats['simulator_loss'] else 0
        
        # TensorBoard
        writer.add_scalar("Loss/main", train_metrics['loss'], epoch)
        writer.add_scalar("Loss/simulator", sim_loss, epoch)
        writer.add_scalar("Accuracy/train_cell", train_metrics['accuracy'], epoch)
        writer.add_scalar("Accuracy/test_cell", test_metrics['cell_accuracy'], epoch)
        writer.add_scalar("Accuracy/test_puzzle", test_metrics['puzzle_accuracy'], epoch)
        writer.add_scalar("Polarity/g_row", g[0].item(), epoch)
        writer.add_scalar("Polarity/g_col", g[1].item(), epoch)
        writer.add_scalar("Polarity/g_box", g[2].item(), epoch)
        writer.add_scalar("Stats/grounding_count", model.stats['grounding_count'], epoch)
        writer.add_scalar("Stats/crystallizations", model.stats['crystallizations'], epoch)
        writer.add_scalar("Stats/evaporations", model.stats['evaporations'], epoch)
        
        is_best = ""
        if test_metrics['puzzle_accuracy'] > best_acc:
            best_acc = test_metrics['puzzle_accuracy']
            is_best = " *"
        
        print(f"{epoch+1:>5} | {train_metrics['loss']:>7.4f} | {train_metrics['accuracy']*100:>5.1f}% | "
              f"{test_metrics['cell_accuracy']*100:>5.1f}% | {test_metrics['puzzle_accuracy']*100:>5.1f}% | "
              f"{g[0]:.3f} {g[1]:.3f} {g[2]:.3f} | {sim_loss:>7.4f} | {best_acc*100:>5.1f}%{is_best}")
        sys.stdout.flush()
        
        model.reset_stats()
    
    writer.close()
    
    # Final test
    print("\n[Final Simulator Test - After Training]")
    run_simulator_test(model, device)
    
    print("\n" + "="*70)
    print(f"FINAL RESULTS")
    print("="*70)
    print(f"Best Puzzle Accuracy: {best_acc*100:.1f}%")
    print(f"Logs saved to: {log_dir}")
    print("="*70)


if __name__ == "__main__":
    main()
