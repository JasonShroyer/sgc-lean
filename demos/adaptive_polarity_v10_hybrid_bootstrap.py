"""
Adaptive Polarity Sheaf Network v10: Hybrid Bootstrap

THEORY (Solving the Cold Start Problem):

THE PROBLEM:
- Untrained physics (SheafDiffusion) is symmetric/isotropic
- Defect(Correct) ≈ Defect(Wrong) when physics is random
- Simulator learns V(s) = const, Planner has no gradient
- This is a Symmetry Breaking failure - stuck in "False Vacuum"

THE SOLUTION: Hybrid Bootstrap
Like biology: evolution (supervision) pre-wires pain circuits (physics)
before the baby (agent) learns to navigate.

PHASE 1: "Build the Walls" (Supervised Physics Pre-training)
- Train SheafDiffusion using v5-style supervision
- Objective: Learn that "Same Numbers on Edge = High Energy"
- After this: Defect(Wrong) >> Defect(Correct)

PHASE 2: "Learn to Navigate" (Planner-Simulator)
- Once physics discriminates, switch to Active Inference
- Simulator learns to predict physics, Planner flows down gradient
- Agent can "close eyes" and simulate the future

WHY THIS IS THEORETICALLY CONSISTENT:
We're not asking the agent to invent gravity - we're giving it gravity
and asking it to learn how to stand. Sudoku rules ARE the physics.
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import DataLoader, TensorDataset
from torch.utils.tensorboard import SummaryWriter
from dataclasses import dataclass
from typing import List, Tuple, Dict, Optional
from collections import deque
import numpy as np
from datetime import datetime
import sys
import random


@dataclass
class HybridBootstrapConfig:
    """Configuration for Hybrid Bootstrap."""
    
    stalk_dim: int = 64
    num_cells: int = 81
    num_digits: int = 9
    
    # Physics
    diffusion_steps: int = 5
    diffusion_dt: float = 0.1
    lookahead_steps: int = 8
    
    # Phase 1: Supervised Pre-training (Build the Walls)
    phase1_epochs: int = 30
    phase1_lr: float = 1e-3
    
    # Phase 2: Planner-Simulator (Learn to Navigate)
    phase2_epochs: int = 70
    phase2_lr: float = 5e-4
    simulator_lr: float = 1e-3
    simulator_hidden: int = 128
    
    # Replay Buffer
    buffer_size: int = 10000
    grounding_freq: int = 4
    simulator_batch: int = 64
    simulator_updates: int = 2
    
    # Confidence dynamics
    alpha_grow_rate: float = 0.15
    alpha_decay_rate: float = 0.25
    crystallize_threshold: float = 0.90
    evaporate_threshold: float = 0.0
    
    # Defect thresholds
    low_defect_threshold: float = -0.001
    high_defect_threshold: float = 0.001
    
    # Cognitive cycles
    max_cycles: int = 4
    
    # Polarity
    polarity_init: float = -0.5
    
    # Training
    batch_size: int = 32
    polarity_lr: float = 0.05
    weight_decay: float = 0.01
    
    # Logging
    log_interval: int = 1
    log_dir: str = "logs/adaptive_polarity_v10"


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
    """Three-Layer State."""
    
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
        return (self.pen == 0) & (self.pencil == 0)


class ReplayBuffer:
    """Experience buffer for grounding."""
    
    def __init__(self, capacity: int):
        self.buffer = deque(maxlen=capacity)
    
    def push(self, state_features: torch.Tensor, cell_idx: int, digit: int, 
             true_defect: torch.Tensor):
        self.buffer.append({
            'state_features': state_features.detach().cpu(),
            'cell_idx': cell_idx,
            'digit': digit,
            'true_defect': true_defect.detach().cpu()
        })
    
    def sample(self, batch_size: int) -> List[Dict]:
        return random.sample(list(self.buffer), min(batch_size, len(self.buffer)))
    
    def __len__(self):
        return len(self.buffer)


class SheafDiffusion(nn.Module):
    """THE PHYSICS (Territory) - learns Sudoku "gravity"."""
    
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
    """THE MAP: Predicts energy landscape."""
    
    def __init__(self, stalk_dim: int, hidden_dim: int):
        super().__init__()
        
        self.state_encoder = nn.Sequential(
            nn.Linear(stalk_dim, hidden_dim),
            nn.ReLU(),
            nn.Linear(hidden_dim, hidden_dim),
        )
        
        self.digit_embed = nn.Embedding(10, hidden_dim)
        
        self.predictor = nn.Sequential(
            nn.Linear(hidden_dim * 2, hidden_dim),
            nn.ReLU(),
            nn.Linear(hidden_dim, hidden_dim),
            nn.ReLU(),
            nn.Linear(hidden_dim, 1)
        )
    
    def forward(self, stalks: torch.Tensor, candidate_cells: torch.Tensor, 
                candidate_digits: torch.Tensor) -> torch.Tensor:
        B, N, D = stalks.shape
        K = candidate_cells.shape[1]
        
        candidate_stalks = torch.gather(
            stalks, 1, 
            candidate_cells.unsqueeze(-1).expand(-1, -1, D)
        )
        state_features = self.state_encoder(candidate_stalks)
        digit_features = self.digit_embed(candidate_digits)
        
        combined = torch.cat([state_features, digit_features], dim=-1)
        predicted_defect = self.predictor(combined).squeeze(-1)
        
        return predicted_defect
    
    def predict_for_all_digits(self, stalks: torch.Tensor, cell_idx: int) -> torch.Tensor:
        B = stalks.shape[0]
        device = stalks.device
        
        candidate_cells = torch.full((B, 9), cell_idx, device=device, dtype=torch.long)
        candidate_digits = torch.arange(1, 10, device=device).unsqueeze(0).expand(B, -1)
        
        return self(stalks, candidate_cells, candidate_digits)


class HybridBootstrapAgent(nn.Module):
    """
    Agent with Hybrid Bootstrap: Pre-train physics, then Planner-Simulator.
    """
    
    def __init__(self, config: HybridBootstrapConfig, edges, edge_types):
        super().__init__()
        self.config = config
        
        # Core network
        self.embed = nn.Embedding(10, config.stalk_dim)
        self.mlp = nn.Sequential(
            nn.Linear(config.stalk_dim, config.stalk_dim * 2),
            nn.ReLU(),
            nn.Linear(config.stalk_dim * 2, config.stalk_dim),
        )
        self.head = nn.Linear(config.stalk_dim, 9)
        
        # Physics (Territory)
        self.diffusion = SheafDiffusion(edges, edge_types, config.stalk_dim, config.polarity_init)
        
        # Simulator (Map)
        self.simulator = WorldSimulator(config.stalk_dim, config.simulator_hidden)
        
        # Replay buffer
        self.replay_buffer = ReplayBuffer(config.buffer_size)
        
        # Mode tracking
        self.phase = 1  # Start in Phase 1
        
        self.stats = {
            'simulator_loss': [],
            'grounding_count': 0,
            'crystallizations': 0,
            'evaporations': 0,
        }
    
    def reset_stats(self):
        self.stats = {
            'simulator_loss': [],
            'grounding_count': 0,
            'crystallizations': 0,
            'evaporations': 0,
        }
    
    def _run_diffusion(self, state: SudokuState, steps: int) -> Tuple[torch.Tensor, torch.Tensor]:
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
    
    @torch.no_grad()
    def compute_true_defect(self, state: SudokuState, conflict_before: torch.Tensor) -> torch.Tensor:
        _, logits_after = self._run_diffusion(
            state, 
            self.config.diffusion_steps + self.config.lookahead_steps
        )
        conflict_after = self.diffusion.compute_local_conflict(logits_after)
        return conflict_after - conflict_before
    
    # ========== PHASE 1: Supervised Pre-training ==========
    
    def forward_phase1(self, puzzles: torch.Tensor, solutions: torch.Tensor) -> torch.Tensor:
        """
        Phase 1: Standard supervised learning to build the "walls".
        This teaches the physics that "same numbers on edge = high energy".
        """
        state = SudokuState(puzzles, solutions)
        stalks, logits = self._run_diffusion(state, self.config.diffusion_steps)
        return logits
    
    # ========== PHASE 2: Planner-Simulator ==========
    
    def plan_action(self, stalks: torch.Tensor, state: SudokuState) -> Tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
        """Select best action using Simulator predictions."""
        B = stalks.shape[0]
        device = stalks.device
        
        empty = state.get_empty_cells()
        
        best_cells = torch.zeros(B, dtype=torch.long, device=device)
        best_digits = torch.zeros(B, dtype=torch.long, device=device)
        best_defects = torch.full((B,), float('inf'), device=device)
        
        for cell_idx in range(81):
            cell_empty = empty[:, cell_idx]
            if not cell_empty.any():
                continue
            
            predicted = self.simulator.predict_for_all_digits(stalks, cell_idx)
            min_defect, min_digit_idx = predicted.min(dim=1)
            min_digit = min_digit_idx + 1
            
            better = cell_empty & (min_defect < best_defects)
            best_cells[better] = cell_idx
            best_digits[better] = min_digit[better]
            best_defects[better] = min_defect[better]
        
        return best_cells, best_digits, best_defects
    
    def ground_simulator(self, state: SudokuState, stalks: torch.Tensor,
                         cell_idx: int, digit: int, conflict_before: torch.Tensor):
        """Run physics and store for Simulator training."""
        temp_state = SudokuState(state.pen.clone(), state.solutions)
        temp_state.pencil = state.pencil.clone()
        temp_state.alpha = state.alpha.clone()
        temp_state.pencil[:, cell_idx] = digit
        temp_state.alpha[:, cell_idx] = 0.5
        
        true_defect = self.compute_true_defect(temp_state, conflict_before)
        
        for b in range(stalks.shape[0]):
            self.replay_buffer.push(
                stalks[b], cell_idx, digit, true_defect[b, cell_idx]
            )
        
        self.stats['grounding_count'] += 1
        return true_defect[:, cell_idx]
    
    def train_simulator(self, optimizer):
        """Update Simulator from replay buffer."""
        if len(self.replay_buffer) < self.config.simulator_batch:
            return 0.0
        
        total_loss = 0.0
        
        for _ in range(self.config.simulator_updates):
            batch = self.replay_buffer.sample(self.config.simulator_batch)
            
            device = next(self.parameters()).device
            
            state_features = torch.stack([b['state_features'] for b in batch]).to(device)
            cell_indices = torch.tensor([b['cell_idx'] for b in batch], dtype=torch.long).to(device)
            digits = torch.tensor([b['digit'] for b in batch], dtype=torch.long).to(device)
            true_defects = torch.tensor([b['true_defect'] for b in batch], dtype=torch.float).to(device)
            
            predicted = self.simulator(
                state_features,
                cell_indices.unsqueeze(-1),
                digits.unsqueeze(-1)
            ).squeeze(-1)
            
            loss = F.mse_loss(predicted, true_defects)
            
            optimizer.zero_grad()
            loss.backward()
            optimizer.step()
            
            total_loss += loss.item()
            self.stats['simulator_loss'].append(loss.item())
        
        return total_loss / self.config.simulator_updates
    
    def forward_phase2(self, puzzles: torch.Tensor, solutions: torch.Tensor,
                       simulator_optimizer=None) -> Tuple[torch.Tensor, Dict]:
        """
        Phase 2: Planner-Simulator with grounding.
        """
        state = SudokuState(puzzles, solutions)
        config = self.config
        
        agg_stats = {'cycles': 0, 'written': 0, 'crystallized': 0, 'evaporated': 0}
        
        for cycle in range(config.max_cycles):
            stalks, logits = self._run_diffusion(state, config.diffusion_steps)
            conflict = self.diffusion.compute_local_conflict(logits)
            
            # Plan action
            best_cells, best_digits, predicted_defects = self.plan_action(stalks, state)
            
            # Grounding
            if cycle % config.grounding_freq == 0 and simulator_optimizer is not None:
                for b in range(stalks.shape[0]):
                    if state.get_empty_cells()[b].any() and best_digits[b] > 0:
                        self.ground_simulator(
                            state, stalks[b:b+1], 
                            best_cells[b].item(), best_digits[b].item(), 
                            conflict[b:b+1]
                        )
                self.train_simulator(simulator_optimizer)
            
            # Execute action
            for b in range(stalks.shape[0]):
                if best_digits[b] > 0:
                    cell = best_cells[b].item()
                    if state.get_empty_cells()[b, cell]:
                        state.pencil[b, cell] = best_digits[b]
                        state.alpha[b, cell] = 0.1
                        agg_stats['written'] += 1
            
            # Update confidence
            has_pencil = (state.pencil > 0)
            
            for b in range(stalks.shape[0]):
                pencil_cells = has_pencil[b].nonzero(as_tuple=True)[0]
                for cell in pencil_cells:
                    cell_idx = cell.item()
                    digit = state.pencil[b, cell_idx].item()
                    
                    pred = self.simulator.predict_for_all_digits(stalks[b:b+1], cell_idx)
                    pred_defect = pred[0, digit - 1].item()
                    
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
                agg_stats['evaporated'] += evaporate_mask.sum().item()
                self.stats['evaporations'] += evaporate_mask.sum().item()
            
            crystallize_mask = (state.alpha > config.crystallize_threshold) & (state.pencil > 0)
            if crystallize_mask.any():
                state.pen[crystallize_mask] = state.pencil[crystallize_mask]
                state.pencil[crystallize_mask] = 0
                state.alpha[crystallize_mask] = 0.0
                agg_stats['crystallized'] += crystallize_mask.sum().item()
                self.stats['crystallizations'] += crystallize_mask.sum().item()
            
            agg_stats['cycles'] += 1
            
            if (state.pen > 0).all():
                break
        
        return logits, agg_stats


# === DATA GENERATION ===

def generate_puzzles(n: int, clues: int = 30) -> Tuple[torch.Tensor, torch.Tensor]:
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

def train_phase1_epoch(model: HybridBootstrapAgent, loader: DataLoader, 
                       optimizer, device) -> Dict:
    """Phase 1: Supervised pre-training to build physics."""
    model.train()
    total_loss = 0
    total_correct = 0
    total_cells = 0
    
    for puzzles, solutions in loader:
        puzzles = puzzles.to(device)
        solutions = solutions.to(device)
        
        optimizer.zero_grad()
        
        logits = model.forward_phase1(puzzles, solutions)
        
        loss = F.cross_entropy(
            logits.view(-1, 9),
            (solutions - 1).view(-1)
        )
        
        loss.backward()
        optimizer.step()
        
        total_loss += loss.item() * puzzles.size(0)
        
        preds = logits.argmax(dim=-1) + 1
        total_correct += (preds == solutions).sum().item()
        total_cells += solutions.numel()
    
    return {
        'loss': total_loss / len(loader.dataset),
        'accuracy': total_correct / total_cells
    }


def train_phase2_epoch(model: HybridBootstrapAgent, loader: DataLoader,
                       main_optimizer, simulator_optimizer, device) -> Dict:
    """Phase 2: Planner-Simulator training."""
    model.train()
    total_loss = 0
    total_correct = 0
    total_cells = 0
    
    for puzzles, solutions in loader:
        puzzles = puzzles.to(device)
        solutions = solutions.to(device)
        
        main_optimizer.zero_grad()
        
        logits, stats = model.forward_phase2(puzzles, solutions, simulator_optimizer)
        
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


def evaluate(model: HybridBootstrapAgent, loader: DataLoader, device) -> Dict:
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
            
            if model.phase == 1:
                logits = model.forward_phase1(puzzles, solutions)
            else:
                logits, _ = model.forward_phase2(puzzles, solutions, simulator_optimizer=None)
            
            preds = logits.argmax(dim=-1) + 1
            total_correct += (preds == solutions).sum().item()
            total_cells += solutions.numel()
            
            puzzle_correct += (preds == solutions).all(dim=1).sum().item()
            total_puzzles += puzzles.size(0)
    
    return {
        'cell_accuracy': total_correct / total_cells,
        'puzzle_accuracy': puzzle_correct / total_puzzles,
    }


def test_physics_discrimination(model: HybridBootstrapAgent, device):
    """
    Test if physics discriminates between correct and wrong.
    This MUST pass before switching to Phase 2.
    """
    print("\n" + "="*60)
    print("PHYSICS DISCRIMINATION TEST")
    print("="*60)
    
    model.eval()
    
    puzzles, solutions = generate_puzzles(10, clues=35)
    puzzles = puzzles.to(device)
    solutions = solutions.to(device)
    
    correct_defects = []
    wrong_defects = []
    
    for i in range(10):
        puzzle = puzzles[i:i+1]
        solution = solutions[i:i+1]
        
        empty_cells = (puzzle[0] == 0).nonzero(as_tuple=True)[0]
        if len(empty_cells) == 0:
            continue
        
        test_cell = empty_cells[0].item()
        correct_digit = solution[0, test_cell].item()
        wrong_digit = (correct_digit % 9) + 1
        
        state = SudokuState(puzzle, solution)
        
        with torch.no_grad():
            stalks, logits = model._run_diffusion(state, model.config.diffusion_steps)
            conflict_before = model.diffusion.compute_local_conflict(logits)
        
        # Test correct
        state_c = SudokuState(puzzle.clone(), solution)
        state_c.pencil[0, test_cell] = correct_digit
        state_c.alpha[0, test_cell] = 0.5
        
        with torch.no_grad():
            defect_c = model.compute_true_defect(state_c, conflict_before)
            correct_defects.append(defect_c[0, test_cell].item())
        
        # Test wrong
        state_w = SudokuState(puzzle.clone(), solution)
        state_w.pencil[0, test_cell] = wrong_digit
        state_w.alpha[0, test_cell] = 0.5
        
        with torch.no_grad():
            defect_w = model.compute_true_defect(state_w, conflict_before)
            wrong_defects.append(defect_w[0, test_cell].item())
    
    mean_correct = np.mean(correct_defects)
    mean_wrong = np.mean(wrong_defects)
    
    print(f"\nMean Defect (Correct): {mean_correct:.6f}")
    print(f"Mean Defect (Wrong):   {mean_wrong:.6f}")
    print(f"Difference:            {mean_wrong - mean_correct:.6f}")
    
    # Check if wrong is significantly higher than correct
    discrimination = mean_wrong > mean_correct + 0.001
    
    if discrimination:
        print("\n[PASS] Physics discriminates! Defect(Wrong) >> Defect(Correct)")
    else:
        print("\n[FAIL] Physics does NOT discriminate. Continue Phase 1.")
    
    print("="*60)
    return discrimination


def main():
    print("="*70)
    print("Adaptive Polarity v10: Hybrid Bootstrap")
    print("="*70)
    print("\nSolving the Cold Start Problem:")
    print("Phase 1: Supervised pre-training (Build the Walls)")
    print("Phase 2: Planner-Simulator (Learn to Navigate)")
    print("="*70)
    
    device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
    print(f"\nDevice: {device}")
    
    config = HybridBootstrapConfig()
    edges, edge_types = build_sudoku_graph()
    
    model = HybridBootstrapAgent(config, edges, edge_types).to(device)
    
    # TensorBoard
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_dir = f"{config.log_dir}/{timestamp}"
    writer = SummaryWriter(log_dir)
    print(f"\nTensorBoard logs: {log_dir}")
    
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
    
    # Initial test
    print("\n[Initial Physics Test - Before Phase 1]")
    test_physics_discrimination(model, device)
    
    # ========== PHASE 1: BUILD THE WALLS ==========
    print("\n" + "="*70)
    print("PHASE 1: Supervised Pre-training (Build the Walls)")
    print("="*70)
    print(f"{'Epoch':>5} | {'Loss':>7} | {'Train':>6} | {'Test':>6} | {'Puzzle':>6} | {'g_row':>5} {'g_col':>5} {'g_box':>5}")
    print("-"*70)
    sys.stdout.flush()
    
    phase1_optimizer = torch.optim.AdamW([
        {'params': [p for n, p in model.named_parameters() 
                   if 'simulator' not in n and 'polarity' not in n]},
        {'params': model.diffusion.polarity, 'lr': config.polarity_lr}
    ], lr=config.phase1_lr, weight_decay=config.weight_decay)
    
    best_phase1_acc = 0
    
    for epoch in range(config.phase1_epochs):
        train_metrics = train_phase1_epoch(model, train_loader, phase1_optimizer, device)
        test_metrics = evaluate(model, test_loader, device)
        
        g = model.diffusion.get_g().detach().cpu()
        
        writer.add_scalar("Phase1/Loss", train_metrics['loss'], epoch)
        writer.add_scalar("Phase1/TrainAcc", train_metrics['accuracy'], epoch)
        writer.add_scalar("Phase1/TestAcc", test_metrics['cell_accuracy'], epoch)
        writer.add_scalar("Phase1/PuzzleAcc", test_metrics['puzzle_accuracy'], epoch)
        
        is_best = ""
        if test_metrics['puzzle_accuracy'] > best_phase1_acc:
            best_phase1_acc = test_metrics['puzzle_accuracy']
            is_best = " *"
        
        print(f"{epoch+1:>5} | {train_metrics['loss']:>7.4f} | {train_metrics['accuracy']*100:>5.1f}% | "
              f"{test_metrics['cell_accuracy']*100:>5.1f}% | {test_metrics['puzzle_accuracy']*100:>5.1f}% | "
              f"{g[0]:.3f} {g[1]:.3f} {g[2]:.3f}{is_best}")
        sys.stdout.flush()
    
    print(f"\nPhase 1 Complete. Best Puzzle Accuracy: {best_phase1_acc*100:.1f}%")
    
    # Test physics discrimination after Phase 1
    print("\n[Physics Test - After Phase 1]")
    physics_ok = test_physics_discrimination(model, device)
    
    if not physics_ok:
        print("\n[WARNING] Physics still doesn't discriminate. Consider more Phase 1 epochs.")
    
    # ========== PHASE 2: LEARN TO NAVIGATE ==========
    print("\n" + "="*70)
    print("PHASE 2: Planner-Simulator (Learn to Navigate)")
    print("="*70)
    
    model.phase = 2
    
    print(f"{'Epoch':>5} | {'Loss':>7} | {'Train':>6} | {'Test':>6} | {'Puzzle':>6} | "
          f"{'g_row':>5} {'g_col':>5} {'g_box':>5} | {'SimLoss':>7} | {'Best':>6}")
    print("-"*95)
    sys.stdout.flush()
    
    phase2_optimizer = torch.optim.AdamW([
        {'params': [p for n, p in model.named_parameters() 
                   if 'simulator' not in n and 'polarity' not in n]},
        {'params': model.diffusion.polarity, 'lr': config.polarity_lr * 0.5}
    ], lr=config.phase2_lr, weight_decay=config.weight_decay)
    
    simulator_optimizer = torch.optim.AdamW(
        model.simulator.parameters(), 
        lr=config.simulator_lr
    )
    
    best_phase2_acc = best_phase1_acc
    
    for epoch in range(config.phase2_epochs):
        train_metrics = train_phase2_epoch(model, train_loader, phase2_optimizer, simulator_optimizer, device)
        test_metrics = evaluate(model, test_loader, device)
        
        g = model.diffusion.get_g().detach().cpu()
        sim_loss = np.mean(model.stats['simulator_loss']) if model.stats['simulator_loss'] else 0
        
        writer.add_scalar("Phase2/Loss", train_metrics['loss'], epoch)
        writer.add_scalar("Phase2/TrainAcc", train_metrics['accuracy'], epoch)
        writer.add_scalar("Phase2/TestAcc", test_metrics['cell_accuracy'], epoch)
        writer.add_scalar("Phase2/PuzzleAcc", test_metrics['puzzle_accuracy'], epoch)
        writer.add_scalar("Phase2/SimulatorLoss", sim_loss, epoch)
        
        is_best = ""
        if test_metrics['puzzle_accuracy'] > best_phase2_acc:
            best_phase2_acc = test_metrics['puzzle_accuracy']
            is_best = " *"
        
        print(f"{epoch+1:>5} | {train_metrics['loss']:>7.4f} | {train_metrics['accuracy']*100:>5.1f}% | "
              f"{test_metrics['cell_accuracy']*100:>5.1f}% | {test_metrics['puzzle_accuracy']*100:>5.1f}% | "
              f"{g[0]:.3f} {g[1]:.3f} {g[2]:.3f} | {sim_loss:>7.4f} | {best_phase2_acc*100:>5.1f}%{is_best}")
        sys.stdout.flush()
        
        model.reset_stats()
    
    writer.close()
    
    # Final physics test
    print("\n[Final Physics Test - After Phase 2]")
    test_physics_discrimination(model, device)
    
    print("\n" + "="*70)
    print("FINAL RESULTS")
    print("="*70)
    print(f"Phase 1 Best: {best_phase1_acc*100:.1f}%")
    print(f"Phase 2 Best: {best_phase2_acc*100:.1f}%")
    print(f"Logs saved to: {log_dir}")
    print("="*70)


if __name__ == "__main__":
    main()
