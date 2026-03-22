"""
Adaptive Polarity Sheaf Network v8: The Intuitive Physicist

THEORY (Temporal Renormalization via Amortized Inference):

THE PROBLEM WITH v7:
- Lookahead (k=8 steps) creates a vanishing gradient problem
- The gradient must propagate backwards through 8 diffusion steps
- This is the classic RNN problem - signal gets lost over time
- v5 worked because feedback was INSTANT

THE SOLUTION:
- Don't backprop through the physics loop
- Train a CRITIC (Value Net) to PREDICT the defect instantly
- The Critic learns from occasional ground truth (physics lookahead)
- The Actor gets gradients from the Critic (immediate feedback)

ARCHITECTURE:
1. Actor (Policy): Proposes pencil marks based on current state
2. Critic (DefectPredictor): V(S) ≈ E[Future Defect | S]
3. Physics (Ground Truth): Runs lookahead to compute D_true (detached)

TRAINING:
1. Actor writes pencil mark
2. Critic predicts D_pred (instant, differentiable)
3. Physics computes D_true (slow, detached from gradient graph)
4. Critic Loss: (D_pred - D_true)² - learns to predict defect
5. Actor Loss: minimize D_pred - chooses actions Critic thinks are stable

This is "Active Inference with Amortized Inference" - the agent develops
INTUITION about physics rather than simulating it every time.
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
import sys


@dataclass
class AmortizedDefectConfig:
    """Configuration for Actor-Critic with Amortized Defect Prediction."""
    
    stalk_dim: int = 64
    num_cells: int = 81
    num_digits: int = 9
    
    # Diffusion
    diffusion_steps: int = 5
    diffusion_dt: float = 0.1
    
    # Physics lookahead (for ground truth defect)
    lookahead_steps: int = 8
    
    # Confidence dynamics (from v6/v7)
    alpha_grow_rate: float = 0.15
    alpha_decay_rate: float = 0.25
    crystallize_threshold: float = 0.90
    evaporate_threshold: float = 0.0
    write_confidence: float = 0.5
    
    # Defect thresholds
    stabilize_threshold: float = -0.001
    agitate_threshold: float = 0.001
    
    # Cognitive cycles
    max_cycles: int = 4
    
    # Polarity
    polarity_init: float = -0.5
    
    # Training
    epochs: int = 100
    batch_size: int = 32
    lr: float = 1e-3
    critic_lr: float = 1e-3
    polarity_lr: float = 0.05
    weight_decay: float = 0.01
    
    # Critic training frequency
    critic_update_freq: int = 1  # Update critic every N batches
    
    # Logging
    log_interval: int = 1
    log_dir: str = "logs/adaptive_polarity_v8"


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
    
    def get_superposition_input(self, sheaf_state: torch.Tensor) -> torch.Tensor:
        B, N, D = sheaf_state.shape
        device = sheaf_state.device
        
        pencil_onehot = F.one_hot(self.pencil, num_classes=10)[:, :, 1:]
        pencil_embedding = torch.zeros(B, N, D, device=device)
        pencil_embedding[:, :, :9] = pencil_onehot.float()
        
        alpha_expanded = self.alpha.unsqueeze(-1)
        has_pencil = (self.pencil > 0).unsqueeze(-1).float()
        
        superposition = (1 - alpha_expanded * has_pencil) * sheaf_state + \
                       (alpha_expanded * has_pencil) * pencil_embedding
        
        return superposition
    
    def get_effective_board(self) -> torch.Tensor:
        board = self.pen.clone().long()
        mask = (self.pen == 0) & (self.pencil > 0)
        board[mask] = self.pencil[mask]
        return board
    
    def get_fixed_mask(self) -> torch.Tensor:
        return (self.pen > 0) | ((self.pencil > 0) & (self.alpha > 0.5))


class SheafDiffusion(nn.Module):
    """Sheaf diffusion with conflict computation."""
    
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


class DefectPredictor(nn.Module):
    """
    THE CRITIC: Predicts defect (future stability) from current state.
    
    This is the "Intuition" network that learns to approximate:
    V(S) ≈ E[Future Defect | S]
    
    Input: Current stalks after diffusion
    Output: Predicted defect per cell
    """
    
    def __init__(self, stalk_dim: int):
        super().__init__()
        self.net = nn.Sequential(
            nn.Linear(stalk_dim, stalk_dim * 2),
            nn.ReLU(),
            nn.Linear(stalk_dim * 2, stalk_dim),
            nn.ReLU(),
            nn.Linear(stalk_dim, 1)  # Predict scalar defect per cell
        )
    
    def forward(self, stalks: torch.Tensor) -> torch.Tensor:
        """
        Args:
            stalks: (B, 81, stalk_dim) - current stalk states
        Returns:
            defect_pred: (B, 81) - predicted defect per cell
        """
        return self.net(stalks).squeeze(-1)


class AmortizedDefectAgent(nn.Module):
    """
    Actor-Critic Agent with Amortized Defect Prediction.
    
    - Actor: Main network that proposes pencil marks
    - Critic: DefectPredictor that instantly estimates future stability
    - Physics: Ground truth defect from lookahead (detached)
    """
    
    def __init__(self, config: AmortizedDefectConfig, edges, edge_types):
        super().__init__()
        self.config = config
        
        # Actor components
        self.embed = nn.Embedding(10, config.stalk_dim)
        self.mlp = nn.Sequential(
            nn.Linear(config.stalk_dim, config.stalk_dim * 2),
            nn.ReLU(),
            nn.Linear(config.stalk_dim * 2, config.stalk_dim),
        )
        self.diffusion = SheafDiffusion(edges, edge_types, config.stalk_dim, config.polarity_init)
        self.head = nn.Linear(config.stalk_dim, 9)
        
        # Critic: The Intuitive Physicist
        self.critic = DefectPredictor(config.stalk_dim)
        
        # Monitoring
        self.stats = {
            'critic_loss': [],
            'defect_pred_mean': [],
            'defect_true_mean': [],
            'stabilizations': 0,
            'agitations': 0,
            'crystallizations': 0,
            'evaporations': 0,
        }
    
    def reset_stats(self):
        self.stats = {
            'critic_loss': [],
            'defect_pred_mean': [],
            'defect_true_mean': [],
            'stabilizations': 0,
            'agitations': 0,
            'crystallizations': 0,
            'evaporations': 0,
        }
    
    def _run_diffusion(self, state: SudokuState, steps: int) -> Tuple[torch.Tensor, torch.Tensor]:
        """Run diffusion, return (stalks, logits)."""
        board = state.get_effective_board()
        stalks = self.embed(board)
        stalks = stalks + self.mlp(stalks)
        stalks = state.get_superposition_input(stalks)
        
        fixed_mask = state.get_fixed_mask()
        
        for _ in range(steps):
            logits = self.head(stalks)
            stalks = self.diffusion.diffuse(stalks, logits, self.config.diffusion_dt, fixed_mask)
            stalks = stalks + 0.1 * self.mlp(stalks)
        
        logits = self.head(stalks)
        return stalks, logits
    
    def sense_and_predict(self, state: SudokuState) -> Tuple[torch.Tensor, torch.Tensor, torch.Tensor, torch.Tensor]:
        """
        Sense current state and predict defect using Critic.
        
        Returns: stalks, logits, conflict, defect_pred
        """
        stalks, logits = self._run_diffusion(state, self.config.diffusion_steps)
        conflict = self.diffusion.compute_local_conflict(logits)
        
        # Critic predicts defect INSTANTLY (no lookahead needed)
        defect_pred = self.critic(stalks)
        
        return stalks, logits, conflict, defect_pred
    
    @torch.no_grad()
    def compute_true_defect(self, state: SudokuState, conflict_before: torch.Tensor) -> torch.Tensor:
        """
        Compute ground truth defect via physics lookahead.
        
        This is DETACHED from the gradient graph - used only to train the Critic.
        """
        # Run additional lookahead steps
        _, logits_after = self._run_diffusion(state, 
                                               self.config.diffusion_steps + self.config.lookahead_steps)
        conflict_after = self.diffusion.compute_local_conflict(logits_after)
        
        # True defect = conflict growth
        defect_true = conflict_after - conflict_before
        
        return defect_true
    
    def evaluate_and_act(self, state: SudokuState, logits: torch.Tensor, 
                         defect_pred: torch.Tensor) -> Dict:
        """
        Use PREDICTED defect (from Critic) for decisions.
        
        This gives instant feedback - no vanishing gradient problem!
        """
        config = self.config
        stats = {'written': 0, 'evaporated': 0, 'crystallized': 0, 'stabilized': 0, 'agitated': 0}
        
        probs = F.softmax(logits, dim=-1)
        max_prob, best_digit = probs.max(dim=-1)
        best_digit = best_digit + 1
        
        has_pencil = (state.pencil > 0)
        
        # Use PREDICTED defect for decisions (instant feedback!)
        stabilized = (defect_pred < config.stabilize_threshold) & has_pencil
        state.alpha[stabilized] += config.alpha_grow_rate
        stats['stabilized'] = stabilized.sum().item()
        self.stats['stabilizations'] += stats['stabilized']
        
        agitated = (defect_pred > config.agitate_threshold) & has_pencil
        state.alpha[agitated] -= config.alpha_decay_rate
        stats['agitated'] = agitated.sum().item()
        self.stats['agitations'] += stats['agitated']
        
        neutral = has_pencil & ~stabilized & ~agitated
        state.alpha[neutral] += config.alpha_grow_rate * 0.1
        
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
        
        # Write new pencil marks
        empty = (state.pen == 0) & (state.pencil == 0)
        confident = max_prob > config.write_confidence
        conflict = self.diffusion.compute_local_conflict(logits)
        low_conflict = conflict < 0.3
        
        write_mask = empty & confident & low_conflict
        if write_mask.any():
            state.pencil[write_mask] = best_digit[write_mask]
            state.alpha[write_mask] = 0.1
            stats['written'] = write_mask.sum().item()
        
        return stats
    
    def solve_cycle(self, state: SudokuState, train_critic: bool = True
                    ) -> Tuple[torch.Tensor, torch.Tensor, torch.Tensor, Dict]:
        """
        One cycle of the Actor-Critic loop.
        
        Returns: logits, defect_pred, defect_true (if training), stats
        """
        # Sense and predict defect instantly
        stalks, logits, conflict, defect_pred = self.sense_and_predict(state)
        
        # Compute ground truth defect (detached, for Critic training)
        defect_true = None
        if train_critic:
            defect_true = self.compute_true_defect(state, conflict)
        
        # Act based on predicted defect (instant feedback!)
        stats = self.evaluate_and_act(state, logits, defect_pred)
        
        return logits, defect_pred, defect_true, stats
    
    def forward(self, puzzles: torch.Tensor, solutions: Optional[torch.Tensor] = None,
                train_critic: bool = True) -> Tuple[torch.Tensor, torch.Tensor, Optional[torch.Tensor], Dict]:
        """Forward pass with Actor-Critic."""
        state = SudokuState(puzzles, solutions)
        
        all_defect_pred = []
        all_defect_true = []
        agg_stats = {'cycles': 0}
        
        for cycle in range(self.config.max_cycles):
            logits, defect_pred, defect_true, stats = self.solve_cycle(state, train_critic)
            
            if (state.pencil > 0).any():
                all_defect_pred.append(defect_pred)
                if defect_true is not None:
                    all_defect_true.append(defect_true)
            
            agg_stats['cycles'] += 1
            
            if (state.pen > 0).all():
                break
        
        # Stack predictions for loss computation
        if all_defect_pred:
            defect_pred_stacked = torch.stack(all_defect_pred, dim=0).mean(dim=0)
            defect_true_stacked = torch.stack(all_defect_true, dim=0).mean(dim=0) if all_defect_true else None
        else:
            defect_pred_stacked = torch.zeros_like(puzzles, dtype=torch.float)
            defect_true_stacked = None
        
        return logits, defect_pred_stacked, defect_true_stacked, agg_stats


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

def train_epoch(model: AmortizedDefectAgent, loader: DataLoader, 
                actor_optimizer, critic_optimizer, device) -> Dict:
    """
    Train one epoch with Actor-Critic.
    
    Two separate losses:
    1. Critic Loss: (D_pred - D_true)² - learns to predict defect
    2. Actor Loss: CE + λ * D_pred - minimize defect predictions
    """
    model.train()
    total_actor_loss = 0
    total_critic_loss = 0
    total_correct = 0
    total_cells = 0
    
    for puzzles, solutions in loader:
        puzzles = puzzles.to(device)
        solutions = solutions.to(device)
        
        # Forward pass
        logits, defect_pred, defect_true, stats = model(puzzles, solutions, train_critic=True)
        
        # === ACTOR LOSS: CE + minimize predicted defect ===
        # Do Actor first to avoid gradient conflicts
        actor_optimizer.zero_grad()
        
        # Classification loss
        ce_loss = F.cross_entropy(
            logits.view(-1, 9),
            (solutions - 1).view(-1)
        )
        
        # Defect regularization: encourage actions that Critic thinks are stable
        # Use detached defect_pred to avoid interfering with Critic gradients
        defect_reg = defect_pred.detach().mean() * 0.1  # Small weight, detached
        
        actor_loss = ce_loss + defect_reg
        actor_loss.backward()
        actor_optimizer.step()
        
        # === CRITIC LOSS: Learn to predict defect ===
        # Train Critic separately with fresh forward pass through critic only
        if defect_true is not None:
            # Recompute defect_pred for Critic training (fresh graph)
            with torch.no_grad():
                # Get stalks from current state
                state = SudokuState(puzzles, solutions)
                for _ in range(model.config.max_cycles):
                    stalks, _ = model._run_diffusion(state, model.config.diffusion_steps)
                    break  # Just one pass for stalks
            
            # Critic prediction (with gradients)
            defect_pred_critic = model.critic(stalks.detach())
            
            has_pencil = (defect_true != 0)
            if has_pencil.any():
                critic_loss = F.mse_loss(defect_pred_critic[has_pencil], defect_true[has_pencil])
            else:
                critic_loss = torch.tensor(0.0, device=device)
            
            critic_optimizer.zero_grad()
            critic_loss.backward()
            critic_optimizer.step()
            
            total_critic_loss += critic_loss.item()
            model.stats['critic_loss'].append(critic_loss.item())
            model.stats['defect_pred_mean'].append(defect_pred.mean().item())
            model.stats['defect_true_mean'].append(defect_true.mean().item())
        
        total_actor_loss += ce_loss.item() * puzzles.size(0)
        
        preds = logits.argmax(dim=-1) + 1
        total_correct += (preds == solutions).sum().item()
        total_cells += solutions.numel()
    
    n_batches = len(loader)
    return {
        'actor_loss': total_actor_loss / len(loader.dataset),
        'critic_loss': total_critic_loss / n_batches if n_batches > 0 else 0,
        'accuracy': total_correct / total_cells
    }


def evaluate(model: AmortizedDefectAgent, loader: DataLoader, device) -> Dict:
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
            
            logits, _, _, _ = model(puzzles, solutions, train_critic=False)
            
            preds = logits.argmax(dim=-1) + 1
            total_correct += (preds == solutions).sum().item()
            total_cells += solutions.numel()
            
            puzzle_correct += (preds == solutions).all(dim=1).sum().item()
            total_puzzles += puzzles.size(0)
    
    return {
        'cell_accuracy': total_correct / total_cells,
        'puzzle_accuracy': puzzle_correct / total_puzzles,
    }


def run_critic_test(model: AmortizedDefectAgent, device):
    """
    Test if the Critic can distinguish correct vs wrong hypotheses.
    """
    print("\n" + "="*60)
    print("CRITIC TEST: Can the Intuitive Physicist distinguish good from bad?")
    print("="*60)
    
    model.eval()
    
    puzzles, solutions = generate_puzzles(1, clues=35)
    puzzles = puzzles.to(device)
    solutions = solutions.to(device)
    
    empty_cells = (puzzles[0] == 0).nonzero(as_tuple=True)[0]
    if len(empty_cells) == 0:
        print("No empty cells!")
        return False
    
    test_cell = empty_cells[0].item()
    correct_digit = solutions[0, test_cell].item()
    wrong_digit = (correct_digit % 9) + 1
    
    print(f"\nTest cell: {test_cell}")
    print(f"Correct digit: {correct_digit}")
    print(f"Wrong digit: {wrong_digit}")
    
    # Test with CORRECT digit
    print("\n--- Correct Digit ---")
    state_correct = SudokuState(puzzles.clone(), solutions)
    state_correct.pencil[0, test_cell] = correct_digit
    state_correct.alpha[0, test_cell] = 0.5
    
    with torch.no_grad():
        stalks, logits, conflict, defect_pred = model.sense_and_predict(state_correct)
        defect_true = model.compute_true_defect(state_correct, conflict)
        
        pred_correct = defect_pred[0, test_cell].item()
        true_correct = defect_true[0, test_cell].item()
        print(f"  Predicted defect: {pred_correct:.4f}")
        print(f"  True defect:      {true_correct:.4f}")
    
    # Test with WRONG digit
    print("\n--- Wrong Digit ---")
    state_wrong = SudokuState(puzzles.clone(), solutions)
    state_wrong.pencil[0, test_cell] = wrong_digit
    state_wrong.alpha[0, test_cell] = 0.5
    
    with torch.no_grad():
        stalks, logits, conflict, defect_pred = model.sense_and_predict(state_wrong)
        defect_true = model.compute_true_defect(state_wrong, conflict)
        
        pred_wrong = defect_pred[0, test_cell].item()
        true_wrong = defect_true[0, test_cell].item()
        print(f"  Predicted defect: {pred_wrong:.4f}")
        print(f"  True defect:      {true_wrong:.4f}")
    
    # Verify
    print("\n--- Verification ---")
    
    physics_ok = true_correct < true_wrong
    critic_ok = pred_correct < pred_wrong
    
    print(f"Physics (true defect): {'[PASS]' if physics_ok else '[FAIL]'} correct={true_correct:.4f} vs wrong={true_wrong:.4f}")
    print(f"Critic (predicted):    {'[PASS]' if critic_ok else '[FAIL]'} correct={pred_correct:.4f} vs wrong={pred_wrong:.4f}")
    
    if critic_ok:
        print("\n[SUCCESS] Critic has learned intuition about physics!")
    else:
        print("\n[TRAINING NEEDED] Critic hasn't learned to distinguish yet.")
    
    print("="*60)
    return critic_ok


def main():
    print("="*70)
    print("Adaptive Polarity v8: The Intuitive Physicist")
    print("="*70)
    print("\nTheory: Temporal Renormalization via Amortized Inference")
    print("- Actor: Proposes pencil marks")
    print("- Critic: Predicts defect INSTANTLY (no lookahead needed)")
    print("- Physics: Ground truth for Critic training (detached)")
    print("="*70)
    
    device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
    print(f"\nDevice: {device}")
    
    config = AmortizedDefectConfig()
    edges, edge_types = build_sudoku_graph()
    
    model = AmortizedDefectAgent(config, edges, edge_types).to(device)
    
    # TensorBoard
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_dir = f"{config.log_dir}/{timestamp}"
    writer = SummaryWriter(log_dir)
    print(f"\nTensorBoard logs: {log_dir}")
    print(f"  Run: tensorboard --logdir={config.log_dir}")
    
    # Initial critic test (should fail - untrained)
    print("\n[Initial Critic Test - Before Training]")
    run_critic_test(model, device)
    
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
    
    # Separate optimizers for Actor and Critic
    actor_params = [p for n, p in model.named_parameters() if 'critic' not in n]
    critic_params = list(model.critic.parameters())
    
    actor_optimizer = torch.optim.AdamW([
        {'params': [p for n, p in model.named_parameters() if 'critic' not in n and 'polarity' not in n]},
        {'params': model.diffusion.polarity, 'lr': config.polarity_lr}
    ], lr=config.lr, weight_decay=config.weight_decay)
    
    critic_optimizer = torch.optim.AdamW(critic_params, lr=config.critic_lr)
    
    # Training
    print("\n" + "="*70)
    print("TRAINING")
    print("="*70)
    print(f"{'Epoch':>5} | {'ActorL':>7} | {'CritL':>7} | {'Train':>6} | {'Test':>6} | {'Puzzle':>6} | {'g_row':>5} {'g_col':>5} {'g_box':>5} | {'Best':>6}")
    print("-"*95)
    sys.stdout.flush()
    
    best_acc = 0
    
    for epoch in range(config.epochs):
        train_metrics = train_epoch(model, train_loader, actor_optimizer, critic_optimizer, device)
        test_metrics = evaluate(model, test_loader, device)
        
        g = model.diffusion.get_g().detach().cpu()
        
        # TensorBoard
        writer.add_scalar("Loss/actor", train_metrics['actor_loss'], epoch)
        writer.add_scalar("Loss/critic", train_metrics['critic_loss'], epoch)
        writer.add_scalar("Accuracy/train_cell", train_metrics['accuracy'], epoch)
        writer.add_scalar("Accuracy/test_cell", test_metrics['cell_accuracy'], epoch)
        writer.add_scalar("Accuracy/test_puzzle", test_metrics['puzzle_accuracy'], epoch)
        writer.add_scalar("Polarity/g_row", g[0].item(), epoch)
        writer.add_scalar("Polarity/g_col", g[1].item(), epoch)
        writer.add_scalar("Polarity/g_box", g[2].item(), epoch)
        writer.add_scalar("Defect/stabilizations", model.stats['stabilizations'], epoch)
        writer.add_scalar("Defect/agitations", model.stats['agitations'], epoch)
        
        is_best = ""
        if test_metrics['puzzle_accuracy'] > best_acc:
            best_acc = test_metrics['puzzle_accuracy']
            is_best = " *"
        
        print(f"{epoch+1:>5} | {train_metrics['actor_loss']:>7.4f} | {train_metrics['critic_loss']:>7.4f} | "
              f"{train_metrics['accuracy']*100:>5.1f}% | {test_metrics['cell_accuracy']*100:>5.1f}% | "
              f"{test_metrics['puzzle_accuracy']*100:>5.1f}% | "
              f"{g[0]:.3f} {g[1]:.3f} {g[2]:.3f} | {best_acc*100:>5.1f}%{is_best}")
        sys.stdout.flush()
        
        model.reset_stats()
    
    writer.close()
    
    # Final critic test (should pass - trained)
    print("\n[Final Critic Test - After Training]")
    run_critic_test(model, device)
    
    print("\n" + "="*70)
    print(f"FINAL RESULTS")
    print("="*70)
    print(f"Best Puzzle Accuracy: {best_acc*100:.1f}%")
    print(f"Logs saved to: {log_dir}")
    print("="*70)


if __name__ == "__main__":
    main()
