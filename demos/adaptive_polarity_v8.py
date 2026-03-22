"""
Adaptive Polarity Sheaf Network v8: The Stochastic Mortal Homeostat

KEY FIXES from v7:
1. Write/Erase are STOCHASTIC initially - near-random, shaped by reward
2. TIME PRESSURE - reward decays with cycles, agent feels time passing
3. MAXIMUM REWARD - there's a ceiling, inefficiency costs real reward
4. Faster training loop for quick iteration

PHYSICS:
- All rules derived from information theory / thermodynamics
- Landauer's principle for costs
- Time as a scarce resource (bounded computation)
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
import math


@dataclass
class StochasticHomeostatConfig:
    stalk_dim: int = 64
    num_cells: int = 81
    num_digits: int = 9
    
    # Diffusion (reduced for speed)
    diffusion_steps: int = 3
    diffusion_dt: float = 0.15
    
    # Cognitive cycles
    max_cycles: int = 4
    
    # === STOCHASTIC ACTION PARAMETERS ===
    # Initial exploration rate (decays during training)
    initial_epsilon: float = 0.5  # 50% random at start
    final_epsilon: float = 0.05   # 5% random at end
    epsilon_decay_epochs: int = 100
    
    # Action probabilities (learned)
    write_temperature: float = 1.0  # Softmax temperature for action selection
    
    # === ENERGY ECONOMY ===
    budget_multiplier: float = 2.0  # Generous budget
    write_cost: float = 1.0
    erase_cost: float = 2.0
    think_cost: float = 0.05  # Reduced
    
    # === REWARD STRUCTURE ===
    max_reward: float = 100.0  # Ceiling
    correct_reward: float = 2.0
    solve_bonus: float = 30.0
    time_decay: float = 0.1  # Reward decays 10% per cycle
    
    # Lives
    initial_lives: int = 3
    
    # Polarity
    polarity_init: float = -1.0  # Start repulsive
    
    # Training (fast iteration)
    epochs: int = 100
    batch_size: int = 64
    lr: float = 2e-3
    log_interval: int = 5
    log_dir: str = "logs/adaptive_polarity_v8"


def build_sudoku_graph():
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
    def __init__(self, puzzles, solutions=None):
        B = puzzles.shape[0]
        device = puzzles.device
        self.pen = puzzles.clone()
        self.pencil = torch.zeros_like(puzzles)
        self.confidence = torch.zeros(B, 81, device=device)
        self.solutions = solutions
        self.rewarded = (puzzles > 0)
    
    def get_board(self):
        board = self.pen.clone()
        mask = (self.pen == 0) & (self.pencil > 0)
        board[mask] = self.pencil[mask]
        return board
    
    def get_fixed_mask(self):
        return (self.pen > 0) | ((self.pencil > 0) & (self.confidence > 0.5))
    
    def num_unknowns(self):
        return (self.pen == 0).sum(dim=1).float().mean().item()
    
    def is_solved(self):
        return (self.pen > 0).all(dim=1)


class ActionNetwork(nn.Module):
    """Network that outputs action probabilities for each cell."""
    
    def __init__(self, stalk_dim):
        super().__init__()
        # Input: stalk + stress + confidence
        self.net = nn.Sequential(
            nn.Linear(stalk_dim + 2, 64),
            nn.ReLU(),
            nn.Linear(64, 3),  # [do_nothing, write, erase]
        )
    
    def forward(self, stalks, stress, confidence):
        # stalks: (B, 81, D), stress: (B, 81), confidence: (B, 81)
        features = torch.cat([
            stalks,
            stress.unsqueeze(-1),
            confidence.unsqueeze(-1),
        ], dim=-1)
        return self.net(features)  # (B, 81, 3)


class SheafDiffusion(nn.Module):
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
    
    def compute_stress(self, logits):
        probs = F.softmax(logits, dim=-1)
        B = probs.shape[0]
        overlap = (probs[:, self.src] * probs[:, self.dst]).sum(-1)
        stress = torch.zeros(B, 81, device=logits.device)
        stress.scatter_add_(1, self.src.unsqueeze(0).expand(B, -1), overlap)
        stress.scatter_add_(1, self.dst.unsqueeze(0).expand(B, -1), overlap)
        return stress / 20.0
    
    def diffuse(self, stalks, logits, dt, fixed):
        B, N, D = stalks.shape
        probs = F.softmax(logits, dim=-1)
        
        g = self.get_g()[self.type_idx].view(1, -1, 1)
        
        src_s = stalks[:, self.src]
        dst_s = stalks[:, self.dst]
        
        # Simplified flow
        overlap = (probs[:, self.src] * probs[:, self.dst]).sum(-1, keepdim=True)
        flow = (1 - g) * (-overlap) * (src_s - dst_s) + g * (src_s - dst_s)
        
        drift = torch.zeros_like(stalks)
        drift.scatter_add_(1, self.dst.view(1,-1,1).expand(B,-1,D), dt * flow)
        drift.scatter_add_(1, self.src.view(1,-1,1).expand(B,-1,D), -dt * flow)
        
        new = stalks + drift
        new = torch.where(fixed.unsqueeze(-1), stalks, new)
        return new


class StochasticHomeostat(nn.Module):
    def __init__(self, config, edges, edge_types):
        super().__init__()
        self.config = config
        
        self.embed = nn.Embedding(10, config.stalk_dim)
        self.mlp = nn.Sequential(
            nn.Linear(config.stalk_dim, config.stalk_dim * 2),
            nn.ReLU(),
            nn.Linear(config.stalk_dim * 2, config.stalk_dim),
        )
        self.diffusion = SheafDiffusion(edges, edge_types, config.stalk_dim, config.polarity_init)
        self.head = nn.Linear(config.stalk_dim, 9)
        self.action_net = ActionNetwork(config.stalk_dim)
    
    def sense(self, state):
        board = state.get_board()
        fixed = state.get_fixed_mask()
        
        stalks = self.embed(board) + self.mlp(self.embed(board))
        
        for _ in range(self.config.diffusion_steps):
            logits = self.head(stalks)
            stalks = self.diffusion.diffuse(stalks, logits, self.config.diffusion_dt, fixed)
        
        logits = self.head(stalks)
        stress = self.diffusion.compute_stress(logits)
        return stalks, logits, stress
    
    def choose_actions(self, stalks, stress, confidence, epsilon):
        """
        Choose actions STOCHASTICALLY.
        
        With probability epsilon: random action
        Otherwise: sample from learned action distribution
        """
        B, N = stress.shape
        device = stress.device
        
        # Get action logits from network
        action_logits = self.action_net(stalks, stress, confidence)  # (B, 81, 3)
        action_probs = F.softmax(action_logits / self.config.write_temperature, dim=-1)
        
        # Epsilon-greedy exploration
        random_mask = torch.rand(B, N, device=device) < epsilon
        random_actions = torch.randint(0, 3, (B, N), device=device)
        
        # Sample from distribution
        sampled_actions = torch.multinomial(action_probs.view(-1, 3), 1).view(B, N)
        
        # Mix random and learned
        actions = torch.where(random_mask, random_actions, sampled_actions)
        
        return actions, action_probs
    
    def execute_actions(self, state, actions, logits, solutions):
        """Execute chosen actions and compute rewards."""
        config = self.config
        B = actions.shape[0]
        device = actions.device
        
        probs = F.softmax(logits, dim=-1)
        best_digits = probs.argmax(dim=-1) + 1  # 1-9
        
        rewards = torch.zeros(B, device=device)
        written = 0
        erased = 0
        correct = 0
        
        # Action 0: do nothing
        # Action 1: write
        # Action 2: erase
        
        write_mask = (actions == 1) & (state.pen == 0) & (state.pencil == 0)
        erase_mask = (actions == 2) & (state.pencil > 0)
        
        # Execute writes
        if write_mask.any():
            state.pencil[write_mask] = best_digits[write_mask]
            state.confidence[write_mask] = 0.3
            written = write_mask.sum().item()
            
            # Immediate feedback: is this correct?
            if solutions is not None:
                correct_writes = (best_digits - 1 == solutions) & write_mask
                correct = correct_writes.sum().item()
                rewards += correct_writes.sum(dim=1).float() * config.correct_reward
        
        # Execute erases
        if erase_mask.any():
            state.pencil[erase_mask] = 0
            state.confidence[erase_mask] = 0
            erased = erase_mask.sum().item()
        
        # Costs
        costs = written * config.write_cost + erased * config.erase_cost
        
        return rewards, costs, written, erased, correct
    
    def solve(self, puzzles, solutions, epsilon=0.1):
        config = self.config
        B = puzzles.shape[0]
        device = puzzles.device
        
        state = SudokuState(puzzles, solutions)
        
        # Energy budget
        budget = config.budget_multiplier * state.num_unknowns() * math.log2(9)
        energy = torch.full((B,), budget, device=device)
        
        total_reward = torch.zeros(B, device=device)
        stats = {'written': 0, 'erased': 0, 'correct': 0, 'cycles': 0}
        
        for cycle in range(config.max_cycles):
            # SENSE
            stalks, logits, stress = self.sense(state)
            energy -= config.think_cost * config.diffusion_steps
            
            # CHOOSE (stochastic!)
            actions, action_probs = self.choose_actions(stalks, stress, state.confidence, epsilon)
            
            # EXECUTE
            rewards, costs, written, erased, correct = self.execute_actions(
                state, actions, logits, solutions
            )
            
            energy -= costs
            
            # TIME DECAY - reward is worth less as time passes
            time_factor = (1 - config.time_decay) ** cycle
            total_reward += rewards * time_factor
            
            stats['written'] += written
            stats['erased'] += erased
            stats['correct'] += correct
            stats['cycles'] += 1
            
            # Crystallize confident pencil marks
            to_crystallize = (state.pencil > 0) & (state.confidence > 0.8)
            state.pen[to_crystallize] = state.pencil[to_crystallize]
            state.pencil[to_crystallize] = 0
            
            # Increase confidence for surviving marks
            state.confidence = torch.clamp(state.confidence + 0.2, 0, 1)
            
            # Check solved
            if state.is_solved().all():
                total_reward += config.solve_bonus * time_factor
                break
        
        # Clamp to maximum
        total_reward = torch.clamp(total_reward, 0, config.max_reward)
        
        _, final_logits, _ = self.sense(state)
        stats['logits'] = final_logits
        stats['reward'] = total_reward.mean().item()
        stats['energy'] = energy.mean().item()
        
        return state, stats
    
    def forward(self, puzzles, solutions, epsilon=0.1):
        state, stats = self.solve(puzzles, solutions, epsilon)
        return stats['logits'], stats


def evaluate(model, loader, device):
    model.eval()
    correct = total = 0
    with torch.no_grad():
        for puzzles, solutions in loader:
            puzzles, solutions = puzzles.to(device), solutions.to(device)
            state, _ = model.solve(puzzles, solutions, epsilon=0.0)
            preds = state.get_board() - 1
            preds = torch.clamp(preds, 0, 8)
            mask = (puzzles == 0)
            correct += ((preds == solutions) & mask).sum().item()
            total += mask.sum().item()
    return correct / max(total, 1)


def run():
    from baby_agi_sudoku import generate_puzzles_with_clues
    
    device = "cuda" if torch.cuda.is_available() else "cpu"
    config = StochasticHomeostatConfig()
    edges, edge_types = build_sudoku_graph()
    
    model = StochasticHomeostat(config, edges, edge_types).to(device)
    
    # Smaller dataset for speed
    train_p, train_s = generate_puzzles_with_clues(500, 35, seed=42)
    test_p, test_s = generate_puzzles_with_clues(100, 35, seed=1042)
    
    train_loader = DataLoader(
        TensorDataset(torch.tensor(train_p, dtype=torch.long), torch.tensor(train_s - 1, dtype=torch.long)),
        batch_size=config.batch_size, shuffle=True, drop_last=True
    )
    test_loader = DataLoader(
        TensorDataset(torch.tensor(test_p, dtype=torch.long), torch.tensor(test_s - 1, dtype=torch.long)),
        batch_size=config.batch_size
    )
    
    optimizer = torch.optim.AdamW(model.parameters(), lr=config.lr)
    scheduler = torch.optim.lr_scheduler.CosineAnnealingLR(optimizer, config.epochs)
    
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_path = f"{config.log_dir}/run_{timestamp}"
    os.makedirs(log_path, exist_ok=True)
    writer = SummaryWriter(log_path)
    
    print("=" * 120)
    print("v8: STOCHASTIC MORTAL HOMEOSTAT")
    print("=" * 120)
    print(f"Stochastic actions | Time decay | Max reward ceiling")
    print(f"Initial epsilon: {config.initial_epsilon} -> {config.final_epsilon}")
    print("-" * 120)
    print(f"{'Ep':>4} | {'Train':>6} | {'Test':>6} | {'Reward':>7} | {'W/E':>8} | {'g':>15} | Status")
    print("-" * 120)
    
    best = 0
    for epoch in range(config.epochs):
        model.train()
        
        # Decay epsilon
        progress = min(1.0, epoch / config.epsilon_decay_epochs)
        epsilon = config.initial_epsilon + (config.final_epsilon - config.initial_epsilon) * progress
        
        epoch_reward = 0
        epoch_written = 0
        epoch_erased = 0
        
        for puzzles, solutions in train_loader:
            puzzles, solutions = puzzles.to(device), solutions.to(device)
            
            optimizer.zero_grad()
            logits, stats = model(puzzles, solutions, epsilon)
            
            # Task loss
            loss = F.cross_entropy(logits.view(-1, 9), solutions.view(-1), reduction='none')
            mask = (puzzles == 0).view(-1).float()
            loss = (loss * mask).sum() / mask.sum()
            
            # Reward-shaped loss (maximize reward)
            reward_loss = -stats['reward'] * 0.01
            
            total_loss = loss + reward_loss
            total_loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
            optimizer.step()
            
            epoch_reward += stats['reward']
            epoch_written += stats['written']
            epoch_erased += stats['erased']
        
        scheduler.step()
        
        if epoch % config.log_interval == 0:
            test_acc = evaluate(model, test_loader, device)
            g = model.diffusion.get_g().detach().cpu().numpy()
            
            status = ""
            if test_acc > best:
                best = test_acc
                status = "BEST"
            if test_acc > 0.9:
                status += " GROKKING!"
            
            print(f"{epoch:>4} | {0:>5.1f}% | {test_acc*100:>5.1f}% | {epoch_reward/len(train_loader):>7.1f} | "
                  f"{epoch_written:>4}/{epoch_erased:<3} | [{g[0]:.2f},{g[1]:.2f},{g[2]:.2f}] | {status}")
            
            writer.add_scalar("test/acc", test_acc, epoch)
            writer.add_scalar("train/reward", epoch_reward/len(train_loader), epoch)
            writer.add_scalar("epsilon", epsilon, epoch)
    
    print("=" * 120)
    print(f"FINAL: {best*100:.1f}% accuracy")
    if best > 0.95:
        print("*** SUDOKU GROKKED! ***")
    print("=" * 120)
    
    writer.close()
    return model, best


if __name__ == "__main__":
    model, acc = run()
