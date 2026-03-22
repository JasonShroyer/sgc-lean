"""
Adaptive Polarity Sheaf Network v7: The Mortal Homeostat

THEORY (Active Inference + Bounded Existence):
- The entity has an ENERGY BUDGET derived from problem complexity
- Actions COST energy (Landauer-informed)
- Correct placements REWARD energy (negative free energy)
- If energy <= 0, the entity DIES and must restart
- Solving the puzzle grants a large survival bonus

THE ENERGY ECONOMY:
- Budget = alpha * (unknowns * log2(9)) -- proportional to uncertainty
- Write cost = 1.0 (state transition)
- Erase cost = 2.0 (Landauer: dissipation + error recognition)  
- Think cost = 0.1 per diffusion step (metabolic overhead)
- Correct digit = +1.5 (reduces uncertainty)
- Solve puzzle = +50.0 (survival achieved!)
- Death = reset, lose 1 life

This creates GENUINE SURVIVAL PRESSURE -- efficiency, not just accuracy.
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
class MortalHomeostatConfig:
    """Configuration for v7 Mortal Homeostat with energy economy."""
    
    stalk_dim: int = 64
    num_cells: int = 81
    num_digits: int = 9
    
    # Diffusion
    diffusion_steps: int = 5
    diffusion_dt: float = 0.1
    
    # Confidence dynamics
    initial_confidence: float = 0.2
    harden_rate: float = 0.2
    fade_rate: float = 0.25
    crystallize_threshold: float = 0.9
    erase_threshold: float = 0.0
    
    # Thresholds
    low_stress_threshold: float = 0.15
    high_stress_threshold: float = 0.4
    write_threshold: float = 0.35
    
    # Cognitive cycles
    max_cycles: int = 4  # Bounded rationality
    
    # === ENERGY ECONOMY (Physics-informed) ===
    # Budget = budget_multiplier * (unknowns * log2(9))
    budget_multiplier: float = 1.5  # ~220 energy for 46 unknowns
    
    # Costs (Landauer-informed)
    write_cost: float = 1.0      # State transition
    erase_cost: float = 2.0      # Dissipation + error recognition
    think_cost: float = 0.1      # Per diffusion step
    
    # Rewards
    correct_reward: float = 1.5   # Per correct digit placed
    solve_bonus: float = 50.0     # BIG bonus for solving
    
    # Death/Lives
    initial_lives: int = 3        # How many deaths allowed
    death_penalty: float = 0.5    # Fraction of budget lost on death
    
    # Polarity
    polarity_init: float = 0.0
    
    # Training
    epochs: int = 200
    batch_size: int = 32
    lr: float = 1e-3
    polarity_lr: float = 0.05
    weight_decay: float = 0.01
    
    log_interval: int = 10
    log_dir: str = "logs/adaptive_polarity_v7"


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


class EnergyBank:
    """
    The entity's energy economy.
    
    Tracks energy, lives, and survival state.
    """
    
    def __init__(self, num_unknowns: int, config: MortalHomeostatConfig, batch_size: int, device):
        self.config = config
        self.device = device
        self.batch_size = batch_size
        
        # Calculate initial budget based on problem complexity
        # Budget = multiplier * unknowns * log2(9) bits of uncertainty
        bits_per_cell = math.log2(9)  # ~3.17 bits
        self.initial_budget = config.budget_multiplier * num_unknowns * bits_per_cell
        
        # Energy per puzzle in batch
        self.energy = torch.full((batch_size,), self.initial_budget, device=device)
        
        # Lives per puzzle
        self.lives = torch.full((batch_size,), config.initial_lives, dtype=torch.long, device=device)
        
        # Track deaths
        self.total_deaths = 0
        self.total_solves = 0
    
    def spend(self, amount: torch.Tensor):
        """Spend energy. Amount can be per-puzzle or scalar."""
        if amount.dim() == 0:
            self.energy -= amount
        else:
            self.energy -= amount
    
    def earn(self, amount: torch.Tensor):
        """Earn energy from correct placements."""
        if amount.dim() == 0:
            self.energy += amount
        else:
            self.energy += amount
    
    def check_death(self) -> torch.Tensor:
        """Check which puzzles have died (energy <= 0)."""
        dead = self.energy <= 0
        return dead
    
    def handle_deaths(self) -> int:
        """Handle deaths: lose life, reset energy or mark as failed."""
        dead = self.check_death()
        num_deaths = dead.sum().item()
        
        if num_deaths > 0:
            self.total_deaths += num_deaths
            
            # Lose a life
            self.lives[dead] -= 1
            
            # Reset energy for those with lives remaining
            has_lives = self.lives > 0
            reset_mask = dead & has_lives
            self.energy[reset_mask] = self.initial_budget * self.config.death_penalty
        
        return num_deaths
    
    def reward_solve(self, solved_mask: torch.Tensor):
        """Reward for solving puzzles."""
        num_solved = solved_mask.sum().item()
        if num_solved > 0:
            self.total_solves += num_solved
            self.energy[solved_mask] += self.config.solve_bonus
    
    def is_alive(self) -> torch.Tensor:
        """Which puzzles are still alive (have lives and energy)."""
        return (self.lives > 0) & (self.energy > 0)
    
    def get_stats(self) -> Dict:
        return {
            'mean_energy': self.energy.mean().item(),
            'min_energy': self.energy.min().item(),
            'total_deaths': self.total_deaths,
            'total_solves': self.total_solves,
            'alive_fraction': self.is_alive().float().mean().item(),
        }


class SudokuState:
    """Three-layer state: Pen, Pencil, Confidence."""
    
    def __init__(self, puzzles: torch.Tensor, solutions: torch.Tensor = None):
        batch_size = puzzles.shape[0]
        device = puzzles.device
        
        self.pen = puzzles.clone()
        self.pencil = torch.zeros_like(puzzles)
        self.confidence = torch.zeros(batch_size, 81, device=device)
        self.solutions = solutions  # For reward calculation
        
        # Track which cells we've already rewarded
        self.rewarded = (puzzles > 0)  # Clues don't count
    
    def get_effective_board(self) -> torch.Tensor:
        board = self.pen.clone()
        pencil_mask = (self.pen == 0) & (self.pencil > 0)
        board[pencil_mask] = self.pencil[pencil_mask]
        return board
    
    def get_fixed_mask(self, threshold: float = 0.5) -> torch.Tensor:
        pen_fixed = (self.pen > 0)
        pencil_fixed = (self.pencil > 0) & (self.confidence > threshold)
        return pen_fixed | pencil_fixed
    
    def num_unknowns(self) -> int:
        return (self.pen == 0).sum(dim=1).float().mean().item()
    
    def write_pencil(self, cell_mask: torch.Tensor, digits: torch.Tensor, 
                     initial_confidence: float) -> int:
        writeable = (self.pen == 0) & (self.pencil == 0) & cell_mask
        count = writeable.sum().item()
        
        self.pencil[writeable] = digits[writeable]
        self.confidence[writeable] = initial_confidence
        
        return count
    
    def update_confidence(self, stress: torch.Tensor, config):
        has_pencil = (self.pencil > 0)
        
        low_stress = (stress < config.low_stress_threshold) & has_pencil
        self.confidence[low_stress] += config.harden_rate
        
        high_stress = (stress > config.high_stress_threshold) & has_pencil
        self.confidence[high_stress] -= config.fade_rate
        
        self.confidence = torch.clamp(self.confidence, 0.0, 1.0)
    
    def erase_faded(self, threshold: float = 0.0) -> int:
        to_erase = (self.pencil > 0) & (self.confidence <= threshold)
        count = to_erase.sum().item()
        
        self.pencil[to_erase] = 0
        self.confidence[to_erase] = 0.0
        
        return count
    
    def crystallize_confident(self, threshold: float, solutions: torch.Tensor = None) -> Tuple[int, int]:
        """Crystallize and return (count, correct_count)."""
        to_crystallize = (self.pencil > 0) & (self.confidence >= threshold)
        count = to_crystallize.sum().item()
        
        # Check correctness before crystallizing
        correct_count = 0
        if solutions is not None and count > 0:
            pencil_digits = self.pencil - 1  # Convert to 0-8
            correct = (pencil_digits == solutions) & to_crystallize & ~self.rewarded
            correct_count = correct.sum().item()
            self.rewarded[correct] = True
        
        self.pen[to_crystallize] = self.pencil[to_crystallize]
        self.pencil[to_crystallize] = 0
        self.confidence[to_crystallize] = 0.0
        
        return count, correct_count
    
    def is_solved(self) -> torch.Tensor:
        """Check which puzzles are completely filled."""
        return (self.pen > 0).all(dim=1)


class SheafDiffusionV7(nn.Module):
    """Sheaf diffusion with stress computation."""
    
    def __init__(self, edges, edge_types, stalk_dim, polarity_init):
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
        probs = F.softmax(logits, dim=-1)
        batch_size = probs.shape[0]
        
        src_probs = probs[:, self.src_idx, :]
        dst_probs = probs[:, self.dst_idx, :]
        
        overlap = (src_probs * dst_probs).sum(dim=-1)
        
        cell_stress = torch.zeros(batch_size, 81, device=logits.device)
        cell_stress.scatter_add_(1, self.src_idx.unsqueeze(0).expand(batch_size, -1), overlap)
        cell_stress.scatter_add_(1, self.dst_idx.unsqueeze(0).expand(batch_size, -1), overlap)
        
        return cell_stress / 20.0
    
    def compute_total_energy(self, logits: torch.Tensor) -> torch.Tensor:
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
                restricted[:, mask, :] = torch.einsum('bed,df->bef', src_stalks[:, mask, :], W)
        return restricted
    
    def diffuse(self, stalks, logits, dt, fixed_mask):
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
                restricted_dst_for_src[:, mask, :] = torch.einsum('bed,df->bef', dst_stalks[:, mask, :], W)
        
        attr_flow_to_dst = restricted_src - dst_stalks
        attr_flow_to_src = restricted_dst_for_src - stalks[:, self.src_idx, :]
        
        overlap = (src_probs * dst_probs).sum(dim=-1, keepdim=True)
        repl_flow_to_dst = -overlap * (restricted_src - dst_stalks)
        repl_flow_to_src = -overlap * (restricted_dst_for_src - stalks[:, self.src_idx, :])
        
        flow_to_dst = g_per_edge * attr_flow_to_dst + (1 - g_per_edge) * repl_flow_to_dst
        flow_to_src = g_per_edge * attr_flow_to_src + (1 - g_per_edge) * repl_flow_to_src
        
        drift = torch.zeros_like(stalks)
        drift.scatter_add_(1, self.dst_idx.view(1, -1, 1).expand(batch_size, -1, stalk_dim), dt * flow_to_dst)
        drift.scatter_add_(1, self.src_idx.view(1, -1, 1).expand(batch_size, -1, stalk_dim), dt * flow_to_src)
        
        new_stalks = stalks + drift
        fixed_mask_expanded = fixed_mask.unsqueeze(-1)
        new_stalks = torch.where(fixed_mask_expanded, stalks, new_stalks)
        
        return new_stalks


class MortalHomeostat(nn.Module):
    """
    The Mortal SGC Homeostat.
    
    An entity with bounded energy that must survive while solving puzzles.
    """
    
    def __init__(self, config: MortalHomeostatConfig, edges, edge_types):
        super().__init__()
        self.config = config
        
        self.embed = nn.Embedding(10, config.stalk_dim)
        
        self.cell_mlp = nn.Sequential(
            nn.Linear(config.stalk_dim, config.stalk_dim * 2),
            nn.ReLU(),
            nn.Linear(config.stalk_dim * 2, config.stalk_dim),
        )
        
        self.diffusion = SheafDiffusionV7(edges, edge_types, config.stalk_dim, config.polarity_init)
        self.output_head = nn.Linear(config.stalk_dim, config.num_digits)
    
    def sense(self, state: SudokuState) -> Tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
        board = state.get_effective_board()
        fixed_mask = state.get_fixed_mask(0.5)
        
        stalks = self.embed(board)
        stalks = stalks + self.cell_mlp(stalks)
        
        for _ in range(self.config.diffusion_steps):
            logits = self.output_head(stalks)
            stalks = self.diffusion.diffuse(stalks, logits, self.config.diffusion_dt, fixed_mask)
            stalks = stalks + 0.1 * self.cell_mlp(stalks)
        
        logits = self.output_head(stalks)
        stress = self.diffusion.compute_cell_stress(logits)
        
        return stalks, logits, stress
    
    def act(self, state: SudokuState, logits: torch.Tensor, stress: torch.Tensor,
            energy_bank: EnergyBank, solutions: torch.Tensor) -> Dict:
        """
        Act based on current state and stress.
        
        Actions cost energy. Correct placements earn energy.
        """
        config = self.config
        probs = F.softmax(logits, dim=-1)
        max_probs, best_digits = probs.max(dim=-1)
        best_digits = best_digits + 1  # Convert to 1-9
        
        # 1. Update existing confidence
        state.update_confidence(stress, config)
        
        # 2. ERASE faded marks (costs energy!)
        erased = state.erase_faded(config.erase_threshold)
        if erased > 0:
            energy_bank.spend(torch.tensor(erased * config.erase_cost, device=logits.device))
        
        # 3. CRYSTALLIZE confident marks (may earn reward!)
        crystallized, correct = state.crystallize_confident(config.crystallize_threshold, solutions)
        if correct > 0:
            energy_bank.earn(torch.tensor(correct * config.correct_reward, device=logits.device))
        
        # 4. WRITE new pencil marks (costs energy!)
        writeable = (state.pen == 0) & (state.pencil == 0)
        confident = (max_probs > config.write_threshold)
        low_stress = (stress < config.high_stress_threshold)
        
        # Only write if we have energy and are alive
        alive = energy_bank.is_alive()
        write_mask = writeable & confident & low_stress & alive.unsqueeze(1)
        
        written = state.write_pencil(write_mask, best_digits, config.initial_confidence)
        if written > 0:
            energy_bank.spend(torch.tensor(written * config.write_cost, device=logits.device))
        
        # 5. Check for DEATH
        deaths = energy_bank.handle_deaths()
        
        # 6. Check for SOLVE
        solved = state.is_solved()
        energy_bank.reward_solve(solved)
        
        return {
            'written': written,
            'erased': erased,
            'crystallized': crystallized,
            'correct': correct,
            'deaths': deaths,
            'solved': solved.sum().item(),
        }
    
    def solve(self, puzzles: torch.Tensor, solutions: torch.Tensor) -> Tuple[SudokuState, EnergyBank, Dict]:
        """
        Solve puzzles with energy economy.
        """
        config = self.config
        batch_size = puzzles.shape[0]
        device = puzzles.device
        
        state = SudokuState(puzzles, solutions)
        num_unknowns = int(state.num_unknowns())
        
        energy_bank = EnergyBank(num_unknowns, config, batch_size, device)
        
        stats = {
            'total_written': 0,
            'total_erased': 0,
            'total_crystallized': 0,
            'total_correct': 0,
            'total_deaths': 0,
            'total_solved': 0,
            'cycles_used': 0,
        }
        
        for cycle in range(config.max_cycles):
            # SENSE (costs thinking energy)
            stalks, logits, stress = self.sense(state)
            energy_bank.spend(torch.tensor(config.think_cost * config.diffusion_steps, device=device))
            
            # ACT
            result = self.act(state, logits, stress, energy_bank, solutions)
            
            stats['total_written'] += result['written']
            stats['total_erased'] += result['erased']
            stats['total_crystallized'] += result['crystallized']
            stats['total_correct'] += result['correct']
            stats['total_deaths'] += result['deaths']
            stats['total_solved'] += result['solved']
            stats['cycles_used'] += 1
            
            # Check if all puzzles done or dead
            alive = energy_bank.is_alive()
            solved = state.is_solved()
            if (solved | ~alive).all():
                break
        
        # Final sense for logits
        _, final_logits, _ = self.sense(state)
        stats['final_logits'] = final_logits
        stats['energy_stats'] = energy_bank.get_stats()
        
        return state, energy_bank, stats
    
    def forward(self, puzzles: torch.Tensor, solutions: torch.Tensor):
        state, energy_bank, stats = self.solve(puzzles, solutions)
        
        logits = stats['final_logits']
        energy = self.diffusion.compute_total_energy(logits)
        
        return logits, energy, state, stats


def evaluate(model, test_loader, device):
    model.eval()
    
    total_correct = 0
    total_cells = 0
    total_solved = 0
    total_deaths = 0
    total_puzzles = 0
    
    with torch.no_grad():
        for batch in test_loader:
            puzzles, solutions = [x.to(device) for x in batch]
            
            state, energy_bank, stats = model.solve(puzzles, solutions)
            
            final_board = state.get_effective_board()
            preds = final_board - 1
            preds = torch.clamp(preds, 0, 8)
            
            still_empty = (final_board == 0)
            if still_empty.any():
                logit_preds = stats['final_logits'].argmax(dim=-1)
                preds[still_empty] = logit_preds[still_empty]
            
            unknown = (puzzles == 0)
            correct = ((preds == solutions) & unknown).sum().item()
            total_correct += correct
            total_cells += unknown.sum().item()
            
            total_solved += stats['total_solved']
            total_deaths += stats['total_deaths']
            total_puzzles += puzzles.shape[0]
    
    return {
        'accuracy': total_correct / max(total_cells, 1),
        'solve_rate': total_solved / max(total_puzzles, 1),
        'death_rate': total_deaths / max(total_puzzles, 1),
    }


def run_test():
    from baby_agi_sudoku import generate_puzzles_with_clues
    
    device = "cuda" if torch.cuda.is_available() else "cpu"
    config = MortalHomeostatConfig()
    edges, edge_types = build_sudoku_graph()
    
    model = MortalHomeostat(config, edges, edge_types).to(device)
    
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
    
    optimizer = torch.optim.AdamW([
        {'params': [p for p in model.parameters() if id(p) != id(model.diffusion.polarity_logit)], 
         'lr': config.lr, 'weight_decay': config.weight_decay},
        {'params': [model.diffusion.polarity_logit], 'lr': config.polarity_lr, 'weight_decay': 0.0},
    ])
    
    scheduler = torch.optim.lr_scheduler.CosineAnnealingLR(optimizer, T_max=config.epochs)
    
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_path = f"{config.log_dir}/run_{timestamp}"
    os.makedirs(log_path, exist_ok=True)
    writer = SummaryWriter(log_path)
    
    print("=" * 150)
    print("ADAPTIVE POLARITY v7: The Mortal Homeostat")
    print("=" * 150)
    print(f"Device: {device}")
    print(f"Budget multiplier: {config.budget_multiplier} | Write: {config.write_cost} | Erase: {config.erase_cost}")
    print(f"Correct reward: {config.correct_reward} | Solve bonus: {config.solve_bonus} | Lives: {config.initial_lives}")
    print("=" * 150)
    print()
    print("Energy Economy (Landauer-informed):")
    print("  Budget = 1.5 * unknowns * log2(9) bits")
    print("  Write -1.0 | Erase -2.0 | Think -0.1/step")
    print("  Correct +1.5 | Solve +50.0 | Death = lose life, reset")
    print()
    
    print("-" * 150)
    print(f" {'Ep':>4} | {'Train':>6} | {'Test':>6} | {'Solve%':>6} | {'Death%':>6} | "
          f"{'Energy':>7} | {'g_row':>6} | {'g_col':>6} | {'g_box':>6} | Status")
    print("-" * 150)
    
    best_acc = 0.0
    
    for epoch in range(config.epochs):
        model.train()
        train_correct = 0
        train_total = 0
        
        for batch in train_loader:
            puzzles, solutions = [x.to(device) for x in batch]
            
            optimizer.zero_grad()
            
            logits, energy, state, stats = model(puzzles, solutions)
            
            loss_ce = F.cross_entropy(
                logits.view(-1, 9),
                solutions.view(-1),
                reduction='none'
            ).view(puzzles.shape[0], 81)
            
            unknown_mask = (puzzles == 0).float()
            loss_ce = (loss_ce * unknown_mask).sum() / unknown_mask.sum()
            
            loss = loss_ce + 0.5 * energy
            
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
            optimizer.step()
            
            with torch.no_grad():
                preds = logits.argmax(dim=-1)
                unknown = (puzzles == 0)
                train_correct += ((preds == solutions) & unknown).sum().item()
                train_total += unknown.sum().item()
        
        scheduler.step()
        
        if epoch % config.log_interval == 0:
            results = evaluate(model, test_loader, device)
            train_acc = train_correct / max(train_total, 1)
            
            g = model.diffusion.get_mixture_weight().detach().cpu()
            
            status = ""
            if results['accuracy'] > best_acc:
                best_acc = results['accuracy']
                status = "BEST"
            if results['solve_rate'] > 0.5:
                status += " SURVIVING"
            if results['death_rate'] < 0.1:
                status += " EFFICIENT"
            if g.max() < 0.3:
                status += " REPULSION"
            
            print(f" {epoch:>4} | {train_acc*100:>5.1f}% | {results['accuracy']*100:>5.1f}% | "
                  f"{results['solve_rate']*100:>5.1f}% | {results['death_rate']*100:>5.1f}% | "
                  f"{'--':>7} | {g[0]:>6.3f} | {g[1]:>6.3f} | {g[2]:>6.3f} | {status}")
            
            writer.add_scalar("test/acc", results['accuracy'], epoch)
            writer.add_scalar("test/solve_rate", results['solve_rate'], epoch)
            writer.add_scalar("test/death_rate", results['death_rate'], epoch)
    
    print("=" * 150)
    final = evaluate(model, test_loader, device)
    print(f"FINAL: Acc={final['accuracy']*100:.1f}%, Solve={final['solve_rate']*100:.1f}%, Death={final['death_rate']*100:.1f}%")
    print("=" * 150)
    
    writer.close()
    return model


if __name__ == "__main__":
    model = run_test()
