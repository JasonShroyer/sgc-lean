"""
Adaptive Polarity Sheaf Network v7: Defect-Driven Collapse

THEORY (SGC.Renormalization - The Defect Operator):
    D = (I - Π) ∘ L ∘ Π
    
The Defect Operator measures "how much the coarse state (pencil marks) fails 
to predict the fine state (future dynamics)."

WHY v6 FAILED:
- v6 sensed STATIC STRESS (immediate conflict energy)
- A configuration can be locally consistent but globally wrong
- v6 was MYOPIC: it only felt pain when marks *immediately* conflicted

THE FIX (Predictive Coding of Consequences):
- v7 senses DYNAMIC STABILITY (field evolution over k lookahead steps)
- Correct marks STABILIZE the field (entropy decreases, gradients vanish)
- Wrong marks AGITATE the field (entropy increases, contradictions propagate)

THE DEFECT-DRIVEN CONTROL LOOP:
1. HYPOTHESIZE: Place a pencil mark
2. PROPAGATE: Run k diffusion steps (lookahead into the future)
3. MEASURE DEFECT:
   - Δentropy = entropy_after - entropy_before
   - Δconflict = conflict_after - conflict_before
   - If Δ < 0 → field stabilized → hypothesis is good
   - If Δ > 0 → field agitated → hypothesis is bad
4. ACT:
   - COLLAPSE only if field stabilizes (Defect → 0)
   - ERASE if field agitates (Defect → High)

This changes the signal from "Does it hurt NOW?" to "Does it create chaos LATER?"
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
import sys


@dataclass
class DefectDrivenConfig:
    """Configuration derived from SGC.Renormalization."""
    
    stalk_dim: int = 64
    num_cells: int = 81
    num_digits: int = 9
    
    # Diffusion
    diffusion_steps: int = 5
    diffusion_dt: float = 0.1
    
    # === THE DEFECT SENSOR (Lookahead) ===
    lookahead_steps: int = 8  # How many steps to propagate for measuring defect (more = stronger signal)
    
    # === DEFECT THRESHOLDS ===
    # Defect = change in entropy/conflict after lookahead
    # Negative defect = stabilization (good)
    # Positive defect = agitation (bad)
    # Calibrated from physics test: correct=-0.0001, wrong=+0.0008
    stabilize_threshold: float = -0.0005  # Δentropy < this → stable
    agitate_threshold: float = 0.0005     # Δentropy > this → unstable
    # Neutral zone: [-0.0005, +0.0005] → neither reward nor punish
    
    # === CONFIDENCE DYNAMICS ===
    alpha_grow_rate: float = 0.2        # How fast α grows when stable
    alpha_decay_rate: float = 0.3       # How fast α decays when agitated
    
    # Phase transitions
    crystallize_threshold: float = 0.90  # α > this → commit to pen
    evaporate_threshold: float = 0.0     # α < this → erase pencil
    
    # Write threshold
    write_confidence: float = 0.5        # Probability to write new pencil
    
    # Cognitive cycles
    max_cycles: int = 4
    
    # Polarity
    polarity_init: float = -0.5
    
    # Training
    epochs: int = 100
    batch_size: int = 32
    lr: float = 1e-3
    polarity_lr: float = 0.05
    weight_decay: float = 0.01
    
    # Logging
    log_interval: int = 1  # Log every epoch for real-time monitoring
    log_dir: str = "logs/adaptive_polarity_v7"


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
    """
    The Three-Layer State (Confidence Manifold).
    
    Pen: Immutable ground truth
    Pencil: Mutable hypothesis
    Alpha: Confidence (opacity) of each pencil mark
    """
    
    def __init__(self, puzzles: torch.Tensor, solutions: Optional[torch.Tensor] = None):
        B, N = puzzles.shape
        device = puzzles.device
        
        self.pen = puzzles.clone()
        self.pencil = torch.zeros(B, N, dtype=torch.long, device=device)
        self.alpha = torch.zeros(B, N, device=device)
        self.solutions = solutions  # For training signal
    
    def get_superposition_input(self, sheaf_state: torch.Tensor) -> torch.Tensor:
        """Input = (1 - α) · SheafState + α · OneHot(Pencil)"""
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
    
    def write_pencil(self, mask: torch.Tensor, digits: torch.Tensor, initial_alpha: float = 0.1):
        """Write pencil marks at specified positions."""
        self.pencil[mask] = digits[mask]
        self.alpha[mask] = initial_alpha
    
    def erase_pencil(self, mask: torch.Tensor):
        """Erase pencil marks (evaporate)."""
        self.pencil[mask] = 0
        self.alpha[mask] = 0.0
    
    def crystallize(self, mask: torch.Tensor):
        """Promote pencil to pen (irreversible)."""
        self.pen[mask] = self.pencil[mask]
        self.pencil[mask] = 0
        self.alpha[mask] = 0.0


class DefectMonitor:
    """
    Monitor the Defect Operator dynamics.
    
    Tracks whether the system is correctly predicting consequences.
    """
    
    def __init__(self):
        self.reset()
    
    def reset(self):
        self.stabilizations = 0      # Correct predictions (field calmed)
        self.agitations = 0          # Wrong predictions (field exploded)
        self.crystallizations = 0
        self.evaporations = 0
        self.defect_history = []
        self.accuracy_history = []
    
    def record_defect(self, defect: float):
        self.defect_history.append(defect)
    
    def record_stabilization(self, count: int):
        self.stabilizations += count
    
    def record_agitation(self, count: int):
        self.agitations += count
    
    def record_crystallization(self, count: int):
        self.crystallizations += count
    
    def record_evaporation(self, count: int):
        self.evaporations += count
    
    def get_summary(self) -> str:
        lines = [
            f"  Stabilizations: {self.stabilizations}",
            f"  Agitations: {self.agitations}",
            f"  Crystallizations: {self.crystallizations}",
            f"  Evaporations: {self.evaporations}",
        ]
        if len(self.defect_history) > 0:
            mean_defect = np.mean(self.defect_history[-100:])
            lines.append(f"  Mean Defect: {mean_defect:.4f}")
        return "\n".join(lines)


class SheafDiffusion(nn.Module):
    """Sheaf diffusion with local conflict computation."""
    
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
        """Compute E_repl per cell (normalized to [0, 1])."""
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
    
    def compute_total_energy(self, logits: torch.Tensor) -> torch.Tensor:
        probs = F.softmax(logits, dim=-1)
        overlap = (probs[:, self.src, :] * probs[:, self.dst, :]).sum(dim=-1)
        return overlap.mean()
    
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


class DefectDrivenAgent(nn.Module):
    """
    The SGC Agent with Defect-Driven Collapse.
    
    Key Innovation: Senses DYNAMIC STABILITY (future consequences)
    instead of STATIC STRESS (immediate conflict).
    """
    
    def __init__(self, config: DefectDrivenConfig, edges, edge_types):
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
        
        self.monitor = DefectMonitor()
    
    def compute_entropy(self, logits: torch.Tensor) -> torch.Tensor:
        probs = F.softmax(logits, dim=-1)
        log_probs = F.log_softmax(logits, dim=-1)
        entropy = -(probs * log_probs).sum(dim=-1)
        return entropy
    
    def _run_diffusion(self, state: SudokuState, steps: int) -> Tuple[torch.Tensor, torch.Tensor]:
        """Run diffusion for given steps, return (stalks, logits)."""
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
    
    def sense_current(self, state: SudokuState) -> Tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
        """
        Sense current state: run diffusion, compute beliefs.
        Returns: logits, conflict, entropy
        """
        _, logits = self._run_diffusion(state, self.config.diffusion_steps)
        conflict = self.diffusion.compute_local_conflict(logits)
        entropy = self.compute_entropy(logits)
        return logits, conflict, entropy
    
    def measure_defect(self, state: SudokuState, 
                       entropy_before: torch.Tensor, 
                       conflict_before: torch.Tensor) -> Tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
        """
        THE DEFECT OPERATOR in action.
        
        From SGC.Renormalization: D = (I - Π) L Π measures leakage from constrained subspace.
        
        The correct metric is CONFLICT GROWTH, not entropy change:
        - Correct hypothesis → constraints propagate cleanly → conflict stays low
        - Wrong hypothesis → creates contradictions in neighbors → conflict GROWS
        
        Returns: defect (per cell), delta_conflict (per cell), final_logits
        """
        # Run additional lookahead steps
        _, logits_after = self._run_diffusion(state, 
                                               self.config.diffusion_steps + self.config.lookahead_steps)
        
        conflict_after = self.diffusion.compute_local_conflict(logits_after)
        
        # THE DEFECT = Conflict Growth (not entropy!)
        # This directly measures constraint violation propagation
        delta_conflict = conflict_after - conflict_before
        
        # Defect = positive conflict growth (wrong hypothesis creates contradictions)
        # Negative conflict growth = stabilization (correct hypothesis resolves tensions)
        defect = delta_conflict
        
        return defect, delta_conflict, logits_after
    
    def evaluate_and_act(self, state: SudokuState, logits: torch.Tensor,
                         defect: torch.Tensor, delta_conflict: torch.Tensor) -> Dict:
        """
        EVALUATE + ACT based on Defect measurement (conflict growth).
        
        - Defect < 0 (conflict decreased) → hypothesis is good → grow α
        - Defect > 0 (conflict increased) → hypothesis is bad → decay α
        """
        config = self.config
        stats = {'written': 0, 'evaporated': 0, 'crystallized': 0, 'stabilized': 0, 'agitated': 0}
        
        probs = F.softmax(logits, dim=-1)
        max_prob, best_digit = probs.max(dim=-1)
        best_digit = best_digit + 1
        
        has_pencil = (state.pencil > 0)
        
        # === EVALUATE based on DEFECT (conflict growth) ===
        
        # Field STABILIZED (conflict decreased) → hypothesis resolves tensions → grow confidence
        stabilized = (defect < config.stabilize_threshold) & has_pencil
        state.alpha[stabilized] += config.alpha_grow_rate
        stats['stabilized'] = stabilized.sum().item()
        self.monitor.record_stabilization(stats['stabilized'])
        
        # Field AGITATED (conflict increased) → hypothesis creates contradictions → decay confidence
        agitated = (defect > config.agitate_threshold) & has_pencil
        state.alpha[agitated] -= config.alpha_decay_rate
        stats['agitated'] = agitated.sum().item()
        self.monitor.record_agitation(stats['agitated'])
        
        # Neutral zone → small growth (not creating contradictions is mildly good)
        neutral = has_pencil & ~stabilized & ~agitated
        state.alpha[neutral] += config.alpha_grow_rate * 0.1
        
        # Clamp α
        state.alpha = torch.clamp(state.alpha, -0.5, 1.0)
        
        # Record mean defect
        if has_pencil.any():
            mean_defect = defect[has_pencil].mean().item()
            self.monitor.record_defect(mean_defect)
        
        # === ACT: Phase Transitions ===
        
        # 1. EVAPORATE: α < 0 → Erase (field agitated too much)
        evaporate_mask = (state.alpha < config.evaporate_threshold) & has_pencil
        evaporate_count = evaporate_mask.sum().item()
        if evaporate_count > 0:
            state.erase_pencil(evaporate_mask)
            stats['evaporated'] = evaporate_count
            self.monitor.record_evaporation(evaporate_count)
        
        # 2. CRYSTALLIZE: α > threshold → Commit to pen (field very stable)
        crystallize_mask = (state.alpha > config.crystallize_threshold) & (state.pencil > 0)
        crystallize_count = crystallize_mask.sum().item()
        if crystallize_count > 0:
            state.crystallize(crystallize_mask)
            stats['crystallized'] = crystallize_count
            self.monitor.record_crystallization(crystallize_count)
        
        # 3. WRITE NEW: Empty cells with good predictions
        empty = (state.pen == 0) & (state.pencil == 0)
        confident = max_prob > config.write_confidence
        # Only write if local conflict is reasonable (don't write into chaos)
        conflict = self.diffusion.compute_local_conflict(logits)
        low_conflict = conflict < 0.3
        
        write_mask = empty & confident & low_conflict
        write_count = write_mask.sum().item()
        if write_count > 0:
            state.write_pencil(write_mask, best_digit, initial_alpha=0.1)
            stats['written'] = write_count
        
        return stats
    
    def solve_cycle(self, state: SudokuState) -> Tuple[torch.Tensor, Dict]:
        """
        Run one complete Defect-Driven cycle:
        1. Sense current state
        2. Measure defect (lookahead)
        3. Evaluate and act based on defect
        """
        # Sense current
        logits_before, conflict_before, entropy_before = self.sense_current(state)
        
        # Measure defect via lookahead
        delta_entropy, delta_conflict, logits_after = self.measure_defect(
            state, entropy_before, conflict_before
        )
        
        # Evaluate and act based on defect
        stats = self.evaluate_and_act(state, logits_after, delta_entropy, delta_conflict)
        
        # Record energy
        energy = self.diffusion.compute_total_energy(logits_after)
        stats['energy'] = energy.item()
        
        return logits_after, stats
    
    def solve(self, puzzles: torch.Tensor, solutions: Optional[torch.Tensor] = None
              ) -> Tuple[SudokuState, torch.Tensor, Dict]:
        """Solve puzzles using Defect-Driven collapse."""
        state = SudokuState(puzzles, solutions)
        
        agg_stats = {
            'total_written': 0,
            'total_evaporated': 0,
            'total_crystallized': 0,
            'total_stabilized': 0,
            'total_agitated': 0,
            'cycles': 0,
        }
        
        for cycle in range(self.config.max_cycles):
            logits, stats = self.solve_cycle(state)
            
            agg_stats['total_written'] += stats['written']
            agg_stats['total_evaporated'] += stats['evaporated']
            agg_stats['total_crystallized'] += stats['crystallized']
            agg_stats['total_stabilized'] += stats['stabilized']
            agg_stats['total_agitated'] += stats['agitated']
            agg_stats['cycles'] += 1
            
            if (state.pen > 0).all():
                break
        
        return state, logits, agg_stats
    
    def forward(self, puzzles: torch.Tensor, solutions: Optional[torch.Tensor] = None
                ) -> Tuple[torch.Tensor, Dict]:
        """Forward pass for training."""
        state, logits, stats = self.solve(puzzles, solutions)
        return logits, stats


# === DATA GENERATION ===

def generate_puzzles(n: int, clues: int = 30) -> Tuple[torch.Tensor, torch.Tensor]:
    """Generate n Sudoku puzzles with given number of clues."""
    
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

def train_epoch(model: DefectDrivenAgent, loader: DataLoader, optimizer, device) -> Dict:
    """Train for one epoch."""
    model.train()
    total_loss = 0
    total_correct = 0
    total_cells = 0
    
    for puzzles, solutions in loader:
        puzzles = puzzles.to(device)
        solutions = solutions.to(device)
        
        optimizer.zero_grad()
        
        logits, stats = model(puzzles, solutions)
        
        # Loss: cross-entropy on all cells
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


def evaluate(model: DefectDrivenAgent, loader: DataLoader, device) -> Dict:
    """Evaluate on test set."""
    model.eval()
    total_correct = 0
    total_cells = 0
    puzzle_correct = 0
    total_puzzles = 0
    
    stats_agg = {
        'total_written': 0,
        'total_evaporated': 0,
        'total_crystallized': 0,
        'total_stabilized': 0,
        'total_agitated': 0,
    }
    
    with torch.no_grad():
        for puzzles, solutions in loader:
            puzzles = puzzles.to(device)
            solutions = solutions.to(device)
            
            logits, stats = model(puzzles, solutions)
            
            for k in stats_agg:
                if k in stats:
                    stats_agg[k] += stats.get(k.replace('total_', ''), 0)
            
            preds = logits.argmax(dim=-1) + 1
            total_correct += (preds == solutions).sum().item()
            total_cells += solutions.numel()
            
            puzzle_correct += (preds == solutions).all(dim=1).sum().item()
            total_puzzles += puzzles.size(0)
    
    return {
        'cell_accuracy': total_correct / total_cells,
        'puzzle_accuracy': puzzle_correct / total_puzzles,
        **stats_agg
    }


def run_physics_test(model: DefectDrivenAgent, device):
    """
    Physics Test: Verify that the Defect Operator works.
    
    1. Write a CORRECT pencil mark → field should STABILIZE
    2. Write a WRONG pencil mark → field should AGITATE
    """
    print("\n" + "="*60)
    print("PHYSICS TEST: Defect Operator Verification")
    print("="*60)
    
    model.eval()
    
    # Generate a test puzzle
    puzzles, solutions = generate_puzzles(1, clues=35)
    puzzles = puzzles.to(device)
    solutions = solutions.to(device)
    
    # Find an empty cell
    empty_cells = (puzzles[0] == 0).nonzero(as_tuple=True)[0]
    if len(empty_cells) == 0:
        print("No empty cells!")
        return
    
    test_cell = empty_cells[0].item()
    correct_digit = solutions[0, test_cell].item()
    wrong_digit = (correct_digit % 9) + 1  # A different digit
    
    print(f"\nTest cell: {test_cell}")
    print(f"Correct digit: {correct_digit}")
    print(f"Wrong digit: {wrong_digit}")
    
    # === TEST 1: Write CORRECT digit ===
    print("\n--- Test 1: Writing CORRECT digit ---")
    state_correct = SudokuState(puzzles.clone(), solutions)
    
    # Get baseline conflict (before writing pencil)
    with torch.no_grad():
        logits, conflict_baseline, entropy = model.sense_current(state_correct)
        baseline_conflict = conflict_baseline[0, test_cell].item()
        print(f"Baseline conflict: {baseline_conflict:.4f}")
    
    # Write correct pencil
    state_correct.pencil[0, test_cell] = correct_digit
    state_correct.alpha[0, test_cell] = 0.5
    
    with torch.no_grad():
        # Sense current state with pencil mark
        _, conflict_before, _ = model.sense_current(state_correct)
        # Measure defect (conflict growth after lookahead)
        defect, delta_c, _ = model.measure_defect(state_correct, entropy, conflict_before)
        
        defect_correct = defect[0, test_cell].item()
        print(f"Conflict before lookahead: {conflict_before[0, test_cell].item():.4f}")
        print(f"Defect (conflict growth): {defect_correct:.4f}")
        print(f"  -> {'STABILIZED' if defect_correct < 0 else 'AGITATED'}")
    
    # === TEST 2: Write WRONG digit ===
    print("\n--- Test 2: Writing WRONG digit ---")
    state_wrong = SudokuState(puzzles.clone(), solutions)
    
    # Get baseline conflict for wrong state
    with torch.no_grad():
        _, conflict_baseline_w, _ = model.sense_current(state_wrong)
    
    state_wrong.pencil[0, test_cell] = wrong_digit
    state_wrong.alpha[0, test_cell] = 0.5
    
    with torch.no_grad():
        # Sense current state with wrong pencil mark
        _, conflict_before_w, _ = model.sense_current(state_wrong)
        # Measure defect (conflict growth after lookahead)
        defect_w, delta_c_w, _ = model.measure_defect(state_wrong, entropy, conflict_before_w)
        
        defect_wrong = defect_w[0, test_cell].item()
        print(f"Conflict before lookahead: {conflict_before_w[0, test_cell].item():.4f}")
        print(f"Defect (conflict growth): {defect_wrong:.4f}")
        print(f"  -> {'STABILIZED' if defect_wrong < 0 else 'AGITATED'}")
    
    # === VERIFY PHYSICS ===
    print("\n--- Physics Verification ---")
    
    # Correct should stabilize more than wrong
    physics_ok = defect_correct < defect_wrong
    
    if physics_ok:
        print("[PASS] Correct digit stabilizes MORE than wrong digit")
        print(f"       Defect(correct) = {defect_correct:.4f} < Defect(wrong) = {defect_wrong:.4f}")
    else:
        print("[FAIL] Physics broken! Correct digit should stabilize more.")
        print(f"       Defect(correct) = {defect_correct:.4f} vs Defect(wrong) = {defect_wrong:.4f}")
    
    # Ideally: correct < 0 (stabilizes), wrong > 0 (agitates)
    ideal = defect_correct < 0 and defect_wrong > 0
    if ideal:
        print("[IDEAL] Correct stabilizes (< 0), Wrong agitates (> 0)")
    else:
        print("[NOTE] Not ideal, but relative ordering is what matters for learning")
    
    print("="*60)
    return physics_ok


def main():
    print("="*70)
    print("Adaptive Polarity v7: Defect-Driven Collapse")
    print("="*70)
    print("\nTheory: D = (I - Pi) o L o Pi")
    print("The Defect Operator measures predictive failure.")
    print("Correct hypotheses STABILIZE the field.")
    print("Wrong hypotheses AGITATE the field.")
    print("="*70)
    
    device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
    print(f"\nDevice: {device}")
    
    config = DefectDrivenConfig()
    edges, edge_types = build_sudoku_graph()
    
    model = DefectDrivenAgent(config, edges, edge_types).to(device)
    
    # === TENSORBOARD SETUP ===
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_dir = f"{config.log_dir}/{timestamp}"
    writer = SummaryWriter(log_dir)
    print(f"\nTensorBoard logs: {log_dir}")
    print(f"  Run: tensorboard --logdir={config.log_dir}")
    
    # Log config
    config_str = "\n".join([f"{k}: {v}" for k, v in vars(config).items()])
    writer.add_text("config", config_str, 0)
    
    # Run physics test first
    physics_ok = run_physics_test(model, device)
    
    if not physics_ok:
        print("\n[WARNING] Physics test failed. Consider adjusting lookahead or thresholds.")
    
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
    
    # Optimizer
    optimizer = torch.optim.AdamW([
        {'params': [p for n, p in model.named_parameters() if 'polarity' not in n]},
        {'params': model.diffusion.polarity, 'lr': config.polarity_lr}
    ], lr=config.lr, weight_decay=config.weight_decay)
    
    # === TRAINING WITH REAL-TIME LOGGING ===
    print("\n" + "="*70)
    print("TRAINING")
    print("="*70)
    print(f"{'Epoch':>5} | {'Loss':>7} | {'Train':>6} | {'Test':>6} | {'Puzzle':>6} | {'g_row':>5} {'g_col':>5} {'g_box':>5} | {'Stab':>5} {'Agit':>5} | {'Best':>6}")
    print("-"*70)
    sys.stdout.flush()
    
    best_acc = 0
    
    for epoch in range(config.epochs):
        train_metrics = train_epoch(model, train_loader, optimizer, device)
        test_metrics = evaluate(model, test_loader, device)
        
        g = model.diffusion.get_g().detach().cpu()
        
        # === TENSORBOARD LOGGING ===
        writer.add_scalar("Loss/train", train_metrics['loss'], epoch)
        writer.add_scalar("Accuracy/train_cell", train_metrics['accuracy'], epoch)
        writer.add_scalar("Accuracy/test_cell", test_metrics['cell_accuracy'], epoch)
        writer.add_scalar("Accuracy/test_puzzle", test_metrics['puzzle_accuracy'], epoch)
        
        writer.add_scalar("Polarity/g_row", g[0].item(), epoch)
        writer.add_scalar("Polarity/g_col", g[1].item(), epoch)
        writer.add_scalar("Polarity/g_box", g[2].item(), epoch)
        
        writer.add_scalar("Defect/stabilizations", model.monitor.stabilizations, epoch)
        writer.add_scalar("Defect/agitations", model.monitor.agitations, epoch)
        writer.add_scalar("Defect/crystallizations", model.monitor.crystallizations, epoch)
        writer.add_scalar("Defect/evaporations", model.monitor.evaporations, epoch)
        
        if len(model.monitor.defect_history) > 0:
            mean_defect = np.mean(model.monitor.defect_history[-100:])
            writer.add_scalar("Defect/mean_defect", mean_defect, epoch)
        
        # Track best
        is_best = ""
        if test_metrics['puzzle_accuracy'] > best_acc:
            best_acc = test_metrics['puzzle_accuracy']
            is_best = " *"
        
        # === REAL-TIME CONSOLE OUTPUT ===
        print(f"{epoch+1:>5} | {train_metrics['loss']:>7.4f} | {train_metrics['accuracy']*100:>5.1f}% | "
              f"{test_metrics['cell_accuracy']*100:>5.1f}% | {test_metrics['puzzle_accuracy']*100:>5.1f}% | "
              f"{g[0]:.3f} {g[1]:.3f} {g[2]:.3f} | "
              f"{model.monitor.stabilizations:>5} {model.monitor.agitations:>5} | "
              f"{best_acc*100:>5.1f}%{is_best}")
        sys.stdout.flush()
        
        # Reset monitor for next epoch
        model.monitor.reset()
    
    writer.close()
    
    print("\n" + "="*70)
    print(f"FINAL RESULTS")
    print("="*70)
    print(f"Best Puzzle Accuracy: {best_acc*100:.1f}%")
    print(f"Logs saved to: {log_dir}")
    print("="*70)


if __name__ == "__main__":
    main()
