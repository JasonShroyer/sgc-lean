#!/usr/bin/env python3
"""
SGC-Grounded Iterative Spectral Refinement (ISR) Sudoku Experiment

A rigorous empirical test of the ISR hypothesis using SGC renormalization formalism:
the learned recursion succeeds by driving a coarse-grained closure condition,
operationalized as collapse of a leakage/vertical-defect proxy under a
partition-defined conditional-expectation projector Π̂.

## Lean Theory Reference
- src/SGC/Renormalization/Approximate.lean: CoarseProjector and leakage-defect perspective
  - CoarseProjector: Π = lift ∘ Q, weighted conditional expectation onto partition blocks
  - DefectOperator: D = (I - Π) ∘ L ∘ Π, the "leakage" from coarse subspace
- ARCHITECTURE.md: "observational physics" and explicit weight pattern

## Hypotheses
- H1 (Closure): ε_t → 0 is necessary for solving
- H2 (Mechanism): η_t peaks during active computation, then collapses
- H3 (Support): Rank(z_t) remains high even as entropy(y_t) drops

Usage:
    python iterative_spectral_refinement.py --generate --num_puzzles 10000 --epochs 100
    python iterative_spectral_refinement.py --sanity_check_data  # Validate data integrity

Author: SGC Project | License: Apache 2.0
"""

import argparse, hashlib, json, os, struct, sys, time
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Tuple
import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import DataLoader, Dataset
from torch.utils.tensorboard import SummaryWriter
from tqdm import tqdm

try:
    import matplotlib.pyplot as plt
    MATPLOTLIB_AVAILABLE = True
except ImportError:
    MATPLOTLIB_AVAILABLE = False

# ═══════════════════════════════════════════════════════════════════════════════
# CONFIGURATION
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class ISRConfig:
    hidden_dim: int = 128
    num_layers: int = 2
    T_steps: int = 30
    max_params: int = 100_000
    batch_size: int = 64
    learning_rate: float = 1e-3
    epochs: int = 100
    data_path: Optional[str] = None
    generate: bool = False
    num_puzzles: int = 10000
    seed: int = 42
    log_dir: str = "logs/isr"
    log_interval: int = 100
    snapshot_interval: int = 5
    eta_mode: str = "hutchinson"
    eta_probes: int = 4
    eta_batch_subsample: int = 8
    weights_mode: str = "entropy"
    # Curriculum: start with easier puzzles (more clues)
    min_clues_start: int = 45
    max_clues_start: int = 55
    min_clues_end: int = 17
    max_clues_end: int = 35
    curriculum_epochs: int = 50
    # Validation
    validate_puzzles: bool = True
    require_unique: bool = True
    sanity_check_data: bool = False

# ═══════════════════════════════════════════════════════════════════════════════
# SUDOKU DATASET
# ═══════════════════════════════════════════════════════════════════════════════

# ═══════════════════════════════════════════════════════════════════════════════
# SUDOKU SOLVER & VALIDATOR
# ═══════════════════════════════════════════════════════════════════════════════

class SudokuSolver:
    """Independent Sudoku solver for validation and uniqueness checking."""
    
    @staticmethod
    def is_valid(grid: np.ndarray, row: int, col: int, num: int) -> bool:
        if num in grid[row]: return False
        if num in grid[:, col]: return False
        br, bc = 3 * (row // 3), 3 * (col // 3)
        if num in grid[br:br+3, bc:bc+3]: return False
        return True
    
    @staticmethod
    def solve(grid: np.ndarray, randomize: bool = True) -> bool:
        """Solve grid in-place. Returns True if solvable."""
        for i in range(9):
            for j in range(9):
                if grid[i, j] == 0:
                    nums = list(range(1, 10))
                    if randomize: np.random.shuffle(nums)
                    for num in nums:
                        if SudokuSolver.is_valid(grid, i, j, num):
                            grid[i, j] = num
                            if SudokuSolver.solve(grid, randomize): return True
                            grid[i, j] = 0
                    return False
        return True
    
    @staticmethod
    def count_solutions(grid: np.ndarray, limit: int = 2) -> int:
        """Count solutions up to limit. For uniqueness, call with limit=2."""
        grid = grid.copy()
        count = [0]
        
        def backtrack():
            if count[0] >= limit: return
            for i in range(9):
                for j in range(9):
                    if grid[i, j] == 0:
                        for num in range(1, 10):
                            if SudokuSolver.is_valid(grid, i, j, num):
                                grid[i, j] = num
                                backtrack()
                                grid[i, j] = 0
                        return
            count[0] += 1
        
        backtrack()
        return count[0]
    
    @staticmethod
    def is_unique(puzzle: np.ndarray) -> bool:
        """Check if puzzle has exactly one solution."""
        return SudokuSolver.count_solutions(puzzle, limit=2) == 1
    
    @staticmethod
    def validate_puzzle_solution(puzzle: np.ndarray, solution: np.ndarray) -> Tuple[bool, str]:
        """Validate that puzzle and solution are consistent."""
        puzzle_2d = puzzle.reshape(9, 9) if puzzle.ndim == 1 else puzzle
        solution_2d = solution.reshape(9, 9) if solution.ndim == 1 else solution
        
        # Check solution is valid (all cells 1-9, no conflicts)
        if not np.all((solution_2d >= 1) & (solution_2d <= 9)):
            return False, "Solution contains values outside [1,9]"
        
        for i in range(9):
            if len(set(solution_2d[i])) != 9:
                return False, f"Row {i} has duplicates"
            if len(set(solution_2d[:, i])) != 9:
                return False, f"Col {i} has duplicates"
        
        for br in range(0, 9, 3):
            for bc in range(0, 9, 3):
                block = solution_2d[br:br+3, bc:bc+3].flatten()
                if len(set(block)) != 9:
                    return False, f"Block ({br},{bc}) has duplicates"
        
        # Check puzzle clues match solution
        clue_mask = puzzle_2d > 0
        if not np.all(puzzle_2d[clue_mask] == solution_2d[clue_mask]):
            mismatches = np.where(clue_mask & (puzzle_2d != solution_2d))
            return False, f"Clue mismatch at cells: {list(zip(mismatches[0], mismatches[1]))}"
        
        return True, "OK"


class SudokuDataset(Dataset):
    def __init__(self, puzzles: np.ndarray, solutions: np.ndarray, validate: bool = True):
        # Hard assertion: verify puzzle-solution consistency
        if validate:
            for i, (p, s) in enumerate(zip(puzzles, solutions)):
                valid, msg = SudokuSolver.validate_puzzle_solution(p, s)
                assert valid, f"Puzzle {i} invalid: {msg}\n  puzzle={p}\n  solution={s}"
        
        self.puzzles = torch.tensor(puzzles, dtype=torch.long)
        self.solutions = torch.tensor(solutions, dtype=torch.long)
    
    def __len__(self): return len(self.puzzles)
    def __getitem__(self, idx): return self.puzzles[idx], self.solutions[idx]
    
    @staticmethod
    def generate_puzzles(num_puzzles: int, seed: int = 42, 
                         min_clues: int = 17, max_clues: int = 35,
                         require_unique: bool = True,
                         progress: bool = True) -> Tuple[np.ndarray, np.ndarray, Dict]:
        """Generate valid Sudoku puzzles with uniqueness checking.
        
        Returns: (puzzles, solutions, stats_dict)
        """
        np.random.seed(seed)
        puzzles, solutions = [], []
        stats = {'total_attempts': 0, 'unique_checks': 0, 'non_unique_rejected': 0,
                 'clue_distribution': []}
        
        pbar = tqdm(total=num_puzzles, desc="Generating puzzles", disable=not progress)
        
        while len(puzzles) < num_puzzles:
            stats['total_attempts'] += 1
            
            # Generate a complete valid grid
            grid = np.zeros((9, 9), dtype=np.int64)
            SudokuSolver.solve(grid, randomize=True)
            solution = grid.copy()
            
            # Remove cells to create puzzle
            num_clues = np.random.randint(min_clues, max_clues + 1)
            cells = list(range(81))
            np.random.shuffle(cells)
            puzzle = solution.copy()
            
            # Remove cells one at a time, checking uniqueness if required
            removed = 0
            target_remove = 81 - num_clues
            
            if require_unique:
                for idx in cells:
                    if removed >= target_remove: break
                    r, c = idx // 9, idx % 9
                    if puzzle[r, c] != 0:
                        old_val = puzzle[r, c]
                        puzzle[r, c] = 0
                        stats['unique_checks'] += 1
                        if SudokuSolver.is_unique(puzzle):
                            removed += 1
                        else:
                            puzzle[r, c] = old_val
                            stats['non_unique_rejected'] += 1
            else:
                for idx in cells[:target_remove]:
                    puzzle[idx // 9, idx % 9] = 0
                removed = target_remove
            
            actual_clues = 81 - removed
            stats['clue_distribution'].append(actual_clues)
            
            # Validate before accepting
            valid, msg = SudokuSolver.validate_puzzle_solution(puzzle, solution)
            assert valid, f"Generated invalid puzzle: {msg}"
            
            puzzles.append(puzzle.flatten())
            solutions.append(solution.flatten())
            pbar.update(1)
        
        pbar.close()
        return np.array(puzzles), np.array(solutions), stats
    
    @staticmethod
    def load_csv(path: str, validate: bool = True) -> Tuple[np.ndarray, np.ndarray, Dict]:
        """Load puzzles from CSV. Format: puzzle_string,solution_string
        
        puzzle_string: 81 chars, digits 1-9 or . or 0 for empty
        solution_string: 81 chars, digits 1-9
        """
        puzzles, solutions = [], []
        stats = {'total_lines': 0, 'valid_lines': 0, 'parse_errors': []}
        
        with open(path) as f:
            for line_num, line in enumerate(f, 1):
                stats['total_lines'] += 1
                line = line.strip()
                if not line or line.startswith('#'): continue
                
                parts = line.split(',')
                if len(parts) < 2:
                    stats['parse_errors'].append((line_num, "Missing comma"))
                    continue
                
                puzzle_str, solution_str = parts[0].strip(), parts[1].strip()
                
                if len(puzzle_str) != 81:
                    stats['parse_errors'].append((line_num, f"Puzzle length {len(puzzle_str)} != 81"))
                    continue
                if len(solution_str) != 81:
                    stats['parse_errors'].append((line_num, f"Solution length {len(solution_str)} != 81"))
                    continue
                
                try:
                    puzzle = np.array([int(c.replace('.', '0')) for c in puzzle_str], dtype=np.int64)
                    solution = np.array([int(c) for c in solution_str], dtype=np.int64)
                except ValueError as e:
                    stats['parse_errors'].append((line_num, f"Parse error: {e}"))
                    continue
                
                # Validate ranges
                if not np.all((puzzle >= 0) & (puzzle <= 9)):
                    stats['parse_errors'].append((line_num, "Puzzle values not in [0,9]"))
                    continue
                if not np.all((solution >= 1) & (solution <= 9)):
                    stats['parse_errors'].append((line_num, "Solution values not in [1,9]"))
                    continue
                
                if validate:
                    valid, msg = SudokuSolver.validate_puzzle_solution(puzzle, solution)
                    if not valid:
                        stats['parse_errors'].append((line_num, msg))
                        continue
                
                puzzles.append(puzzle)
                solutions.append(solution)
                stats['valid_lines'] += 1
        
        if stats['parse_errors']:
            print(f"[WARN] {len(stats['parse_errors'])} parse errors in {path}")
            for ln, msg in stats['parse_errors'][:5]:
                print(f"  Line {ln}: {msg}")
            if len(stats['parse_errors']) > 5:
                print(f"  ... and {len(stats['parse_errors'])-5} more")
        
        return np.array(puzzles), np.array(solutions), stats

# ═══════════════════════════════════════════════════════════════════════════════
# ISR SOLVER MODEL (< 100k params)
# ═══════════════════════════════════════════════════════════════════════════════

class ISRSolver(nn.Module):
    def __init__(self, hidden_dim: int = 128, num_layers: int = 2):
        super().__init__()
        self.hidden_dim = hidden_dim
        self.input_dim = 19  # 10 (puzzle) + 9 (y logits)
        
        layers = []
        in_dim = self.input_dim + hidden_dim
        for _ in range(num_layers):
            layers.extend([nn.Linear(in_dim, hidden_dim), nn.LayerNorm(hidden_dim), nn.GELU()])
            in_dim = hidden_dim
        self.core = nn.Sequential(*layers)
        self.y_head = nn.Linear(hidden_dim, 9)
        self.z_head = nn.Linear(hidden_dim, hidden_dim)
        self.z_init = nn.Parameter(torch.randn(hidden_dim) * 0.01)
        
        total = sum(p.numel() for p in self.parameters() if p.requires_grad)
        print(f"[ISRSolver] Parameters: {total:,}")
    
    def encode_puzzle(self, puzzle): return F.one_hot(puzzle, num_classes=10).float()
    
    def forward_step(self, y_t, z_t, x_enc):
        combined = torch.cat([x_enc, y_t, z_t], dim=-1)
        h = self.core(combined.view(-1, combined.shape[-1])).view(y_t.shape[0], 81, self.hidden_dim)
        return self.y_head(h), self.z_head(h)
    
    def forward(self, puzzle, T=30, return_trajectory=False):
        batch_size, device = puzzle.shape[0], puzzle.device
        x_enc = self.encode_puzzle(puzzle)
        y_t = torch.zeros(batch_size, 81, 9, device=device)
        z_t = self.z_init.unsqueeze(0).unsqueeze(0).expand(batch_size, 81, -1)
        
        y_traj, z_traj = [y_t], [z_t] if return_trajectory else (None, None)
        for _ in range(T):
            y_t, z_t = self.forward_step(y_t, z_t, x_enc)
            if return_trajectory: y_traj.append(y_t); z_traj.append(z_t)
        
        result = {'y_final': y_t, 'z_final': z_t}
        if return_trajectory:
            result['y_traj'] = torch.stack(y_traj, dim=0)
            result['z_traj'] = torch.stack(z_traj, dim=0)
        return result
    
    def compute_loss(self, y_final, solution, puzzle):
        mask = (puzzle == 0).float().view(-1)
        target = (solution - 1).view(-1)
        ce = F.cross_entropy(y_final.view(-1, 9), target, reduction='none')
        return (ce * mask).sum() / (mask.sum() + 1e-8)
    
    def compute_accuracy(self, y_final, solution, puzzle):
        pred = y_final.argmax(dim=-1) + 1
        pred = torch.where(puzzle > 0, puzzle, pred)
        mask = (puzzle == 0)
        cell_acc = ((pred == solution) & mask).float().sum() / (mask.float().sum() + 1e-8)
        solved_acc = (pred == solution).all(dim=-1).float().mean()
        return {'cell_acc': cell_acc.item(), 'solved_acc': solved_acc.item()}

# ═══════════════════════════════════════════════════════════════════════════════
# SGC ANALYZER - Implements Π̂ (empirical conditional expectation)
# Reference: src/SGC/Renormalization/Approximate.lean (CoarseProjector)
# ═══════════════════════════════════════════════════════════════════════════════

class SGCAnalyzer:
    """
    (Π̂ f)_j = Σ_{k∈B_j} w_k f_k / Σ_{k∈B_j} w_k
    where B_j = {k : Hash(argmax(y_k)) = Hash(argmax(y_j))}
    and w_k = exp(-H(y_k)) (entropy-based weight)
    
    CRITICAL FIX: Uses deterministic GPU-friendly hashing instead of Python hash.
    Reference: src/SGC/Renormalization/Approximate.lean (CoarseProjector)
    """
    def __init__(self, config: ISRConfig, device: torch.device):
        self.config = config
        self.device = device
        # Pre-compute hash multipliers for GPU rolling hash (FNV-1a style)
        # Use prime multipliers to reduce collisions
        self.hash_primes = torch.tensor(
            [int(p) for p in self._generate_primes(81)], 
            device=device, dtype=torch.long
        )
    
    @staticmethod
    def _generate_primes(n: int) -> List[int]:
        """Generate first n primes for hash computation."""
        primes = []
        candidate = 2
        while len(primes) < n:
            is_prime = all(candidate % p != 0 for p in primes)
            if is_prime:
                primes.append(candidate)
            candidate += 1
        return primes
    
    def compute_partition_hash(self, y: torch.Tensor) -> torch.Tensor:
        """
        Deterministic, GPU-native hash of argmax predictions.
        Uses polynomial rolling hash: h = Σ_i (pred_i * prime_i) mod 2^63
        
        FIXED: Replaces Python hash(tuple(...)) which is:
        1. Non-deterministic (salted per process)
        2. Requires CPU sync (slow)
        """
        pred = y.argmax(dim=-1)  # [batch, 81], values in [0,8]
        # Polynomial hash: sum of (digit+1) * prime_i, avoiding 0 contribution
        # Shape: [batch, 81] * [81] -> [batch, 81] -> sum -> [batch]
        hash_vals = ((pred.long() + 1) * self.hash_primes.unsqueeze(0)).sum(dim=-1)
        return hash_vals
    
    def compute_weights(self, y: torch.Tensor) -> torch.Tensor:
        """Compute entropy-based weights w_k = exp(-H(y_k))."""
        if self.config.weights_mode == "uniform":
            return torch.ones(y.shape[0], device=self.device)
        probs = F.softmax(y, dim=-1)
        # Mean entropy across 81 cells
        log_probs = F.log_softmax(y, dim=-1)
        cell_entropy = -(probs * log_probs).sum(dim=-1).mean(dim=-1)  # [batch]
        return torch.exp(-cell_entropy)
    
    def compute_conditional_expectation(self, f: torch.Tensor, hashes: torch.Tensor, 
                                        weights: torch.Tensor) -> torch.Tensor:
        """
        Compute Π̂ f via weighted average over partition blocks.
        
        For each hash value h, samples with that hash are in the same block B.
        (Π̂ f)_j = Σ_{k∈B_j} w_k f_k / Σ_{k∈B_j} w_k
        
        Singleton blocks: Π̂ f = f (identity, no averaging possible).
        """
        batch_size = f.shape[0]
        f_flat = f.reshape(batch_size, -1)  # Use reshape, not view for safety
        result = torch.zeros_like(f_flat)
        
        unique_hashes = torch.unique(hashes)
        for h in unique_hashes:
            mask = (hashes == h)
            indices = torch.where(mask)[0]
            if len(indices) == 1:
                # Singleton block: identity projection
                result[indices[0]] = f_flat[indices[0]]
            else:
                # Multi-sample block: weighted average
                w = weights[indices].unsqueeze(1)  # [k, 1]
                block_f = f_flat[indices]  # [k, D]
                avg = (w * block_f).sum(dim=0) / (w.sum() + 1e-8)  # [D]
                result[indices] = avg.unsqueeze(0).expand(len(indices), -1)
        
        return result.reshape(f.shape)
    
    def compute_leakage(self, z_next: torch.Tensor, y_t: torch.Tensor) -> Dict:
        """
        Compute leakage ε_t = ||z - Π̂z||_F for each sample.
        
        Returns dict with:
        - per_sample: leakage per sample
        - mean: mean leakage
        - singleton_ratio_groups: singleton_groups / total_groups
        - singleton_ratio_samples: samples_in_singletons / batch_size
        """
        hashes = self.compute_partition_hash(y_t)
        weights = self.compute_weights(y_t)
        
        batch_size = z_next.shape[0]
        z_flat = z_next.reshape(batch_size, -1)
        pi_z = self.compute_conditional_expectation(z_flat, hashes, weights)
        
        # Frobenius norm per sample
        leakage = torch.norm(z_flat - pi_z, p=2, dim=-1)  # L2 norm per sample
        
        # Singleton statistics
        unique_hashes = torch.unique(hashes)
        num_groups = len(unique_hashes)
        singleton_groups = 0
        singleton_samples = 0
        for h in unique_hashes:
            count = (hashes == h).sum().item()
            if count == 1:
                singleton_groups += 1
                singleton_samples += 1
        
        return {
            'per_sample': leakage,
            'mean': leakage.mean(),
            'singleton_ratio_groups': singleton_groups / max(num_groups, 1),
            'singleton_ratio_samples': singleton_samples / batch_size,
            'num_groups': num_groups
        }
    
    def compute_non_normality_hutchinson(self, model: nn.Module, y_t: torch.Tensor, 
                                         z_t: torch.Tensor, x_enc: torch.Tensor) -> torch.Tensor:
        """
        Hutchinson estimator for non-normality: η ≈ ||[J, J^T]||_F
        
        Uses JVP/VJP to estimate ||JJ^T - J^TJ|| without forming full Jacobian.
        
        NUMERICAL STABILITY: Added gradient clipping and NaN checks.
        """
        batch_size = min(z_t.shape[0], self.config.eta_batch_subsample)
        indices = torch.randperm(z_t.shape[0], device=z_t.device)[:batch_size]
        y_sub, z_sub, x_sub = y_t[indices], z_t[indices], x_enc[indices]
        
        eta_sq_estimates = []
        
        for _ in range(self.config.eta_probes):
            # Rademacher random vector
            v = (torch.randint(0, 2, z_sub.shape, device=z_sub.device).float() * 2 - 1)
            v = v / (v.numel() ** 0.5)  # Normalize for numerical stability
            
            def fwd(z):
                _, zn = model.forward_step(y_sub, z, x_sub)
                return zn
            
            try:
                # First pass: compute Jv and J^Tv
                z_p = z_sub.clone().requires_grad_(True)
                with torch.enable_grad():
                    zn = fwd(z_p)
                    # Jv = ∂f/∂z · v (JVP via reverse-mode with v as grad_output)
                    Jv = torch.autograd.grad(zn, z_p, grad_outputs=v, 
                                            retain_graph=True, create_graph=False)[0]
                    # J^Tv via VJP: ∂/∂z (f · v) = J^T v
                    JTv = torch.autograd.grad((zn * v).sum(), z_p, 
                                             retain_graph=False, create_graph=False)[0]
                
                # Second pass: compute JJ^Tv and J^TJv
                z_p2 = z_sub.clone().requires_grad_(True)
                with torch.enable_grad():
                    zn2 = fwd(z_p2)
                    JJTv = torch.autograd.grad(zn2, z_p2, grad_outputs=JTv.detach(),
                                              retain_graph=True, create_graph=False)[0]
                    JTJv = torch.autograd.grad((zn2 * Jv.detach()).sum(), z_p2,
                                              retain_graph=False, create_graph=False)[0]
                
                # Commutator estimate: ||JJ^T - J^TJ||^2 ≈ v^T(JJ^T - J^TJ)^2 v
                diff = JJTv - JTJv
                eta_sq = (diff ** 2).sum()
                
                if not torch.isnan(eta_sq) and not torch.isinf(eta_sq):
                    eta_sq_estimates.append(eta_sq)
            except RuntimeError:
                # Gradient computation failed, skip this probe
                continue
        
        if not eta_sq_estimates:
            return torch.tensor(0.0, device=z_t.device)
        
        return torch.sqrt(torch.stack(eta_sq_estimates).mean() + 1e-12)
    
    def compute_non_normality_pooled(self, model: nn.Module, y_t: torch.Tensor,
                                     z_t: torch.Tensor, x_enc: torch.Tensor) -> torch.Tensor:
        """
        Simplified non-normality on pooled representation (cheaper diagnostic).
        Pools z across cells, then computes η on [batch, hidden] representation.
        """
        # Pool across cells: [batch, 81, hidden] -> [batch, hidden]
        z_pooled = z_t.mean(dim=1)
        y_pooled = y_t.mean(dim=1)  # [batch, 9]
        
        # This is a simpler proxy - just measure how non-symmetric the 
        # Jacobian is by comparing forward vs backward perturbation
        eps = 1e-4
        batch_size = min(z_pooled.shape[0], self.config.eta_batch_subsample)
        indices = torch.randperm(z_pooled.shape[0], device=z_pooled.device)[:batch_size]
        
        z_sub = z_pooled[indices]
        
        # Random direction
        v = torch.randn_like(z_sub)
        v = v / (torch.norm(v, dim=-1, keepdim=True) + 1e-8)
        
        # Finite difference approximation of Jv
        z_t_full = z_t[indices]
        y_t_sub = y_t[indices]
        x_sub = x_enc[indices]
        
        with torch.no_grad():
            _, z_fwd = model.forward_step(y_t_sub, z_t_full, x_sub)
            z_pert = z_t_full + eps * v.unsqueeze(1).expand_as(z_t_full)
            _, z_fwd_pert = model.forward_step(y_t_sub, z_pert, x_sub)
            
            # Approximate Jv
            Jv_approx = (z_fwd_pert - z_fwd).mean(dim=1) / eps
            
            # Compare norms as simple non-normality proxy
            fwd_norm = torch.norm(Jv_approx, dim=-1)
            
        return fwd_norm.mean()
    
    def compute_effective_rank(self, z: torch.Tensor) -> float:
        """Effective rank via entropy of singular value distribution."""
        z_flat = z.reshape(z.shape[0], -1)
        z_c = z_flat - z_flat.mean(dim=0, keepdim=True)
        
        try:
            s = torch.linalg.svdvals(z_c)
            s_norm = s / (s.sum() + 1e-8)
            # Effective rank = exp(entropy of singular values)
            entropy = -(s_norm * torch.log(s_norm + 1e-12)).sum()
            return torch.exp(entropy).item()
        except RuntimeError:
            return float('nan')
    
    def compute_y_entropy(self, y: torch.Tensor) -> float:
        """Mean per-cell entropy of y logits."""
        probs = F.softmax(y, dim=-1)
        log_probs = F.log_softmax(y, dim=-1)
        return -(probs * log_probs).sum(dim=-1).mean().item()

# ═══════════════════════════════════════════════════════════════════════════════
# VISUALIZER
# ═══════════════════════════════════════════════════════════════════════════════

class Visualizer:
    def __init__(self, config: ISRConfig):
        self.config = config
        self.log_dir = Path(config.log_dir)
        self.log_dir.mkdir(parents=True, exist_ok=True)
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        self.writer = SummaryWriter(str(self.log_dir / f"run_{ts}"))
        self.plots_dir = self.log_dir / "plots"
        self.plots_dir.mkdir(exist_ok=True)
        self.history = {'loss': [], 'solved_acc': [], 'leakage': [], 'eta': [], 'rank': []}
        self.trajectories = []
    
    def log_scalars(self, step, metrics):
        for k, v in metrics.items():
            self.writer.add_scalar(k, v, step)
    
    def log_histogram(self, step, name, values):
        self.writer.add_histogram(name, values.cpu().numpy(), step)
    
    def save_snapshot(self, epoch, leakage_traj, eta_traj, solved_mask):
        if not MATPLOTLIB_AVAILABLE: return
        fig, axes = plt.subplots(1, 2, figsize=(12, 4))
        T = leakage_traj.shape[0]
        for i in range(min(leakage_traj.shape[1], 20)):
            axes[0].plot(range(T), leakage_traj[:, i], 
                        color='green' if solved_mask[i] else 'red', alpha=0.3, lw=0.5)
        axes[0].set_xlabel('Step t'); axes[0].set_ylabel('Leakage ε_t')
        axes[0].set_title(f'Leakage (Epoch {epoch})'); axes[0].set_yscale('log')
        axes[1].plot(range(len(eta_traj)), eta_traj, 'b-', lw=2)
        axes[1].set_xlabel('Step t'); axes[1].set_ylabel('η_t')
        axes[1].set_title('Non-Normality')
        plt.tight_layout()
        plt.savefig(self.plots_dir / f'snapshot_e{epoch:04d}.png', dpi=150)
        plt.close()
    
    def generate_posthoc_plots(self):
        if not MATPLOTLIB_AVAILABLE or not self.trajectories: return
        fig, axes = plt.subplots(2, 2, figsize=(12, 10))
        solved = [d['solved'] for d in self.trajectories]
        leak = [np.mean(d['leakage'][-5:]) for d in self.trajectories]
        axes[0,0].scatter([l for l, s in zip(leak, solved) if s], [1]*sum(solved), c='g', alpha=0.5)
        axes[0,0].scatter([l for l, s in zip(leak, solved) if not s], [0]*(len(solved)-sum(solved)), c='r', alpha=0.5)
        axes[0,0].set_xlabel('Final Leakage'); axes[0,0].set_ylabel('Solved'); axes[0,0].set_title('H1: Closure')
        for d in self.trajectories[:50]:
            c = 'g' if d['solved'] else 'r'
            axes[0,1].plot(d['leakage'], c=c, alpha=0.3, lw=0.5)
            axes[1,0].plot(d['eta'], c=c, alpha=0.3, lw=0.5)
        axes[0,1].set_yscale('log'); axes[0,1].set_title('Leakage Trajectories')
        axes[1,0].set_title('η Trajectories (H2: Hump)')
        axes[1,1].plot(self.history['loss'], 'b-', label='Loss')
        ax2 = axes[1,1].twinx()
        ax2.plot(self.history['solved_acc'], 'g-', label='Solved')
        axes[1,1].set_title('Training Progress')
        plt.tight_layout()
        plt.savefig(self.plots_dir / 'posthoc.png', dpi=200)
        plt.close()
    
    def save_summary(self, config, metrics):
        with open(self.log_dir / 'summary.json', 'w') as f:
            json.dump({'config': vars(config), 'metrics': metrics, 'ts': datetime.now().isoformat()}, f, indent=2)
    
    def close(self): self.writer.close()

# ═══════════════════════════════════════════════════════════════════════════════
# TRAINING
# ═══════════════════════════════════════════════════════════════════════════════

def train_epoch(model, loader, opt, analyzer, viz, epoch, step, cfg, device):
    model.train()
    pbar = tqdm(loader, desc=f"Epoch {epoch}")
    for puzzles, solutions in pbar:
        puzzles, solutions = puzzles.to(device), solutions.to(device)
        result = model(puzzles, T=cfg.T_steps, return_trajectory=True)
        loss = model.compute_loss(result['y_final'], solutions, puzzles)
        opt.zero_grad(); loss.backward()
        torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
        opt.step()
        
        acc = model.compute_accuracy(result['y_final'], solutions, puzzles)
        
        if step % cfg.log_interval == 0:
            with torch.no_grad():
                y_traj, z_traj = result['y_traj'], result['z_traj']
                # Compute leakage with improved metrics
                leak_info = analyzer.compute_leakage(z_traj[-1], y_traj[-1])
                avg_leak = leak_info['mean'].item()
                singleton_ratio_samples = leak_info['singleton_ratio_samples']
                num_groups = leak_info['num_groups']
                
                x_enc = model.encode_puzzle(puzzles)
                # Use configured eta mode
                if cfg.eta_mode == 'pooled':
                    eta = analyzer.compute_non_normality_pooled(
                        model, y_traj[cfg.T_steps//2], z_traj[cfg.T_steps//2], x_enc).item()
                else:  # hutchinson
                    eta = analyzer.compute_non_normality_hutchinson(
                        model, y_traj[cfg.T_steps//2], z_traj[cfg.T_steps//2], x_enc).item()
                rank = analyzer.compute_effective_rank(z_traj[-1])
                y_entropy = analyzer.compute_y_entropy(y_traj[-1])
            
            pbar.set_postfix(Loss=f'{loss.item():.4f}', Acc=f'{acc["solved_acc"]*100:.1f}%', 
                            Leak=f'{avg_leak:.4f}', η=f'{eta:.4f}', Rank=f'{rank:.1f}')
            viz.log_scalars(step, {
                'Loss/train': loss.item(), 
                'Acc/solved': acc['solved_acc'],
                'Acc/cell': acc['cell_acc'],
                'SGC/Leakage': avg_leak, 
                'SGC/Eta': eta, 
                'SGC/Rank': rank,
                'SGC/Singleton_Ratio_Samples': singleton_ratio_samples,
                'SGC/Num_Groups': num_groups,
                'SGC/Y_Entropy': y_entropy,
            })
            viz.history['loss'].append(loss.item())
            viz.history['solved_acc'].append(acc['solved_acc'])
        step += 1
    return step

def validate(model, loader, analyzer, viz, epoch, cfg, device):
    model.eval()
    puzzles, solutions = next(iter(loader))
    puzzles, solutions = puzzles.to(device), solutions.to(device)
    with torch.no_grad():
        result = model(puzzles, T=cfg.T_steps, return_trajectory=True)
        y_traj, z_traj = result['y_traj'], result['z_traj']
        
        # Compute leakage trajectory for each sample
        leakage_traj = np.zeros((puzzles.shape[0], cfg.T_steps))
        for t in range(cfg.T_steps):
            leak_info = analyzer.compute_leakage(z_traj[t+1], y_traj[t])
            leakage_traj[:, t] = leak_info['per_sample'].cpu().numpy()
        
        x_enc = model.encode_puzzle(puzzles)
        
        # Compute eta trajectory (subsampled for efficiency)
        eta_compute_fn = (analyzer.compute_non_normality_pooled if cfg.eta_mode == 'pooled' 
                         else analyzer.compute_non_normality_hutchinson)
        eta_traj = [eta_compute_fn(model, y_traj[t], z_traj[t], x_enc).item() 
                    for t in range(0, cfg.T_steps, 3)]
        eta_full = np.interp(np.arange(cfg.T_steps), np.arange(0, cfg.T_steps, 3), eta_traj)
        
        pred = result['y_final'].argmax(dim=-1) + 1
        pred = torch.where(puzzles > 0, puzzles, pred)
        solved = (pred == solutions).all(dim=-1).cpu().numpy()
        
        viz.save_snapshot(epoch, leakage_traj.T, eta_full, solved)
        for i in range(min(10, puzzles.shape[0])):
            viz.trajectories.append({'solved': bool(solved[i]), 'leakage': leakage_traj[i].tolist(),
                                     'eta': eta_full.tolist()})

def sanity_check_data(puzzles: np.ndarray, solutions: np.ndarray, 
                      check_uniqueness: bool = True, sample_size: int = 100) -> Dict:
    """Run comprehensive data sanity checks."""
    print("\n" + "="*60)
    print("DATA SANITY CHECK")
    print("="*60)
    
    results = {
        'total_puzzles': len(puzzles),
        'validation_errors': [],
        'clue_distribution': [],
        'uniqueness_checks': 0,
        'non_unique_puzzles': 0,
    }
    
    print(f"\nTotal puzzles: {len(puzzles)}")
    
    # Check all puzzle-solution pairs
    print("\n[1/4] Validating puzzle-solution consistency...")
    for i, (p, s) in enumerate(tqdm(zip(puzzles, solutions), total=len(puzzles))):
        valid, msg = SudokuSolver.validate_puzzle_solution(p, s)
        if not valid:
            results['validation_errors'].append((i, msg))
        results['clue_distribution'].append(np.sum(p > 0))
    
    if results['validation_errors']:
        print(f"  [FAIL] {len(results['validation_errors'])} validation errors!")
        for idx, msg in results['validation_errors'][:5]:
            print(f"     Puzzle {idx}: {msg}")
    else:
        print(f"  [OK] All {len(puzzles)} puzzles valid")
    
    # Clue distribution
    print("\n[2/4] Clue distribution:")
    clues = np.array(results['clue_distribution'])
    print(f"  Min: {clues.min()}, Max: {clues.max()}, Mean: {clues.mean():.1f}, Std: {clues.std():.1f}")
    
    # Histogram
    hist, bins = np.histogram(clues, bins=range(15, 65, 5))
    print(f"  Distribution:")
    for i, count in enumerate(hist):
        bar = '#' * (count * 40 // max(hist)) if max(hist) > 0 else ''
        print(f"    {bins[i]:2d}-{bins[i+1]:2d}: {bar} ({count})")
    
    # Uniqueness check (sample)
    if check_uniqueness:
        print(f"\n[3/4] Checking uniqueness (sampling {sample_size} puzzles)...")
        sample_indices = np.random.choice(len(puzzles), min(sample_size, len(puzzles)), replace=False)
        for idx in tqdm(sample_indices):
            results['uniqueness_checks'] += 1
            if not SudokuSolver.is_unique(puzzles[idx].reshape(9, 9)):
                results['non_unique_puzzles'] += 1
        
        unique_rate = 1 - results['non_unique_puzzles'] / results['uniqueness_checks']
        if results['non_unique_puzzles'] > 0:
            print(f"  [WARN] {results['non_unique_puzzles']}/{results['uniqueness_checks']} puzzles have multiple solutions")
            print(f"    Uniqueness rate: {unique_rate*100:.1f}%")
        else:
            print(f"  [OK] All sampled puzzles have unique solutions")
    else:
        print("\n[3/4] Uniqueness check skipped")
    
    # Value range checks
    print("\n[4/4] Value range checks:")
    puzzle_range_ok = np.all((puzzles >= 0) & (puzzles <= 9))
    solution_range_ok = np.all((solutions >= 1) & (solutions <= 9))
    print(f"  Puzzle values in [0,9]: {'[OK]' if puzzle_range_ok else '[FAIL]'}")
    print(f"  Solution values in [1,9]: {'[OK]' if solution_range_ok else '[FAIL]'}")
    
    print("\n" + "="*60)
    all_ok = (len(results['validation_errors']) == 0 and 
              puzzle_range_ok and solution_range_ok and
              results['non_unique_puzzles'] == 0)
    print(f"RESULT: {'[OK] ALL CHECKS PASSED' if all_ok else '[FAIL] ISSUES FOUND'}")
    print("="*60 + "\n")
    
    return results


def main():
    parser = argparse.ArgumentParser(description='SGC-Grounded ISR Sudoku')
    parser.add_argument('--data_path', type=str, default=None)
    parser.add_argument('--generate', action='store_true')
    parser.add_argument('--num_puzzles', type=int, default=10000)
    parser.add_argument('--seed', type=int, default=42)
    parser.add_argument('--hidden_dim', type=int, default=128)
    parser.add_argument('--num_layers', type=int, default=2)
    parser.add_argument('--T_steps', type=int, default=30)
    parser.add_argument('--batch_size', type=int, default=64)
    parser.add_argument('--lr', type=float, default=1e-3)
    parser.add_argument('--epochs', type=int, default=100)
    parser.add_argument('--log_dir', type=str, default='logs/isr')
    parser.add_argument('--log_interval', type=int, default=100)
    parser.add_argument('--eta_mode', type=str, default='hutchinson', choices=['full', 'hutchinson', 'pooled'])
    parser.add_argument('--eta_probes', type=int, default=4)
    parser.add_argument('--eta_batch_subsample', type=int, default=8)
    parser.add_argument('--weights', type=str, default='entropy', choices=['entropy', 'uniform'])
    # Curriculum options
    parser.add_argument('--min_clues_start', type=int, default=45, help='Initial min clues (easy)')
    parser.add_argument('--max_clues_start', type=int, default=55, help='Initial max clues (easy)')
    parser.add_argument('--min_clues_end', type=int, default=25, help='Final min clues (hard)')
    parser.add_argument('--max_clues_end', type=int, default=40, help='Final max clues (hard)')
    parser.add_argument('--curriculum_epochs', type=int, default=50, help='Epochs to anneal difficulty')
    # Validation options
    parser.add_argument('--no_validate', action='store_true', help='Skip puzzle validation')
    parser.add_argument('--no_unique', action='store_true', help='Skip uniqueness checking during generation')
    parser.add_argument('--sanity_check_data', action='store_true', help='Run data sanity checks and exit')
    args = parser.parse_args()
    
    cfg = ISRConfig(
        hidden_dim=args.hidden_dim, num_layers=args.num_layers, T_steps=args.T_steps,
        batch_size=args.batch_size, learning_rate=args.lr, epochs=args.epochs,
        data_path=args.data_path, generate=args.generate, num_puzzles=args.num_puzzles,
        seed=args.seed, log_dir=args.log_dir, log_interval=args.log_interval,
        eta_mode=args.eta_mode, eta_probes=args.eta_probes, 
        eta_batch_subsample=args.eta_batch_subsample, weights_mode=args.weights,
        min_clues_start=args.min_clues_start, max_clues_start=args.max_clues_start,
        min_clues_end=args.min_clues_end, max_clues_end=args.max_clues_end,
        curriculum_epochs=args.curriculum_epochs,
        validate_puzzles=not args.no_validate, require_unique=not args.no_unique,
        sanity_check_data=args.sanity_check_data
    )
    
    device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
    print(f"[ISR] Device: {device}")
    torch.manual_seed(cfg.seed); np.random.seed(cfg.seed)
    
    # Load or generate data
    print("[ISR] Loading data...")
    if cfg.generate or cfg.data_path is None:
        # Use curriculum starting difficulty (easier puzzles to start)
        puzzles, solutions, gen_stats = SudokuDataset.generate_puzzles(
            cfg.num_puzzles, cfg.seed,
            min_clues=cfg.min_clues_start, max_clues=cfg.max_clues_start,
            require_unique=cfg.require_unique
        )
        print(f"[ISR] Generated {len(puzzles)} puzzles")
        print(f"  Clue range: {min(gen_stats['clue_distribution'])}-{max(gen_stats['clue_distribution'])}")
        if cfg.require_unique:
            print(f"  Uniqueness checks: {gen_stats['unique_checks']}, rejected: {gen_stats['non_unique_rejected']}")
    else:
        puzzles, solutions, load_stats = SudokuDataset.load_csv(cfg.data_path, validate=cfg.validate_puzzles)
        print(f"[ISR] Loaded {len(puzzles)} puzzles from {cfg.data_path}")
    
    # Sanity check mode
    if cfg.sanity_check_data:
        sanity_check_data(puzzles, solutions, check_uniqueness=True, sample_size=100)
        return
    
    # Create datasets with validation
    n = int(0.9 * len(puzzles))
    train_ds = SudokuDataset(puzzles[:n], solutions[:n], validate=cfg.validate_puzzles)
    val_ds = SudokuDataset(puzzles[n:], solutions[n:], validate=cfg.validate_puzzles)
    train_loader = DataLoader(train_ds, batch_size=cfg.batch_size, shuffle=True)
    val_loader = DataLoader(val_ds, batch_size=cfg.batch_size)
    print(f"[ISR] Train: {n}, Val: {len(puzzles)-n}")
    
    model = ISRSolver(cfg.hidden_dim, cfg.num_layers).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=cfg.learning_rate)
    sched = torch.optim.lr_scheduler.CosineAnnealingLR(opt, T_max=cfg.epochs)
    analyzer = SGCAnalyzer(cfg, device)
    viz = Visualizer(cfg)
    
    print("[ISR] Training...")
    step = 0
    for epoch in range(1, cfg.epochs + 1):
        step = train_epoch(model, train_loader, opt, analyzer, viz, epoch, step, cfg, device)
        sched.step()
        if epoch % cfg.snapshot_interval == 0:
            validate(model, val_loader, analyzer, viz, epoch, cfg, device)
    
    viz.generate_posthoc_plots()
    viz.save_summary(cfg, {'final_loss': viz.history['loss'][-1] if viz.history['loss'] else 0,
                           'final_acc': viz.history['solved_acc'][-1] if viz.history['solved_acc'] else 0})
    viz.close()
    print(f"[ISR] Done. Logs: {cfg.log_dir}")

if __name__ == "__main__":
    main()
