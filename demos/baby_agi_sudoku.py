"""
Baby AGI Sudoku: Thermodynamic Annealing Curriculum

This script implements the "Into the Cool" approach to Sudoku solving:
- Start with easy puzzles (many clues) - shallow gradient
- Progressively remove clues - steepens gradient, spikes energy
- Arousal spikes in response - precision drops, beliefs "melt"
- System re-enters fluid phase and escapes local minima

Key Insight: The 54% local / 0% global trap is a LOCAL MINIMUM.
The system froze into a suboptimal crystal. We use the Homeostatic
Controller's arousal mechanism as "temperature" to melt it.

This is NOT:
- Adding global attention (abandons sheaf topology)
- Just scaling up (memorizes wrong topology faster)

This IS:
- Thermodynamic annealing via the SGC homeostatic mechanism
- Curriculum learning interpreted through thermodynamics
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

# Import components from sudoku_homeostatic
from sudoku_homeostatic import (
    SudokuConfig,
    HomeostaticSudokuAgent,
    build_sudoku_graph,
    evaluate,
)
from sudoku_data_utils import fast_generate_puzzles, load_or_generate


@dataclass
class ThermodynamicConfig:
    """Configuration for Thermodynamic Annealing curriculum."""
    
    # Curriculum phases (clue counts)
    # Standard Sudoku has 81 cells, typical puzzles have 17-35 clues
    # Start at moderate difficulty to get enough constraint pressure
    # Previous experiment showed 54% accuracy with ~25-30 clues
    clue_schedule: List[int] = field(default_factory=lambda: [
        35,  # Phase 0: Medium-easy (46 unknowns) - enough pressure to learn
        30,  # Phase 1: Medium (51 unknowns)
        25,  # Phase 2: Medium-hard (56 unknowns)
        22,  # Phase 3: Hard (59 unknowns)
        20,  # Phase 4: Very hard (61 unknowns)
        17,  # Phase 5: Minimal (64 unknowns) - theoretical minimum for unique
    ])
    
    # Epochs per phase before advancing
    epochs_per_phase: int = 100
    
    # Grokking threshold to advance phase
    grok_threshold: float = 0.95  # Cell accuracy required to advance
    
    # Minimum epochs in phase before grokking check
    min_epochs_before_advance: int = 50
    
    # Training config (inherits from SudokuConfig)
    base_config: SudokuConfig = field(default_factory=lambda: SudokuConfig(
        epochs=1000,
        train_puzzles=2000,
        test_puzzles=400,
        batch_size=32,
        diffusion_steps=10,
        tau=0.1,  # Calibrated from experiments
        precision_penalty=0.1,
        scaffold_epochs=0,  # No scaffolding - curriculum provides gradient
        log_interval=10,
    ))
    
    # Logging
    log_dir: str = "logs/baby_agi_sudoku"


def generate_puzzles_with_clues(n_puzzles: int, n_clues: int, seed: int = 42
                                ) -> Tuple[np.ndarray, np.ndarray]:
    """
    Generate Sudoku puzzles with a specific number of clues.
    
    Args:
        n_puzzles: Number of puzzles to generate
        n_clues: Number of clues (given cells) per puzzle
        seed: Random seed
    
    Returns:
        puzzles: (n, 81) array with 0=unknown, 1-9=clues
        solutions: (n, 81) array with full solutions (1-9)
    """
    np.random.seed(seed)
    
    # Generate full solutions first
    solutions = np.zeros((n_puzzles, 81), dtype=np.int32)
    puzzles = np.zeros((n_puzzles, 81), dtype=np.int32)
    
    for i in range(n_puzzles):
        # Generate a valid solution using backtracking
        grid = np.zeros((9, 9), dtype=np.int32)
        if not _solve_sudoku(grid):
            # Fallback: use a shuffled base pattern
            grid = _generate_base_solution()
        
        solutions[i] = grid.flatten()
        
        # Create puzzle by keeping n_clues cells
        mask = np.zeros(81, dtype=bool)
        clue_indices = np.random.choice(81, n_clues, replace=False)
        mask[clue_indices] = True
        
        puzzle = np.zeros(81, dtype=np.int32)
        puzzle[mask] = solutions[i][mask]
        puzzles[i] = puzzle
    
    return puzzles, solutions


def _solve_sudoku(grid: np.ndarray) -> bool:
    """Solve Sudoku using backtracking. Modifies grid in-place."""
    # Find empty cell
    for i in range(9):
        for j in range(9):
            if grid[i, j] == 0:
                # Try digits 1-9 in random order
                digits = np.random.permutation(9) + 1
                for d in digits:
                    if _is_valid(grid, i, j, d):
                        grid[i, j] = d
                        if _solve_sudoku(grid):
                            return True
                        grid[i, j] = 0
                return False
    return True


def _is_valid(grid: np.ndarray, row: int, col: int, digit: int) -> bool:
    """Check if placing digit at (row, col) is valid."""
    # Check row
    if digit in grid[row, :]:
        return False
    # Check column
    if digit in grid[:, col]:
        return False
    # Check 3x3 box
    box_r, box_c = 3 * (row // 3), 3 * (col // 3)
    if digit in grid[box_r:box_r+3, box_c:box_c+3]:
        return False
    return True


def _generate_base_solution() -> np.ndarray:
    """Generate a valid Sudoku solution using pattern shifting."""
    base = np.array([1, 2, 3, 4, 5, 6, 7, 8, 9])
    np.random.shuffle(base)
    
    grid = np.zeros((9, 9), dtype=np.int32)
    for i in range(9):
        shift = (i // 3) + (i % 3) * 3
        grid[i] = np.roll(base, shift)
    
    # Shuffle rows within bands and columns within stacks
    for band in range(3):
        rows = np.random.permutation(3) + band * 3
        grid[band*3:band*3+3] = grid[rows]
    
    for stack in range(3):
        cols = np.random.permutation(3) + stack * 3
        grid[:, stack*3:stack*3+3] = grid[:, cols]
    
    return grid


def run_thermodynamic_curriculum(config: ThermodynamicConfig) -> HomeostaticSudokuAgent:
    """
    Run the Thermodynamic Annealing curriculum.
    
    The key insight: we use the Homeostatic Controller's arousal as "temperature".
    - High clues = low energy = low arousal = "cold" = stable crystal
    - Low clues = high energy = high arousal = "hot" = melted, fluid
    
    By starting cold and progressively heating, we anneal the solution:
    1. Build initial structure with easy puzzles
    2. Heat up (remove clues) to escape local minima
    3. Cool down (the model learns) to crystallize global solution
    """
    device = "cuda" if torch.cuda.is_available() else "cpu"
    
    # Setup logging
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_path = f"{config.log_dir}/run_{timestamp}"
    os.makedirs(log_path, exist_ok=True)
    writer = SummaryWriter(log_path)
    
    # Create model
    model = HomeostaticSudokuAgent(config.base_config).to(device)
    
    # Optimizer with separate LR for precision parameters
    precision_param_ids = {id(p) for p in model.precision_controller.parameters()}
    precision_params = list(model.precision_controller.parameters())
    other_params = [p for p in model.parameters() if id(p) not in precision_param_ids]
    
    optimizer = torch.optim.AdamW([
        {'params': other_params, 'lr': config.base_config.lr},
        {'params': precision_params, 'lr': config.base_config.precision_lr}
    ], weight_decay=config.base_config.weight_decay)
    
    scheduler = torch.optim.lr_scheduler.CosineAnnealingLR(
        optimizer, T_max=config.base_config.epochs
    )
    
    print("=" * 100)
    print("BABY AGI SUDOKU: THERMODYNAMIC ANNEALING CURRICULUM")
    print("=" * 100)
    print(f"Device: {device}")
    print(f"Parameters: {sum(p.numel() for p in model.parameters()):,}")
    print(f"Clue Schedule: {config.clue_schedule}")
    print(f"Epochs per Phase: {config.epochs_per_phase}")
    print(f"Grok Threshold: {config.grok_threshold}")
    print(f"TensorBoard: {log_path}")
    print("=" * 100)
    print()
    
    # Header
    print("-" * 130)
    print(f" {'Phase':>5} | {'Epoch':>5} | {'Clues':>5} | {'Train':>6} | {'Test':>6} | "
          f"{'Puzzle':>6} | {'Energy':>7} | {'Pain':>6} | {'Arousal':>7} | {'Prec':>6} | Status")
    print("-" * 130)
    
    global_epoch = 0
    current_phase = 0
    phase_epoch = 0
    best_test_acc = 0.0
    
    while current_phase < len(config.clue_schedule) and global_epoch < config.base_config.epochs:
        n_clues = config.clue_schedule[current_phase]
        
        # Generate puzzles for this phase
        train_puzzles, train_solutions = generate_puzzles_with_clues(
            config.base_config.train_puzzles, n_clues, seed=42 + current_phase
        )
        test_puzzles, test_solutions = generate_puzzles_with_clues(
            config.base_config.test_puzzles, n_clues, seed=1042 + current_phase
        )
        
        # Create datasets (solutions are 0-indexed for cross-entropy)
        train_dataset = TensorDataset(
            torch.tensor(train_puzzles, dtype=torch.long),
            torch.tensor(train_solutions - 1, dtype=torch.long),
        )
        test_dataset = TensorDataset(
            torch.tensor(test_puzzles, dtype=torch.long),
            torch.tensor(test_solutions - 1, dtype=torch.long),
        )
        
        train_loader = DataLoader(train_dataset, batch_size=config.base_config.batch_size, 
                                  shuffle=True, drop_last=True)
        test_loader = DataLoader(test_dataset, batch_size=config.base_config.batch_size)
        
        # Train for this phase
        for phase_ep in range(config.epochs_per_phase):
            model.train()
            epoch_loss = 0.0
            epoch_energy = 0.0
            
            for batch in train_loader:
                puzzles, solutions = [x.to(device) for x in batch]
                
                optimizer.zero_grad()
                
                # Pass solutions for task pain feedback - "being wrong feels hot"
                logits, energy, complexity, per_type_energy, arousal = model(puzzles, None, solutions)
                
                # Task loss: cross-entropy on unknown cells
                loss_ce = F.cross_entropy(
                    logits.view(-1, 9),
                    solutions.view(-1),
                    reduction='none'
                ).view(puzzles.shape[0], 81)
                
                unknown_mask = (puzzles == 0).float()
                loss_ce = (loss_ce * unknown_mask).sum() / unknown_mask.sum()
                
                # Total loss
                # CRITICAL: Exclusion energy (REPULSIVE) enforces Sudoku constraints
                loss = loss_ce + 1.0 * energy + complexity
                
                loss.backward()
                torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
                optimizer.step()
                
                epoch_loss += loss.item()
                epoch_energy += energy.item()
            
            scheduler.step()
            global_epoch += 1
            phase_epoch += 1
            
            # Evaluate
            if phase_ep % config.base_config.log_interval == 0:
                train_cell_acc, train_puzzle_acc, _ = evaluate(model, train_loader, device)
                test_cell_acc, test_puzzle_acc, test_energy = evaluate(model, test_loader, device)
                
                # Get controller state
                prior_prec, eff_prec = model.precision_controller.get_effective_precision()
                arousal = model.precision_controller.get_arousal()
                task_pain = model.precision_controller.task_pain_ema.item()
                
                mean_arousal = arousal.mean().item()
                mean_prec = prior_prec.mean().item()
                
                # Determine status
                if test_cell_acc > best_test_acc:
                    best_test_acc = test_cell_acc
                    status = "NEW BEST"
                elif test_cell_acc >= config.grok_threshold:
                    status = "GROKKED!"
                else:
                    status = ""
                
                print(f" {current_phase:>5} | {global_epoch:>5} | {n_clues:>5} | "
                      f"{train_cell_acc*100:>5.1f}% | {test_cell_acc*100:>5.1f}% | "
                      f"{test_puzzle_acc*100:>5.1f}% | {test_energy:>7.3f} | "
                      f"{task_pain:>6.2f} | {mean_arousal:>7.3f} | {mean_prec:>6.2f} | {status}")
                
                # Log to TensorBoard
                writer.add_scalar("phase", current_phase, global_epoch)
                writer.add_scalar("clues", n_clues, global_epoch)
                writer.add_scalar("train/cell_acc", train_cell_acc, global_epoch)
                writer.add_scalar("test/cell_acc", test_cell_acc, global_epoch)
                writer.add_scalar("test/puzzle_acc", test_puzzle_acc, global_epoch)
                writer.add_scalar("test/energy", test_energy, global_epoch)
                writer.add_scalar("controller/task_pain", task_pain, global_epoch)
                writer.add_scalar("controller/arousal", mean_arousal, global_epoch)
                writer.add_scalar("controller/precision", mean_prec, global_epoch)
                
                # Check for phase advancement
                if (phase_epoch >= config.min_epochs_before_advance and 
                    test_cell_acc >= config.grok_threshold):
                    print(f"\n>>> PHASE {current_phase} GROKKED at {n_clues} clues! "
                          f"Advancing to harder puzzles...\n")
                    current_phase += 1
                    phase_epoch = 0
                    break
        
        # If we didn't grok, still advance after max epochs
        if phase_epoch >= config.epochs_per_phase:
            print(f"\n>>> PHASE {current_phase} timeout at {n_clues} clues. "
                  f"Best accuracy: {best_test_acc*100:.1f}%. Advancing anyway...\n")
            current_phase += 1
            phase_epoch = 0
    
    print("=" * 100)
    print("TRAINING COMPLETE")
    print(f"  Final Phase: {current_phase}")
    print(f"  Best Cell Accuracy: {best_test_acc*100:.1f}%")
    print("=" * 100)
    
    writer.close()
    
    return model


if __name__ == "__main__":
    config = ThermodynamicConfig()
    model = run_thermodynamic_curriculum(config)
