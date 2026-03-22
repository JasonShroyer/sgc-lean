#!/usr/bin/env python3
"""
Fast Sudoku data loading utilities.

Supports:
1. Loading from CSV (Kaggle format: puzzle,solution as 81-digit strings)
2. Local caching of generated puzzles
3. Fast generation without uniqueness checking

Usage:
    puzzles, solutions = load_or_generate(n=1000, cache_dir='data/sudoku_cache')
"""

import os
import numpy as np
from pathlib import Path
from typing import Tuple, Optional
import random


def fast_generate_puzzles(n: int, min_clues: int = 25, max_clues: int = 35, 
                          seed: int = 42) -> Tuple[np.ndarray, np.ndarray]:
    """Generate puzzles WITHOUT uniqueness checking (fast).
    
    Strategy:
    1. Generate valid filled grid via backtracking with randomization
    2. Remove cells to target clue count
    3. Keep the original as "the" solution (may not be unique, but valid)
    """
    np.random.seed(seed)
    random.seed(seed)
    
    puzzles, solutions = [], []
    
    for _ in range(n):
        # Generate filled grid
        grid = np.zeros((9, 9), dtype=np.int64)
        _fill_grid(grid)
        solution = grid.flatten()
        
        # Remove cells
        num_clues = np.random.randint(min_clues, max_clues + 1)
        puzzle = grid.flatten().copy()
        
        # Randomly select cells to clear
        indices = list(range(81))
        random.shuffle(indices)
        for idx in indices[:81 - num_clues]:
            puzzle[idx] = 0
        
        puzzles.append(puzzle)
        solutions.append(solution)
    
    return np.array(puzzles), np.array(solutions)


def _fill_grid(grid: np.ndarray) -> bool:
    """Fill a 9x9 grid with valid Sudoku solution via backtracking."""
    # Find empty cell
    for i in range(9):
        for j in range(9):
            if grid[i, j] == 0:
                # Try digits in random order
                digits = list(range(1, 10))
                random.shuffle(digits)
                for d in digits:
                    if _is_valid(grid, i, j, d):
                        grid[i, j] = d
                        if _fill_grid(grid):
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


def load_csv(path: str, max_puzzles: Optional[int] = None) -> Tuple[np.ndarray, np.ndarray]:
    """Load puzzles from Kaggle-format CSV (puzzle,solution as 81-digit strings)."""
    puzzles, solutions = [], []
    
    with open(path) as f:
        header = f.readline()  # Skip header if present
        if ',' in header and len(header.split(',')[0]) == 81:
            # No header, reprocess first line
            f.seek(0)
        
        for line in f:
            line = line.strip()
            if not line:
                continue
            
            parts = line.split(',')
            if len(parts) < 2:
                continue
            
            puzzle_str, solution_str = parts[0].strip(), parts[1].strip()
            
            if len(puzzle_str) != 81 or len(solution_str) != 81:
                continue
            
            try:
                puzzle = np.array([int(c.replace('.', '0')) for c in puzzle_str], dtype=np.int64)
                solution = np.array([int(c) for c in solution_str], dtype=np.int64)
            except ValueError:
                continue
            
            puzzles.append(puzzle)
            solutions.append(solution)
            
            if max_puzzles and len(puzzles) >= max_puzzles:
                break
    
    return np.array(puzzles), np.array(solutions)


def save_csv(path: str, puzzles: np.ndarray, solutions: np.ndarray):
    """Save puzzles to Kaggle-format CSV."""
    with open(path, 'w') as f:
        f.write("puzzle,solution\n")
        for p, s in zip(puzzles, solutions):
            puzzle_str = ''.join(str(d) for d in p)
            solution_str = ''.join(str(d) for d in s)
            f.write(f"{puzzle_str},{solution_str}\n")


def load_or_generate(n: int, cache_dir: str = 'data/sudoku_cache', 
                     dataset_path: Optional[str] = None,
                     min_clues: int = 25, max_clues: int = 35,
                     seed: int = 42, split: str = 'train') -> Tuple[np.ndarray, np.ndarray]:
    """Load puzzles from cache/dataset, or generate fast (no uniqueness).
    
    Priority:
    1. If dataset_path provided, load from there
    2. If cache exists, load from cache
    3. Generate fast and save to cache
    
    Args:
        n: Number of puzzles
        cache_dir: Directory for cached puzzles
        dataset_path: Path to external dataset (CSV format)
        min_clues, max_clues: Clue count range for generation
        seed: Random seed
        split: 'train' or 'test' (affects cache filename)
    
    Returns:
        (puzzles, solutions) as numpy arrays of shape (n, 81)
    """
    # Option 1: Load from external dataset
    if dataset_path and os.path.exists(dataset_path):
        print(f"Loading from dataset: {dataset_path}")
        puzzles, solutions = load_csv(dataset_path, max_puzzles=n)
        if len(puzzles) >= n:
            return puzzles[:n], solutions[:n]
        print(f"  Dataset has only {len(puzzles)} puzzles, need {n}")
    
    # Option 2: Load from cache
    cache_dir = Path(cache_dir)
    cache_file = cache_dir / f"{split}_n{n}_seed{seed}.csv"
    
    if cache_file.exists():
        print(f"Loading from cache: {cache_file}")
        puzzles, solutions = load_csv(str(cache_file))
        if len(puzzles) >= n:
            return puzzles[:n], solutions[:n]
    
    # Option 3: Generate fast (no uniqueness) and cache
    print(f"Generating {n} puzzles (fast, no uniqueness)...")
    puzzles, solutions = fast_generate_puzzles(n, min_clues, max_clues, seed)
    
    # Save to cache
    cache_dir.mkdir(parents=True, exist_ok=True)
    save_csv(str(cache_file), puzzles, solutions)
    print(f"  Cached to: {cache_file}")
    
    return puzzles, solutions


if __name__ == '__main__':
    # Quick test
    import time
    
    print("Testing fast puzzle generation...")
    start = time.time()
    puzzles, solutions = load_or_generate(100, seed=42, split='test')
    elapsed = time.time() - start
    print(f"Generated/loaded 100 puzzles in {elapsed:.2f}s")
    print(f"Puzzles shape: {puzzles.shape}")
    print(f"Solutions shape: {solutions.shape}")
    print(f"Sample puzzle clues: {np.sum(puzzles[0] > 0)}")
    
    # Verify a solution is valid
    def check_valid(sol):
        grid = sol.reshape(9, 9)
        for i in range(9):
            if len(set(grid[i, :])) != 9: return False
            if len(set(grid[:, i])) != 9: return False
        for br in range(3):
            for bc in range(3):
                box = grid[br*3:(br+1)*3, bc*3:(bc+1)*3].flatten()
                if len(set(box)) != 9: return False
        return True
    
    valid_count = sum(check_valid(s) for s in solutions)
    print(f"Valid solutions: {valid_count}/{len(solutions)}")
