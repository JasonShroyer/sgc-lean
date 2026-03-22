"""
Iterative Sheaf Atlas Evaluation

This script implements TRUE iterative learning on ARC:
1. Load persisted atlas from previous runs (if exists)
2. Run evaluation on all tasks
3. Save atlas with accumulated predicates and transitions
4. Track progress across iterations

Theory:
  Unlike single-shot evaluation, this allows the atlas to:
  - Accumulate predicates across multiple runs
  - Learn transition functions (gauge connections) empirically
  - Build up chart structure that captures task manifold geometry

Usage:
  # First run (fresh atlas)
  python eval_iterative_atlas.py
  
  # Subsequent runs (load existing atlas, continue learning)
  python eval_iterative_atlas.py
  
  # Specify iteration number explicitly
  python eval_iterative_atlas.py --iteration 3
  
Environment:
  SGFE_TASK_LIMIT=N  - Limit to first N tasks (default: all)
  SGFE_VERBOSE=1     - Enable verbose output
"""

import os
import sys
import time
import json
import argparse
from pathlib import Path
from datetime import datetime

import numpy as np

# Add demos to path
sys.path.insert(0, str(Path(__file__).parent))

from arc_sgc_phase9 import load_arc_tasks, ARCTask
from arc_sgc_residual_solver import RecursiveResidualSolver

# =============================================================================
# CONFIGURATION
# =============================================================================

ATLAS_DIR = Path(__file__).parent.parent / "data" / "atlas"
ATLAS_FILE = ATLAS_DIR / "sheaf_atlas.json"
PROGRESS_FILE = ATLAS_DIR / "iteration_progress.json"
ARC_DATA_DIR = Path(__file__).parent.parent / "data" / "arc" / "training"


def ensure_atlas_dir():
    """Create atlas directory if it doesn't exist."""
    ATLAS_DIR.mkdir(parents=True, exist_ok=True)


def load_progress() -> dict:
    """Load progress from previous iterations."""
    if PROGRESS_FILE.exists():
        with open(PROGRESS_FILE, 'r') as f:
            return json.load(f)
    return {
        'iterations': [],
        'total_perfect': 0,
        'best_perfect': 0,
        'best_iteration': 0,
    }


def save_progress(progress: dict):
    """Save progress after this iteration."""
    with open(PROGRESS_FILE, 'w') as f:
        json.dump(progress, f, indent=2)


def run_iteration(iteration: int, task_limit: int = None, verbose: bool = True):
    """
    Run one iteration of the evaluation.
    
    Args:
        iteration: Current iteration number (1-indexed)
        task_limit: Max tasks to evaluate (None = all)
        verbose: Print detailed output
    """
    ensure_atlas_dir()
    
    print("="*70)
    print(f"SHEAF ATLAS ITERATIVE EVALUATION - ITERATION {iteration}")
    print("="*70)
    print(f"Atlas file: {ATLAS_FILE}")
    print(f"Started: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print()
    
    # Load previous progress
    progress = load_progress()
    
    # Create solver with SheafAtlas
    solver = RecursiveResidualSolver(
        max_depth=3,
        beam_width=8,
        verbose=verbose,
    )
    
    # Load existing atlas if available
    if solver._sgfe_library is not None and hasattr(solver._sgfe_library, 'load'):
        n_loaded = solver._sgfe_library.load(str(ATLAS_FILE))
        if n_loaded > 0:
            print(f"[ATLAS] Loaded {n_loaded} predicates from iteration {len(progress['iterations'])}")
            solver._sgfe_library.print_summary()
    
    # Load tasks
    print(f"\nLoading tasks from {ARC_DATA_DIR}...")
    tasks = load_arc_tasks(str(ARC_DATA_DIR))
    
    if task_limit:
        tasks = tasks[:task_limit]
        print(f"Limited to {task_limit} tasks")
    
    print(f"Evaluating {len(tasks)} tasks\n")
    
    # Track results
    results = {
        'perfect': 0,
        'near_miss': 0,
        'fail': 0,
        'tasks': [],
    }
    
    start_time = time.time()
    
    for i, task in enumerate(tasks):
        task_start = time.time()
        
        print(f"\n[{i+1}/{len(tasks)}] Task {task.task_id}")
        
        try:
            result = solver.solve_task(task)
            
            # Check if perfect
            is_perfect = result.get('is_perfect', False)
            defect = result.get('energy', 1.0)
            
            if is_perfect:
                results['perfect'] += 1
                status = "PERFECT"
            elif defect < 0.1:
                results['near_miss'] += 1
                status = "NEAR-MISS"
            else:
                results['fail'] += 1
                status = "FAIL"
            
            task_time = time.time() - task_start
            print(f"  -> {status} (defect={defect:.4f}, time={task_time:.1f}s)")
            
            results['tasks'].append({
                'task_id': task.task_id,
                'status': status,
                'defect': defect,
                'time': task_time,
            })
            
        except Exception as e:
            results['fail'] += 1
            print(f"  -> ERROR: {e}")
            results['tasks'].append({
                'task_id': task.task_id,
                'status': 'ERROR',
                'error': str(e),
            })
    
    total_time = time.time() - start_time
    
    # Save atlas
    if solver._sgfe_library is not None and hasattr(solver._sgfe_library, 'save'):
        solver._sgfe_library.save(str(ATLAS_FILE))
        solver._sgfe_library.print_summary()
    
    # Print summary
    print("\n" + "="*70)
    print(f"ITERATION {iteration} COMPLETE")
    print("="*70)
    print(f"Perfect: {results['perfect']} / {len(tasks)} ({100*results['perfect']/len(tasks):.1f}%)")
    print(f"Near-miss: {results['near_miss']}")
    print(f"Fail: {results['fail']}")
    print(f"Total time: {total_time:.1f}s ({total_time/len(tasks):.1f}s/task)")
    
    # Update progress
    iteration_record = {
        'iteration': iteration,
        'timestamp': datetime.now().isoformat(),
        'perfect': results['perfect'],
        'near_miss': results['near_miss'],
        'fail': results['fail'],
        'total_tasks': len(tasks),
        'total_time': total_time,
    }
    
    if solver._sgfe_library is not None:
        stats = solver._sgfe_library.get_statistics()
        iteration_record['atlas_size'] = stats.get('total_predicates', 0)
        iteration_record['num_charts'] = stats.get('num_charts', 0)
        iteration_record['gauge_transfers'] = stats.get('gauge_transfers', 0)
    
    progress['iterations'].append(iteration_record)
    progress['total_perfect'] = results['perfect']
    
    if results['perfect'] > progress['best_perfect']:
        progress['best_perfect'] = results['perfect']
        progress['best_iteration'] = iteration
    
    save_progress(progress)
    
    # Print iteration history
    print("\n" + "-"*70)
    print("ITERATION HISTORY")
    print("-"*70)
    print(f"{'Iter':>4} | {'Perfect':>7} | {'Atlas':>6} | {'Charts':>6} | {'Gauge':>6}")
    print("-"*70)
    for rec in progress['iterations']:
        print(f"{rec['iteration']:>4} | {rec['perfect']:>7} | {rec.get('atlas_size', 0):>6} | {rec.get('num_charts', 0):>6} | {rec.get('gauge_transfers', 0):>6}")
    print("-"*70)
    print(f"Best: {progress['best_perfect']} perfect (iteration {progress['best_iteration']})")
    print("="*70)
    
    return results


def main():
    parser = argparse.ArgumentParser(description='Iterative Sheaf Atlas Evaluation')
    parser.add_argument('--iteration', type=int, default=None,
                        help='Iteration number (auto-increments if not specified)')
    parser.add_argument('--limit', type=int, default=None,
                        help='Limit number of tasks')
    parser.add_argument('--quiet', action='store_true',
                        help='Reduce output verbosity')
    args = parser.parse_args()
    
    # Get task limit from environment or args
    task_limit = args.limit or int(os.environ.get('SGFE_TASK_LIMIT', 0)) or None
    verbose = not args.quiet and os.environ.get('SGFE_VERBOSE', '1') == '1'
    
    # Determine iteration number
    progress = load_progress()
    if args.iteration is not None:
        iteration = args.iteration
    else:
        iteration = len(progress['iterations']) + 1
    
    # Run the iteration
    run_iteration(iteration, task_limit, verbose)


if __name__ == "__main__":
    main()
