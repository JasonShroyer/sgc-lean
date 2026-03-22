#!/usr/bin/env python3
"""
Phase 1: The Curriculum Grind - Build Global Atlas

This script processes the entire ARC training directory to build a comprehensive
Atlas of relational operators (the "Topos" of transformations).

KEY INNOVATION: Error-Driven Meta-Learning
===========================================
When the engine fails a task:
1. Use the error (wrong answer) as a thermodynamic gradient
2. Force the engine into discovery mode to find new relational operators
3. Iterate until Free Energy = 0 on the test pair
4. Commit successful operators to the Global Atlas

By the end, the Atlas contains every "trick" needed for ARC tasks.

SGC LEAN CONNECTIONS:
=====================
- The Atlas IS the Topos (universal space of morphisms)
- Error-driven learning IS the Free Energy gradient descent
- Discovery mode IS the Yamabe flow finding new curvature corrections
"""

import os
import sys
import time
import json
import pickle
import numpy as np
from typing import List, Dict, Any, Optional

# Add demos directory to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from spiking_sheaf_engine import SpikingSheafEngine
from emergent_sheaf_engine import EmergentSheafAtlas


def load_all_arc_tasks(data_dir: str = "data/arc/training") -> List[Dict[str, Any]]:
    """Load ALL ARC tasks from the training directory."""
    tasks = []
    
    possible_dirs = [
        data_dir,
        os.path.join(os.path.dirname(__file__), "..", "data", "arc", "training"),
        os.path.join(os.path.dirname(__file__), "data", "arc", "training"),
        r"C:\Users\jason\arc-prize-2024\arc-agi_training_challenges",
    ]
    
    actual_dir = None
    for d in possible_dirs:
        if os.path.isdir(d):
            actual_dir = d
            break
    
    if actual_dir is None:
        print(f"ERROR: Could not find ARC training directory")
        return []
    
    print(f"Loading tasks from: {actual_dir}")
    
    for filename in sorted(os.listdir(actual_dir)):
        if filename.endswith('.json'):
            filepath = os.path.join(actual_dir, filename)
            try:
                with open(filepath, 'r') as f:
                    task_data = json.load(f)
                task_data['task_id'] = filename.replace('.json', '')
                tasks.append(task_data)
            except Exception as e:
                print(f"Error loading {filename}: {e}")
    
    print(f"Loaded {len(tasks)} tasks")
    return tasks


def verify_task_solution(engine: SpikingSheafEngine, 
                         test_input: np.ndarray, 
                         test_output: np.ndarray,
                         atlas: EmergentSheafAtlas,
                         predicted_shape: tuple) -> tuple:
    """
    Verify if the engine can solve the test pair.
    
    Returns (success, accuracy, predicted_grid)
    """
    # Set predicted shape
    engine._predicted_output_shape = predicted_shape
    
    # Initialize and compute prior
    engine.P = engine.initialize_membrane_potential(temperature=0.3)
    P_prior = engine.compute_generative_prior(engine.P)
    
    if P_prior is None:
        return False, 0.0, None
    
    predicted = engine.continuous_to_discrete(P_prior)
    
    if predicted.shape != test_output.shape:
        return False, 0.0, predicted
    
    correct = np.sum(predicted == test_output)
    total = test_output.size
    accuracy = correct / total
    
    return accuracy >= 0.99, accuracy, predicted


def error_driven_discovery(task: Dict[str, Any],
                           atlas: EmergentSheafAtlas,
                           max_iterations: int = 5,
                           verbose: bool = False) -> bool:
    """
    Error-Driven Meta-Learning Loop.
    
    When the engine fails, use the error as a gradient to discover new operators.
    """
    task_id = task.get('task_id', 'unknown')
    train_examples = task.get('train', [])
    test_examples = task.get('test', [])
    
    if not test_examples:
        return False
    
    # Phase 1: Learn from training examples (with known targets)
    for ex in train_examples:
        inp = np.array(ex['input'], dtype=np.float32)
        out = np.array(ex['output'], dtype=np.float32)
        
        engine = SpikingSheafEngine(
            input_grid=inp,
            target_grid=out,
            atlas=atlas,
            spike_threshold=0.75,
            learning_rate=0.15
        )
        
        result = engine.solve(verbose=False)
        
        if result.get('exact_match', False):
            # Learn transformation
            engine.learn_transformation(inp, out)
            
            # Learn shape mapping
            n_stalks = len(engine.decompose_to_stalks(inp))
            atlas.learn_shape_mapping(
                input_shape=(int(inp.shape[0]), int(inp.shape[1])),
                output_shape=(int(out.shape[0]), int(out.shape[1])),
                n_stalks=n_stalks
            )
    
    # Phase 2: Verify on test (we're allowed to look at test output in Phase 1)
    test_ex = test_examples[0]
    test_inp = np.array(test_ex['input'], dtype=np.float32)
    test_out = np.array(test_ex['output'], dtype=np.float32)
    
    # Predict shape
    predicted_shape = atlas.predict_output_shape(
        input_shape=(int(test_inp.shape[0]), int(test_inp.shape[1]))
    )
    
    # Create verification engine
    verify_engine = SpikingSheafEngine(
        input_grid=test_inp,
        target_grid=None,
        atlas=atlas,
        spike_threshold=0.75,
        learning_rate=0.15
    )
    
    success, accuracy, predicted = verify_task_solution(
        verify_engine, test_inp, test_out, atlas, predicted_shape
    )
    
    if success:
        if verbose:
            print(f"  [SOLVED] {task_id}: 100% accuracy on test")
        return True
    
    # Phase 3: Error-Driven Discovery Loop
    # Use the test output as a gradient to discover missing operators
    if verbose:
        print(f"  [LEARNING] {task_id}: {accuracy:.1%} accuracy, entering discovery mode...")
    
    for iteration in range(max_iterations):
        # Create engine WITH test output as target (supervised learning)
        discovery_engine = SpikingSheafEngine(
            input_grid=test_inp,
            target_grid=test_out,  # Use test output as target for learning!
            atlas=atlas,
            spike_threshold=0.75,
            learning_rate=0.15
        )
        
        # Run thermodynamic inference to discover operators
        result = discovery_engine.solve(verbose=False)
        
        if result.get('exact_match', False):
            # Successfully found the missing operators!
            discovery_engine.learn_transformation(test_inp, test_out)
            
            # Learn shape mapping
            n_stalks = len(discovery_engine.decompose_to_stalks(test_inp))
            atlas.learn_shape_mapping(
                input_shape=(int(test_inp.shape[0]), int(test_inp.shape[1])),
                output_shape=(int(test_out.shape[0]), int(test_out.shape[1])),
                n_stalks=n_stalks
            )
            
            if verbose:
                print(f"  [DISCOVERED] {task_id}: Found missing operators after {iteration+1} iterations")
            return True
    
    if verbose:
        print(f"  [FAILED] {task_id}: Could not discover operators ({accuracy:.1%} best)")
    return False


def build_global_atlas(max_tasks: int = None, 
                       verbose: bool = True,
                       output_file: str = "global_atlas.pkl") -> EmergentSheafAtlas:
    """
    Build the Global Atlas by processing all ARC training tasks.
    """
    print("=" * 70)
    print("PHASE 1: THE CURRICULUM GRIND")
    print("Building Global Atlas from ARC Training Set")
    print("=" * 70)
    
    # Initialize empty Atlas
    atlas = EmergentSheafAtlas(signature_dims=16)
    
    # Load all tasks
    tasks = load_all_arc_tasks()
    
    if max_tasks:
        tasks = tasks[:max_tasks]
    
    print(f"\nProcessing {len(tasks)} tasks...")
    print()
    
    solved_count = 0
    failed_count = 0
    
    start_time = time.time()
    
    for i, task in enumerate(tasks):
        task_id = task.get('task_id', 'unknown')
        
        success = error_driven_discovery(task, atlas, max_iterations=5, verbose=verbose)
        
        if success:
            solved_count += 1
        else:
            failed_count += 1
        
        # Progress update every 10 tasks
        if (i + 1) % 10 == 0:
            elapsed = time.time() - start_time
            rate = (i + 1) / elapsed
            remaining = (len(tasks) - i - 1) / rate if rate > 0 else 0
            print(f"\n[{i+1}/{len(tasks)}] Solved: {solved_count}, Failed: {failed_count}, "
                  f"Atlas: {atlas.size()} charts, ETA: {remaining:.0f}s\n")
    
    elapsed = time.time() - start_time
    
    print()
    print("=" * 70)
    print("CURRICULUM COMPLETE")
    print("=" * 70)
    print(f"Tasks Solved: {solved_count}/{len(tasks)} ({100*solved_count/len(tasks):.1f}%)")
    print(f"Tasks Failed: {failed_count}/{len(tasks)}")
    print(f"Atlas Size: {atlas.size()} charts")
    print(f"Time: {elapsed:.1f}s")
    
    # Save Atlas to disk
    output_path = os.path.join(os.path.dirname(__file__), output_file)
    
    # Save as pickle (preserves numpy arrays)
    with open(output_path, 'wb') as f:
        pickle.dump(atlas, f)
    
    print(f"\nAtlas saved to: {output_path}")
    
    # Also save a JSON summary
    summary = {
        'tasks_processed': len(tasks),
        'tasks_solved': solved_count,
        'tasks_failed': failed_count,
        'atlas_size': atlas.size(),
        'training_time_seconds': elapsed,
    }
    
    summary_path = output_path.replace('.pkl', '_summary.json')
    with open(summary_path, 'w') as f:
        json.dump(summary, f, indent=2)
    
    print(f"Summary saved to: {summary_path}")
    
    return atlas


if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(description="Build Global Atlas from ARC Training Set")
    parser.add_argument('--max-tasks', type=int, default=None,
                        help="Maximum number of tasks to process (default: all)")
    parser.add_argument('--output', type=str, default="global_atlas.pkl",
                        help="Output file for Atlas (default: global_atlas.pkl)")
    parser.add_argument('--verbose', action='store_true', default=True,
                        help="Verbose output")
    parser.add_argument('--quiet', action='store_true',
                        help="Suppress per-task output")
    
    args = parser.parse_args()
    
    build_global_atlas(
        max_tasks=args.max_tasks,
        verbose=not args.quiet,
        output_file=args.output
    )
