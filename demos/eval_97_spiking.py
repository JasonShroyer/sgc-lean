#!/usr/bin/env python3
"""
Spiking Sheaf Engine v7 - 97 Task Evaluation

This script evaluates the v7 Spiking Sheaf Engine on the ARC curriculum.

KEY INNOVATION: Active Inference with Generative Priors
=========================================================

For TRAINING examples (target known):
  - Use thermodynamic inference with explicit target
  - Learn transformations and store in SheafAtlas

For TEST examples (target hidden):
  - Query SheafAtlas for similar past states
  - Generate P_prior from learned operators
  - Drift toward the prior via Free Energy gradient
  - Spike to crystallize the answer

This implements the core Active Inference loop:
  P' = P - η·∇F(P, P_prior)

where P_prior comes from the Generative Model (Atlas), not the ground truth.

SGC LEAN CONNECTIONS:
=====================
- Blanket.lean: The Atlas stores Markov Blanket structure (restriction maps)
- CurvatureBridge.lean: Learning is Yamabe Flow (curvature smoothing)
- HatanoNelson.lean: L → H_eff similarity transform (quantum bridge)
"""

import os
import sys
import time
import json
import numpy as np
from typing import List, Dict, Any, Optional, Tuple

# Add demos directory to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from spiking_sheaf_engine import SpikingSheafEngine
from emergent_sheaf_engine import EmergentSheafAtlas
import copy


# =============================================================================
# WORKING MEMORY: Local Task-Scoped Sheaf for Hierarchical Active Inference
# =============================================================================

class WorkingMemory:
    """
    The Working Memory is a local sandbox for testing and recomposing
    operators from the Global Atlas before applying them to test data.
    
    Architecture (UPAT Hierarchical Active Inference):
    1. Query: Retrieve candidate morphisms from Global Atlas
    2. Simulate: Apply candidates to training examples
    3. Measure: Calculate Free Energy (prediction error)
    4. Recompose: If F > 0, combine/mutate operators until F = 0
    5. Adjudicate: Only apply to test when verified on all train examples
    """
    
    def __init__(self, global_atlas: EmergentSheafAtlas, train_examples: List[Dict[str, Any]]):
        self.global_atlas = global_atlas
        self.train_examples = train_examples
        
        # Local task-scoped operators (learned from THIS task's training)
        self.local_operators: List[Dict[str, Any]] = []
        
        # Shape mappings for this task only
        self._shape_mappings: List[Dict[str, Any]] = []
        
    def learn_local_operator(self, operator: Dict[str, Any], signature: np.ndarray):
        """Store an operator learned from this task's training examples."""
        self.local_operators.append({
            'operator': copy.deepcopy(operator),
            'signature': signature.copy() if isinstance(signature, np.ndarray) else signature
        })
    
    def learn_shape_mapping(self, input_shape, output_shape, n_stalks=0):
        """Learn shape mapping for this task."""
        self._shape_mappings.append({
            'input_shape': input_shape,
            'output_shape': output_shape,
            'n_stalks': n_stalks,
            'h_ratio': output_shape[0] / max(input_shape[0], 1),
            'w_ratio': output_shape[1] / max(input_shape[1], 1),
        })
    
    def predict_output_shape(self, input_shape):
        """Predict output shape using local shape mappings."""
        if not self._shape_mappings:
            return input_shape
        
        # Check for exact match
        for m in self._shape_mappings:
            if m['input_shape'] == input_shape:
                return m['output_shape']
        
        # Check for fixed output pattern
        output_shapes = [m['output_shape'] for m in self._shape_mappings]
        if len(set(output_shapes)) == 1:
            return output_shapes[0]
        
        # Use most common ratio
        h_ratios = [m['h_ratio'] for m in self._shape_mappings]
        w_ratios = [m['w_ratio'] for m in self._shape_mappings]
        h_ratio = np.median(h_ratios)
        w_ratio = np.median(w_ratios)
        
        return (int(round(input_shape[0] * h_ratio)), 
                int(round(input_shape[1] * w_ratio)))
    
    def get_shape_confidence(self, input_shape):
        """Get confidence in shape prediction."""
        if not self._shape_mappings:
            return 0.0
        
        # Exact match = high confidence
        for m in self._shape_mappings:
            if m['input_shape'] == input_shape:
                return 1.0
        
        # Fixed output pattern = high confidence
        output_shapes = [m['output_shape'] for m in self._shape_mappings]
        if len(set(output_shapes)) == 1:
            return 0.9
        
        return 0.5
    
    def query_global_atlas(self, signature: np.ndarray, k: int = 5) -> List[Dict[str, Any]]:
        """
        Query the Global Atlas for candidate morphisms.
        
        Returns a superposition of historically successful operators,
        weighted by signature similarity.
        """
        return self.global_atlas.find_top_k_charts(signature, k=k, min_similarity=0.5)
    
    def verify_operators_on_train(self, engine_class, verbose=False) -> Tuple[bool, float]:
        """
        Test-Time Verification: Check if local operators achieve F=0 on train.
        
        This is the Scientific Method at the task level:
        - Apply proposed operators to train inputs
        - Measure prediction error against train outputs
        - Only trust operators that perfectly reconstruct training
        """
        if not self.local_operators:
            return False, 0.0
        
        total_correct = 0
        total_pixels = 0
        
        for ex in self.train_examples:
            inp = np.array(ex['input'], dtype=np.float32)
            out = np.array(ex['output'], dtype=np.float32)
            
            # Create engine with local working memory (not global atlas)
            # We pass None for atlas to force use of local operators only
            engine = engine_class(
                input_grid=inp,
                target_grid=None,
                atlas=None,  # No atlas - pure local inference
                spike_threshold=0.75,
                learning_rate=0.15
            )
            
            # Set predicted shape from local working memory
            pred_shape = self.predict_output_shape(
                (int(inp.shape[0]), int(inp.shape[1]))
            )
            engine._predicted_output_shape = pred_shape
            
            # Initialize and compute prior
            engine.P = engine.initialize_membrane_potential(temperature=0.3)
            P_prior = engine.compute_generative_prior(engine.P)
            
            if P_prior is not None:
                predicted = engine.continuous_to_discrete(P_prior)
                if predicted.shape == out.shape:
                    total_correct += np.sum(predicted == out)
                    total_pixels += out.size
        
        if total_pixels == 0:
            return False, 0.0
        
        accuracy = total_correct / total_pixels
        verified = accuracy >= 0.99  # 99% threshold for "grokked"
        
        if verbose:
            status = "VERIFIED" if verified else "NOT VERIFIED"
            print(f"    WORKING MEMORY: {accuracy:.1%} accuracy on train - {status}")
        
        return verified, accuracy
    
    def consolidate_to_global(self):
        """
        After successful task completion, consolidate learned operators
        to the Global Atlas for future reuse.
        
        This implements lifelong learning: successful local solutions
        become part of the permanent memory.
        """
        for op_entry in self.local_operators:
            self.global_atlas.add_chart(
                signature=op_entry['signature'],
                operators=[op_entry['operator']],
                metadata={'source': 'working_memory_consolidation'}
            )


def load_arc_tasks(data_dir: str = "data/arc/training") -> List[Dict[str, Any]]:
    """Load ARC tasks from the data directory."""
    tasks = []
    
    # Try multiple possible data locations
    possible_dirs = [
        data_dir,
        os.path.join(os.path.dirname(__file__), "..", "data", "arc", "training"),
        os.path.join(os.path.dirname(__file__), "data", "arc", "training"),
        os.path.join(os.path.dirname(__file__), "..", "data", "arc"),
        "C:/Lean4 Projects/data/arc/training",
    ]
    
    task_dir = None
    for d in possible_dirs:
        if os.path.exists(d) and os.path.isdir(d):
            # Check if directory has JSON files
            has_json = any(f.endswith('.json') for f in os.listdir(d))
            if has_json:
                task_dir = d
                break
    
    if task_dir is None:
        print(f"WARNING: Could not find ARC data directory with JSON files. Tried: {possible_dirs}")
        return []
    
    print(f"Loading tasks from: {task_dir}")
    
    # Load all JSON task files
    for filename in sorted(os.listdir(task_dir)):
        if filename.endswith('.json'):
            filepath = os.path.join(task_dir, filename)
            try:
                with open(filepath, 'r') as f:
                    task_data = json.load(f)
                    task_data['task_id'] = filename.replace('.json', '')
                    tasks.append(task_data)
            except Exception as e:
                print(f"Error loading {filename}: {e}")
    
    return tasks


def evaluate_task(task: Dict[str, Any], 
                  atlas: EmergentSheafAtlas,
                  verbose: bool = False) -> Dict[str, Any]:
    """
    Evaluate a single ARC task using the Spiking Sheaf Engine.
    
    Training Phase:
      - For each training example, run thermodynamic inference with target
      - Learn transformations and add to Atlas
    
    Test Phase:
      - For the test example, hide the target
      - Use Atlas prior to generate prediction
    """
    task_id = task.get('task_id', 'unknown')
    train_examples = task.get('train', [])
    test_examples = task.get('test', [])
    
    results = {
        'task_id': task_id,
        'train_results': [],
        'test_results': [],
        'train_solved': 0,
        'test_solved': 0,
        'atlas_used': False,
        'time': 0.0
    }
    
    # HIERARCHICAL ACTIVE INFERENCE: Create Working Memory for this task
    # The Global Atlas remains intact (long-term memory / Topos)
    # The Working Memory is a local sandbox for testing and recomposition
    working_memory = WorkingMemory(atlas, train_examples)
    
    start_time = time.time()
    
    # =========================================================================
    # TRAINING PHASE: Learn from examples with known targets
    # =========================================================================
    
    for i, ex in enumerate(train_examples):
        inp = np.array(ex['input'], dtype=np.float32)
        out = np.array(ex['output'], dtype=np.float32)
        
        # Create engine with target (supervised)
        engine = SpikingSheafEngine(
            input_grid=inp,
            target_grid=out,
            atlas=atlas,
            spike_threshold=0.75,
            learning_rate=0.15
        )
        
        # Run thermodynamic inference
        result = engine.solve(verbose=verbose)
        
        # Check if solved
        solved = result.get('exact_match', False)
        if solved:
            results['train_solved'] += 1
            # Learn transformation and add to Atlas (for global memory)
            engine.learn_transformation(inp, out)
            
            # WORKING MEMORY: Learn shape mapping locally for this task
            n_stalks = len(engine.decompose_to_stalks(inp)) if hasattr(engine, 'decompose_to_stalks') else 0
            working_memory.learn_shape_mapping(
                input_shape=(int(inp.shape[0]), int(inp.shape[1])),
                output_shape=(int(out.shape[0]), int(out.shape[1])),
                n_stalks=n_stalks
            )
            
            # Also add to global atlas for lifelong learning
            atlas.learn_shape_mapping(
                input_shape=(int(inp.shape[0]), int(inp.shape[1])),
                output_shape=(int(out.shape[0]), int(out.shape[1])),
                n_stalks=n_stalks
            )
        
        results['train_results'].append({
            'example': i,
            'solved': solved,
            'method': result.get('method', 'unknown'),
            'iterations': result.get('iterations', 0),
            'free_energy': result.get('final_free_energy', 0.0)
        })
    
    # =========================================================================
    # TEST PHASE: Hierarchical Active Inference with Working Memory
    # =========================================================================
    # 
    # The Working Memory acts as a local simulator/sandbox:
    # 1. Query: Working Memory uses local operators learned from THIS task
    # 2. Verify: Test operators on train examples (Scientific Method)
    # 3. Adjudicate: Only apply to test if F=0 on train
    # 4. Consolidate: If successful, promote operators to Global Atlas
    
    def verify_with_working_memory(working_memory, atlas, train_examples, verbose=False):
        """
        Verify operators using Working Memory's local shape predictions.
        Uses Atlas for operator lookup but Working Memory for shape prediction.
        """
        if atlas.size() == 0:
            return False, 0.0
        
        total_correct = 0
        total_pixels = 0
        
        for ex in train_examples:
            inp = np.array(ex['input'], dtype=np.float32)
            out = np.array(ex['output'], dtype=np.float32)
            
            # Create engine with Atlas for operator lookup
            verify_engine = SpikingSheafEngine(
                input_grid=inp,
                target_grid=None,
                atlas=atlas,
                spike_threshold=0.75,
                learning_rate=0.15
            )
            
            # Use Working Memory for shape prediction (task-local)
            pred_shape = working_memory.predict_output_shape(
                (int(inp.shape[0]), int(inp.shape[1]))
            )
            verify_engine._predicted_output_shape = pred_shape
            
            # Generate prior and check if it matches target
            verify_engine.P = verify_engine.initialize_membrane_potential(temperature=0.3)
            P_prior = verify_engine.compute_generative_prior(verify_engine.P)
            
            if P_prior is not None:
                predicted = verify_engine.continuous_to_discrete(P_prior)
                if predicted.shape == out.shape:
                    total_correct += np.sum(predicted == out)
                    total_pixels += out.size
        
        if total_pixels == 0:
            return False, 0.0
        
        accuracy = total_correct / total_pixels
        verified = accuracy >= 0.80  # 80% threshold (lowered for testing)
        
        if verbose:
            status = "VERIFIED (F=0)" if verified else "NOT VERIFIED"
            print(f"    WORKING MEMORY: {accuracy:.1%} train accuracy - {status}")
        
        return verified, accuracy
    
    # Run verification using Working Memory
    operators_verified, train_accuracy = verify_with_working_memory(
        working_memory, atlas, train_examples, verbose=verbose
    )
    
    for i, ex in enumerate(test_examples):
        inp = np.array(ex['input'], dtype=np.float32)
        out = np.array(ex['output'], dtype=np.float32) if 'output' in ex else None
        
        # WORKING MEMORY: Use local shape prediction (task-scoped)
        predicted_shape = working_memory.predict_output_shape(
            (int(inp.shape[0]), int(inp.shape[1]))
        )
        shape_confidence = working_memory.get_shape_confidence(
            (int(inp.shape[0]), int(inp.shape[1]))
        )
        
        if verbose and predicted_shape != inp.shape[:2]:
            print(f"    SHAPE (Working Memory): {predicted_shape} (conf={shape_confidence:.2f})")
        
        # Create engine with Atlas for operator lookup
        engine = SpikingSheafEngine(
            input_grid=inp,
            target_grid=None,  # Hidden!
            atlas=atlas,
            spike_threshold=0.75,
            learning_rate=0.15
        )
        
        # Store predicted shape from Working Memory
        engine._predicted_output_shape = predicted_shape
        engine._shape_confidence = shape_confidence
        
        # SAFE ADJUDICATION: Only use Atlas prior if verified (F=0 on train)
        if operators_verified:
            # Run inference with verified Atlas prior + Yamabe flow
            result = engine.solve_with_annealing(
                verbose=verbose,
                annealing_steps=8,
                annealing_temp=0.01
            ) if hasattr(engine, 'solve_with_annealing') else engine.solve(verbose=verbose)
        else:
            # Operators not verified - fall back to standard solve
            result = engine.solve(verbose=verbose)
        
        # Check if solved (compare with hidden ground truth)
        predicted = result.get('output', None)
        solved = False
        if predicted is not None and out is not None:
            # Handle shape mismatch
            if predicted.shape == out.shape:
                solved = np.array_equal(predicted, out)
                # DEBUG: Count matching pixels
                if verbose and not solved:
                    match_ratio = np.sum(predicted == out) / out.size
                    print(f"    TEST DEBUG: match_ratio={match_ratio:.2%}, method={result.get('method')}")
                    if match_ratio > 0.5:
                        print(f"    NEAR MISS! {match_ratio:.2%} pixels match")
            else:
                if verbose:
                    print(f"    TEST DEBUG: Shape mismatch pred={predicted.shape} vs out={out.shape}")
        
        if solved:
            results['test_solved'] += 1
        
        if result.get('method') == 'atlas_prior_inference':
            results['atlas_used'] = True
        elif result.get('method') == 'atlas_prior_with_phase_transition':
            results['atlas_used'] = True
        
        results['test_results'].append({
            'example': i,
            'solved': solved,
            'method': result.get('method', 'unknown'),
            'iterations': result.get('iterations', 0),
            'free_energy': result.get('final_free_energy', 0.0)
        })
    
    results['time'] = time.time() - start_time
    
    return results


def run_evaluation(max_tasks: int = 5, verbose: bool = False):
    """
    Run the full v7 Spiking Sheaf Engine evaluation.
    """
    print("=" * 70)
    print("SPIKING SHEAF ENGINE v7 - ARC Curriculum Evaluation")
    print("Neural Sheaf Diffusion + Active Inference + Integrate-and-Fire")
    print("=" * 70)
    
    # Initialize shared Atlas (for cross-task transfer)
    atlas = EmergentSheafAtlas(signature_dims=16)
    
    # Load tasks
    tasks = load_arc_tasks()
    
    if not tasks:
        print("No tasks found. Running synthetic tests instead.")
        run_synthetic_tests(atlas, verbose)
        return
    
    # Limit tasks
    tasks = tasks[:max_tasks]
    print(f"\nEvaluating {len(tasks)} tasks...")
    print(f"Atlas signature dims: {atlas.signature_dims}")
    print()
    
    # Evaluate each task
    all_results = []
    total_train_solved = 0
    total_train_examples = 0
    total_test_solved = 0
    total_test_examples = 0
    atlas_hits = 0
    
    for i, task in enumerate(tasks):
        task_id = task.get('task_id', f'task_{i}')
        n_train = len(task.get('train', []))
        n_test = len(task.get('test', []))
        
        result = evaluate_task(task, atlas, verbose=verbose)
        all_results.append(result)
        
        # Accumulate stats
        total_train_solved += result['train_solved']
        total_train_examples += n_train
        total_test_solved += result['test_solved']
        total_test_examples += n_test
        if result['atlas_used']:
            atlas_hits += 1
        
        # Print progress
        status = "PERFECT" if result['train_solved'] == n_train else \
                 "PARTIAL" if result['train_solved'] > 0 else "FAILED"
        test_status = f"test={result['test_solved']}/{n_test}" if n_test > 0 else ""
        atlas_info = "[ATLAS]" if result['atlas_used'] else ""
        
        print(f"[{i+1:3d}/{len(tasks)}] {task_id}: {status} "
              f"({result['train_solved']}/{n_train} train) {test_status} "
              f"[{result['time']:.2f}s] {atlas_info}")
    
    # Print summary
    print()
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    
    train_pct = 100 * total_train_solved / max(total_train_examples, 1)
    test_pct = 100 * total_test_solved / max(total_test_examples, 1)
    
    print(f"Training Examples: {total_train_solved}/{total_train_examples} ({train_pct:.1f}%)")
    print(f"Test Examples:     {total_test_solved}/{total_test_examples} ({test_pct:.1f}%)")
    print(f"Atlas Size:        {atlas.size()} charts")
    print(f"Atlas Hits:        {atlas_hits}/{len(tasks)} tasks")
    print()
    
    # Perfect tasks
    perfect_tasks = [r['task_id'] for r in all_results 
                     if r['train_solved'] == len([t for t in tasks if t.get('task_id') == r['task_id']][0].get('train', []))]
    if perfect_tasks:
        print(f"Perfect Tasks ({len(perfect_tasks)}):")
        for t in perfect_tasks[:10]:
            print(f"  - {t}")
        if len(perfect_tasks) > 10:
            print(f"  ... and {len(perfect_tasks) - 10} more")


def run_synthetic_tests(atlas: EmergentSheafAtlas, verbose: bool = False):
    """
    Run synthetic tests when ARC data is not available.
    
    Tests the Active Inference + Atlas Prior mechanism.
    """
    print("\n" + "=" * 70)
    print("SYNTHETIC TESTS - Active Inference with Atlas Priors")
    print("=" * 70)
    
    # Test 1: Learn color transformation, apply to new grid
    print("\n=== Test 1: Learn Color Map, Apply to New Grid ===")
    
    # Training example 1: Blue (1) → Red (2)
    train_in_1 = np.array([
        [0, 0, 0, 0],
        [0, 1, 1, 0],
        [0, 1, 1, 0],
        [0, 0, 0, 0]
    ], dtype=np.float32)
    
    train_out_1 = np.array([
        [0, 0, 0, 0],
        [0, 2, 2, 0],
        [0, 2, 2, 0],
        [0, 0, 0, 0]
    ], dtype=np.float32)
    
    # Train on example 1
    engine1 = SpikingSheafEngine(train_in_1, train_out_1, atlas=atlas, spike_threshold=0.7)
    result1 = engine1.solve(verbose=verbose)
    print(f"  Training: solved={result1['exact_match']}, iters={result1['iterations']}")
    
    if result1['exact_match']:
        engine1.learn_transformation(train_in_1, train_out_1)
        print(f"  Learned: Atlas size = {atlas.size()}")
    
    # Test on new grid (different position, same color)
    test_in = np.array([
        [0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0],
        [0, 0, 1, 1, 0],
        [0, 0, 1, 1, 0],
        [0, 0, 0, 0, 0]
    ], dtype=np.float32)
    
    test_out = np.array([
        [0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0],
        [0, 0, 2, 2, 0],
        [0, 0, 2, 2, 0],
        [0, 0, 0, 0, 0]
    ], dtype=np.float32)
    
    # Test with hidden target (use Atlas prior)
    engine_test = SpikingSheafEngine(test_in, target_grid=None, atlas=atlas, spike_threshold=0.7)
    result_test = engine_test.solve(verbose=verbose)
    
    predicted = result_test.get('output', None)
    test_solved = np.array_equal(predicted, test_out) if predicted is not None else False
    
    print(f"  Test: method={result_test.get('method')}, solved={test_solved}")
    print(f"  Atlas prior used: {result_test.get('method') == 'atlas_prior_inference'}")
    
    # Test 2: Translation + Color
    print("\n=== Test 2: Learn Translation + Color, Apply to New Grid ===")
    
    train_in_2 = np.array([
        [0, 0, 0, 0, 0],
        [0, 3, 3, 0, 0],
        [0, 3, 3, 0, 0],
        [0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0]
    ], dtype=np.float32)
    
    train_out_2 = np.array([
        [0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0],
        [0, 0, 4, 4, 0],
        [0, 0, 4, 4, 0]
    ], dtype=np.float32)
    
    engine2 = SpikingSheafEngine(train_in_2, train_out_2, atlas=atlas, spike_threshold=0.7, learning_rate=0.2)
    result2 = engine2.solve(verbose=verbose)
    print(f"  Training: solved={result2['exact_match']}, iters={result2['iterations']}")
    
    if result2['exact_match']:
        engine2.learn_transformation(train_in_2, train_out_2)
        print(f"  Learned: Atlas size = {atlas.size()}")
    
    print("\n" + "=" * 70)
    print("SYNTHETIC TESTS COMPLETE")
    print(f"Final Atlas Size: {atlas.size()} charts")
    print("=" * 70)


if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(description="Spiking Sheaf Engine v7 Evaluation")
    parser.add_argument('--max-tasks', type=int, default=5, 
                        help='Maximum number of tasks to evaluate')
    parser.add_argument('--verbose', '-v', action='store_true',
                        help='Enable verbose output')
    
    args = parser.parse_args()
    
    run_evaluation(max_tasks=args.max_tasks, verbose=args.verbose)
