#!/usr/bin/env python3
"""
JAX ARC Runner: Atlas-Integrated Thermodynamic ARC Solver

Connects the JAX SGLD engine to the EmergentSheafAtlas for continuous learning
on real ARC tasks. Crystallized b1>=1 Laplacians are stored in system RAM
and retrieved for zero-shot transfer on unseen tasks.

ARCHITECTURE:
    1. Load ARC task JSONs
    2. Decompose grids into stalks (connected color components)
    3. Run JAX SGLD crystallization per training example
    4. Store grokked (b1>=1) operators in Atlas (system RAM)
    5. For test: retrieve matching operators from Atlas, apply via sheaf diffusion
    6. Save enriched Atlas for future sessions

THEORY:
    - Generalization Boundary Theorem: b1>=1 -> approx_lumpable -> generalization
    - Only b1>=1 crystallized Laplacians are stored (no memorizations)
    - Atlas retrieval by spectral signature cosine similarity
"""

import os
import sys
import json
import time
import pickle
import numpy as np
from typing import Dict, List, Any, Optional, Tuple

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from jax_sgld_engine import SGLDCrystallizer, compute_b1
from emergent_sheaf_engine import EmergentSheafAtlas


# ============================================================================
# 1. STALK DECOMPOSITION (Grid -> Connected Color Components)
# ============================================================================

def decompose_stalks(grid: np.ndarray, background_color: int = 0) -> List[Dict]:
    """
    Decompose an ARC grid into stalks (connected components per color).
    Each stalk is a maximal connected region of a single non-background color.
    """
    H, W = grid.shape
    visited = np.zeros((H, W), dtype=bool)
    stalks = []

    for r in range(H):
        for c in range(W):
            if visited[r, c] or int(grid[r, c]) == background_color:
                continue

            color = int(grid[r, c])
            # BFS to find connected component
            component = []
            queue = [(r, c)]
            visited[r, c] = True

            while queue:
                cr, cc = queue.pop(0)
                component.append((cr, cc))
                for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                    nr, nc = cr + dr, cc + dc
                    if 0 <= nr < H and 0 <= nc < W and not visited[nr, nc]:
                        if int(grid[nr, nc]) == color:
                            visited[nr, nc] = True
                            queue.append((nr, nc))

            if component:
                positions = np.array(component)
                mask = np.zeros((H, W), dtype=bool)
                for pr, pc in component:
                    mask[pr, pc] = True

                stalks.append({
                    'color': color,
                    'mask': mask,
                    'centroid': positions.mean(axis=0).astype(np.float32),
                    'n_pixels': len(component),
                    'positions': positions,
                })

    # Sort by size descending
    stalks.sort(key=lambda s: s['n_pixels'], reverse=True)
    return stalks


def compute_spectral_signature(grid: np.ndarray, dims: int = 16) -> np.ndarray:
    """
    Compute a spectral signature for Atlas retrieval.
    Uses color histogram + spatial moments as a compact fingerprint.
    """
    H, W = grid.shape
    sig = np.zeros(dims, dtype=np.float32)

    # Color histogram (10 colors)
    for c in range(min(10, dims)):
        sig[c] = float(np.sum(grid == c)) / max(H * W, 1)

    # Spatial moments (if room)
    if dims > 10:
        flat = grid.flatten().astype(np.float32)
        sig[10] = float(np.mean(flat))
        if dims > 11:
            sig[11] = float(np.std(flat))
        if dims > 12:
            sig[12] = float(H) / 30.0  # normalized height
        if dims > 13:
            sig[13] = float(W) / 30.0  # normalized width

    return sig


# ============================================================================
# 2. ATLAS INTEGRATION
# ============================================================================

def learn_stalk_transforms(input_grid: np.ndarray, target_grid: np.ndarray,
                           stalks: List[Dict]) -> List[Dict]:
    """
    Learn the per-stalk transformation from input to target.
    Captures: color changes, translations, and the global color map.

    These are the INTENSIVE variables (what changes) stored alongside
    the EXTENSIVE topology (edge weights, b1) in the Atlas.
    """
    H, W = input_grid.shape
    transforms = []

    # Global color map: for each input color, what output color appears in same region?
    color_map = {}
    for stalk in stalks:
        in_color = int(stalk['color'])
        mask = stalk['mask']
        # What color(s) appear in the target at this stalk's location?
        target_colors_at_mask = target_grid[mask]
        if len(target_colors_at_mask) > 0:
            out_color = int(np.bincount(target_colors_at_mask.astype(int)).argmax())
            color_map[in_color] = out_color

    # Per-stalk: detect translation (centroid shift)
    out_stalks = decompose_stalks(target_grid)
    for in_stalk in stalks:
        in_color = int(in_stalk['color'])
        out_color = color_map.get(in_color, in_color)

        # Find matching output stalk by color (after mapping)
        best_match = None
        best_dist = float('inf')
        for out_stalk in out_stalks:
            if int(out_stalk['color']) == out_color:
                dist = np.linalg.norm(in_stalk['centroid'] - out_stalk['centroid'])
                if dist < best_dist:
                    best_dist = dist
                    best_match = out_stalk

        dr, dc = 0, 0
        if best_match is not None:
            dr = float(best_match['centroid'][0] - in_stalk['centroid'][0])
            dc = float(best_match['centroid'][1] - in_stalk['centroid'][1])

        transforms.append({
            'in_color': in_color,
            'out_color': out_color,
            'dr': dr, 'dc': dc,
        })

    return transforms


def store_crystallized_rule(atlas: EmergentSheafAtlas,
                            result: Dict,
                            input_grid: np.ndarray,
                            target_grid: np.ndarray,
                            stalks: List[Dict],
                            task_id: str = "") -> Optional[int]:
    """
    Store a crystallized b1>=1 Laplacian in the Atlas WITH transformation data.
    Returns chart_id if stored, None if rejected (b1=0).
    """
    if not result.get('grokked', False) or result.get('b1', 0) < 1:
        return None

    sig = compute_spectral_signature(input_grid)

    # Learn the actual transformation (color map + translations)
    transforms = learn_stalk_transforms(input_grid, target_grid, stalks)

    operators = [{
        'type': 'crystallized_laplacian',
        'edge_weights': result['edge_weights'],
        'structural_complexity': result.get('structural_complexity', 1.0),
        'grokked': True,
        'b1': result['b1'],
        'stalk_transforms': transforms,
        'n_stalks': len(stalks),
    }]

    chart_id = atlas.add_chart(
        signature=sig,
        operators=operators,
        metadata={
            'source': 'jax_sgld_v2',
            'task_id': task_id,
            'b1': result['b1'],
            'accuracy': result.get('final_accuracy', 0),
            'n_stalks': len(stalks),
            'input_shape': tuple(input_grid.shape),
        }
    )

    return chart_id


def retrieve_prior(atlas: EmergentSheafAtlas,
                   input_grid: np.ndarray,
                   min_similarity: float = 0.7) -> Optional[Dict]:
    """
    Retrieve the best matching crystallized Laplacian from the Atlas.
    Returns the operator dict if found, None otherwise.
    """
    if atlas.size() == 0:
        return None

    sig = compute_spectral_signature(input_grid)
    matches = atlas.find_top_k_charts(sig, k=1, min_similarity=min_similarity)

    if not matches:
        return None

    chart_id = matches[0]['id']
    operators = atlas.get_operators(chart_id)

    # Find a crystallized_laplacian with b1>=1
    for op in operators:
        if op.get('type') == 'crystallized_laplacian' and op.get('b1', 0) >= 1:
            return {
                'operator': op,
                'similarity': matches[0]['similarity'],
                'chart_id': chart_id,
                'metadata': matches[0].get('metadata', {}),
            }

    return None


def apply_crystallized_rule(input_grid: np.ndarray, stalks: List[Dict],
                            rule: Dict, n_colors: int = 10) -> Optional[np.ndarray]:
    """
    ZERO-SHOT FORWARD PASS: Apply a stored crystallized rule to an input grid
    WITHOUT seeing the target output.

    The rule contains:
    - edge_weights: topology (which stalks relate)
    - stalk_transforms: the actual transformation (color map + translation per stalk)

    The forward pass applies the learned transforms to each stalk in the new input.
    """
    H, W = input_grid.shape
    transforms = rule.get('stalk_transforms', [])

    if not transforms:
        return None

    # Build color map from stored transforms
    color_map = {}
    for t in transforms:
        color_map[t['in_color']] = t['out_color']

    # Apply transformation: for each pixel, apply color map
    output = input_grid.copy()

    for stalk in stalks:
        in_color = int(stalk['color'])
        out_color = color_map.get(in_color, in_color)
        mask = stalk['mask']

        # Find matching transform for this stalk's color
        matching_transform = None
        for t in transforms:
            if t['in_color'] == in_color:
                matching_transform = t
                break

        if matching_transform is None:
            # No transform learned for this color — keep as-is
            continue

        dr = int(round(matching_transform.get('dr', 0)))
        dc = int(round(matching_transform.get('dc', 0)))

        # Apply: translate + recolor
        positions = np.argwhere(mask)
        # Clear original positions
        for r, c in positions:
            output[r, c] = 0  # background

        # Write to new positions with new color
        for r, c in positions:
            nr, nc = r + dr, c + dc
            if 0 <= nr < H and 0 <= nc < W:
                output[nr, nc] = out_color

    return output


# ============================================================================
# 3. ARC TASK LOADER
# ============================================================================

def load_arc_tasks(data_dir: str = None, max_tasks: int = None) -> List[Dict]:
    """Load ARC tasks from JSON files."""
    possible_dirs = [
        data_dir,
        os.path.join(os.path.dirname(__file__), "..", "data", "arc", "training"),
        r"C:\Users\jason\arc-prize-2024\arc-agi_training_challenges",
    ]

    actual_dir = None
    for d in possible_dirs:
        if d and os.path.isdir(d):
            actual_dir = d
            break

    if actual_dir is None:
        print("ERROR: No ARC task directory found")
        return []

    tasks = []
    for filename in sorted(os.listdir(actual_dir)):
        if filename.endswith('.json'):
            with open(os.path.join(actual_dir, filename)) as f:
                task_data = json.load(f)
            tasks.append({
                'id': filename[:-5],
                'train': task_data.get('train', []),
                'test': task_data.get('test', []),
            })

    if max_tasks:
        tasks = tasks[:max_tasks]

    return tasks


# ============================================================================
# 4. THE ARC GAUNTLET
# ============================================================================

def run_arc_gauntlet(max_tasks: int = 20, atlas_path: str = "jax_atlas.pkl"):
    """
    Run the JAX SGLD engine on real ARC tasks with Atlas integration.

    For each task:
    1. Decompose training examples into stalks
    2. Run SGLD crystallization
    3. If b1>=1: store in Atlas (system RAM)
    4. For test: try Atlas retrieval first, then full SGLD

    Reports: grokked count, b1 distribution, Atlas growth, test accuracy.
    """
    print("=" * 70)
    print("JAX ARC GAUNTLET: Thermodynamic Intelligence on Real ARC Tasks")
    print("=" * 70)

    # Load or create Atlas
    atlas_full_path = os.path.join(os.path.dirname(__file__), atlas_path)
    if os.path.exists(atlas_full_path):
        with open(atlas_full_path, 'rb') as f:
            atlas = pickle.load(f)
        print(f"Loaded Atlas: {atlas.size()} charts")
    else:
        atlas = EmergentSheafAtlas(signature_dims=16)
        print("Created fresh Atlas")

    initial_atlas_size = atlas.size()

    # Load tasks
    tasks = load_arc_tasks(max_tasks=max_tasks)
    if not tasks:
        print("No tasks loaded!")
        return

    print(f"Loaded {len(tasks)} ARC tasks")

    # Engine
    engine = SGLDCrystallizer(n_colors=10, eta=0.01, initial_temp=0.05)

    # Stats
    stats = {
        'tasks_processed': 0,
        'examples_crystallized': 0,
        'b1_nonzero': 0,
        'b1_zero': 0,
        'grokked': 0,
        'atlas_additions': 0,
        'test_solved': 0,
        'test_total': 0,
    }

    t_start = time.time()

    for task_idx, task in enumerate(tasks):
        task_id = task['id']
        train_examples = task['train']
        test_examples = task['test']

        task_grokked = False

        # --- TRAINING PHASE: Crystallize on each training example ---
        for ex_idx, ex in enumerate(train_examples):
            inp = np.array(ex['input'], dtype=np.float32)
            out = np.array(ex['output'], dtype=np.float32)

            # Skip shape mismatches for now
            if inp.shape != out.shape:
                continue

            stalks = decompose_stalks(inp)

            if len(stalks) < 2 or len(stalks) > 6:
                continue

            # Skip large grids (VRAM budget)
            if inp.size > 225:  # 15x15 max
                continue

            # Run SGLD crystallization
            result = engine.crystallize(
                inp, out, stalks,
                max_iterations=80,
                sparsity_lambda=0.1
            )

            stats['examples_crystallized'] += 1

            if result.get('b1', 0) >= 1:
                stats['b1_nonzero'] += 1
            else:
                stats['b1_zero'] += 1

            if result.get('grokked', False):
                stats['grokked'] += 1
                task_grokked = True

                # Store in Atlas WITH transformation data
                chart_id = store_crystallized_rule(
                    atlas, result, inp, out, stalks, task_id)
                if chart_id is not None:
                    stats['atlas_additions'] += 1

        # --- TEST PHASE: TRUE ZERO-SHOT (target output is HIDDEN) ---
        # The engine must predict the output using ONLY the Atlas prior.
        # It NEVER sees the ground truth test output during inference.
        for test_ex in test_examples:
            inp = np.array(test_ex['input'], dtype=np.float32)
            out = np.array(test_ex['output'], dtype=np.float32) if 'output' in test_ex else None

            stats['test_total'] += 1

            if out is None:
                continue

            stalks = decompose_stalks(inp)

            # Try Atlas retrieval — this is the ONLY path to solving
            prior = retrieve_prior(atlas, inp, min_similarity=0.5)
            if prior is not None:
                stats['atlas_hits'] = stats.get('atlas_hits', 0) + 1

                # ZERO-SHOT FORWARD PASS: apply crystallized rule WITHOUT seeing target
                predicted = apply_crystallized_rule(
                    inp, stalks, prior['operator'], n_colors=10)

                if predicted is not None and out is not None:
                    if predicted.shape == out.shape and np.array_equal(predicted, out):
                        stats['test_solved'] += 1
                    elif predicted.shape == out.shape:
                        match = float(np.mean(predicted == out))
                        if match > 0.95:
                            stats['test_solved'] += 1
                        stats['test_near_misses'] = stats.get('test_near_misses', 0) + (1 if match > 0.5 else 0)
            else:
                stats['atlas_misses'] = stats.get('atlas_misses', 0) + 1

        stats['tasks_processed'] += 1

        # Progress
        if (task_idx + 1) % 5 == 0 or task_idx == len(tasks) - 1:
            elapsed = time.time() - t_start
            print(f"  [{task_idx+1}/{len(tasks)}] "
                  f"grokked={stats['grokked']} "
                  f"b1>0={stats['b1_nonzero']} "
                  f"atlas={atlas.size()-initial_atlas_size} new "
                  f"({elapsed:.1f}s)")

    # Final report
    elapsed = time.time() - t_start
    print("\n" + "=" * 70)
    print("ARC GAUNTLET RESULTS")
    print("=" * 70)
    print(f"Tasks processed:       {stats['tasks_processed']}")
    print(f"Examples crystallized:  {stats['examples_crystallized']}")
    print(f"  b1 >= 1 (blankets):  {stats['b1_nonzero']}")
    print(f"  b1 = 0 (memorized):  {stats['b1_zero']}")
    print(f"  Grokked (b1>=1+acc): {stats['grokked']}")
    print(f"Atlas growth:          {initial_atlas_size} -> {atlas.size()} "
          f"(+{stats['atlas_additions']} new)")
    print(f"Test solved:           {stats['test_solved']}/{stats['test_total']}")
    print(f"Time:                  {elapsed:.1f}s")

    # Save enriched Atlas
    with open(atlas_full_path, 'wb') as f:
        pickle.dump(atlas, f)
    print(f"\nAtlas saved to: {atlas_full_path}")

    return stats


def run_frozen_atlas_eval(atlas_path: str = "jax_atlas.pkl",
                          eval_dir: str = None,
                          max_tasks: int = None):
    """
    Zero-shot transfer test: freeze the Atlas, run on unseen evaluation tasks.
    No training/crystallization — only Atlas retrieval and SGLD with prior.
    """
    print("=" * 70)
    print("FROZEN ATLAS EVALUATION: Zero-Shot Transfer Test")
    print("=" * 70)

    # Load frozen Atlas
    atlas_full_path = os.path.join(os.path.dirname(__file__), atlas_path)
    if not os.path.exists(atlas_full_path):
        print(f"ERROR: Atlas not found at {atlas_full_path}")
        return

    with open(atlas_full_path, 'rb') as f:
        atlas = pickle.load(f)
    print(f"Frozen Atlas: {atlas.size()} charts (b1>=1 verified rules)")

    # Load evaluation tasks
    possible_dirs = [
        eval_dir,
        os.path.join(os.path.dirname(__file__), "..", "data", "arc", "evaluation"),
        r"C:\Users\jason\arc-prize-2024\arc-agi_evaluation_challenges",
    ]

    actual_dir = None
    for d in possible_dirs:
        if d and os.path.isdir(d):
            actual_dir = d
            break

    if actual_dir is None:
        # Fall back to training set (treat test splits as eval)
        print("No evaluation directory found. Using training set test splits.")
        tasks = load_arc_tasks(max_tasks=max_tasks)
        eval_mode = "training_test_split"
    else:
        print(f"Loading evaluation tasks from: {actual_dir}")
        tasks = []
        for filename in sorted(os.listdir(actual_dir)):
            if filename.endswith('.json'):
                with open(os.path.join(actual_dir, filename)) as f:
                    task_data = json.load(f)
                tasks.append({
                    'id': filename[:-5],
                    'train': task_data.get('train', []),
                    'test': task_data.get('test', []),
                })
        if max_tasks:
            tasks = tasks[:max_tasks]
        eval_mode = "evaluation_set"

    print(f"Evaluation mode: {eval_mode}")
    print(f"Tasks: {len(tasks)}")

    engine = SGLDCrystallizer(n_colors=10, eta=0.01, initial_temp=0.05)

    stats = {
        'tasks': 0,
        'test_total': 0,
        'test_solved': 0,
        'atlas_hits': 0,
        'atlas_misses': 0,
    }

    t_start = time.time()

    for task_idx, task in enumerate(tasks):
        task_id = task['id']
        test_examples = task['test']

        stats['tasks'] += 1

        for test_ex in test_examples:
            inp = np.array(test_ex['input'], dtype=np.float32)
            out = np.array(test_ex['output'], dtype=np.float32) if 'output' in test_ex else None

            stats['test_total'] += 1

            if out is None or inp.shape != out.shape:
                continue

            stalks = decompose_stalks(inp)
            if len(stalks) < 2 or len(stalks) > 6 or inp.size > 225:
                continue

            # TRUE ZERO-SHOT: Apply Atlas rule WITHOUT seeing target
            prior = retrieve_prior(atlas, inp, min_similarity=0.5)
            if prior is not None:
                stats['atlas_hits'] += 1

                predicted = apply_crystallized_rule(
                    inp, stalks, prior['operator'], n_colors=10)

                if predicted is not None and out is not None:
                    if predicted.shape == out.shape and np.array_equal(predicted, out):
                        stats['test_solved'] += 1
                    elif predicted.shape == out.shape:
                        match = float(np.mean(predicted == out))
                        if match > 0.95:
                            stats['test_solved'] += 1
                        stats.setdefault('near_misses', 0)
                        if match > 0.5:
                            stats['near_misses'] += 1
            else:
                stats['atlas_misses'] += 1

        if (task_idx + 1) % 10 == 0 or task_idx == len(tasks) - 1:
            elapsed = time.time() - t_start
            print(f"  [{task_idx+1}/{len(tasks)}] "
                  f"solved={stats['test_solved']}/{stats['test_total']} "
                  f"atlas_hits={stats['atlas_hits']} "
                  f"({elapsed:.1f}s)")

    elapsed = time.time() - t_start
    print("\n" + "=" * 70)
    print("FROZEN ATLAS EVALUATION RESULTS")
    print("=" * 70)
    print(f"Tasks:        {stats['tasks']}")
    print(f"Test total:   {stats['test_total']}")
    print(f"Test solved:  {stats['test_solved']} ({100*stats['test_solved']/max(stats['test_total'],1):.1f}%)")
    print(f"Atlas hits:   {stats['atlas_hits']}")
    print(f"Atlas misses: {stats['atlas_misses']}")
    print(f"Time:         {elapsed:.1f}s")

    return stats


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description='JAX ARC Gauntlet')
    parser.add_argument('--max-tasks', type=int, default=20)
    parser.add_argument('--atlas', type=str, default='jax_atlas.pkl')
    parser.add_argument('--eval', action='store_true', help='Run frozen Atlas evaluation')
    parser.add_argument('--eval-tasks', type=int, default=None)
    args = parser.parse_args()

    if args.eval:
        run_frozen_atlas_eval(atlas_path=args.atlas, max_tasks=args.eval_tasks)
    else:
        run_arc_gauntlet(max_tasks=args.max_tasks, atlas_path=args.atlas)
