"""
ARC-SGC Diagnostic: Understand why performance is dropping

This script runs the solvers with detailed logging to understand:
1. Which tasks are being solved by which method
2. Why some tasks that were solved before are now failing
3. The energy distribution across examples per task
"""

import torch
from dataclasses import dataclass
from typing import List, Tuple, Dict
from collections import Counter
import numpy as np
from pathlib import Path
import sys
import time

sys.path.insert(0, str(Path(__file__).parent))
from arc_sgc_phase8_3 import (
    ARCPhase83Config, ARCGrid, ARCExample, ARCTask,
    load_arc_tasks, compute_defect_energy,
    GeometryFirstSolver, CompositePotential, relax_all_colors,
    V_ContactDist, V_TopEdge, V_BottomEdge, V_BoundaryDist,
    CropToContentMorphism, ExtractObjectMorphism
)

def printfl(*args, **kwargs):
    print(*args, **kwargs)
    sys.stdout.flush()


def diagnose_task(task: ARCTask, config: ARCPhase83Config) -> Dict:
    """
    Diagnose a single task with detailed logging.
    """
    examples = task.train_examples
    n_examples = len(examples)
    
    result = {
        'task_id': task.task_id,
        'n_examples': n_examples,
        'methods_tried': [],
        'best_method': 'none',
        'best_energy': float('inf'),
        'per_example_energies': [],
        'consistency': False,  # Does the best method work for ALL examples?
    }
    
    # Test 1: Identity
    energies = []
    valid = True
    for ex in examples:
        if ex.input_grid.shape != ex.output_grid.shape:
            valid = False
            break
        e = compute_defect_energy(ex.input_grid, ex.output_grid)
        energies.append(e)
    
    if valid:
        avg_e = sum(energies) / len(energies)
        max_e = max(energies)
        result['methods_tried'].append(('identity', avg_e, energies))
        if avg_e < result['best_energy']:
            result['best_energy'] = avg_e
            result['best_method'] = 'identity'
            result['per_example_energies'] = energies
            result['consistency'] = max_e < config.energy_threshold
    
    # Test 2: Movement potentials
    potentials = [V_ContactDist(), V_TopEdge(), V_BottomEdge(), V_BoundaryDist()]
    for i, pot in enumerate(potentials):
        for sign in [-1.0, 1.0]:
            for strength in [0.5, 1.0, 1.5]:
                weights = np.zeros(4)
                weights[i] = sign * strength
                potential = CompositePotential(potentials, weights)
                
                energies = []
                valid = True
                for ex in examples:
                    try:
                        res = relax_all_colors(ex.input_grid, potential, config)
                        if res.shape != ex.output_grid.shape:
                            valid = False
                            break
                        e = compute_defect_energy(res, ex.output_grid)
                        energies.append(e)
                    except:
                        valid = False
                        break
                
                if valid:
                    avg_e = sum(energies) / len(energies)
                    method_name = f"move:{sign*strength:+.1f}*{pot.name()}"
                    result['methods_tried'].append((method_name, avg_e, energies))
                    if avg_e < result['best_energy']:
                        result['best_energy'] = avg_e
                        result['best_method'] = method_name
                        result['per_example_energies'] = energies
                        result['consistency'] = max(energies) < config.energy_threshold
    
    # Test 3: Crop to content
    try:
        morph = CropToContentMorphism()
        energies = []
        valid = True
        for ex in examples:
            res = morph.apply(ex.input_grid, config)
            if res.shape != ex.output_grid.shape:
                valid = False
                break
            e = compute_defect_energy(res, ex.output_grid)
            energies.append(e)
        
        if valid:
            avg_e = sum(energies) / len(energies)
            result['methods_tried'].append(('crop_to_content', avg_e, energies))
            if avg_e < result['best_energy']:
                result['best_energy'] = avg_e
                result['best_method'] = 'crop_to_content'
                result['per_example_energies'] = energies
                result['consistency'] = max(energies) < config.energy_threshold
    except:
        pass
    
    # Test 4: Extract largest/smallest
    for selector in ['largest', 'smallest']:
        try:
            morph = ExtractObjectMorphism(selector)
            energies = []
            valid = True
            for ex in examples:
                res = morph.apply(ex.input_grid, config)
                if res.shape != ex.output_grid.shape:
                    valid = False
                    break
                e = compute_defect_energy(res, ex.output_grid)
                energies.append(e)
            
            if valid:
                avg_e = sum(energies) / len(energies)
                method_name = f"extract({selector})"
                result['methods_tried'].append((method_name, avg_e, energies))
                if avg_e < result['best_energy']:
                    result['best_energy'] = avg_e
                    result['best_method'] = method_name
                    result['per_example_energies'] = energies
                    result['consistency'] = max(energies) < config.energy_threshold
        except:
            pass
    
    # Test 5: Pattern transforms
    transforms = [
        ('rot90', lambda g: ARCGrid(g.data.rot90(1, [0, 1]))),
        ('rot180', lambda g: ARCGrid(g.data.rot90(2, [0, 1]))),
        ('rot270', lambda g: ARCGrid(g.data.rot90(3, [0, 1]))),
        ('flip_h', lambda g: ARCGrid(g.data.flip(1))),
        ('flip_v', lambda g: ARCGrid(g.data.flip(0))),
    ]
    
    for name, transform in transforms:
        try:
            energies = []
            valid = True
            for ex in examples:
                res = transform(ex.input_grid)
                if res.shape != ex.output_grid.shape:
                    valid = False
                    break
                e = compute_defect_energy(res, ex.output_grid)
                energies.append(e)
            
            if valid:
                avg_e = sum(energies) / len(energies)
                result['methods_tried'].append((name, avg_e, energies))
                if avg_e < result['best_energy']:
                    result['best_energy'] = avg_e
                    result['best_method'] = name
                    result['per_example_energies'] = energies
                    result['consistency'] = max(energies) < config.energy_threshold
        except:
            pass
    
    # Test 6: Shift operations
    for dr in range(-2, 3):
        for dc in range(-2, 3):
            if dr == 0 and dc == 0:
                continue
            
            energies = []
            valid = True
            for ex in examples:
                if ex.input_grid.shape != ex.output_grid.shape:
                    valid = False
                    break
                
                H, W = ex.input_grid.shape
                data = torch.full_like(ex.input_grid.data, config.background_color)
                src_r1, src_r2 = max(0, -dr), min(H, H - dr)
                src_c1, src_c2 = max(0, -dc), min(W, W - dc)
                dst_r1, dst_r2 = max(0, dr), min(H, H + dr)
                dst_c1, dst_c2 = max(0, dc), min(W, W + dc)
                
                if dst_r2 > dst_r1 and dst_c2 > dst_c1:
                    data[dst_r1:dst_r2, dst_c1:dst_c2] = ex.input_grid.data[src_r1:src_r2, src_c1:src_c2]
                
                e = compute_defect_energy(ARCGrid(data), ex.output_grid)
                energies.append(e)
            
            if valid:
                avg_e = sum(energies) / len(energies)
                method_name = f"shift({dr},{dc})"
                result['methods_tried'].append((method_name, avg_e, energies))
                if avg_e < result['best_energy']:
                    result['best_energy'] = avg_e
                    result['best_method'] = method_name
                    result['per_example_energies'] = energies
                    result['consistency'] = max(energies) < config.energy_threshold
    
    return result


def run_diagnostic(data_path: str):
    printfl("=" * 70)
    printfl("ARC-SGC Diagnostic: Understanding Performance Regression")
    printfl("=" * 70)
    
    config = ARCPhase83Config()
    tasks = load_arc_tasks(data_path, 'cpu')
    printfl(f"\nLoaded {len(tasks)} tasks")
    
    all_results = []
    perfect_count = 0
    inconsistent_perfect = 0  # Tasks where avg_energy < threshold but max_energy >= threshold
    
    printfl("\n" + "=" * 50)
    printfl("Per-Task Analysis")
    printfl("=" * 50)
    
    for i, task in enumerate(tasks):
        result = diagnose_task(task, config)
        all_results.append(result)
        
        is_perfect = result['best_energy'] < config.energy_threshold
        
        if is_perfect:
            perfect_count += 1
            
            # Check consistency
            if not result['consistency']:
                inconsistent_perfect += 1
                printfl(f"\n  [INCONSISTENT] {task.task_id}: {result['best_method']}")
                printfl(f"    avg_energy={result['best_energy']:.4f}")
                printfl(f"    per_example={[f'{e:.4f}' for e in result['per_example_energies']]}")
            else:
                printfl(f"  [PERFECT] {task.task_id}: {result['best_method']}")
        
        if (i + 1) % 20 == 0:
            printfl(f"\n  Progress: {i+1}/{len(tasks)}, perfect={perfect_count}, inconsistent={inconsistent_perfect}")
    
    # Summary
    printfl("\n" + "=" * 70)
    printfl("DIAGNOSTIC SUMMARY")
    printfl("=" * 70)
    
    printfl(f"\nResults:")
    printfl(f"  Total perfect (avg_energy < threshold): {perfect_count}")
    printfl(f"  Truly consistent (all examples < threshold): {perfect_count - inconsistent_perfect}")
    printfl(f"  Inconsistent (avg good but some examples bad): {inconsistent_perfect}")
    
    # Method distribution
    method_counts = Counter()
    for r in all_results:
        if r['best_energy'] < config.energy_threshold:
            method_type = r['best_method'].split(':')[0].split('(')[0]
            method_counts[method_type] += 1
    
    printfl(f"\nSolves by method type:")
    for method, count in method_counts.most_common():
        printfl(f"  {method}: {count}")
    
    # Near-misses
    near_misses = [r for r in all_results if 0.0001 < r['best_energy'] < 0.1]
    printfl(f"\nNear-misses (E<0.1): {len(near_misses)}")
    for r in sorted(near_misses, key=lambda x: x['best_energy'])[:10]:
        printfl(f"  {r['task_id']}: E={r['best_energy']:.4f} ({r['best_method']})")
        printfl(f"    per_example={[f'{e:.4f}' for e in r['per_example_energies']]}")
    
    return all_results


def main():
    paths = ["data/arc/training", "C:/Lean4 Projects/data/arc/training"]
    arc_path = next((p for p in paths if Path(p).exists()), None)
    
    if arc_path:
        run_diagnostic(arc_path)
    else:
        printfl("ARC data not found!")


if __name__ == "__main__":
    main()
