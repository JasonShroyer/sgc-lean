"""97-task evaluation of the Thermodynamic Sheaf Engine.

This evaluates the SGC/UPAT theory-derived perception system:
- Spectral Kinematics (Graph Laplacian, Hermite-Gaussian modes)
- Gauge Group Detection (Z2, Zn, C4, Sn)
- Sheaf Atlas Matching Loop (experience-based learning)
- Spectral Regularization (denoise before transform)

Key Hypothesis: The rule IS the ground state.
Direct derivation from spectral structure should outperform stochastic search.

Output: eval_97_thermodynamic_results.csv
"""
import os
import sys
import io
import json
import time
import csv
from pathlib import Path
from typing import Dict, Any, List

os.environ['PYTHONUNBUFFERED'] = '1'
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8',
                               errors='replace', line_buffering=True)

# Tee for logging
class Tee:
    def __init__(self, stdout, log_path):
        self.stdout = stdout
        self.log_file = open(log_path, 'w', encoding='utf-8', buffering=1)
    def write(self, data):
        self.stdout.write(data)
        self.log_file.write(data)
        self.log_file.flush()
    def flush(self):
        self.stdout.flush()
        self.log_file.flush()

LOG_PATH = 'eval_97_thermodynamic.log'
sys.stdout = Tee(sys.stdout, LOG_PATH)

import numpy as np
from thermodynamic_perception import (
    ThermodynamicPerception, 
    SheafAtlas, 
    solve_with_atlas
)


def load_arc_tasks(arc_dir: Path, limit: int = 97) -> List[Dict]:
    """Load ARC training tasks."""
    tasks = []
    task_files = sorted(arc_dir.glob("*.json"))[:limit]
    
    for task_file in task_files:
        with open(task_file) as f:
            task_data = json.load(f)
            task_data['task_id'] = task_file.stem
            tasks.append(task_data)
    
    return tasks


def evaluate_task(task: Dict, atlas: SheafAtlas) -> Dict[str, Any]:
    """Evaluate a single ARC task using the Thermodynamic Sheaf Engine."""
    task_id = task['task_id']
    results = {
        'task_id': task_id,
        'n_train': len(task['train']),
        'n_test': len(task.get('test', [])),
        'train_solved': 0,
        'train_total': 0,
        'test_solved': 0,
        'test_total': 0,
        'gauge_groups_used': [],
        'methods_used': [],
        'errors': []
    }
    
    # Evaluate training examples
    for ex_idx, ex in enumerate(task['train']):
        inp = np.array(ex['input'])
        out = np.array(ex['output'])
        
        if inp.shape != out.shape:
            # Shape change tasks not yet supported
            continue
        
        results['train_total'] += 1
        
        try:
            result = solve_with_atlas(inp, out, atlas, verbose=False)
            
            if result.get('success', False):
                results['train_solved'] += 1
                if 'gauge_group' in result:
                    results['gauge_groups_used'].append(result['gauge_group'])
                if 'method' in result:
                    results['methods_used'].append(result['method'])
        except Exception as e:
            results['errors'].append(str(e))
    
    # Evaluate test examples (if available and training succeeded)
    if results['train_solved'] > 0:
        for ex_idx, ex in enumerate(task.get('test', [])):
            inp = np.array(ex['input'])
            out = np.array(ex['output'])
            
            if inp.shape != out.shape:
                continue
            
            results['test_total'] += 1
            
            try:
                result = solve_with_atlas(inp, out, atlas, verbose=False)
                if result.get('success', False):
                    results['test_solved'] += 1
            except Exception as e:
                results['errors'].append(str(e))
    
    return results


def main():
    print("=" * 70)
    print("THERMODYNAMIC SHEAF ENGINE: 97-Task Evaluation")
    print("=" * 70)
    print()
    print("Theory: Spectral Geometry of Consolidation (SGC)")
    print("Hypothesis: The rule IS the ground state.")
    print("Method: Direct derivation from spectral modes, not stochastic search.")
    print()
    
    # Load tasks
    arc_dir = Path(__file__).parent.parent / "data" / "arc" / "training"
    tasks = load_arc_tasks(arc_dir, limit=97)
    print(f"Loaded {len(tasks)} ARC tasks")
    print()
    
    # Initialize Atlas (starts empty, learns from experience)
    atlas = SheafAtlas()
    
    # Results storage
    all_results = []
    
    # Counters
    perfect_tasks = 0
    partial_tasks = 0
    failed_tasks = 0
    shape_skip = 0
    
    start_time = time.time()
    
    for idx, task in enumerate(tasks):
        task_start = time.time()
        task_id = task['task_id']
        
        # Evaluate
        result = evaluate_task(task, atlas)
        all_results.append(result)
        
        task_time = time.time() - task_start
        
        # Classify result
        if result['train_total'] == 0:
            shape_skip += 1
            status = "SHAPE_SKIP"
        elif result['train_solved'] == result['train_total']:
            perfect_tasks += 1
            status = "PERFECT"
        elif result['train_solved'] > 0:
            partial_tasks += 1
            status = "PARTIAL"
        else:
            failed_tasks += 1
            status = "FAILED"
        
        # Progress output
        print(f"[{idx+1:3d}/97] {task_id}: {status} "
              f"({result['train_solved']}/{result['train_total']} train) "
              f"[{task_time:.2f}s] "
              f"Atlas: {atlas.get_summary()['n_charts']} charts")
        
        if result['gauge_groups_used']:
            gauges = set(result['gauge_groups_used'])
            print(f"         Gauges: {', '.join(gauges)}")
    
    total_time = time.time() - start_time
    
    # Summary
    print()
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"Total time: {total_time:.1f}s ({total_time/len(tasks):.2f}s/task)")
    print()
    print(f"Task Results:")
    print(f"  Perfect:    {perfect_tasks:3d} ({100*perfect_tasks/len(tasks):.1f}%)")
    print(f"  Partial:    {partial_tasks:3d} ({100*partial_tasks/len(tasks):.1f}%)")
    print(f"  Failed:     {failed_tasks:3d} ({100*failed_tasks/len(tasks):.1f}%)")
    print(f"  Shape skip: {shape_skip:3d} (input/output size differs)")
    print()
    
    # Atlas summary
    atlas_summary = atlas.get_summary()
    print(f"Sheaf Atlas State:")
    print(f"  Charts discovered: {atlas_summary['n_charts']}")
    
    # Count gauge groups
    gauge_counts = {}
    for g in atlas_summary['gauge_groups']:
        gauge_counts[g] = gauge_counts.get(g, 0) + 1
    print(f"  Gauge groups: {gauge_counts}")
    print(f"  Total applications: {atlas_summary['total_applications']}")
    print()
    
    # Example-level stats
    total_train_solved = sum(r['train_solved'] for r in all_results)
    total_train = sum(r['train_total'] for r in all_results)
    print(f"Example-level accuracy: {total_train_solved}/{total_train} "
          f"({100*total_train_solved/max(total_train,1):.1f}%)")
    
    # Method breakdown
    method_counts = {}
    for r in all_results:
        for m in r['methods_used']:
            method_counts[m] = method_counts.get(m, 0) + 1
    print(f"Methods: {method_counts}")
    
    # Write CSV
    csv_path = 'eval_97_thermodynamic_results.csv'
    with open(csv_path, 'w', newline='', encoding='utf-8') as f:
        writer = csv.DictWriter(f, fieldnames=[
            'task_id', 'n_train', 'n_test', 
            'train_solved', 'train_total', 
            'test_solved', 'test_total',
            'gauge_groups', 'methods', 'errors'
        ])
        writer.writeheader()
        for r in all_results:
            writer.writerow({
                'task_id': r['task_id'],
                'n_train': r['n_train'],
                'n_test': r['n_test'],
                'train_solved': r['train_solved'],
                'train_total': r['train_total'],
                'test_solved': r['test_solved'],
                'test_total': r['test_total'],
                'gauge_groups': '|'.join(r['gauge_groups_used']),
                'methods': '|'.join(r['methods_used']),
                'errors': '|'.join(r['errors'][:3])  # Truncate errors
            })
    
    print(f"\nResults saved to {csv_path}")
    
    return atlas, all_results


if __name__ == "__main__":
    atlas, results = main()
