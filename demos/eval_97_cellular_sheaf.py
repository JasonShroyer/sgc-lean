"""
97-Task Evaluation: Cellular Sheaf Engine

Evaluates the Cellular Sheaf architecture on the first 97 ARC training tasks.
Compares against the baseline Thermodynamic Sheaf Engine (1% perfect).

Key improvements:
1. Color-weighted normalized Laplacian (semantic manifold)
2. Color-aware connected components (correct stalks)
3. Object-wise gauge detection
4. EM-loop for iterative refinement
5. RG Flow for shape-change handling
"""

import sys
import json
import time
import numpy as np
from pathlib import Path
from typing import Dict, Any, List
from datetime import datetime

# Add parent directory for imports
sys.path.insert(0, str(Path(__file__).parent))

from cellular_sheaf_engine import CellularSheafEngine


class Tee:
    """Write to both file and stdout."""
    def __init__(self, filename):
        self.file = open(filename, 'w', encoding='utf-8')
        self.stdout = sys.stdout
    
    def write(self, data):
        self.file.write(data)
        self.stdout.write(data)
        self.file.flush()
    
    def flush(self):
        self.file.flush()
        self.stdout.flush()
    
    def close(self):
        self.file.close()


def evaluate_task(task_path: Path) -> Dict[str, Any]:
    """Evaluate a single ARC task with the Cellular Sheaf Engine."""
    
    with open(task_path, 'r') as f:
        task = json.load(f)
    
    train_examples = task['train']
    results = []
    methods_used = set()
    gauges_found = set()
    
    for i, example in enumerate(train_examples):
        input_grid = np.array(example['input'], dtype=np.float32)
        output_grid = np.array(example['output'], dtype=np.float32)
        
        try:
            engine = CellularSheafEngine(input_grid, output_grid)
            result = engine.solve()
            
            if result['success']:
                methods_used.add(result.get('method', 'unknown'))
                if 'gauges' in result:
                    for g in result['gauges']:
                        if g:
                            gauges_found.add(g.get('gauge_group', 'unknown'))
            
            results.append({
                'example': i,
                'success': result['success'],
                'method': result.get('method', 'none'),
                'n_stalks': result.get('n_stalks', 0)
            })
            
        except Exception as e:
            results.append({
                'example': i,
                'success': False,
                'error': str(e)[:100]
            })
    
    n_success = sum(1 for r in results if r['success'])
    
    return {
        'task_id': task_path.stem,
        'n_train': len(train_examples),
        'n_success': n_success,
        'success_rate': n_success / len(train_examples) if train_examples else 0,
        'methods': list(methods_used),
        'gauges': list(gauges_found),
        'results': results
    }


def main():
    # Setup logging
    log_file = Path(__file__).parent / 'eval_97_cellular_sheaf.log'
    tee = Tee(str(log_file))
    sys.stdout = tee
    
    print("=" * 70)
    print("CELLULAR SHEAF ENGINE: 97-Task Evaluation")
    print("=" * 70)
    print()
    print("Architecture: Cellular Sheaf Network (Phase 1)")
    print("Key Features:")
    print("  - Color-weighted normalized Laplacian (L_rw)")
    print("  - Color-aware connected components (correct stalks)")
    print("  - Object-wise gauge detection")
    print("  - EM-loop iterative refinement")
    print("  - RG Flow for shape-change")
    print()
    
    # Find ARC tasks
    arc_dir = Path(__file__).parent.parent / 'data' / 'arc' / 'training'
    
    if not arc_dir.exists():
        print(f"ERROR: ARC directory not found: {arc_dir}")
        return
    
    task_files = sorted(arc_dir.glob('*.json'))[:97]
    print(f"Loaded {len(task_files)} ARC tasks")
    print()
    
    # Evaluation metrics
    results = []
    perfect_tasks = []
    partial_tasks = []
    failed_tasks = []
    shape_skip = []
    
    total_examples = 0
    total_success = 0
    
    method_counts = {}
    gauge_counts = {}
    
    start_time = time.time()
    
    for i, task_path in enumerate(task_files):
        task_start = time.time()
        
        try:
            result = evaluate_task(task_path)
            task_time = time.time() - task_start
            
            results.append(result)
            
            # Track examples
            total_examples += result['n_train']
            total_success += result['n_success']
            
            # Classify task
            if result['n_success'] == result['n_train'] and result['n_train'] > 0:
                status = 'PERFECT'
                perfect_tasks.append(result['task_id'])
            elif result['n_success'] > 0:
                status = 'PARTIAL'
                partial_tasks.append(result['task_id'])
            else:
                # Check if shape mismatch
                has_shape_issue = any(
                    'shape' in str(r.get('error', '')).lower() or 
                    r.get('method') == 'none'
                    for r in result['results']
                )
                status = 'FAILED'
                failed_tasks.append(result['task_id'])
            
            # Track methods and gauges
            for m in result['methods']:
                method_counts[m] = method_counts.get(m, 0) + 1
            for g in result['gauges']:
                gauge_counts[g] = gauge_counts.get(g, 0) + 1
            
            # Print progress
            print(f"[{i+1:3d}/97] {result['task_id']}: {status} "
                  f"({result['n_success']}/{result['n_train']} train) "
                  f"[{task_time:.2f}s]")
            
            if result['gauges']:
                print(f"         Gauges: {', '.join(result['gauges'])}")
            
        except Exception as e:
            print(f"[{i+1:3d}/97] {task_path.stem}: ERROR - {str(e)[:50]}")
            failed_tasks.append(task_path.stem)
    
    total_time = time.time() - start_time
    
    # Summary
    print()
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"Total time: {total_time:.1f}s ({total_time/len(task_files):.2f}s/task)")
    print()
    print("Task Results:")
    print(f"  Perfect:      {len(perfect_tasks)} ({100*len(perfect_tasks)/len(task_files):.1f}%)")
    print(f"  Partial:      {len(partial_tasks)} ({100*len(partial_tasks)/len(task_files):.1f}%)")
    print(f"  Failed:       {len(failed_tasks)} ({100*len(failed_tasks)/len(task_files):.1f}%)")
    print()
    print(f"Example-level accuracy: {total_success}/{total_examples} "
          f"({100*total_success/total_examples:.1f}%)")
    print()
    print(f"Methods used: {method_counts}")
    print(f"Gauges found: {gauge_counts}")
    
    if perfect_tasks:
        print()
        print("Perfect tasks:")
        for t in perfect_tasks[:10]:
            print(f"  - {t}")
        if len(perfect_tasks) > 10:
            print(f"  ... and {len(perfect_tasks) - 10} more")
    
    # Comparison with baseline
    print()
    print("=" * 70)
    print("COMPARISON WITH BASELINE (Thermodynamic Sheaf Engine v1)")
    print("=" * 70)
    print(f"Baseline: 1 perfect (1.0%), 10/221 examples (4.5%)")
    print(f"Cellular: {len(perfect_tasks)} perfect ({100*len(perfect_tasks)/len(task_files):.1f}%), "
          f"{total_success}/{total_examples} examples ({100*total_success/total_examples:.1f}%)")
    
    improvement = (total_success / total_examples) / 0.045 - 1
    print(f"Improvement: {improvement*100:+.1f}% relative")
    
    # Save CSV
    csv_path = Path(__file__).parent / 'eval_97_cellular_sheaf_results.csv'
    with open(csv_path, 'w') as f:
        f.write('task_id,n_train,n_success,success_rate,methods,gauges\n')
        for r in results:
            f.write(f"{r['task_id']},{r['n_train']},{r['n_success']},"
                    f"{r['success_rate']:.3f},"
                    f"\"{','.join(r['methods'])}\","
                    f"\"{','.join(r['gauges'])}\"\n")
    
    print()
    print(f"Results saved to {csv_path}")
    
    tee.close()


if __name__ == '__main__':
    main()
