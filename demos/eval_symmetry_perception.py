"""
Evaluate Symmetry Perception on 97 ARC Training Tasks

Tests the theory-derived symmetry completion algorithm from spine_reflection.py
across all ARC training tasks to identify which tasks it can solve.
"""

import numpy as np
import json
from pathlib import Path
from typing import Dict, Any, List, Tuple
import time

from spine_reflection import compute_reflection_completion, predict_output


def evaluate_task(task: Dict, task_id: str) -> Dict[str, Any]:
    """
    Evaluate the symmetry completion algorithm on a single task.
    
    Returns metrics including IoU for each example and whether the task
    appears to be a symmetry completion task.
    """
    results = []
    
    for ex_idx, ex in enumerate(task['train']):
        inp = np.array(ex['input'])
        out = np.array(ex['output'])
        
        # Try symmetry completion
        completion_result = compute_reflection_completion(inp)
        
        if not completion_result['success']:
            results.append({
                'example': ex_idx,
                'success': False,
                'reason': completion_result.get('reason', 'unknown'),
                'iou': 0.0
            })
            continue
        
        # Generate prediction
        predicted = predict_output(inp, completion_result)
        
        # Handle shape mismatch (task changes grid size)
        if inp.shape != out.shape:
            results.append({
                'example': ex_idx,
                'success': False,
                'reason': 'shape_mismatch',
                'iou': 0.0
            })
            continue
        
        # Calculate IoU for the additions (color 2)
        actual_add = (out == 2) & (inp == 0)
        predicted_add = (predicted == 2) & (inp == 0)
        
        if actual_add.sum() == 0 and predicted_add.sum() == 0:
            # No additions expected or predicted - check if grids match
            iou = 1.0 if np.array_equal(inp, out) else 0.0
        elif actual_add.sum() == 0:
            # No additions expected but we predicted some
            iou = 0.0
        else:
            overlap = (actual_add & predicted_add).sum()
            union = (actual_add | predicted_add).sum()
            iou = overlap / max(union, 1)
        
        results.append({
            'example': ex_idx,
            'success': True,
            'axis': completion_result['axis'],
            'body_cols': completion_result['body_cols'],
            'n_protrusions': completion_result['n_protrusions'],
            'predicted_additions': len(completion_result['additions']),
            'actual_additions': int(actual_add.sum()),
            'iou': iou
        })
    
    # Aggregate results
    if not results:
        return {'task_id': task_id, 'n_examples': 0, 'avg_iou': 0.0}
    
    avg_iou = sum(r['iou'] for r in results) / len(results)
    perfect_examples = sum(1 for r in results if r['iou'] >= 0.99)
    
    # Check if this looks like a symmetry completion task
    # (at least one example has additions and we got good IoU)
    has_additions = any(r.get('actual_additions', 0) > 0 for r in results)
    is_symmetry_task = has_additions and avg_iou > 0.5
    
    return {
        'task_id': task_id,
        'n_examples': len(results),
        'avg_iou': avg_iou,
        'perfect_examples': perfect_examples,
        'is_symmetry_task': is_symmetry_task,
        'example_results': results
    }


def run_evaluation(arc_dir: Path, limit: int = None) -> List[Dict[str, Any]]:
    """Run evaluation on all ARC training tasks."""
    task_files = sorted(arc_dir.glob("*.json"))
    
    if limit:
        task_files = task_files[:limit]
    
    results = []
    
    print(f"Evaluating {len(task_files)} tasks...")
    print()
    
    for i, task_file in enumerate(task_files):
        task_id = task_file.stem
        
        with open(task_file) as f:
            task = json.load(f)
        
        result = evaluate_task(task, task_id)
        results.append(result)
        
        # Progress indicator
        if (i + 1) % 10 == 0:
            print(f"  Processed {i + 1}/{len(task_files)} tasks...")
    
    return results


def print_summary(results: List[Dict[str, Any]]):
    """Print summary of evaluation results."""
    total = len(results)
    
    # Categorize by IoU
    perfect = [r for r in results if r['avg_iou'] >= 0.99]
    high = [r for r in results if 0.8 <= r['avg_iou'] < 0.99]
    medium = [r for r in results if 0.5 <= r['avg_iou'] < 0.8]
    low = [r for r in results if 0.0 < r['avg_iou'] < 0.5]
    zero = [r for r in results if r['avg_iou'] == 0.0]
    
    # Symmetry tasks
    symmetry_tasks = [r for r in results if r.get('is_symmetry_task', False)]
    
    print("=" * 70)
    print("SYMMETRY PERCEPTION EVALUATION RESULTS")
    print("=" * 70)
    print()
    print(f"Total tasks evaluated: {total}")
    print()
    print("IoU Distribution:")
    print(f"  Perfect (>=99%):  {len(perfect):3d} ({100*len(perfect)/total:.1f}%)")
    print(f"  High (80-99%):    {len(high):3d} ({100*len(high)/total:.1f}%)")
    print(f"  Medium (50-80%):  {len(medium):3d} ({100*len(medium)/total:.1f}%)")
    print(f"  Low (1-50%):      {len(low):3d} ({100*len(low)/total:.1f}%)")
    print(f"  Zero (0%):        {len(zero):3d} ({100*len(zero)/total:.1f}%)")
    print()
    print(f"Likely symmetry completion tasks: {len(symmetry_tasks)}")
    print()
    
    # Show top performers
    print("Top 10 by IoU:")
    sorted_results = sorted(results, key=lambda x: x['avg_iou'], reverse=True)
    for i, r in enumerate(sorted_results[:10]):
        print(f"  {i+1}. {r['task_id']}: {r['avg_iou']:.2%} IoU ({r['perfect_examples']}/{r['n_examples']} perfect)")
    
    print()
    
    # Show symmetry tasks specifically
    if symmetry_tasks:
        print("Likely symmetry tasks (IoU > 50%, has additions):")
        for r in sorted(symmetry_tasks, key=lambda x: x['avg_iou'], reverse=True):
            print(f"  {r['task_id']}: {r['avg_iou']:.2%} IoU")
    
    return {
        'total': total,
        'perfect': len(perfect),
        'high': len(high),
        'medium': len(medium),
        'low': len(low),
        'zero': len(zero),
        'symmetry_tasks': len(symmetry_tasks)
    }


if __name__ == "__main__":
    arc_dir = Path(__file__).parent.parent / "data" / "arc" / "training"
    
    start_time = time.time()
    results = run_evaluation(arc_dir)
    elapsed = time.time() - start_time
    
    print()
    summary = print_summary(results)
    
    print()
    print(f"Evaluation completed in {elapsed:.1f} seconds")
    
    # Save detailed results
    output_file = Path(__file__).parent / "symmetry_eval_results.json"
    with open(output_file, 'w') as f:
        json.dump({
            'summary': summary,
            'results': results
        }, f, indent=2, default=str)
    
    print(f"Detailed results saved to: {output_file}")
