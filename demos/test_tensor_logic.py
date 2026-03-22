"""
Quick test: Apply Tensor Logic predicate discovery to near-miss ARC tasks.
Demonstrates that gradient descent can discover predicates that beam search misses.
"""
import numpy as np
import sys
import time
sys.path.insert(0, '.')

from arc_sgc_phase8_3 import load_arc_tasks
from arc_sgc_residual_solver import RecursiveResidualSolver
from arc_tensor_logic import TensorPredicateLearner, make_tensor_predicate_expr

# Load tasks
tasks = load_arc_tasks('../data/arc/training')
print(f"Loaded {len(tasks)} tasks")

# Find near-misses
solver = RecursiveResidualSolver(max_depth=3, beam_width=8, verbose=False)

near_misses = []
print("\n--- Finding near-misses (first 30 tasks) ---")
for task in tasks[:30]:
    try:
        result = solver.solve_task(task)
        d = result['avg_train_energy']
        if 0.001 < d < 0.12 and result['program'] is not None:
            grids = [ex.input_grid.data.numpy() for ex in task.train_examples]
            targets = [ex.output_grid.data.numpy() for ex in task.train_examples]
            preds_list = []
            for ex in task.train_examples:
                inp = ex.input_grid.data.numpy()
                preds_list.append(result['program'].apply(inp))
            near_misses.append({
                'task_id': task.task_id,
                'grids': grids,
                'targets': targets,
                'predictions': preds_list,
                'defect': d,
                'method': result['method']
            })
            print(f"  {task.task_id[:8]} d={d:.4f} {result['method'][:50]}")
    except Exception as e:
        pass

print(f"\nFound {len(near_misses)} near-misses")
if not near_misses:
    print("No near-misses found. Exiting.")
    sys.exit(0)

# Apply tensor logic to each near-miss
print("\n--- Tensor Logic Predicate Discovery ---")
learner = TensorPredicateLearner(n_factors=4, lr=0.05, steps=200, min_f1=0.25)

for nm in near_misses[:5]:
    tid = nm['task_id'][:8]
    print(f"\n{'='*50}")
    print(f"Task {tid} (defect={nm['defect']:.4f})")
    print(f"  Current method: {nm['method'][:60]}")

    t0 = time.time()
    try:
        discovered = learner.discover_predicates(
            nm['grids'], nm['targets'], nm['predictions'], verbose=True)
    except Exception as e:
        print(f"  ERROR: {e}")
        continue
    elapsed = time.time() - t0

    print(f"  Tensor logic: {len(discovered)} predicates in {elapsed:.1f}s")

    for dp in discovered:
        tp = make_tensor_predicate_expr(dp, dp.weights, dp.bias)
        print(f"  -> {tp.name}")
        print(f"     F1={dp.f1:.3f} (P={dp.precision:.3f}, R={dp.recall:.3f})")

        # Verify on each example
        for e_idx, (g, t, p) in enumerate(zip(nm['grids'], nm['targets'], nm['predictions'])):
            mask = tp.evaluate(g)
            res = (p != t)
            tp_count = int((mask & res).sum())
            fp_count = int((mask & ~res).sum())
            fn_count = int((~mask & res).sum())
            print(f"     Ex{e_idx}: mask={mask.sum()} pixels, "
                  f"covers {tp_count}/{res.sum()} wrong, "
                  f"{fp_count} false positives")

print("\n--- DONE ---")
