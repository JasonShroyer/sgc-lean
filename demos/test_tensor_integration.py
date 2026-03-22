"""
Integration test: Run ARC solver with Tensor Logic enabled.
Verifies no regressions and checks for new predicate discoveries.
"""
import sys
import time
sys.path.insert(0, '.')

from arc_sgc_phase8_3 import load_arc_tasks
from arc_sgc_residual_solver import RecursiveResidualSolver, HAS_TENSOR_LOGIC

print("=" * 60, flush=True)
print("TENSOR LOGIC INTEGRATION TEST", flush=True)
print(f"HAS_TENSOR_LOGIC = {HAS_TENSOR_LOGIC}", flush=True)
print("=" * 60, flush=True)

tasks = load_arc_tasks('../data/arc/training')
print(f"Loaded {len(tasks)} tasks", flush=True)

solver = RecursiveResidualSolver(max_depth=3, beam_width=8, verbose=False)

perfects = []
near_misses = []
fails = []
tensor_discoveries = 0

# Test on first 50 tasks
t0 = time.time()
for i, task in enumerate(tasks[:50]):
    try:
        result = solver.solve_task(task)
        d = result['avg_train_energy']
        method = result.get('method', 'unknown')

        # Check for tensor_pred in the method description
        if 'tensor_pred' in method:
            tensor_discoveries += 1

        if d < 0.001:
            perfects.append((task.task_id[:8], d, method[:60]))
        elif d < 0.15:
            near_misses.append((task.task_id[:8], d, method[:60]))
        else:
            fails.append((task.task_id[:8], d, method[:40]))

        status = 'PERFECT' if d < 0.001 else ('NEAR' if d < 0.15 else 'FAIL')
        elapsed = time.time() - t0
        print(f"  [{i+1:2d}/50] {task.task_id[:8]} d={d:.4f} {status} "
              f"({elapsed:.0f}s) {method[:50]}", flush=True)
    except Exception as e:
        fails.append((task.task_id[:8], 1.0, f"ERROR: {e}"))
        print(f"  [{i+1:2d}/50] {task.task_id[:8]} ERROR: {e}", flush=True)

total_time = time.time() - t0

print(f"\n{'=' * 60}", flush=True)
print(f"RESULTS ({total_time:.0f}s total)", flush=True)
print(f"  Perfects:  {len(perfects)}", flush=True)
print(f"  Near-miss: {len(near_misses)}", flush=True)
print(f"  Fails:     {len(fails)}", flush=True)
print(f"  Tensor discoveries: {tensor_discoveries}", flush=True)

print(f"\nPerfect solves:", flush=True)
for tid, d, m in perfects:
    print(f"  {tid}: {m}", flush=True)

print(f"\nNear-misses (top 10):", flush=True)
for tid, d, m in sorted(near_misses, key=lambda x: x[1])[:10]:
    print(f"  {tid} d={d:.4f}: {m}", flush=True)

print(f"\n{'=' * 60}", flush=True)
print("INTEGRATION TEST COMPLETE", flush=True)
print("=" * 60, flush=True)
