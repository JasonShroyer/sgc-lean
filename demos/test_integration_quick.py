"""Quick integration test: verify tensor logic wiring doesn't break existing solves."""
import sys, time
sys.path.insert(0, '.')

from arc_sgc_phase8_3 import load_arc_tasks
from arc_sgc_residual_solver import RecursiveResidualSolver, HAS_TENSOR_LOGIC

print(f"HAS_TENSOR_LOGIC = {HAS_TENSOR_LOGIC}", flush=True)
tasks = load_arc_tasks('../data/arc/training')
solver = RecursiveResidualSolver(max_depth=3, beam_width=8, verbose=False)

t0 = time.time()
for i in range(20):
    task = tasks[i]
    result = solver.solve_task(task)
    d = result['avg_train_energy']
    tag = "PERFECT" if d < 0.001 else (f"near d={d:.4f}" if d < 0.15 else "fail")
    m = result.get('method', '?')[:50]
    print(f"  [{i+1:2d}/20] {task.task_id[:8]} {tag} {m} ({time.time()-t0:.0f}s)", flush=True)

print(f"\nDone in {time.time()-t0:.0f}s", flush=True)
