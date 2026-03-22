"""Diagnostic: run verbose tensor logic on the 7 tasks that triggered it."""
import sys, time
sys.path.insert(0, '.')

from arc_sgc_phase8_3 import load_arc_tasks
from arc_sgc_residual_solver import RecursiveResidualSolver, HAS_TENSOR_LOGIC

tasks = load_arc_tasks('C:/Lean4 Projects/data/arc/training')

# The 7 tasks that triggered tensor logic in the 97-task eval
triggered_ids = ['0520fde7', '05f2a901', '1b2d62fb', '3bd67248',
                 '40853293', '4612dd53', '0dfd9992']

# Find matching tasks
target_tasks = []
for t in tasks:
    if any(t.task_id.startswith(tid) for tid in triggered_ids):
        target_tasks.append(t)

print(f'Found {len(target_tasks)} target tasks (verbose=True)', flush=True)
print(f'HAS_TENSOR_LOGIC = {HAS_TENSOR_LOGIC}', flush=True)

solver = RecursiveResidualSolver(max_depth=3, beam_width=8, verbose=True)

for i, task in enumerate(target_tasks):
    print(f'\n{"="*60}', flush=True)
    print(f'[{i+1}/{len(target_tasks)}] {task.task_id}', flush=True)
    print(f'{"="*60}', flush=True)
    t0 = time.time()
    r = solver.solve_task(task)
    dt = time.time() - t0
    d = r['avg_train_energy']
    tlog = r.get('tensor_log', [])
    print(f'\n  Result: d={d:.4f} ({dt:.1f}s) method={r.get("method","?")[:60]}', flush=True)
    print(f'  tensor_log: {tlog}', flush=True)
