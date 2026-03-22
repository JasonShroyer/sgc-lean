"""Full 97-task SIE integration test."""
import sys, time
sys.path.insert(0, '.')
from arc_sgc_phase8_3 import load_arc_tasks
from arc_sgc_residual_solver import RecursiveResidualSolver

tasks = load_arc_tasks('C:/Lean4 Projects/data/arc/training')
print(f'Loaded {len(tasks)} tasks')

solver = RecursiveResidualSolver(max_depth=3, beam_width=8, verbose=False, use_sie=True)

perfect = []
near = []
t0 = time.time()

for i, task in enumerate(tasks[:97]):
    r = solver.solve_task(task)
    if r['is_perfect']:
        perfect.append((task.task_id, r['method']))
    elif r['avg_train_energy'] < 0.1:
        near.append((task.task_id, r['avg_train_energy'], r['method']))
    if (i+1) % 25 == 0:
        print(f"  {i+1}/97: {len(perfect)} perfect, {len(near)} near  ({time.time()-t0:.0f}s)")

elapsed = time.time() - t0
print(f"\n{'='*70}")
print(f"SIE-INTEGRATED RESIDUAL SOLVER - 97 Training Tasks ({elapsed:.0f}s)")
print(f"{'='*70}")
print(f"Perfect: {len(perfect)}")
print(f"Near-miss: {len(near)}")
print(f"\nPerfect solves:")
for tid, method in perfect:
    print(f"  {tid}: {method[:70]}")
print(f"\nTop near-misses:")
near.sort(key=lambda x: x[1])
for tid, e, method in near[:15]:
    print(f"  {tid}: E={e:.4f} {method[:60]}")
