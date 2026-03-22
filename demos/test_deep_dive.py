"""Test Deep Dive improvements on 97 ARC training tasks.

Changes tested:
  1. Pooled NMI (statistical power fix)
  2. MDL complexity penalty (Occam regularizer)
  3. Expanded predicate vocabulary (+15 relational predicates)
  4. Top-k exhaustive conjunction search (submodularity exploit)
  5. Test-time refinement loop (defect gradient descent)

Baseline: 19 perfect (prior session), 16 perfect (standalone test_agent_prior.py)
"""
import sys, time, io

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8',
                               errors='replace', line_buffering=True)

sys.path.insert(0, '.')
from arc_sgc_phase8_3 import load_arc_tasks
from arc_sgc_residual_solver import RecursiveResidualSolver
from arc_sgc_sie import PredicatePrior

tasks = load_arc_tasks('C:/Lean4 Projects/data/arc/training')
print(f'Loaded {len(tasks)} tasks', flush=True)

# Fresh prior for clean comparison
prior = PredicatePrior()
solver = RecursiveResidualSolver(
    max_depth=3, beam_width=8, verbose=False,
    predicate_prior=prior,
)

perfect = []
near = []
fails = []
refine_wins = 0
t0 = time.time()

for i, task in enumerate(tasks[:97]):
    task_t0 = time.time()
    try:
        result = solver.solve_task(task)
    except Exception as e:
        result = {'is_perfect': False, 'avg_train_energy': 1.0, 'method': f'error:{e}'}
    task_dt = time.time() - task_t0

    is_perf = result.get('is_perfect', False)
    energy = result.get('avg_train_energy', 1.0)
    method = result.get('method', 'unknown')

    tag = ""
    if is_perf:
        perfect.append((task.task_id, method))
        tag = " ** PERFECT **"
    elif energy < 0.1:
        near.append((task.task_id, energy, method))
        tag = f" near(E={energy:.4f})"
    else:
        fails.append((task.task_id, energy))

    # Detect refinement wins
    if '[REFINE]' in method or ('-> ' in method and energy < 0.1):
        pass  # refinement tracking is implicit in method description

    print(f"[{i+1:3d}/97] {task.task_id[:12]:12s} E={energy:.4f} "
          f"({task_dt:.1f}s) {method[:60]}{tag}", flush=True)

    if (i+1) % 25 == 0:
        elapsed = time.time() - t0
        p_k = len(prior.attempt_counts)
        print(f"  --- {i+1}/97: {len(perfect)} perfect, {len(near)} near, "
              f"{len(fails)} fail, prior({p_k} preds) ({elapsed:.0f}s) ---",
              flush=True)

elapsed = time.time() - t0

print(f"\n{'='*70}", flush=True)
print(f"DEEP DIVE IMPROVEMENTS ({elapsed:.0f}s)", flush=True)
print(f"{'='*70}", flush=True)
print(f"Perfect: {len(perfect)}  (baseline: 7 standalone / 19 agent)", flush=True)
print(f"Near-miss: {len(near)}", flush=True)
print(f"Fails: {len(fails)}", flush=True)

print(f"\nPerfect solves:", flush=True)
for tid, method in perfect:
    print(f"  {tid}: {method[:80]}", flush=True)

print(f"\nTop near-misses:", flush=True)
near.sort(key=lambda x: x[1])
for tid, e, method in near[:15]:
    print(f"  {tid}: E={e:.4f} {method[:65]}", flush=True)

print(f"\nPredicate Prior (final):", flush=True)
print(prior.summary(top_k=15), flush=True)
