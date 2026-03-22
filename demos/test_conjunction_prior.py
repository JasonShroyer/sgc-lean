"""Test conjunction refinement + predicate prior on 97 ARC training tasks.

Tests SIE-integrated solver WITH conjunction refinement + predicate prior.
The predicate prior accumulates across tasks, making later tasks benefit
from earlier experience. Tests BOTH within-task improvement (conjunctions)
and cross-task learning (prior).
"""
import sys, time, io

# Force UTF-8 and unbuffered stdout for Windows
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8', errors='replace', line_buffering=True)

sys.path.insert(0, '.')
from arc_sgc_phase8_3 import load_arc_tasks
from arc_sgc_residual_solver import RecursiveResidualSolver
from arc_sgc_sie import PredicatePrior

tasks = load_arc_tasks('C:/Lean4 Projects/data/arc/training')
print(f'Loaded {len(tasks)} tasks', flush=True)

# --- Run WITH conjunction refinement + predicate prior ---
prior = PredicatePrior()
solver = RecursiveResidualSolver(
    max_depth=3, beam_width=8, verbose=False,
    use_sie=True, predicate_prior=prior
)

perfect = []
near = []
conj_used = []  # Tasks where conjunction refinement improved the predicate
t0 = time.time()

for i, task in enumerate(tasks[:97]):
    task_t0 = time.time()
    r = solver.solve_task(task)
    task_dt = time.time() - task_t0

    tag = ""
    if r['is_perfect']:
        perfect.append((task.task_id, r['method']))
        tag = " ** PERFECT **"
    elif r['avg_train_energy'] < 0.1:
        near.append((task.task_id, r['avg_train_energy'], r['method']))
        tag = f" near(E={r['avg_train_energy']:.4f})"

    # Check if method contains conjunction with negation
    method = r.get('method', '')
    has_conj = '&!' in method or (method.count('&') > 0 and
               sum(1 for p in method.split('&') if p.startswith('!')) > 0)
    if has_conj:
        conj_used.append((task.task_id, method[:80]))

    # Per-task progress line
    print(f"[{i+1:3d}/97] {task.task_id[:12]:12s} E={r['avg_train_energy']:.4f} "
          f"({task_dt:.1f}s) {method[:50]}{tag}", flush=True)

    # Summary every 25 tasks
    if (i+1) % 25 == 0:
        elapsed = time.time() - t0
        print(f"  --- {i+1}/97 summary: {len(perfect)} perfect, {len(near)} near, "
              f"{len(conj_used)} conjunctions, prior={prior.total_tasks} updates "
              f"({elapsed:.0f}s) ---", flush=True)

elapsed = time.time() - t0
print(f"\n{'='*70}", flush=True)
print(f"SIE + CONJUNCTION REFINEMENT + PREDICATE PRIOR ({elapsed:.0f}s)", flush=True)
print(f"{'='*70}", flush=True)
print(f"Perfect: {len(perfect)}", flush=True)
print(f"Near-miss: {len(near)}", flush=True)
print(f"Conjunction refinements used: {len(conj_used)}", flush=True)

print(f"\nPerfect solves:", flush=True)
for tid, method in perfect:
    print(f"  {tid}: {method[:70]}", flush=True)

print(f"\nTop near-misses:", flush=True)
near.sort(key=lambda x: x[1])
for tid, e, method in near[:15]:
    print(f"  {tid}: E={e:.4f} {method[:60]}", flush=True)

if conj_used:
    print(f"\nConjunction refinements applied:", flush=True)
    for tid, method in conj_used[:15]:
        print(f"  {tid}: {method}", flush=True)

print(f"\nPredicate Prior Summary:", flush=True)
print(prior.summary(top_k=15), flush=True)
