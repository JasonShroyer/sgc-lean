"""Test full agent with persistent PredicatePrior on 97 ARC training tasks.

This tests the complete pipeline:
  - Phase 45 (pattern rules)
  - Phase 62 (residual solver with SIE + conjunction refinement + predicate prior)
  - Heuristic solver (macro operations)
  - Dream Consolidation (compiled programs)
  - LongTermMemory persistence (patterns, operators, predicate prior)

The predicate prior accumulates across tasks IN-PLACE via the shared
reference between LTM and solver. After the run, save_memory() persists
the entire prior to agent_memory.json for cross-session learning.
"""
import sys, time, io

# Force UTF-8 and line-buffered stdout for Windows
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8',
                               errors='replace', line_buffering=True)

sys.path.insert(0, '.')
from arc_sgc_phase8_3 import load_arc_tasks
from arc_sgc_agent import ARCSGCAgent

tasks = load_arc_tasks('C:/Lean4 Projects/data/arc/training')
print(f'Loaded {len(tasks)} tasks', flush=True)

# Use a FRESH memory file so we don't contaminate existing agent_memory.json
MEMORY_PATH = 'agent_memory_prior_test.json'

agent = ARCSGCAgent(
    memory_path=MEMORY_PATH,
    verbose=False,
    recall_enabled=True,
    update_enabled=True,
)

# Report initial prior state
prior = agent.ltm.predicate_prior
print(f'Initial prior: {prior.total_tasks} tasks, '
      f'{len(prior.attempt_counts)} predicates', flush=True)
print(flush=True)

perfect = []
near = []
fails = []
solver_wins = {'residual': 0, 'phase45': 0, 'heuristic': 0, 'other': 0}
t0 = time.time()

for i, task in enumerate(tasks[:97]):
    task_t0 = time.time()
    result = agent.solve_task(task)
    task_dt = time.time() - task_t0

    dist = result.get('distance', 1.0)
    is_perfect = result.get('perfect', False)
    is_near = result.get('near_miss', False)
    winner = result.get('winning_solver', 'none')

    tag = ""
    if is_perfect:
        perfect.append((task.task_id, winner))
        tag = " ** PERFECT **"
    elif is_near:
        near.append((task.task_id, dist, winner))
        tag = f" near(E={dist:.4f})"
    else:
        fails.append((task.task_id, dist))

    # Track solver family
    if 'residual' in winner:
        solver_wins['residual'] += 1
    elif 'phase45' in winner:
        solver_wins['phase45'] += 1
    elif 'heuristic' in winner:
        solver_wins['heuristic'] += 1
    else:
        solver_wins['other'] += 1

    print(f"[{i+1:3d}/97] {task.task_id[:12]:12s} d={dist:.4f} "
          f"({task_dt:.1f}s) {winner[:30]}{tag}", flush=True)

    # Summary every 25 tasks
    if (i+1) % 25 == 0:
        elapsed = time.time() - t0
        p_n = prior.total_tasks
        p_k = len(prior.attempt_counts)
        print(f"  --- {i+1}/97: {len(perfect)} perfect, {len(near)} near, "
              f"prior({p_n} tasks, {p_k} preds) ({elapsed:.0f}s) ---",
              flush=True)

elapsed = time.time() - t0

# Save memory (persists prior to disk)
agent.save_memory()

print(f"\n{'='*70}", flush=True)
print(f"FULL AGENT + PREDICATE PRIOR ({elapsed:.0f}s)", flush=True)
print(f"{'='*70}", flush=True)
print(f"Perfect: {len(perfect)}", flush=True)
print(f"Near-miss: {len(near)}", flush=True)
print(f"Fails: {len(fails)}", flush=True)
print(f"Solver wins: {solver_wins}", flush=True)

print(f"\nPerfect solves:", flush=True)
for tid, winner in perfect:
    print(f"  {tid}: {winner[:70]}", flush=True)

print(f"\nTop near-misses:", flush=True)
near.sort(key=lambda x: x[1])
for tid, d, winner in near[:15]:
    print(f"  {tid}: d={d:.4f} {winner[:60]}", flush=True)

print(f"\nPredicate Prior (final):", flush=True)
print(prior.summary(top_k=15), flush=True)

print(f"\nAgent stats:", flush=True)
stats = agent.get_stats()
for k, v in stats['session'].items():
    print(f"  {k}: {v}", flush=True)
