"""97-task evaluation with tensor logic instrumentation.

Captures:
  (i)   trigger frequency: how often tensor logic fires (DSL found nothing)
  (ii)  accepted-op rate: how often the IG gate passes
  (iii) net perfect gains: tasks solved ONLY because of tensor refinement
  (iv)  worst-case overhead: per-task time distribution

Output: structured log to stdout + summary CSV to eval_97_tensor_results.csv
Watch live: Get-Content -Wait eval_97_tensor.log
"""
import os, sys, time, io, json

os.environ['PYTHONUNBUFFERED'] = '1'
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8',
                               errors='replace', line_buffering=True)

# Tee: stdout + log file
class Tee:
    def __init__(self, stdout, log_path):
        self.stdout = stdout
        self.log_file = open(log_path, 'w', encoding='utf-8', buffering=1)
    def write(self, data):
        self.stdout.write(data)
        self.log_file.write(data)
        self.log_file.flush()
    def flush(self):
        self.stdout.flush()
        self.log_file.flush()

LOG_PATH = 'eval_97_tensor.log'
sys.stdout = Tee(sys.stdout, LOG_PATH)

sys.path.insert(0, '.')
from arc_sgc_phase8_3 import load_arc_tasks
from arc_sgc_residual_solver import RecursiveResidualSolver, HAS_TENSOR_LOGIC
from arc_sgc_sie import PredicatePrior
import numpy as np

# SGFE metrics
try:
    from sgfe_engine import functional_blanket_variance
    HAS_SGFE = True
except ImportError:
    HAS_SGFE = False
print(f'HAS_SGFE = {HAS_SGFE}', flush=True)

tasks = load_arc_tasks('C:/Lean4 Projects/data/arc/training')
print(f'Loaded {len(tasks)} tasks', flush=True)
print(f'HAS_TENSOR_LOGIC = {HAS_TENSOR_LOGIC}', flush=True)
print(f'Log: {os.path.abspath(LOG_PATH)}', flush=True)
print(flush=True)

N = 97

prior = PredicatePrior()
# SGFE v2.1: Enable thermodynamic beam search with Tsallis temperature annealing
# Theory (grokking_is_lifshitz): Temperature enables phase transition by allowing
# traversal of saddle points in operator space. Dream→Crystallize→Consolidate arc.
solver = RecursiveResidualSolver(
    max_depth=3, beam_width=8, verbose=False,
    use_sie=True, predicate_prior=prior,
    temperature=0.5  # v2.1: Enable thermodynamic exploration
)

# Accumulators
perfect = []
near = []
fails = []
tl_triggered = 0
tl_accepted = 0
tl_accepted_tasks = []
tl_times = []
rows = []  # CSV rows

t0 = time.time()

for i, task in enumerate(tasks[:N]):
    task_t0 = time.time()
    r = solver.solve_task(task)
    task_dt = time.time() - task_t0

    d = r['avg_train_energy']
    method = r.get('method', '?')
    tlog = r.get('tensor_log', [])

    # Classify result
    if d < 0.001:
        tag = 'PERFECT'
        perfect.append(task.task_id)
    elif d < 0.15:
        tag = f'near d={d:.4f}'
        near.append((task.task_id, d))
    else:
        tag = 'fail'
        fails.append(task.task_id)

    # Tensor logic stats
    tl_tag = ''
    tl_fired = False
    tl_ops = 0
    tl_time = 0.0
    for entry in tlog:
        if entry.get('triggered'):
            tl_fired = True
            tl_triggered += 1
            tl_time = entry.get('elapsed_s', 0.0)
            tl_times.append(tl_time)
            n_acc = entry.get('n_accepted', 0)
            tl_ops = n_acc
            if n_acc > 0:
                tl_accepted += 1
                op_names = [o.get('op', '?') for o in entry.get('ops', [])]
                tl_tag = f' [TL:{n_acc} ops={",".join(op_names)[:40]} {tl_time:.1f}s]'
                tl_accepted_tasks.append((task.task_id, tag, op_names, tl_time))
            else:
                tl_tag = f' [TL:0 {tl_time:.1f}s]'

    print(f'[{i+1:3d}/{N}] {task.task_id[:12]:12s} {tag:20s} '
          f'({task_dt:.1f}s) {method[:50]}{tl_tag}', flush=True)

    # SGFE: compute functional defect (discrete = pixel mismatch, ANOVA = feature-space)
    eps_discrete = d  # pixel mismatch IS discrete functional defect
    eps_anova = 0.0
    sheaf_e = 0.0
    if HAS_SGFE and r.get('predictions'):
        try:
            test_pred = r['predictions'][0]
            test_tgt = task.test_examples[0].output_grid.data.numpy()
            if test_pred.shape == test_tgt.shape:
                eps_anova = functional_blanket_variance(test_pred, test_tgt)
        except Exception:
            pass
    # Extract sheaf energy from tensor log
    for entry in tlog:
        for op_log in entry.get('ops', []):
            se = op_log.get('sheaf_energy', 0.0)
            if se > sheaf_e:
                sheaf_e = se

    # Library size (from solver)
    lib_size = 0
    cross_task_accepts = 0
    cross_task_validator_size = 0
    if hasattr(solver, '_sgfe_library') and solver._sgfe_library is not None:
        lib_size = solver._sgfe_library.size
        cross_task_accepts = solver._sgfe_library.cross_task_accepts
    if hasattr(solver, 'cross_task_validator') and solver.cross_task_validator is not None:
        cross_task_validator_size = solver.cross_task_validator.size

    rows.append({
        'task_id': task.task_id,
        'status': tag.split()[0],
        'defect': round(d, 6),
        'eps_anova': round(eps_anova, 6),
        'sheaf_energy': round(sheaf_e, 4),
        'time_s': round(task_dt, 1),
        'method': method[:80],
        'tl_fired': tl_fired,
        'tl_accepted': tl_ops,
        'tl_time_s': round(tl_time, 2),
        'lib_size': lib_size,
    })

    # Summary every 25 tasks
    if (i + 1) % 25 == 0:
        elapsed = time.time() - t0
        print(f'  --- {i+1}/{N}: {len(perfect)}P {len(near)}N {len(fails)}F | '
              f'TL: {tl_triggered} triggered, {tl_accepted} accepted '
              f'({elapsed:.0f}s) ---', flush=True)

elapsed = time.time() - t0

# === SUMMARY ===
print(f'\n{"="*70}', flush=True)
print(f'97-TASK EVALUATION WITH TENSOR LOGIC ({elapsed:.0f}s)', flush=True)
print(f'{"="*70}', flush=True)
print(f'Perfect:   {len(perfect)}', flush=True)
print(f'Near-miss: {len(near)}', flush=True)
print(f'Fail:      {len(fails)}', flush=True)

# SGFE metrics summary
if rows:
    # Clamp defects to [0, 1]: values > 1 indicate shape mismatch, not valid ε_func
    defects = [min(r['defect'], 1.0) for r in rows]
    anova_vals = [r['eps_anova'] for r in rows if 0 < r['eps_anova'] <= 1.0]
    lib_final = rows[-1].get('lib_size', 0)
    print(f'\n--- SGFE Metrics (FunctionalBlanket.lean) ---', flush=True)
    print(f'Functional defect (discrete, avg): {np.mean(defects):.4f}', flush=True)
    print(f'Functional defect (ANOVA, avg):    {np.mean(anova_vals):.4f}' if anova_vals else 'Functional defect (ANOVA): N/A', flush=True)
    print(f'Library size (primitives):         {lib_final}', flush=True)
    
    # SGFE v2.2: Cross-task validation metrics
    if hasattr(solver, 'cross_task_validator') and solver.cross_task_validator is not None:
        ctv = solver.cross_task_validator
        print(f'\n--- SGFE v2.2 Cross-Task Metrics ---', flush=True)
        print(f'Near-miss tasks cached:            {ctv.size}', flush=True)
        print(f'Cross-task validated predicates:   {solver._sgfe_library.cross_task_accepts if solver._sgfe_library else 0}', flush=True)
        clusters = ctv.get_cluster_summary()
        if clusters:
            print(f'Transformation signature clusters: {len(clusters)}', flush=True)
            top_clusters = sorted(clusters.items(), key=lambda x: -x[1])[:3]
            for sig, count in top_clusters:
                print(f'  {sig}: {count} tasks', flush=True)

print(f'\n--- Tensor Logic Stats ---', flush=True)
print(f'Triggered: {tl_triggered}/{N} tasks ({100*tl_triggered/N:.1f}%)', flush=True)
print(f'Accepted:  {tl_accepted}/{max(tl_triggered,1)} triggered '
      f'({100*tl_accepted/max(tl_triggered,1):.1f}%)', flush=True)
if tl_times:
    import statistics
    print(f'TL time:   median={statistics.median(tl_times):.1f}s  '
          f'mean={statistics.mean(tl_times):.1f}s  '
          f'max={max(tl_times):.1f}s  '
          f'p95={sorted(tl_times)[int(0.95*len(tl_times))]:.1f}s', flush=True)

if tl_accepted_tasks:
    print(f'\n--- Tensor-Accepted Tasks ---', flush=True)
    for tid, status, ops, dt in tl_accepted_tasks:
        print(f'  {tid[:12]:12s} {status:20s} ops={ops}  ({dt:.1f}s)', flush=True)

print(f'\nPerfect solves:', flush=True)
for tid in perfect:
    print(f'  {tid}', flush=True)

print(f'\nTop near-misses:', flush=True)
near.sort(key=lambda x: x[1])
for tid, d in near[:15]:
    print(f'  {tid}: d={d:.4f}', flush=True)

# Write CSV
csv_path = 'eval_97_tensor_results.csv'
with open(csv_path, 'w') as f:
    cols = ['task_id', 'status', 'defect', 'eps_anova', 'sheaf_energy',
            'time_s', 'method', 'tl_fired', 'tl_accepted', 'tl_time_s', 'lib_size']
    f.write(','.join(cols) + '\n')
    for row in rows:
        vals = [str(row[c]) for c in cols]
        f.write(','.join(vals) + '\n')

print(f'\nCSV: {os.path.abspath(csv_path)}', flush=True)
print(f'Log: {os.path.abspath(LOG_PATH)}', flush=True)
