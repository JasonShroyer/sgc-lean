"""SGFE v2.2: Two-Pass Coset Curriculum Evaluation

Architecture:
  Pass 1 (Scout/Dream): Run all 97 tasks sequentially with require_cross_task=False
    - Populates the CrossTaskPredicateValidator with near-miss data
    - Collects staging library candidates (pass within-task SGFE gate)
    - Maps transformation signatures across the curriculum

  Pass 2 (Consolidate): Re-run tasks grouped by transformation signature clusters
    - Tasks are grouped by similar transformation signatures (cosets)
    - Predicates discovered within a cluster benefit peers immediately
    - Only curriculum-validated predicates enter permanent library (require_cross_task=True)

Theory (SGC.Renormalization):
  - Pass 1 = Dream phase (high temperature exploration, broad sampling)
  - Pass 2 = Consolidation phase (low temperature, only stable invariants remain)
  - Cross-task validation implements dirichlet_gap_non_decrease at curriculum level

GPU Acceleration:
  - TensorPredicateLearner now runs on CUDA for 10-100x speedup
  - This enables much more rigorous predicate search within time budget
"""
import os, sys, time, io, json
import random
import hashlib
import statistics
from collections import Counter
from typing import Dict
import torch

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

LOG_PATH = 'eval_97_tensor_v2.log'
sys.stdout = Tee(sys.stdout, LOG_PATH)

sys.path.insert(0, '.')
from arc_sgc_phase8_3 import load_arc_tasks
from arc_sgc_residual_solver import RecursiveResidualSolver, HAS_TENSOR_LOGIC
from arc_sgc_sie import PredicatePrior
from sgfe_engine import CrossTaskPredicateValidator, SGFEPrimitiveLibrary
import numpy as np

# GPU check
print(f'PyTorch version: {torch.__version__}', flush=True)
print(f'CUDA available: {torch.cuda.is_available()}', flush=True)
if torch.cuda.is_available():
    print(f'CUDA device: {torch.cuda.get_device_name(0)}', flush=True)
    print(f'CUDA memory: {torch.cuda.get_device_properties(0).total_memory / 1e9:.1f} GB', flush=True)

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

N = max(int(os.getenv('SGFE_TASK_LIMIT', '97')), 1)

# Cross-task validator instrumentation/config (env-overridable)
CROSS_TASK_SIM_THRESHOLD = float(os.getenv('SGFE_CROSS_SIM_THRESHOLD', '0.3'))
CROSS_TASK_MIN_DELTA = float(os.getenv('SGFE_CROSS_MIN_DELTA', '0.001'))
CROSS_TASK_MIN_TASKS = max(int(os.getenv('SGFE_CROSS_MIN_TASKS', '2')), 1)
CROSS_TASK_DEBUG = os.getenv('SGFE_CROSS_DEBUG', '1') == '1'
PASS2_TL_ONLY = os.getenv('SGFE_PASS2_TL_ONLY', '0') == '1'
XVAL_REPORT_TOPK = max(int(os.getenv('SGFE_XVAL_TOPK', '8')), 1)

# Initialize GLOBAL cross-task validator and libraries
# This is the key architectural change: these persist across both passes
cross_task_validator = CrossTaskPredicateValidator(
    similarity_threshold=CROSS_TASK_SIM_THRESHOLD,
    min_delta=CROSS_TASK_MIN_DELTA,
    debug=CROSS_TASK_DEBUG,
)
staging_library = SGFEPrimitiveLibrary(
    cross_task_validator,
    require_cross_task=False,
    min_tasks=CROSS_TASK_MIN_TASKS,
)  # Pass 1 accepts locally
permanent_library = SGFEPrimitiveLibrary(
    cross_task_validator,
    require_cross_task=True,
    min_tasks=CROSS_TASK_MIN_TASKS,
)  # Pass 2 enforces cross-task generalization

print(
    f'Cross-task config: sim<{CROSS_TASK_SIM_THRESHOLD:.3f} '
    f'min_delta>{CROSS_TASK_MIN_DELTA:.4f} min_tasks={CROSS_TASK_MIN_TASKS} '
    f'debug={CROSS_TASK_DEBUG} pass2_tl_only={PASS2_TL_ONLY}',
    flush=True,
)

prior = PredicatePrior()


def _fmt_status_counts(counts: Dict[str, int]) -> str:
    """Compact non-CSV-breaking formatter for validation status counters."""
    if not counts:
        return '-'
    keys = ('improved', 'flat', 'regressed', 'shape_mismatch', 'error')
    return '|'.join(f'{k}:{int(counts.get(k, 0))}' for k in keys)

def run_pass(tasks, solver, pass_name, require_cross_task, task_order=None):
    """Run evaluation pass over tasks.
    
    Args:
        tasks: List of ARC tasks
        solver: RecursiveResidualSolver instance
        pass_name: Name for logging (e.g., "Pass 1 (Scout)")
        require_cross_task: Whether to enforce cross-task validation
        task_order: Optional list of task indices in desired order (for clustering)
    
    Returns:
        Dict with results: perfect, near, fails, tl_stats, rows
    """
    perfect = []
    near = []
    fails = []
    tl_triggered = 0
    tl_accepted = 0
    tl_accepted_tasks = []
    tl_fired_task_ids = []
    tl_times = []
    xval_rejections = []
    rows = []
    
    # Use provided order or sequential
    indices = task_order if task_order else list(range(len(tasks)))
    
    print(f'\n{"="*70}', flush=True)
    print(f'{pass_name} ({len(indices)} tasks, require_cross_task={require_cross_task})', flush=True)
    print(f'{"="*70}', flush=True)
    
    t0 = time.time()
    
    for idx_pos, task_idx in enumerate(indices):
        task = tasks[task_idx]
        prev_lib_size = 0
        prev_log_len = 0
        if hasattr(solver, '_sgfe_library') and solver._sgfe_library is not None:
            prev_lib_size = solver._sgfe_library.size
            prev_log_len = len(solver._sgfe_library.compression_log)
        
        # SGFE v2.4: Per-task deterministic seeding
        # This ensures reproducibility regardless of task ordering between passes.
        # The 08ed6ac7 regression was caused by non-deterministic beam state
        # that varied with task order.
        task_seed = int(hashlib.md5(task.task_id.encode()).hexdigest()[:8], 16) % (2**31)
        random.seed(task_seed)
        np.random.seed(task_seed)
        torch.manual_seed(task_seed)
        if torch.cuda.is_available():
            torch.cuda.manual_seed(task_seed)
        
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

        if tl_fired:
            tl_fired_task_ids.append(task.task_id)

        print(f'[{idx_pos+1:3d}/{len(indices)}] {task.task_id[:12]:12s} {tag:20s} '
              f'({task_dt:.1f}s) {method[:50]}{tl_tag}', flush=True)

        # SGFE metrics
        eps_discrete = d
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
        for entry in tlog:
            for op_log in entry.get('ops', []):
                se = op_log.get('sheaf_energy', 0.0)
                if se > sheaf_e:
                    sheaf_e = se

        # Library size
        lib_size = 0
        cross_task_accepts = 0
        if hasattr(solver, '_sgfe_library') and solver._sgfe_library is not None:
            lib_size = solver._sgfe_library.size
            cross_task_accepts = solver._sgfe_library.cross_task_accepts

        # New cross-task validation diagnostics for this task
        task_rejections = []
        if hasattr(solver, '_sgfe_library') and solver._sgfe_library is not None:
            new_logs = solver._sgfe_library.compression_log[prev_log_len:]
            for clog in new_logs:
                if clog.get('cross_task_rejected'):
                    task_rejections.append(clog)
                    xval_rejections.append(clog)

        if require_cross_task and tl_fired and task_rejections:
            last_rej = task_rejections[-1]
            print(
                f"    [XVAL] reject peers={int(last_rej.get('cross_task_similar_peers', 0))} "
                f"n_improved={int(last_rej.get('n_improved', 0))}/{int(last_rej.get('cross_task_min_tasks', 0))} "
                f"reason={last_rej.get('cross_task_reason', '?')} "
                f"status={_fmt_status_counts(last_rej.get('cross_task_status_counts', {}))}",
                flush=True,
            )
            top_failures = last_rej.get('cross_task_top_failures', [])
            if top_failures:
                worst = top_failures[0]
                print(
                    f"      worst_peer={str(worst.get('task_id', '?'))[:8]} "
                    f"dist={worst.get('distance', '?')} status={worst.get('status', '?')} "
                    f"delta={worst.get('total_delta', '?')}",
                    flush=True,
                )

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
            'xval_rejected': bool(task_rejections),
            'xval_peer_count': int(task_rejections[-1].get('cross_task_similar_peers', 0)) if task_rejections else 0,
            'xval_reason': str(task_rejections[-1].get('cross_task_reason', '-')) if task_rejections else '-',
            'xval_status_counts': _fmt_status_counts(task_rejections[-1].get('cross_task_status_counts', {})) if task_rejections else '-',
            'lib_delta': lib_size - prev_lib_size,
        })

        # Summary every 25 tasks
        if (idx_pos + 1) % 25 == 0:
            elapsed = time.time() - t0
            print(f'  --- {idx_pos+1}/{len(indices)}: {len(perfect)}P {len(near)}N {len(fails)}F | '
                  f'TL: {tl_triggered} triggered, {tl_accepted} accepted '
                  f'({elapsed:.0f}s) ---', flush=True)

    elapsed = time.time() - t0

    if require_cross_task and xval_rejections:
        agg = Counter()
        peer_counts = []
        for rej in xval_rejections:
            agg.update(rej.get('cross_task_status_counts', {}))
            peer_counts.append(int(rej.get('cross_task_similar_peers', 0)))

        print(f"\n  [XVAL] pass rejection count: {len(xval_rejections)}", flush=True)
        print(
            f"  [XVAL] peer-count: min={min(peer_counts)} "
            f"median={statistics.median(peer_counts):.1f} max={max(peer_counts)}",
            flush=True,
        )
        print(f"  [XVAL] status totals: {_fmt_status_counts(agg)}", flush=True)

        sparse = sorted(
            xval_rejections,
            key=lambda r: (int(r.get('cross_task_similar_peers', 0)), int(r.get('n_improved', 0))),
        )[:XVAL_REPORT_TOPK]
        if sparse:
            print("  [XVAL] most isolated rejects:", flush=True)
            for rej in sparse:
                print(
                    f"    - {str(rej.get('task_id', ''))[:8]} "
                    f"peers={int(rej.get('cross_task_similar_peers', 0))} "
                    f"n_improved={int(rej.get('n_improved', 0))} "
                    f"reason={rej.get('cross_task_reason', '?')}",
                    flush=True,
                )
    
    return {
        'perfect': perfect,
        'near': near,
        'fails': fails,
        'tl_triggered': tl_triggered,
        'tl_accepted': tl_accepted,
        'tl_accepted_tasks': tl_accepted_tasks,
        'tl_fired_task_ids': tl_fired_task_ids,
        'tl_times': tl_times,
        'xval_rejections': xval_rejections,
        'rows': rows,
        'elapsed': elapsed,
    }


# =============================================================================
# PASS 1: SCOUT / DREAM
# =============================================================================
# Run all tasks sequentially to populate the cross-task validator
# Accept predicates with relaxed criteria (no cross-task requirement)

solver_pass1 = RecursiveResidualSolver(
    max_depth=3, beam_width=8, verbose=False,
    use_sie=True, predicate_prior=prior,
    temperature=0.5,  # Higher temperature for exploration
    cross_task_validator=cross_task_validator,
)

# Disable cross-task requirement for Pass 1
# (Predicates go to staging library, not permanent)
if solver_pass1._sgfe_library:
    solver_pass1._sgfe_library = staging_library

pass1_results = run_pass(tasks[:N], solver_pass1, "PASS 1: SCOUT (Dream Phase)", 
                         require_cross_task=False)

# =============================================================================
# ANALYZE TRANSFORMATION SIGNATURES AND CREATE CLUSTERS
# =============================================================================
print(f'\n{"="*70}', flush=True)
print(f'ANALYZING TRANSFORMATION SIGNATURE CLUSTERS', flush=True)
print(f'{"="*70}', flush=True)

ctv_size = cross_task_validator.size
print(f'Near-miss tasks cached: {ctv_size}', flush=True)

neighbor_counts = cross_task_validator.get_neighbor_counts()
if neighbor_counts:
    nvals = list(neighbor_counts.values())
    print(
        f'Neighbor counts @ sim<{cross_task_validator.similarity_threshold:.3f}: '
        f'min={min(nvals)} median={statistics.median(nvals):.1f} '
        f'mean={statistics.mean(nvals):.2f} max={max(nvals)}',
        flush=True,
    )
    most_isolated = sorted(neighbor_counts.items(), key=lambda x: x[1])[:XVAL_REPORT_TOPK]
    print('Most isolated near-miss tasks:', flush=True)
    for tid, n in most_isolated:
        print(f'  {tid}: peers={n}', flush=True)

# Get cluster summary
clusters = cross_task_validator.get_cluster_summary()
print(f'Distinct transformation signatures: {len(clusters)}', flush=True)

# Build task index -> cluster mapping
task_to_cluster = {}
cluster_to_tasks = {}

for task_id, entry in cross_task_validator.entries.items():
    sig = entry.get('signature', (0, 0, 0, 0))
    # Discretize signature for clustering
    sig_key = (
        'fill' if sig[0] > 0.5 else '',
        'erase' if sig[1] > 0.5 else '',
        'recolor' if sig[2] > 0.5 else '',
        'pure_recolor' if sig[3] > 0.5 else '',
    )
    sig_str = '_'.join(s for s in sig_key if s) or 'mixed'
    task_to_cluster[task_id] = sig_str
    if sig_str not in cluster_to_tasks:
        cluster_to_tasks[sig_str] = []
    cluster_to_tasks[sig_str].append(task_id)

# Print cluster distribution
print(f'\nCluster distribution:', flush=True)
for cluster_name, task_ids in sorted(cluster_to_tasks.items(), key=lambda x: -len(x[1])):
    print(f'  {cluster_name}: {len(task_ids)} tasks', flush=True)

# Build task order for Pass 2: group by cluster
# Tasks not in cache (perfect solves, hard fails) go last
task_id_to_idx = {t.task_id: i for i, t in enumerate(tasks[:N])}
pass2_order = []
unclustered = []

for cluster_name in sorted(cluster_to_tasks.keys(), key=lambda x: -len(cluster_to_tasks[x])):
    cluster_task_ids = cluster_to_tasks[cluster_name]
    for tid in cluster_task_ids:
        if tid in task_id_to_idx:
            pass2_order.append(task_id_to_idx[tid])

# Add unclustered tasks (perfects, hard fails from pass 1)
for i in range(N):
    if i not in pass2_order:
        unclustered.append(i)

pass2_order.extend(unclustered)

if PASS2_TL_ONLY:
    tl_set = set(pass1_results.get('tl_fired_task_ids', []))
    pass2_order = [i for i in pass2_order if tasks[i].task_id in tl_set]
    print(f'Pass 2 TL-only filter enabled: {len(pass2_order)} tasks (from {len(tl_set)} TL-triggered tasks)', flush=True)

clustered_count = sum(1 for i in pass2_order if i not in unclustered)
unclustered_count = len(pass2_order) - clustered_count
print(f'\nPass 2 order: {clustered_count} clustered, {unclustered_count} unclustered', flush=True)

# =============================================================================
# PASS 2: CONSOLIDATE
# =============================================================================
# Re-run tasks grouped by transformation signature clusters
# Now cross-task validation has teeth because cache is populated

solver_pass2 = RecursiveResidualSolver(
    max_depth=3, beam_width=8, verbose=False,
    use_sie=True, predicate_prior=prior,
    temperature=0.3,  # Lower temperature for consolidation
    cross_task_validator=cross_task_validator,  # Same validator (populated from Pass 1)
)

# Use permanent library with cross-task validation
if solver_pass2._sgfe_library:
    solver_pass2._sgfe_library = permanent_library

pass2_results = run_pass(tasks[:N], solver_pass2, "PASS 2: CONSOLIDATE (Coset Learning)", 
                         require_cross_task=True, task_order=pass2_order)

# =============================================================================
# COMBINED SUMMARY
# =============================================================================
print(f'\n{"="*70}', flush=True)
print(f'TWO-PASS COSET CURRICULUM EVALUATION COMPLETE', flush=True)
print(f'{"="*70}', flush=True)

print(f'\n--- Pass 1 (Scout) Results ---', flush=True)
print(f'Perfect:   {len(pass1_results["perfect"])}', flush=True)
print(f'Near-miss: {len(pass1_results["near"])}', flush=True)
print(f'Fail:      {len(pass1_results["fails"])}', flush=True)
print(f'TL Triggered: {pass1_results["tl_triggered"]}', flush=True)
print(f'TL Accepted:  {pass1_results["tl_accepted"]}', flush=True)
print(f'Time: {pass1_results["elapsed"]:.0f}s', flush=True)

print(f'\n--- Pass 2 (Consolidate) Results ---', flush=True)
print(f'Perfect:   {len(pass2_results["perfect"])}', flush=True)
print(f'Near-miss: {len(pass2_results["near"])}', flush=True)
print(f'Fail:      {len(pass2_results["fails"])}', flush=True)
print(f'TL Triggered: {pass2_results["tl_triggered"]}', flush=True)
print(f'TL Accepted:  {pass2_results["tl_accepted"]}', flush=True)
print(f'Time: {pass2_results["elapsed"]:.0f}s', flush=True)

# Cross-task validation metrics
print(f'\n--- SGFE v2.2 Cross-Task Metrics ---', flush=True)
print(f'Near-miss tasks cached:            {cross_task_validator.size}', flush=True)
print(f'Staging library size (Pass 1):     {staging_library.size}', flush=True)
print(f'Permanent library size (Pass 2):   {permanent_library.size}', flush=True)
print(f'Cross-task validated predicates:   {permanent_library.cross_task_accepts}', flush=True)

rejected_logs = [x for x in permanent_library.compression_log if x.get('cross_task_rejected')]
if rejected_logs:
    agg = Counter()
    for rej in rejected_logs:
        agg.update(rej.get('cross_task_status_counts', {}))
    print(f'Rejected at cross-task gate:      {len(rejected_logs)}', flush=True)
    print(f'Rejection status totals:          {_fmt_status_counts(agg)}', flush=True)

    print('Sample rejection diagnostics:', flush=True)
    for rej in rejected_logs[:XVAL_REPORT_TOPK]:
        print(
            f"  {str(rej.get('task_id', ''))[:8]} peers={int(rej.get('cross_task_similar_peers', 0))} "
            f"n_improved={int(rej.get('n_improved', 0))}/{int(rej.get('cross_task_min_tasks', 0))} "
            f"reason={rej.get('cross_task_reason', '?')} "
            f"status={_fmt_status_counts(rej.get('cross_task_status_counts', {}))}",
            flush=True,
        )

if CROSS_TASK_DEBUG:
    recent_reports = cross_task_validator.get_recent_reports(XVAL_REPORT_TOPK)
    if recent_reports:
        print('Recent validator reports:', flush=True)
        for rep in recent_reports:
            print(
                f"  task={str(rep.get('current_task_id', ''))[:8]} "
                f"accepted={rep.get('accepted')} peers={rep.get('candidate_peer_count', 0)} "
                f"n_improved={rep.get('n_improved', 0)}/{rep.get('min_tasks', 0)} "
                f"reason={rep.get('reason', '?')} "
                f"status={_fmt_status_counts(rep.get('status_counts', {}))}",
                flush=True,
            )

# Improvement analysis
pass1_perfect_set = set(pass1_results['perfect'])
pass2_perfect_set = set(pass2_results['perfect'])
new_perfects = pass2_perfect_set - pass1_perfect_set
lost_perfects = pass1_perfect_set - pass2_perfect_set

if new_perfects:
    print(f'\n--- New Perfect Solves in Pass 2 ---', flush=True)
    for tid in new_perfects:
        print(f'  {tid} (cross-task learning benefit)', flush=True)

if lost_perfects:
    print(f'\n--- Lost Perfect Solves in Pass 2 ---', flush=True)
    for tid in lost_perfects:
        print(f'  {tid}', flush=True)

# TL stats
all_tl_times = pass1_results['tl_times'] + pass2_results['tl_times']
if all_tl_times:
    print(f'\n--- Combined Tensor Logic Stats ---', flush=True)
    print(f'Total TL triggered: {pass1_results["tl_triggered"] + pass2_results["tl_triggered"]}', flush=True)
    print(f'Total TL accepted:  {pass1_results["tl_accepted"] + pass2_results["tl_accepted"]}', flush=True)
    print(f'TL time: median={statistics.median(all_tl_times):.1f}s  '
          f'mean={statistics.mean(all_tl_times):.1f}s  '
          f'max={max(all_tl_times):.1f}s', flush=True)

# Perfect solves
print(f'\nFinal Perfect solves ({len(pass2_results["perfect"])}):', flush=True)
for tid in pass2_results['perfect']:
    marker = ' (new)' if tid in new_perfects else ''
    print(f'  {tid}{marker}', flush=True)

# Top near-misses
print(f'\nTop near-misses (Pass 2):', flush=True)
near_sorted = sorted(pass2_results['near'], key=lambda x: x[1])
for tid, d in near_sorted[:15]:
    print(f'  {tid}: d={d:.4f}', flush=True)

# Write CSV
csv_path = 'eval_97_tensor_v2_results.csv'
with open(csv_path, 'w') as f:
    cols = ['pass', 'task_id', 'status', 'defect', 'eps_anova', 'sheaf_energy',
            'time_s', 'method', 'tl_fired', 'tl_accepted', 'tl_time_s', 'lib_size',
            'xval_rejected', 'xval_peer_count', 'xval_reason', 'xval_status_counts', 'lib_delta']
    f.write(','.join(cols) + '\n')
    for row in pass1_results['rows']:
        row['pass'] = 1
        vals = [str(row.get(c, '')) for c in cols]
        f.write(','.join(vals) + '\n')
    for row in pass2_results['rows']:
        row['pass'] = 2
        vals = [str(row.get(c, '')) for c in cols]
        f.write(','.join(vals) + '\n')

print(f'\nCSV: {os.path.abspath(csv_path)}', flush=True)
print(f'Log: {os.path.abspath(LOG_PATH)}', flush=True)

total_time = pass1_results['elapsed'] + pass2_results['elapsed']
print(f'\nTotal time: {total_time:.0f}s ({total_time/60:.1f}min)', flush=True)
