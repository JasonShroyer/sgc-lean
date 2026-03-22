"""
TENSOR LOGIC BREAKTHROUGH DEMO
===============================

Demonstrates the full Tensor Logic x SGC pipeline:
  1. WAKE (T=0):   Run Boolean solver, find near-misses
  2. DREAM (T>0):  Relax predicates to continuous, gradient descent on defect
  3. CRYSTALLIZE:  Threshold learned predicates back to Boolean
  4. VERIFY:       Check that new predicates produce better solutions

Theory: Domingos (2024) Tensor Logic x SGC defect minimization
  min_Pi eps(Pi,L) = min_{M,C} ||A - M*C*M^T|| = max_Pi I(X_Pi; X_dPi)
  (SGC defect)       (Tucker decomposition)        (RSMI-RG)

All three are the same optimization. We solve it by gradient descent.
"""
import sys
import time
import numpy as np
sys.path.insert(0, '.')

from arc_sgc_phase8_3 import load_arc_tasks, compute_defect_energy
from arc_sgc_residual_solver import RecursiveResidualSolver
from arc_tensor_logic import TensorPredicateLearner, make_tensor_predicate_expr

print("=" * 70, flush=True)
print("  TENSOR LOGIC x SGC: DIFFERENTIABLE PREDICATE DISCOVERY", flush=True)
print("  Domingos (2024) arXiv:2510.12269 + SGC Defect Minimization", flush=True)
print("=" * 70, flush=True)

# Load tasks
tasks = load_arc_tasks('../data/arc/training')
task_by_id = {t.task_id: t for t in tasks}
print(f"\nLoaded {len(tasks)} ARC training tasks", flush=True)

# =====================================================================
# PHASE 1: WAKE (Boolean Mode, T=0)
# Run existing solver, collect near-misses
# =====================================================================
print(f"\n{'='*70}", flush=True)
print("PHASE 1: WAKE (Boolean mode, T=0)", flush=True)
print("  Running solver to find near-miss tasks...", flush=True)
print("="*70, flush=True)

solver = RecursiveResidualSolver(max_depth=3, beam_width=8, verbose=False)

near_misses = []
perfects = []
t0 = time.time()

for ti, task in enumerate(tasks):
    try:
        result = solver.solve_task(task)
        d = result['avg_train_energy']
        elapsed = time.time() - t0
        tag = "PERFECT" if d < 0.001 else (f"near d={d:.4f}" if d < 0.12 else "fail")
        print(f"  [{ti+1:2d}/{len(tasks)}] {task.task_id[:8]} {tag} ({elapsed:.0f}s)", flush=True)

        if d < 0.001:
            perfects.append(task.task_id)
        elif 0.001 < d < 0.15 and result['program'] is not None:
            # Collect detailed data for tensor dream
            grids = [ex.input_grid.data.numpy() for ex in task.train_examples]
            targets = [ex.output_grid.data.numpy() for ex in task.train_examples]

            # Check ALL grids AND targets have same shape (needed for batching)
            all_shapes = set(g.shape for g in grids) | set(t.shape for t in targets)
            if len(all_shapes) > 1:
                continue

            # Compute predictions for defect tracking
            preds = []
            for ex in task.train_examples:
                inp = ex.input_grid.data.numpy()
                try:
                    preds.append(result['program'].apply(inp))
                except Exception:
                    preds = None
                    break

            if preds is None:
                continue

            near_misses.append({
                'task_id': task.task_id,
                'grids': grids,
                'targets': targets,
                'predictions': preds,
                'defect': d,
                'method': result['method'],
                'program': result['program'],
            })
    except Exception:
        pass

wake_time = time.time() - t0
print(f"\n  Wake complete: {len(perfects)}P, {len(near_misses)}N ({wake_time:.0f}s)", flush=True)
print(f"  Near-misses to analyze: {len(near_misses)}", flush=True)

if not near_misses:
    print("  No near-misses found. Exiting.")
    sys.exit(0)

# Show top near-misses
print(f"\n  Top near-misses (closest to perfect):", flush=True)
near_misses.sort(key=lambda x: x['defect'])
for nm in near_misses[:10]:
    n_changed = sum((g != t).sum() for g, t in zip(nm['grids'], nm['targets']))
    n_wrong = sum((p != t).sum() for p, t in zip(nm['predictions'], nm['targets']))
    print(f"    {nm['task_id'][:8]} d={nm['defect']:.4f} "
          f"({n_changed} changed, {n_wrong} still wrong) {nm['method'][:45]}", flush=True)

# =====================================================================
# PHASE 2: DREAM (Continuous Mode, T>0)
# Relax predicates to continuous, gradient descent on defect
# =====================================================================
print(f"\n{'='*70}", flush=True)
print("PHASE 2: DREAM (Continuous mode, T: 1.0 -> 0.1)", flush=True)
print("  Gradient descent on differentiable predicate space...", flush=True)
print("="*70, flush=True)

learner = TensorPredicateLearner(
    n_factors=4,      # Number of spatial regions to discover
    lr=0.05,          # Learning rate
    steps=300,        # Optimization steps
    temperature=1.0,  # Start temperature (anneals to 0.1)
    min_f1=0.25,      # Minimum quality threshold
)

dream_results = []
for nm in near_misses:
    tid = nm['task_id'][:8]

    try:
        # Learn from FULL transformation (input->target), NOT residual.
        # SGC: the defect measures the full coarse-graining quality,
        # not just the incremental error. The tensor factorization needs
        # the complete transformation signal to discover spatial structure.
        discovered = learner.discover_predicates(
            nm['grids'], nm['targets'], predictions=None,
            verbose=False)
    except Exception as e:
        print(f"    {tid}: error - {e}", flush=True)
        continue

    if discovered:
        best = discovered[0]
        tensor_pred = make_tensor_predicate_expr(best, best.weights, best.bias)
        print(f"    {tid}: F1={best.f1:.3f} {tensor_pred.name[:40]} "
              f"({len(discovered)} factors)", flush=True)

        dream_results.append({
            'task_id': nm['task_id'],
            'original_defect': nm['defect'],
            'method': nm['method'],
            'tensor_f1': best.f1,
            'tensor_precision': best.precision,
            'tensor_recall': best.recall,
            'tensor_pred': tensor_pred,
            'top_features': best.top_features[:5],
            'discovered': discovered,
            'nm': nm,
        })
    else:
        print(f"    {tid}: no predicates above threshold", flush=True)

dream_results.sort(key=lambda x: -x['tensor_f1'])
print(f"\n  Total: {len(dream_results)}/{len(near_misses)} tasks with predicates", flush=True)

# =====================================================================
# PHASE 3: CRYSTALLIZE (Boolean Mode, T->0)
# Use learned spatial predicates + color rules to reconstruct output
# =====================================================================
print(f"\n{'='*70}", flush=True)
print("PHASE 3: CRYSTALLIZE & VERIFY", flush=True)
print("  Applying learned tensor factors to reconstruct outputs...", flush=True)
print("="*70, flush=True)

improved = []
for dr in dream_results:
    nm = dr['nm']
    all_factors = dr['discovered']

    # STEP 1: Compute ANALYTIC color rules from the learned spatial partition
    # SGC: first partition (predicates, learned by gradient descent), then
    # compute coarse-grained dynamics (color rules) by counting empirical
    # (input_color -> output_color) transitions within each region.
    # This is the correct RG procedure: block-spin → then compute effective H.
    n_colors = 10
    analytic_rules = {}  # factor_idx -> {input_color: output_color}

    for dp in all_factors:
        counts = np.zeros((n_colors, n_colors), dtype=int)
        for e_idx, (g, t) in enumerate(zip(nm['grids'], nm['targets'])):
            if e_idx >= len(dp.masks):
                continue
            mask = dp.masks[e_idx]
            for r in range(g.shape[0]):
                for c in range(g.shape[1]):
                    if mask[r, c]:
                        counts[int(g[r, c]), int(t[r, c])] += 1

        # For each input color, output = most common target color in this region
        rule = {}
        for ic in range(n_colors):
            if counts[ic].sum() > 0:
                rule[ic] = int(np.argmax(counts[ic]))
            else:
                rule[ic] = ic  # identity if no data
        analytic_rules[dp.factor_idx] = rule

    # STEP 2: Apply factors with analytic color rules
    new_defects = []
    for e_idx, (g, t, p) in enumerate(zip(nm['grids'], nm['targets'], nm['predictions'])):
        try:
            corrected = p.copy()

            for dp in all_factors:
                if e_idx >= len(dp.masks):
                    continue
                mask = dp.masks[e_idx]
                rule = analytic_rules.get(dp.factor_idx, {})

                # Apply: for each pixel in region, map input color -> learned output
                for r in range(g.shape[0]):
                    for c in range(g.shape[1]):
                        if mask[r, c]:
                            inp_c = int(g[r, c])
                            out_c = rule.get(inp_c, inp_c)
                            corrected[r, c] = out_c

            new_d = compute_defect_energy(corrected, t)
            new_defects.append(new_d)
        except Exception as e:
            print(f"      Ex{e_idx} error: {e}", flush=True)

    if new_defects:
        avg_new = np.mean(new_defects)
        improvement = nm['defect'] - avg_new

        print(f"    {nm['task_id'][:8]}: d={nm['defect']:.4f} -> {avg_new:.4f} "
              f"(delta={improvement:+.4f})", flush=True)

        # Show per-factor analytic rules
        for dp in all_factors:
            rule = analytic_rules.get(dp.factor_idx, {})
            changes = [(ic, oc) for ic, oc in rule.items() if ic != oc]
            if changes:
                print(f"      Factor {dp.factor_idx}: "
                      f"{', '.join(f'{ic}->{oc}' for ic,oc in changes[:5])}", flush=True)

        if improvement > 0.001:
            improved.append({
                'task_id': nm['task_id'],
                'old_defect': nm['defect'],
                'new_defect': avg_new,
                'improvement': improvement,
                'tensor_f1': dr['tensor_f1'],
                'predicate_name': dr['tensor_pred'].name,
                'features': dr['top_features'],
            })
    else:
        print(f"    {nm['task_id'][:8]}: no valid defects computed", flush=True)

# Sort by improvement
improved.sort(key=lambda x: -x['improvement'])

print(f"\n  Tasks improved by tensor predicates: {len(improved)}/{len(dream_results)}", flush=True)

if improved:
    print(f"\n  BREAKTHROUGH RESULTS:", flush=True)
    print(f"  {'Task':<12} {'Old d':>8} {'New d':>8} {'Impr':>8} {'F1':>6}  Predicate", flush=True)
    print(f"  {'-'*75}", flush=True)
    for imp in improved[:15]:
        print(f"  {imp['task_id'][:10]:<12} {imp['old_defect']:8.4f} "
              f"{imp['new_defect']:8.4f} {imp['improvement']:+8.4f} "
              f"{imp['tensor_f1']:6.3f}  {imp['predicate_name'][:35]}", flush=True)

    total_imp = sum(i['improvement'] for i in improved)
    print(f"\n  Total defect reduction: {total_imp:+.4f}", flush=True)
    print(f"  Average per task: {total_imp/len(improved):+.4f}", flush=True)

    # Check if any task was pushed to perfect
    new_perfects = [i for i in improved if i['new_defect'] < 0.001]
    if new_perfects:
        print(f"\n  *** NEW PERFECT SOLVES: {len(new_perfects)} ***", flush=True)
        for np_ in new_perfects:
            print(f"    {np_['task_id'][:8]}: d={np_['old_defect']:.4f} -> 0.0000", flush=True)

# =====================================================================
# SUMMARY
# =====================================================================
print(f"\n{'='*70}", flush=True)
print("SUMMARY: TENSOR LOGIC x SGC PREDICATE DISCOVERY", flush=True)
print("="*70, flush=True)
print(f"  Theory: Predicates = coarse-grainings = tensor factors", flush=True)
print(f"  Method: Gradient descent on defect in differentiable predicate space", flush=True)
print(f"  Temperature annealing: T=1.0 (explore) -> T=0.1 (crystallize)", flush=True)
print(f"", flush=True)
print(f"  Wake phase: {len(perfects)} perfect, {len(near_misses)} near-misses ({wake_time:.0f}s)", flush=True)
print(f"  Dream phase: {len(dream_results)} tasks with discovered predicates", flush=True)
print(f"  Verify phase: {len(improved)} tasks improved by tensor predicates", flush=True)
if improved:
    total_imp = sum(i['improvement'] for i in improved)
    print(f"  Total defect reduction: {total_imp:+.4f}", flush=True)
print(f"", flush=True)
print(f"  Key features discovered:", flush=True)
seen_features = set()
for dr in dream_results[:10]:
    for fname, fweight in dr['top_features'][:2]:
        if fname not in seen_features:
            seen_features.add(fname)
            sign = '+' if fweight > 0 else '-'
            print(f"    {sign}{fname} (w={fweight:.3f})", flush=True)
print(f"\n{'='*70}", flush=True)
print("TENSOR LOGIC DEMO COMPLETE", flush=True)
print("="*70, flush=True)
