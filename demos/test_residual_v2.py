"""Test the new discover_residual_predicate: direct binary classification of wrong pixels."""
import sys, time
import numpy as np
sys.path.insert(0, '.')

from arc_sgc_phase8_3 import load_arc_tasks
from arc_sgc_residual_solver import RecursiveResidualSolver
from arc_tensor_logic import TensorPredicateLearner, make_tensor_predicate_expr

def defect(pred, target):
    if pred.shape != target.shape:
        return 1.0
    return float((pred != target).sum()) / max(target.size, 1)

tasks = load_arc_tasks('../data/arc/training')
solver = RecursiveResidualSolver(max_depth=3, beam_width=8, verbose=False)

# Find near-misses with > 5 wrong pixels
print("Finding near-misses...", flush=True)
candidates = []
for task in tasks:
    try:
        result = solver.solve_task(task)
        d = result['avg_train_energy']
        if 0.005 < d < 0.15 and result['program'] is not None:
            grids = [ex.input_grid.data.numpy() for ex in task.train_examples]
            targets = [ex.output_grid.data.numpy() for ex in task.train_examples]
            all_shapes = set(g.shape for g in grids) | set(t.shape for t in targets)
            if len(all_shapes) > 1:
                continue
            preds = []
            for ex in task.train_examples:
                try:
                    preds.append(result['program'].apply(ex.input_grid.data.numpy()))
                except Exception:
                    preds = None
                    break
            if preds is None:
                continue
            n_wrong = sum(int((p != t).sum()) for p, t in zip(preds, targets))
            if n_wrong >= 3:
                candidates.append({
                    'task_id': task.task_id, 'grids': grids, 'targets': targets,
                    'predictions': preds, 'defect': d, 'method': result['method'],
                    'n_wrong': n_wrong,
                })
    except Exception:
        pass

candidates.sort(key=lambda x: -x['n_wrong'])
print(f"Found {len(candidates)} candidates\n", flush=True)

learner = TensorPredicateLearner(
    n_factors=4, lr=0.05, steps=300, temperature=1.0, min_f1=0.15)

print("=" * 60, flush=True)
print("RESIDUAL PREDICATE DISCOVERY (direct binary classification)", flush=True)
print("=" * 60, flush=True)

improved_count = 0
for nm in candidates[:10]:
    tid = nm['task_id'][:8]
    print(f"\n  {tid} (d={nm['defect']:.4f}, {nm['n_wrong']} wrong)", flush=True)

    discovered = learner.discover_residual_predicate(
        nm['grids'], nm['targets'], nm['predictions'], verbose=True)

    if not discovered:
        print(f"    No predicates found", flush=True)
        continue

    best = discovered[0]
    tp = make_tensor_predicate_expr(best, best.weights, best.bias)
    print(f"    Best: F1={best.f1:.3f} P={best.precision:.3f} R={best.recall:.3f} "
          f"{tp.name[:40]}", flush=True)

    # Apply analytic color rule within the predicate region
    n_colors = 10
    counts = np.zeros((n_colors, n_colors), dtype=int)
    for e_idx, (g, t) in enumerate(zip(nm['grids'], nm['targets'])):
        if e_idx < len(best.masks):
            mask = best.masks[e_idx]
            for r in range(g.shape[0]):
                for c in range(g.shape[1]):
                    if mask[r, c]:
                        counts[int(g[r, c]), int(t[r, c])] += 1

    rule = {}
    for ic in range(n_colors):
        if counts[ic].sum() > 0:
            rule[ic] = int(np.argmax(counts[ic]))
        else:
            rule[ic] = ic
    changes = [(ic, oc) for ic, oc in rule.items() if ic != oc]
    if changes:
        print(f"    Color rules: {', '.join(f'{ic}->{oc}' for ic, oc in changes[:6])}", flush=True)

    # Verify
    for e_idx, (g, t, p) in enumerate(zip(nm['grids'], nm['targets'], nm['predictions'])):
        corrected = p.copy()
        if e_idx < len(best.masks):
            mask = best.masks[e_idx]
            for r in range(g.shape[0]):
                for c in range(g.shape[1]):
                    if mask[r, c]:
                        corrected[r, c] = rule.get(int(g[r, c]), int(g[r, c]))

        old_d = defect(p, t)
        new_d = defect(corrected, t)
        old_w = int((p != t).sum())
        new_w = int((corrected != t).sum())
        tag = "BETTER" if new_d < old_d - 0.001 else ("SAME" if abs(new_d - old_d) < 0.001 else "WORSE")
        print(f"    Ex{e_idx}: d={old_d:.4f}->{new_d:.4f} wrong:{old_w}->{new_w} [{tag}]", flush=True)

    avg_old = nm['defect']
    avg_new = np.mean([defect(
        np.where(best.masks[i] if i < len(best.masks) else np.zeros_like(p),
                 np.vectorize(rule.get)(g.astype(int), g.astype(int)), p)
        if i < len(best.masks) else p, t)
        for i, (g, t, p) in enumerate(zip(nm['grids'], nm['targets'], nm['predictions']))])
    if avg_new < avg_old - 0.001:
        improved_count += 1
        print(f"    >>> IMPROVED: {avg_old:.4f} -> {avg_new:.4f}", flush=True)

print(f"\n{'='*60}", flush=True)
print(f"Total improved: {improved_count}/{min(len(candidates), 10)}", flush=True)
print("=" * 60, flush=True)
