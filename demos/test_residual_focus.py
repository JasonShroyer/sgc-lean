"""
Focused test: Learn predicates targeting the RESIDUAL of near-miss tasks.
Uses heavy residual weighting (20x) and more optimization steps.
"""
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

# Find near-misses with meaningful residuals
print("Finding near-misses with > 5 wrong pixels...", flush=True)
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
            if n_wrong >= 5:
                candidates.append({
                    'task_id': task.task_id,
                    'grids': grids, 'targets': targets, 'predictions': preds,
                    'defect': d, 'method': result['method'], 'n_wrong': n_wrong,
                })
                print(f"  {task.task_id[:8]} d={d:.4f} ({n_wrong} wrong) "
                      f"{result['method'][:40]}", flush=True)
    except Exception:
        pass

print(f"\nFound {len(candidates)} candidates", flush=True)
if not candidates:
    sys.exit(0)

# Sort by number of wrong pixels (more signal = easier to learn)
candidates.sort(key=lambda x: -x['n_wrong'])

# Test tensor logic with aggressive residual-focused settings
learner = TensorPredicateLearner(
    n_factors=4, lr=0.08, steps=400, temperature=1.0, min_f1=0.10)

print(f"\n{'='*60}", flush=True)
print("TENSOR LOGIC: RESIDUAL-FOCUSED PREDICATE DISCOVERY", flush=True)
print("="*60, flush=True)

total_improved = 0
for nm in candidates[:10]:
    tid = nm['task_id'][:8]
    print(f"\n  Task {tid} (d={nm['defect']:.4f}, {nm['n_wrong']} wrong pixels)", flush=True)
    print(f"  Solver: {nm['method'][:55]}", flush=True)

    # Learn from residual (predictions vs targets)
    discovered = learner.discover_predicates(
        nm['grids'], nm['targets'], nm['predictions'], verbose=True)

    if not discovered:
        # Fallback: learn from full transformation
        print(f"    Fallback: learning from full transformation...", flush=True)
        discovered = learner.discover_predicates(
            nm['grids'], nm['targets'], predictions=None, verbose=False)

    if not discovered:
        print(f"    No predicates found", flush=True)
        continue

    # Apply analytic color rules from learned partition
    n_colors = 10
    for dp in discovered[:3]:
        # Compute analytic rule within this factor's region
        counts = np.zeros((n_colors, n_colors), dtype=int)
        for e_idx, (g, t) in enumerate(zip(nm['grids'], nm['targets'])):
            if e_idx >= len(dp.masks):
                continue
            mask = dp.masks[e_idx]
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

        # Apply and measure improvement
        improvements = []
        for e_idx, (g, t, p) in enumerate(zip(nm['grids'], nm['targets'], nm['predictions'])):
            corrected = p.copy()
            if e_idx < len(dp.masks):
                mask = dp.masks[e_idx]
                for r in range(g.shape[0]):
                    for c in range(g.shape[1]):
                        if mask[r, c]:
                            inp_c = int(g[r, c])
                            out_c = rule.get(inp_c, inp_c)
                            corrected[r, c] = out_c

            old_d = defect(p, t)
            new_d = defect(corrected, t)
            old_w = int((p != t).sum())
            new_w = int((corrected != t).sum())
            improvements.append((old_d, new_d, old_w, new_w))

        avg_old = np.mean([x[0] for x in improvements])
        avg_new = np.mean([x[1] for x in improvements])
        delta = avg_old - avg_new

        tp = make_tensor_predicate_expr(dp, dp.weights, dp.bias)
        n_pixels = sum(int(m.sum()) for m in dp.masks)
        print(f"    Factor {dp.factor_idx} (F1={dp.f1:.3f}, {n_pixels}px): "
              f"{tp.name[:35]}", flush=True)
        if changes:
            print(f"      Rules: {', '.join(f'{ic}->{oc}' for ic,oc in changes[:5])}", flush=True)
        for i, (od, nd, ow, nw) in enumerate(improvements):
            tag = "BETTER" if nd < od - 0.001 else ("SAME" if abs(nd-od) < 0.001 else "WORSE")
            print(f"      Ex{i}: d={od:.4f}->{nd:.4f} wrong:{ow}->{nw} [{tag}]", flush=True)

        if delta > 0.001:
            total_improved += 1
            print(f"      >>> IMPROVEMENT: avg d delta = {delta:+.4f}", flush=True)

print(f"\n{'='*60}", flush=True)
print(f"Total tasks improved: {total_improved}", flush=True)
print("="*60, flush=True)
