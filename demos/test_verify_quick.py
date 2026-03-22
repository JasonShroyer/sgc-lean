"""Quick test: verify analytic color rules on the 3 tasks that produced predicates."""
import sys, time
import numpy as np
sys.path.insert(0, '.')

from arc_sgc_phase8_3 import load_arc_tasks
from arc_sgc_residual_solver import RecursiveResidualSolver

def defect(pred, target):
    """Pixel-level defect between numpy arrays."""
    if pred.shape != target.shape:
        return 1.0
    return float((pred != target).sum()) / max(target.size, 1)
from arc_tensor_logic import TensorPredicateLearner, make_tensor_predicate_expr

tasks = load_arc_tasks('../data/arc/training')
task_by_id = {t.task_id: t for t in tasks}

# These 3 tasks produced predicates in the full run
test_ids = ['23581191', '0962bcdd', '31aa019c']
solver = RecursiveResidualSolver(max_depth=3, beam_width=8, verbose=False)

learner = TensorPredicateLearner(
    n_factors=4, lr=0.05, steps=300, temperature=1.0, min_f1=0.20)

for tid in test_ids:
    # Find task
    task = None
    for t in tasks:
        if t.task_id.startswith(tid):
            task = t
            break
    if task is None:
        print(f"Task {tid} not found", flush=True)
        continue

    print(f"\n{'='*60}", flush=True)
    print(f"Task: {task.task_id}", flush=True)

    # Solve with existing solver
    result = solver.solve_task(task)
    d = result['avg_train_energy']
    print(f"  Solver: d={d:.4f} {result['method'][:50]}", flush=True)

    grids = [ex.input_grid.data.numpy() for ex in task.train_examples]
    targets = [ex.output_grid.data.numpy() for ex in task.train_examples]

    # Check shapes
    all_shapes = set(g.shape for g in grids) | set(t.shape for t in targets)
    if len(all_shapes) > 1:
        print(f"  Different shapes, skipping", flush=True)
        continue

    # Get predictions
    preds = []
    for ex in task.train_examples:
        try:
            preds.append(result['program'].apply(ex.input_grid.data.numpy()))
        except Exception:
            preds = None
            break
    if preds is None:
        print(f"  Cannot compute predictions", flush=True)
        continue

    # Dream: learn from full transformation
    print(f"  Dream phase (learning full input->target transformation)...", flush=True)
    discovered = learner.discover_predicates(
        grids, targets, predictions=None, verbose=True)
    print(f"  Discovered {len(discovered)} factors", flush=True)

    if not discovered:
        continue

    # Analytic color rules
    n_colors = 10
    print(f"\n  Analytic color rules (from partition):", flush=True)
    for dp in discovered:
        counts = np.zeros((n_colors, n_colors), dtype=int)
        for e_idx, (g, t) in enumerate(zip(grids, targets)):
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
        n_pixels = sum(m.sum() for m in dp.masks)
        print(f"    Factor {dp.factor_idx} ({n_pixels} pixels, F1={dp.f1:.3f}): "
              f"{changes if changes else 'identity'}", flush=True)

        # Apply and verify
        for e_idx, (g, t, p) in enumerate(zip(grids, targets, preds)):
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
            old_wrong = int((p != t).sum())
            new_wrong = int((corrected != t).sum())
            delta = old_d - new_d
            print(f"      Ex{e_idx}: d={old_d:.4f}->{new_d:.4f} (delta={delta:+.4f}) "
                  f"wrong: {old_wrong}->{new_wrong}", flush=True)

print(f"\n{'='*60}", flush=True)
print("DONE", flush=True)
