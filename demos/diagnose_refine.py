"""
Focused diagnostic: why doesn't refinement convert task 11852cab (d=0.03)?
The diagnostic showed cross_8 has F1=0.75 for the missing pixels.
Refinement SHOULD find this and add fill(3|cross_8). Why doesn't it?
"""
import numpy as np
import sys
sys.path.insert(0, '.')

from arc_sgc_phase8_3 import load_arc_tasks
from arc_sgc_residual_solver import (
    RecursiveResidualSolver, _compute_pixel_predicates,
)
from arc_sgc_sie import compute_transformation_map

tasks = load_arc_tasks('C:/Lean4 Projects/data/arc/training')
task_map = {t.task_id[:8]: t for t in tasks}

# Focus on 11852cab: fill(2|cross_3) d=0.03
task = task_map['11852cab']
solver = RecursiveResidualSolver(max_depth=3, beam_width=5, verbose=True)
result = solver.solve_task(task)
program = result.get('program')
method = result.get('method', '?')
defect = result.get('avg_train_energy', 1.0)

print(f"\n{'='*60}")
print(f"Result: {method}, test_d={defect:.4f}")
# Compute training defect
train_d = []
for ex in task.train_examples:
    inp = ex.input_grid.data.numpy()
    tgt = ex.output_grid.data.numpy()
    try:
        pred_out = program.apply(inp)
        train_d.append(np.mean(pred_out != tgt) if pred_out.shape == tgt.shape else 1.0)
    except: train_d.append(1.0)
print(f"Train defects: {[f'{d:.4f}' for d in train_d]}, avg={np.mean(train_d):.4f}")
print(f"{'='*60}")

if program and 0.001 < defect < 0.15:
    print("\nManual refinement analysis:")
    # Compute residual
    for ex_idx, ex in enumerate(task.train_examples):
        inp = ex.input_grid.data.numpy()
        tgt = ex.output_grid.data.numpy()
        try:
            pred_out = program.apply(inp)
        except:
            continue
        if pred_out.shape != tgt.shape:
            continue
        
        wrong = pred_out != tgt
        n_wrong = wrong.sum()
        if n_wrong == 0:
            print(f"  Example {ex_idx}: PERFECT")
            continue
        
        print(f"\n  Example {ex_idx}: {n_wrong} wrong pixels, d={n_wrong/wrong.size:.4f}")
        
        # Compute residual transformation map
        res_tmap = np.zeros_like(tgt, dtype=np.int32)
        res_tmap[wrong] = tgt[wrong] + 1
        
        res_types = set(np.unique(res_tmap).tolist())
        res_types.discard(0)
        print(f"  Residual types: {res_types}")
        
        preds = _compute_pixel_predicates(inp)
        pred_names = sorted(preds.keys())
        print(f"  Predicate vocab size: {len(pred_names)}")
        
        for rt in sorted(res_types):
            out_color = rt - 1
            rt_mask = (res_tmap == rt)
            n_rt = rt_mask.sum()
            print(f"\n  Residual type {rt} (should be color {out_color}): {n_rt} pixels")
            
            # Score predicates
            scored = []
            for pn in pred_names:
                pm = preds[pn]
                if pm.shape != rt_mask.shape:
                    continue
                tp = int((pm & rt_mask).sum())
                fp = int((pm & ~rt_mask).sum())
                fn = int((~pm & rt_mask).sum())
                prec = tp / max(tp + fp, 1)
                rec = tp / max(tp + fn, 1)
                if prec >= 0.3 and rec >= 0.1:
                    f1 = 2 * prec * rec / max(prec + rec, 1e-10)
                    scored.append((pn, prec, rec, f1, tp))
            
            scored.sort(key=lambda x: -x[3])
            print(f"  Top predicates (prec>=0.3, rec>=0.1):")
            for pn, prec, rec, f1, tp in scored[:10]:
                marker = " PASS" if prec >= 0.5 and rec >= 0.15 and f1 >= 0.25 else ""
                print(f"    {pn:40s} P={prec:.3f} R={rec:.3f} F1={f1:.3f} tp={tp}{marker}")
            
            if not scored:
                print(f"    (none)")
    
    # Check common_names
    print(f"\n--- Common predicate names across examples ---")
    all_names = None
    for ex in task.train_examples:
        inp = ex.input_grid.data.numpy()
        preds = _compute_pixel_predicates(inp)
        names = set(preds.keys())
        all_names = names if all_names is None else all_names & names
    
    # Check if cross_8 is in common names
    for check in ['cross_8', 'cross_3', 'near8_1', 'between_fg_v', 'on_border']:
        status = "YES" if check in all_names else "NO"
        print(f"  {check}: {status}")
    
    print(f"  Total common predicates: {len(all_names)}")

print("\nDone.")
