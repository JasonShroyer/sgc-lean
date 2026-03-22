"""
Diagnose near-miss tasks to identify what new predicates are needed.
For each near-miss, shows:
  - What the program predicts vs expected
  - Which pixels are wrong
  - What predicates match wrong vs correct pixels
  - What CONJUNCTION would fix the error
"""
import numpy as np
import sys
sys.path.insert(0, '.')

from arc_sgc_phase8_3 import load_arc_tasks
from arc_sgc_residual_solver import (
    RecursiveResidualSolver, _compute_pixel_predicates,
    _make_predicated_fill, _make_predicated_recolor,
)
from arc_sgc_sie import compute_transformation_map

# Load tasks
tasks = load_arc_tasks('C:/Lean4 Projects/data/arc/training')
task_map = {t.task_id[:8]: t for t in tasks}

# Target near-miss tasks (from logs)
TARGETS = [
    '2281f1f4',  # d=0.0100 fill(2|cross_5)
    '11852cab',  # d=0.0300 fill(2|cross_3)
    '4093f84a',  # d=0.0153 fill(5|between_fg_h&adj_to_5)
    '025d127b',  # d=0.0200 shift:(0,1)
    '1a07d186',  # d=0.0142 erase_dynamic(small_obj)
    '3345333e',  # d=0.0352 operator_transfer
]

solver = RecursiveResidualSolver(max_depth=3, beam_width=5, verbose=False)

for tid in TARGETS:
    task = task_map.get(tid)
    if not task:
        print(f"\n=== {tid}: NOT FOUND ===")
        continue
    
    print(f"\n{'='*70}")
    print(f"TASK {tid}")
    print(f"{'='*70}")
    
    # Solve the task
    result = solver.solve_task(task)
    program = result.get('program')
    if not program:
        print(f"  No program found")
        continue
    
    method = result.get('method', '?')
    print(f"  Method: {method}")
    print(f"  Avg defect: {result.get('avg_train_energy', '?'):.4f}")
    
    # Analyze residual per training example
    for ex_idx, ex in enumerate(task.train_examples):
        inp = ex.input_grid.data.numpy()
        tgt = ex.output_grid.data.numpy()
        
        try:
            pred_out = program.apply(inp)
        except Exception as e:
            print(f"  Example {ex_idx}: apply failed: {e}")
            continue
        
        if pred_out.shape != tgt.shape:
            print(f"  Example {ex_idx}: shape mismatch {pred_out.shape} vs {tgt.shape}")
            continue
        
        wrong = pred_out != tgt
        n_wrong = wrong.sum()
        n_total = wrong.size
        defect = n_wrong / n_total
        
        print(f"\n  --- Example {ex_idx} ({inp.shape[0]}x{inp.shape[1]}) defect={defect:.4f} ({n_wrong}/{n_total} wrong) ---")
        
        if n_wrong == 0:
            print(f"    PERFECT")
            continue
        
        # Show wrong pixel details
        wrong_coords = list(zip(*np.where(wrong)))
        print(f"    Wrong pixels ({len(wrong_coords)}):")
        for r, c in wrong_coords[:15]:  # show first 15
            print(f"      ({r},{c}): input={inp[r,c]} predicted={pred_out[r,c]} expected={tgt[r,c]}")
        if len(wrong_coords) > 15:
            print(f"      ... and {len(wrong_coords)-15} more")
        
        # Classify errors
        error_types = {}
        for r, c in wrong_coords:
            key = (int(inp[r,c]), int(pred_out[r,c]), int(tgt[r,c]))
            error_types.setdefault(key, []).append((r,c))
        
        print(f"    Error classes (input_color, predicted, expected):")
        for (ic, pc, ec), pixels in sorted(error_types.items(), key=lambda x: -len(x[1])):
            print(f"      ({ic}->{pc}, should be {ec}): {len(pixels)} pixels")
        
        # Compute predicates and find which ones separate wrong from correct
        preds = _compute_pixel_predicates(inp)
        
        # For each error class, find best separating predicate
        for (ic, pc, ec), pixels in sorted(error_types.items(), key=lambda x: -len(x[1])):
            if len(pixels) < 1:
                continue
            
            target = np.zeros_like(wrong, dtype=bool)
            for r, c in pixels:
                target[r, c] = True
            target_count = target.sum()
            
            # Also compute "correct pixels of same predicted color"
            # These are pixels where pred_out == ec and tgt == ec
            correct_same = (pred_out == ec) & (tgt == ec)
            
            print(f"\n    Separating predicates for error class ({ic}->{pc}, should be {ec}):")
            print(f"      Target: {target_count} wrong pixels")
            print(f"      Correct same-output: {correct_same.sum()} pixels")
            
            scored = []
            for pn, pm in preds.items():
                tp = int((pm & target).sum())
                fp_wrong = int((pm & wrong & ~target).sum())  # wrong pixels NOT in this class
                fp_correct = int((pm & ~wrong).sum())  # correct pixels matched
                fn = target_count - tp
                
                # What matters: does this predicate separate wrong from correct?
                # High tp/target_count AND low fp_correct/pm.sum()
                total_matched = int(pm.sum())
                if total_matched == 0:
                    continue
                
                precision_vs_wrong = tp / max(tp + fp_correct + fp_wrong, 1)
                recall = tp / max(target_count, 1)
                
                if tp > 0 and recall >= 0.3:
                    scored.append((pn, precision_vs_wrong, recall, tp, total_matched))
            
            scored.sort(key=lambda x: (-x[1], -x[2]))
            
            # Show top 10 predicates
            for pn, prec, rec, tp, total in scored[:10]:
                f1 = 2*prec*rec / max(prec+rec, 1e-10)
                marker = " ***" if f1 > 0.8 else " **" if f1 > 0.5 else ""
                print(f"      {pn:40s} prec={prec:.3f} rec={rec:.3f} F1={f1:.3f} tp={tp}/{target_count} matched={total}{marker}")
            
            if not scored:
                print(f"      (no predicates with recall >= 0.3)")

print("\nDone.")
