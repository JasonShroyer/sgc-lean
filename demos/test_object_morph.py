"""Test object-level morphology integration."""
import numpy as np
from arc_sgc_phase8_3 import load_arc_tasks
from arc_sgc_residual_solver import _morph_residual_refine, detect_color_roles
from arc_sgc_phase21 import SceneGraphBuilder

tasks = load_arc_tasks('C:/Lean4 Projects/data/arc/training')
# Task 10 (09629e4f): 8 objects of color 8 erased, same-shape
task = tasks[10]
print(f'Task: {task.task_id}')

# Diagnose residual structure
print("\n--- Residual Analysis ---")
builder = SceneGraphBuilder()
for i, ex in enumerate(task.train_examples):
    inp = ex.input_grid.data.numpy()
    out = ex.output_grid.data.numpy()
    roles = detect_color_roles(inp)
    sg = builder.build(ex.input_grid)
    
    # Check MAJORITY objects
    maj_color = None
    for c, r in roles.items():
        if r.upper() == 'MAJORITY':
            maj_color = c
            break
    
    if maj_color:
        maj_objs = [o for o in sg.objects.values() if o.color == maj_color]
        print(f"Ex {i}: MAJORITY color={maj_color}, {len(maj_objs)} objects")
        
        # Check residual near majority objects
        wrong = inp != out
        for obj in maj_objs:
            r1, c1, r2, c2 = obj.bbox
            r1_exp, c1_exp = max(0, r1-2), max(0, c1-2)
            r2_exp, c2_exp = min(inp.shape[0], r2+2), min(inp.shape[1], c2+2)
            
            near_mask = np.zeros(inp.shape, dtype=bool)
            near_mask[r1_exp:r2_exp, c1_exp:c2_exp] = True
            
            wrong_near = wrong & near_mask
            if wrong_near.any():
                # Sample transitions
                for ri in range(inp.shape[0]):
                    for ci in range(inp.shape[1]):
                        if wrong_near[ri, ci]:
                            print(f"    Wrong near obj {obj.obj_id}: ({ri},{ci}) {inp[ri,ci]} -> {out[ri,ci]}")
                            break
                    else:
                        continue
                    break

print("\n--- Running _morph_residual_refine ---")

class IdentityOp:
    name = 'identity'
    def apply(self, grid):
        return grid.copy()

program = IdentityOp()
active_indices = list(range(len(task.train_examples)))

result = _morph_residual_refine(task, program, active_indices, verbose=True)
print(f'\nAccepted ops: {len(result)}')
for op, log in result:
    print(f'  Op: {op.name}')
    print(f'    sheaf_energy: {log.get("sheaf_energy")}')
    print(f'    deltas: {log.get("deltas")}')
    print(f'    source: {log.get("source")}')
