"""Diagnostic: trace why library_size = 0 despite TL accepts."""
import os
import sys
sys.path.insert(0, '.')

# SGFE v2.8: Test lumpable-only mode
os.environ['SGFE_LUMPABLE_ONLY'] = '1'

from arc_sgc_phase8_3 import load_arc_tasks
from arc_sgc_residual_solver import RecursiveResidualSolver, HAS_TENSOR_LOGIC
from sgfe_engine import CrossTaskPredicateValidator, SGFEPrimitiveLibrary

print(f'HAS_TENSOR_LOGIC: {HAS_TENSOR_LOGIC}')
print(f'SGFE_LUMPABLE_ONLY: {os.getenv("SGFE_LUMPABLE_ONLY", "0")}')

# Create components
ctv = CrossTaskPredicateValidator()
staging = SGFEPrimitiveLibrary(ctv, require_cross_task=False)
print(f'Staging library require_cross_task: {staging.require_cross_task}')
print(f'Staging library initial size: {staging.size}')

# Create solver
solver = RecursiveResidualSolver(
    max_depth=3, beam_width=8, verbose=True,
    cross_task_validator=ctv
)
print(f'Solver _sgfe_library exists: {solver._sgfe_library is not None}')
print(f'Solver _sgfe_library type: {type(solver._sgfe_library).__name__}')

# Replace library
if solver._sgfe_library:
    solver._sgfe_library = staging
    print(f'Library replaced with staging')
    print(f'solver._sgfe_library is staging: {solver._sgfe_library is staging}')

# Run on one task
tasks = load_arc_tasks('C:/Lean4 Projects/data/arc/training')
task = tasks[5]  # 0520fde7 - one that shows TL:1
print(f'\nRunning task: {task.task_id}')
r = solver.solve_task(task)
print(f'\nResult: d={r["avg_train_energy"]:.4f}')
print(f'Tensor log entries: {len(r.get("tensor_log", []))}')
for entry in r.get('tensor_log', []):
    print(f'  triggered={entry.get("triggered")}, n_accepted={entry.get("n_accepted", 0)}')
    for op in entry.get('ops', []):
        print(f'    op={op.get("op", "?")}, sheaf_energy={op.get("sheaf_energy", "?")}')
print(f'\nStaging library size after: {staging.size}')
print(f'Staging compression_log entries: {len(staging.compression_log)}')
for log in staging.compression_log:
    print(f'  {log}')
