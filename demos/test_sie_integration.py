"""Test SIE integration into the residual solver."""
import sys
sys.path.insert(0, '.')
from arc_sgc_phase8_3 import load_arc_tasks
from arc_sgc_residual_solver import RecursiveResidualSolver

tasks = load_arc_tasks('C:/Lean4 Projects/data/arc/training')
print(f'Loaded {len(tasks)} tasks')

# Focus on tasks where SIE found good structure
target_ids = [
    '00d62c1b',  # SIE defect=0.00, known perfect
    '3aa6fb7a',  # SIE defect=0.00, known perfect
    '4258a5f9',  # known perfect
    '2281f1f4',  # SIE defect=0.10
    '22168020',  # SIE defect=0.13
    '2204b7a8',  # SIE defect=0.14
    '150deff5',  # SIE defect=0.22
    '0ca9ddb6',  # SIE defect=0.50
    '08ed6ac7',  # SIE defect=0.38
    '0dfd9992',  # SIE defect=0.36
]

solver_sie = RecursiveResidualSolver(max_depth=3, beam_width=8, verbose=False, use_sie=True)
solver_base = RecursiveResidualSolver(max_depth=3, beam_width=8, verbose=False, use_sie=False)

print(f"\n{'Task':<14} {'SIE Result':<14} {'Base Result':<14} {'SIE Method':<50}")
print("-" * 92)

sie_wins = 0
base_wins = 0
both_win = 0

for task in tasks:
    if task.task_id not in target_ids:
        continue

    r_sie = solver_sie.solve_task(task)
    r_base = solver_base.solve_task(task)

    sie_tag = "PERFECT" if r_sie['is_perfect'] else f"E={r_sie['avg_train_energy']:.4f}"
    base_tag = "PERFECT" if r_base['is_perfect'] else f"E={r_base['avg_train_energy']:.4f}"

    sie_method = r_sie['method'][:50]

    marker = ""
    if r_sie['is_perfect'] and not r_base['is_perfect']:
        marker = " <-- SIE WIN"
        sie_wins += 1
    elif r_base['is_perfect'] and not r_sie['is_perfect']:
        marker = " <-- BASE WIN"
        base_wins += 1
    elif r_sie['is_perfect'] and r_base['is_perfect']:
        both_win += 1

    print(f"{task.task_id:<14} {sie_tag:<14} {base_tag:<14} {sie_method}{marker}")

print(f"\nSummary: SIE-only wins={sie_wins}, Base-only wins={base_wins}, Both={both_win}")
