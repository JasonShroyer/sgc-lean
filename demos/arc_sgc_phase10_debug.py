"""
Phase 10 Debug: Analyze near-misses to find what's preventing perfect solves.
"""

import torch
import numpy as np
from pathlib import Path
import sys
import json

sys.path.insert(0, str(Path(__file__).parent))
from arc_sgc_phase8_3 import (
    ARCPhase83Config, ARCGrid, ARCTask, load_arc_tasks,
    detect_objects, compute_defect_energy,
    V_TopEdge, V_ContactDist, V_BoundaryDist, V_BottomEdge,
    CompositePotential, relax_all_colors
)

def printfl(*args, **kwargs):
    print(*args, **kwargs)
    sys.stdout.flush()


def analyze_task(task_id: str, tasks):
    """Deep analysis of a specific task."""
    task = next((t for t in tasks if t.task_id == task_id), None)
    if not task:
        printfl(f"Task {task_id} not found")
        return
    
    printfl(f"\n{'='*60}")
    printfl(f"ANALYZING: {task_id}")
    printfl(f"{'='*60}")
    
    config = ARCPhase83Config()
    
    for i, ex in enumerate(task.train_examples):
        printfl(f"\n--- Example {i+1} ---")
        printfl(f"Input shape: {ex.input_grid.shape}")
        printfl(f"Output shape: {ex.output_grid.shape}")
        
        # Show grids
        printfl(f"\nInput:")
        printfl(ex.input_grid.data.cpu().numpy())
        printfl(f"\nTarget output:")
        printfl(ex.output_grid.data.cpu().numpy())
        
        # Analyze differences
        if ex.input_grid.shape == ex.output_grid.shape:
            diff = (ex.input_grid.data != ex.output_grid.data)
            diff_count = diff.sum().item()
            total = ex.input_grid.data.numel()
            printfl(f"\nDifferences: {diff_count}/{total} pixels ({diff_count/total*100:.1f}%)")
            
            if diff_count > 0:
                diff_positions = torch.argwhere(diff)
                printfl(f"Changed positions: {diff_positions.tolist()[:10]}...")
        
        # Try movement potentials
        potentials = [V_ContactDist(), V_TopEdge(), V_BottomEdge(), V_BoundaryDist()]
        pot_names = ['V_contact', 'V_top', 'V_bottom', 'V_boundary']
        
        printfl(f"\n--- Movement potential results ---")
        for j, (pot, name) in enumerate(zip(potentials, pot_names)):
            for sign in [-1.0, 1.0]:
                weights = np.zeros(4)
                weights[j] = sign
                composite = CompositePotential(potentials, weights)
                result = relax_all_colors(ex.input_grid, composite, config)
                energy = compute_defect_energy(result, ex.output_grid)
                if energy < 0.1:
                    printfl(f"  {'+' if sign>0 else ''}{sign:.0f}*{name}: E={energy:.4f}")
                    if energy < 0.01:
                        printfl(f"    Result:")
                        printfl(result.data.cpu().numpy())


def main():
    paths = ["data/arc/training", "C:/Lean4 Projects/data/arc/training"]
    arc_path = next((p for p in paths if Path(p).exists()), None)
    
    if not arc_path:
        printfl("No data found")
        return
    
    tasks = load_arc_tasks(arc_path, 'cpu')
    
    # Analyze the closest near-misses
    near_miss_ids = ['3906de3d', '11852cab', '3345333e', '2dd70a9a']
    
    for task_id in near_miss_ids:
        analyze_task(task_id, tasks)


if __name__ == "__main__":
    main()
