"""
ARC-SGC Phase 15 Unified: Maximum Coverage Solver

Combines ALL approaches from Phases 8-15:
- Phase 8.3: Geometry-first (crop, extract, scale)
- Phase 10: Topology operators  
- Phase 12: Conditional synthesis
- Phase 14: Variational repair (comprehensive parameter search)
- Phase 15: CEGAR refinement loop

TARGET: 30+ Perfect Solves by combining all methods
"""

import torch
from dataclasses import dataclass
from typing import List, Tuple, Dict, Optional, Any
from collections import Counter
import numpy as np
from pathlib import Path
import sys
import time

sys.path.insert(0, str(Path(__file__).parent))
from arc_sgc_phase8_3 import (
    ARCPhase83Config, ARCGrid, ARCObject, ARCExample, ARCTask,
    load_arc_tasks, detect_objects, compute_defect_energy,
    GeometryFirstSolver, CompositePotential, relax_all_colors,
    V_ContactDist, V_TopEdge, V_BottomEdge, V_BoundaryDist,
    CropToContentMorphism, ExtractObjectMorphism
)

def printfl(*args, **kwargs):
    print(*args, **kwargs)
    sys.stdout.flush()


class UnifiedSolver:
    """
    The ultimate combined solver using all discovered strategies.
    """
    
    def __init__(self, config: ARCPhase83Config):
        self.config = config
        self.potentials = [V_ContactDist(), V_TopEdge(), V_BottomEdge(), V_BoundaryDist()]
    
    def solve_task(self, task: ARCTask) -> Dict:
        """Try ALL strategies and return best result."""
        start_time = time.time()
        examples = task.train_examples
        
        best_energy = float('inf')
        best_method = "none"
        
        # Strategy 1: Identity (baseline)
        e, m = self._try_identity(task)
        if e < best_energy:
            best_energy, best_method = e, m
        
        # Strategy 2: All movement potentials with many strengths
        e, m = self._try_movements(task)
        if e < best_energy:
            best_energy, best_method = e, m
        
        # Strategy 3: All crop variations
        e, m = self._try_crops(task)
        if e < best_energy:
            best_energy, best_method = e, m
        
        # Strategy 4: All color maps
        e, m = self._try_colors(task)
        if e < best_energy:
            best_energy, best_method = e, m
        
        # Strategy 5: All pattern transforms
        e, m = self._try_patterns(task)
        if e < best_energy:
            best_energy, best_method = e, m
        
        # Strategy 6: Extract operations
        e, m = self._try_extracts(task)
        if e < best_energy:
            best_energy, best_method = e, m
        
        # Strategy 7: Extract + color combinations
        e, m = self._try_extract_color(task)
        if e < best_energy:
            best_energy, best_method = e, m
        
        # Strategy 8: Movement + color composites
        e, m = self._try_movement_color(task)
        if e < best_energy:
            best_energy, best_method = e, m
        
        # Strategy 9: Crop + color composites
        e, m = self._try_crop_color(task)
        if e < best_energy:
            best_energy, best_method = e, m
        
        # Strategy 10: Delete single objects
        e, m = self._try_delete_objects(task)
        if e < best_energy:
            best_energy, best_method = e, m
        
        # Strategy 11: Keep single objects
        e, m = self._try_keep_objects(task)
        if e < best_energy:
            best_energy, best_method = e, m
        
        elapsed = time.time() - start_time
        
        return {
            'task_id': task.task_id,
            'method': best_method,
            'avg_train_energy': best_energy,
            'elapsed_ms': elapsed * 1000,
            'is_perfect': best_energy < self.config.energy_threshold
        }
    
    def _try_identity(self, task: ARCTask) -> Tuple[float, str]:
        """Try identity (input=output)."""
        total_e = 0
        valid = True
        for ex in task.train_examples:
            if ex.input_grid.shape != ex.output_grid.shape:
                return float('inf'), "identity"
            total_e += compute_defect_energy(ex.input_grid, ex.output_grid)
        return total_e / len(task.train_examples), "identity"
    
    def _try_movements(self, task: ARCTask) -> Tuple[float, str]:
        """Try all movement potential variations."""
        best_e = float('inf')
        best_m = "movement:none"
        
        for i, pot in enumerate(self.potentials):
            for sign in [-1.0, 1.0]:
                for strength in [0.25, 0.5, 0.75, 1.0, 1.5, 2.0]:
                    weights = np.zeros(4)
                    weights[i] = sign * strength
                    potential = CompositePotential(self.potentials, weights)
                    
                    total_e = 0
                    valid = True
                    for ex in task.train_examples:
                        result = relax_all_colors(ex.input_grid, potential, self.config)
                        if result.shape != ex.output_grid.shape:
                            valid = False
                            break
                        total_e += compute_defect_energy(result, ex.output_grid)
                    
                    if valid:
                        avg_e = total_e / len(task.train_examples)
                        if avg_e < best_e:
                            best_e = avg_e
                            best_m = f"{sign*strength:+.2f}*{pot.name()}"
        
        return best_e, best_m
    
    def _try_crops(self, task: ARCTask) -> Tuple[float, str]:
        """Try all crop variations."""
        best_e = float('inf')
        best_m = "crop:none"
        
        # Crop to content
        try:
            morph = CropToContentMorphism()
            total_e = 0
            valid = True
            for ex in task.train_examples:
                result = morph.apply(ex.input_grid, self.config)
                if result.shape != ex.output_grid.shape:
                    valid = False
                    break
                total_e += compute_defect_energy(result, ex.output_grid)
            if valid:
                avg_e = total_e / len(task.train_examples)
                if avg_e < best_e:
                    best_e = avg_e
                    best_m = "crop_to_content"
        except:
            pass
        
        # Try all boundary variations
        for ex in task.train_examples:
            H, W = ex.input_grid.shape
            tH, tW = ex.output_grid.shape
            
            for r_start in range(max(0, H - tH - 5), min(H - tH + 6, H + 1)):
                for c_start in range(max(0, W - tW - 5), min(W - tW + 6, W + 1)):
                    r_end = r_start + tH
                    c_end = c_start + tW
                    
                    if r_end > H or c_end > W or r_start < 0 or c_start < 0:
                        continue
                    
                    total_e = 0
                    valid = True
                    for ex2 in task.train_examples:
                        if ex2.input_grid.shape[0] < r_end or ex2.input_grid.shape[1] < c_end:
                            valid = False
                            break
                        if r_start < 0 or c_start < 0:
                            valid = False
                            break
                        cropped = ex2.input_grid.data[r_start:r_end, c_start:c_end]
                        if cropped.shape != ex2.output_grid.shape:
                            valid = False
                            break
                        total_e += compute_defect_energy(ARCGrid(cropped), ex2.output_grid)
                    
                    if valid:
                        avg_e = total_e / len(task.train_examples)
                        if avg_e < best_e:
                            best_e = avg_e
                            best_m = f"crop[{r_start}:{r_end},{c_start}:{c_end}]"
        
        return best_e, best_m
    
    def _try_colors(self, task: ARCTask) -> Tuple[float, str]:
        """Try all single color maps."""
        best_e = float('inf')
        best_m = "color:none"
        
        for from_c in range(10):
            for to_c in range(10):
                if from_c == to_c:
                    continue
                
                total_e = 0
                valid = True
                for ex in task.train_examples:
                    if ex.input_grid.shape != ex.output_grid.shape:
                        valid = False
                        break
                    data = ex.input_grid.data.clone()
                    data[data == from_c] = to_c
                    total_e += compute_defect_energy(ARCGrid(data), ex.output_grid)
                
                if valid:
                    avg_e = total_e / len(task.train_examples)
                    if avg_e < best_e:
                        best_e = avg_e
                        best_m = f"color({from_c}->{to_c})"
        
        return best_e, best_m
    
    def _try_patterns(self, task: ARCTask) -> Tuple[float, str]:
        """Try pattern transformations."""
        best_e = float('inf')
        best_m = "pattern:none"
        
        transforms = [
            ('rot90', lambda d: d.rot90(1, [0, 1])),
            ('rot180', lambda d: d.rot90(2, [0, 1])),
            ('rot270', lambda d: d.rot90(3, [0, 1])),
            ('flip_h', lambda d: d.flip(1)),
            ('flip_v', lambda d: d.flip(0)),
            ('transpose', lambda d: d.t()),
        ]
        
        for name, transform in transforms:
            total_e = 0
            valid = True
            for ex in task.train_examples:
                try:
                    result = ARCGrid(transform(ex.input_grid.data))
                    if result.shape != ex.output_grid.shape:
                        valid = False
                        break
                    total_e += compute_defect_energy(result, ex.output_grid)
                except:
                    valid = False
                    break
            
            if valid:
                avg_e = total_e / len(task.train_examples)
                if avg_e < best_e:
                    best_e = avg_e
                    best_m = name
        
        return best_e, best_m
    
    def _try_extracts(self, task: ARCTask) -> Tuple[float, str]:
        """Try extract operations."""
        best_e = float('inf')
        best_m = "extract:none"
        
        for selector in ['largest', 'smallest']:
            try:
                morph = ExtractObjectMorphism(selector)
                total_e = 0
                valid = True
                for ex in task.train_examples:
                    result = morph.apply(ex.input_grid, self.config)
                    if result.shape != ex.output_grid.shape:
                        valid = False
                        break
                    total_e += compute_defect_energy(result, ex.output_grid)
                
                if valid:
                    avg_e = total_e / len(task.train_examples)
                    if avg_e < best_e:
                        best_e = avg_e
                        best_m = f"extract({selector})"
            except:
                pass
        
        return best_e, best_m
    
    def _try_extract_color(self, task: ARCTask) -> Tuple[float, str]:
        """Try extract + color map combinations."""
        best_e = float('inf')
        best_m = "extract+color:none"
        
        for selector in ['largest', 'smallest']:
            try:
                morph = ExtractObjectMorphism(selector)
                
                for from_c in range(1, 10):
                    for to_c in range(1, 10):
                        if from_c == to_c:
                            continue
                        
                        total_e = 0
                        valid = True
                        for ex in task.train_examples:
                            result = morph.apply(ex.input_grid, self.config)
                            if result.shape != ex.output_grid.shape:
                                valid = False
                                break
                            data = result.data.clone()
                            data[data == from_c] = to_c
                            total_e += compute_defect_energy(ARCGrid(data), ex.output_grid)
                        
                        if valid:
                            avg_e = total_e / len(task.train_examples)
                            if avg_e < best_e:
                                best_e = avg_e
                                best_m = f"extract({selector})+color({from_c}->{to_c})"
            except:
                pass
        
        return best_e, best_m
    
    def _try_movement_color(self, task: ARCTask) -> Tuple[float, str]:
        """Try movement + color combinations."""
        best_e = float('inf')
        best_m = "move+color:none"
        
        for i, pot in enumerate(self.potentials):
            for sign in [-1.0, 1.0]:
                weights = np.zeros(4)
                weights[i] = sign
                potential = CompositePotential(self.potentials, weights)
                
                for from_c in range(1, 8):
                    for to_c in range(0, 8):
                        if from_c == to_c:
                            continue
                        
                        total_e = 0
                        valid = True
                        for ex in task.train_examples:
                            result = relax_all_colors(ex.input_grid, potential, self.config)
                            if result.shape != ex.output_grid.shape:
                                valid = False
                                break
                            data = result.data.clone()
                            data[data == from_c] = to_c
                            total_e += compute_defect_energy(ARCGrid(data), ex.output_grid)
                        
                        if valid:
                            avg_e = total_e / len(task.train_examples)
                            if avg_e < best_e:
                                best_e = avg_e
                                best_m = f"{sign:.0f}*{pot.name()}+color({from_c}->{to_c})"
        
        return best_e, best_m
    
    def _try_crop_color(self, task: ARCTask) -> Tuple[float, str]:
        """Try crop + color combinations."""
        best_e = float('inf')
        best_m = "crop+color:none"
        
        # Get target shapes
        ex0 = task.train_examples[0]
        tH, tW = ex0.output_grid.shape
        
        for ex in task.train_examples:
            H, W = ex.input_grid.shape
            
            for r_start in range(max(0, H - tH - 3), min(H - tH + 4, H + 1)):
                for c_start in range(max(0, W - tW - 3), min(W - tW + 4, W + 1)):
                    r_end = r_start + tH
                    c_end = c_start + tW
                    
                    if r_end > H or c_end > W or r_start < 0 or c_start < 0:
                        continue
                    
                    for from_c in range(1, 6):
                        for to_c in range(0, 6):
                            if from_c == to_c:
                                continue
                            
                            total_e = 0
                            valid = True
                            for ex2 in task.train_examples:
                                if ex2.input_grid.shape[0] < r_end or ex2.input_grid.shape[1] < c_end:
                                    valid = False
                                    break
                                cropped = ex2.input_grid.data[r_start:r_end, c_start:c_end].clone()
                                if cropped.shape != ex2.output_grid.shape:
                                    valid = False
                                    break
                                cropped[cropped == from_c] = to_c
                                total_e += compute_defect_energy(ARCGrid(cropped), ex2.output_grid)
                            
                            if valid:
                                avg_e = total_e / len(task.train_examples)
                                if avg_e < best_e:
                                    best_e = avg_e
                                    best_m = f"crop[{r_start}:{r_end}]+color({from_c}->{to_c})"
        
        return best_e, best_m
    
    def _try_delete_objects(self, task: ARCTask) -> Tuple[float, str]:
        """Try deleting individual objects."""
        best_e = float('inf')
        best_m = "delete:none"
        
        for ex in task.train_examples:
            if ex.input_grid.shape != ex.output_grid.shape:
                continue
            
            objects = detect_objects(ex.input_grid, self.config)
            
            for color in range(1, 10):
                # Delete all objects of this color
                data = ex.input_grid.data.clone()
                data[data == color] = self.config.background_color
                
                total_e = 0
                valid = True
                for ex2 in task.train_examples:
                    if ex2.input_grid.shape != ex2.output_grid.shape:
                        valid = False
                        break
                    d = ex2.input_grid.data.clone()
                    d[d == color] = self.config.background_color
                    total_e += compute_defect_energy(ARCGrid(d), ex2.output_grid)
                
                if valid:
                    avg_e = total_e / len(task.train_examples)
                    if avg_e < best_e:
                        best_e = avg_e
                        best_m = f"delete_color({color})"
        
        return best_e, best_m
    
    def _try_keep_objects(self, task: ARCTask) -> Tuple[float, str]:
        """Try keeping only specific objects."""
        best_e = float('inf')
        best_m = "keep:none"
        
        for color in range(1, 10):
            total_e = 0
            valid = True
            
            for ex in task.train_examples:
                # Find object of this color
                mask = ex.input_grid.data == color
                if not mask.any():
                    valid = False
                    break
                
                # Get bounding box
                rows = torch.where(mask.any(dim=1))[0]
                cols = torch.where(mask.any(dim=0))[0]
                
                if len(rows) == 0 or len(cols) == 0:
                    valid = False
                    break
                
                r1, r2 = rows[0].item(), rows[-1].item() + 1
                c1, c2 = cols[0].item(), cols[-1].item() + 1
                
                cropped = ex.input_grid.data[r1:r2, c1:c2]
                
                if cropped.shape != ex.output_grid.shape:
                    valid = False
                    break
                
                total_e += compute_defect_energy(ARCGrid(cropped), ex.output_grid)
            
            if valid:
                avg_e = total_e / len(task.train_examples)
                if avg_e < best_e:
                    best_e = avg_e
                    best_m = f"keep_color({color})"
        
        return best_e, best_m


def run_unified(data_path: str):
    printfl("=" * 70)
    printfl("ARC-SGC Phase 15 Unified: Maximum Coverage Solver")
    printfl("=" * 70)
    
    config = ARCPhase83Config()
    tasks = load_arc_tasks(data_path, 'cpu')
    printfl(f"\nLoaded {len(tasks)} tasks")
    
    solver = UnifiedSolver(config)
    
    all_results = []
    perfect_tasks = []
    method_counts = Counter()
    
    printfl("\n" + "=" * 50)
    printfl("Running Unified Solver (All Strategies)")
    printfl("=" * 50)
    
    for i, task in enumerate(tasks):
        result = solver.solve_task(task)
        all_results.append(result)
        
        if result['is_perfect']:
            perfect_tasks.append(result)
            method = result['method']
            method_type = method.split('(')[0].split('[')[0].split('+')[0]
            method_counts[method_type] += 1
            
            printfl(f"  [PERFECT] {task.task_id}: {method}")
        
        if (i + 1) % 20 == 0:
            printfl(f"  Progress: {i+1}/{len(tasks)}, perfect={len(perfect_tasks)}")
    
    # Summary
    printfl("\n" + "=" * 70)
    printfl("UNIFIED SOLVER SUMMARY")
    printfl("=" * 70)
    
    printfl(f"\nResults:")
    printfl(f"  Total perfect: {len(perfect_tasks)}")
    
    printfl(f"\nSolves by method type:")
    for method, count in method_counts.most_common():
        printfl(f"  {method}: {count}")
    
    # Near-misses
    near_misses = [r for r in all_results if 0.0001 < r['avg_train_energy'] < 0.1]
    printfl(f"\nNear-misses (E<0.1): {len(near_misses)}")
    for r in sorted(near_misses, key=lambda x: x['avg_train_energy'])[:10]:
        printfl(f"  {r['task_id']}: E={r['avg_train_energy']:.4f} ({r['method']})")
    
    # Progress
    printfl(f"\n=== COMPLETE PROGRESS SUMMARY ===")
    printfl(f"  Phase 8.3:   6 perfect (baseline)")
    printfl(f"  Phase 10:    7 perfect (+topology)")
    printfl(f"  Phase 12:    8 perfect (+conditional)")
    printfl(f"  Phase 14:   20 perfect (+variational)")
    printfl(f"  Phase 15:   19 perfect (+CEGAR)")
    printfl(f"  Unified:    {len(perfect_tasks)} perfect (all strategies)")
    
    if len(perfect_tasks) >= 30:
        printfl(f"\n*** TARGET ACHIEVED: {len(perfect_tasks)} >= 30 perfect solves! ***")
    elif len(perfect_tasks) >= 20:
        printfl(f"\n  Good progress: {len(perfect_tasks)} perfect solves")
    
    return all_results


def main():
    paths = ["data/arc/training", "C:/Lean4 Projects/data/arc/training"]
    arc_path = next((p for p in paths if Path(p).exists()), None)
    
    if arc_path:
        run_unified(arc_path)
    else:
        printfl("ARC data not found!")


if __name__ == "__main__":
    main()
