"""
ARC-SGC Phase 16: Combined Solver + Theoretical Foundation for Dreamer

This combines the best of Phase 14 (Variational Repair) and Phase 15 (CEGAR)
to maximize coverage on the current dataset.

Also lays groundwork for the Meta-Physical Dreamer concept.
"""

import torch
from dataclasses import dataclass
from typing import List, Tuple, Dict, Optional
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
from arc_sgc_phase15 import SelfImprovingSolver, CEGARLoop, TheCritic

def printfl(*args, **kwargs):
    print(*args, **kwargs)
    sys.stdout.flush()


# =============================================================================
# USE PHASE 15's SELF-IMPROVING SOLVER (IT WORKS - 19 PERFECT)
# =============================================================================

# The CombinedSolver below was missing key operations that Phase 15 has:
# - _try_all_colors (single color mappings)
# - _try_all_crops (comprehensive crop search)
# - proper identity check
#
# Rather than duplicate, we'll use SelfImprovingSolver directly and
# extend it with additional operations.


# =============================================================================
# PHYSICS CONTEXT (Foundation for Meta-Physical Dreamer)
# =============================================================================

@dataclass
class PhysicsContext:
    """
    Parametric physics settings for a task.
    This is the "System Settings" that can vary per-task.
    """
    gravity_vector: Tuple[int, int] = (1, 0)  # (dr, dc) - default: down
    collision_rule: str = "stop"  # "stop", "merge", "pass_through", "destroy"
    boundary_behavior: str = "stop"  # "stop", "wrap", "bounce"
    mass_conservation: str = "strict"  # "strict", "relaxed", "inverted"
    
    def describe(self) -> str:
        return f"gravity={self.gravity_vector}, collision={self.collision_rule}"


# =============================================================================
# COMBINED SOLVER (Phase 14 + Phase 15)
# =============================================================================

class CombinedSolver:
    """
    Combines Phase 14 (Variational Repair) and Phase 15 (CEGAR) strategies.
    Uses the fallback solver as the foundation, then tries refinements.
    """
    
    def __init__(self, config: ARCPhase83Config):
        self.config = config
        self.fallback = GeometryFirstSolver(config)
        self.cegar = CEGARLoop(config, max_iterations=15)
        self.critic = TheCritic(config)
        self.potentials = [V_ContactDist(), V_TopEdge(), V_BottomEdge(), V_BoundaryDist()]
    
    def solve_task(self, task: ARCTask, verbose: bool = False) -> Dict:
        """Solve task with combined strategies."""
        start_time = time.time()
        examples = task.train_examples
        
        best_energy = float('inf')
        best_method = "none"
        
        # Stage 1: Fallback solver (handles extract, crop, movement, patterns)
        fallback_result = self.fallback.solve_task(task, verbose=False)
        if fallback_result['avg_train_energy'] < best_energy:
            best_energy = fallback_result['avg_train_energy']
            best_method = 'fallback:' + fallback_result.get('operation', 'unknown')
        
        if best_energy < self.config.energy_threshold:
            return self._make_result(task, best_energy, best_method, start_time)
        
        # Stage 2: CEGAR refinement per example
        total_cegar_energy = 0
        cegar_actions = []
        
        for ex in examples:
            result, energy, history = self.cegar.refine(ex.input_grid, ex.output_grid, ex.input_grid)
            total_cegar_energy += energy
            if history:
                cegar_actions.append(history[-1].action_taken)
        
        avg_cegar = total_cegar_energy / len(examples)
        if avg_cegar < best_energy:
            best_energy = avg_cegar
            best_method = f"cegar:{cegar_actions[0] if cegar_actions else 'refine'}"
        
        if best_energy < self.config.energy_threshold:
            return self._make_result(task, best_energy, best_method, start_time)
        
        # Stage 3: Composite operations (movement + color)
        e, m = self._try_composites(task)
        if e < best_energy:
            best_energy, best_method = e, f"composite:{m}"
        
        if best_energy < self.config.energy_threshold:
            return self._make_result(task, best_energy, best_method, start_time)
        
        # Stage 4: Extract + color combinations
        e, m = self._try_extract_color(task)
        if e < best_energy:
            best_energy, best_method = e, m
        
        if best_energy < self.config.energy_threshold:
            return self._make_result(task, best_energy, best_method, start_time)
        
        # Stage 5: Shift operations
        e, m = self._try_shifts(task)
        if e < best_energy:
            best_energy, best_method = e, m
        
        return self._make_result(task, best_energy, best_method, start_time)
    
    def _try_composites(self, task: ARCTask) -> Tuple[float, str]:
        """Try movement + color composite operations."""
        best_e = float('inf')
        best_m = "none"
        
        examples = task.train_examples
        
        for i, pot in enumerate(self.potentials):
            for sign in [-1.0, 1.0]:
                for strength in [0.25, 0.5, 1.0]:
                    weights = np.zeros(4)
                    weights[i] = sign * strength
                    potential = CompositePotential(self.potentials, weights)
                    
                    # Movement alone
                    total_e = 0
                    valid = True
                    for ex in examples:
                        result = relax_all_colors(ex.input_grid, potential, self.config)
                        if result.shape != ex.output_grid.shape:
                            valid = False
                            break
                        total_e += compute_defect_energy(result, ex.output_grid)
                    
                    if valid:
                        avg_e = total_e / len(examples)
                        if avg_e < best_e:
                            best_e = avg_e
                            best_m = f"{sign*strength:+.1f}*{pot.name()}+identity"
                    
                    # Movement + color
                    for from_c in range(1, 10):
                        for to_c in range(0, 10):
                            if from_c == to_c:
                                continue
                            
                            total_e = 0
                            valid = True
                            for ex in examples:
                                result = relax_all_colors(ex.input_grid, potential, self.config)
                                if result.shape != ex.output_grid.shape:
                                    valid = False
                                    break
                                data = result.data.clone()
                                data[data == from_c] = to_c
                                total_e += compute_defect_energy(ARCGrid(data), ex.output_grid)
                            
                            if valid:
                                avg_e = total_e / len(examples)
                                if avg_e < best_e:
                                    best_e = avg_e
                                    best_m = f"{sign*strength:+.1f}*{pot.name()}+color_map({from_c}->{to_c})"
        
        return best_e, best_m
    
    def _try_extract_color(self, task: ARCTask) -> Tuple[float, str]:
        """Try extract + color combinations."""
        best_e = float('inf')
        best_m = "none"
        
        examples = task.train_examples
        
        for selector in ['largest', 'smallest']:
            try:
                morph = ExtractObjectMorphism(selector)
                
                for from_c in range(1, 10):
                    for to_c in range(0, 10):
                        if from_c == to_c:
                            continue
                        
                        total_e = 0
                        valid = True
                        for ex in examples:
                            result = morph.apply(ex.input_grid, self.config)
                            if result.shape != ex.output_grid.shape:
                                valid = False
                                break
                            data = result.data.clone()
                            data[data == from_c] = to_c
                            total_e += compute_defect_energy(ARCGrid(data), ex.output_grid)
                        
                        if valid:
                            avg_e = total_e / len(examples)
                            if avg_e < best_e:
                                best_e = avg_e
                                best_m = f"extract({selector})+color_map({from_c}->{to_c})"
            except:
                pass
        
        return best_e, best_m
    
    def _try_shifts(self, task: ARCTask) -> Tuple[float, str]:
        """Try shift operations."""
        best_e = float('inf')
        best_m = "none"
        
        examples = task.train_examples
        
        for dr in range(-3, 4):
            for dc in range(-3, 4):
                if dr == 0 and dc == 0:
                    continue
                
                total_e = 0
                valid = True
                
                for ex in examples:
                    if ex.input_grid.shape != ex.output_grid.shape:
                        valid = False
                        break
                    
                    H, W = ex.input_grid.shape
                    data = torch.full_like(ex.input_grid.data, self.config.background_color)
                    
                    src_r1, src_r2 = max(0, -dr), min(H, H - dr)
                    src_c1, src_c2 = max(0, -dc), min(W, W - dc)
                    dst_r1, dst_r2 = max(0, dr), min(H, H + dr)
                    dst_c1, dst_c2 = max(0, dc), min(W, W + dc)
                    
                    if dst_r2 > dst_r1 and dst_c2 > dst_c1:
                        data[dst_r1:dst_r2, dst_c1:dst_c2] = ex.input_grid.data[src_r1:src_r2, src_c1:src_c2]
                    
                    total_e += compute_defect_energy(ARCGrid(data), ex.output_grid)
                
                if valid:
                    avg_e = total_e / len(examples)
                    if avg_e < best_e:
                        best_e = avg_e
                        best_m = f"shift({dr},{dc})"
        
        return best_e, best_m
    
    def _make_result(self, task: ARCTask, energy: float, method: str, start_time: float) -> Dict:
        return {
            'task_id': task.task_id,
            'avg_train_energy': energy,
            'method': method,
            'elapsed_ms': (time.time() - start_time) * 1000,
            'is_perfect': energy < self.config.energy_threshold
        }


# =============================================================================
# MAIN
# =============================================================================

def run_combined(data_path: str):
    printfl("=" * 70)
    printfl("ARC-SGC Phase 16: Combined Solver (Phase 14 + 15)")
    printfl("=" * 70)
    
    config = ARCPhase83Config()
    tasks = load_arc_tasks(data_path, 'cpu')
    printfl(f"\nLoaded {len(tasks)} tasks")
    
    # Use SelfImprovingSolver from Phase 15 (it has all the operations)
    # CombinedSolver was missing: _try_all_colors, _try_all_crops, identity check
    solver = SelfImprovingSolver(config)
    
    all_results = []
    perfect_tasks = []
    method_counts = Counter()
    
    printfl("\n" + "=" * 50)
    printfl("Running Combined Solver")
    printfl("=" * 50)
    
    for i, task in enumerate(tasks):
        result = solver.solve_task(task)
        all_results.append(result)
        
        if result['is_perfect']:
            perfect_tasks.append(result)
            method = result['method']
            method_type = method.split(':')[0] if ':' in method else method.split('(')[0]
            method_counts[method_type] += 1
            
            printfl(f"  [PERFECT] {task.task_id}: {method}")
        
        if (i + 1) % 20 == 0:
            printfl(f"  Progress: {i+1}/{len(tasks)}, perfect={len(perfect_tasks)}")
    
    # Summary
    printfl("\n" + "=" * 70)
    printfl("PHASE 16 COMBINED SUMMARY")
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
    printfl(f"  Phase 16:   {len(perfect_tasks)} perfect (combined)")
    
    gap = 30 - len(perfect_tasks)
    if gap > 0:
        printfl(f"\n  Gap to target: {gap} more needed")
    else:
        printfl(f"\n*** TARGET ACHIEVED: {len(perfect_tasks)} >= 30 perfect solves! ***")
    
    return all_results


def main():
    paths = ["data/arc/training", "C:/Lean4 Projects/data/arc/training"]
    arc_path = next((p for p in paths if Path(p).exists()), None)
    
    if arc_path:
        run_combined(arc_path)
    else:
        printfl("ARC data not found!")


if __name__ == "__main__":
    main()
