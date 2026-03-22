"""
ARC-SGC Phase 17: Task-Level CEGAR with Symmetry Awareness

KEY FIX: CEGAR refines a SHARED HYPOTHESIS (program) across ALL examples,
not independent per-example grid edits.

The insight from the reviewer:
- A "task" is a logical universe - refinement must produce a single program
- Per-example averaging can "solve" with inconsistent fixes
- The critic should propose parameter updates aggregated across examples

Theoretical grounding:
- In SGC, coarse-graining changes the effective geometry (π → π̄)
- The "program" is the invariant; the "grid" is a representation
- CEGAR refines the abstraction, not the output
"""

import torch
from dataclasses import dataclass, field
from typing import List, Tuple, Dict, Optional, Callable
from collections import Counter
from enum import Enum
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


# =============================================================================
# HYPOTHESIS REPRESENTATION (The Program, not the Grid)
# =============================================================================

@dataclass
class Hypothesis:
    """
    A hypothesis is a PROGRAM that can be applied to any input.
    This is the unit of refinement, NOT the output grid.
    """
    operation: str  # e.g., "movement", "crop", "color", "extract", "composite"
    parameters: Dict  # e.g., {"potential_weights": [0,1,0,0], "color_map": {3: 0}}
    
    def describe(self) -> str:
        if self.operation == "identity":
            return "identity"
        elif self.operation == "movement":
            return f"movement:{self.parameters.get('strength', 1.0):.2f}*{self.parameters.get('potential', 'V')}"
        elif self.operation == "crop":
            return f"crop:{self.parameters.get('coords', 'content')}"
        elif self.operation == "color":
            return f"color:{self.parameters.get('mapping', {})}"
        elif self.operation == "extract":
            return f"extract:{self.parameters.get('selector', 'largest')}"
        elif self.operation == "composite":
            parts = []
            if 'movement' in self.parameters:
                parts.append(f"move({self.parameters['movement']})")
            if 'color' in self.parameters:
                parts.append(f"color({self.parameters['color']})")
            return "+".join(parts) if parts else "composite"
        elif self.operation == "shift":
            return f"shift:{self.parameters.get('offset', (0,0))}"
        elif self.operation == "pattern":
            return f"pattern:{self.parameters.get('transform', 'none')}"
        return f"{self.operation}:{self.parameters}"


# =============================================================================
# D4 SYMMETRY GROUP (Rotations + Reflections)
# =============================================================================

class D4Symmetry:
    """
    The dihedral group D4: 4 rotations × 2 reflections = 8 elements.
    Used to treat symmetry as a latent gauge variable.
    """
    
    @staticmethod
    def apply(grid: ARCGrid, element: int) -> ARCGrid:
        """Apply symmetry element to grid. element in [0,7]."""
        data = grid.data
        # Rotations: 0=identity, 1=90°, 2=180°, 3=270°
        # Reflections: 4=flip_h, 5=flip_v, 6=rot90+flip_h, 7=rot90+flip_v
        if element == 0:
            return grid
        elif element == 1:
            return ARCGrid(data.rot90(1, [0, 1]))
        elif element == 2:
            return ARCGrid(data.rot90(2, [0, 1]))
        elif element == 3:
            return ARCGrid(data.rot90(3, [0, 1]))
        elif element == 4:
            return ARCGrid(data.flip(1))  # horizontal flip
        elif element == 5:
            return ARCGrid(data.flip(0))  # vertical flip
        elif element == 6:
            return ARCGrid(data.rot90(1, [0, 1]).flip(1))
        elif element == 7:
            return ARCGrid(data.rot90(1, [0, 1]).flip(0))
        return grid
    
    @staticmethod
    def inverse(element: int) -> int:
        """Inverse of a D4 element."""
        # 0→0, 1→3, 2→2, 3→1, 4→4, 5→5, 6→6, 7→7
        inverses = [0, 3, 2, 1, 4, 5, 6, 7]
        return inverses[element]
    
    @staticmethod
    def all_elements() -> List[int]:
        return list(range(8))


# =============================================================================
# TASK-LEVEL CEGAR (The Core Fix)
# =============================================================================

class TaskLevelCEGAR:
    """
    CEGAR that refines a SHARED HYPOTHESIS across all training examples.
    
    The key insight: instead of refining grids per-example, we refine
    the PROGRAM that must work for ALL examples.
    
    Contract:
    1. Maintain candidate hypothesis H
    2. Score E(H) = sum_i defect(H(x_i), y_i) across ALL examples
    3. Pick worst counterexample i* = argmax_i defect(...)
    4. Refine H using info from that counterexample
    5. Only accept refinements that reduce GLOBAL energy
    """
    
    def __init__(self, config: ARCPhase83Config, max_iterations: int = 10):
        self.config = config
        self.max_iterations = max_iterations
        self.potentials = [V_ContactDist(), V_TopEdge(), V_BottomEdge(), V_BoundaryDist()]
    
    def apply_hypothesis(self, hypothesis: Hypothesis, grid: ARCGrid) -> ARCGrid:
        """Apply a hypothesis (program) to an input grid."""
        try:
            if hypothesis.operation == "identity":
                return grid
            
            elif hypothesis.operation == "movement":
                weights = hypothesis.parameters.get('weights', np.zeros(4))
                potential = CompositePotential(self.potentials, weights)
                return relax_all_colors(grid, potential, self.config)
            
            elif hypothesis.operation == "crop":
                coords = hypothesis.parameters.get('coords', None)
                if coords == 'content':
                    morph = CropToContentMorphism()
                    return morph.apply(grid, self.config)
                elif coords is not None:
                    r1, r2, c1, c2 = coords
                    return ARCGrid(grid.data[r1:r2, c1:c2])
                return grid
            
            elif hypothesis.operation == "color":
                mapping = hypothesis.parameters.get('mapping', {})
                data = grid.data.clone()
                for from_c, to_c in mapping.items():
                    data[data == from_c] = to_c
                return ARCGrid(data)
            
            elif hypothesis.operation == "extract":
                selector = hypothesis.parameters.get('selector', 'largest')
                morph = ExtractObjectMorphism(selector)
                return morph.apply(grid, self.config)
            
            elif hypothesis.operation == "shift":
                dr, dc = hypothesis.parameters.get('offset', (0, 0))
                H, W = grid.shape
                data = torch.full_like(grid.data, self.config.background_color)
                src_r1, src_r2 = max(0, -dr), min(H, H - dr)
                src_c1, src_c2 = max(0, -dc), min(W, W - dc)
                dst_r1, dst_r2 = max(0, dr), min(H, H + dr)
                dst_c1, dst_c2 = max(0, dc), min(W, W + dc)
                if dst_r2 > dst_r1 and dst_c2 > dst_c1:
                    data[dst_r1:dst_r2, dst_c1:dst_c2] = grid.data[src_r1:src_r2, src_c1:src_c2]
                return ARCGrid(data)
            
            elif hypothesis.operation == "pattern":
                transform = hypothesis.parameters.get('transform', 'identity')
                if transform == 'rot90':
                    return ARCGrid(grid.data.rot90(1, [0, 1]))
                elif transform == 'rot180':
                    return ARCGrid(grid.data.rot90(2, [0, 1]))
                elif transform == 'rot270':
                    return ARCGrid(grid.data.rot90(3, [0, 1]))
                elif transform == 'flip_h':
                    return ARCGrid(grid.data.flip(1))
                elif transform == 'flip_v':
                    return ARCGrid(grid.data.flip(0))
                return grid
            
            elif hypothesis.operation == "composite":
                result = grid
                # Apply movement first
                if 'movement_weights' in hypothesis.parameters:
                    weights = hypothesis.parameters['movement_weights']
                    potential = CompositePotential(self.potentials, weights)
                    result = relax_all_colors(result, potential, self.config)
                # Then color mapping
                if 'color_mapping' in hypothesis.parameters:
                    data = result.data.clone()
                    for from_c, to_c in hypothesis.parameters['color_mapping'].items():
                        data[data == from_c] = to_c
                    result = ARCGrid(data)
                return result
            
            return grid
        except:
            return grid
    
    def evaluate_hypothesis(self, hypothesis: Hypothesis, task: ARCTask) -> Tuple[float, int]:
        """
        Evaluate hypothesis on ALL training examples.
        Returns (total_energy, worst_example_idx).
        """
        total_energy = 0
        worst_energy = -1
        worst_idx = 0
        
        for i, ex in enumerate(task.train_examples):
            try:
                result = self.apply_hypothesis(hypothesis, ex.input_grid)
                if result.shape != ex.output_grid.shape:
                    return float('inf'), i
                energy = compute_defect_energy(result, ex.output_grid)
                total_energy += energy
                if energy > worst_energy:
                    worst_energy = energy
                    worst_idx = i
            except:
                return float('inf'), i
        
        return total_energy / len(task.train_examples), worst_idx
    
    def generate_candidate_hypotheses(self, task: ARCTask) -> List[Hypothesis]:
        """Generate candidate hypotheses to try."""
        candidates = []
        
        # Identity
        candidates.append(Hypothesis("identity", {}))
        
        # Movement potentials
        for i, pot in enumerate(self.potentials):
            for sign in [-1.0, 1.0]:
                for strength in [0.25, 0.5, 1.0, 1.5, 2.0]:
                    weights = np.zeros(4)
                    weights[i] = sign * strength
                    candidates.append(Hypothesis("movement", {
                        'weights': weights,
                        'strength': sign * strength,
                        'potential': pot.name()
                    }))
        
        # Crop operations
        candidates.append(Hypothesis("crop", {'coords': 'content'}))
        
        # Extract operations
        for selector in ['largest', 'smallest']:
            candidates.append(Hypothesis("extract", {'selector': selector}))
        
        # Pattern transforms
        for transform in ['rot90', 'rot180', 'rot270', 'flip_h', 'flip_v']:
            candidates.append(Hypothesis("pattern", {'transform': transform}))
        
        # Shift operations
        for dr in range(-2, 3):
            for dc in range(-2, 3):
                if dr != 0 or dc != 0:
                    candidates.append(Hypothesis("shift", {'offset': (dr, dc)}))
        
        # Color mappings (inferred from first example)
        ex0 = task.train_examples[0]
        in_colors = set(ex0.input_grid.data.unique().tolist())
        out_colors = set(ex0.output_grid.data.unique().tolist())
        for from_c in in_colors:
            for to_c in out_colors:
                if from_c != to_c and from_c != 0:
                    candidates.append(Hypothesis("color", {'mapping': {from_c: to_c}}))
        
        return candidates
    
    def generate_composite_hypotheses(self, base: Hypothesis, task: ARCTask) -> List[Hypothesis]:
        """Generate composite hypotheses by combining base with color mappings."""
        composites = []
        
        ex0 = task.train_examples[0]
        in_colors = set(ex0.input_grid.data.unique().tolist())
        out_colors = set(ex0.output_grid.data.unique().tolist())
        
        if base.operation == "movement":
            for from_c in in_colors:
                for to_c in out_colors:
                    if from_c != to_c and from_c != 0:
                        composites.append(Hypothesis("composite", {
                            'movement_weights': base.parameters.get('weights', np.zeros(4)),
                            'color_mapping': {from_c: to_c}
                        }))
        
        elif base.operation == "extract":
            for from_c in in_colors:
                for to_c in out_colors:
                    if from_c != to_c and from_c != 0:
                        composites.append(Hypothesis("composite", {
                            'extract_selector': base.parameters.get('selector', 'largest'),
                            'color_mapping': {from_c: to_c}
                        }))
        
        return composites
    
    def refine_task(self, task: ARCTask) -> Tuple[Hypothesis, float, str]:
        """
        Run task-level CEGAR.
        Returns (best_hypothesis, best_energy, description).
        """
        candidates = self.generate_candidate_hypotheses(task)
        
        best_hypothesis = Hypothesis("identity", {})
        best_energy = float('inf')
        
        # Phase 1: Evaluate all base hypotheses
        for h in candidates:
            energy, worst_idx = self.evaluate_hypothesis(h, task)
            if energy < best_energy:
                best_energy = energy
                best_hypothesis = h
        
        if best_energy < self.config.energy_threshold:
            return best_hypothesis, best_energy, best_hypothesis.describe()
        
        # Phase 2: Try composites based on best hypothesis
        composites = self.generate_composite_hypotheses(best_hypothesis, task)
        for h in composites:
            energy, worst_idx = self.evaluate_hypothesis(h, task)
            if energy < best_energy:
                best_energy = energy
                best_hypothesis = h
        
        if best_energy < self.config.energy_threshold:
            return best_hypothesis, best_energy, best_hypothesis.describe()
        
        # Phase 3: CEGAR refinement loop on best hypothesis
        for iteration in range(self.max_iterations):
            current_energy, worst_idx = self.evaluate_hypothesis(best_hypothesis, task)
            
            if current_energy < self.config.energy_threshold:
                break
            
            # Use worst example to guide refinement
            worst_ex = task.train_examples[worst_idx]
            
            # Try to find a better composite
            improved = False
            for h in self.generate_composite_hypotheses(best_hypothesis, task):
                energy, _ = self.evaluate_hypothesis(h, task)
                if energy < best_energy:
                    best_energy = energy
                    best_hypothesis = h
                    improved = True
                    break
            
            if not improved:
                break
        
        return best_hypothesis, best_energy, best_hypothesis.describe()


# =============================================================================
# SYMMETRY-AWARE SOLVER
# =============================================================================

class SymmetryAwareSolver:
    """
    Solver that treats D4 symmetry as a latent gauge variable.
    Instead of canonicalizing (which loses equivariant evidence),
    we try multiple frames and pick the one that minimizes energy.
    """
    
    def __init__(self, config: ARCPhase83Config):
        self.config = config
        self.cegar = TaskLevelCEGAR(config)
        self.fallback = GeometryFirstSolver(config)
    
    def solve_task(self, task: ARCTask, verbose: bool = False) -> Dict:
        """Solve with symmetry awareness."""
        start_time = time.time()
        
        best_energy = float('inf')
        best_method = "none"
        best_gauge = 0
        
        # Stage 1: Try fallback first (fast baseline)
        fallback_result = self.fallback.solve_task(task, verbose=False)
        if fallback_result['avg_train_energy'] < best_energy:
            best_energy = fallback_result['avg_train_energy']
            best_method = 'fallback:' + fallback_result.get('operation', 'unknown')
        
        if best_energy < self.config.energy_threshold:
            return self._make_result(task, best_energy, best_method, start_time)
        
        # Stage 2: Task-level CEGAR (the fixed approach)
        hypothesis, energy, desc = self.cegar.refine_task(task)
        if energy < best_energy:
            best_energy = energy
            best_method = f"cegar:{desc}"
        
        if best_energy < self.config.energy_threshold:
            return self._make_result(task, best_energy, best_method, start_time)
        
        # Stage 3: Try with D4 symmetry gauge choices
        # Only if we haven't solved yet and task is small enough
        if len(task.train_examples) <= 5:
            for gauge in D4Symmetry.all_elements()[1:]:  # Skip identity (already tried)
                # Create transformed task
                transformed_examples = []
                valid = True
                for ex in task.train_examples:
                    try:
                        t_input = D4Symmetry.apply(ex.input_grid, gauge)
                        t_output = D4Symmetry.apply(ex.output_grid, gauge)
                        transformed_examples.append(ARCExample(t_input, t_output))
                    except:
                        valid = False
                        break
                
                if not valid:
                    continue
                
                # Create temporary task with transformed examples
                temp_task = ARCTask(task.task_id + f"_g{gauge}", transformed_examples, [])
                
                # Try CEGAR on transformed task
                h, e, d = self.cegar.refine_task(temp_task)
                if e < best_energy:
                    best_energy = e
                    best_method = f"symmetry(g{gauge}):{d}"
                    best_gauge = gauge
                
                if best_energy < self.config.energy_threshold:
                    break
        
        return self._make_result(task, best_energy, best_method, start_time)
    
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

def run_phase17(data_path: str):
    printfl("=" * 70)
    printfl("ARC-SGC Phase 17: Task-Level CEGAR with Symmetry Awareness")
    printfl("=" * 70)
    printfl("\nKEY FIX: Refining SHARED HYPOTHESIS across all examples")
    printfl("(Not per-example grid editing)\n")
    
    config = ARCPhase83Config()
    tasks = load_arc_tasks(data_path, 'cpu')
    printfl(f"Loaded {len(tasks)} tasks")
    
    solver = SymmetryAwareSolver(config)
    
    all_results = []
    perfect_tasks = []
    method_counts = Counter()
    
    printfl("\n" + "=" * 50)
    printfl("Running Task-Level CEGAR Solver")
    printfl("=" * 50)
    
    for i, task in enumerate(tasks):
        result = solver.solve_task(task)
        all_results.append(result)
        
        if result['is_perfect']:
            perfect_tasks.append(result)
            method = result['method']
            method_type = method.split(':')[0] if ':' in method else method
            method_counts[method_type] += 1
            
            printfl(f"  [PERFECT] {task.task_id}: {method}")
        
        if (i + 1) % 20 == 0:
            printfl(f"  Progress: {i+1}/{len(tasks)}, perfect={len(perfect_tasks)}")
    
    # Summary
    printfl("\n" + "=" * 70)
    printfl("PHASE 17 SUMMARY")
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
    printfl(f"  Phase 14:   20 perfect (variational)")
    printfl(f"  Phase 15:   19 perfect (per-example CEGAR)")
    printfl(f"  Phase 17:   {len(perfect_tasks)} perfect (TASK-LEVEL CEGAR)")
    
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
        run_phase17(arc_path)
    else:
        printfl("ARC data not found!")


if __name__ == "__main__":
    main()
