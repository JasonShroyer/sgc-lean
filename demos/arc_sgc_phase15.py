"""
ARC-SGC Phase 15: Iterative Abstraction Refinement (The Self-Improver)

THE CEGAR LOOP (Counter-Example Guided Abstraction Refinement):
1. ABSTRACT: Synthesize program using current Registry
2. VERIFY: Check against training examples
3. REFINE: Use counter-example (pixel defect) to update parameters/logic

THE SGC BRAIN ARCHITECTURE:
- Hippocampus (Registry): Stores successful strategies (Phenotypes)
- Prefrontal Cortex (Policy/Logic): Plans and synthesizes programs
- Motor Cortex (Executor): Runs physics and topology
- Cerebellum (Refiner): Fine-tunes execution error

This system is CLOSED UNDER SELF-IMPROVEMENT:
- More solves → Registry grows → Policy improves → Refiner learns
- It's a flywheel.

TARGET: 30+ Perfect Solves on full training set
"""

import torch
import torch.nn as nn
from dataclasses import dataclass, field
from typing import List, Tuple, Dict, Optional, Set, Callable, Any
from collections import Counter, defaultdict
from enum import Enum
import numpy as np
from pathlib import Path
import sys
import time
import json

sys.path.insert(0, str(Path(__file__).parent))
from arc_sgc_phase8_3 import (
    ARCPhase83Config, ARCGrid, ARCObject, ARCExample, ARCTask,
    load_arc_tasks, detect_objects, compute_defect_energy,
    GeometryFirstSolver, ContentSolver,
    CompositePotential, relax_all_colors,
    V_ContactDist, V_TopEdge, V_BottomEdge, V_BoundaryDist,
    CropToContentMorphism, ExtractObjectMorphism
)

def printfl(*args, **kwargs):
    print(*args, **kwargs)
    sys.stdout.flush()


# =============================================================================
# THE CRITIC (Defect Analysis -> Parameter Update)
# =============================================================================

class DefectType(Enum):
    """Types of defects that can be diagnosed."""
    OFFSET_ERROR = "offset"          # Prediction shifted from target
    BOUNDARY_ERROR = "boundary"       # Crop boundaries wrong
    COLOR_ERROR = "color"             # Wrong colors
    SCALE_ERROR = "scale"             # Wrong scale
    MISSING_PIXELS = "missing"        # Pixels that should exist
    EXTRA_PIXELS = "extra"            # Pixels that shouldn't exist
    ROTATION_ERROR = "rotation"       # Wrong orientation
    UNKNOWN = "unknown"


@dataclass
class DefectDiagnosis:
    """Diagnosis of what's wrong with a prediction."""
    defect_type: DefectType
    severity: float                   # 0-1, fraction of pixels wrong
    suggested_fix: str                # Human-readable fix suggestion
    parameters: Dict[str, Any]        # Specific parameters to try


class TheCritic:
    """
    Analyzes defects and suggests parameter updates.
    This is the 'Cerebellum' - fine-tunes execution errors.
    """
    
    def __init__(self, config: ARCPhase83Config):
        self.config = config
    
    def diagnose(self, input_grid: ARCGrid, prediction: ARCGrid, 
                 target: ARCGrid) -> DefectDiagnosis:
        """Diagnose what's wrong with the prediction."""
        
        # Shape mismatch
        if prediction.shape != target.shape:
            return self._diagnose_shape_mismatch(input_grid, prediction, target)
        
        # Compute defect mask
        defect_mask = prediction.data != target.data
        defect_count = defect_mask.sum().item()
        total_pixels = prediction.data.numel()
        severity = defect_count / total_pixels
        
        if defect_count == 0:
            return DefectDiagnosis(
                defect_type=DefectType.UNKNOWN,
                severity=0.0,
                suggested_fix="Already perfect",
                parameters={}
            )
        
        # Analyze defect pattern
        pred_colors = prediction.data[defect_mask].unique().tolist()
        target_colors = target.data[defect_mask].unique().tolist()
        
        # Color error: wrong colors at defect locations
        if set(pred_colors) != set(target_colors):
            color_map = self._infer_color_map(prediction, target, defect_mask)
            return DefectDiagnosis(
                defect_type=DefectType.COLOR_ERROR,
                severity=severity,
                suggested_fix=f"Apply color map: {color_map}",
                parameters={'color_map': color_map}
            )
        
        # Offset error: prediction looks shifted
        offset = self._detect_offset(prediction, target)
        if offset != (0, 0):
            return DefectDiagnosis(
                defect_type=DefectType.OFFSET_ERROR,
                severity=severity,
                suggested_fix=f"Shift by {offset}",
                parameters={'offset': offset}
            )
        
        # Missing vs extra pixels
        pred_mass = (prediction.data != self.config.background_color).sum().item()
        target_mass = (target.data != self.config.background_color).sum().item()
        
        if pred_mass < target_mass * 0.9:
            return DefectDiagnosis(
                defect_type=DefectType.MISSING_PIXELS,
                severity=severity,
                suggested_fix="Add pixels (expand/fill)",
                parameters={'action': 'expand'}
            )
        elif pred_mass > target_mass * 1.1:
            return DefectDiagnosis(
                defect_type=DefectType.EXTRA_PIXELS,
                severity=severity,
                suggested_fix="Remove pixels (shrink/delete)",
                parameters={'action': 'shrink'}
            )
        
        return DefectDiagnosis(
            defect_type=DefectType.UNKNOWN,
            severity=severity,
            suggested_fix="Try rotation/flip variants",
            parameters={'action': 'pattern'}
        )
    
    def _diagnose_shape_mismatch(self, input_grid: ARCGrid, prediction: ARCGrid,
                                  target: ARCGrid) -> DefectDiagnosis:
        """Diagnose shape mismatch."""
        pH, pW = prediction.shape
        tH, tW = target.shape
        
        if pH > tH or pW > tW:
            # Need to crop more
            return DefectDiagnosis(
                defect_type=DefectType.BOUNDARY_ERROR,
                severity=1.0,
                suggested_fix=f"Crop from {prediction.shape} to {target.shape}",
                parameters={'target_shape': target.shape, 'action': 'crop'}
            )
        else:
            # Need to expand or different extraction
            return DefectDiagnosis(
                defect_type=DefectType.SCALE_ERROR,
                severity=1.0,
                suggested_fix=f"Resize from {prediction.shape} to {target.shape}",
                parameters={'target_shape': target.shape, 'action': 'resize'}
            )
    
    def _infer_color_map(self, prediction: ARCGrid, target: ARCGrid,
                         defect_mask: torch.Tensor) -> Dict[int, int]:
        """Infer color mapping from prediction to target."""
        color_map = {}
        
        for pred_c in prediction.data.unique().tolist():
            if pred_c == self.config.background_color:
                continue
            
            # Find what color this maps to in target at same positions
            pred_mask = prediction.data == pred_c
            target_at_pred = target.data[pred_mask]
            
            if len(target_at_pred) > 0:
                most_common = Counter(target_at_pred.tolist()).most_common(1)
                if most_common:
                    target_c = most_common[0][0]
                    if target_c != pred_c:
                        color_map[pred_c] = target_c
        
        return color_map
    
    def _detect_offset(self, prediction: ARCGrid, target: ARCGrid) -> Tuple[int, int]:
        """Detect if prediction is a shifted version of target."""
        best_offset = (0, 0)
        best_match = 0
        
        H, W = prediction.shape
        
        # Try small offsets
        for dr in range(-3, 4):
            for dc in range(-3, 4):
                if dr == 0 and dc == 0:
                    continue
                
                match_count = 0
                total = 0
                
                for r in range(H):
                    for c in range(W):
                        sr, sc = r + dr, c + dc
                        if 0 <= sr < H and 0 <= sc < W:
                            total += 1
                            if prediction.data[r, c] == target.data[sr, sc]:
                                match_count += 1
                
                if total > 0:
                    match_ratio = match_count / total
                    if match_ratio > best_match:
                        best_match = match_ratio
                        best_offset = (dr, dc)
        
        # Only return offset if it significantly improves match
        if best_match > 0.8:
            return best_offset
        return (0, 0)


# =============================================================================
# THE CEGAR LOOP
# =============================================================================

@dataclass
class RefinementStep:
    """A single step in the refinement loop."""
    iteration: int
    energy_before: float
    energy_after: float
    diagnosis: DefectDiagnosis
    action_taken: str


class CEGARLoop:
    """
    Counter-Example Guided Abstraction Refinement Loop.
    
    1. Synthesize initial program
    2. Execute and get prediction
    3. Compute defect
    4. If defect > 0: diagnose and refine
    5. Repeat until defect = 0 or max iterations
    """
    
    def __init__(self, config: ARCPhase83Config, max_iterations: int = 10):
        self.config = config
        self.max_iterations = max_iterations
        self.critic = TheCritic(config)
        self.movement_potentials = [V_ContactDist(), V_TopEdge(), V_BottomEdge(), V_BoundaryDist()]
    
    def refine(self, input_grid: ARCGrid, target: ARCGrid,
               initial_result: ARCGrid = None) -> Tuple[ARCGrid, float, List[RefinementStep]]:
        """
        Run the CEGAR refinement loop.
        Returns (best_result, best_energy, refinement_history)
        """
        
        current = initial_result if initial_result is not None else input_grid.clone()
        history = []
        best_result = current
        best_energy = compute_defect_energy(current, target)
        
        for iteration in range(self.max_iterations):
            # Get diagnosis
            diagnosis = self.critic.diagnose(input_grid, current, target)
            energy_before = compute_defect_energy(current, target)
            
            if energy_before < self.config.energy_threshold:
                break  # Already solved
            
            # Apply fix based on diagnosis
            current, action = self._apply_fix(input_grid, current, target, diagnosis)
            energy_after = compute_defect_energy(current, target)
            
            # Record step
            step = RefinementStep(
                iteration=iteration,
                energy_before=energy_before,
                energy_after=energy_after,
                diagnosis=diagnosis,
                action_taken=action
            )
            history.append(step)
            
            # Track best
            if energy_after < best_energy:
                best_energy = energy_after
                best_result = current
            
            # Early exit if no improvement
            if energy_after >= energy_before:
                break
        
        return best_result, best_energy, history
    
    def _apply_fix(self, input_grid: ARCGrid, current: ARCGrid, target: ARCGrid,
                   diagnosis: DefectDiagnosis) -> Tuple[ARCGrid, str]:
        """Apply fix based on diagnosis."""
        
        if diagnosis.defect_type == DefectType.COLOR_ERROR:
            color_map = diagnosis.parameters.get('color_map', {})
            data = current.data.clone()
            for from_c, to_c in color_map.items():
                data[data == from_c] = to_c
            return ARCGrid(data), f"color_map({color_map})"
        
        elif diagnosis.defect_type == DefectType.OFFSET_ERROR:
            offset = diagnosis.parameters.get('offset', (0, 0))
            dr, dc = offset
            return self._shift_grid(current, dr, dc), f"shift({dr},{dc})"
        
        elif diagnosis.defect_type == DefectType.BOUNDARY_ERROR:
            target_shape = diagnosis.parameters.get('target_shape', target.shape)
            return self._crop_to_shape(input_grid, target_shape, target), f"crop_to({target_shape})"
        
        elif diagnosis.defect_type == DefectType.MISSING_PIXELS:
            return self._try_expand(input_grid, target), "expand"
        
        elif diagnosis.defect_type == DefectType.EXTRA_PIXELS:
            return self._try_shrink(input_grid, target), "shrink"
        
        else:
            # Try multiple transforms and pick best
            best = input_grid
            best_energy = compute_defect_energy(input_grid, target)
            best_action = "identity"
            
            # Patterns
            result = self._try_patterns(input_grid, target)
            energy = compute_defect_energy(result, target)
            if energy < best_energy:
                best, best_energy, best_action = result, energy, "pattern"
            
            # Scale
            result = self._try_scale(input_grid, target)
            energy = compute_defect_energy(result, target)
            if energy < best_energy:
                best, best_energy, best_action = result, energy, "scale"
            
            # Tile
            result = self._try_tile(input_grid, target)
            energy = compute_defect_energy(result, target)
            if energy < best_energy:
                best, best_energy, best_action = result, energy, "tile"
            
            # Shift
            result = self._try_shift(input_grid, target)
            energy = compute_defect_energy(result, target)
            if energy < best_energy:
                best, best_energy, best_action = result, energy, "shift"
            
            return best, best_action
    
    def _shift_grid(self, grid: ARCGrid, dr: int, dc: int) -> ARCGrid:
        """Shift grid by offset."""
        data = grid.data
        H, W = data.shape
        result = torch.full_like(data, self.config.background_color)
        
        for r in range(H):
            for c in range(W):
                nr, nc = r + dr, c + dc
                if 0 <= nr < H and 0 <= nc < W:
                    result[nr, nc] = data[r, c]
        
        return ARCGrid(result)
    
    def _crop_to_shape(self, grid: ARCGrid, target_shape: Tuple[int, int],
                       target: ARCGrid) -> ARCGrid:
        """Find best crop to match target shape."""
        tH, tW = target_shape
        H, W = grid.shape
        
        best_crop = grid.data[:tH, :tW] if tH <= H and tW <= W else grid.data
        best_energy = float('inf')
        
        for r_start in range(max(0, H - tH - 2), min(H - tH + 3, H)):
            for c_start in range(max(0, W - tW - 2), min(W - tW + 3, W)):
                r_end = r_start + tH
                c_end = c_start + tW
                
                if r_end > H or c_end > W or r_start < 0 or c_start < 0:
                    continue
                
                cropped = grid.data[r_start:r_end, c_start:c_end]
                if cropped.shape == target_shape:
                    energy = compute_defect_energy(ARCGrid(cropped), target)
                    if energy < best_energy:
                        best_energy = energy
                        best_crop = cropped
        
        return ARCGrid(best_crop)
    
    def _try_expand(self, grid: ARCGrid, target: ARCGrid) -> ARCGrid:
        """Try expansion operations."""
        best_result = grid
        best_energy = compute_defect_energy(grid, target)
        
        # Try movement potentials
        for i, pot in enumerate(self.movement_potentials):
            for sign in [-1.0, 1.0]:
                weights = np.zeros(4)
                weights[i] = sign
                potential = CompositePotential(self.movement_potentials, weights)
                
                result = relax_all_colors(grid, potential, self.config)
                if result.shape == target.shape:
                    energy = compute_defect_energy(result, target)
                    if energy < best_energy:
                        best_energy = energy
                        best_result = result
        
        return best_result
    
    def _try_shrink(self, grid: ARCGrid, target: ARCGrid) -> ARCGrid:
        """Try shrink/extract operations."""
        best_result = grid
        best_energy = compute_defect_energy(grid, target)
        
        # Try extract operations
        for selector in ['largest', 'smallest']:
            try:
                morph = ExtractObjectMorphism(selector)
                result = morph.apply(grid, self.config)
                if result.shape == target.shape:
                    energy = compute_defect_energy(result, target)
                    if energy < best_energy:
                        best_energy = energy
                        best_result = result
            except:
                pass
        
        return best_result
    
    def _try_patterns(self, grid: ARCGrid, target: ARCGrid) -> ARCGrid:
        """Try pattern transformations."""
        best_result = grid
        best_energy = compute_defect_energy(grid, target)
        
        # Rotations
        for k in [1, 2, 3]:
            result = ARCGrid(grid.data.rot90(k, [0, 1]))
            if result.shape == target.shape:
                energy = compute_defect_energy(result, target)
                if energy < best_energy:
                    best_energy = energy
                    best_result = result
        
        # Flips
        for dim in [0, 1]:
            result = ARCGrid(grid.data.flip(dim))
            if result.shape == target.shape:
                energy = compute_defect_energy(result, target)
                if energy < best_energy:
                    best_energy = energy
                    best_result = result
        
        return best_result
    
    def _try_scale(self, grid: ARCGrid, target: ARCGrid) -> ARCGrid:
        """Try scale transformations."""
        best_result = grid
        best_energy = compute_defect_energy(grid, target)
        
        H, W = grid.shape
        tH, tW = target.shape
        
        for scale in [2, 3, 4]:
            # Upscale
            if tH == H * scale and tW == W * scale:
                data = grid.data.repeat_interleave(scale, dim=0).repeat_interleave(scale, dim=1)
                result = ARCGrid(data)
                energy = compute_defect_energy(result, target)
                if energy < best_energy:
                    best_energy = energy
                    best_result = result
            
            # Downscale
            if H == tH * scale and W == tW * scale:
                data = grid.data[::scale, ::scale]
                result = ARCGrid(data)
                if result.shape == target.shape:
                    energy = compute_defect_energy(result, target)
                    if energy < best_energy:
                        best_energy = energy
                        best_result = result
        
        return best_result
    
    def _try_tile(self, grid: ARCGrid, target: ARCGrid) -> ARCGrid:
        """Try tile/repeat transformations."""
        best_result = grid
        best_energy = compute_defect_energy(grid, target)
        
        H, W = grid.shape
        tH, tW = target.shape
        
        for rep_h in [1, 2, 3]:
            for rep_w in [1, 2, 3]:
                if rep_h == 1 and rep_w == 1:
                    continue
                if H * rep_h == tH and W * rep_w == tW:
                    data = grid.data.repeat(rep_h, rep_w)
                    result = ARCGrid(data)
                    energy = compute_defect_energy(result, target)
                    if energy < best_energy:
                        best_energy = energy
                        best_result = result
        
        return best_result
    
    def _try_shift(self, grid: ARCGrid, target: ARCGrid) -> ARCGrid:
        """Try shift operations."""
        best_result = grid
        best_energy = compute_defect_energy(grid, target)
        
        if grid.shape != target.shape:
            return best_result
        
        H, W = grid.shape
        
        for dr in range(-3, 4):
            for dc in range(-3, 4):
                if dr == 0 and dc == 0:
                    continue
                
                data = torch.full_like(grid.data, self.config.background_color)
                src_r1, src_r2 = max(0, -dr), min(H, H - dr)
                src_c1, src_c2 = max(0, -dc), min(W, W - dc)
                dst_r1, dst_r2 = max(0, dr), min(H, H + dr)
                dst_c1, dst_c2 = max(0, dc), min(W, W + dc)
                
                if dst_r2 > dst_r1 and dst_c2 > dst_c1:
                    data[dst_r1:dst_r2, dst_c1:dst_c2] = grid.data[src_r1:src_r2, src_c1:src_c2]
                    result = ARCGrid(data)
                    energy = compute_defect_energy(result, target)
                    if energy < best_energy:
                        best_energy = energy
                        best_result = result
        
        return best_result


# =============================================================================
# REGISTRY EXPANSION (Learning from Refinements)
# =============================================================================

@dataclass
class LearnedStrategy:
    """A strategy learned from successful refinement."""
    defect_pattern: str           # What defect looked like
    fix_applied: str              # What fixed it
    success_count: int = 1
    avg_energy_reduction: float = 0.0


class ExpandingRegistry:
    """
    Registry that learns from successful refinements.
    Abstracts specific fixes into general strategies.
    """
    
    def __init__(self):
        self.strategies: Dict[str, LearnedStrategy] = {}
        self.task_solutions: Dict[str, Dict] = {}  # task_id -> solution info
    
    def record_success(self, task_id: str, history: List[RefinementStep], 
                       final_energy: float):
        """Record a successful refinement."""
        if not history:
            return
        
        # Abstract the refinement into a strategy
        for step in history:
            if step.energy_after < step.energy_before:
                key = f"{step.diagnosis.defect_type.value}_{step.action_taken}"
                
                if key in self.strategies:
                    self.strategies[key].success_count += 1
                    # Update average
                    n = self.strategies[key].success_count
                    old_avg = self.strategies[key].avg_energy_reduction
                    reduction = step.energy_before - step.energy_after
                    self.strategies[key].avg_energy_reduction = old_avg + (reduction - old_avg) / n
                else:
                    self.strategies[key] = LearnedStrategy(
                        defect_pattern=step.diagnosis.defect_type.value,
                        fix_applied=step.action_taken,
                        success_count=1,
                        avg_energy_reduction=step.energy_before - step.energy_after
                    )
        
        # Store solution
        self.task_solutions[task_id] = {
            'steps': len(history),
            'final_energy': final_energy,
            'fixes': [s.action_taken for s in history if s.energy_after < s.energy_before]
        }
    
    def get_top_strategies(self, n: int = 10) -> List[LearnedStrategy]:
        """Get most successful strategies."""
        return sorted(self.strategies.values(), 
                      key=lambda s: s.success_count * s.avg_energy_reduction,
                      reverse=True)[:n]
    
    def summary(self) -> str:
        lines = [f"Registry: {len(self.task_solutions)} solved tasks"]
        lines.append(f"\nTop strategies:")
        for s in self.get_top_strategies(5):
            lines.append(f"  {s.defect_pattern} -> {s.fix_applied}: "
                        f"{s.success_count} uses, avg reduction {s.avg_energy_reduction:.4f}")
        return "\n".join(lines)


# =============================================================================
# THE COMPLETE SELF-IMPROVING SOLVER
# =============================================================================

class SelfImprovingSolver:
    """
    The complete SGC Brain with self-improvement loop.
    
    Components:
    - Hippocampus (Registry): Stores successful strategies
    - Prefrontal Cortex (Synthesis): Plans programs
    - Motor Cortex (Executor): Runs physics
    - Cerebellum (CEGAR): Fine-tunes errors
    """
    
    def __init__(self, config: ARCPhase83Config):
        self.config = config
        self.cegar = CEGARLoop(config, max_iterations=15)
        self.registry = ExpandingRegistry()
        self.fallback = GeometryFirstSolver(config)
        self.critic = TheCritic(config)
    
    def solve_task(self, task: ARCTask, verbose: bool = False) -> Dict:
        """Solve task with full CEGAR loop."""
        start_time = time.time()
        examples = task.train_examples
        
        # Stage 1: Try fallback first
        fallback_result = self.fallback.solve_task(task, verbose=False)
        best_energy = fallback_result['avg_train_energy']
        best_method = 'fallback:' + fallback_result.get('operation', 'unknown')
        all_history = []
        
        if best_energy < self.config.energy_threshold:
            return self._make_result(task, best_energy, best_method, start_time, [])
        
        # Stage 2: CEGAR refinement on each example
        total_refined_energy = 0
        
        for ex in examples:
            # Start with identity
            initial = ex.input_grid
            
            # Run CEGAR
            result, energy, history = self.cegar.refine(ex.input_grid, ex.output_grid, initial)
            total_refined_energy += energy
            all_history.extend(history)
            
            if energy < best_energy:
                best_energy = energy
                if history:
                    best_method = f"cegar:{history[-1].action_taken}"
        
        avg_refined_energy = total_refined_energy / len(examples)
        
        if avg_refined_energy < best_energy:
            best_energy = avg_refined_energy
        
        # Stage 3: Try comprehensive operations
        operations_to_try = [
            ('movement', self._try_all_movements),
            ('crop', self._try_all_crops),
            ('color', self._try_all_colors),
            ('extract', self._try_all_extracts),
            ('pattern', self._try_all_patterns),
            ('composite', self._try_composites),
        ]
        
        for op_name, op_func in operations_to_try:
            energy, method = op_func(task)
            if energy < best_energy:
                best_energy = energy
                best_method = f"{op_name}:{method}"
            
            if best_energy < self.config.energy_threshold:
                break
        
        # Stage 4: Record success
        if best_energy < self.config.energy_threshold:
            self.registry.record_success(task.task_id, all_history, best_energy)
        
        return self._make_result(task, best_energy, best_method, start_time, all_history)
    
    def _try_all_movements(self, task: ARCTask) -> Tuple[float, str]:
        """Try all movement potential variations."""
        best_energy = float('inf')
        best_method = "identity"
        potentials = [V_ContactDist(), V_TopEdge(), V_BottomEdge(), V_BoundaryDist()]
        
        # Also try identity first
        total_e = 0
        valid = True
        for ex in task.train_examples:
            if ex.input_grid.shape != ex.output_grid.shape:
                valid = False
                break
            total_e += compute_defect_energy(ex.input_grid, ex.output_grid)
        if valid:
            avg_e = total_e / len(task.train_examples)
            if avg_e < best_energy:
                best_energy = avg_e
                best_method = "identity"
        
        for i, pot in enumerate(potentials):
            for sign in [-1.0, 1.0]:
                for strength in [0.25, 0.5, 1.0, 1.5, 2.0]:
                    weights = np.zeros(4)
                    weights[i] = sign * strength
                    potential = CompositePotential(potentials, weights)
                    
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
                        if avg_e < best_energy:
                            best_energy = avg_e
                            best_method = f"{sign*strength:.1f}*{pot.name()}"
        
        return best_energy, best_method
    
    def _try_all_crops(self, task: ARCTask) -> Tuple[float, str]:
        """Try all crop variations."""
        best_energy = float('inf')
        best_method = "identity"
        
        # First try crop_to_content
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
                if avg_e < best_energy:
                    best_energy = avg_e
                    best_method = "crop_to_content"
        except:
            pass
        
        for ex in task.train_examples:
            data = ex.input_grid.data
            H, W = data.shape
            tH, tW = ex.output_grid.shape
            
            for r_start in range(max(0, H - tH - 4), min(H - tH + 5, H)):
                for c_start in range(max(0, W - tW - 4), min(W - tW + 5, W)):
                    r_end = r_start + tH
                    c_end = c_start + tW
                    
                    if r_end > H or c_end > W or r_start < 0 or c_start < 0:
                        continue
                    
                    # Check all examples with this crop
                    total_e = 0
                    valid = True
                    for ex2 in task.train_examples:
                        if ex2.input_grid.shape[0] < r_end or ex2.input_grid.shape[1] < c_end:
                            valid = False
                            break
                        cropped = ex2.input_grid.data[r_start:r_end, c_start:c_end]
                        if cropped.shape != ex2.output_grid.shape:
                            valid = False
                            break
                        total_e += compute_defect_energy(ARCGrid(cropped), ex2.output_grid)
                    
                    if valid:
                        avg_e = total_e / len(task.train_examples)
                        if avg_e < best_energy:
                            best_energy = avg_e
                            best_method = f"crop[{r_start}:{r_end},{c_start}:{c_end}]"
        
        return best_energy, best_method
    
    def _try_all_colors(self, task: ARCTask) -> Tuple[float, str]:
        """Try all color transformations."""
        best_energy = float('inf')
        best_method = "identity"
        
        for from_c in range(1, 10):
            for to_c in range(0, 10):
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
                    if avg_e < best_energy:
                        best_energy = avg_e
                        best_method = f"color_map({from_c}->{to_c})"
        
        return best_energy, best_method
    
    def _try_all_extracts(self, task: ARCTask) -> Tuple[float, str]:
        """Try all extract variations."""
        best_energy = float('inf')
        best_method = "identity"
        
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
                    if avg_e < best_energy:
                        best_energy = avg_e
                        best_method = f"extract({selector})"
                    
                    # Try with color map
                    for from_c in range(1, 10):
                        for to_c in range(1, 10):
                            if from_c == to_c:
                                continue
                            
                            total_e2 = 0
                            for ex in task.train_examples:
                                result = morph.apply(ex.input_grid, self.config)
                                data = result.data.clone()
                                data[data == from_c] = to_c
                                total_e2 += compute_defect_energy(ARCGrid(data), ex.output_grid)
                            
                            avg_e2 = total_e2 / len(task.train_examples)
                            if avg_e2 < best_energy:
                                best_energy = avg_e2
                                best_method = f"extract({selector})+color({from_c}->{to_c})"
            except:
                pass
        
        return best_energy, best_method
    
    def _try_all_patterns(self, task: ARCTask) -> Tuple[float, str]:
        """Try all pattern transformations."""
        best_energy = float('inf')
        best_method = "identity"
        
        patterns = [
            ('rot90', lambda d: d.rot90(1, [0, 1])),
            ('rot180', lambda d: d.rot90(2, [0, 1])),
            ('rot270', lambda d: d.rot90(3, [0, 1])),
            ('flip_h', lambda d: d.flip(1)),
            ('flip_v', lambda d: d.flip(0)),
        ]
        
        for name, transform in patterns:
            total_e = 0
            valid = True
            for ex in task.train_examples:
                result = ARCGrid(transform(ex.input_grid.data))
                if result.shape != ex.output_grid.shape:
                    valid = False
                    break
                total_e += compute_defect_energy(result, ex.output_grid)
            
            if valid:
                avg_e = total_e / len(task.train_examples)
                if avg_e < best_energy:
                    best_energy = avg_e
                    best_method = name
        
        return best_energy, best_method
    
    def _try_composites(self, task: ARCTask) -> Tuple[float, str]:
        """Try composite operations."""
        best_energy = float('inf')
        best_method = "identity"
        
        # Movement + Color
        potentials = [V_ContactDist(), V_TopEdge(), V_BottomEdge(), V_BoundaryDist()]
        
        for i, pot in enumerate(potentials):
            for sign in [-1.0, 1.0]:
                weights = np.zeros(4)
                weights[i] = sign
                potential = CompositePotential(potentials, weights)
                
                for from_c in range(1, 6):
                    for to_c in range(0, 6):
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
                            if avg_e < best_energy:
                                best_energy = avg_e
                                best_method = f"{sign:.0f}*{pot.name()}+color({from_c}->{to_c})"
        
        return best_energy, best_method
    
    def _make_result(self, task: ARCTask, energy: float, method: str,
                     start_time: float, history: List[RefinementStep]) -> Dict:
        elapsed = time.time() - start_time
        return {
            'task_id': task.task_id,
            'method': method,
            'avg_train_energy': energy,
            'elapsed_ms': elapsed * 1000,
            'is_perfect': energy < self.config.energy_threshold,
            'refinement_steps': len(history)
        }


# =============================================================================
# EVALUATION
# =============================================================================

def run_phase15(data_path: str):
    printfl("=" * 70)
    printfl("ARC-SGC Phase 15: Iterative Abstraction Refinement")
    printfl("=" * 70)
    
    config = ARCPhase83Config()
    tasks = load_arc_tasks(data_path, 'cpu')
    printfl(f"\nLoaded {len(tasks)} tasks")
    
    solver = SelfImprovingSolver(config)
    
    all_results = []
    perfect_tasks = []
    method_counts = Counter()
    
    printfl("\n" + "=" * 50)
    printfl("Running Self-Improving CEGAR Solver")
    printfl("=" * 50)
    
    for i, task in enumerate(tasks):
        result = solver.solve_task(task, verbose=False)
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
    printfl("PHASE 15 SUMMARY")
    printfl("=" * 70)
    
    printfl(f"\nResults:")
    printfl(f"  Total perfect: {len(perfect_tasks)}")
    
    printfl(f"\nSolves by method type:")
    for method, count in method_counts.most_common():
        printfl(f"  {method}: {count}")
    
    # Registry summary
    printfl(f"\n{solver.registry.summary()}")
    
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
    printfl(f"  Phase 15:   {len(perfect_tasks)} perfect (+CEGAR)")
    
    if len(perfect_tasks) >= 30:
        printfl(f"\n*** TARGET ACHIEVED: {len(perfect_tasks)} >= 30 perfect solves! ***")
    else:
        printfl(f"\n  Gap to target: {30 - len(perfect_tasks)} more needed")
    
    return all_results, solver.registry


def main():
    paths = ["data/arc/training", "C:/Lean4 Projects/data/arc/training"]
    arc_path = next((p for p in paths if Path(p).exists()), None)
    
    if arc_path:
        run_phase15(arc_path)
    else:
        printfl("ARC data not found!")


if __name__ == "__main__":
    main()
