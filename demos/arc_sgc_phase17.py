"""
ARC-SGC Phase 17: The Invariant Physics Engine

THEORETICAL FOUNDATION:
The ARC task lives in a Quotient Space G/S, where G is the grid and S is the 
symmetry group. By mapping input I → canonical form Ī and output O → Ō, the 
transformation T: Ī → Ō becomes simpler.

This aligns with SGC theory:
- Canonicalizer ≈ Wavelet Transform: Isolating signal (shape) from noise (position/orientation)
- Context Detector ≈ Sufficient Statistics: Minimal parameters describing the transformation
- Fisher-Rao metric provides the unique invariant manifold under sufficient statistics (Chentsov)

COMPONENTS:
1. CanonicalTransform - Maps grids to canonical form (COM centering, principal axis, color normalization)
2. PhysicsContext - Detects the "laws" of a task before solving
3. ContextGuidedCEGAR - Uses detected physics to guide refinement

TARGET: Solve tasks requiring abstract reasoning that Phase 15 failed at.
"""

import torch
import torch.nn.functional as F
from dataclasses import dataclass, field
from typing import List, Tuple, Dict, Optional, Set
from collections import Counter
from enum import Enum, auto
import numpy as np
from pathlib import Path
import sys
import time
import math

sys.path.insert(0, str(Path(__file__).parent))
from arc_sgc_phase8_3 import (
    ARCPhase83Config, ARCGrid, ARCObject, ARCExample, ARCTask,
    load_arc_tasks, detect_objects, compute_defect_energy,
    GeometryFirstSolver, CompositePotential, relax_all_colors,
    V_ContactDist, V_TopEdge, V_BottomEdge, V_BoundaryDist,
    CropToContentMorphism, ExtractObjectMorphism
)
from arc_sgc_phase15 import SelfImprovingSolver

def printfl(*args, **kwargs):
    print(*args, **kwargs)
    sys.stdout.flush()


# =============================================================================
# COMPONENT 1: THE CANONICALIZER (The "Wavelet" Transform)
# =============================================================================

@dataclass
class CanonicalForm:
    """
    Canonical representation of a grid, removing "nuisance variables":
    - Position (via COM centering)
    - Orientation (via principal axis alignment)
    - Color palette (via frequency-based normalization)
    """
    grid: ARCGrid
    # Transform parameters (for inversion)
    com_offset: Tuple[float, float]  # Original center of mass
    rotation_angle: float  # Angle applied (in 90° increments)
    color_map: Dict[int, int]  # Original color → canonical color
    inverse_color_map: Dict[int, int]  # Canonical → original
    original_shape: Tuple[int, int]
    

class CanonicalTransform:
    """
    Transforms grids to/from canonical form.
    
    The canonical form removes nuisance variables:
    1. Center of Mass → (H/2, W/2)
    2. Principal Axis → Vertical
    3. Color Palette → Frequency-ordered (most common = 0, second = 1, etc.)
    """
    
    def __init__(self, config: ARCPhase83Config):
        self.config = config
    
    def compute_center_of_mass(self, grid: ARCGrid) -> Tuple[float, float]:
        """Compute center of mass of non-background pixels."""
        data = grid.data
        mask = data != self.config.background_color
        
        if not mask.any():
            return grid.shape[0] / 2, grid.shape[1] / 2
        
        rows, cols = torch.where(mask)
        com_r = rows.float().mean().item()
        com_c = cols.float().mean().item()
        return com_r, com_c
    
    def compute_principal_axis(self, grid: ARCGrid) -> float:
        """
        Compute principal axis angle using second moment (inertia tensor).
        Returns angle in radians from vertical (0 = vertical, π/2 = horizontal).
        """
        data = grid.data
        mask = data != self.config.background_color
        
        if mask.sum() < 3:
            return 0.0
        
        rows, cols = torch.where(mask)
        rows = rows.float()
        cols = cols.float()
        
        # Center the coordinates
        r_c = rows.mean()
        c_c = cols.mean()
        r_centered = rows - r_c
        c_centered = cols - c_c
        
        # Compute second moments (inertia tensor components)
        I_rr = (r_centered ** 2).sum().item()
        I_cc = (c_centered ** 2).sum().item()
        I_rc = (r_centered * c_centered).sum().item()
        
        # Principal axis angle
        if abs(I_rr - I_cc) < 1e-10:
            return 0.0
        
        theta = 0.5 * math.atan2(2 * I_rc, I_cc - I_rr)
        return theta
    
    def compute_color_normalization(self, grid: ARCGrid) -> Tuple[Dict[int, int], Dict[int, int]]:
        """
        Compute color normalization map based on frequency.
        Most frequent non-background color → 1, second → 2, etc.
        Background (0) stays 0.
        """
        data = grid.data
        colors = data.flatten().tolist()
        
        # Count non-background colors
        color_counts = Counter(c for c in colors if c != self.config.background_color)
        
        if not color_counts:
            return {}, {}
        
        # Sort by frequency (descending), then by color value for stability
        sorted_colors = sorted(color_counts.keys(), key=lambda c: (-color_counts[c], c))
        
        # Map to canonical colors (1, 2, 3, ...)
        forward_map = {self.config.background_color: self.config.background_color}
        inverse_map = {self.config.background_color: self.config.background_color}
        
        for i, orig_color in enumerate(sorted_colors):
            canonical_color = i + 1
            forward_map[orig_color] = canonical_color
            inverse_map[canonical_color] = orig_color
        
        return forward_map, inverse_map
    
    def to_canonical(self, grid: ARCGrid) -> CanonicalForm:
        """Transform grid to canonical form."""
        H, W = grid.shape
        
        # Step 1: Compute center of mass
        com_r, com_c = self.compute_center_of_mass(grid)
        
        # Step 2: Center the grid (shift COM to center)
        target_r, target_c = H / 2, W / 2
        shift_r = int(round(target_r - com_r))
        shift_c = int(round(target_c - com_c))
        
        centered_data = torch.full_like(grid.data, self.config.background_color)
        for r in range(H):
            for c in range(W):
                new_r, new_c = r + shift_r, c + shift_c
                if 0 <= new_r < H and 0 <= new_c < W:
                    centered_data[new_r, new_c] = grid.data[r, c]
        
        # Step 3: Compute principal axis and rotate to vertical
        centered_grid = ARCGrid(centered_data)
        angle = self.compute_principal_axis(centered_grid)
        
        # Quantize to 90° rotations
        rot_90_count = int(round(angle / (math.pi / 2))) % 4
        
        if rot_90_count > 0:
            rotated_data = centered_data.rot90(rot_90_count, [0, 1])
        else:
            rotated_data = centered_data
        
        # Step 4: Color normalization
        rotated_grid = ARCGrid(rotated_data)
        color_map, inverse_color_map = self.compute_color_normalization(rotated_grid)
        
        # Apply color normalization
        normalized_data = rotated_data.clone()
        for orig, canonical in color_map.items():
            normalized_data[rotated_data == orig] = canonical
        
        return CanonicalForm(
            grid=ARCGrid(normalized_data),
            com_offset=(com_r, com_c),
            rotation_angle=rot_90_count * (math.pi / 2),
            color_map=color_map,
            inverse_color_map=inverse_color_map,
            original_shape=(H, W)
        )
    
    def from_canonical(self, canonical: CanonicalForm, target_shape: Tuple[int, int] = None) -> ARCGrid:
        """Transform from canonical form back to original space."""
        data = canonical.grid.data.clone()
        
        # Step 1: Inverse color normalization
        denormalized_data = data.clone()
        for canonical_c, orig_c in canonical.inverse_color_map.items():
            denormalized_data[data == canonical_c] = orig_c
        
        # Step 2: Inverse rotation
        rot_count = int(round(canonical.rotation_angle / (math.pi / 2)))
        if rot_count > 0:
            # Inverse rotation
            inverse_rot = (4 - rot_count) % 4
            if inverse_rot > 0:
                denormalized_data = denormalized_data.rot90(inverse_rot, [0, 1])
        
        # Step 3: Inverse centering (shift back)
        H, W = canonical.original_shape if target_shape is None else target_shape
        target_r, target_c = H / 2, W / 2
        com_r, com_c = canonical.com_offset
        shift_r = int(round(com_r - target_r))
        shift_c = int(round(com_c - target_c))
        
        result_data = torch.full((H, W), self.config.background_color, dtype=denormalized_data.dtype)
        src_H, src_W = denormalized_data.shape
        
        for r in range(src_H):
            for c in range(src_W):
                new_r, new_c = r + shift_r, c + shift_c
                if 0 <= new_r < H and 0 <= new_c < W:
                    result_data[new_r, new_c] = denormalized_data[r, c]
        
        return ARCGrid(result_data)


# =============================================================================
# COMPONENT 2: THE CONTEXT DETECTOR (The "Physics" Sensor)
# =============================================================================

class PhysicsType(Enum):
    """Types of physics detected in a task."""
    GLOBAL_MOTION = auto()      # All objects move by same vector
    GRAVITY = auto()            # Objects move toward a direction
    CONSERVATION_MASS = auto()  # Total non-background pixels preserved
    CONSERVATION_COLOR = auto() # Color histogram preserved
    CONSERVATION_TOPOLOGY = auto()  # Number of connected components preserved
    SCALE = auto()              # Grid is scaled
    CROP = auto()               # Grid is cropped
    COLOR_REMAP = auto()        # Colors are remapped
    IDENTITY = auto()           # Input equals output
    ROTATION = auto()           # Grid is rotated
    REFLECTION = auto()         # Grid is reflected


@dataclass
class PhysicsContext:
    """
    Detected physics laws for a task.
    This is the "sufficient statistics" that describe the transformation.
    """
    detected_physics: Set[PhysicsType] = field(default_factory=set)
    confidence: Dict[PhysicsType, float] = field(default_factory=dict)
    parameters: Dict[PhysicsType, Dict] = field(default_factory=dict)
    
    def has(self, physics_type: PhysicsType) -> bool:
        return physics_type in self.detected_physics
    
    def strongest(self) -> Optional[PhysicsType]:
        if not self.detected_physics:
            return None
        return max(self.detected_physics, key=lambda p: self.confidence.get(p, 0))


class PhysicsDetector:
    """
    Detects the "laws" of a task before attempting to solve it.
    Analyzes training pairs to infer conservation laws and transformation types.
    """
    
    def __init__(self, config: ARCPhase83Config):
        self.config = config
    
    def detect(self, task: ARCTask) -> PhysicsContext:
        """Detect physics from all training examples."""
        context = PhysicsContext()
        
        examples = task.train_examples
        
        # Run all detectors
        self._detect_identity(examples, context)
        self._detect_conservation_mass(examples, context)
        self._detect_conservation_color(examples, context)
        self._detect_conservation_topology(examples, context)
        self._detect_global_motion(examples, context)
        self._detect_scale(examples, context)
        self._detect_crop(examples, context)
        self._detect_color_remap(examples, context)
        self._detect_rotation(examples, context)
        self._detect_reflection(examples, context)
        
        return context
    
    def _detect_identity(self, examples: List[ARCExample], context: PhysicsContext):
        """Detect if input equals output."""
        all_identity = True
        for ex in examples:
            if ex.input_grid.shape != ex.output_grid.shape:
                all_identity = False
                break
            if not torch.equal(ex.input_grid.data, ex.output_grid.data):
                all_identity = False
                break
        
        if all_identity:
            context.detected_physics.add(PhysicsType.IDENTITY)
            context.confidence[PhysicsType.IDENTITY] = 1.0
    
    def _detect_conservation_mass(self, examples: List[ARCExample], context: PhysicsContext):
        """Detect if total non-background pixels are preserved."""
        conserved = True
        for ex in examples:
            in_mass = (ex.input_grid.data != self.config.background_color).sum().item()
            out_mass = (ex.output_grid.data != self.config.background_color).sum().item()
            if in_mass != out_mass:
                conserved = False
                break
        
        if conserved:
            context.detected_physics.add(PhysicsType.CONSERVATION_MASS)
            context.confidence[PhysicsType.CONSERVATION_MASS] = 1.0
    
    def _detect_conservation_color(self, examples: List[ARCExample], context: PhysicsContext):
        """Detect if color histogram is preserved."""
        conserved = True
        for ex in examples:
            in_colors = Counter(ex.input_grid.data.flatten().tolist())
            out_colors = Counter(ex.output_grid.data.flatten().tolist())
            # Ignore background
            del in_colors[self.config.background_color]
            if self.config.background_color in out_colors:
                del out_colors[self.config.background_color]
            
            if in_colors != out_colors:
                conserved = False
                break
        
        if conserved:
            context.detected_physics.add(PhysicsType.CONSERVATION_COLOR)
            context.confidence[PhysicsType.CONSERVATION_COLOR] = 1.0
    
    def _detect_conservation_topology(self, examples: List[ARCExample], context: PhysicsContext):
        """Detect if number of connected components is preserved."""
        conserved = True
        for ex in examples:
            in_objects = detect_objects(ex.input_grid, self.config)
            out_objects = detect_objects(ex.output_grid, self.config)
            if len(in_objects) != len(out_objects):
                conserved = False
                break
        
        if conserved:
            context.detected_physics.add(PhysicsType.CONSERVATION_TOPOLOGY)
            context.confidence[PhysicsType.CONSERVATION_TOPOLOGY] = 1.0
    
    def _detect_global_motion(self, examples: List[ARCExample], context: PhysicsContext):
        """Detect if all objects move by approximately the same vector."""
        if len(examples) < 1:
            return
        
        motion_vectors = []
        
        for ex in examples:
            if ex.input_grid.shape != ex.output_grid.shape:
                return  # Shape change, not pure motion
            
            in_com = self._compute_com(ex.input_grid)
            out_com = self._compute_com(ex.output_grid)
            
            if in_com is None or out_com is None:
                return
            
            dr = out_com[0] - in_com[0]
            dc = out_com[1] - in_com[1]
            motion_vectors.append((dr, dc))
        
        if not motion_vectors:
            return
        
        # Check if all vectors are approximately the same
        ref_dr, ref_dc = motion_vectors[0]
        consistent = all(
            abs(dr - ref_dr) < 1 and abs(dc - ref_dc) < 1
            for dr, dc in motion_vectors
        )
        
        if consistent and (abs(ref_dr) > 0.5 or abs(ref_dc) > 0.5):
            context.detected_physics.add(PhysicsType.GLOBAL_MOTION)
            context.confidence[PhysicsType.GLOBAL_MOTION] = 0.9
            context.parameters[PhysicsType.GLOBAL_MOTION] = {
                'vector': (int(round(ref_dr)), int(round(ref_dc)))
            }
    
    def _compute_com(self, grid: ARCGrid) -> Optional[Tuple[float, float]]:
        """Compute center of mass."""
        mask = grid.data != self.config.background_color
        if not mask.any():
            return None
        rows, cols = torch.where(mask)
        return rows.float().mean().item(), cols.float().mean().item()
    
    def _detect_scale(self, examples: List[ARCExample], context: PhysicsContext):
        """Detect if output is a scaled version of input."""
        scale_factors = []
        
        for ex in examples:
            in_h, in_w = ex.input_grid.shape
            out_h, out_w = ex.output_grid.shape
            
            if in_h == 0 or in_w == 0:
                return
            
            scale_r = out_h / in_h
            scale_c = out_w / in_w
            
            # Check if scales are integers
            if scale_r == scale_c and scale_r == int(scale_r) and scale_r > 1:
                scale_factors.append(int(scale_r))
        
        if len(scale_factors) == len(examples) and len(set(scale_factors)) == 1:
            context.detected_physics.add(PhysicsType.SCALE)
            context.confidence[PhysicsType.SCALE] = 1.0
            context.parameters[PhysicsType.SCALE] = {'factor': scale_factors[0]}
    
    def _detect_crop(self, examples: List[ARCExample], context: PhysicsContext):
        """Detect if output is a crop of input."""
        is_crop = True
        
        for ex in examples:
            out_h, out_w = ex.output_grid.shape
            in_h, in_w = ex.input_grid.shape
            
            if out_h > in_h or out_w > in_w:
                is_crop = False
                break
            
            # Check if output exists as a subgrid of input
            found = False
            for r in range(in_h - out_h + 1):
                for c in range(in_w - out_w + 1):
                    subgrid = ex.input_grid.data[r:r+out_h, c:c+out_w]
                    if torch.equal(subgrid, ex.output_grid.data):
                        found = True
                        break
                if found:
                    break
            
            if not found:
                is_crop = False
                break
        
        if is_crop:
            context.detected_physics.add(PhysicsType.CROP)
            context.confidence[PhysicsType.CROP] = 1.0
    
    def _detect_color_remap(self, examples: List[ARCExample], context: PhysicsContext):
        """Detect if colors are remapped."""
        if not examples:
            return
        
        # Try to infer a consistent color map from first example
        ex0 = examples[0]
        if ex0.input_grid.shape != ex0.output_grid.shape:
            return
        
        # Build candidate color map
        candidate_map = {}
        in_data = ex0.input_grid.data
        out_data = ex0.output_grid.data
        
        for r in range(in_data.shape[0]):
            for c in range(in_data.shape[1]):
                in_c = in_data[r, c].item()
                out_c = out_data[r, c].item()
                
                if in_c in candidate_map:
                    if candidate_map[in_c] != out_c:
                        return  # Inconsistent mapping
                else:
                    candidate_map[in_c] = out_c
        
        # Verify on all examples
        consistent = True
        for ex in examples[1:]:
            if ex.input_grid.shape != ex.output_grid.shape:
                consistent = False
                break
            
            in_data = ex.input_grid.data
            out_data = ex.output_grid.data
            
            for r in range(in_data.shape[0]):
                for c in range(in_data.shape[1]):
                    in_c = in_data[r, c].item()
                    out_c = out_data[r, c].item()
                    
                    expected = candidate_map.get(in_c, in_c)
                    if expected != out_c:
                        consistent = False
                        break
                if not consistent:
                    break
        
        if consistent and any(k != v for k, v in candidate_map.items()):
            context.detected_physics.add(PhysicsType.COLOR_REMAP)
            context.confidence[PhysicsType.COLOR_REMAP] = 1.0
            context.parameters[PhysicsType.COLOR_REMAP] = {'map': candidate_map}
    
    def _detect_rotation(self, examples: List[ARCExample], context: PhysicsContext):
        """Detect if output is a rotation of input."""
        for rot_count in [1, 2, 3]:  # 90°, 180°, 270°
            all_match = True
            for ex in examples:
                rotated = ex.input_grid.data.rot90(rot_count, [0, 1])
                if rotated.shape != ex.output_grid.shape:
                    all_match = False
                    break
                if not torch.equal(rotated, ex.output_grid.data):
                    all_match = False
                    break
            
            if all_match:
                context.detected_physics.add(PhysicsType.ROTATION)
                context.confidence[PhysicsType.ROTATION] = 1.0
                context.parameters[PhysicsType.ROTATION] = {'count': rot_count}
                return
    
    def _detect_reflection(self, examples: List[ARCExample], context: PhysicsContext):
        """Detect if output is a reflection of input."""
        for flip_axis, flip_name in [(0, 'vertical'), (1, 'horizontal')]:
            all_match = True
            for ex in examples:
                flipped = ex.input_grid.data.flip(flip_axis)
                if flipped.shape != ex.output_grid.shape:
                    all_match = False
                    break
                if not torch.equal(flipped, ex.output_grid.data):
                    all_match = False
                    break
            
            if all_match:
                context.detected_physics.add(PhysicsType.REFLECTION)
                context.confidence[PhysicsType.REFLECTION] = 1.0
                context.parameters[PhysicsType.REFLECTION] = {'axis': flip_name}
                return


# =============================================================================
# COMPONENT 3: CONTEXT-GUIDED CEGAR
# =============================================================================

class ContextGuidedSolver:
    """
    Solver that uses detected physics to guide refinement.
    
    Strategy:
    1. Detect physics context before solving
    2. If context is clear (high confidence), apply detected transform directly
    3. Otherwise, use context to prune search space
    4. Fall back to general solver if context-guided fails
    """
    
    def __init__(self, config: ARCPhase83Config):
        self.config = config
        self.detector = PhysicsDetector(config)
        self.canonicalizer = CanonicalTransform(config)
        # Use SelfImprovingSolver (has comprehensive color mapping, crops, patterns)
        # NOT GeometryFirstSolver (too weak - misses color discovery)
        self.fallback = SelfImprovingSolver(config)
        self.potentials = [V_ContactDist(), V_TopEdge(), V_BottomEdge(), V_BoundaryDist()]
    
    def solve_task(self, task: ARCTask, verbose: bool = False) -> Dict:
        """Solve task with context-guided approach."""
        start_time = time.time()
        
        # Step 1: Detect physics
        context = self.detector.detect(task)
        
        if verbose:
            printfl(f"  Detected physics: {[p.name for p in context.detected_physics]}")
        
        best_energy = float('inf')
        best_method = "none"
        
        # Step 2: Try context-guided solutions first
        if context.has(PhysicsType.IDENTITY):
            e, m = self._try_identity(task)
            if e < best_energy:
                best_energy, best_method = e, m
        
        if context.has(PhysicsType.ROTATION):
            e, m = self._try_rotation(task, context)
            if e < best_energy:
                best_energy, best_method = e, m
        
        if context.has(PhysicsType.REFLECTION):
            e, m = self._try_reflection(task, context)
            if e < best_energy:
                best_energy, best_method = e, m
        
        if context.has(PhysicsType.COLOR_REMAP):
            e, m = self._try_color_remap(task, context)
            if e < best_energy:
                best_energy, best_method = e, m
        
        if context.has(PhysicsType.CROP):
            e, m = self._try_crop(task)
            if e < best_energy:
                best_energy, best_method = e, m
        
        if context.has(PhysicsType.SCALE):
            e, m = self._try_scale(task, context)
            if e < best_energy:
                best_energy, best_method = e, m
        
        if context.has(PhysicsType.GLOBAL_MOTION):
            e, m = self._try_global_motion(task, context)
            if e < best_energy:
                best_energy, best_method = e, m
        
        # Step 3: If context-guided found a solution, return it
        if best_energy < self.config.energy_threshold:
            return self._make_result(task, best_energy, f"context:{best_method}", context, start_time)
        
        # Step 4: Try in canonical space
        e, m = self._try_canonical_space(task)
        if e < best_energy:
            best_energy, best_method = e, f"canonical:{m}"
        
        if best_energy < self.config.energy_threshold:
            return self._make_result(task, best_energy, best_method, context, start_time)
        
        # Step 5: Fall back to general solver
        fallback_result = self.fallback.solve_task(task, verbose=False)
        if fallback_result['avg_train_energy'] < best_energy:
            best_energy = fallback_result['avg_train_energy']
            best_method = f"fallback:{fallback_result.get('operation', 'unknown')}"
        
        return self._make_result(task, best_energy, best_method, context, start_time)
    
    def _try_identity(self, task: ARCTask) -> Tuple[float, str]:
        """Try identity transformation."""
        total_e = 0
        for ex in task.train_examples:
            if ex.input_grid.shape != ex.output_grid.shape:
                return float('inf'), "identity"
            total_e += compute_defect_energy(ex.input_grid, ex.output_grid)
        return total_e / len(task.train_examples), "identity"
    
    def _try_rotation(self, task: ARCTask, context: PhysicsContext) -> Tuple[float, str]:
        """Apply detected rotation."""
        rot_count = context.parameters.get(PhysicsType.ROTATION, {}).get('count', 1)
        
        total_e = 0
        for ex in task.train_examples:
            rotated = ARCGrid(ex.input_grid.data.rot90(rot_count, [0, 1]))
            if rotated.shape != ex.output_grid.shape:
                return float('inf'), f"rot{rot_count * 90}"
            total_e += compute_defect_energy(rotated, ex.output_grid)
        
        return total_e / len(task.train_examples), f"rot{rot_count * 90}"
    
    def _try_reflection(self, task: ARCTask, context: PhysicsContext) -> Tuple[float, str]:
        """Apply detected reflection."""
        axis = context.parameters.get(PhysicsType.REFLECTION, {}).get('axis', 'horizontal')
        flip_dim = 1 if axis == 'horizontal' else 0
        
        total_e = 0
        for ex in task.train_examples:
            flipped = ARCGrid(ex.input_grid.data.flip(flip_dim))
            if flipped.shape != ex.output_grid.shape:
                return float('inf'), f"flip_{axis}"
            total_e += compute_defect_energy(flipped, ex.output_grid)
        
        return total_e / len(task.train_examples), f"flip_{axis}"
    
    def _try_color_remap(self, task: ARCTask, context: PhysicsContext) -> Tuple[float, str]:
        """Apply detected color remapping."""
        color_map = context.parameters.get(PhysicsType.COLOR_REMAP, {}).get('map', {})
        
        total_e = 0
        for ex in task.train_examples:
            if ex.input_grid.shape != ex.output_grid.shape:
                return float('inf'), f"color_remap"
            
            data = ex.input_grid.data.clone()
            for from_c, to_c in color_map.items():
                data[ex.input_grid.data == from_c] = to_c
            
            total_e += compute_defect_energy(ARCGrid(data), ex.output_grid)
        
        return total_e / len(task.train_examples), f"color_remap({color_map})"
    
    def _try_crop(self, task: ARCTask) -> Tuple[float, str]:
        """Try crop to content."""
        try:
            morph = CropToContentMorphism()
            total_e = 0
            for ex in task.train_examples:
                result = morph.apply(ex.input_grid, self.config)
                if result.shape != ex.output_grid.shape:
                    return float('inf'), "crop"
                total_e += compute_defect_energy(result, ex.output_grid)
            return total_e / len(task.train_examples), "crop_to_content"
        except:
            return float('inf'), "crop"
    
    def _try_scale(self, task: ARCTask, context: PhysicsContext) -> Tuple[float, str]:
        """Apply detected scaling."""
        factor = context.parameters.get(PhysicsType.SCALE, {}).get('factor', 2)
        
        total_e = 0
        for ex in task.train_examples:
            # Simple nearest-neighbor scaling
            data = ex.input_grid.data
            scaled = data.repeat_interleave(factor, dim=0).repeat_interleave(factor, dim=1)
            
            if scaled.shape != ex.output_grid.shape:
                return float('inf'), f"scale_{factor}x"
            
            total_e += compute_defect_energy(ARCGrid(scaled), ex.output_grid)
        
        return total_e / len(task.train_examples), f"scale_{factor}x"
    
    def _try_global_motion(self, task: ARCTask, context: PhysicsContext) -> Tuple[float, str]:
        """Apply detected global motion."""
        vector = context.parameters.get(PhysicsType.GLOBAL_MOTION, {}).get('vector', (0, 0))
        dr, dc = vector
        
        total_e = 0
        for ex in task.train_examples:
            if ex.input_grid.shape != ex.output_grid.shape:
                return float('inf'), f"shift({dr},{dc})"
            
            H, W = ex.input_grid.shape
            data = torch.full_like(ex.input_grid.data, self.config.background_color)
            
            for r in range(H):
                for c in range(W):
                    new_r, new_c = r + dr, c + dc
                    if 0 <= new_r < H and 0 <= new_c < W:
                        data[new_r, new_c] = ex.input_grid.data[r, c]
            
            total_e += compute_defect_energy(ARCGrid(data), ex.output_grid)
        
        return total_e / len(task.train_examples), f"shift({dr},{dc})"
    
    def _try_canonical_space(self, task: ARCTask) -> Tuple[float, str]:
        """
        Solve in canonical space, then invert.
        The hypothesis: transformations become simpler in canonical form.
        """
        best_e = float('inf')
        best_m = "none"
        
        # Canonicalize all examples
        canonical_examples = []
        for ex in task.train_examples:
            try:
                canon_in = self.canonicalizer.to_canonical(ex.input_grid)
                canon_out = self.canonicalizer.to_canonical(ex.output_grid)
                canonical_examples.append((canon_in, canon_out, ex))
            except:
                return float('inf'), "canonical_failed"
        
        if not canonical_examples:
            return float('inf'), "canonical_empty"
        
        # Try identity in canonical space
        total_e = 0
        valid = True
        for canon_in, canon_out, ex in canonical_examples:
            if canon_in.grid.shape != canon_out.grid.shape:
                valid = False
                break
            total_e += compute_defect_energy(canon_in.grid, canon_out.grid)
        
        if valid:
            avg_e = total_e / len(canonical_examples)
            if avg_e < best_e:
                best_e = avg_e
                best_m = "identity_in_canonical"
        
        # Try simple transformations in canonical space
        for pot in self.potentials:
            for sign in [-1.0, 1.0]:
                weights = np.zeros(4)
                weights[self.potentials.index(pot)] = sign
                potential = CompositePotential(self.potentials, weights)
                
                total_e = 0
                valid = True
                for canon_in, canon_out, ex in canonical_examples:
                    try:
                        result = relax_all_colors(canon_in.grid, potential, self.config)
                        if result.shape != canon_out.grid.shape:
                            valid = False
                            break
                        total_e += compute_defect_energy(result, canon_out.grid)
                    except:
                        valid = False
                        break
                
                if valid:
                    avg_e = total_e / len(canonical_examples)
                    if avg_e < best_e:
                        best_e = avg_e
                        best_m = f"canonical_{sign:+.0f}*{pot.name()}"
        
        return best_e, best_m
    
    def _make_result(self, task: ARCTask, energy: float, method: str, 
                     context: PhysicsContext, start_time: float) -> Dict:
        return {
            'task_id': task.task_id,
            'avg_train_energy': energy,
            'method': method,
            'detected_physics': [p.name for p in context.detected_physics],
            'elapsed_ms': (time.time() - start_time) * 1000,
            'is_perfect': energy < self.config.energy_threshold
        }


# =============================================================================
# MAIN
# =============================================================================

def run_phase17(data_path: str):
    printfl("=" * 70)
    printfl("ARC-SGC Phase 17: The Invariant Physics Engine")
    printfl("=" * 70)
    printfl("\nCOMPONENTS:")
    printfl("  1. Canonicalizer: COM centering, principal axis, color normalization")
    printfl("  2. PhysicsDetector: Motion, conservation, topology, scale, crop, remap")
    printfl("  3. ContextGuidedSolver: Physics-informed search pruning")
    printfl()
    
    config = ARCPhase83Config()
    tasks = load_arc_tasks(data_path, 'cpu')
    printfl(f"Loaded {len(tasks)} tasks")
    
    solver = ContextGuidedSolver(config)
    
    all_results = []
    perfect_tasks = []
    method_counts = Counter()
    physics_counts = Counter()
    
    printfl("\n" + "=" * 50)
    printfl("Running Invariant Physics Engine")
    printfl("=" * 50)
    
    for i, task in enumerate(tasks):
        result = solver.solve_task(task)
        all_results.append(result)
        
        # Track physics detections
        for physics in result.get('detected_physics', []):
            physics_counts[physics] += 1
        
        if result['is_perfect']:
            perfect_tasks.append(result)
            method = result['method']
            method_type = method.split(':')[0]
            method_counts[method_type] += 1
            
            printfl(f"  [PERFECT] {task.task_id}: {method}")
            if result.get('detected_physics'):
                printfl(f"            Physics: {result['detected_physics']}")
        
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
    
    printfl(f"\nPhysics detection frequency:")
    for physics, count in physics_counts.most_common():
        printfl(f"  {physics}: {count} tasks")
    
    # Near-misses
    near_misses = [r for r in all_results if 0.0001 < r['avg_train_energy'] < 0.1]
    printfl(f"\nNear-misses (E<0.1): {len(near_misses)}")
    for r in sorted(near_misses, key=lambda x: x['avg_train_energy'])[:10]:
        printfl(f"  {r['task_id']}: E={r['avg_train_energy']:.4f} ({r['method']})")
        if r.get('detected_physics'):
            printfl(f"            Physics: {r['detected_physics']}")
    
    # Progress
    printfl(f"\n=== COMPLETE PROGRESS SUMMARY ===")
    printfl(f"  Phase 8.3:   6 perfect (baseline)")
    printfl(f"  Phase 15:   19 perfect (CEGAR)")
    printfl(f"  Phase 17:   {len(perfect_tasks)} perfect (INVARIANT PHYSICS)")
    
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
