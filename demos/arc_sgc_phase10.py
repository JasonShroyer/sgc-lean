"""
ARC-SGC Phase 10: Relational Physics & Topology

DIAGNOSIS FROM PHASE 9c:
- 33 near-misses predict physics=none with 99%+ confidence
- Policy is saying "I see the pattern, but I don't have a name for it"
- Single-particle potentials (V_1) fail → need Interaction Potentials (V_12)

THE MISSING PHYSICS (SGC Theory):
1. TOPOLOGY: Enclosure, Connectivity, Holes (Homology)
2. CAUSALITY: Pattern completion, Line extension (Predictability)
3. LOCAL INTERACTIONS: Flood fill, Neighbor coloring (Markov Blankets)

NEW OPERATORS:
- Topological Potentials: V_enclosed_by(color), V_connected_to(color)
- Relational Color Ops: flood_fill, color_enclosed_region, extend_line
- Causal Primitives: copy_relative, complete_pattern

This transitions from "Classical Mechanics" to "Field Theory".
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import Dataset, DataLoader
from dataclasses import dataclass
from typing import List, Tuple, Dict, Optional, Set
from collections import deque, Counter
from abc import ABC, abstractmethod
import numpy as np
import json
from pathlib import Path
import sys
import time
from scipy import ndimage

# Import Phase 8.3 base components
sys.path.insert(0, str(Path(__file__).parent))
from arc_sgc_phase8_3 import (
    ARCPhase83Config, ARCGrid, ARCObject, ARCExample, ARCTask,
    load_arc_tasks, detect_objects, compute_defect_energy,
    ShapeInference, MorphismInference, ContentSolver,
    GeometryFirstSolver, ShapeMorphism, IdentityMorphism,
    CropToContentMorphism, ExtractObjectMorphism,
    ScaleMorphism, DownscaleMorphism,
    PotentialFunction, CompositePotential, relax_all_colors,
    V_BoundaryDist, V_TopEdge, V_BottomEdge, V_ContactDist
)

def printfl(*args, **kwargs):
    print(*args, **kwargs)
    sys.stdout.flush()


# =============================================================================
# CONFIGURATION
# =============================================================================

@dataclass
class Phase10Config:
    max_grid_size: int = 30
    num_colors: int = 10
    background_color: int = 0
    max_relax_steps: int = 20
    energy_threshold: float = 0.0001
    consistency_threshold: float = 0.005
    
    # Policy
    hidden_dim: int = 128
    num_geometry_families: int = 5
    num_physics_families: int = 6  # Added: topology, relational
    
    # Training
    batch_size: int = 32
    learning_rate: float = 1e-3
    num_epochs: int = 50
    
    device: str = 'cuda' if torch.cuda.is_available() else 'cpu'


PHYSICS_FAMILIES = ['movement', 'color', 'pattern', 'topology', 'relational', 'none']


# =============================================================================
# TOPOLOGICAL OPERATORS
# =============================================================================

def find_enclosed_regions(grid: ARCGrid, boundary_color: int, config) -> np.ndarray:
    """
    Find regions enclosed by boundary_color using flood fill from edges.
    Returns mask where 1 = enclosed, 0 = not enclosed.
    """
    data = grid.data.cpu().numpy()
    H, W = data.shape
    
    # Create binary mask: boundary pixels
    boundary_mask = (data == boundary_color).astype(np.uint8)
    
    # Flood fill from edges to find exterior
    exterior = np.zeros((H + 2, W + 2), dtype=np.uint8)
    padded_boundary = np.pad(boundary_mask, 1, mode='constant', constant_values=0)
    
    # Start flood fill from (0,0) - outside the grid
    queue = deque([(0, 0)])
    exterior[0, 0] = 1
    
    while queue:
        r, c = queue.popleft()
        for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
            nr, nc = r + dr, c + dc
            if 0 <= nr < H + 2 and 0 <= nc < W + 2:
                if exterior[nr, nc] == 0 and padded_boundary[nr, nc] == 0:
                    exterior[nr, nc] = 1
                    queue.append((nr, nc))
    
    # Interior = not exterior and not boundary
    interior = exterior[1:-1, 1:-1]
    enclosed = (interior == 0) & (boundary_mask == 0)
    
    return enclosed.astype(np.uint8)


def compute_connectivity_distance(grid: ARCGrid, target_color: int, config) -> np.ndarray:
    """
    Compute geodesic distance to nearest pixel of target_color.
    Uses BFS on the adjacency graph.
    """
    data = grid.data.cpu().numpy()
    H, W = data.shape
    
    # Find target pixels
    targets = np.argwhere(data == target_color)
    if len(targets) == 0:
        return np.ones((H, W)) * 1000
    
    # BFS from all target pixels
    distance = np.ones((H, W)) * 1000
    queue = deque()
    
    for r, c in targets:
        distance[r, c] = 0
        queue.append((r, c, 0))
    
    while queue:
        r, c, d = queue.popleft()
        for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
            nr, nc = r + dr, c + dc
            if 0 <= nr < H and 0 <= nc < W:
                if distance[nr, nc] > d + 1:
                    distance[nr, nc] = d + 1
                    queue.append((nr, nc, d + 1))
    
    return distance


class TopologyOp(ABC):
    """Base class for topological operations."""
    @abstractmethod
    def apply(self, grid: ARCGrid, config) -> ARCGrid:
        pass
    @abstractmethod
    def name(self) -> str:
        pass


class FloodFillOp(TopologyOp):
    """Flood fill enclosed regions with a color."""
    
    def __init__(self, boundary_color: int, fill_color: int):
        self.boundary_color = boundary_color
        self.fill_color = fill_color
    
    def apply(self, grid: ARCGrid, config) -> ARCGrid:
        data = grid.data.clone()
        enclosed = find_enclosed_regions(grid, self.boundary_color, config)
        data[torch.tensor(enclosed, dtype=torch.bool)] = self.fill_color
        return ARCGrid(data)
    
    def name(self) -> str:
        return f"flood_fill(boundary={self.boundary_color}, fill={self.fill_color})"


class FillEnclosedOp(TopologyOp):
    """Fill all enclosed regions (by any non-background) with fill_color."""
    
    def __init__(self, fill_color: int):
        self.fill_color = fill_color
    
    def apply(self, grid: ARCGrid, config) -> ARCGrid:
        data = grid.data.cpu().numpy()
        H, W = data.shape
        
        # Find exterior via flood fill from edges
        exterior = np.zeros((H + 2, W + 2), dtype=np.uint8)
        padded = np.pad(data != config.background_color, 1, mode='constant', constant_values=False)
        
        queue = deque([(0, 0)])
        exterior[0, 0] = 1
        
        while queue:
            r, c = queue.popleft()
            for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                nr, nc = r + dr, c + dc
                if 0 <= nr < H + 2 and 0 <= nc < W + 2:
                    if exterior[nr, nc] == 0 and not padded[nr, nc]:
                        exterior[nr, nc] = 1
                        queue.append((nr, nc))
        
        interior = exterior[1:-1, 1:-1]
        enclosed = (interior == 0) & (data == config.background_color)
        
        result = data.copy()
        result[enclosed] = self.fill_color
        return ARCGrid(torch.tensor(result, dtype=torch.long, device=grid.data.device))
    
    def name(self) -> str:
        return f"fill_enclosed({self.fill_color})"


class ConnectPointsOp(TopologyOp):
    """Draw lines between objects of the same color."""
    
    def __init__(self, color: int):
        self.color = color
    
    def apply(self, grid: ARCGrid, config) -> ARCGrid:
        data = grid.data.clone()
        H, W = data.shape
        
        # Find objects of this color
        objects = detect_objects(grid, config)
        color_objs = [o for o in objects if o.color == self.color]
        
        if len(color_objs) < 2:
            return grid.clone()
        
        # Get centroids
        centroids = []
        for obj in color_objs:
            rows = [p[0] for p in obj.pixels]
            cols = [p[1] for p in obj.pixels]
            centroids.append((sum(rows) // len(rows), sum(cols) // len(cols)))
        
        # Draw lines between consecutive centroids
        for i in range(len(centroids) - 1):
            r1, c1 = centroids[i]
            r2, c2 = centroids[i + 1]
            
            # Bresenham's line algorithm (simplified)
            dr = abs(r2 - r1)
            dc = abs(c2 - c1)
            sr = 1 if r1 < r2 else -1
            sc = 1 if c1 < c2 else -1
            err = dr - dc
            
            r, c = r1, c1
            while True:
                if 0 <= r < H and 0 <= c < W:
                    data[r, c] = self.color
                if r == r2 and c == c2:
                    break
                e2 = 2 * err
                if e2 > -dc:
                    err -= dc
                    r += sr
                if e2 < dr:
                    err += dr
                    c += sc
        
        return ARCGrid(data)
    
    def name(self) -> str:
        return f"connect_points({self.color})"


class ExtendLineOp(TopologyOp):
    """Extend linear patterns until boundary."""
    
    def __init__(self, color: int):
        self.color = color
    
    def apply(self, grid: ARCGrid, config) -> ARCGrid:
        data = grid.data.clone()
        H, W = data.shape
        
        # Find pixels of this color
        positions = torch.argwhere(data == self.color)
        if len(positions) < 2:
            return grid.clone()
        
        # Detect direction from first two pixels
        positions = positions.tolist()
        r1, c1 = positions[0]
        r2, c2 = positions[1]
        dr, dc = r2 - r1, c2 - c1
        
        # Normalize to unit direction
        if dr != 0: dr = dr // abs(dr)
        if dc != 0: dc = dc // abs(dc)
        
        if dr == 0 and dc == 0:
            return grid.clone()
        
        # Extend forward from last pixel
        last_r, last_c = positions[-1]
        r, c = last_r + dr, last_c + dc
        while 0 <= r < H and 0 <= c < W and data[r, c] == config.background_color:
            data[r, c] = self.color
            r += dr
            c += dc
        
        # Extend backward from first pixel
        first_r, first_c = positions[0]
        r, c = first_r - dr, first_c - dc
        while 0 <= r < H and 0 <= c < W and data[r, c] == config.background_color:
            data[r, c] = self.color
            r -= dr
            c -= dc
        
        return ARCGrid(data)
    
    def name(self) -> str:
        return f"extend_line({self.color})"


class ProjectRayOp(TopologyOp):
    """Project ray from each object until collision."""
    
    def __init__(self, color: int, direction: Tuple[int, int]):
        self.color = color
        self.direction = direction  # (dr, dc)
    
    def apply(self, grid: ARCGrid, config) -> ARCGrid:
        data = grid.data.clone()
        H, W = data.shape
        dr, dc = self.direction
        
        objects = detect_objects(grid, config)
        color_objs = [o for o in objects if o.color == self.color]
        
        for obj in color_objs:
            # Get bounding edge in direction of projection
            if dr > 0:  # Down
                start_pixels = [(max(p[0] for p in obj.pixels), c) 
                               for c in set(p[1] for p in obj.pixels)]
            elif dr < 0:  # Up
                start_pixels = [(min(p[0] for p in obj.pixels), c)
                               for c in set(p[1] for p in obj.pixels)]
            elif dc > 0:  # Right
                start_pixels = [(r, max(p[1] for p in obj.pixels))
                               for r in set(p[0] for p in obj.pixels)]
            else:  # Left
                start_pixels = [(r, min(p[1] for p in obj.pixels))
                               for r in set(p[0] for p in obj.pixels)]
            
            for sr, sc in start_pixels:
                r, c = sr + dr, sc + dc
                while 0 <= r < H and 0 <= c < W:
                    if data[r, c] != config.background_color:
                        break
                    data[r, c] = self.color
                    r += dr
                    c += dc
        
        return ARCGrid(data)
    
    def name(self) -> str:
        dir_names = {(1, 0): 'down', (-1, 0): 'up', (0, 1): 'right', (0, -1): 'left'}
        return f"project_ray({self.color}, {dir_names.get(self.direction, self.direction)})"


class MirrorOp(TopologyOp):
    """Mirror content across an axis defined by a color."""
    
    def __init__(self, axis_color: int, direction: str = 'horizontal'):
        self.axis_color = axis_color
        self.direction = direction
    
    def apply(self, grid: ARCGrid, config) -> ARCGrid:
        data = grid.data.clone()
        H, W = data.shape
        
        # Find axis
        axis_positions = torch.argwhere(data == self.axis_color)
        if len(axis_positions) == 0:
            return grid.clone()
        
        if self.direction == 'horizontal':
            # Find horizontal line (row)
            rows = axis_positions[:, 0].unique()
            if len(rows) == 1:
                axis_row = rows[0].item()
                # Mirror above to below (or vice versa)
                for r in range(axis_row):
                    mirror_r = 2 * axis_row - r
                    if 0 <= mirror_r < H:
                        for c in range(W):
                            if data[r, c] != config.background_color and data[r, c] != self.axis_color:
                                data[mirror_r, c] = data[r, c]
        else:
            # Find vertical line (column)
            cols = axis_positions[:, 1].unique()
            if len(cols) == 1:
                axis_col = cols[0].item()
                for c in range(axis_col):
                    mirror_c = 2 * axis_col - c
                    if 0 <= mirror_c < W:
                        for r in range(H):
                            if data[r, c] != config.background_color and data[r, c] != self.axis_color:
                                data[r, mirror_c] = data[r, c]
        
        return ARCGrid(data)
    
    def name(self) -> str:
        return f"mirror({self.axis_color}, {self.direction})"


class CopyObjectOp(TopologyOp):
    """Copy object to new position based on pattern."""
    
    def __init__(self, source_color: int, delta: Tuple[int, int]):
        self.source_color = source_color
        self.delta = delta
    
    def apply(self, grid: ARCGrid, config) -> ARCGrid:
        data = grid.data.clone()
        H, W = data.shape
        dr, dc = self.delta
        
        objects = detect_objects(grid, config)
        source_objs = [o for o in objects if o.color == self.source_color]
        
        for obj in source_objs:
            for r, c in obj.pixels:
                nr, nc = r + dr, c + dc
                if 0 <= nr < H and 0 <= nc < W:
                    data[nr, nc] = obj.color
        
        return ARCGrid(data)
    
    def name(self) -> str:
        return f"copy_object({self.source_color}, delta={self.delta})"


class ConnectMarkersOp(TopologyOp):
    """
    Connect pairs of same-colored markers with orthogonal lines (L-shape).
    This handles the common ARC pattern of drawing connecting lines.
    """
    
    def __init__(self, color: int):
        self.color = color
    
    def apply(self, grid: ARCGrid, config) -> ARCGrid:
        data = grid.data.clone()
        H, W = data.shape
        
        # Find all objects of this color
        objects = detect_objects(grid, config)
        color_objs = [o for o in objects if o.color == self.color]
        
        if len(color_objs) < 2:
            return grid.clone()
        
        # Get representative pixel from each object (top-left of bbox)
        markers = []
        for obj in color_objs:
            rows = [p[0] for p in obj.pixels]
            cols = [p[1] for p in obj.pixels]
            markers.append((min(rows), min(cols)))
        
        # Connect pairs with L-shaped lines
        for i in range(len(markers)):
            for j in range(i + 1, len(markers)):
                r1, c1 = markers[i]
                r2, c2 = markers[j]
                
                # Draw horizontal line then vertical (L-shape)
                for c in range(min(c1, c2), max(c1, c2) + 1):
                    if data[r1, c] == config.background_color:
                        data[r1, c] = self.color
                for r in range(min(r1, r2), max(r1, r2) + 1):
                    if data[r, c2] == config.background_color:
                        data[r, c2] = self.color
        
        return ARCGrid(data)
    
    def name(self) -> str:
        return f"connect_markers({self.color})"


class CompleteRectangleOp(TopologyOp):
    """Complete a rectangle given corner markers."""
    
    def __init__(self, color: int):
        self.color = color
    
    def apply(self, grid: ARCGrid, config) -> ARCGrid:
        data = grid.data.clone()
        H, W = data.shape
        
        objects = detect_objects(grid, config)
        color_objs = [o for o in objects if o.color == self.color]
        
        if len(color_objs) < 2:
            return grid.clone()
        
        # Get all pixel positions
        all_pixels = []
        for obj in color_objs:
            all_pixels.extend(obj.pixels)
        
        if not all_pixels:
            return grid.clone()
        
        # Find bounding rectangle
        rows = [p[0] for p in all_pixels]
        cols = [p[1] for p in all_pixels]
        r1, r2 = min(rows), max(rows)
        c1, c2 = min(cols), max(cols)
        
        # Draw rectangle border
        for c in range(c1, c2 + 1):
            if data[r1, c] == config.background_color:
                data[r1, c] = self.color
            if data[r2, c] == config.background_color:
                data[r2, c] = self.color
        for r in range(r1, r2 + 1):
            if data[r, c1] == config.background_color:
                data[r, c1] = self.color
            if data[r, c2] == config.background_color:
                data[r, c2] = self.color
        
        return ARCGrid(data)
    
    def name(self) -> str:
        return f"complete_rectangle({self.color})"


class RemoveOverlappingColorOp(TopologyOp):
    """Remove pixels where one color overlaps with another's region."""
    
    def __init__(self, remove_color: int):
        self.remove_color = remove_color
    
    def apply(self, grid: ARCGrid, config) -> ARCGrid:
        data = grid.data.clone()
        data[data == self.remove_color] = config.background_color
        return ARCGrid(data)
    
    def name(self) -> str:
        return f"remove_color({self.remove_color})"


# =============================================================================
# ENHANCED CONTENT SOLVER WITH TOPOLOGY
# =============================================================================

class TopologyContentSolver:
    """Content solver with topological and relational operators."""
    
    def __init__(self, config: Phase10Config):
        self.config = config
        self.phase83_config = ARCPhase83Config(
            max_grid_size=config.max_grid_size,
            num_colors=config.num_colors,
            background_color=config.background_color
        )
        
        # Movement potentials (from Phase 8.3)
        self.movement_potentials = [V_ContactDist(), V_TopEdge(), V_BottomEdge(), V_BoundaryDist()]
    
    def generate_topology_ops(self, grid: ARCGrid) -> List[TopologyOp]:
        """Generate candidate topological operations from grid invariants."""
        ops = []
        colors = torch.unique(grid.data).tolist()
        non_bg = [c for c in colors if c != self.config.background_color]
        
        # Fill enclosed regions
        for fill_c in non_bg[:3]:
            ops.append(FillEnclosedOp(fill_c))
        
        # Flood fill with boundary
        for boundary_c in non_bg[:3]:
            for fill_c in non_bg[:3]:
                if boundary_c != fill_c:
                    ops.append(FloodFillOp(boundary_c, fill_c))
        
        # Connect points
        for c in non_bg[:3]:
            ops.append(ConnectPointsOp(c))
        
        # Extend lines
        for c in non_bg[:3]:
            ops.append(ExtendLineOp(c))
        
        # Project rays
        for c in non_bg[:2]:
            for direction in [(1, 0), (-1, 0), (0, 1), (0, -1)]:
                ops.append(ProjectRayOp(c, direction))
        
        # Mirror
        for c in non_bg[:2]:
            ops.append(MirrorOp(c, 'horizontal'))
            ops.append(MirrorOp(c, 'vertical'))
        
        # Connect markers (NEW)
        for c in non_bg[:3]:
            ops.append(ConnectMarkersOp(c))
        
        # Complete rectangle (NEW)
        for c in non_bg[:3]:
            ops.append(CompleteRectangleOp(c))
        
        # Remove color (NEW)
        for c in non_bg[:5]:
            ops.append(RemoveOverlappingColorOp(c))
        
        return ops
    
    def solve(self, input_grid: ARCGrid, target_grid: ARCGrid) -> Tuple[ARCGrid, float, str]:
        """Try all content operations and return best."""
        best_result = input_grid.clone()
        best_energy = compute_defect_energy(input_grid, target_grid)
        best_method = "identity"
        
        if input_grid.shape != target_grid.shape:
            return best_result, 1000.0, "shape_mismatch"
        
        # 1. Try movement potentials
        for i, pot in enumerate(self.movement_potentials):
            for sign in [-1.0, 1.0]:
                weights = np.zeros(4)
                weights[i] = sign
                potential = CompositePotential(self.movement_potentials, weights)
                result = relax_all_colors(input_grid, potential, self.phase83_config)
                energy = compute_defect_energy(result, target_grid)
                if energy < best_energy:
                    best_energy = energy
                    best_result = result
                    best_method = f"{'+' if sign > 0 else '-'}1.0*{pot.name()}"
        
        # 2. Try color operations
        for from_c in range(1, 6):
            for to_c in range(0, 6):
                if from_c == to_c:
                    continue
                data = input_grid.data.clone()
                data[data == from_c] = to_c
                result = ARCGrid(data)
                energy = compute_defect_energy(result, target_grid)
                if energy < best_energy:
                    best_energy = energy
                    best_result = result
                    best_method = f"color_map({from_c}->{to_c})"
        
        # 3. Try pattern operations
        for name, rot in [('rot180', 2), ('rot90', 1), ('rot270', 3)]:
            try:
                result = ARCGrid(input_grid.data.rot90(rot, [0, 1]))
                if result.shape == target_grid.shape:
                    energy = compute_defect_energy(result, target_grid)
                    if energy < best_energy:
                        best_energy = energy
                        best_result = result
                        best_method = name
            except:
                pass
        
        for name, dim in [('flip_h', 1), ('flip_v', 0)]:
            result = ARCGrid(input_grid.data.flip(dim))
            energy = compute_defect_energy(result, target_grid)
            if energy < best_energy:
                best_energy = energy
                best_result = result
                best_method = name
        
        # 4. Try topological operations (NEW!)
        topo_ops = self.generate_topology_ops(input_grid)
        for op in topo_ops:
            try:
                result = op.apply(input_grid, self.config)
                if result.shape == target_grid.shape:
                    energy = compute_defect_energy(result, target_grid)
                    if energy < best_energy:
                        best_energy = energy
                        best_result = result
                        best_method = op.name()
            except Exception as e:
                pass
        
        return best_result, best_energy, best_method


# =============================================================================
# PHASE 10 SOLVER
# =============================================================================

class Phase10Solver:
    """Unified solver with topology and relational physics."""
    
    def __init__(self, config: Phase10Config):
        self.config = config
        self.phase83_config = ARCPhase83Config(
            energy_threshold=config.energy_threshold,
            consistency_threshold=config.consistency_threshold
        )
        self.content_solver = TopologyContentSolver(config)
        
        # Shape morphisms (from Phase 8.3)
        self.morphisms = [
            IdentityMorphism(),
            CropToContentMorphism(),
            ExtractObjectMorphism('largest'),
            ExtractObjectMorphism('smallest'),
            ScaleMorphism(2),
            ScaleMorphism(3),
            DownscaleMorphism(2),
            DownscaleMorphism(3),
        ]
    
    def check_morphism_consistency(self, morphism: ShapeMorphism, 
                                   examples: List[ARCExample]) -> bool:
        for ex in examples:
            try:
                result = morphism.apply(ex.input_grid, self.phase83_config)
                if result.shape != ex.output_grid.shape:
                    return False
            except:
                return False
        return True
    
    def solve_task(self, task: ARCTask, verbose: bool = False) -> Dict:
        start_time = time.time()
        examples = task.train_examples
        
        best_energy = float('inf')
        best_morphism = "identity"
        best_method = "identity"
        
        for morphism in self.morphisms:
            if not self.check_morphism_consistency(morphism, examples):
                continue
            
            # Solve content for each example, track avg energy
            total_e = 0
            method = "identity"
            for ex in examples:
                transformed = morphism.apply(ex.input_grid, self.phase83_config)
                result, energy, m = self.content_solver.solve(transformed, ex.output_grid)
                total_e += energy
                method = m
            
            avg_e = total_e / len(examples)
            if avg_e < best_energy:
                best_energy = avg_e
                best_morphism = morphism.name()
                best_method = method
                
                if verbose and avg_e < 0.1:
                    printfl(f"      {morphism.name()} + {method}: E={avg_e:.4f}")
            
            if best_energy < self.config.energy_threshold:
                break
        
        elapsed = time.time() - start_time
        is_perfect = best_energy < self.config.energy_threshold
        
        return {
            'task_id': task.task_id,
            'morphism': best_morphism,
            'method': best_method,
            'operation': f"{best_morphism} + {best_method}",
            'energy': best_energy,
            'elapsed_ms': elapsed * 1000,
            'is_perfect': is_perfect
        }


# =============================================================================
# EVALUATION
# =============================================================================

def classify_physics(method: str) -> str:
    """Classify physics family from method name."""
    m = method.lower()
    if 'v_' in m or 'contact' in m or 'top' in m or 'boundary' in m or 'bottom' in m:
        return 'movement'
    if 'color' in m or 'map' in m:
        return 'color'
    if 'rot' in m or 'flip' in m:
        return 'pattern'
    if 'fill' in m or 'connect' in m or 'extend' in m or 'project' in m or 'mirror' in m or 'copy' in m:
        return 'topology'
    return 'none'


def run_phase10(data_path: str, config: Phase10Config):
    printfl("=" * 70)
    printfl("ARC-SGC Phase 10: Relational Physics & Topology")
    printfl("=" * 70)
    
    tasks = load_arc_tasks(data_path, 'cpu')
    printfl(f"\nLoaded {len(tasks)} tasks")
    
    solver = Phase10Solver(config)
    
    all_results = []
    perfect_tasks = []
    near_misses = []
    physics_dist = Counter()
    
    printfl(f"\nRunning solver on {len(tasks)} tasks...")
    
    for i, task in enumerate(tasks):
        result = solver.solve_task(task, verbose=False)
        all_results.append(result)
        
        physics = classify_physics(result['method'])
        physics_dist[physics] += 1
        
        if result['is_perfect']:
            perfect_tasks.append(result)
            printfl(f"  [PERFECT] {task.task_id}: {result['operation']} ({result['elapsed_ms']:.0f}ms)")
        elif result['energy'] < 0.1:
            near_misses.append(result)
        
        if (i + 1) % 20 == 0:
            printfl(f"  Progress: {i+1}/{len(tasks)}, perfect={len(perfect_tasks)}")
    
    # Summary
    printfl("\n" + "=" * 70)
    printfl("PHASE 10 SUMMARY")
    printfl("=" * 70)
    
    printfl(f"\nResults:")
    printfl(f"  Perfect solves: {len(perfect_tasks)}")
    printfl(f"  Near-misses (E<0.1): {len(near_misses)}")
    printfl(f"  Avg energy: {np.mean([r['energy'] for r in all_results]):.4f}")
    
    printfl(f"\nPhysics distribution (perfect + partial):")
    for phys in PHYSICS_FAMILIES:
        count = physics_dist.get(phys, 0)
        printfl(f"  {phys}: {count}")
    
    # New solves from topology
    topo_solves = [r for r in perfect_tasks if classify_physics(r['method']) == 'topology']
    printfl(f"\n=== NEW TOPOLOGY SOLVES ===")
    for r in topo_solves:
        printfl(f"  {r['task_id']}: {r['method']}")
    
    printfl(f"\n=== ALL PERFECT SOLVES ===")
    for r in perfect_tasks:
        printfl(f"  {r['task_id']}: {r['operation']}")
    
    # Comparison
    printfl(f"\n=== Comparison ===")
    printfl(f"Phase 8.3/9c perfect: 6")
    printfl(f"Phase 10 perfect:     {len(perfect_tasks)}")
    printfl(f"New from topology:    {len(topo_solves)}")
    
    # Analyze near-misses using topology
    topo_near = [r for r in near_misses if classify_physics(r['method']) == 'topology']
    printfl(f"\n=== TOPOLOGY NEAR-MISSES (closest to perfect) ===")
    for r in sorted(topo_near, key=lambda x: x['energy'])[:10]:
        printfl(f"  {r['task_id']}: {r['method']} E={r['energy']:.4f}")
    
    # Best overall near-misses
    printfl(f"\n=== BEST NEAR-MISSES (all physics) ===")
    for r in sorted(near_misses, key=lambda x: x['energy'])[:15]:
        printfl(f"  {r['task_id']}: {r['method']} E={r['energy']:.4f}")
    
    return all_results


def main():
    config = Phase10Config()
    paths = ["data/arc/training", "C:/Lean4 Projects/data/arc/training"]
    arc_path = next((p for p in paths if Path(p).exists()), None)
    
    if arc_path:
        run_phase10(arc_path, config)
    else:
        printfl("ARC data not found!")


if __name__ == "__main__":
    main()
