"""
ARC-SGC Phase 5: Learned DSL & Policy

THE VOCABULARY OF PHYSICS

Phase 4 Analysis showed:
- Architecture is sound (Active Inference, Gluing, Renormalization)
- Bottleneck is DSL EXPRESSIVENESS
- Near-misses (0.04-0.06) prove we're in the right basin

Phase 5 Strategy:
1. PARAMETERIZED PRIMITIVES: Dynamic arguments from scene
2. SPATIAL PREDICATES: Topological conditions
3. NEURAL SIMULATOR: Learned policy for DSL selection

From SGC Theory:
- Physical laws are RELATIONAL (gravity depends on mass AND distance)
- Symmetries are broken by BOUNDARY CONDITIONS (topology)
- The SIMULATOR learns priors of the ARC universe

REFERENCES:
- SGC.Renormalization.lean: Coarse-graining
- SGC.Bridge.Quantum.lean: No Coherent Backaction
- demos/adaptive_polarity_v9_planner_simulator.py: Planner-Simulator architecture
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
from dataclasses import dataclass, field
from typing import List, Tuple, Dict, Optional, Set, Any, Callable
from collections import deque
from abc import ABC, abstractmethod
import numpy as np
import json
from pathlib import Path
import random
from copy import deepcopy


# =============================================================================
# CONFIGURATION
# =============================================================================

@dataclass
class ARCPhase5Config:
    """Configuration for Phase 5: Learned DSL & Policy."""
    
    max_grid_size: int = 30
    num_colors: int = 10
    background_color: int = 0
    
    # Object detection
    min_object_size: int = 1
    max_objects: int = 50
    
    # Solver
    max_search_depth: int = 5
    max_candidates: int = 40
    energy_threshold: float = 0.0001
    max_iterations: int = 20
    
    # Neural simulator
    grid_embed_dim: int = 64
    hidden_dim: int = 128
    num_dsl_categories: int = 8  # Categories of operations
    
    device: str = 'cuda' if torch.cuda.is_available() else 'cpu'


# =============================================================================
# GRID AND OBJECT STRUCTURES
# =============================================================================

@dataclass
class ARCGrid:
    data: torch.Tensor
    
    @property
    def height(self) -> int:
        return self.data.shape[0]
    
    @property
    def width(self) -> int:
        return self.data.shape[1]
    
    @property
    def shape(self) -> Tuple[int, int]:
        return (self.height, self.width)
    
    @classmethod
    def from_list(cls, grid_list: List[List[int]], device: str = 'cpu') -> 'ARCGrid':
        return cls(torch.tensor(grid_list, dtype=torch.long, device=device))
    
    def clone(self) -> 'ARCGrid':
        return ARCGrid(self.data.clone())
    
    def to_numpy(self) -> np.ndarray:
        return self.data.cpu().numpy()


@dataclass
class ARCObject:
    """Detected object with rich attributes."""
    object_id: int
    color: int
    pixels: List[Tuple[int, int]]
    
    @property
    def mass(self) -> int:
        return len(self.pixels)
    
    @property
    def bbox(self) -> Tuple[int, int, int, int]:
        if not self.pixels:
            return (0, 0, 0, 0)
        rows = [p[0] for p in self.pixels]
        cols = [p[1] for p in self.pixels]
        return (min(rows), min(cols), max(rows) + 1, max(cols) + 1)
    
    @property
    def width(self) -> int:
        r1, c1, r2, c2 = self.bbox
        return c2 - c1
    
    @property
    def height(self) -> int:
        r1, c1, r2, c2 = self.bbox
        return r2 - r1
    
    @property
    def centroid(self) -> Tuple[float, float]:
        if not self.pixels:
            return (0.0, 0.0)
        return (sum(p[0] for p in self.pixels) / len(self.pixels),
                sum(p[1] for p in self.pixels) / len(self.pixels))
    
    def get_mask(self, H: int, W: int, device: str = 'cpu') -> torch.Tensor:
        mask = torch.zeros(H, W, dtype=torch.bool, device=device)
        for r, c in self.pixels:
            if 0 <= r < H and 0 <= c < W:
                mask[r, c] = True
        return mask


@dataclass
class ARCExample:
    input_grid: ARCGrid
    output_grid: ARCGrid


@dataclass
class ARCTask:
    task_id: str
    train_examples: List[ARCExample]
    test_examples: List[ARCExample]
    
    @classmethod
    def from_json(cls, task_id: str, data: dict, device: str = 'cpu') -> 'ARCTask':
        train = [ARCExample(
            ARCGrid.from_list(ex['input'], device),
            ARCGrid.from_list(ex.get('output', ex['input']), device)
        ) for ex in data['train']]
        test = [ARCExample(
            ARCGrid.from_list(ex['input'], device),
            ARCGrid.from_list(ex.get('output', ex['input']), device)
        ) for ex in data['test']]
        return cls(task_id, train, test)


def load_arc_tasks(path: str, device: str = 'cpu', limit: int = None) -> List[ARCTask]:
    tasks = []
    p = Path(path)
    if not p.exists():
        return tasks
    for f in sorted(p.glob("*.json"))[:limit]:
        try:
            with open(f) as fp:
                tasks.append(ARCTask.from_json(f.stem, json.load(fp), device))
        except Exception as e:
            print(f"Error {f}: {e}")
    return tasks


def detect_objects(grid: ARCGrid, config: ARCPhase5Config) -> List[ARCObject]:
    """Flood-fill object detection."""
    data = grid.to_numpy()
    H, W = data.shape
    visited = np.zeros((H, W), dtype=bool)
    objects = []
    obj_id = 0
    
    for r in range(H):
        for c in range(W):
            if visited[r, c]:
                continue
            color = data[r, c]
            pixels = []
            queue = deque([(r, c)])
            visited[r, c] = True
            
            while queue:
                cr, cc = queue.popleft()
                pixels.append((cr, cc))
                for dr, dc in [(-1,0), (1,0), (0,-1), (0,1)]:
                    nr, nc = cr + dr, cc + dc
                    if 0 <= nr < H and 0 <= nc < W and not visited[nr, nc]:
                        if data[nr, nc] == color:
                            visited[nr, nc] = True
                            queue.append((nr, nc))
            
            if len(pixels) >= config.min_object_size:
                objects.append(ARCObject(obj_id, int(color), pixels))
                obj_id += 1
                if obj_id >= config.max_objects:
                    return objects
    return objects


# =============================================================================
# TASK 2: SPATIAL PREDICATES
# =============================================================================

def touches_boundary(obj: ARCObject, H: int, W: int) -> bool:
    """Check if object touches grid boundary."""
    for r, c in obj.pixels:
        if r == 0 or r == H - 1 or c == 0 or c == W - 1:
            return True
    return False


def is_enclosed(obj: ARCObject, all_objects: List[ARCObject], grid: ARCGrid) -> bool:
    """Check if object is completely surrounded by another color."""
    H, W = grid.height, grid.width
    r1, c1, r2, c2 = obj.bbox
    
    # Expand bbox by 1
    r1, c1 = max(0, r1 - 1), max(0, c1 - 1)
    r2, c2 = min(H, r2 + 1), min(W, c2 + 1)
    
    obj_mask = obj.get_mask(H, W, grid.data.device)
    
    # Check if all adjacent non-object pixels have same color
    border_colors = set()
    for r in range(r1, r2):
        for c in range(c1, c2):
            if not obj_mask[r, c]:
                # Adjacent to object?
                for dr, dc in [(-1,0), (1,0), (0,-1), (0,1)]:
                    nr, nc = r + dr, c + dc
                    if 0 <= nr < H and 0 <= nc < W and obj_mask[nr, nc]:
                        border_colors.add(grid.data[r, c].item())
                        break
    
    return len(border_colors) == 1 and border_colors != {obj.color}


def has_neighbors(obj: ARCObject, all_objects: List[ARCObject], count: int = 1) -> bool:
    """Check if object has at least N neighboring objects."""
    neighbors = 0
    for other in all_objects:
        if other.object_id == obj.object_id:
            continue
        # Check if bboxes are adjacent
        r1, c1, r2, c2 = obj.bbox
        or1, oc1, or2, oc2 = other.bbox
        
        # Adjacent if overlapping when expanded by 1
        if not (r2 < or1 - 1 or r1 > or2 + 1 or c2 < oc1 - 1 or c1 > oc2 + 1):
            neighbors += 1
            if neighbors >= count:
                return True
    return neighbors >= count


def is_largest(obj: ARCObject, all_objects: List[ARCObject]) -> bool:
    """Check if this is the largest non-background object."""
    max_mass = max((o.mass for o in all_objects if o.color != 0), default=0)
    return obj.mass == max_mass and obj.color != 0


def is_smallest(obj: ARCObject, all_objects: List[ARCObject]) -> bool:
    """Check if this is the smallest non-background object."""
    fg_objects = [o for o in all_objects if o.color != 0]
    if not fg_objects:
        return False
    min_mass = min(o.mass for o in fg_objects)
    return obj.mass == min_mass


def is_aligned_h(obj1: ARCObject, obj2: ARCObject) -> bool:
    """Check if objects are horizontally aligned (same row range)."""
    r1_1, _, r1_2, _ = obj1.bbox
    r2_1, _, r2_2, _ = obj2.bbox
    return not (r1_2 <= r2_1 or r2_2 <= r1_1)


def is_aligned_v(obj1: ARCObject, obj2: ARCObject) -> bool:
    """Check if objects are vertically aligned (same column range)."""
    _, c1_1, _, c1_2 = obj1.bbox
    _, c2_1, _, c2_2 = obj2.bbox
    return not (c1_2 <= c2_1 or c2_2 <= c1_1)


# =============================================================================
# INVARIANT DELTA
# =============================================================================

@dataclass
class InvariantDelta:
    mass_change: int
    mass_conserved: bool
    colors_changed: bool
    histogram_conserved: bool
    likely_color_swap: bool
    swap_pairs: List[Tuple[int, int]]
    size_change: Tuple[int, int]
    size_conserved: bool
    symmetry_gained_h: bool
    symmetry_gained_v: bool
    # New: object relationship changes
    object_count_change: int
    largest_object_changed: bool


def compute_delta(input_grid: ARCGrid, output_grid: ARCGrid, config: ARCPhase5Config) -> InvariantDelta:
    in_np, out_np = input_grid.to_numpy(), output_grid.to_numpy()
    bg = config.background_color
    
    in_mass = int((in_np != bg).sum())
    out_mass = int((out_np != bg).sum())
    
    in_hist, out_hist = {}, {}
    for c in range(config.num_colors):
        ic, oc = int((in_np == c).sum()), int((out_np == c).sum())
        if ic > 0: in_hist[c] = ic
        if oc > 0: out_hist[c] = oc
    
    in_colors = set(in_hist.keys()) - {bg}
    out_colors = set(out_hist.keys()) - {bg}
    
    swap_pairs = []
    likely_swap = False
    if sorted(in_hist.values()) == sorted(out_hist.values()):
        if input_grid.shape == output_grid.shape and not torch.equal(input_grid.data, output_grid.data):
            for c1 in in_hist:
                for c2 in in_hist:
                    if c1 < c2 and in_hist.get(c1,0) == out_hist.get(c2,0) and in_hist.get(c2,0) == out_hist.get(c1,0):
                        if in_hist.get(c1,0) != in_hist.get(c2,0):
                            swap_pairs.append((c1, c2))
                            likely_swap = True
    
    in_objs = detect_objects(input_grid, config)
    out_objs = detect_objects(output_grid, config)
    
    in_largest = max((o.mass for o in in_objs if o.color != bg), default=0)
    out_largest = max((o.mass for o in out_objs if o.color != bg), default=0)
    
    ref_h_in = np.array_equal(in_np, np.flip(in_np, axis=1))
    ref_h_out = np.array_equal(out_np, np.flip(out_np, axis=1))
    ref_v_in = np.array_equal(in_np, np.flip(in_np, axis=0))
    ref_v_out = np.array_equal(out_np, np.flip(out_np, axis=0))
    
    return InvariantDelta(
        mass_change=out_mass - in_mass,
        mass_conserved=abs(out_mass - in_mass) < 3,
        colors_changed=(in_colors != out_colors),
        histogram_conserved=(in_hist == out_hist),
        likely_color_swap=likely_swap,
        swap_pairs=swap_pairs,
        size_change=(output_grid.height - input_grid.height, output_grid.width - input_grid.width),
        size_conserved=(input_grid.shape == output_grid.shape),
        symmetry_gained_h=(ref_h_out and not ref_h_in),
        symmetry_gained_v=(ref_v_out and not ref_v_in),
        object_count_change=len(out_objs) - len(in_objs),
        largest_object_changed=(in_largest != out_largest)
    )


# =============================================================================
# TASK 1: PARAMETERIZED DSL PRIMITIVES
# =============================================================================

class DSLPrimitive(ABC):
    """Base DSL primitive."""
    
    @abstractmethod
    def apply(self, grid: ARCGrid, config: ARCPhase5Config) -> ARCGrid:
        pass
    
    @abstractmethod
    def signature(self) -> str:
        pass
    
    def category(self) -> int:
        """Category for neural policy: 0=identity, 1=geometry, 2=color, 3=spatial, etc."""
        return 0
    
    def priority(self, delta: InvariantDelta) -> float:
        return 0.5


class Identity(DSLPrimitive):
    def apply(self, grid, config): return grid.clone()
    def signature(self): return "identity"
    def priority(self, delta): return 0.01


class Rotate90(DSLPrimitive):
    def apply(self, grid, config):
        return ARCGrid(torch.rot90(grid.data, k=-1))
    def signature(self): return "rotate_90"
    def category(self): return 1
    def priority(self, delta):
        return 0.8 if delta.mass_conserved and not delta.colors_changed else 0.2


class Rotate180(DSLPrimitive):
    def apply(self, grid, config):
        return ARCGrid(torch.rot90(grid.data, k=2))
    def signature(self): return "rotate_180"
    def category(self): return 1
    def priority(self, delta):
        return 0.7 if delta.mass_conserved else 0.2


class FlipH(DSLPrimitive):
    def apply(self, grid, config):
        return ARCGrid(torch.flip(grid.data, dims=[1]))
    def signature(self): return "flip_h"
    def category(self): return 1
    def priority(self, delta):
        return 0.9 if delta.symmetry_gained_h else 0.5


class FlipV(DSLPrimitive):
    def apply(self, grid, config):
        return ARCGrid(torch.flip(grid.data, dims=[0]))
    def signature(self): return "flip_v"
    def category(self): return 1
    def priority(self, delta):
        return 0.9 if delta.symmetry_gained_v else 0.5


class ColorSwap(DSLPrimitive):
    def __init__(self, a: int, b: int):
        self.a, self.b = a, b
    
    def apply(self, grid, config):
        data = grid.data.clone()
        ma, mb = (data == self.a), (data == self.b)
        data[ma], data[mb] = self.b, self.a
        return ARCGrid(data)
    
    def signature(self): return f"swap_{self.a}_{self.b}"
    def category(self): return 2
    def priority(self, delta):
        if (self.a, self.b) in delta.swap_pairs or (self.b, self.a) in delta.swap_pairs:
            return 0.95
        return 0.3 if delta.likely_color_swap else 0.1


class Recolor(DSLPrimitive):
    def __init__(self, from_c: int, to_c: int):
        self.from_c, self.to_c = from_c, to_c
    
    def apply(self, grid, config):
        data = grid.data.clone()
        data[data == self.from_c] = self.to_c
        return ARCGrid(data)
    
    def signature(self): return f"recolor_{self.from_c}_to_{self.to_c}"
    def category(self): return 2
    def priority(self, delta):
        return 0.7 if delta.colors_changed else 0.2


class Shift(DSLPrimitive):
    def __init__(self, dr: int, dc: int):
        self.dr, self.dc = dr, dc
    
    def apply(self, grid, config):
        data = grid.data.clone()
        H, W = data.shape
        result = torch.full_like(data, config.background_color)
        
        for r in range(H):
            for c in range(W):
                nr, nc = r + self.dr, c + self.dc
                if 0 <= nr < H and 0 <= nc < W:
                    result[nr, nc] = data[r, c]
        
        return ARCGrid(result)
    
    def signature(self): return f"shift_{self.dr}_{self.dc}"
    def category(self): return 1
    def priority(self, delta):
        return 0.6 if delta.mass_conserved and not delta.colors_changed else 0.3


class Crop(DSLPrimitive):
    def apply(self, grid, config):
        data = grid.data
        mask = (data != config.background_color)
        if not mask.any():
            return grid.clone()
        rows = mask.any(dim=1).nonzero().flatten()
        cols = mask.any(dim=0).nonzero().flatten()
        if len(rows) == 0:
            return grid.clone()
        return ARCGrid(data[rows[0]:rows[-1]+1, cols[0]:cols[-1]+1].clone())
    
    def signature(self): return "crop"
    def category(self): return 3
    def priority(self, delta):
        return 0.8 if not delta.size_conserved else 0.2


# --- PARAMETERIZED PRIMITIVES ---

class ShiftToBoundary(DSLPrimitive):
    """Shift all foreground until it touches boundary."""
    def __init__(self, direction: str):
        self.direction = direction  # 'up', 'down', 'left', 'right'
    
    def apply(self, grid, config):
        data = grid.data.clone()
        H, W = data.shape
        bg = config.background_color
        
        if self.direction == 'up':
            for c in range(W):
                col = data[:, c].clone()
                fg_idx = (col != bg).nonzero().flatten()
                if len(fg_idx) > 0:
                    fg_vals = col[fg_idx]
                    data[:, c] = bg
                    data[:len(fg_vals), c] = fg_vals
        
        elif self.direction == 'down':
            for c in range(W):
                col = data[:, c].clone()
                fg_idx = (col != bg).nonzero().flatten()
                if len(fg_idx) > 0:
                    fg_vals = col[fg_idx]
                    data[:, c] = bg
                    data[H-len(fg_vals):, c] = fg_vals
        
        elif self.direction == 'left':
            for r in range(H):
                row = data[r, :].clone()
                fg_idx = (row != bg).nonzero().flatten()
                if len(fg_idx) > 0:
                    fg_vals = row[fg_idx]
                    data[r, :] = bg
                    data[r, :len(fg_vals)] = fg_vals
        
        elif self.direction == 'right':
            for r in range(H):
                row = data[r, :].clone()
                fg_idx = (row != bg).nonzero().flatten()
                if len(fg_idx) > 0:
                    fg_vals = row[fg_idx]
                    data[r, :] = bg
                    data[r, W-len(fg_vals):] = fg_vals
        
        return ARCGrid(data)
    
    def signature(self): return f"shift_to_{self.direction}"
    def category(self): return 4
    def priority(self, delta):
        return 0.7 if delta.mass_conserved else 0.3


class ShiftObjectToBoundary(DSLPrimitive):
    """Shift objects of specific color to boundary."""
    def __init__(self, color: int, direction: str):
        self.color = color
        self.direction = direction
    
    def apply(self, grid, config):
        data = grid.data.clone()
        H, W = data.shape
        
        # Find objects of this color
        objects = detect_objects(grid, config)
        color_objs = [o for o in objects if o.color == self.color]
        
        if not color_objs:
            return ARCGrid(data)
        
        for obj in color_objs:
            mask = obj.get_mask(H, W, data.device)
            r1, c1, r2, c2 = obj.bbox
            
            # Clear original
            data[mask] = config.background_color
            
            # Compute new position
            if self.direction == 'up':
                new_r1 = 0
            elif self.direction == 'down':
                new_r1 = H - (r2 - r1)
            elif self.direction == 'left':
                new_c1 = 0
            elif self.direction == 'right':
                new_c1 = W - (c2 - c1)
            else:
                continue
            
            # Place at new position
            for r, c in obj.pixels:
                if self.direction in ['up', 'down']:
                    nr = new_r1 + (r - r1)
                    nc = c
                else:
                    nr = r
                    nc = new_c1 + (c - c1)
                
                if 0 <= nr < H and 0 <= nc < W:
                    data[nr, nc] = self.color
        
        return ARCGrid(data)
    
    def signature(self): return f"shift_obj_{self.color}_to_{self.direction}"
    def category(self): return 4
    def priority(self, delta):
        return 0.6 if delta.mass_conserved else 0.2


class CopyToPoints(DSLPrimitive):
    """Copy pattern at marker color locations."""
    def __init__(self, pattern_color: int, marker_color: int):
        self.pattern_color = pattern_color
        self.marker_color = marker_color
    
    def apply(self, grid, config):
        data = grid.data.clone()
        H, W = data.shape
        
        # Find pattern (object of pattern_color)
        objects = detect_objects(grid, config)
        pattern_objs = [o for o in objects if o.color == self.pattern_color]
        marker_objs = [o for o in objects if o.color == self.marker_color]
        
        if not pattern_objs or not marker_objs:
            return ARCGrid(data)
        
        pattern = pattern_objs[0]
        pr1, pc1, pr2, pc2 = pattern.bbox
        pattern_pixels = [(r - pr1, c - pc1) for r, c in pattern.pixels]
        
        # Copy pattern to each marker centroid
        for marker in marker_objs:
            mr, mc = int(marker.centroid[0]), int(marker.centroid[1])
            for dr, dc in pattern_pixels:
                nr, nc = mr + dr, mc + dc
                if 0 <= nr < H and 0 <= nc < W:
                    data[nr, nc] = self.pattern_color
        
        return ARCGrid(data)
    
    def signature(self): return f"copy_{self.pattern_color}_to_{self.marker_color}"
    def category(self): return 5
    def priority(self, delta):
        return 0.5 if delta.mass_change > 0 else 0.2


class EncloseWith(DSLPrimitive):
    """Draw enclosing rectangle around objects of a color."""
    def __init__(self, target_color: int, border_color: int):
        self.target_color = target_color
        self.border_color = border_color
    
    def apply(self, grid, config):
        data = grid.data.clone()
        H, W = data.shape
        
        objects = detect_objects(grid, config)
        targets = [o for o in objects if o.color == self.target_color]
        
        for obj in targets:
            r1, c1, r2, c2 = obj.bbox
            # Expand by 1
            r1, c1 = max(0, r1 - 1), max(0, c1 - 1)
            r2, c2 = min(H, r2 + 1), min(W, c2 + 1)
            
            # Draw border
            for r in range(r1, r2):
                if c1 >= 0: data[r, c1] = self.border_color
                if c2 - 1 < W: data[r, c2 - 1] = self.border_color
            for c in range(c1, c2):
                if r1 >= 0: data[r1, c] = self.border_color
                if r2 - 1 < H: data[r2 - 1, c] = self.border_color
        
        return ARCGrid(data)
    
    def signature(self): return f"enclose_{self.target_color}_with_{self.border_color}"
    def category(self): return 5
    def priority(self, delta):
        return 0.5 if delta.mass_change > 0 else 0.2


class FillEnclosed(DSLPrimitive):
    """Fill enclosed regions with a color."""
    def __init__(self, fill_color: int):
        self.fill_color = fill_color
    
    def apply(self, grid, config):
        data = grid.data.clone()
        H, W = data.shape
        bg = config.background_color
        
        # Flood fill from edges to find exterior
        exterior = torch.zeros(H, W, dtype=torch.bool, device=data.device)
        queue = deque()
        
        for r in range(H):
            if data[r, 0] == bg:
                queue.append((r, 0))
                exterior[r, 0] = True
            if data[r, W-1] == bg:
                queue.append((r, W-1))
                exterior[r, W-1] = True
        for c in range(W):
            if data[0, c] == bg:
                queue.append((0, c))
                exterior[0, c] = True
            if data[H-1, c] == bg:
                queue.append((H-1, c))
                exterior[H-1, c] = True
        
        while queue:
            r, c = queue.popleft()
            for dr, dc in [(-1,0), (1,0), (0,-1), (0,1)]:
                nr, nc = r + dr, c + dc
                if 0 <= nr < H and 0 <= nc < W:
                    if not exterior[nr, nc] and data[nr, nc] == bg:
                        exterior[nr, nc] = True
                        queue.append((nr, nc))
        
        # Fill interior
        interior = (data == bg) & ~exterior
        data[interior] = self.fill_color
        
        return ARCGrid(data)
    
    def signature(self): return f"fill_enclosed_{self.fill_color}"
    def category(self): return 5
    def priority(self, delta):
        return 0.6 if delta.mass_change > 0 else 0.2


class MapIf(DSLPrimitive):
    """Apply operation only to objects satisfying predicate."""
    def __init__(self, op: DSLPrimitive, predicate: str, color: int = None):
        self.op = op
        self.predicate = predicate  # 'largest', 'smallest', 'touches_boundary', 'enclosed'
        self.color = color
    
    def apply(self, grid, config):
        H, W = grid.height, grid.width
        objects = detect_objects(grid, config)
        
        # Select objects by predicate
        selected = []
        for obj in objects:
            if obj.color == config.background_color:
                continue
            
            if self.predicate == 'largest' and is_largest(obj, objects):
                selected.append(obj)
            elif self.predicate == 'smallest' and is_smallest(obj, objects):
                selected.append(obj)
            elif self.predicate == 'touches_boundary' and touches_boundary(obj, H, W):
                selected.append(obj)
            elif self.predicate == 'enclosed' and is_enclosed(obj, objects, grid):
                selected.append(obj)
            elif self.predicate == 'color' and obj.color == self.color:
                selected.append(obj)
        
        if not selected:
            return grid.clone()
        
        # Build mask for selected objects
        mask = torch.zeros(H, W, dtype=torch.bool, device=grid.data.device)
        for obj in selected:
            mask = mask | obj.get_mask(H, W, grid.data.device)
        
        # Apply operation to masked region
        # For simplicity, apply globally but preserve unmasked
        result = self.op.apply(grid, config)
        
        # Blend: keep original where not masked
        final = grid.data.clone()
        final[mask] = result.data[mask]
        
        return ARCGrid(final)
    
    def signature(self):
        if self.color is not None:
            return f"map_if({self.op.signature()}, {self.predicate}={self.color})"
        return f"map_if({self.op.signature()}, {self.predicate})"
    
    def category(self): return 6
    def priority(self, delta):
        return self.op.priority(delta) * 0.9


class ShiftByObjectSize(DSLPrimitive):
    """Shift objects by their own width/height."""
    def __init__(self, color: int, axis: str):
        self.color = color
        self.axis = axis  # 'width' or 'height'
    
    def apply(self, grid, config):
        data = grid.data.clone()
        H, W = data.shape
        
        objects = detect_objects(grid, config)
        targets = [o for o in objects if o.color == self.color]
        
        for obj in targets:
            mask = obj.get_mask(H, W, data.device)
            data[mask] = config.background_color
            
            shift = obj.width if self.axis == 'width' else obj.height
            
            for r, c in obj.pixels:
                if self.axis == 'width':
                    nc = c + shift
                    nr = r
                else:
                    nr = r + shift
                    nc = c
                
                if 0 <= nr < H and 0 <= nc < W:
                    data[nr, nc] = self.color
        
        return ARCGrid(data)
    
    def signature(self): return f"shift_{self.color}_by_{self.axis}"
    def category(self): return 4
    def priority(self, delta):
        return 0.7 if delta.mass_conserved else 0.3


class ComposedOp(DSLPrimitive):
    def __init__(self, ops: List[DSLPrimitive]):
        self.ops = ops
    
    def apply(self, grid, config):
        result = grid
        for op in self.ops:
            result = op.apply(result, config)
        return result
    
    def signature(self):
        return " -> ".join(op.signature() for op in self.ops)
    
    def category(self): return 7
    def priority(self, delta):
        return max(op.priority(delta) for op in self.ops) if self.ops else 0.0


# =============================================================================
# TASK 3: NEURAL SIMULATOR (LEARNED POLICY)
# =============================================================================

class NeuralSimulator(nn.Module):
    """
    The Simulator: Learns to predict which DSL category is useful.
    
    Input: Grid pair embedding
    Output: Probability distribution over DSL categories
    
    This implements LEARNED PRIORS for Active Inference.
    """
    
    def __init__(self, config: ARCPhase5Config):
        super().__init__()
        self.config = config
        
        # Grid encoder: simple CNN
        self.encoder = nn.Sequential(
            nn.Conv2d(config.num_colors, 32, 3, padding=1),
            nn.ReLU(),
            nn.MaxPool2d(2),
            nn.Conv2d(32, 64, 3, padding=1),
            nn.ReLU(),
            nn.AdaptiveAvgPool2d(4)
        )
        
        # Combine input + output embeddings
        self.combiner = nn.Sequential(
            nn.Linear(64 * 4 * 4 * 2, config.hidden_dim),
            nn.ReLU(),
            nn.Linear(config.hidden_dim, config.hidden_dim)
        )
        
        # Category predictor
        self.predictor = nn.Linear(config.hidden_dim, config.num_dsl_categories)
    
    def encode_grid(self, grid: ARCGrid) -> torch.Tensor:
        """Encode grid to fixed-size tensor."""
        # One-hot encode colors
        H, W = grid.height, grid.width
        one_hot = F.one_hot(grid.data, self.config.num_colors).float()  # H x W x C
        one_hot = one_hot.permute(2, 0, 1).unsqueeze(0)  # 1 x C x H x W
        
        # Pad to fixed size
        padded = F.pad(one_hot, (0, 30-W, 0, 30-H))
        
        return self.encoder(padded).flatten(1)  # 1 x (64*4*4)
    
    def forward(self, input_grid: ARCGrid, output_grid: ARCGrid) -> torch.Tensor:
        """Predict DSL category distribution."""
        in_enc = self.encode_grid(input_grid)
        out_enc = self.encode_grid(output_grid)
        combined = torch.cat([in_enc, out_enc], dim=1)
        hidden = self.combiner(combined)
        return F.softmax(self.predictor(hidden), dim=-1)
    
    def get_category_weights(self, input_grid: ARCGrid, output_grid: ARCGrid) -> Dict[int, float]:
        """Get learned weights for each DSL category."""
        with torch.no_grad():
            probs = self.forward(input_grid, output_grid).squeeze()
        return {i: probs[i].item() for i in range(self.config.num_dsl_categories)}


# =============================================================================
# DSL LIBRARY BUILDER
# =============================================================================

def build_dsl_library(config: ARCPhase5Config) -> List[DSLPrimitive]:
    """Build expanded DSL library."""
    ops: List[DSLPrimitive] = [
        Identity(),
        Rotate90(), Rotate180(),
        FlipH(), FlipV(),
        Crop(),
    ]
    
    # Color swaps
    for a in range(config.num_colors):
        for b in range(a + 1, config.num_colors):
            ops.append(ColorSwap(a, b))
    
    # Recolors
    for a in range(config.num_colors):
        for b in range(config.num_colors):
            if a != b:
                ops.append(Recolor(a, b))
    
    # Shifts
    for dr in [-1, 0, 1]:
        for dc in [-1, 0, 1]:
            if dr != 0 or dc != 0:
                ops.append(Shift(dr, dc))
    
    # === NEW PARAMETERIZED PRIMITIVES ===
    
    # Shift to boundary
    for direction in ['up', 'down', 'left', 'right']:
        ops.append(ShiftToBoundary(direction))
    
    # Shift specific color objects to boundary
    for color in range(1, 6):
        for direction in ['up', 'down', 'left', 'right']:
            ops.append(ShiftObjectToBoundary(color, direction))
    
    # Shift by object size
    for color in range(1, 6):
        for axis in ['width', 'height']:
            ops.append(ShiftByObjectSize(color, axis))
    
    # Fill enclosed
    for color in range(1, 6):
        ops.append(FillEnclosed(color))
    
    # Enclose with border
    for target in range(1, 4):
        for border in range(1, 4):
            if target != border:
                ops.append(EncloseWith(target, border))
    
    # Copy to points (limited combinations)
    for pattern in range(1, 4):
        for marker in range(1, 4):
            if pattern != marker:
                ops.append(CopyToPoints(pattern, marker))
    
    # MapIf with predicates
    base_ops = [Shift(0, 1), Shift(1, 0), FlipH(), FlipV(), Rotate90()]
    for base in base_ops:
        for pred in ['largest', 'smallest', 'touches_boundary']:
            ops.append(MapIf(base, pred))
    
    # MapIf with color
    for color in range(1, 5):
        for base in [Shift(0, 1), Shift(1, 0), Shift(-1, 0), Shift(0, -1)]:
            ops.append(MapIf(base, 'color', color))
    
    return ops


# =============================================================================
# PHASE 5 SOLVER
# =============================================================================

class Phase5Solver:
    """
    Phase 5 Solver with expanded DSL and neural policy.
    
    Key features:
    1. Expanded parameterized DSL
    2. Spatial predicates
    3. Neural policy for category weighting
    4. Greedy search with composition
    """
    
    def __init__(self, config: ARCPhase5Config):
        self.config = config
        self.dsl = build_dsl_library(config)
        self.simulator = NeuralSimulator(config).to(config.device)
        self.use_neural_policy = False  # Enable after training
        
        print(f"   DSL: {len(self.dsl)} primitives")
        
        # Group by category
        self.ops_by_cat = {}
        for op in self.dsl:
            cat = op.category()
            if cat not in self.ops_by_cat:
                self.ops_by_cat[cat] = []
            self.ops_by_cat[cat].append(op)
    
    def compute_energy(self, pred: ARCGrid, target: ARCGrid) -> float:
        if pred.shape != target.shape:
            return 1000.0 + abs(pred.height - target.height) + abs(pred.width - target.width)
        return (pred.data != target.data).float().sum().item() / target.data.numel()
    
    def solve(
        self,
        input_grid: ARCGrid,
        target_grid: ARCGrid,
        verbose: bool = False
    ) -> Tuple[DSLPrimitive, float]:
        """Solve with expanded DSL and optional neural policy."""
        
        delta = compute_delta(input_grid, target_grid, self.config)
        
        if verbose:
            print(f"   Delta: mass={delta.mass_change}, colors_changed={delta.colors_changed}")
        
        # Get category weights (neural or uniform)
        if self.use_neural_policy:
            cat_weights = self.simulator.get_category_weights(input_grid, target_grid)
        else:
            cat_weights = {i: 1.0 for i in range(self.config.num_dsl_categories)}
        
        # Rank all operations
        ranked = []
        for op in self.dsl:
            base_priority = op.priority(delta)
            cat_boost = cat_weights.get(op.category(), 1.0)
            score = base_priority * (0.5 + 0.5 * cat_boost)
            ranked.append((score, op))
        
        ranked.sort(key=lambda x: -x[0])
        
        # Greedy search
        current = input_grid
        program_parts: List[DSLPrimitive] = []
        visited: Set[bytes] = {current.data.cpu().numpy().tobytes()}
        
        best_energy = self.compute_energy(current, target_grid)
        best_program: List[DSLPrimitive] = []
        
        for iteration in range(self.config.max_iterations):
            energy = self.compute_energy(current, target_grid)
            
            if energy < best_energy:
                best_energy = energy
                best_program = program_parts.copy()
            
            if energy < self.config.energy_threshold:
                if verbose:
                    print(f"   SOLVED at iteration {iteration + 1}!")
                break
            
            if verbose and iteration < 6:
                print(f"   Iter {iteration + 1}: E={energy:.4f}")
            
            # Find best improvement
            best_op, best_new_energy, best_result = None, energy, None
            
            for score, op in ranked[:self.config.max_candidates]:
                try:
                    result = op.apply(current, self.config)
                    h = result.data.cpu().numpy().tobytes()
                    
                    if h in visited:
                        continue
                    
                    new_energy = self.compute_energy(result, target_grid)
                    
                    if new_energy < best_new_energy:
                        best_op = op
                        best_new_energy = new_energy
                        best_result = result
                        
                        if new_energy < self.config.energy_threshold:
                            break
                except Exception:
                    continue
            
            if best_op is None:
                if verbose:
                    print(f"   No improvement found")
                break
            
            current = best_result
            visited.add(current.data.cpu().numpy().tobytes())
            program_parts.append(best_op)
            
            if verbose:
                print(f"   Applied: {best_op.signature()} -> E={best_new_energy:.4f}")
        
        # Return best found
        if not best_program:
            return Identity(), best_energy
        elif len(best_program) == 1:
            return best_program[0], best_energy
        else:
            return ComposedOp(best_program), best_energy


# =============================================================================
# EVALUATION
# =============================================================================

def evaluate_task(solver: Phase5Solver, task: ARCTask, config: ARCPhase5Config, verbose: bool = False) -> Dict:
    results = {'task_id': task.task_id, 'train': [], 'test': [], 'programs': []}
    
    for i, ex in enumerate(task.train_examples):
        if verbose:
            print(f"\n   Train {i+1}:")
        program, energy = solver.solve(ex.input_grid, ex.output_grid, verbose)
        results['train'].append({'energy': energy, 'program': program.signature()})
        results['programs'].append(program)
        if verbose:
            print(f"   Result: {program.signature()} (E={energy:.6f})")
    
    for i, ex in enumerate(task.test_examples):
        if results['programs']:
            pred = results['programs'][0].apply(ex.input_grid, config)
            energy = solver.compute_energy(pred, ex.output_grid)
        else:
            energy = solver.compute_energy(ex.input_grid, ex.output_grid)
        results['test'].append({'energy': energy})
    
    return results


def run_evaluation(data_path: str, config: ARCPhase5Config, num_tasks: int = 10) -> List[Dict]:
    print("=" * 70)
    print("ARC-SGC Phase 5: Learned DSL & Policy")
    print("=" * 70)
    
    tasks = load_arc_tasks(data_path, config.device, num_tasks)
    print(f"\nLoaded {len(tasks)} tasks")
    
    if not tasks:
        return []
    
    print("\nBuilding Phase 5 Solver...")
    solver = Phase5Solver(config)
    
    all_results = []
    
    for i, task in enumerate(tasks):
        print(f"\n{'='*70}")
        print(f"Task {i+1}/{len(tasks)}: {task.task_id}")
        
        results = evaluate_task(solver, task, config, verbose=True)
        all_results.append(results)
        
        avg_train = np.mean([r['energy'] for r in results['train']])
        print(f"\n  Summary: avg_train={avg_train:.6f}")
    
    # Final summary
    print("\n" + "=" * 70)
    print("FINAL SUMMARY")
    print("=" * 70)
    
    train_energies = [np.mean([r['energy'] for r in res['train']]) for res in all_results]
    
    perfect = sum(1 for e in train_energies if e < 0.001)
    near = sum(1 for e in train_energies if 0.001 <= e < 0.01)
    partial = sum(1 for e in train_energies if 0.01 <= e < 0.5)
    failed = sum(1 for e in train_energies if e >= 0.5)
    
    print(f"Tasks: {len(all_results)}")
    print(f"  PERFECT      (< 0.001):  {perfect}")
    print(f"  NEAR-PERFECT (< 0.01):   {near}")
    print(f"  PARTIAL      (< 0.5):    {partial}")
    print(f"  FAILED       (>= 0.5):   {failed}")
    print(f"  Average energy: {np.mean(train_energies):.6f}")
    
    print(f"\n  Phase 3 baseline: 0 perfect, 8 partial")
    print(f"  Phase 5 result:   {perfect} perfect, {near} near-perfect, {partial} partial")
    
    if perfect > 0:
        print(f"\n  🎉 BREAKTHROUGH: {perfect} task(s) PERFECTLY SOLVED!")
    
    # Show details for near-misses
    print("\n  Detailed results:")
    for res, e in sorted(zip(all_results, train_energies), key=lambda x: x[1]):
        if e < 0.2:
            progs = [r['program'] for r in res['train']]
            status = "[PERFECT]" if e < 0.001 else ("[NEAR]" if e < 0.01 else "[PARTIAL]")
            prog_str = progs[0][:50] if len(progs[0]) > 50 else progs[0]
            print(f"    {status} {res['task_id']}: E={e:.4f}, prog={prog_str}")
    
    return all_results


def main():
    config = ARCPhase5Config()
    paths = ["data/arc/training", "C:/Lean4 Projects/data/arc/training"]
    arc_path = next((p for p in paths if Path(p).exists()), None)
    
    if arc_path:
        return run_evaluation(arc_path, config, num_tasks=10)
    else:
        print("ARC data not found!")
        return []


if __name__ == "__main__":
    main()
