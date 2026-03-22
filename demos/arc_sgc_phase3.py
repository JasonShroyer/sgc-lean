"""
ARC-SGC Phase 3: The Sheaf of Programs

THEORETICAL UPGRADE:
- Phase 1: Sheaf over pixel grid
- Phase 2: Sheaf over object graph  
- Phase 3: **Program Space itself is a Sheaf**

KEY INSIGHT:
A "Program" is a GLOBAL SECTION of a sheaf defined over the input grid.
Most ARC tasks are NOT solvable by a single global rule.
They are solvable by GLUING LOCAL SECTIONS:
  - Region A: "Move Right"
  - Region B: "Stay Still"
  
The solution is a collection of local rules that AGREE ON OVERLAPS.

IMPLEMENTATION:
1. Object-Specific DSL: map(function, object_mask)
2. Gluing Solver: decompose → focus → glue
3. Pattern Primitives: detect_pattern, tile_pattern

REFERENCES:
- SGC.Renormalization.lean: Coarse-graining theory
- Sheaf theory: Global sections from local sections via gluing
"""

import torch
import torch.nn.functional as F
from dataclasses import dataclass, field
from typing import List, Tuple, Dict, Optional, Set, Any, Callable
from collections import deque
from abc import ABC, abstractmethod
import numpy as np
import json
from pathlib import Path
import heapq
from copy import deepcopy


# =============================================================================
# CONFIGURATION
# =============================================================================

@dataclass
class ARCPhase3Config:
    """Configuration for Phase 3: Sheaf of Programs."""
    
    max_grid_size: int = 30
    num_colors: int = 10
    background_color: int = 0
    
    # Object detection
    min_object_size: int = 1
    max_objects: int = 50
    
    # Gluing solver
    max_search_depth: int = 4
    max_candidates: int = 25
    energy_threshold: float = 0.001  # Stricter for perfect solve
    local_energy_threshold: float = 0.01  # For declaring object "solved"
    max_gluing_iterations: int = 8  # Max rounds of decompose-focus-glue
    
    device: str = 'cuda' if torch.cuda.is_available() else 'cpu'


# =============================================================================
# GRID AND OBJECT STRUCTURES (from Phase 2)
# =============================================================================

@dataclass
class ARCGrid:
    """ARC grid as tensor."""
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
        train = [
            ARCExample(
                input_grid=ARCGrid.from_list(ex['input'], device),
                output_grid=ARCGrid.from_list(ex.get('output', ex['input']), device)
            )
            for ex in data['train']
        ]
        test = [
            ARCExample(
                input_grid=ARCGrid.from_list(ex['input'], device),
                output_grid=ARCGrid.from_list(ex.get('output', ex['input']), device)
            )
            for ex in data['test']
        ]
        return cls(task_id=task_id, train_examples=train, test_examples=test)


def load_arc_tasks(data_path: str, device: str = 'cpu', limit: int = None) -> List[ARCTask]:
    """Load ARC tasks from directory."""
    tasks = []
    path = Path(data_path)
    if not path.exists():
        return tasks
    
    json_files = sorted(path.glob("*.json"))
    if limit:
        json_files = json_files[:limit]
    
    for json_file in json_files:
        try:
            with open(json_file, 'r') as f:
                data = json.load(f)
            task = ARCTask.from_json(json_file.stem, data, device)
            tasks.append(task)
        except Exception as e:
            print(f"Error loading {json_file}: {e}")
    
    return tasks


# =============================================================================
# OBJECT DETECTION
# =============================================================================

@dataclass
class ARCObject:
    """A detected object (connected component)."""
    object_id: int
    color: int
    pixels: List[Tuple[int, int]]
    
    @property
    def mass(self) -> int:
        return len(self.pixels)
    
    @property
    def centroid(self) -> Tuple[float, float]:
        if not self.pixels:
            return (0.0, 0.0)
        rows = [p[0] for p in self.pixels]
        cols = [p[1] for p in self.pixels]
        return (sum(rows) / len(rows), sum(cols) / len(cols))
    
    @property
    def bbox(self) -> Tuple[int, int, int, int]:
        """(min_row, min_col, max_row, max_col)"""
        if not self.pixels:
            return (0, 0, 0, 0)
        rows = [p[0] for p in self.pixels]
        cols = [p[1] for p in self.pixels]
        return (min(rows), min(cols), max(rows), max(cols))
    
    def get_mask(self, H: int, W: int, device: str = 'cpu') -> torch.Tensor:
        """Get binary mask for this object."""
        mask = torch.zeros(H, W, dtype=torch.bool, device=device)
        for r, c in self.pixels:
            if 0 <= r < H and 0 <= c < W:
                mask[r, c] = True
        return mask


def detect_objects(grid: ARCGrid, config: ARCPhase3Config) -> List[ARCObject]:
    """Detect connected components via flood-fill."""
    grid_np = grid.to_numpy()
    H, W = grid_np.shape
    visited = np.zeros((H, W), dtype=bool)
    objects = []
    object_id = 0
    
    for r in range(H):
        for c in range(W):
            if visited[r, c]:
                continue
            
            color = grid_np[r, c]
            pixels = []
            queue = deque([(r, c)])
            visited[r, c] = True
            
            while queue:
                cr, cc = queue.popleft()
                pixels.append((cr, cc))
                
                for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                    nr, nc = cr + dr, cc + dc
                    if 0 <= nr < H and 0 <= nc < W and not visited[nr, nc]:
                        if grid_np[nr, nc] == color:
                            visited[nr, nc] = True
                            queue.append((nr, nc))
            
            if len(pixels) >= config.min_object_size:
                objects.append(ARCObject(
                    object_id=object_id,
                    color=int(color),
                    pixels=pixels
                ))
                object_id += 1
                
                if object_id >= config.max_objects:
                    return objects
    
    return objects


# =============================================================================
# TASK 1: OBJECT-SPECIFIC DSL
# =============================================================================

class LocalDSLPrimitive(ABC):
    """
    DSL primitive that can operate on SPECIFIC OBJECTS via masks.
    
    This is the key upgrade: from global f(grid) to local f(grid, mask).
    """
    
    @abstractmethod
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        """Apply to entire grid (backward compatible)."""
        pass
    
    @abstractmethod
    def apply_local(self, grid: ARCGrid, mask: torch.Tensor) -> ARCGrid:
        """Apply only to pixels in mask, preserve others."""
        pass
    
    @abstractmethod
    def signature(self) -> str:
        pass
    
    def priority_score(self, delta: 'InvariantDelta') -> float:
        return 0.5  # Default


class Identity(LocalDSLPrimitive):
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        return grid.clone()
    
    def apply_local(self, grid: ARCGrid, mask: torch.Tensor) -> ARCGrid:
        return grid.clone()
    
    def signature(self) -> str:
        return "identity"
    
    def priority_score(self, delta: 'InvariantDelta') -> float:
        return 0.0


class Rotate90(LocalDSLPrimitive):
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        return ARCGrid(torch.rot90(grid.data, k=-1))
    
    def apply_local(self, grid: ARCGrid, mask: torch.Tensor) -> ARCGrid:
        # For local rotation, extract bbox, rotate, paste back
        result = grid.clone()
        if not mask.any():
            return result
        
        rows = mask.any(dim=1).nonzero().flatten()
        cols = mask.any(dim=0).nonzero().flatten()
        if len(rows) == 0 or len(cols) == 0:
            return result
        
        r_min, r_max = rows[0].item(), rows[-1].item() + 1
        c_min, c_max = cols[0].item(), cols[-1].item() + 1
        
        # Extract, rotate, paste (only if square)
        sub = grid.data[r_min:r_max, c_min:c_max].clone()
        if sub.shape[0] == sub.shape[1]:
            rotated = torch.rot90(sub, k=-1)
            result.data[r_min:r_max, c_min:c_max] = rotated
        
        return result
    
    def signature(self) -> str:
        return "rotate_90"
    
    def priority_score(self, delta: 'InvariantDelta') -> float:
        if delta.mass_conserved and not delta.colors_changed:
            return 0.8
        return 0.2


class Rotate180(LocalDSLPrimitive):
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        return ARCGrid(torch.rot90(grid.data, k=2))
    
    def apply_local(self, grid: ARCGrid, mask: torch.Tensor) -> ARCGrid:
        result = grid.clone()
        if not mask.any():
            return result
        
        rows = mask.any(dim=1).nonzero().flatten()
        cols = mask.any(dim=0).nonzero().flatten()
        if len(rows) == 0 or len(cols) == 0:
            return result
        
        r_min, r_max = rows[0].item(), rows[-1].item() + 1
        c_min, c_max = cols[0].item(), cols[-1].item() + 1
        
        sub = grid.data[r_min:r_max, c_min:c_max].clone()
        rotated = torch.rot90(sub, k=2)
        result.data[r_min:r_max, c_min:c_max] = rotated
        
        return result
    
    def signature(self) -> str:
        return "rotate_180"
    
    def priority_score(self, delta: 'InvariantDelta') -> float:
        if delta.mass_conserved and not delta.colors_changed:
            return 0.7
        return 0.2


class FlipHorizontal(LocalDSLPrimitive):
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        return ARCGrid(torch.flip(grid.data, dims=[1]))
    
    def apply_local(self, grid: ARCGrid, mask: torch.Tensor) -> ARCGrid:
        result = grid.clone()
        if not mask.any():
            return result
        
        rows = mask.any(dim=1).nonzero().flatten()
        cols = mask.any(dim=0).nonzero().flatten()
        if len(rows) == 0 or len(cols) == 0:
            return result
        
        r_min, r_max = rows[0].item(), rows[-1].item() + 1
        c_min, c_max = cols[0].item(), cols[-1].item() + 1
        
        sub = grid.data[r_min:r_max, c_min:c_max].clone()
        flipped = torch.flip(sub, dims=[1])
        result.data[r_min:r_max, c_min:c_max] = flipped
        
        return result
    
    def signature(self) -> str:
        return "flip_h"
    
    def priority_score(self, delta: 'InvariantDelta') -> float:
        if delta.symmetry_gained_h:
            return 0.9
        if delta.mass_conserved:
            return 0.6
        return 0.2


class FlipVertical(LocalDSLPrimitive):
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        return ARCGrid(torch.flip(grid.data, dims=[0]))
    
    def apply_local(self, grid: ARCGrid, mask: torch.Tensor) -> ARCGrid:
        result = grid.clone()
        if not mask.any():
            return result
        
        rows = mask.any(dim=1).nonzero().flatten()
        cols = mask.any(dim=0).nonzero().flatten()
        if len(rows) == 0 or len(cols) == 0:
            return result
        
        r_min, r_max = rows[0].item(), rows[-1].item() + 1
        c_min, c_max = cols[0].item(), cols[-1].item() + 1
        
        sub = grid.data[r_min:r_max, c_min:c_max].clone()
        flipped = torch.flip(sub, dims=[0])
        result.data[r_min:r_max, c_min:c_max] = flipped
        
        return result
    
    def signature(self) -> str:
        return "flip_v"
    
    def priority_score(self, delta: 'InvariantDelta') -> float:
        if delta.symmetry_gained_v:
            return 0.9
        if delta.mass_conserved:
            return 0.6
        return 0.2


class ColorSwap(LocalDSLPrimitive):
    def __init__(self, color_a: int, color_b: int):
        self.color_a = color_a
        self.color_b = color_b
    
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        data = grid.data.clone()
        mask_a = (data == self.color_a)
        mask_b = (data == self.color_b)
        data[mask_a] = self.color_b
        data[mask_b] = self.color_a
        return ARCGrid(data)
    
    def apply_local(self, grid: ARCGrid, mask: torch.Tensor) -> ARCGrid:
        data = grid.data.clone()
        local_a = (data == self.color_a) & mask
        local_b = (data == self.color_b) & mask
        data[local_a] = self.color_b
        data[local_b] = self.color_a
        return ARCGrid(data)
    
    def signature(self) -> str:
        return f"swap_{self.color_a}_{self.color_b}"
    
    def priority_score(self, delta: 'InvariantDelta') -> float:
        if delta.likely_color_swap:
            if (self.color_a, self.color_b) in delta.swap_pairs or \
               (self.color_b, self.color_a) in delta.swap_pairs:
                return 0.95
            return 0.8
        if delta.histogram_conserved and delta.mass_conserved:
            return 0.6
        return 0.2


class Recolor(LocalDSLPrimitive):
    """Change all pixels of one color to another (within mask)."""
    def __init__(self, from_color: int, to_color: int):
        self.from_color = from_color
        self.to_color = to_color
    
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        data = grid.data.clone()
        data[data == self.from_color] = self.to_color
        return ARCGrid(data)
    
    def apply_local(self, grid: ARCGrid, mask: torch.Tensor) -> ARCGrid:
        data = grid.data.clone()
        target = (data == self.from_color) & mask
        data[target] = self.to_color
        return ARCGrid(data)
    
    def signature(self) -> str:
        return f"recolor_{self.from_color}_to_{self.to_color}"
    
    def priority_score(self, delta: 'InvariantDelta') -> float:
        if delta.colors_changed:
            return 0.7
        return 0.2


class Shift(LocalDSLPrimitive):
    def __init__(self, dr: int, dc: int, bg: int = 0):
        self.dr = dr
        self.dc = dc
        self.bg = bg
    
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        data = grid.data.clone()
        H, W = data.shape
        result = torch.full_like(data, self.bg)
        
        src_r_start = max(0, -self.dr)
        src_r_end = min(H, H - self.dr)
        src_c_start = max(0, -self.dc)
        src_c_end = min(W, W - self.dc)
        
        tgt_r_start = max(0, self.dr)
        tgt_c_start = max(0, self.dc)
        
        if src_r_end > src_r_start and src_c_end > src_c_start:
            result[tgt_r_start:tgt_r_start+(src_r_end-src_r_start),
                   tgt_c_start:tgt_c_start+(src_c_end-src_c_start)] = \
                data[src_r_start:src_r_end, src_c_start:src_c_end]
        
        return ARCGrid(result)
    
    def apply_local(self, grid: ARCGrid, mask: torch.Tensor) -> ARCGrid:
        """Shift only masked pixels, fill vacated with background."""
        data = grid.data.clone()
        H, W = data.shape
        
        # Get masked pixels
        masked_coords = mask.nonzero()
        if len(masked_coords) == 0:
            return ARCGrid(data)
        
        # Clear original positions
        for coord in masked_coords:
            data[coord[0], coord[1]] = self.bg
        
        # Place at new positions
        original = grid.data
        for coord in masked_coords:
            nr, nc = coord[0].item() + self.dr, coord[1].item() + self.dc
            if 0 <= nr < H and 0 <= nc < W:
                data[nr, nc] = original[coord[0], coord[1]]
        
        return ARCGrid(data)
    
    def signature(self) -> str:
        return f"shift_{self.dr}_{self.dc}"
    
    def priority_score(self, delta: 'InvariantDelta') -> float:
        if delta.mass_conserved and not delta.colors_changed:
            return 0.5
        return 0.2


class FillMask(LocalDSLPrimitive):
    """Fill masked region with a specific color."""
    def __init__(self, color: int):
        self.color = color
    
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        data = grid.data.clone()
        data[:] = self.color
        return ARCGrid(data)
    
    def apply_local(self, grid: ARCGrid, mask: torch.Tensor) -> ARCGrid:
        data = grid.data.clone()
        data[mask] = self.color
        return ARCGrid(data)
    
    def signature(self) -> str:
        return f"fill_{self.color}"
    
    def priority_score(self, delta: 'InvariantDelta') -> float:
        if delta.colors_changed:
            return 0.4
        return 0.1


# =============================================================================
# CONDITIONAL/COMPOSED OPERATIONS
# =============================================================================

@dataclass
class ObjectSelector:
    """Selects objects based on criteria."""
    criteria: str  # 'color', 'size', 'position', 'all'
    value: Any = None  # e.g., color=3, size='large'
    
    def select(self, objects: List[ARCObject], grid: ARCGrid) -> List[ARCObject]:
        if self.criteria == 'all':
            return objects
        elif self.criteria == 'color':
            return [o for o in objects if o.color == self.value]
        elif self.criteria == 'not_color':
            return [o for o in objects if o.color != self.value]
        elif self.criteria == 'size_above':
            return [o for o in objects if o.mass > self.value]
        elif self.criteria == 'size_below':
            return [o for o in objects if o.mass < self.value]
        elif self.criteria == 'background':
            return [o for o in objects if o.color == 0]
        elif self.criteria == 'foreground':
            return [o for o in objects if o.color != 0]
        return objects
    
    def signature(self) -> str:
        if self.criteria == 'all':
            return "all"
        return f"{self.criteria}={self.value}"


class MapOp(LocalDSLPrimitive):
    """
    Map a function over selected objects.
    
    This is the KEY PRIMITIVE for local sections:
    map(rotate_90, color=red) applies rotate_90 only to red objects.
    """
    
    def __init__(self, op: LocalDSLPrimitive, selector: ObjectSelector, config: ARCPhase3Config):
        self.op = op
        self.selector = selector
        self.config = config
    
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        # Detect objects, select, apply to each
        objects = detect_objects(grid, self.config)
        selected = self.selector.select(objects, grid)
        
        if not selected:
            return grid.clone()
        
        # Build combined mask
        H, W = grid.height, grid.width
        mask = torch.zeros(H, W, dtype=torch.bool, device=grid.data.device)
        for obj in selected:
            obj_mask = obj.get_mask(H, W, grid.data.device)
            mask = mask | obj_mask
        
        return self.op.apply_local(grid, mask)
    
    def apply_local(self, grid: ARCGrid, outer_mask: torch.Tensor) -> ARCGrid:
        # Apply within outer_mask constraint
        objects = detect_objects(grid, self.config)
        selected = self.selector.select(objects, grid)
        
        if not selected:
            return grid.clone()
        
        H, W = grid.height, grid.width
        mask = torch.zeros(H, W, dtype=torch.bool, device=grid.data.device)
        for obj in selected:
            obj_mask = obj.get_mask(H, W, grid.data.device)
            mask = mask | (obj_mask & outer_mask)
        
        return self.op.apply_local(grid, mask)
    
    def signature(self) -> str:
        return f"map({self.op.signature()}, {self.selector.signature()})"
    
    def priority_score(self, delta: 'InvariantDelta') -> float:
        return self.op.priority_score(delta) * 0.9


class ConditionalOp(LocalDSLPrimitive):
    """
    Conditional: If selector matches -> op1, else -> op2.
    
    This implements the GLUING of local sections:
    ConditionalOp(rotate_90, identity, color=red)
    = "Rotate red objects, leave others unchanged"
    """
    
    def __init__(self, op_true: LocalDSLPrimitive, op_false: LocalDSLPrimitive, 
                 selector: ObjectSelector, config: ARCPhase3Config):
        self.op_true = op_true
        self.op_false = op_false
        self.selector = selector
        self.config = config
    
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        objects = detect_objects(grid, self.config)
        selected = self.selector.select(objects, grid)
        not_selected = [o for o in objects if o not in selected]
        
        H, W = grid.height, grid.width
        result = grid.clone()
        
        # Apply op_true to selected
        if selected:
            mask_true = torch.zeros(H, W, dtype=torch.bool, device=grid.data.device)
            for obj in selected:
                mask_true = mask_true | obj.get_mask(H, W, grid.data.device)
            result = self.op_true.apply_local(result, mask_true)
        
        # Apply op_false to not_selected
        if not_selected:
            mask_false = torch.zeros(H, W, dtype=torch.bool, device=grid.data.device)
            for obj in not_selected:
                mask_false = mask_false | obj.get_mask(H, W, grid.data.device)
            result = self.op_false.apply_local(result, mask_false)
        
        return result
    
    def apply_local(self, grid: ARCGrid, outer_mask: torch.Tensor) -> ARCGrid:
        return self.apply_global(grid)  # For now, ignore outer_mask
    
    def signature(self) -> str:
        return f"if({self.selector.signature()}) then {self.op_true.signature()} else {self.op_false.signature()}"
    
    def priority_score(self, delta: 'InvariantDelta') -> float:
        return max(self.op_true.priority_score(delta), self.op_false.priority_score(delta))


class ComposedOp(LocalDSLPrimitive):
    """Composition of multiple operations."""
    
    def __init__(self, ops: List[LocalDSLPrimitive]):
        self.ops = ops
    
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        result = grid
        for op in self.ops:
            result = op.apply_global(result)
        return result
    
    def apply_local(self, grid: ARCGrid, mask: torch.Tensor) -> ARCGrid:
        result = grid
        for op in self.ops:
            result = op.apply_local(result, mask)
        return result
    
    def signature(self) -> str:
        return " -> ".join(op.signature() for op in self.ops)
    
    def priority_score(self, delta: 'InvariantDelta') -> float:
        return max(op.priority_score(delta) for op in self.ops) if self.ops else 0.0


# =============================================================================
# TASK 3: PATTERN PRIMITIVES
# =============================================================================

def detect_pattern(grid: ARCGrid, min_size: int = 2) -> Optional[Tuple[ARCGrid, int, int]]:
    """
    Detect repeating unit cell (smallest translational symmetry).
    
    Returns: (unit_cell, period_h, period_w) or None if no pattern found.
    """
    data = grid.to_numpy()
    H, W = data.shape
    
    # Try different period sizes
    for ph in range(min_size, H // 2 + 1):
        for pw in range(min_size, W // 2 + 1):
            if H % ph == 0 and W % pw == 0:
                # Check if grid is tiled by this period
                unit = data[:ph, :pw]
                is_tiled = True
                
                for i in range(0, H, ph):
                    for j in range(0, W, pw):
                        if not np.array_equal(data[i:i+ph, j:j+pw], unit):
                            is_tiled = False
                            break
                    if not is_tiled:
                        break
                
                if is_tiled:
                    unit_grid = ARCGrid(torch.tensor(unit, dtype=torch.long, device=grid.data.device))
                    return (unit_grid, ph, pw)
    
    return None


class TilePattern(LocalDSLPrimitive):
    """Tile a pattern across the grid."""
    
    def __init__(self, pattern: ARCGrid):
        self.pattern = pattern
    
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        H, W = grid.height, grid.width
        ph, pw = self.pattern.height, self.pattern.width
        
        result = torch.zeros(H, W, dtype=torch.long, device=grid.data.device)
        
        for i in range(0, H, ph):
            for j in range(0, W, pw):
                h_end = min(i + ph, H)
                w_end = min(j + pw, W)
                result[i:h_end, j:w_end] = self.pattern.data[:h_end-i, :w_end-j]
        
        return ARCGrid(result)
    
    def apply_local(self, grid: ARCGrid, mask: torch.Tensor) -> ARCGrid:
        tiled = self.apply_global(grid)
        result = grid.data.clone()
        result[mask] = tiled.data[mask]
        return ARCGrid(result)
    
    def signature(self) -> str:
        return f"tile_{self.pattern.height}x{self.pattern.width}"
    
    def priority_score(self, delta: 'InvariantDelta') -> float:
        return 0.3


class ExtractAndTile(LocalDSLPrimitive):
    """Extract a subregion and tile it to fill the output."""
    
    def __init__(self, r1: int, c1: int, r2: int, c2: int):
        self.r1, self.c1 = r1, c1
        self.r2, self.c2 = r2, c2
    
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        pattern = grid.data[self.r1:self.r2, self.c1:self.c2].clone()
        pattern_grid = ARCGrid(pattern)
        return TilePattern(pattern_grid).apply_global(grid)
    
    def apply_local(self, grid: ARCGrid, mask: torch.Tensor) -> ARCGrid:
        return self.apply_global(grid)
    
    def signature(self) -> str:
        return f"extract_tile_{self.r1}_{self.c1}_{self.r2}_{self.c2}"
    
    def priority_score(self, delta: 'InvariantDelta') -> float:
        return 0.3


class Crop(LocalDSLPrimitive):
    """Crop to bounding box of non-background."""
    
    def __init__(self, bg: int = 0):
        self.bg = bg
    
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        data = grid.data
        mask = (data != self.bg)
        
        if not mask.any():
            return grid.clone()
        
        rows = mask.any(dim=1)
        cols = mask.any(dim=0)
        
        r_min = rows.nonzero()[0].item()
        r_max = rows.nonzero()[-1].item() + 1
        c_min = cols.nonzero()[0].item()
        c_max = cols.nonzero()[-1].item() + 1
        
        return ARCGrid(data[r_min:r_max, c_min:c_max].clone())
    
    def apply_local(self, grid: ARCGrid, mask: torch.Tensor) -> ARCGrid:
        return self.apply_global(grid)
    
    def signature(self) -> str:
        return "crop"
    
    def priority_score(self, delta: 'InvariantDelta') -> float:
        if not delta.size_conserved:
            return 0.7
        return 0.2


class Upscale(LocalDSLPrimitive):
    """Upscale by integer factor."""
    
    def __init__(self, factor: int):
        self.factor = factor
    
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        data = grid.data
        result = data.repeat_interleave(self.factor, dim=0).repeat_interleave(self.factor, dim=1)
        return ARCGrid(result)
    
    def apply_local(self, grid: ARCGrid, mask: torch.Tensor) -> ARCGrid:
        return self.apply_global(grid)
    
    def signature(self) -> str:
        return f"upscale_{self.factor}"
    
    def priority_score(self, delta: 'InvariantDelta') -> float:
        if delta.size_change[0] > 0 and delta.size_change[1] > 0:
            return 0.6
        return 0.1


# =============================================================================
# INVARIANT COMPUTATION
# =============================================================================

@dataclass
class InvariantDelta:
    """Difference in invariants between input and output."""
    mass_change: int
    mass_conserved: bool
    colors_added: Set[int]
    colors_removed: Set[int]
    colors_changed: bool
    histogram_conserved: bool
    likely_color_swap: bool
    swap_pairs: List[Tuple[int, int]]
    object_count_change: int
    objects_conserved: bool
    size_change: Tuple[int, int]
    size_conserved: bool
    symmetry_gained_h: bool
    symmetry_gained_v: bool


def compute_invariant_delta(
    input_grid: ARCGrid,
    output_grid: ARCGrid,
    config: ARCPhase3Config
) -> InvariantDelta:
    """Compute invariant delta between input and output."""
    in_np = input_grid.to_numpy()
    out_np = output_grid.to_numpy()
    
    # Histograms
    in_hist = {}
    out_hist = {}
    for c in range(config.num_colors):
        in_count = int((in_np == c).sum())
        out_count = int((out_np == c).sum())
        if in_count > 0:
            in_hist[c] = in_count
        if out_count > 0:
            out_hist[c] = out_count
    
    # Mass
    bg = config.background_color
    in_mass = int((in_np != bg).sum())
    out_mass = int((out_np != bg).sum())
    mass_change = out_mass - in_mass
    
    # Colors
    in_colors = set(in_hist.keys()) - {bg}
    out_colors = set(out_hist.keys()) - {bg}
    colors_added = out_colors - in_colors
    colors_removed = in_colors - out_colors
    
    # Histogram analysis
    histogram_conserved = (in_hist == out_hist)
    in_counts = sorted(in_hist.values())
    out_counts = sorted(out_hist.values())
    histogram_is_permutation = (in_counts == out_counts)
    
    # Color swap detection
    swap_pairs = []
    likely_color_swap = False
    if histogram_is_permutation and input_grid.shape == output_grid.shape:
        if not torch.equal(input_grid.data, output_grid.data):
            for c1 in in_hist:
                for c2 in in_hist:
                    if c1 < c2:
                        in_c1 = in_hist.get(c1, 0)
                        in_c2 = in_hist.get(c2, 0)
                        out_c1 = out_hist.get(c1, 0)
                        out_c2 = out_hist.get(c2, 0)
                        if in_c1 == out_c2 and in_c2 == out_c1 and in_c1 != in_c2:
                            swap_pairs.append((c1, c2))
                            likely_color_swap = True
    
    # Objects
    in_objects = detect_objects(input_grid, config)
    out_objects = detect_objects(output_grid, config)
    obj_change = len(out_objects) - len(in_objects)
    
    # Size
    size_change = (output_grid.height - input_grid.height, 
                   output_grid.width - input_grid.width)
    
    # Symmetry
    sym_h_in = np.allclose(in_np, np.flip(in_np, axis=1))
    sym_h_out = np.allclose(out_np, np.flip(out_np, axis=1))
    sym_v_in = np.allclose(in_np, np.flip(in_np, axis=0))
    sym_v_out = np.allclose(out_np, np.flip(out_np, axis=0))
    
    return InvariantDelta(
        mass_change=mass_change,
        mass_conserved=(abs(mass_change) < 3),
        colors_added=colors_added,
        colors_removed=colors_removed,
        colors_changed=(len(colors_added) > 0 or len(colors_removed) > 0),
        histogram_conserved=histogram_conserved,
        likely_color_swap=likely_color_swap,
        swap_pairs=swap_pairs,
        object_count_change=obj_change,
        objects_conserved=(obj_change == 0),
        size_change=size_change,
        size_conserved=(size_change == (0, 0)),
        symmetry_gained_h=(sym_h_out and not sym_h_in),
        symmetry_gained_v=(sym_v_out and not sym_v_in)
    )


# =============================================================================
# TASK 2: GLUING SOLVER
# =============================================================================

def build_dsl_library(config: ARCPhase3Config) -> List[LocalDSLPrimitive]:
    """Build comprehensive DSL library."""
    ops: List[LocalDSLPrimitive] = [
        Identity(),
        Rotate90(),
        Rotate180(),
        FlipHorizontal(),
        FlipVertical(),
        Crop(),
    ]
    
    # Color operations
    for a in range(config.num_colors):
        for b in range(a + 1, config.num_colors):
            ops.append(ColorSwap(a, b))
    
    # Recolor operations
    for a in range(config.num_colors):
        for b in range(config.num_colors):
            if a != b:
                ops.append(Recolor(a, b))
    
    # Shifts
    for dr in [-1, 0, 1]:
        for dc in [-1, 0, 1]:
            if dr != 0 or dc != 0:
                ops.append(Shift(dr, dc))
    
    # Fill
    for c in range(config.num_colors):
        ops.append(FillMask(c))
    
    # Upscale
    for f in [2, 3]:
        ops.append(Upscale(f))
    
    return ops


def build_map_ops(base_ops: List[LocalDSLPrimitive], config: ARCPhase3Config) -> List[LocalDSLPrimitive]:
    """Build map operations for object-specific DSL."""
    map_ops = []
    
    # Selectors
    selectors = [
        ObjectSelector('foreground'),
        ObjectSelector('background'),
    ]
    for c in range(1, config.num_colors):
        selectors.append(ObjectSelector('color', c))
        selectors.append(ObjectSelector('not_color', c))
    
    # Only map key operations to avoid explosion
    key_ops = [op for op in base_ops if isinstance(op, (Rotate90, FlipHorizontal, FlipVertical, Shift))]
    
    for op in key_ops[:10]:
        for sel in selectors[:6]:
            map_ops.append(MapOp(op, sel, config))
    
    return map_ops


@dataclass
class ObjectDefect:
    """Defect (energy) for a single object."""
    object_id: int
    color: int
    defect: float  # How "wrong" this object is
    solved: bool


def compute_object_defects(
    current: ARCGrid, 
    target: ARCGrid,
    config: ARCPhase3Config
) -> List[ObjectDefect]:
    """Compute per-object defect to identify solved/unsolved regions."""
    if current.shape != target.shape:
        return []
    
    objects = detect_objects(current, config)
    defects = []
    
    for obj in objects:
        mask = obj.get_mask(current.height, current.width, current.data.device)
        
        # Count mismatches within this object's region
        mismatches = ((current.data != target.data) & mask).sum().item()
        total = mask.sum().item()
        
        if total > 0:
            defect = mismatches / total
        else:
            defect = 0.0
        
        defects.append(ObjectDefect(
            object_id=obj.object_id,
            color=obj.color,
            defect=defect,
            solved=(defect < config.local_energy_threshold)
        ))
    
    return defects


class GluingSolver:
    """
    The Gluing Solver: constructs global sections from local sections.
    
    Algorithm:
    1. DECOMPOSE: Identify solved objects (defect ≈ 0) and unsolved objects
    2. FOCUS: Search for operations that fix unsolved objects
    3. GLUE: Combine local solutions into ConditionalOp
    4. ITERATE: Repeat until all objects solved or max iterations
    """
    
    def __init__(self, config: ARCPhase3Config):
        self.config = config
        self.base_ops = build_dsl_library(config)
        self.map_ops = build_map_ops(self.base_ops, config)
        self.all_ops = self.base_ops + self.map_ops
        print(f"   DSL: {len(self.base_ops)} base + {len(self.map_ops)} map = {len(self.all_ops)} total")
    
    def compute_energy(self, pred: ARCGrid, target: ARCGrid) -> float:
        """Global energy (mismatch ratio)."""
        if pred.shape != target.shape:
            return 1000.0 + abs(pred.height - target.height) + abs(pred.width - target.width)
        mismatch = (pred.data != target.data).float().sum().item()
        return mismatch / target.data.numel()
    
    def find_best_global_op(
        self,
        current: ARCGrid,
        target: ARCGrid,
        delta: InvariantDelta,
        depth: int = 0
    ) -> Tuple[Optional[LocalDSLPrimitive], float]:
        """Find best global operation via priority-guided search."""
        best_op = None
        best_energy = self.compute_energy(current, target)
        
        if best_energy < self.config.energy_threshold:
            return None, best_energy
        
        # Rank operations
        ranked = [(op.priority_score(delta), op) for op in self.all_ops]
        ranked.sort(key=lambda x: -x[0])
        
        for priority, op in ranked[:self.config.max_candidates]:
            if priority < 0.1:
                continue
            
            try:
                result = op.apply_global(current)
                energy = self.compute_energy(result, target)
                
                if energy < best_energy:
                    best_energy = energy
                    best_op = op
                    
                    if energy < self.config.energy_threshold:
                        return best_op, energy
            except Exception:
                continue
        
        # Try compositions if still not solved
        if depth < self.config.max_search_depth and best_energy > self.config.energy_threshold:
            if best_op is not None:
                intermediate = best_op.apply_global(current)
                sub_op, sub_energy = self.find_best_global_op(
                    intermediate, target, delta, depth + 1
                )
                if sub_op is not None and sub_energy < best_energy:
                    best_op = ComposedOp([best_op, sub_op])
                    best_energy = sub_energy
        
        return best_op, best_energy
    
    def find_local_solution(
        self,
        current: ARCGrid,
        target: ARCGrid,
        unsolved_objects: List[ARCObject],
        delta: InvariantDelta
    ) -> Tuple[Optional[LocalDSLPrimitive], float]:
        """Find operation that fixes unsolved objects."""
        best_op = None
        best_energy = self.compute_energy(current, target)
        
        # Build mask for unsolved objects
        H, W = current.height, current.width
        unsolved_mask = torch.zeros(H, W, dtype=torch.bool, device=current.data.device)
        for obj in unsolved_objects:
            unsolved_mask = unsolved_mask | obj.get_mask(H, W, current.data.device)
        
        # Try operations focused on unsolved region
        for op in self.all_ops:
            try:
                # Apply locally to unsolved region
                result = op.apply_local(current, unsolved_mask)
                energy = self.compute_energy(result, target)
                
                if energy < best_energy:
                    best_energy = energy
                    # Wrap in map to only affect unsolved objects
                    if unsolved_objects:
                        colors = set(obj.color for obj in unsolved_objects)
                        if len(colors) == 1:
                            color = list(colors)[0]
                            best_op = MapOp(op, ObjectSelector('color', color), self.config)
                        else:
                            best_op = op
                    else:
                        best_op = op
            except Exception:
                continue
        
        return best_op, best_energy
    
    def solve(
        self,
        input_grid: ARCGrid,
        target_grid: ARCGrid,
        verbose: bool = False
    ) -> Tuple[Optional[LocalDSLPrimitive], float]:
        """
        Main solve loop with gluing.
        
        Returns: (program, final_energy)
        """
        delta = compute_invariant_delta(input_grid, target_grid, self.config)
        
        if verbose:
            print(f"   Delta: mass={delta.mass_change}, colors_changed={delta.colors_changed}, size={delta.size_change}")
        
        current = input_grid
        program_parts: List[LocalDSLPrimitive] = []
        best_seen_energy = self.compute_energy(current, target_grid)
        best_seen_state = current
        best_seen_program: List[LocalDSLPrimitive] = []
        
        # Track visited states to prevent oscillation
        visited_hashes: Set[bytes] = set()
        visited_hashes.add(current.data.cpu().numpy().tobytes())
        
        for iteration in range(self.config.max_gluing_iterations):
            energy = self.compute_energy(current, target_grid)
            
            if verbose:
                print(f"   Iteration {iteration + 1}: energy={energy:.4f}")
            
            # Track best state seen
            if energy < best_seen_energy:
                best_seen_energy = energy
                best_seen_state = current.clone()
                best_seen_program = program_parts.copy()
            
            if energy < self.config.energy_threshold:
                if verbose:
                    print(f"   SOLVED!")
                break
            
            # DECOMPOSE: Find solved vs unsolved objects
            defects = compute_object_defects(current, target_grid, self.config)
            solved_objs = [d for d in defects if d.solved]
            unsolved_objs = [d for d in defects if not d.solved]
            
            if verbose:
                print(f"   Objects: {len(solved_objs)} solved, {len(unsolved_objs)} unsolved")
            
            # Strategy 1: Try global operation
            global_op, global_energy = self.find_best_global_op(current, target_grid, delta)
            
            # Strategy 2: Try local operation on unsolved
            local_op, local_energy = None, float('inf')
            if unsolved_objs:
                unsolved_arc_objs = [
                    obj for obj in detect_objects(current, self.config)
                    if any(d.object_id == obj.object_id for d in unsolved_objs if not d.solved)
                ]
                if unsolved_arc_objs:
                    local_op, local_energy = self.find_local_solution(
                        current, target_grid, unsolved_arc_objs, delta
                    )
            
            # Choose better strategy (must improve AND not revisit)
            best_op, best_energy = None, float('inf')
            
            for op, op_energy in [(global_op, global_energy), (local_op, local_energy)]:
                if op is None:
                    continue
                if op_energy >= energy:
                    continue
                    
                # Check if this would create a visited state
                test_result = op.apply_global(current)
                test_hash = test_result.data.cpu().numpy().tobytes()
                
                if test_hash in visited_hashes:
                    continue  # Skip - would cause oscillation
                
                if op_energy < best_energy:
                    best_op = op
                    best_energy = op_energy
            
            if best_op is None:
                if verbose:
                    print(f"   No non-oscillating improvement found")
                break
            
            if verbose:
                print(f"   Applying: {best_op.signature()} -> energy={best_energy:.4f}")
            
            # Apply and continue
            current = best_op.apply_global(current)
            visited_hashes.add(current.data.cpu().numpy().tobytes())
            program_parts.append(best_op)
        
        # Return best seen state (may not be final if we got stuck)
        final_energy = best_seen_energy
        
        if not best_seen_program:
            return Identity(), final_energy
        elif len(best_seen_program) == 1:
            return best_seen_program[0], final_energy
        else:
            return ComposedOp(best_seen_program), final_energy


# =============================================================================
# EVALUATION
# =============================================================================

def evaluate_task(
    solver: GluingSolver,
    task: ARCTask,
    config: ARCPhase3Config,
    verbose: bool = False
) -> Dict[str, Any]:
    """Evaluate on a single task."""
    results = {
        'task_id': task.task_id,
        'train_results': [],
        'test_results': [],
        'programs': []
    }
    
    # Solve each training example
    for i, example in enumerate(task.train_examples):
        if verbose:
            print(f"\n   Train {i + 1}:")
        
        program, energy = solver.solve(
            example.input_grid,
            example.output_grid,
            verbose=verbose
        )
        
        sig = program.signature() if program else "none"
        results['train_results'].append({'energy': energy, 'program': sig})
        results['programs'].append(program)
    
    # Apply to test
    for i, example in enumerate(task.test_examples):
        if results['programs'] and results['programs'][0]:
            pred = results['programs'][0].apply_global(example.input_grid)
            energy = solver.compute_energy(pred, example.output_grid)
        else:
            energy = solver.compute_energy(example.input_grid, example.output_grid)
        
        results['test_results'].append({'energy': energy})
    
    return results


def run_evaluation(data_path: str, config: ARCPhase3Config, num_tasks: int = 10) -> List[Dict]:
    """Run full evaluation."""
    print("=" * 70)
    print("ARC-SGC Phase 3: The Sheaf of Programs (Gluing Solver)")
    print("=" * 70)
    
    # Load tasks
    tasks = load_arc_tasks(data_path, config.device, limit=num_tasks)
    print(f"\nLoaded {len(tasks)} tasks from {data_path}")
    
    if not tasks:
        print("No tasks found!")
        return []
    
    # Build solver
    print("\nBuilding Gluing Solver...")
    solver = GluingSolver(config)
    
    # Evaluate
    all_results = []
    
    for i, task in enumerate(tasks):
        print(f"\n{'='*70}")
        print(f"Task {i+1}/{len(tasks)}: {task.task_id}")
        print(f"  Train: {len(task.train_examples)}, Test: {len(task.test_examples)}")
        
        results = evaluate_task(solver, task, config, verbose=True)
        all_results.append(results)
        
        avg_train = np.mean([r['energy'] for r in results['train_results']])
        programs = [r['program'] for r in results['train_results']]
        
        print(f"\n  Summary:")
        print(f"    Avg train energy: {avg_train:.4f}")
        print(f"    Programs: {programs}")
        
        if results['test_results']:
            avg_test = np.mean([r['energy'] for r in results['test_results']])
            print(f"    Avg test energy: {avg_test:.4f}")
    
    # Final summary
    print("\n" + "=" * 70)
    print("FINAL SUMMARY")
    print("=" * 70)
    
    train_energies = [np.mean([r['energy'] for r in res['train_results']]) for res in all_results]
    
    perfect = sum(1 for e in train_energies if e < 0.001)
    partial = sum(1 for e in train_energies if 0.001 <= e < 0.5)
    failed = sum(1 for e in train_energies if e >= 0.5)
    
    print(f"Tasks: {len(all_results)}")
    print(f"  PERFECT (energy < 0.001): {perfect}")
    print(f"  PARTIAL (energy < 0.5):   {partial}")
    print(f"  FAILED  (energy >= 0.5):  {failed}")
    print(f"  Average energy: {np.mean(train_energies):.4f}")
    
    # Comparison with Phase 2
    print("\n  Phase 2 baseline: 0 perfect, 7 partial")
    print(f"  Phase 3 result:   {perfect} perfect, {partial} partial")
    
    if perfect > 0:
        print(f"\n  🎉 IMPROVEMENT: {perfect} tasks now PERFECTLY SOLVED!")
    
    return all_results


# =============================================================================
# MAIN
# =============================================================================

def main():
    config = ARCPhase3Config()
    
    # Find ARC data
    possible_paths = [
        "data/arc/training",
        "C:/Lean4 Projects/data/arc/training",
    ]
    
    arc_path = None
    for path in possible_paths:
        if Path(path).exists():
            arc_path = path
            break
    
    if arc_path:
        results = run_evaluation(arc_path, config, num_tasks=10)
    else:
        print("ARC data not found!")
        return
    
    return results


if __name__ == "__main__":
    main()
