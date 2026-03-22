"""
ARC-SGC Phase 2: Object-Centric Active Inference

UPGRADE FROM PHASE 1:
- Base Space: Pixel Grid -> Object Graph (connected components)
- Search: Exhaustive -> Invariant-Guided Priority Queue (Proto-Active Inference)
- Scale: Synthetic -> Real ARC Training Data

THEORETICAL BASIS:

1. THE "OBJECT" LIFT (Coarse-Graining / Lumpability):
   - Nodes: Individual objects (connected color regions)
   - Edges: Spatial relationships (touching, aligned, inside)
   - Stalks: Object attributes (color, centroid, mass, bbox)
   - Restriction Maps: DSL operations on object attributes
   
   This is EXACT LUMPABILITY from SGC: we solve at macro-scale first.

2. ACTIVE INFERENCE (Expected Free Energy):
   G(pi) = D_KL[Q(z|pi) || P(z)] + E_Q[ln P(o|z)]
         = Information Gain + Pragmatic Value (Defect)
   
   Instead of exhaustive search, we PREDICT which DSL minimizes defect
   using invariants as heuristics.

3. INVARIANT-GUIDED POLICY:
   - Mass conserved? -> Prioritize Move/Rotate/Flip
   - Colors change? -> Prioritize Recolor
   - Object count changes? -> Prioritize Split/Merge
   
   This is the PLANNER minimizing Expected Free Energy.

REFERENCES:
- SGC.Renormalization.lean: Coarse-graining theory
- SGC.ContinualLearning.AdiabaticInvariant.lean: Invariant protection
- demos/adaptive_polarity_v9_planner_simulator.py: Active inference architecture
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
from dataclasses import dataclass, field
from typing import List, Tuple, Dict, Optional, Set, Any
from collections import deque
from enum import Enum, auto
from abc import ABC, abstractmethod
import numpy as np
import json
import os
from pathlib import Path
import heapq


# =============================================================================
# CONFIGURATION
# =============================================================================

@dataclass
class ARCPhase2Config:
    """Configuration for Phase 2: Object-Centric Active Inference."""
    
    # Grid properties
    max_grid_size: int = 30
    num_colors: int = 10
    background_color: int = 0  # Black is typically background
    
    # Object graph
    min_object_size: int = 1  # Minimum pixels to count as object
    max_objects: int = 50     # Maximum objects to track
    
    # Sheaf structure
    stalk_dim: int = 16       # Object feature dimension
    
    # Active inference
    max_search_depth: int = 3     # Max DSL composition depth
    max_candidates: int = 20      # Max candidates to evaluate per level
    energy_threshold: float = 0.01  # Stop if energy below this
    
    # Data
    arc_data_path: str = ""  # Path to ARC training data
    
    device: str = 'cuda' if torch.cuda.is_available() else 'cpu'


# =============================================================================
# ARC DATA STRUCTURES
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
    """Single input-output example."""
    input_grid: ARCGrid
    output_grid: ARCGrid


@dataclass
class ARCTask:
    """ARC task with train/test examples."""
    task_id: str
    train_examples: List[ARCExample]
    test_examples: List[ARCExample]
    
    @classmethod
    def from_json(cls, task_id: str, data: dict, device: str = 'cpu') -> 'ARCTask':
        train = [
            ARCExample(
                input_grid=ARCGrid.from_list(ex['input'], device),
                output_grid=ARCGrid.from_list(ex['output'], device)
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
    """Load ARC tasks from a directory of JSON files."""
    tasks = []
    path = Path(data_path)
    
    if not path.exists():
        print(f"Warning: ARC data path {data_path} does not exist")
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
# TASK 1: OBJECT DETECTION & GRAPH CONSTRUCTION
# =============================================================================

@dataclass
class ARCObject:
    """
    A detected object (connected component) in an ARC grid.
    
    This is a NODE in our Object Graph.
    """
    object_id: int
    color: int
    pixels: List[Tuple[int, int]]  # List of (row, col) coordinates
    
    @property
    def mass(self) -> int:
        """Number of pixels."""
        return len(self.pixels)
    
    @property
    def centroid(self) -> Tuple[float, float]:
        """Center of mass (row, col)."""
        if not self.pixels:
            return (0.0, 0.0)
        rows = [p[0] for p in self.pixels]
        cols = [p[1] for p in self.pixels]
        return (sum(rows) / len(rows), sum(cols) / len(cols))
    
    @property
    def bbox(self) -> Tuple[int, int, int, int]:
        """Bounding box (min_row, min_col, max_row, max_col)."""
        if not self.pixels:
            return (0, 0, 0, 0)
        rows = [p[0] for p in self.pixels]
        cols = [p[1] for p in self.pixels]
        return (min(rows), min(cols), max(rows), max(cols))
    
    @property
    def width(self) -> int:
        bbox = self.bbox
        return bbox[3] - bbox[1] + 1
    
    @property
    def height(self) -> int:
        bbox = self.bbox
        return bbox[2] - bbox[0] + 1
    
    def to_stalk(self) -> torch.Tensor:
        """
        Convert object to stalk vector (feature representation).
        
        Stalk contains: [color_onehot(10), centroid(2), mass(1), bbox_size(2), aspect_ratio(1)]
        Total: 16 dimensions
        """
        features = []
        
        # Color one-hot (10 dims)
        color_oh = torch.zeros(10)
        color_oh[self.color] = 1.0
        features.append(color_oh)
        
        # Normalized centroid (2 dims)
        cr, cc = self.centroid
        features.append(torch.tensor([cr / 30.0, cc / 30.0]))
        
        # Normalized mass (1 dim)
        features.append(torch.tensor([self.mass / 100.0]))
        
        # Normalized bbox size (2 dims)
        features.append(torch.tensor([self.width / 30.0, self.height / 30.0]))
        
        # Aspect ratio (1 dim)
        aspect = self.width / max(self.height, 1)
        features.append(torch.tensor([aspect]))
        
        return torch.cat(features)


@dataclass
class ObjectEdge:
    """
    An edge in the Object Graph representing spatial relationship.
    """
    source_id: int
    target_id: int
    relation: str  # 'adjacent', 'aligned_h', 'aligned_v', 'inside', 'contains'
    distance: float  # Centroid distance


class ObjectGraph:
    """
    The Object Graph: our coarse-grained base space.
    
    This replaces the pixel grid as the domain for the Sheaf.
    Solving at this macro-scale is LUMPABILITY from SGC theory.
    """
    
    def __init__(self, grid: ARCGrid, config: ARCPhase2Config):
        self.grid = grid
        self.config = config
        self.objects: Dict[int, ARCObject] = {}
        self.edges: List[ObjectEdge] = []
        
        # Detect objects and build graph
        self._detect_objects()
        self._build_edges()
    
    def _detect_objects(self):
        """Flood-fill to find connected components."""
        grid_np = self.grid.to_numpy()
        H, W = grid_np.shape
        visited = np.zeros((H, W), dtype=bool)
        object_id = 0
        
        for r in range(H):
            for c in range(W):
                if visited[r, c]:
                    continue
                
                color = grid_np[r, c]
                
                # Skip background (optional - include all for now)
                # if color == self.config.background_color:
                #     visited[r, c] = True
                #     continue
                
                # Flood fill
                pixels = []
                queue = deque([(r, c)])
                visited[r, c] = True
                
                while queue:
                    cr, cc = queue.popleft()
                    pixels.append((cr, cc))
                    
                    # 4-connectivity
                    for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                        nr, nc = cr + dr, cc + dc
                        if 0 <= nr < H and 0 <= nc < W and not visited[nr, nc]:
                            if grid_np[nr, nc] == color:
                                visited[nr, nc] = True
                                queue.append((nr, nc))
                
                if len(pixels) >= self.config.min_object_size:
                    self.objects[object_id] = ARCObject(
                        object_id=object_id,
                        color=int(color),
                        pixels=pixels
                    )
                    object_id += 1
                    
                    if object_id >= self.config.max_objects:
                        return
    
    def _build_edges(self):
        """Build edges based on spatial relationships."""
        obj_list = list(self.objects.values())
        
        for i, obj1 in enumerate(obj_list):
            for obj2 in obj_list[i+1:]:
                # Check adjacency (bounding boxes touch or overlap)
                b1 = obj1.bbox
                b2 = obj2.bbox
                
                # Expand bbox by 1 to check adjacency
                adjacent = not (
                    b1[2] + 1 < b2[0] or  # obj1 above obj2
                    b2[2] + 1 < b1[0] or  # obj2 above obj1
                    b1[3] + 1 < b2[1] or  # obj1 left of obj2
                    b2[3] + 1 < b1[1]     # obj2 left of obj1
                )
                
                if adjacent:
                    # Compute centroid distance
                    c1 = obj1.centroid
                    c2 = obj2.centroid
                    dist = np.sqrt((c1[0] - c2[0])**2 + (c1[1] - c2[1])**2)
                    
                    # Determine relation type
                    if abs(c1[0] - c2[0]) < 1.0:
                        relation = 'aligned_h'
                    elif abs(c1[1] - c2[1]) < 1.0:
                        relation = 'aligned_v'
                    else:
                        relation = 'adjacent'
                    
                    self.edges.append(ObjectEdge(
                        source_id=obj1.object_id,
                        target_id=obj2.object_id,
                        relation=relation,
                        distance=dist
                    ))
    
    @property
    def num_objects(self) -> int:
        return len(self.objects)
    
    @property
    def num_edges(self) -> int:
        return len(self.edges)
    
    def get_stalks(self) -> torch.Tensor:
        """Get stalk vectors for all objects: (num_objects, stalk_dim)."""
        if not self.objects:
            return torch.zeros(0, 16)
        return torch.stack([obj.to_stalk() for obj in self.objects.values()])
    
    def get_adjacency(self) -> torch.Tensor:
        """Get adjacency matrix: (num_objects, num_objects)."""
        n = self.num_objects
        adj = torch.zeros(n, n)
        for edge in self.edges:
            adj[edge.source_id, edge.target_id] = 1.0
            adj[edge.target_id, edge.source_id] = 1.0
        return adj


# =============================================================================
# TASK 2: INVARIANT COMPUTATION (FOR ACTIVE INFERENCE)
# =============================================================================

@dataclass
class GridInvariants:
    """
    Computed invariants of a grid.
    These guide the Active Inference policy.
    """
    total_mass: int           # Total non-background pixels
    color_histogram: Dict[int, int]  # Color -> count
    num_objects: int          # Number of connected components
    object_colors: Set[int]   # Unique object colors
    grid_size: Tuple[int, int]
    
    # Derived
    has_symmetry_h: bool = False
    has_symmetry_v: bool = False


def compute_invariants(grid: ARCGrid, config: ARCPhase2Config) -> GridInvariants:
    """Compute invariants of a grid for Active Inference."""
    data = grid.to_numpy()
    H, W = data.shape
    
    # Color histogram (position-independent)
    hist = {}
    for c in range(config.num_colors):
        count = int((data == c).sum())
        if count > 0:
            hist[c] = count
    
    # Total mass (non-background)
    bg = config.background_color
    total_mass = int((data != bg).sum())
    
    # Object graph for counting
    obj_graph = ObjectGraph(grid, config)
    
    # Check symmetries
    has_sym_h = np.allclose(data, np.flip(data, axis=1))
    has_sym_v = np.allclose(data, np.flip(data, axis=0))
    
    return GridInvariants(
        total_mass=total_mass,
        color_histogram=hist,
        num_objects=obj_graph.num_objects,
        object_colors=set(obj.color for obj in obj_graph.objects.values()),
        grid_size=(H, W),
        has_symmetry_h=has_sym_h,
        has_symmetry_v=has_sym_v
    )


def grids_match_up_to_color_permutation(grid1: ARCGrid, grid2: ARCGrid) -> Tuple[bool, Dict[int, int]]:
    """
    Check if two grids are identical up to a color permutation.
    Returns (is_match, color_mapping).
    """
    if grid1.shape != grid2.shape:
        return False, {}
    
    data1 = grid1.to_numpy().flatten()
    data2 = grid2.to_numpy().flatten()
    
    # Try to build consistent mapping
    mapping = {}
    for c1, c2 in zip(data1, data2):
        if c1 in mapping:
            if mapping[c1] != c2:
                return False, {}
        else:
            mapping[int(c1)] = int(c2)
    
    # Check mapping is bijective
    if len(set(mapping.values())) != len(mapping):
        return False, {}
    
    return True, mapping


@dataclass
class InvariantDelta:
    """
    Difference in invariants between input and output.
    This tells us WHAT changed, guiding DSL selection.
    """
    mass_change: int          # output.mass - input.mass
    mass_conserved: bool
    
    colors_added: Set[int]
    colors_removed: Set[int]
    colors_changed: bool
    
    # NEW: Detect if colors were swapped/permuted (same histogram, different positions)
    histogram_conserved: bool
    likely_color_swap: bool
    swap_pairs: List[Tuple[int, int]]  # Likely color pairs that were swapped
    
    object_count_change: int
    objects_conserved: bool
    
    size_change: Tuple[int, int]  # (dH, dW)
    size_conserved: bool
    
    symmetry_gained_h: bool
    symmetry_gained_v: bool


def compute_invariant_delta(
    input_inv: GridInvariants, 
    output_inv: GridInvariants,
    input_grid: ARCGrid = None,
    output_grid: ARCGrid = None
) -> InvariantDelta:
    """Compute what changed between input and output."""
    
    mass_change = output_inv.total_mass - input_inv.total_mass
    
    colors_added = output_inv.object_colors - input_inv.object_colors
    colors_removed = input_inv.object_colors - output_inv.object_colors
    
    obj_change = output_inv.num_objects - input_inv.num_objects
    
    size_change = (
        output_inv.grid_size[0] - input_inv.grid_size[0],
        output_inv.grid_size[1] - input_inv.grid_size[1]
    )
    
    # Check if histogram is conserved (same color counts, different positions)
    histogram_conserved = (input_inv.color_histogram == output_inv.color_histogram)
    
    # Detect likely color swaps
    swap_pairs = []
    likely_color_swap = False
    
    if input_grid is not None and output_grid is not None and input_grid.shape == output_grid.shape:
        in_hist = input_inv.color_histogram
        out_hist = output_inv.color_histogram
        
        # Check if output histogram is a PERMUTATION of input histogram
        # (same multiset of counts, but possibly different color assignments)
        in_counts = sorted(in_hist.values())
        out_counts = sorted(out_hist.values())
        histogram_is_permutation = (in_counts == out_counts)
        
        if histogram_is_permutation and not torch.equal(input_grid.data, output_grid.data):
            # Find candidate swap pairs by matching count changes
            # If input has color A with count X and output has color A with count Y,
            # and input has color B with count Y and output has color B with count X,
            # then (A,B) is a candidate swap pair
            
            for c1 in in_hist:
                for c2 in in_hist:
                    if c1 < c2:  # Avoid duplicates
                        in_c1 = in_hist.get(c1, 0)
                        in_c2 = in_hist.get(c2, 0)
                        out_c1 = out_hist.get(c1, 0)
                        out_c2 = out_hist.get(c2, 0)
                        
                        # Check if counts are swapped
                        if in_c1 == out_c2 and in_c2 == out_c1 and in_c1 != in_c2:
                            swap_pairs.append((c1, c2))
                            likely_color_swap = True
    
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
        symmetry_gained_h=(output_inv.has_symmetry_h and not input_inv.has_symmetry_h),
        symmetry_gained_v=(output_inv.has_symmetry_v and not input_inv.has_symmetry_v)
    )


# =============================================================================
# OBJECT-LEVEL DSL PRIMITIVES
# =============================================================================

class ObjectDSLPrimitive(ABC):
    """Abstract base for object-level DSL operations."""
    
    @abstractmethod
    def apply(self, grid: ARCGrid) -> ARCGrid:
        """Apply transformation to grid."""
        pass
    
    @abstractmethod
    def signature(self) -> str:
        """Human-readable name."""
        pass
    
    @abstractmethod
    def priority_score(self, delta: InvariantDelta) -> float:
        """
        Score for Active Inference priority queue.
        Higher = more likely to be useful given the invariant delta.
        """
        pass


class Identity(ObjectDSLPrimitive):
    def apply(self, grid: ARCGrid) -> ARCGrid:
        return grid.clone()
    
    def signature(self) -> str:
        return "identity"
    
    def priority_score(self, delta: InvariantDelta) -> float:
        return 0.0  # Never prioritize identity


class Rotate90(ObjectDSLPrimitive):
    def apply(self, grid: ARCGrid) -> ARCGrid:
        return ARCGrid(torch.rot90(grid.data, k=-1))
    
    def signature(self) -> str:
        return "rotate_90"
    
    def priority_score(self, delta: InvariantDelta) -> float:
        # Rotation conserves mass, colors, object count
        if delta.mass_conserved and not delta.colors_changed and delta.objects_conserved:
            return 0.8
        return 0.1


class Rotate180(ObjectDSLPrimitive):
    def apply(self, grid: ARCGrid) -> ARCGrid:
        return ARCGrid(torch.rot90(grid.data, k=2))
    
    def signature(self) -> str:
        return "rotate_180"
    
    def priority_score(self, delta: InvariantDelta) -> float:
        if delta.mass_conserved and not delta.colors_changed:
            return 0.7
        return 0.1


class Rotate270(ObjectDSLPrimitive):
    def apply(self, grid: ARCGrid) -> ARCGrid:
        return ARCGrid(torch.rot90(grid.data, k=1))
    
    def signature(self) -> str:
        return "rotate_270"
    
    def priority_score(self, delta: InvariantDelta) -> float:
        if delta.mass_conserved and not delta.colors_changed:
            return 0.7
        return 0.1


class FlipHorizontal(ObjectDSLPrimitive):
    def apply(self, grid: ARCGrid) -> ARCGrid:
        return ARCGrid(torch.flip(grid.data, dims=[1]))
    
    def signature(self) -> str:
        return "flip_h"
    
    def priority_score(self, delta: InvariantDelta) -> float:
        # Flip to gain symmetry
        if delta.symmetry_gained_h:
            return 0.9
        if delta.mass_conserved and not delta.colors_changed:
            return 0.6
        return 0.1


class FlipVertical(ObjectDSLPrimitive):
    def apply(self, grid: ARCGrid) -> ARCGrid:
        return ARCGrid(torch.flip(grid.data, dims=[0]))
    
    def signature(self) -> str:
        return "flip_v"
    
    def priority_score(self, delta: InvariantDelta) -> float:
        if delta.symmetry_gained_v:
            return 0.9
        if delta.mass_conserved and not delta.colors_changed:
            return 0.6
        return 0.1


class ColorSwap(ObjectDSLPrimitive):
    def __init__(self, color_a: int, color_b: int):
        self.color_a = color_a
        self.color_b = color_b
    
    def apply(self, grid: ARCGrid) -> ARCGrid:
        data = grid.data.clone()
        mask_a = (data == self.color_a)
        mask_b = (data == self.color_b)
        data[mask_a] = self.color_b
        data[mask_b] = self.color_a
        return ARCGrid(data)
    
    def signature(self) -> str:
        return f"swap_{self.color_a}_{self.color_b}"
    
    def priority_score(self, delta: InvariantDelta) -> float:
        # HIGH priority if likely color swap detected
        if delta.likely_color_swap:
            # Even higher if this specific pair is in swap_pairs
            if (self.color_a, self.color_b) in delta.swap_pairs or \
               (self.color_b, self.color_a) in delta.swap_pairs:
                return 0.95
            return 0.8
        
        # Medium priority if histogram conserved but colors changed position
        if delta.histogram_conserved and delta.mass_conserved:
            return 0.6
        
        # Color swap when colors change but mass conserved
        if delta.colors_changed and delta.mass_conserved:
            return 0.5
        return 0.1


class FillColor(ObjectDSLPrimitive):
    """Fill all non-background with a single color."""
    def __init__(self, color: int, bg: int = 0):
        self.color = color
        self.bg = bg
    
    def apply(self, grid: ARCGrid) -> ARCGrid:
        data = grid.data.clone()
        data[data != self.bg] = self.color
        return ARCGrid(data)
    
    def signature(self) -> str:
        return f"fill_{self.color}"
    
    def priority_score(self, delta: InvariantDelta) -> float:
        if delta.colors_changed and len(delta.colors_removed) > 1:
            return 0.5
        return 0.1


class Shift(ObjectDSLPrimitive):
    """Shift grid contents."""
    def __init__(self, dr: int, dc: int, bg: int = 0):
        self.dr = dr
        self.dc = dc
        self.bg = bg
    
    def apply(self, grid: ARCGrid) -> ARCGrid:
        data = grid.data.clone()
        H, W = data.shape
        result = torch.full_like(data, self.bg)
        
        # Compute valid source and target ranges
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
    
    def signature(self) -> str:
        return f"shift_{self.dr}_{self.dc}"
    
    def priority_score(self, delta: InvariantDelta) -> float:
        if delta.mass_conserved and not delta.colors_changed:
            return 0.5
        return 0.2


class Crop(ObjectDSLPrimitive):
    """Crop to bounding box of non-background."""
    def __init__(self, bg: int = 0):
        self.bg = bg
    
    def apply(self, grid: ARCGrid) -> ARCGrid:
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
    
    def signature(self) -> str:
        return "crop"
    
    def priority_score(self, delta: InvariantDelta) -> float:
        if not delta.size_conserved and delta.mass_conserved:
            return 0.7
        return 0.2


class Upscale(ObjectDSLPrimitive):
    """Upscale by factor."""
    def __init__(self, factor: int):
        self.factor = factor
    
    def apply(self, grid: ARCGrid) -> ARCGrid:
        data = grid.data
        H, W = data.shape
        result = data.repeat_interleave(self.factor, dim=0).repeat_interleave(self.factor, dim=1)
        return ARCGrid(result)
    
    def signature(self) -> str:
        return f"upscale_{self.factor}"
    
    def priority_score(self, delta: InvariantDelta) -> float:
        dH, dW = delta.size_change
        if dH > 0 and dW > 0:
            return 0.6
        return 0.1


def build_dsl_library(config: ARCPhase2Config) -> List[ObjectDSLPrimitive]:
    """Build the full DSL library with object-level primitives."""
    ops = [
        Identity(),
        Rotate90(),
        Rotate180(),
        Rotate270(),
        FlipHorizontal(),
        FlipVertical(),
        Crop(),
    ]
    
    # Color swaps for common color pairs
    for a in range(config.num_colors):
        for b in range(a + 1, config.num_colors):
            ops.append(ColorSwap(a, b))
    
    # Fill operations
    for c in range(1, config.num_colors):
        ops.append(FillColor(c))
    
    # Small shifts
    for dr in [-1, 0, 1]:
        for dc in [-1, 0, 1]:
            if dr != 0 or dc != 0:
                ops.append(Shift(dr, dc))
    
    # Upscale
    for factor in [2, 3]:
        ops.append(Upscale(factor))
    
    return ops


# =============================================================================
# OBJECT-LEVEL SHEAF
# =============================================================================

class ObjectSheaf:
    """
    Cellular Sheaf over the Object Graph.
    
    This is the coarse-grained sheaf where:
    - Nodes = Objects (connected components)
    - Stalks = Object feature vectors
    - Restriction maps = Identity (objects are autonomous)
    
    The Laplacian energy measures inconsistency between
    neighboring objects.
    """
    
    def __init__(self, grid: ARCGrid, config: ARCPhase2Config):
        self.config = config
        self.object_graph = ObjectGraph(grid, config)
        
        # Get stalks and adjacency
        self.stalks = self.object_graph.get_stalks()
        self.adjacency = self.object_graph.get_adjacency()
        
        # Compute degree matrix
        self.degree = self.adjacency.sum(dim=1)
    
    def compute_laplacian_energy(self) -> float:
        """
        Compute Sheaf Laplacian energy: <x, L x>.
        
        For object graph, this measures how much neighboring
        objects "disagree" in their features.
        """
        if self.stalks.shape[0] == 0:
            return 0.0
        
        n = self.stalks.shape[0]
        energy = 0.0
        
        for edge in self.object_graph.edges:
            i, j = edge.source_id, edge.target_id
            if i < n and j < n:
                diff = self.stalks[i] - self.stalks[j]
                energy += (diff ** 2).sum().item()
        
        return energy
    
    @property
    def num_objects(self) -> int:
        return self.object_graph.num_objects


# =============================================================================
# TASK 2: ACTIVE INFERENCE SOLVER
# =============================================================================

@dataclass
class SearchState:
    """State in the program search."""
    grid: ARCGrid
    program: List[ObjectDSLPrimitive]
    energy: float
    
    def __lt__(self, other):
        # For heapq: lower energy = higher priority
        return self.energy < other.energy


class ActiveInferenceSolver:
    """
    Active Inference solver using invariant-guided priority queue.
    
    This replaces exhaustive search with Expected Free Energy minimization:
    - Compute invariant delta (what needs to change)
    - Prioritize DSL operations that address those changes
    - Search depth-first with energy-based pruning
    
    This is the PLANNER from the Planner-Simulator architecture.
    """
    
    def __init__(self, config: ARCPhase2Config):
        self.config = config
        self.dsl = build_dsl_library(config)
        print(f"   DSL library: {len(self.dsl)} primitives")
    
    def compute_match_energy(self, pred: ARCGrid, target: ARCGrid) -> float:
        """
        Compute energy = mismatch between prediction and target.
        
        Lower is better. Zero = perfect match.
        """
        if pred.shape != target.shape:
            # Shape mismatch: high penalty
            return 1000.0 + abs(pred.height - target.height) + abs(pred.width - target.width)
        
        # Cell-wise mismatch
        mismatch = (pred.data != target.data).float().sum().item()
        total = target.data.numel()
        
        return mismatch / total
    
    def rank_operations(
        self, 
        delta: InvariantDelta,
        current_grid: ARCGrid,
        target_grid: ARCGrid
    ) -> List[Tuple[float, ObjectDSLPrimitive]]:
        """
        Rank DSL operations by priority (Expected Free Energy proxy).
        
        Higher priority = more likely to reduce defect.
        """
        ranked = []
        
        for op in self.dsl:
            # Get base priority from invariant delta
            priority = op.priority_score(delta)
            
            # Boost if operation might fix shape mismatch
            if not delta.size_conserved:
                if isinstance(op, Crop) and current_grid.shape > target_grid.shape:
                    priority += 0.3
                if isinstance(op, Upscale) and current_grid.shape < target_grid.shape:
                    priority += 0.3
            
            ranked.append((priority, op))
        
        # Sort by priority (descending)
        ranked.sort(key=lambda x: -x[0])
        
        return ranked
    
    def solve(
        self,
        input_grid: ARCGrid,
        target_grid: ARCGrid,
        verbose: bool = False
    ) -> Tuple[List[ObjectDSLPrimitive], float]:
        """
        Solve using Active Inference search.
        
        Returns: (program, final_energy)
        """
        # Compute invariant delta (pass grids for color swap detection)
        input_inv = compute_invariants(input_grid, self.config)
        target_inv = compute_invariants(target_grid, self.config)
        delta = compute_invariant_delta(input_inv, target_inv, input_grid, target_grid)
        
        if verbose:
            print(f"   Invariant Delta:")
            print(f"     Mass: {'+' if delta.mass_change >= 0 else ''}{delta.mass_change} (conserved: {delta.mass_conserved})")
            print(f"     Colors changed: {delta.colors_changed}, Histogram conserved: {delta.histogram_conserved}")
            print(f"     Likely color swap: {delta.likely_color_swap}, Pairs: {delta.swap_pairs}")
            print(f"     Objects: {'+' if delta.object_count_change >= 0 else ''}{delta.object_count_change}")
            print(f"     Size: {delta.size_change}")
        
        # Initialize search
        initial_energy = self.compute_match_energy(input_grid, target_grid)
        best_program = []
        best_energy = initial_energy
        
        if verbose:
            print(f"   Initial energy: {initial_energy:.4f}")
        
        if initial_energy < self.config.energy_threshold:
            return [], initial_energy
        
        # Priority queue: (energy, state)
        # Use heap for best-first search
        initial_state = SearchState(input_grid, [], initial_energy)
        frontier = [initial_state]
        heapq.heapify(frontier)
        
        visited = set()
        iterations = 0
        max_iterations = 1000
        
        while frontier and iterations < max_iterations:
            iterations += 1
            
            # Pop best state
            current = heapq.heappop(frontier)
            
            # Skip if we've seen this grid
            grid_hash = current.grid.data.cpu().numpy().tobytes()
            if grid_hash in visited:
                continue
            visited.add(grid_hash)
            
            # Check if this is better than best
            if current.energy < best_energy:
                best_energy = current.energy
                best_program = current.program
                
                if verbose:
                    sig = " -> ".join(op.signature() for op in best_program) or "identity"
                    print(f"   Found better: {sig} (energy={best_energy:.4f})")
                
                if best_energy < self.config.energy_threshold:
                    break
            
            # Don't expand if too deep
            if len(current.program) >= self.config.max_search_depth:
                continue
            
            # Rank operations
            ranked_ops = self.rank_operations(delta, current.grid, target_grid)
            
            # Try top candidates
            for priority, op in ranked_ops[:self.config.max_candidates]:
                if priority < 0.1:
                    continue  # Skip very low priority
                
                try:
                    new_grid = op.apply(current.grid)
                    new_energy = self.compute_match_energy(new_grid, target_grid)
                    
                    # Only add if promising
                    if new_energy < current.energy + 0.5:  # Allow some slack
                        new_program = current.program + [op]
                        new_state = SearchState(new_grid, new_program, new_energy)
                        heapq.heappush(frontier, new_state)
                except Exception:
                    continue
        
        if verbose:
            print(f"   Search complete: {iterations} iterations, {len(visited)} states visited")
        
        return best_program, best_energy


# =============================================================================
# TASK 3: REAL ARC DATA EVALUATION
# =============================================================================

def evaluate_on_task(
    solver: ActiveInferenceSolver,
    task: ARCTask,
    config: ARCPhase2Config,
    verbose: bool = False
) -> Dict[str, Any]:
    """
    Evaluate solver on a single ARC task.
    
    Returns metrics including Sheaf energy reduction.
    """
    results = {
        'task_id': task.task_id,
        'train_results': [],
        'test_results': [],
        'avg_train_energy': 0.0,
        'avg_test_energy': 0.0,
        'programs_found': []
    }
    
    # Learn from training examples
    programs = []
    
    for i, example in enumerate(task.train_examples):
        if verbose:
            print(f"\n   Train example {i+1}:")
        
        program, energy = solver.solve(
            example.input_grid,
            example.output_grid,
            verbose=verbose
        )
        
        programs.append(program)
        results['train_results'].append({
            'energy': energy,
            'program': " -> ".join(op.signature() for op in program) or "identity"
        })
    
    results['avg_train_energy'] = np.mean([r['energy'] for r in results['train_results']])
    results['programs_found'] = [r['program'] for r in results['train_results']]
    
    # Apply learned programs to test examples
    for i, example in enumerate(task.test_examples):
        # Use first successful program (simple strategy)
        if programs:
            pred_grid = example.input_grid
            for op in programs[0]:
                pred_grid = op.apply(pred_grid)
            energy = solver.compute_match_energy(pred_grid, example.output_grid)
        else:
            energy = solver.compute_match_energy(example.input_grid, example.output_grid)
        
        results['test_results'].append({'energy': energy})
    
    results['avg_test_energy'] = np.mean([r['energy'] for r in results['test_results']]) if results['test_results'] else 0.0
    
    return results


def run_arc_evaluation(
    data_path: str,
    config: ARCPhase2Config,
    num_tasks: int = 10,
    verbose: bool = True
) -> List[Dict[str, Any]]:
    """
    Run evaluation on real ARC tasks.
    """
    print("=" * 60)
    print("ARC-SGC Phase 2: Object-Centric Active Inference")
    print("=" * 60)
    
    # Load tasks
    print(f"\nLoading ARC tasks from: {data_path}")
    tasks = load_arc_tasks(data_path, config.device, limit=num_tasks)
    print(f"Loaded {len(tasks)} tasks")
    
    if not tasks:
        print("No tasks found! Using synthetic test.")
        return run_synthetic_test(config)
    
    # Build solver
    print("\nBuilding Active Inference Solver...")
    solver = ActiveInferenceSolver(config)
    
    # Evaluate
    all_results = []
    
    for i, task in enumerate(tasks):
        print(f"\n{'='*60}")
        print(f"Task {i+1}/{len(tasks)}: {task.task_id}")
        print(f"  Train examples: {len(task.train_examples)}")
        print(f"  Test examples: {len(task.test_examples)}")
        
        results = evaluate_on_task(solver, task, config, verbose=verbose)
        all_results.append(results)
        
        print(f"\n  Results:")
        print(f"    Avg train energy: {results['avg_train_energy']:.4f}")
        print(f"    Programs found: {results['programs_found']}")
        if results['test_results']:
            print(f"    Avg test energy: {results['avg_test_energy']:.4f}")
    
    # Summary
    print("\n" + "=" * 60)
    print("EVALUATION SUMMARY")
    print("=" * 60)
    
    solved = sum(1 for r in all_results if r['avg_train_energy'] < 0.01)
    partial = sum(1 for r in all_results if 0.01 <= r['avg_train_energy'] < 0.5)
    
    print(f"Tasks evaluated: {len(all_results)}")
    print(f"Perfectly solved (energy < 0.01): {solved}")
    print(f"Partially solved (energy < 0.5): {partial}")
    print(f"Average train energy: {np.mean([r['avg_train_energy'] for r in all_results]):.4f}")
    
    return all_results


def run_synthetic_test(config: ARCPhase2Config) -> List[Dict[str, Any]]:
    """Run on synthetic test tasks when real data unavailable."""
    print("\n" + "=" * 60)
    print("SYNTHETIC TEST (No ARC data found)")
    print("=" * 60)
    
    solver = ActiveInferenceSolver(config)
    results = []
    
    # Test 1: Rotation
    print("\n--- Test 1: Rotation ---")
    input_data = torch.tensor([
        [0, 0, 0, 0, 0],
        [0, 1, 2, 3, 0],
        [0, 4, 5, 6, 0],
        [0, 7, 8, 9, 0],
        [0, 0, 0, 0, 0]
    ], dtype=torch.long, device=config.device)
    output_data = torch.rot90(input_data, k=-1)
    
    input_grid = ARCGrid(input_data)
    output_grid = ARCGrid(output_data)
    
    print(f"Input:\n{input_grid.data}")
    print(f"Output:\n{output_grid.data}")
    
    program, energy = solver.solve(input_grid, output_grid, verbose=True)
    sig = " -> ".join(op.signature() for op in program) or "identity"
    print(f"Found: {sig} (energy={energy:.4f})")
    results.append({'test': 'rotation', 'program': sig, 'energy': energy})
    
    # Test 2: Color swap
    print("\n--- Test 2: Color Swap ---")
    input_data2 = torch.tensor([
        [1, 1, 1],
        [2, 2, 2],
        [1, 1, 1]
    ], dtype=torch.long, device=config.device)
    output_data2 = torch.tensor([
        [2, 2, 2],
        [1, 1, 1],
        [2, 2, 2]
    ], dtype=torch.long, device=config.device)
    
    input_grid2 = ARCGrid(input_data2)
    output_grid2 = ARCGrid(output_data2)
    
    print(f"Input:\n{input_grid2.data}")
    print(f"Output:\n{output_grid2.data}")
    
    program2, energy2 = solver.solve(input_grid2, output_grid2, verbose=True)
    sig2 = " -> ".join(op.signature() for op in program2) or "identity"
    print(f"Found: {sig2} (energy={energy2:.4f})")
    results.append({'test': 'color_swap', 'program': sig2, 'energy': energy2})
    
    # Test 3: Flip + Rotate (composition)
    print("\n--- Test 3: Flip + Rotate (Composition) ---")
    input_data3 = torch.tensor([
        [1, 2, 3],
        [0, 0, 0],
        [0, 0, 0]
    ], dtype=torch.long, device=config.device)
    output_data3 = torch.rot90(torch.flip(input_data3, dims=[0]), k=-1)
    
    input_grid3 = ARCGrid(input_data3)
    output_grid3 = ARCGrid(output_data3)
    
    print(f"Input:\n{input_grid3.data}")
    print(f"Output:\n{output_grid3.data}")
    
    program3, energy3 = solver.solve(input_grid3, output_grid3, verbose=True)
    sig3 = " -> ".join(op.signature() for op in program3) or "identity"
    print(f"Found: {sig3} (energy={energy3:.4f})")
    results.append({'test': 'flip_rotate', 'program': sig3, 'energy': energy3})
    
    # Summary
    print("\n" + "=" * 60)
    print("SYNTHETIC TEST SUMMARY")
    print("=" * 60)
    for r in results:
        status = "SOLVED" if r['energy'] < 0.01 else "PARTIAL" if r['energy'] < 0.5 else "FAILED"
        print(f"  {r['test']}: {status} ({r['program']}, energy={r['energy']:.4f})")
    
    return results


# =============================================================================
# MAIN
# =============================================================================

def main():
    config = ARCPhase2Config()
    
    # Try to find ARC data
    possible_paths = [
        "data/arc/training",
        "data/ARC/training", 
        "C:/Lean4 Projects/data/arc/training",
        "../ARC/data/training",
        "arc_data/training"
    ]
    
    arc_path = None
    for path in possible_paths:
        if Path(path).exists():
            arc_path = path
            break
    
    if arc_path:
        print(f"Found ARC data at: {arc_path}")
        results = run_arc_evaluation(arc_path, config, num_tasks=10, verbose=True)
    else:
        print("ARC data not found. Running synthetic tests.")
        results = run_synthetic_test(config)
    
    return results


if __name__ == "__main__":
    main()
