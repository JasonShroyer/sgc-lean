"""
ARC-SGC Phase 8.1: Scaling the Physics

THE BIRTH OF A PHYSICIST - EXPANDED VOCABULARY

Phase 8 proved: ARC solutions are Hamiltonians H = sum(w_i * V_i).
Task 8 solved with H = V_contact (objects maximize separation).

The gap to solving more tasks is VOCABULARY - we need richer potentials:
- V_topology: enclosure, connectivity, holes
- V_shape: symmetry, aspect ratio, compactness
- V_pattern: periodicity, repetition, mirroring
- V_spatial: relative positions, quadrants, edges

ARCHITECTURE (Validated):
1. Perception: Grid -> Object Graph (Lumpability)
2. Induction: Find weights w such that output = argmin H(x; w)
3. Deduction: Relax input grid under discovered Hamiltonian

This file scales the potential library from 5 to 25+ primitives.
"""

import torch
import torch.nn.functional as F
from dataclasses import dataclass
from typing import List, Tuple, Dict, Optional, Set
from collections import deque
from abc import ABC, abstractmethod
import numpy as np
import json
from pathlib import Path
from copy import deepcopy
import sys

# Force unbuffered output for real-time progress
def printfl(*args, **kwargs):
    print(*args, **kwargs)
    sys.stdout.flush()


# =============================================================================
# CONFIGURATION
# =============================================================================

@dataclass
class ARCPhase81Config:
    max_grid_size: int = 30
    num_colors: int = 10
    background_color: int = 0
    min_object_size: int = 1
    max_objects: int = 50
    
    # Relaxation
    max_relax_steps: int = 20
    convergence_threshold: float = 0.001
    
    # Optimization
    energy_threshold: float = 0.0001
    consistency_threshold: float = 0.005
    
    device: str = 'cuda' if torch.cuda.is_available() else 'cpu'


# =============================================================================
# GRID AND OBJECT STRUCTURES
# =============================================================================

@dataclass
class ARCGrid:
    data: torch.Tensor
    
    @property
    def height(self) -> int: return self.data.shape[0]
    @property
    def width(self) -> int: return self.data.shape[1]
    @property
    def shape(self) -> Tuple[int, int]: return (self.height, self.width)
    
    @classmethod
    def from_list(cls, lst: List[List[int]], device: str = 'cpu') -> 'ARCGrid':
        return cls(torch.tensor(lst, dtype=torch.long, device=device))
    
    def clone(self) -> 'ARCGrid': return ARCGrid(self.data.clone())
    def to_numpy(self) -> np.ndarray: return self.data.cpu().numpy()


@dataclass
class ARCObject:
    object_id: int
    color: int
    pixels: List[Tuple[int, int]]
    
    @property
    def mass(self) -> int: return len(self.pixels)
    
    @property
    def bbox(self) -> Tuple[int, int, int, int]:
        if not self.pixels: return (0, 0, 0, 0)
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
        if not self.pixels: return (0.0, 0.0)
        return (sum(p[0] for p in self.pixels) / len(self.pixels),
                sum(p[1] for p in self.pixels) / len(self.pixels))
    
    @property
    def aspect_ratio(self) -> float:
        w, h = self.width, self.height
        if h == 0: return 1.0
        return w / h
    
    @property
    def compactness(self) -> float:
        """How filled is the bounding box? 1.0 = solid rectangle."""
        w, h = self.width, self.height
        if w * h == 0: return 0.0
        return len(self.pixels) / (w * h)
    
    def get_mask(self, H: int, W: int, device: str = 'cpu') -> torch.Tensor:
        mask = torch.zeros(H, W, dtype=torch.bool, device=device)
        for r, c in self.pixels:
            if 0 <= r < H and 0 <= c < W:
                mask[r, c] = True
        return mask
    
    def get_perimeter(self) -> Set[Tuple[int, int]]:
        """Get boundary pixels (adjacent to non-object pixels)."""
        pixel_set = set(self.pixels)
        perimeter = set()
        for r, c in self.pixels:
            for dr, dc in [(-1,0), (1,0), (0,-1), (0,1)]:
                if (r+dr, c+dc) not in pixel_set:
                    perimeter.add((r, c))
                    break
        return perimeter


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
    if not p.exists(): return tasks
    for f in sorted(p.glob("*.json"))[:limit]:
        try:
            with open(f) as fp:
                tasks.append(ARCTask.from_json(f.stem, json.load(fp), device))
        except Exception:
            pass
    return tasks


def detect_objects(grid: ARCGrid, config: ARCPhase81Config) -> List[ARCObject]:
    data = grid.to_numpy()
    H, W = data.shape
    visited = np.zeros((H, W), dtype=bool)
    objects = []
    obj_id = 0
    
    for r in range(H):
        for c in range(W):
            if visited[r, c]: continue
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
# EXPANDED POTENTIAL LIBRARY (25+ Potentials)
# =============================================================================

class PotentialFunction(ABC):
    """Base class for potential energy functions."""
    
    @abstractmethod
    def compute(self, obj: ARCObject, grid: ARCGrid, all_objects: List[ARCObject], config: ARCPhase81Config) -> float:
        pass
    
    @abstractmethod
    def name(self) -> str:
        pass


# -----------------------------------------------------------------------------
# CATEGORY 1: BOUNDARY POTENTIALS (Where is the object relative to edges?)
# -----------------------------------------------------------------------------

class V_BoundaryDist(PotentialFunction):
    """Distance to nearest grid boundary. Minimize -> walls."""
    def compute(self, obj, grid, all_objects, config):
        H, W = grid.height, grid.width
        r1, c1, r2, c2 = obj.bbox
        return min(r1, H - r2, c1, W - c2)
    def name(self): return "V_boundary"


class V_TopEdge(PotentialFunction):
    """Distance to top edge. Minimize -> move up."""
    def compute(self, obj, grid, all_objects, config):
        r1, _, _, _ = obj.bbox
        return r1
    def name(self): return "V_top"


class V_BottomEdge(PotentialFunction):
    """Distance to bottom edge. Minimize -> move down."""
    def compute(self, obj, grid, all_objects, config):
        _, _, r2, _ = obj.bbox
        return grid.height - r2
    def name(self): return "V_bottom"


class V_LeftEdge(PotentialFunction):
    """Distance to left edge. Minimize -> move left."""
    def compute(self, obj, grid, all_objects, config):
        _, c1, _, _ = obj.bbox
        return c1
    def name(self): return "V_left"


class V_RightEdge(PotentialFunction):
    """Distance to right edge. Minimize -> move right."""
    def compute(self, obj, grid, all_objects, config):
        _, _, _, c2 = obj.bbox
        return grid.width - c2
    def name(self): return "V_right"


# -----------------------------------------------------------------------------
# CATEGORY 2: CENTER POTENTIALS (Where is the object relative to center?)
# -----------------------------------------------------------------------------

class V_CenterDist(PotentialFunction):
    """Distance to grid center. Minimize -> center."""
    def compute(self, obj, grid, all_objects, config):
        H, W = grid.height, grid.width
        cr, cc = obj.centroid
        return ((cr - H/2)**2 + (cc - W/2)**2) ** 0.5
    def name(self): return "V_center"


class V_CenterH(PotentialFunction):
    """Horizontal distance to center. Minimize -> horizontal center."""
    def compute(self, obj, grid, all_objects, config):
        _, cc = obj.centroid
        return abs(cc - grid.width / 2)
    def name(self): return "V_center_h"


class V_CenterV(PotentialFunction):
    """Vertical distance to center. Minimize -> vertical center."""
    def compute(self, obj, grid, all_objects, config):
        cr, _ = obj.centroid
        return abs(cr - grid.height / 2)
    def name(self): return "V_center_v"


# -----------------------------------------------------------------------------
# CATEGORY 3: CONTACT POTENTIALS (Object-to-object relationships)
# -----------------------------------------------------------------------------

class V_ContactDist(PotentialFunction):
    """Distance to nearest other non-background object."""
    def compute(self, obj, grid, all_objects, config):
        cr, cc = obj.centroid
        min_dist = float('inf')
        for other in all_objects:
            if other.object_id == obj.object_id: continue
            if other.color == config.background_color: continue
            or_, oc = other.centroid
            dist = ((cr - or_)**2 + (cc - oc)**2) ** 0.5
            min_dist = min(min_dist, dist)
        return min_dist if min_dist != float('inf') else 0.0
    def name(self): return "V_contact"


class V_ContactSameColor(PotentialFunction):
    """Distance to nearest object of SAME color."""
    def compute(self, obj, grid, all_objects, config):
        cr, cc = obj.centroid
        min_dist = float('inf')
        for other in all_objects:
            if other.object_id == obj.object_id: continue
            if other.color != obj.color: continue
            or_, oc = other.centroid
            dist = ((cr - or_)**2 + (cc - oc)**2) ** 0.5
            min_dist = min(min_dist, dist)
        return min_dist if min_dist != float('inf') else 0.0
    def name(self): return "V_contact_same"


class V_ContactDiffColor(PotentialFunction):
    """Distance to nearest object of DIFFERENT color."""
    def compute(self, obj, grid, all_objects, config):
        cr, cc = obj.centroid
        min_dist = float('inf')
        for other in all_objects:
            if other.object_id == obj.object_id: continue
            if other.color == obj.color: continue
            if other.color == config.background_color: continue
            or_, oc = other.centroid
            dist = ((cr - or_)**2 + (cc - oc)**2) ** 0.5
            min_dist = min(min_dist, dist)
        return min_dist if min_dist != float('inf') else 0.0
    def name(self): return "V_contact_diff"


class V_TouchCount(PotentialFunction):
    """Number of adjacent pixels touching other objects. Maximize -> stick together."""
    def compute(self, obj, grid, all_objects, config):
        data = grid.to_numpy()
        H, W = data.shape
        pixel_set = set(obj.pixels)
        touch_count = 0
        for r, c in obj.pixels:
            for dr, dc in [(-1,0), (1,0), (0,-1), (0,1)]:
                nr, nc = r + dr, c + dc
                if 0 <= nr < H and 0 <= nc < W:
                    if (nr, nc) not in pixel_set:
                        if data[nr, nc] != config.background_color and data[nr, nc] != obj.color:
                            touch_count += 1
        return -touch_count  # Negative so minimizing = maximizing touch
    def name(self): return "V_touch"


# -----------------------------------------------------------------------------
# CATEGORY 4: ALIGNMENT POTENTIALS (Relative positioning)
# -----------------------------------------------------------------------------

class V_AlignH(PotentialFunction):
    """Distance to horizontal alignment with nearest object."""
    def compute(self, obj, grid, all_objects, config):
        cr, _ = obj.centroid
        min_dist = float('inf')
        for other in all_objects:
            if other.object_id == obj.object_id: continue
            if other.color == config.background_color: continue
            or_, _ = other.centroid
            min_dist = min(min_dist, abs(cr - or_))
        return min_dist if min_dist != float('inf') else 0.0
    def name(self): return "V_align_h"


class V_AlignV(PotentialFunction):
    """Distance to vertical alignment with nearest object."""
    def compute(self, obj, grid, all_objects, config):
        _, cc = obj.centroid
        min_dist = float('inf')
        for other in all_objects:
            if other.object_id == obj.object_id: continue
            if other.color == config.background_color: continue
            _, oc = other.centroid
            min_dist = min(min_dist, abs(cc - oc))
        return min_dist if min_dist != float('inf') else 0.0
    def name(self): return "V_align_v"


class V_StackAbove(PotentialFunction):
    """Distance to being directly above another object."""
    def compute(self, obj, grid, all_objects, config):
        cr, cc = obj.centroid
        min_cost = float('inf')
        for other in all_objects:
            if other.object_id == obj.object_id: continue
            if other.color == config.background_color: continue
            or_, oc = other.centroid
            if cr < or_:  # obj is above other
                cost = abs(cc - oc) + abs(or_ - cr - obj.height)
                min_cost = min(min_cost, cost)
        return min_cost if min_cost != float('inf') else 10.0
    def name(self): return "V_stack_above"


class V_StackBelow(PotentialFunction):
    """Distance to being directly below another object."""
    def compute(self, obj, grid, all_objects, config):
        cr, cc = obj.centroid
        min_cost = float('inf')
        for other in all_objects:
            if other.object_id == obj.object_id: continue
            if other.color == config.background_color: continue
            or_, oc = other.centroid
            if cr > or_:  # obj is below other
                cost = abs(cc - oc) + abs(cr - or_ - other.height)
                min_cost = min(min_cost, cost)
        return min_cost if min_cost != float('inf') else 10.0
    def name(self): return "V_stack_below"


# -----------------------------------------------------------------------------
# CATEGORY 5: SHAPE POTENTIALS (Intrinsic object properties)
# -----------------------------------------------------------------------------

class V_Compactness(PotentialFunction):
    """How filled is the bounding box? Maximize -> solid shapes."""
    def compute(self, obj, grid, all_objects, config):
        return -obj.compactness  # Negative to maximize
    def name(self): return "V_compact"


class V_AspectSquare(PotentialFunction):
    """Distance from square aspect ratio."""
    def compute(self, obj, grid, all_objects, config):
        return abs(obj.aspect_ratio - 1.0)
    def name(self): return "V_square"


# -----------------------------------------------------------------------------
# CATEGORY 6: TOPOLOGY POTENTIALS (Structural relationships)
# -----------------------------------------------------------------------------

class V_Enclosure(PotentialFunction):
    """Is this object inside another object's bounding box?"""
    def compute(self, obj, grid, all_objects, config):
        r1, c1, r2, c2 = obj.bbox
        cr, cc = obj.centroid
        
        for other in all_objects:
            if other.object_id == obj.object_id: continue
            if other.color == config.background_color: continue
            if other.mass <= obj.mass: continue  # Only check larger objects
            
            or1, oc1, or2, oc2 = other.bbox
            # Check if obj is inside other's bbox
            if or1 <= r1 and r2 <= or2 and oc1 <= c1 and c2 <= oc2:
                return 0.0  # Already enclosed
            
            # Distance to being enclosed
            dist = max(0, or1 - r1) + max(0, r2 - or2) + max(0, oc1 - c1) + max(0, c2 - oc2)
            return dist
        
        return 10.0  # No enclosing object found
    def name(self): return "V_enclosed"


class V_Surround(PotentialFunction):
    """Distance to surrounding another object."""
    def compute(self, obj, grid, all_objects, config):
        r1, c1, r2, c2 = obj.bbox
        
        for other in all_objects:
            if other.object_id == obj.object_id: continue
            if other.color == config.background_color: continue
            if other.mass >= obj.mass: continue  # Only check smaller objects
            
            or1, oc1, or2, oc2 = other.bbox
            # Check if other is inside obj's bbox
            if r1 <= or1 and or2 <= r2 and c1 <= oc1 and oc2 <= c2:
                return 0.0  # Already surrounding
        
        return 10.0
    def name(self): return "V_surround"


# -----------------------------------------------------------------------------
# CATEGORY 7: COLOR-SPECIFIC POTENTIALS
# -----------------------------------------------------------------------------

class V_ColorDist(PotentialFunction):
    """Distance to nearest object of specific color."""
    def __init__(self, target_color: int):
        self.target_color = target_color
    
    def compute(self, obj, grid, all_objects, config):
        cr, cc = obj.centroid
        min_dist = float('inf')
        for other in all_objects:
            if other.color != self.target_color: continue
            if other.object_id == obj.object_id: continue
            or_, oc = other.centroid
            dist = ((cr - or_)**2 + (cc - oc)**2) ** 0.5
            min_dist = min(min_dist, dist)
        return min_dist if min_dist != float('inf') else 0.0
    
    def name(self): return f"V_color_{self.target_color}"


# -----------------------------------------------------------------------------
# CATEGORY 8: QUADRANT POTENTIALS (Which quadrant should object be in?)
# -----------------------------------------------------------------------------

class V_QuadrantTL(PotentialFunction):
    """Distance to top-left quadrant."""
    def compute(self, obj, grid, all_objects, config):
        cr, cc = obj.centroid
        H, W = grid.height, grid.width
        target_r, target_c = H/4, W/4
        return ((cr - target_r)**2 + (cc - target_c)**2) ** 0.5
    def name(self): return "V_quad_TL"


class V_QuadrantTR(PotentialFunction):
    """Distance to top-right quadrant."""
    def compute(self, obj, grid, all_objects, config):
        cr, cc = obj.centroid
        H, W = grid.height, grid.width
        target_r, target_c = H/4, 3*W/4
        return ((cr - target_r)**2 + (cc - target_c)**2) ** 0.5
    def name(self): return "V_quad_TR"


class V_QuadrantBL(PotentialFunction):
    """Distance to bottom-left quadrant."""
    def compute(self, obj, grid, all_objects, config):
        cr, cc = obj.centroid
        H, W = grid.height, grid.width
        target_r, target_c = 3*H/4, W/4
        return ((cr - target_r)**2 + (cc - target_c)**2) ** 0.5
    def name(self): return "V_quad_BL"


class V_QuadrantBR(PotentialFunction):
    """Distance to bottom-right quadrant."""
    def compute(self, obj, grid, all_objects, config):
        cr, cc = obj.centroid
        H, W = grid.height, grid.width
        target_r, target_c = 3*H/4, 3*W/4
        return ((cr - target_r)**2 + (cc - target_c)**2) ** 0.5
    def name(self): return "V_quad_BR"


# =============================================================================
# COMPOSITE POTENTIAL (THE HAMILTONIAN)
# =============================================================================

class CompositePotential:
    """H = sum(w_i * V_i) - The discovered physical law."""
    
    def __init__(self, potentials: List[PotentialFunction], weights: np.ndarray):
        self.potentials = potentials
        self.weights = weights
    
    def compute(self, obj: ARCObject, grid: ARCGrid, all_objects: List[ARCObject], config: ARCPhase81Config) -> float:
        total = 0.0
        for pot, w in zip(self.potentials, self.weights):
            if abs(w) > 0.01:
                total += w * pot.compute(obj, grid, all_objects, config)
        return total
    
    def gradient(self, obj: ARCObject, grid: ARCGrid, all_objects: List[ARCObject], config: ARCPhase81Config) -> Tuple[int, int]:
        """Find best direction to decrease potential."""
        H, W = grid.height, grid.width
        current = self.compute(obj, grid, all_objects, config)
        
        best_dir = (0, 0)
        best_decrease = 0.0
        
        for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
            new_pixels = [(r + dr, c + dc) for r, c in obj.pixels]
            if all(0 <= r < H and 0 <= c < W for r, c in new_pixels):
                moved_obj = ARCObject(obj.object_id, obj.color, new_pixels)
                new_potential = self.compute(moved_obj, grid, all_objects, config)
                decrease = current - new_potential
                if decrease > best_decrease:
                    best_decrease = decrease
                    best_dir = (dr, dc)
        
        return best_dir
    
    def signature(self) -> str:
        parts = []
        for pot, w in zip(self.potentials, self.weights):
            if abs(w) > 0.01:
                parts.append(f"{w:+.1f}*{pot.name()}")
        return " ".join(parts) if parts else "identity"


# =============================================================================
# SYSTEM RELAXATION (GRADIENT DESCENT)
# =============================================================================

def relax_system(
    grid: ARCGrid,
    potential: CompositePotential,
    target_color: int,
    config: ARCPhase81Config
) -> ARCGrid:
    """Iteratively relax objects of target_color to minimize potential."""
    data = grid.data.clone()
    H, W = data.shape
    
    for step in range(config.max_relax_steps):
        current_grid = ARCGrid(data)
        objects = detect_objects(current_grid, config)
        targets = [o for o in objects if o.color == target_color]
        
        if not targets:
            break
        
        moved_any = False
        
        for obj in targets:
            dr, dc = potential.gradient(obj, current_grid, objects, config)
            
            if dr == 0 and dc == 0:
                continue
            
            mask = obj.get_mask(H, W, data.device)
            can_move = True
            
            for r, c in obj.pixels:
                nr, nc = r + dr, c + dc
                if not (0 <= nr < H and 0 <= nc < W):
                    can_move = False
                    break
                if data[nr, nc] != config.background_color and not mask[nr, nc]:
                    can_move = False
                    break
            
            if can_move:
                data[mask] = config.background_color
                for r, c in obj.pixels:
                    data[r + dr, c + dc] = target_color
                moved_any = True
        
        if not moved_any:
            break
    
    return ARCGrid(data)


def relax_all_colors(grid: ARCGrid, potential: CompositePotential, config: ARCPhase81Config) -> ARCGrid:
    """Relax all non-background colors."""
    result = grid.clone()
    for color in range(1, config.num_colors):
        if (result.data == color).any():
            result = relax_system(result, potential, color, config)
    return result


# =============================================================================
# ENERGY COMPUTATION
# =============================================================================

def compute_defect_energy(pred: ARCGrid, target: ARCGrid) -> float:
    if pred.shape != target.shape:
        return 1000.0 + abs(pred.height - target.height) + abs(pred.width - target.width)
    return (pred.data != target.data).float().sum().item() / target.data.numel()


def evaluate_weights(
    weights: np.ndarray,
    potentials: List[PotentialFunction],
    examples: List[ARCExample],
    config: ARCPhase81Config
) -> float:
    potential = CompositePotential(potentials, weights)
    total = 0.0
    for ex in examples:
        result = relax_all_colors(ex.input_grid, potential, config)
        total += compute_defect_energy(result, ex.output_grid)
    return total / len(examples)


# =============================================================================
# PHYSICIST SOLVER (Discovers the Hamiltonian)
# =============================================================================

class PhysicistSolver:
    """
    The Physicist: Discovers the physical law H = sum(w_i * V_i) from observations.
    """
    
    def __init__(self, config: ARCPhase81Config):
        self.config = config
        self.potentials = self._build_potential_library()
        printfl(f"   Potential Library: {len(self.potentials)} potentials")
    
    def _build_potential_library(self) -> List[PotentialFunction]:
        """Build the full vocabulary of physical laws."""
        potentials = [
            # Boundary (5)
            V_BoundaryDist(),
            V_TopEdge(),
            V_BottomEdge(),
            V_LeftEdge(),
            V_RightEdge(),
            # Center (3)
            V_CenterDist(),
            V_CenterH(),
            V_CenterV(),
            # Contact (4)
            V_ContactDist(),
            V_ContactSameColor(),
            V_ContactDiffColor(),
            V_TouchCount(),
            # Alignment (4)
            V_AlignH(),
            V_AlignV(),
            V_StackAbove(),
            V_StackBelow(),
            # Topology (2)
            V_Enclosure(),
            V_Surround(),
            # Quadrants (4)
            V_QuadrantTL(),
            V_QuadrantTR(),
            V_QuadrantBL(),
            V_QuadrantBR(),
        ]
        
        # Color-specific (add for colors 1-4)
        for c in range(1, 5):
            potentials.append(V_ColorDist(c))
        
        return potentials
    
    def solve_task(self, task: ARCTask, verbose: bool = False) -> Dict:
        """Find the Hamiltonian that explains all training examples."""
        examples = task.train_examples
        n = len(self.potentials)
        
        # Track best
        best_weights = np.zeros(n)
        best_energy = evaluate_weights(best_weights, self.potentials, examples, self.config)
        
        if verbose:
            printfl(f"   Baseline (identity): E={best_energy:.4f}")
        
        # Phase 1: Single potentials
        if verbose:
            printfl(f"   Searching single potentials...")
        
        for i, pot in enumerate(self.potentials):
            for sign in [-1.0, 1.0]:
                w = np.zeros(n)
                w[i] = sign
                e = evaluate_weights(w, self.potentials, examples, self.config)
                
                if e < best_energy:
                    if verbose:
                        printfl(f"      {sign:+.0f}*{pot.name()}: E={e:.4f}")
                    best_energy = e
                    best_weights = w.copy()
        
        # Phase 2: Pairs of potentials (if single not perfect)
        if best_energy > self.config.energy_threshold:
            if verbose:
                printfl(f"   Searching pairs...")
            
            # Only search promising pairs (top 8 potentials)
            for i in range(min(n, 12)):
                for j in range(i+1, min(n, 12)):
                    for s1 in [-1.0, 1.0]:
                        for s2 in [-1.0, 1.0]:
                            w = np.zeros(n)
                            w[i], w[j] = s1, s2
                            e = evaluate_weights(w, self.potentials, examples, self.config)
                            if e < best_energy:
                                if verbose:
                                    printfl(f"      {s1:+.0f}*{self.potentials[i].name()} {s2:+.0f}*{self.potentials[j].name()}: E={e:.4f}")
                                best_energy = e
                                best_weights = w.copy()
        
        # Phase 3: Triplets (only if still not solved)
        if best_energy > self.config.consistency_threshold and best_energy < 0.3:
            if verbose:
                printfl(f"   Searching triplets...")
            
            for i in range(min(n, 8)):
                for j in range(i+1, min(n, 8)):
                    for k in range(j+1, min(n, 8)):
                        for s1 in [-1.0, 1.0]:
                            for s2 in [-1.0, 1.0]:
                                for s3 in [-1.0, 1.0]:
                                    w = np.zeros(n)
                                    w[i], w[j], w[k] = s1, s2, s3
                                    e = evaluate_weights(w, self.potentials, examples, self.config)
                                    if e < best_energy:
                                        if verbose:
                                            printfl(f"      triplet: E={e:.4f}")
                                        best_energy = e
                                        best_weights = w.copy()
        
        # Build result
        best_potential = CompositePotential(self.potentials, best_weights)
        
        train_energies = []
        for ex in examples:
            result = relax_all_colors(ex.input_grid, best_potential, self.config)
            train_energies.append(compute_defect_energy(result, ex.output_grid))
        
        test_energies = []
        for ex in task.test_examples:
            result = relax_all_colors(ex.input_grid, best_potential, self.config)
            test_energies.append(compute_defect_energy(result, ex.output_grid))
        
        avg_train = np.mean(train_energies)
        is_consistent = all(e < self.config.consistency_threshold for e in train_energies)
        is_perfect = avg_train < self.config.energy_threshold
        
        return {
            'task_id': task.task_id,
            'hamiltonian': best_potential.signature(),
            'weights': best_weights,
            'avg_train_energy': avg_train,
            'train_energies': train_energies,
            'avg_test_energy': np.mean(test_energies) if test_energies else 0,
            'test_energies': test_energies,
            'is_consistent': is_consistent,
            'is_perfect': is_perfect
        }


# =============================================================================
# EVALUATION
# =============================================================================

def run_evaluation(data_path: str, config: ARCPhase81Config, num_tasks: int = 30):
    printfl("=" * 70)
    printfl("ARC-SGC Phase 8.1: Scaling the Physics")
    printfl("=" * 70)
    printfl("Paradigm: The Physicist discovers H = sum(w_i * V_i)")
    
    tasks = load_arc_tasks(data_path, config.device, num_tasks)
    printfl(f"\nLoaded {len(tasks)} tasks")
    
    if not tasks:
        printfl("No tasks found!")
        return []
    
    printfl("\nBuilding Physicist Solver...")
    solver = PhysicistSolver(config)
    
    all_results = []
    perfect_tasks = []
    consistent_tasks = []
    
    for i, task in enumerate(tasks):
        printfl(f"\n{'='*60}")
        printfl(f"Task {i+1}/{len(tasks)}: {task.task_id}")
        printfl(f"  Examples: {len(task.train_examples)} train, {len(task.test_examples)} test")
        
        result = solver.solve_task(task, verbose=True)
        all_results.append(result)
        
        if result['is_perfect']:
            status = "[PERFECT]"
            perfect_tasks.append(result)
        elif result['is_consistent']:
            status = "[CONSISTENT]"
            consistent_tasks.append(result)
        elif result['avg_train_energy'] < 0.3:
            status = "[partial]"
        else:
            status = "[failed]"
        
        printfl(f"\n  {status} H = {result['hamiltonian']}")
        printfl(f"  Train: {[f'{e:.4f}' for e in result['train_energies']]}")
        if result['test_energies']:
            printfl(f"  Test:  {[f'{e:.4f}' for e in result['test_energies']]}")
        
        # Progress summary every 10 tasks
        if (i + 1) % 10 == 0:
            printfl(f"\n  --- Progress: {len(perfect_tasks)} perfect, {len(consistent_tasks)} consistent ---")
    
    # Final summary
    printfl("\n" + "=" * 70)
    printfl("FINAL SUMMARY: Phase 8.1 - The Physicist")
    printfl("=" * 70)
    
    perfect = len(perfect_tasks)
    consistent = len(consistent_tasks)
    partial = sum(1 for r in all_results if not r['is_consistent'] and r['avg_train_energy'] < 0.3)
    failed = sum(1 for r in all_results if r['avg_train_energy'] >= 0.3)
    
    avg_energy = np.mean([r['avg_train_energy'] for r in all_results])
    
    printfl(f"Tasks evaluated: {len(all_results)}")
    printfl(f"  PERFECT    (E < 0.0001):  {perfect}")
    printfl(f"  CONSISTENT (all < 0.005): {consistent}")
    printfl(f"  PARTIAL    (avg < 0.3):   {partial}")
    printfl(f"  FAILED     (avg >= 0.3):  {failed}")
    printfl(f"  Average energy: {avg_energy:.4f}")
    
    if perfect > 0 or consistent > 0:
        printfl(f"\n=== BREAKTHROUGHS ===")
        for r in perfect_tasks:
            printfl(f"  [PERFECT] {r['task_id']}: H = {r['hamiltonian']}")
        for r in consistent_tasks:
            printfl(f"  [CONSISTENT] {r['task_id']}: H = {r['hamiltonian']}")
    
    printfl(f"\n=== Best Hamiltonians ===")
    for r in sorted(all_results, key=lambda x: x['avg_train_energy'])[:10]:
        status = "PERFECT" if r['is_perfect'] else ("CONS" if r['is_consistent'] else "part")
        printfl(f"  [{status}] {r['task_id']}: H = {r['hamiltonian'][:40]}... E={r['avg_train_energy']:.4f}")
    
    return all_results


def main():
    config = ARCPhase81Config()
    paths = ["data/arc/training", "C:/Lean4 Projects/data/arc/training"]
    arc_path = next((p for p in paths if Path(p).exists()), None)
    
    if arc_path:
        # Run on 100 tasks to find more solvable ones
        return run_evaluation(arc_path, config, num_tasks=30)
    else:
        printfl("ARC data not found!")
        return []


if __name__ == "__main__":
    main()
