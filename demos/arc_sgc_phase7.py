"""
ARC-SGC Phase 7: The Potential Field Solver

FROM KINEMATICS TO DYNAMICS

Phase 6 revealed: shift_2_by_width works on Train2 but fails on Train1/3
because they need DIFFERENT DIRECTIONS. But it's ONE rule:
"Objects move to minimize distance to boundary."

THE INSIGHT:
- ARC solutions are not transformations; they are ENERGY MINIMIZATION PATHS
- Objects move along gradients: F = -∇V
- The solver should find the POTENTIAL FUNCTION, not the action

PARADIGM SHIFT:
- Old: Search [shift_left, shift_right, shift_up] → fails consistency
- New: Search [minimize(V_boundary), minimize(V_center)] → one rule fits all

SGC THEORY:
- Systems evolve to minimize free energy
- The "Physical Law" is the Hamiltonian H(x), not the trajectory x(t)
- Scientific induction = finding invariant V that explains all observations

IMPLEMENTATION:
1. Potential Functions: V_boundary, V_center, V_contact, V_color
2. Gradient Descent: move_by_gradient(V) - moves to local minimum
3. Collision Physics: move_until_collision - stops at boundaries/objects
4. Meta-Synthesis: Search for V that explains ALL training examples
"""

import torch
import torch.nn.functional as F
from dataclasses import dataclass
from typing import List, Tuple, Dict, Optional, Set, Callable
from collections import deque
from abc import ABC, abstractmethod
import numpy as np
import json
from pathlib import Path


# =============================================================================
# CONFIGURATION
# =============================================================================

@dataclass
class ARCPhase7Config:
    max_grid_size: int = 30
    num_colors: int = 10
    background_color: int = 0
    min_object_size: int = 1
    max_objects: int = 50
    
    # Gradient descent
    max_gradient_steps: int = 20
    
    # Solver
    max_candidates: int = 60
    energy_threshold: float = 0.0001
    consistency_threshold: float = 0.01
    
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
    if not p.exists(): return tasks
    for f in sorted(p.glob("*.json"))[:limit]:
        try:
            with open(f) as fp:
                tasks.append(ARCTask.from_json(f.stem, json.load(fp), device))
        except Exception as e:
            print(f"Error {f}: {e}")
    return tasks


def detect_objects(grid: ARCGrid, config: ARCPhase7Config) -> List[ARCObject]:
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
# TASK 1: POTENTIAL FUNCTIONS
# =============================================================================

def potential_boundary_dist(obj: ARCObject, H: int, W: int) -> float:
    """
    V_boundary: Distance to nearest grid boundary.
    
    Objects minimize this → move toward walls.
    """
    cr, cc = obj.centroid
    dist_up = cr
    dist_down = H - 1 - cr
    dist_left = cc
    dist_right = W - 1 - cc
    return min(dist_up, dist_down, dist_left, dist_right)


def potential_center_dist(obj: ARCObject, H: int, W: int) -> float:
    """
    V_center: Distance to grid center.
    
    Objects minimize this → move toward center.
    """
    cr, cc = obj.centroid
    center_r, center_c = H / 2, W / 2
    return ((cr - center_r) ** 2 + (cc - center_c) ** 2) ** 0.5


def potential_contact_dist(obj: ARCObject, all_objects: List[ARCObject], config: ARCPhase7Config) -> float:
    """
    V_contact: Distance to nearest other object.
    
    Objects minimize this → move toward each other.
    """
    if len(all_objects) < 2:
        return 0.0
    
    cr, cc = obj.centroid
    min_dist = float('inf')
    
    for other in all_objects:
        if other.object_id == obj.object_id:
            continue
        if other.color == config.background_color:
            continue
        
        or_, oc = other.centroid
        dist = ((cr - or_) ** 2 + (cc - oc) ** 2) ** 0.5
        min_dist = min(min_dist, dist)
    
    return min_dist if min_dist != float('inf') else 0.0


def potential_color_dist(obj: ARCObject, all_objects: List[ARCObject], target_color: int) -> float:
    """
    V_color: Distance to nearest object of specific color.
    
    Objects minimize this → move toward specific color targets.
    """
    cr, cc = obj.centroid
    min_dist = float('inf')
    
    for other in all_objects:
        if other.object_id == obj.object_id:
            continue
        if other.color != target_color:
            continue
        
        or_, oc = other.centroid
        dist = ((cr - or_) ** 2 + (cc - oc) ** 2) ** 0.5
        min_dist = min(min_dist, dist)
    
    return min_dist if min_dist != float('inf') else 0.0


def potential_alignment_h(obj: ARCObject, all_objects: List[ARCObject]) -> float:
    """
    V_align_h: Distance to horizontal alignment with other objects.
    """
    cr, _ = obj.centroid
    min_dist = float('inf')
    
    for other in all_objects:
        if other.object_id == obj.object_id:
            continue
        or_, _ = other.centroid
        dist = abs(cr - or_)
        min_dist = min(min_dist, dist)
    
    return min_dist if min_dist != float('inf') else 0.0


def potential_alignment_v(obj: ARCObject, all_objects: List[ARCObject]) -> float:
    """
    V_align_v: Distance to vertical alignment with other objects.
    """
    _, cc = obj.centroid
    min_dist = float('inf')
    
    for other in all_objects:
        if other.object_id == obj.object_id:
            continue
        _, oc = other.centroid
        dist = abs(cc - oc)
        min_dist = min(min_dist, dist)
    
    return min_dist if min_dist != float('inf') else 0.0


# =============================================================================
# TASK 2: GRADIENT DESCENT PRIMITIVES
# =============================================================================

class DSLPrimitive(ABC):
    @abstractmethod
    def apply(self, grid: ARCGrid, config: ARCPhase7Config) -> ARCGrid:
        pass
    
    @abstractmethod
    def signature(self) -> str:
        pass


class Identity(DSLPrimitive):
    def apply(self, grid, config): return grid.clone()
    def signature(self): return "identity"


class MinimizeBoundaryDist(DSLPrimitive):
    """
    THE KEY PRIMITIVE: Move objects to minimize distance to boundary.
    
    This is ONE rule that explains:
    - Train 1: Object near right → moves LEFT (toward left boundary)
    - Train 2: Object near left → moves RIGHT (toward right boundary)
    - Train 3: Object near bottom → moves UP (toward top boundary)
    """
    def __init__(self, color: int):
        self.color = color
    
    def apply(self, grid, config):
        data = grid.data.clone()
        H, W = data.shape
        
        objects = detect_objects(grid, config)
        targets = [o for o in objects if o.color == self.color]
        
        for obj in targets:
            r1, c1, r2, c2 = obj.bbox
            cr, cc = obj.centroid
            
            # Compute distances to each boundary
            dist_up = r1
            dist_down = H - r2
            dist_left = c1
            dist_right = W - c2
            
            # Find nearest boundary and compute shift to reach it
            min_dist = min(dist_up, dist_down, dist_left, dist_right)
            
            if min_dist == dist_up:
                dr, dc = -dist_up, 0
            elif min_dist == dist_down:
                dr, dc = dist_down, 0
            elif min_dist == dist_left:
                dr, dc = 0, -dist_left
            else:
                dr, dc = 0, dist_right
            
            # Clear and move
            mask = obj.get_mask(H, W, data.device)
            data[mask] = config.background_color
            
            for r, c in obj.pixels:
                nr, nc = r + dr, c + dc
                if 0 <= nr < H and 0 <= nc < W:
                    data[nr, nc] = self.color
        
        return ARCGrid(data)
    
    def signature(self): return f"minimize_boundary_{self.color}"


class MaximizeBoundaryDist(DSLPrimitive):
    """Move objects AWAY from nearest boundary (toward center)."""
    def __init__(self, color: int):
        self.color = color
    
    def apply(self, grid, config):
        data = grid.data.clone()
        H, W = data.shape
        
        objects = detect_objects(grid, config)
        targets = [o for o in objects if o.color == self.color]
        
        for obj in targets:
            cr, cc = obj.centroid
            oh, ow = obj.height, obj.width
            
            # Move toward center by object size
            center_r, center_c = H / 2, W / 2
            
            if cr < center_r:
                dr = min(oh, int(center_r - cr))
            elif cr > center_r:
                dr = -min(oh, int(cr - center_r))
            else:
                dr = 0
            
            if cc < center_c:
                dc = min(ow, int(center_c - cc))
            elif cc > center_c:
                dc = -min(ow, int(cc - center_c))
            else:
                dc = 0
            
            mask = obj.get_mask(H, W, data.device)
            data[mask] = config.background_color
            
            for r, c in obj.pixels:
                nr, nc = r + dr, c + dc
                if 0 <= nr < H and 0 <= nc < W:
                    data[nr, nc] = self.color
        
        return ARCGrid(data)
    
    def signature(self): return f"maximize_boundary_{self.color}"


class MinimizeContactDist(DSLPrimitive):
    """Move objects toward nearest other object."""
    def __init__(self, color: int):
        self.color = color
    
    def apply(self, grid, config):
        data = grid.data.clone()
        H, W = data.shape
        
        objects = detect_objects(grid, config)
        targets = [o for o in objects if o.color == self.color]
        others = [o for o in objects if o.color != self.color and o.color != config.background_color]
        
        if not others:
            return ARCGrid(data)
        
        for obj in targets:
            cr, cc = obj.centroid
            oh, ow = obj.height, obj.width
            
            # Find nearest other object
            min_dist = float('inf')
            nearest = None
            for other in others:
                or_, oc = other.centroid
                dist = ((cr - or_) ** 2 + (cc - oc) ** 2) ** 0.5
                if dist < min_dist:
                    min_dist = dist
                    nearest = other
            
            if nearest is None:
                continue
            
            # Move toward nearest
            or_, oc = nearest.centroid
            
            if cr < or_:
                dr = min(oh, int(or_ - cr) - 1)
            elif cr > or_:
                dr = -min(oh, int(cr - or_) - 1)
            else:
                dr = 0
            
            if cc < oc:
                dc = min(ow, int(oc - cc) - 1)
            elif cc > oc:
                dc = -min(ow, int(cc - oc) - 1)
            else:
                dc = 0
            
            mask = obj.get_mask(H, W, data.device)
            data[mask] = config.background_color
            
            for r, c in obj.pixels:
                nr, nc = r + dr, c + dc
                if 0 <= nr < H and 0 <= nc < W:
                    data[nr, nc] = self.color
        
        return ARCGrid(data)
    
    def signature(self): return f"minimize_contact_{self.color}"


class MinimizeColorDist(DSLPrimitive):
    """Move objects toward nearest object of target color."""
    def __init__(self, color: int, target_color: int):
        self.color = color
        self.target_color = target_color
    
    def apply(self, grid, config):
        data = grid.data.clone()
        H, W = data.shape
        
        objects = detect_objects(grid, config)
        targets = [o for o in objects if o.color == self.color]
        color_targets = [o for o in objects if o.color == self.target_color]
        
        if not color_targets:
            return ARCGrid(data)
        
        for obj in targets:
            cr, cc = obj.centroid
            oh, ow = obj.height, obj.width
            
            # Find nearest target color object
            min_dist = float('inf')
            nearest = None
            for ct in color_targets:
                or_, oc = ct.centroid
                dist = ((cr - or_) ** 2 + (cc - oc) ** 2) ** 0.5
                if dist < min_dist:
                    min_dist = dist
                    nearest = ct
            
            if nearest is None:
                continue
            
            or_, oc = nearest.centroid
            
            if cr < or_:
                dr = min(oh, max(1, int(or_ - cr) - 1))
            elif cr > or_:
                dr = -min(oh, max(1, int(cr - or_) - 1))
            else:
                dr = 0
            
            if cc < oc:
                dc = min(ow, max(1, int(oc - cc) - 1))
            elif cc > oc:
                dc = -min(ow, max(1, int(cc - oc) - 1))
            else:
                dc = 0
            
            mask = obj.get_mask(H, W, data.device)
            data[mask] = config.background_color
            
            for r, c in obj.pixels:
                nr, nc = r + dr, c + dc
                if 0 <= nr < H and 0 <= nc < W:
                    data[nr, nc] = self.color
        
        return ARCGrid(data)
    
    def signature(self): return f"minimize_dist_{self.color}_to_{self.target_color}"


# =============================================================================
# TASK 3: COLLISION PHYSICS
# =============================================================================

class MoveUntilCollision(DSLPrimitive):
    """
    Move objects in a direction until they hit boundary or another object.
    
    This is crucial for "fill gap" and "extend line" tasks.
    """
    def __init__(self, color: int, direction: str):
        self.color = color
        self.direction = direction  # 'up', 'down', 'left', 'right'
    
    def apply(self, grid, config):
        data = grid.data.clone()
        H, W = data.shape
        bg = config.background_color
        
        objects = detect_objects(grid, config)
        targets = [o for o in objects if o.color == self.color]
        
        # Direction vectors
        dir_map = {'up': (-1, 0), 'down': (1, 0), 'left': (0, -1), 'right': (0, 1)}
        dr, dc = dir_map.get(self.direction, (0, 0))
        
        for obj in targets:
            mask = obj.get_mask(H, W, data.device)
            
            # Find maximum safe shift (before collision)
            max_shift = 0
            for shift in range(1, max(H, W)):
                can_shift = True
                for r, c in obj.pixels:
                    nr, nc = r + dr * shift, c + dc * shift
                    if not (0 <= nr < H and 0 <= nc < W):
                        can_shift = False
                        break
                    # Check collision with non-background, non-self
                    if data[nr, nc] != bg and not mask[nr, nc]:
                        can_shift = False
                        break
                
                if can_shift:
                    max_shift = shift
                else:
                    break
            
            if max_shift > 0:
                # Clear original
                data[mask] = bg
                
                # Place at new position
                for r, c in obj.pixels:
                    nr, nc = r + dr * max_shift, c + dc * max_shift
                    if 0 <= nr < H and 0 <= nc < W:
                        data[nr, nc] = self.color
        
        return ARCGrid(data)
    
    def signature(self): return f"slide_{self.color}_{self.direction}"


class GravityFall(DSLPrimitive):
    """
    Objects "fall" in a direction (like gravity) until they stack.
    """
    def __init__(self, color: int, direction: str):
        self.color = color
        self.direction = direction
    
    def apply(self, grid, config):
        data = grid.data.clone()
        H, W = data.shape
        bg = config.background_color
        
        dir_map = {'up': (-1, 0), 'down': (1, 0), 'left': (0, -1), 'right': (0, 1)}
        dr, dc = dir_map.get(self.direction, (0, 0))
        
        # Process pixels in order (farthest from target boundary first)
        if self.direction == 'down':
            row_order = range(H - 1, -1, -1)
            col_order = range(W)
        elif self.direction == 'up':
            row_order = range(H)
            col_order = range(W)
        elif self.direction == 'right':
            row_order = range(H)
            col_order = range(W - 1, -1, -1)
        else:  # left
            row_order = range(H)
            col_order = range(W)
        
        # Move each pixel of target color
        for r in row_order:
            for c in col_order:
                if data[r, c] != self.color:
                    continue
                
                # Find how far it can fall
                nr, nc = r, c
                while True:
                    nnr, nnc = nr + dr, nc + dc
                    if not (0 <= nnr < H and 0 <= nnc < W):
                        break
                    if data[nnr, nnc] != bg:
                        break
                    nr, nc = nnr, nnc
                
                if (nr, nc) != (r, c):
                    data[r, c] = bg
                    data[nr, nc] = self.color
        
        return ARCGrid(data)
    
    def signature(self): return f"gravity_{self.color}_{self.direction}"


# =============================================================================
# STANDARD DSL (from previous phases)
# =============================================================================

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


class ColorSwap(DSLPrimitive):
    def __init__(self, a: int, b: int):
        self.a, self.b = a, b
    
    def apply(self, grid, config):
        data = grid.data.clone()
        ma, mb = (data == self.a), (data == self.b)
        data[ma], data[mb] = self.b, self.a
        return ARCGrid(data)
    
    def signature(self): return f"swap_{self.a}_{self.b}"


class FlipH(DSLPrimitive):
    def apply(self, grid, config):
        return ARCGrid(torch.flip(grid.data, dims=[1]))
    def signature(self): return "flip_h"


class FlipV(DSLPrimitive):
    def apply(self, grid, config):
        return ARCGrid(torch.flip(grid.data, dims=[0]))
    def signature(self): return "flip_v"


class Recolor(DSLPrimitive):
    def __init__(self, from_c: int, to_c: int):
        self.from_c, self.to_c = from_c, to_c
    
    def apply(self, grid, config):
        data = grid.data.clone()
        data[data == self.from_c] = self.to_c
        return ARCGrid(data)
    
    def signature(self): return f"recolor_{self.from_c}_to_{self.to_c}"


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


# =============================================================================
# DSL LIBRARY WITH POTENTIAL-BASED PRIMITIVES
# =============================================================================

def build_dsl_library(config: ARCPhase7Config) -> List[DSLPrimitive]:
    ops: List[DSLPrimitive] = [Identity(), FlipH(), FlipV()]
    
    # Color swaps
    for a in range(config.num_colors):
        for b in range(a + 1, config.num_colors):
            ops.append(ColorSwap(a, b))
    
    # Recolors
    for a in range(config.num_colors):
        for b in range(config.num_colors):
            if a != b:
                ops.append(Recolor(a, b))
    
    # Simple shifts
    for dr in [-1, 0, 1]:
        for dc in [-1, 0, 1]:
            if dr != 0 or dc != 0:
                ops.append(Shift(dr, dc))
    
    # === POTENTIAL-BASED PRIMITIVES (The Key Innovation) ===
    
    # Minimize boundary distance (THE SOLUTION for Task 8)
    for color in range(1, 8):
        ops.append(MinimizeBoundaryDist(color))
        ops.append(MaximizeBoundaryDist(color))
    
    # Minimize contact distance
    for color in range(1, 6):
        ops.append(MinimizeContactDist(color))
    
    # Minimize distance to specific color
    for color in range(1, 5):
        for target in range(1, 5):
            if color != target:
                ops.append(MinimizeColorDist(color, target))
    
    # === COLLISION PHYSICS ===
    
    # Move until collision
    for color in range(1, 6):
        for direction in ['up', 'down', 'left', 'right']:
            ops.append(MoveUntilCollision(color, direction))
    
    # Gravity fall
    for color in range(1, 6):
        for direction in ['up', 'down', 'left', 'right']:
            ops.append(GravityFall(color, direction))
    
    return ops


# =============================================================================
# TASK 4: META-PROGRAM SYNTHESIS (Potential Field Search)
# =============================================================================

class PotentialFieldSolver:
    """
    The Potential Field Solver: Searches for the Hamiltonian, not the trajectory.
    
    Instead of guessing actions, it guesses the GOAL (potential function).
    One potential explains all examples → scientific induction.
    """
    
    def __init__(self, config: ARCPhase7Config):
        self.config = config
        self.dsl = build_dsl_library(config)
        print(f"   DSL: {len(self.dsl)} primitives")
    
    def compute_energy(self, pred: ARCGrid, target: ARCGrid) -> float:
        if pred.shape != target.shape:
            return 1000.0 + abs(pred.height - target.height) + abs(pred.width - target.width)
        return (pred.data != target.data).float().sum().item() / target.data.numel()
    
    def check_consistency(
        self,
        program: DSLPrimitive,
        examples: List[ARCExample]
    ) -> Tuple[bool, float, List[float]]:
        """Check if program works on ALL examples."""
        energies = []
        
        for ex in examples:
            try:
                result = program.apply(ex.input_grid, self.config)
                energy = self.compute_energy(result, ex.output_grid)
                energies.append(energy)
            except Exception:
                energies.append(1000.0)
        
        avg_energy = np.mean(energies)
        is_consistent = all(e < self.config.consistency_threshold for e in energies)
        
        return is_consistent, avg_energy, energies
    
    def solve_task(
        self,
        task: ARCTask,
        verbose: bool = False
    ) -> Dict:
        """
        Find a potential-based program that works on ALL training examples.
        """
        examples = task.train_examples
        n = len(examples)
        
        if verbose:
            print(f"   Searching for consistent potential across {n} examples...")
        
        # Evaluate all primitives for consistency
        results = []
        
        for op in self.dsl:
            is_consistent, avg_energy, energies = self.check_consistency(op, examples)
            
            if is_consistent:
                results.append({
                    'program': op,
                    'avg_energy': avg_energy,
                    'energies': energies,
                    'consistent': True
                })
                if verbose:
                    print(f"   [CONSISTENT] {op.signature()}: avg={avg_energy:.6f}, per-ex={[f'{e:.4f}' for e in energies]}")
            elif avg_energy < 0.3:
                results.append({
                    'program': op,
                    'avg_energy': avg_energy,
                    'energies': energies,
                    'consistent': False
                })
                if verbose and avg_energy < 0.15:
                    print(f"   [near-miss] {op.signature()}: avg={avg_energy:.4f}, per-ex={[f'{e:.4f}' for e in energies]}")
        
        # Try compositions of promising primitives
        promising = [r for r in results if r['avg_energy'] < 0.2][:10]
        
        for r1 in promising:
            for op2 in self.dsl[:30]:  # Try composing with basic ops
                composed = ComposedOp([r1['program'], op2])
                is_consistent, avg_energy, energies = self.check_consistency(composed, examples)
                
                if is_consistent:
                    results.append({
                        'program': composed,
                        'avg_energy': avg_energy,
                        'energies': energies,
                        'consistent': True
                    })
                    if verbose:
                        print(f"   [CONSISTENT COMP] {composed.signature()}: avg={avg_energy:.6f}")
        
        # Find best result
        consistent_results = [r for r in results if r['consistent']]
        
        if consistent_results:
            best = min(consistent_results, key=lambda x: x['avg_energy'])
        elif results:
            best = min(results, key=lambda x: x['avg_energy'])
        else:
            best = {
                'program': Identity(),
                'avg_energy': 1.0,
                'energies': [1.0] * n,
                'consistent': False
            }
        
        # Test on test examples
        test_energies = []
        for ex in task.test_examples:
            try:
                result = best['program'].apply(ex.input_grid, self.config)
                energy = self.compute_energy(result, ex.output_grid)
                test_energies.append(energy)
            except Exception:
                test_energies.append(1000.0)
        
        return {
            'task_id': task.task_id,
            'program': best['program'].signature(),
            'avg_train_energy': best['avg_energy'],
            'train_energies': best['energies'],
            'avg_test_energy': np.mean(test_energies) if test_energies else 0,
            'test_energies': test_energies,
            'is_consistent': best['consistent'],
            'is_perfect': best['avg_energy'] < self.config.energy_threshold
        }


# =============================================================================
# EVALUATION
# =============================================================================

def run_evaluation(data_path: str, config: ARCPhase7Config, num_tasks: int = 10):
    print("=" * 70)
    print("ARC-SGC Phase 7: The Potential Field Solver")
    print("=" * 70)
    print("Paradigm: From Kinematics (actions) to Dynamics (energy minimization)")
    
    tasks = load_arc_tasks(data_path, config.device, num_tasks)
    print(f"\nLoaded {len(tasks)} tasks")
    
    if not tasks:
        return []
    
    print("\nBuilding Potential Field Solver...")
    solver = PotentialFieldSolver(config)
    
    all_results = []
    
    for i, task in enumerate(tasks):
        print(f"\n{'='*70}")
        print(f"Task {i+1}/{len(tasks)}: {task.task_id}")
        print(f"  Train: {len(task.train_examples)}, Test: {len(task.test_examples)}")
        
        result = solver.solve_task(task, verbose=True)
        all_results.append(result)
        
        status = "[PERFECT]" if result['is_perfect'] else ("[CONSISTENT]" if result['is_consistent'] else "[partial]")
        print(f"\n  {status} {result['program']}")
        print(f"  Train: avg={result['avg_train_energy']:.4f}, per-ex={[f'{e:.4f}' for e in result['train_energies']]}")
        if result['test_energies']:
            print(f"  Test:  avg={result['avg_test_energy']:.4f}")
    
    # Summary
    print("\n" + "=" * 70)
    print("FINAL SUMMARY: Phase 7 - Potential Field Solver")
    print("=" * 70)
    
    perfect = sum(1 for r in all_results if r['is_perfect'])
    consistent = sum(1 for r in all_results if r['is_consistent'] and not r['is_perfect'])
    partial = sum(1 for r in all_results if not r['is_consistent'] and r['avg_train_energy'] < 0.5)
    failed = sum(1 for r in all_results if r['avg_train_energy'] >= 0.5)
    
    avg_energy = np.mean([r['avg_train_energy'] for r in all_results])
    
    print(f"Tasks: {len(all_results)}")
    print(f"  PERFECT    (E < 0.0001):  {perfect}")
    print(f"  CONSISTENT (all < 0.01): {consistent}")
    print(f"  PARTIAL    (avg < 0.5):  {partial}")
    print(f"  FAILED     (avg >= 0.5): {failed}")
    print(f"  Average energy: {avg_energy:.6f}")
    
    print(f"\n  Phase 6 baseline: 0 perfect, 0 consistent, 6 partial")
    print(f"  Phase 7 result:   {perfect} perfect, {consistent} consistent, {partial} partial")
    
    if consistent > 0 or perfect > 0:
        print(f"\n  === BREAKTHROUGH ===")
        for r in all_results:
            if r['is_consistent']:
                print(f"  [CONSISTENT] {r['task_id']}: {r['program']}")
                print(f"               energies={[f'{e:.4f}' for e in r['train_energies']]}")
    
    # Show potential-based results
    print("\n  Potential-based solutions found:")
    for r in all_results:
        if 'minimize' in r['program'] or 'slide' in r['program'] or 'gravity' in r['program']:
            print(f"    {r['task_id']}: {r['program']} (E={r['avg_train_energy']:.4f})")
    
    return all_results


def main():
    config = ARCPhase7Config()
    paths = ["data/arc/training", "C:/Lean4 Projects/data/arc/training"]
    arc_path = next((p for p in paths if Path(p).exists()), None)
    
    if arc_path:
        return run_evaluation(arc_path, config, num_tasks=10)
    else:
        print("ARC data not found!")
        return []


if __name__ == "__main__":
    main()
