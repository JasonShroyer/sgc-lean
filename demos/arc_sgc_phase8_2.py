"""
ARC-SGC Phase 8.2: Unified Physics (Movement + Color)

DIAGNOSIS FROM PHASE 8.1:
- Task 8 SOLVED with H = V_contact (pure movement)
- Many tasks show "identity" = movement doesn't help
- These tasks need COLOR TRANSFORMATIONS

THE UNIFIED PHYSICS:
ARC tasks fall into categories:
1. KINETIC: Objects move (solved by movement potentials)
2. CHROMATIC: Colors change (solved by color operations)  
3. TOPOLOGICAL: Shapes transform (solved by pattern ops)
4. HYBRID: Combination of above

This phase implements a HYBRID SOLVER:
- First tries movement potentials (Phase 8.1 approach)
- Then tries color operations
- Combines both for hybrid tasks
"""

import torch
from dataclasses import dataclass
from typing import List, Tuple, Dict, Optional, Set
from collections import deque, Counter
from abc import ABC, abstractmethod
import numpy as np
import json
from pathlib import Path
import sys

def printfl(*args, **kwargs):
    print(*args, **kwargs)
    sys.stdout.flush()


# =============================================================================
# CONFIGURATION
# =============================================================================

@dataclass
class ARCPhase82Config:
    max_grid_size: int = 30
    num_colors: int = 10
    background_color: int = 0
    min_object_size: int = 1
    max_objects: int = 50
    max_relax_steps: int = 20
    energy_threshold: float = 0.0001
    consistency_threshold: float = 0.005
    device: str = 'cuda' if torch.cuda.is_available() else 'cpu'


# =============================================================================
# DATA STRUCTURES
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
        except: pass
    return tasks


def detect_objects(grid: ARCGrid, config: ARCPhase82Config) -> List[ARCObject]:
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


def compute_defect_energy(pred: ARCGrid, target: ARCGrid) -> float:
    if pred.shape != target.shape:
        return 1000.0 + abs(pred.height - target.height) + abs(pred.width - target.width)
    return (pred.data != target.data).float().sum().item() / target.data.numel()


# =============================================================================
# CATEGORY 1: MOVEMENT POTENTIALS (From Phase 8.1)
# =============================================================================

class PotentialFunction(ABC):
    @abstractmethod
    def compute(self, obj, grid, all_objects, config) -> float: pass
    @abstractmethod
    def name(self) -> str: pass


class V_BoundaryDist(PotentialFunction):
    def compute(self, obj, grid, all_objects, config):
        H, W = grid.height, grid.width
        r1, c1, r2, c2 = obj.bbox
        return min(r1, H - r2, c1, W - c2)
    def name(self): return "V_boundary"


class V_TopEdge(PotentialFunction):
    def compute(self, obj, grid, all_objects, config):
        return obj.bbox[0]
    def name(self): return "V_top"


class V_BottomEdge(PotentialFunction):
    def compute(self, obj, grid, all_objects, config):
        return grid.height - obj.bbox[2]
    def name(self): return "V_bottom"


class V_LeftEdge(PotentialFunction):
    def compute(self, obj, grid, all_objects, config):
        return obj.bbox[1]
    def name(self): return "V_left"


class V_RightEdge(PotentialFunction):
    def compute(self, obj, grid, all_objects, config):
        return grid.width - obj.bbox[3]
    def name(self): return "V_right"


class V_CenterDist(PotentialFunction):
    def compute(self, obj, grid, all_objects, config):
        H, W = grid.height, grid.width
        cr, cc = obj.centroid
        return ((cr - H/2)**2 + (cc - W/2)**2) ** 0.5
    def name(self): return "V_center"


class V_ContactDist(PotentialFunction):
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


class V_AlignH(PotentialFunction):
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


# =============================================================================
# COMPOSITE POTENTIAL & RELAXATION
# =============================================================================

class CompositePotential:
    def __init__(self, potentials: List[PotentialFunction], weights: np.ndarray):
        self.potentials = potentials
        self.weights = weights
    
    def compute(self, obj, grid, all_objects, config) -> float:
        total = 0.0
        for pot, w in zip(self.potentials, self.weights):
            if abs(w) > 0.01:
                total += w * pot.compute(obj, grid, all_objects, config)
        return total
    
    def gradient(self, obj, grid, all_objects, config) -> Tuple[int, int]:
        H, W = grid.height, grid.width
        current = self.compute(obj, grid, all_objects, config)
        best_dir, best_decrease = (0, 0), 0.0
        
        for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
            new_pixels = [(r + dr, c + dc) for r, c in obj.pixels]
            if all(0 <= r < H and 0 <= c < W for r, c in new_pixels):
                moved_obj = ARCObject(obj.object_id, obj.color, new_pixels)
                new_pot = self.compute(moved_obj, grid, all_objects, config)
                decrease = current - new_pot
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


def relax_system(grid: ARCGrid, potential: CompositePotential, target_color: int, config: ARCPhase82Config) -> ARCGrid:
    data = grid.data.clone()
    H, W = data.shape
    
    for step in range(config.max_relax_steps):
        current_grid = ARCGrid(data)
        objects = detect_objects(current_grid, config)
        targets = [o for o in objects if o.color == target_color]
        if not targets: break
        
        moved_any = False
        for obj in targets:
            dr, dc = potential.gradient(obj, current_grid, objects, config)
            if dr == 0 and dc == 0: continue
            
            mask = obj.get_mask(H, W, data.device)
            can_move = True
            for r, c in obj.pixels:
                nr, nc = r + dr, c + dc
                if not (0 <= nr < H and 0 <= nc < W):
                    can_move = False; break
                if data[nr, nc] != config.background_color and not mask[nr, nc]:
                    can_move = False; break
            
            if can_move:
                data[mask] = config.background_color
                for r, c in obj.pixels:
                    data[r + dr, c + dc] = target_color
                moved_any = True
        
        if not moved_any: break
    
    return ARCGrid(data)


def relax_all_colors(grid: ARCGrid, potential: CompositePotential, config: ARCPhase82Config) -> ARCGrid:
    result = grid.clone()
    for color in range(1, config.num_colors):
        if (result.data == color).any():
            result = relax_system(result, potential, color, config)
    return result


# =============================================================================
# CATEGORY 2: COLOR OPERATIONS (New in Phase 8.2)
# =============================================================================

class ColorOperation(ABC):
    @abstractmethod
    def apply(self, grid: ARCGrid, config: ARCPhase82Config) -> ARCGrid: pass
    @abstractmethod
    def name(self) -> str: pass


class ColorSwap(ColorOperation):
    """Swap two colors throughout the grid."""
    def __init__(self, color1: int, color2: int):
        self.c1, self.c2 = color1, color2
    
    def apply(self, grid, config):
        data = grid.data.clone()
        mask1 = data == self.c1
        mask2 = data == self.c2
        data[mask1] = self.c2
        data[mask2] = self.c1
        return ARCGrid(data)
    
    def name(self): return f"swap({self.c1},{self.c2})"


class ColorMap(ColorOperation):
    """Map one color to another."""
    def __init__(self, from_color: int, to_color: int):
        self.from_c, self.to_c = from_color, to_color
    
    def apply(self, grid, config):
        data = grid.data.clone()
        data[data == self.from_c] = self.to_c
        return ARCGrid(data)
    
    def name(self): return f"map({self.from_c}->{self.to_c})"


class FillBackground(ColorOperation):
    """Fill background with a specific color based on pattern."""
    def __init__(self, fill_color: int):
        self.fill_color = fill_color
    
    def apply(self, grid, config):
        data = grid.data.clone()
        data[data == config.background_color] = self.fill_color
        return ARCGrid(data)
    
    def name(self): return f"fill_bg({self.fill_color})"


class InvertColors(ColorOperation):
    """Swap foreground and background for a specific color."""
    def __init__(self, target_color: int):
        self.target = target_color
    
    def apply(self, grid, config):
        data = grid.data.clone()
        fg_mask = data == self.target
        bg_mask = data == config.background_color
        data[fg_mask] = config.background_color
        data[bg_mask] = self.target
        return ARCGrid(data)
    
    def name(self): return f"invert({self.target})"


class MajorityColor(ColorOperation):
    """Replace minority colors with majority non-background color."""
    def apply(self, grid, config):
        data = grid.data.clone()
        flat = data.flatten().tolist()
        counts = Counter(c for c in flat if c != config.background_color)
        if not counts:
            return grid.clone()
        majority = counts.most_common(1)[0][0]
        for color in counts:
            if color != majority:
                data[data == color] = majority
        return ARCGrid(data)
    
    def name(self): return "majority_color"


class RemoveColor(ColorOperation):
    """Remove a specific color (set to background)."""
    def __init__(self, color: int):
        self.color = color
    
    def apply(self, grid, config):
        data = grid.data.clone()
        data[data == self.color] = config.background_color
        return ARCGrid(data)
    
    def name(self): return f"remove({self.color})"


# =============================================================================
# CATEGORY 3: PATTERN OPERATIONS
# =============================================================================

class PatternOperation(ABC):
    @abstractmethod
    def apply(self, grid: ARCGrid, config: ARCPhase82Config) -> ARCGrid: pass
    @abstractmethod
    def name(self) -> str: pass


class FlipHorizontal(PatternOperation):
    def apply(self, grid, config):
        return ARCGrid(grid.data.flip(1))
    def name(self): return "flip_h"


class FlipVertical(PatternOperation):
    def apply(self, grid, config):
        return ARCGrid(grid.data.flip(0))
    def name(self): return "flip_v"


class Rotate90(PatternOperation):
    def apply(self, grid, config):
        return ARCGrid(grid.data.rot90(1, [0, 1]))
    def name(self): return "rot90"


class Rotate180(PatternOperation):
    def apply(self, grid, config):
        return ARCGrid(grid.data.rot90(2, [0, 1]))
    def name(self): return "rot180"


class Rotate270(PatternOperation):
    def apply(self, grid, config):
        return ARCGrid(grid.data.rot90(3, [0, 1]))
    def name(self): return "rot270"


class Transpose(PatternOperation):
    def apply(self, grid, config):
        return ARCGrid(grid.data.t())
    def name(self): return "transpose"


# =============================================================================
# UNIFIED HYBRID SOLVER
# =============================================================================

class HybridSolver:
    """
    Unified solver that tries:
    1. Movement potentials (for spatial tasks)
    2. Color operations (for chromatic tasks)
    3. Pattern operations (for geometric tasks)
    4. Combinations
    """
    
    def __init__(self, config: ARCPhase82Config):
        self.config = config
        self.movement_potentials = self._build_movement_potentials()
        self.color_ops = self._build_color_ops()
        self.pattern_ops = self._build_pattern_ops()
        
        printfl(f"   Movement potentials: {len(self.movement_potentials)}")
        printfl(f"   Color operations: {len(self.color_ops)}")
        printfl(f"   Pattern operations: {len(self.pattern_ops)}")
    
    def _build_movement_potentials(self) -> List[PotentialFunction]:
        return [
            V_BoundaryDist(), V_TopEdge(), V_BottomEdge(),
            V_LeftEdge(), V_RightEdge(), V_CenterDist(),
            V_ContactDist(), V_AlignH(), V_AlignV()
        ]
    
    def _build_color_ops(self) -> List[ColorOperation]:
        ops = [MajorityColor()]
        # Color swaps and maps for colors 1-5
        for c1 in range(1, 6):
            for c2 in range(c1+1, 6):
                ops.append(ColorSwap(c1, c2))
            for c2 in range(0, 6):
                if c1 != c2:
                    ops.append(ColorMap(c1, c2))
            ops.append(RemoveColor(c1))
        return ops
    
    def _build_pattern_ops(self) -> List[PatternOperation]:
        return [
            FlipHorizontal(), FlipVertical(),
            Rotate90(), Rotate180(), Rotate270(),
            Transpose()
        ]
    
    def _try_movement(self, examples: List[ARCExample], verbose: bool) -> Tuple[str, float, Optional[CompositePotential]]:
        """Try movement potentials."""
        n = len(self.movement_potentials)
        best_weights = np.zeros(n)
        best_energy = self._eval_movement(best_weights, examples)
        
        # Single potentials
        for i, pot in enumerate(self.movement_potentials):
            for sign in [-1.0, 1.0]:
                w = np.zeros(n)
                w[i] = sign
                e = self._eval_movement(w, examples)
                if e < best_energy:
                    if verbose:
                        printfl(f"      Movement: {sign:+.0f}*{pot.name()}: E={e:.4f}")
                    best_energy = e
                    best_weights = w.copy()
        
        # Pairs (if needed)
        if best_energy > self.config.energy_threshold:
            for i in range(n):
                for j in range(i+1, n):
                    for s1 in [-1.0, 1.0]:
                        for s2 in [-1.0, 1.0]:
                            w = np.zeros(n)
                            w[i], w[j] = s1, s2
                            e = self._eval_movement(w, examples)
                            if e < best_energy:
                                best_energy = e
                                best_weights = w.copy()
        
        potential = CompositePotential(self.movement_potentials, best_weights)
        return potential.signature(), best_energy, potential
    
    def _eval_movement(self, weights: np.ndarray, examples: List[ARCExample]) -> float:
        potential = CompositePotential(self.movement_potentials, weights)
        total = 0.0
        for ex in examples:
            result = relax_all_colors(ex.input_grid, potential, self.config)
            total += compute_defect_energy(result, ex.output_grid)
        return total / len(examples)
    
    def _try_color_ops(self, examples: List[ARCExample], verbose: bool) -> Tuple[str, float, Optional[ColorOperation]]:
        """Try color operations."""
        best_op = None
        best_energy = float('inf')
        best_name = "identity"
        
        for op in self.color_ops:
            energies = []
            for ex in examples:
                result = op.apply(ex.input_grid, self.config)
                energies.append(compute_defect_energy(result, ex.output_grid))
            avg = np.mean(energies)
            
            if avg < best_energy:
                if verbose and avg < 0.5:
                    printfl(f"      Color: {op.name()}: E={avg:.4f}")
                best_energy = avg
                best_op = op
                best_name = op.name()
        
        return best_name, best_energy, best_op
    
    def _try_pattern_ops(self, examples: List[ARCExample], verbose: bool) -> Tuple[str, float, Optional[PatternOperation]]:
        """Try pattern operations."""
        best_op = None
        best_energy = float('inf')
        best_name = "identity"
        
        for op in self.pattern_ops:
            energies = []
            valid = True
            for ex in examples:
                try:
                    result = op.apply(ex.input_grid, self.config)
                    energies.append(compute_defect_energy(result, ex.output_grid))
                except:
                    valid = False
                    break
            
            if valid:
                avg = np.mean(energies)
                if avg < best_energy:
                    if verbose and avg < 0.5:
                        printfl(f"      Pattern: {op.name()}: E={avg:.4f}")
                    best_energy = avg
                    best_op = op
                    best_name = op.name()
        
        return best_name, best_energy, best_op
    
    def solve_task(self, task: ARCTask, verbose: bool = False) -> Dict:
        """Find the best operation (movement, color, or pattern) for this task."""
        examples = task.train_examples
        
        # Check for size mismatch first
        size_mismatch = any(ex.input_grid.shape != ex.output_grid.shape for ex in examples)
        
        if verbose:
            if size_mismatch:
                printfl(f"   [Size mismatch - limited operations]")
            printfl(f"   Trying movement potentials...")
        
        # Try movement
        move_name, move_energy, move_pot = self._try_movement(examples, verbose)
        
        if verbose:
            printfl(f"   Trying color operations...")
        
        # Try color ops
        color_name, color_energy, color_op = self._try_color_ops(examples, verbose)
        
        if verbose:
            printfl(f"   Trying pattern operations...")
        
        # Try pattern ops
        pattern_name, pattern_energy, pattern_op = self._try_pattern_ops(examples, verbose)
        
        # Select best
        best_name = "identity"
        best_energy = float('inf')
        best_type = "none"
        
        if move_energy < best_energy:
            best_energy = move_energy
            best_name = move_name
            best_type = "movement"
        
        if color_energy < best_energy:
            best_energy = color_energy
            best_name = color_name
            best_type = "color"
        
        if pattern_energy < best_energy:
            best_energy = pattern_energy
            best_name = pattern_name
            best_type = "pattern"
        
        # Compute per-example energies
        train_energies = []
        test_energies = []
        
        for ex in examples:
            if best_type == "movement" and move_pot:
                result = relax_all_colors(ex.input_grid, move_pot, self.config)
            elif best_type == "color" and color_op:
                result = color_op.apply(ex.input_grid, self.config)
            elif best_type == "pattern" and pattern_op:
                result = pattern_op.apply(ex.input_grid, self.config)
            else:
                result = ex.input_grid.clone()
            train_energies.append(compute_defect_energy(result, ex.output_grid))
        
        for ex in task.test_examples:
            if best_type == "movement" and move_pot:
                result = relax_all_colors(ex.input_grid, move_pot, self.config)
            elif best_type == "color" and color_op:
                result = color_op.apply(ex.input_grid, self.config)
            elif best_type == "pattern" and pattern_op:
                result = pattern_op.apply(ex.input_grid, self.config)
            else:
                result = ex.input_grid.clone()
            test_energies.append(compute_defect_energy(result, ex.output_grid))
        
        avg_train = np.mean(train_energies)
        is_consistent = all(e < self.config.consistency_threshold for e in train_energies)
        is_perfect = avg_train < self.config.energy_threshold
        
        return {
            'task_id': task.task_id,
            'operation': best_name,
            'op_type': best_type,
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

def run_evaluation(data_path: str, config: ARCPhase82Config, num_tasks: int = 50):
    printfl("=" * 70)
    printfl("ARC-SGC Phase 8.2: Unified Physics (Movement + Color + Pattern)")
    printfl("=" * 70)
    
    tasks = load_arc_tasks(data_path, config.device, num_tasks)
    printfl(f"\nLoaded {len(tasks)} tasks")
    
    if not tasks:
        printfl("No tasks found!")
        return []
    
    printfl("\nBuilding Hybrid Solver...")
    solver = HybridSolver(config)
    
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
        
        printfl(f"\n  {status} [{result['op_type']}] {result['operation']}")
        printfl(f"  Train: {[f'{e:.4f}' for e in result['train_energies']]}")
        if result['test_energies']:
            printfl(f"  Test:  {[f'{e:.4f}' for e in result['test_energies']]}")
        
        if (i + 1) % 10 == 0:
            printfl(f"\n  --- Progress: {len(perfect_tasks)} perfect, {len(consistent_tasks)} consistent ---")
    
    # Summary
    printfl("\n" + "=" * 70)
    printfl("FINAL SUMMARY: Phase 8.2 - Unified Physics")
    printfl("=" * 70)
    
    perfect = len(perfect_tasks)
    consistent = len(consistent_tasks)
    partial = sum(1 for r in all_results if not r['is_consistent'] and r['avg_train_energy'] < 0.3)
    failed = sum(1 for r in all_results if r['avg_train_energy'] >= 0.3)
    
    avg_energy = np.mean([r['avg_train_energy'] for r in all_results])
    
    printfl(f"Tasks: {len(all_results)}")
    printfl(f"  PERFECT    (E < 0.0001):  {perfect}")
    printfl(f"  CONSISTENT (all < 0.005): {consistent}")
    printfl(f"  PARTIAL    (avg < 0.3):   {partial}")
    printfl(f"  FAILED     (avg >= 0.3):  {failed}")
    printfl(f"  Average energy: {avg_energy:.4f}")
    
    # Breakdown by operation type
    type_counts = Counter(r['op_type'] for r in all_results if r['avg_train_energy'] < 0.5)
    printfl(f"\n  By Operation Type (partial+ only):")
    for t, c in type_counts.most_common():
        printfl(f"    {t}: {c}")
    
    if perfect > 0 or consistent > 0:
        printfl(f"\n=== BREAKTHROUGHS ===")
        for r in perfect_tasks + consistent_tasks:
            status = "PERFECT" if r['is_perfect'] else "CONSISTENT"
            printfl(f"  [{status}] {r['task_id']}: [{r['op_type']}] {r['operation']}")
    
    printfl(f"\n=== Best Results ===")
    for r in sorted(all_results, key=lambda x: x['avg_train_energy'])[:15]:
        status = "PERFECT" if r['is_perfect'] else ("CONS" if r['is_consistent'] else "part")
        printfl(f"  [{status}] {r['task_id']}: [{r['op_type']}] {r['operation'][:30]}... E={r['avg_train_energy']:.4f}")
    
    return all_results


def main():
    config = ARCPhase82Config()
    paths = ["data/arc/training", "C:/Lean4 Projects/data/arc/training"]
    arc_path = next((p for p in paths if Path(p).exists()), None)
    
    if arc_path:
        return run_evaluation(arc_path, config, num_tasks=100)
    else:
        printfl("ARC data not found!")
        return []


if __name__ == "__main__":
    main()
