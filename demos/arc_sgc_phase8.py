"""
ARC-SGC Phase 8: Composite Dynamics & Iterative Relaxation

FROM SINGLE POTENTIALS TO COMPOSITE HAMILTONIANS

Phase 7 validated: Potential fields explain ARC better than explicit actions.
The 5% remaining error suggests the true Hamiltonian is a SUPERPOSITION:

    V_total = α·V_boundary + β·V_contact + γ·V_align

The "Program" is no longer an action sequence - it's the WEIGHT VECTOR (α, β, γ).

SGC THEORY:
- Complex behavior emerges from competition between simple forces
- Learning = adjusting coupling constants
- The agent becomes a PHYSICIST discovering laws and constants

IMPLEMENTATION:
1. Composite Potential Engine: WeightedPotential(potentials, weights)
2. System Relaxation: Coupled dynamics - all objects move simultaneously
3. Weight Optimization: Coordinate Descent to tune coefficients
4. The "Program" is H = Σ wᵢ Vᵢ

This is how physicists discover laws:
- Define entities (Objects)
- Hypothesize forces (Potentials)
- Tune coupling constants to match experiment (Optimization)
"""

import torch
import torch.nn.functional as F
from dataclasses import dataclass
from typing import List, Tuple, Dict, Optional, Callable
from collections import deque
from abc import ABC, abstractmethod
import numpy as np
import json
from pathlib import Path
from scipy.optimize import minimize, differential_evolution
from copy import deepcopy


# =============================================================================
# CONFIGURATION
# =============================================================================

@dataclass
class ARCPhase8Config:
    max_grid_size: int = 30
    num_colors: int = 10
    background_color: int = 0
    min_object_size: int = 1
    max_objects: int = 50
    
    # Relaxation
    max_relax_steps: int = 15
    convergence_threshold: float = 0.001
    
    # Optimization
    max_optim_iters: int = 50
    weight_bounds: Tuple[float, float] = (-2.0, 2.0)
    
    # Solver
    energy_threshold: float = 0.0001
    consistency_threshold: float = 0.005  # Stricter for Phase 8
    
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
            pass
    return tasks


def detect_objects(grid: ARCGrid, config: ARCPhase8Config) -> List[ARCObject]:
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
# TASK 1: POTENTIAL FUNCTIONS (Building Blocks)
# =============================================================================

class PotentialFunction(ABC):
    """Base class for potential energy functions."""
    
    @abstractmethod
    def compute(self, obj: ARCObject, grid: ARCGrid, all_objects: List[ARCObject], config: ARCPhase8Config) -> float:
        """Compute potential energy for an object."""
        pass
    
    @abstractmethod
    def name(self) -> str:
        pass
    
    def gradient(self, obj: ARCObject, grid: ARCGrid, all_objects: List[ARCObject], config: ARCPhase8Config) -> Tuple[float, float]:
        """
        Compute gradient (direction of steepest descent).
        Returns (dr, dc) - the direction to move to DECREASE potential.
        """
        H, W = grid.height, grid.width
        current = self.compute(obj, grid, all_objects, config)
        
        # Check all 4 directions
        best_dir = (0, 0)
        best_decrease = 0.0
        
        for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
            # Simulate moving object
            new_pixels = [(r + dr, c + dc) for r, c in obj.pixels]
            
            # Check bounds
            if all(0 <= r < H and 0 <= c < W for r, c in new_pixels):
                # Create temporary moved object
                moved_obj = ARCObject(obj.object_id, obj.color, new_pixels)
                new_potential = self.compute(moved_obj, grid, all_objects, config)
                decrease = current - new_potential
                
                if decrease > best_decrease:
                    best_decrease = decrease
                    best_dir = (dr, dc)
        
        return best_dir


class BoundaryDistPotential(PotentialFunction):
    """V = distance to nearest boundary. Minimize → move to walls."""
    
    def compute(self, obj, grid, all_objects, config):
        H, W = grid.height, grid.width
        r1, c1, r2, c2 = obj.bbox
        return min(r1, H - r2, c1, W - c2)
    
    def name(self): return "V_boundary"


class CenterDistPotential(PotentialFunction):
    """V = distance to grid center. Minimize → move to center."""
    
    def compute(self, obj, grid, all_objects, config):
        H, W = grid.height, grid.width
        cr, cc = obj.centroid
        return ((cr - H/2)**2 + (cc - W/2)**2) ** 0.5
    
    def name(self): return "V_center"


class ContactDistPotential(PotentialFunction):
    """V = distance to nearest other object. Minimize → move toward objects."""
    
    def compute(self, obj, grid, all_objects, config):
        cr, cc = obj.centroid
        min_dist = float('inf')
        
        for other in all_objects:
            if other.object_id == obj.object_id:
                continue
            if other.color == config.background_color:
                continue
            
            or_, oc = other.centroid
            dist = ((cr - or_)**2 + (cc - oc)**2) ** 0.5
            min_dist = min(min_dist, dist)
        
        return min_dist if min_dist != float('inf') else 0.0
    
    def name(self): return "V_contact"


class AlignHPotential(PotentialFunction):
    """V = distance to horizontal alignment with other objects."""
    
    def compute(self, obj, grid, all_objects, config):
        cr, _ = obj.centroid
        min_dist = float('inf')
        
        for other in all_objects:
            if other.object_id == obj.object_id:
                continue
            if other.color == config.background_color:
                continue
            
            or_, _ = other.centroid
            min_dist = min(min_dist, abs(cr - or_))
        
        return min_dist if min_dist != float('inf') else 0.0
    
    def name(self): return "V_align_h"


class AlignVPotential(PotentialFunction):
    """V = distance to vertical alignment with other objects."""
    
    def compute(self, obj, grid, all_objects, config):
        _, cc = obj.centroid
        min_dist = float('inf')
        
        for other in all_objects:
            if other.object_id == obj.object_id:
                continue
            if other.color == config.background_color:
                continue
            
            _, oc = other.centroid
            min_dist = min(min_dist, abs(cc - oc))
        
        return min_dist if min_dist != float('inf') else 0.0
    
    def name(self): return "V_align_v"


class ColorDistPotential(PotentialFunction):
    """V = distance to nearest object of specific color."""
    
    def __init__(self, target_color: int):
        self.target_color = target_color
    
    def compute(self, obj, grid, all_objects, config):
        cr, cc = obj.centroid
        min_dist = float('inf')
        
        for other in all_objects:
            if other.color != self.target_color:
                continue
            if other.object_id == obj.object_id:
                continue
            
            or_, oc = other.centroid
            dist = ((cr - or_)**2 + (cc - oc)**2) ** 0.5
            min_dist = min(min_dist, dist)
        
        return min_dist if min_dist != float('inf') else 0.0
    
    def name(self): return f"V_color_{self.target_color}"


# =============================================================================
# TASK 1: COMPOSITE POTENTIAL ENGINE
# =============================================================================

class CompositePotential:
    """
    The Hamiltonian: H = Σ wᵢ Vᵢ
    
    This is the "Program" - a weighted combination of potential functions.
    """
    
    def __init__(self, potentials: List[PotentialFunction], weights: np.ndarray):
        self.potentials = potentials
        self.weights = weights
    
    def compute(self, obj: ARCObject, grid: ARCGrid, all_objects: List[ARCObject], config: ARCPhase8Config) -> float:
        """Compute total weighted potential for an object."""
        total = 0.0
        for pot, w in zip(self.potentials, self.weights):
            if abs(w) > 0.01:  # Skip negligible weights
                total += w * pot.compute(obj, grid, all_objects, config)
        return total
    
    def gradient(self, obj: ARCObject, grid: ARCGrid, all_objects: List[ARCObject], config: ARCPhase8Config) -> Tuple[float, float]:
        """Compute composite gradient (weighted sum of individual gradients)."""
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
                parts.append(f"{w:.2f}*{pot.name()}")
        return " + ".join(parts) if parts else "0"


# =============================================================================
# TASK 2: SYSTEM RELAXATION (Coupled Dynamics)
# =============================================================================

def relax_system(
    grid: ARCGrid,
    potential: CompositePotential,
    target_color: int,
    config: ARCPhase8Config
) -> ARCGrid:
    """
    Iteratively relax all objects of target color to minimize composite potential.
    
    This models COUPLED DYNAMICS: moving Object A changes potential for Object B.
    """
    data = grid.data.clone()
    H, W = data.shape
    
    for step in range(config.max_relax_steps):
        # Detect objects in current state
        current_grid = ARCGrid(data)
        objects = detect_objects(current_grid, config)
        targets = [o for o in objects if o.color == target_color]
        
        if not targets:
            break
        
        moved_any = False
        
        for obj in targets:
            # Compute gradient for this object
            dr, dc = potential.gradient(obj, current_grid, objects, config)
            
            if dr == 0 and dc == 0:
                continue
            
            # Check if move is valid (no collision with non-background)
            mask = obj.get_mask(H, W, data.device)
            can_move = True
            
            for r, c in obj.pixels:
                nr, nc = r + dr, c + dc
                if not (0 <= nr < H and 0 <= nc < W):
                    can_move = False
                    break
                # Check collision (skip own pixels)
                if data[nr, nc] != config.background_color and not mask[nr, nc]:
                    can_move = False
                    break
            
            if can_move:
                # Move object
                data[mask] = config.background_color
                for r, c in obj.pixels:
                    nr, nc = r + dr, c + dc
                    data[nr, nc] = target_color
                moved_any = True
        
        if not moved_any:
            break  # Converged
    
    return ARCGrid(data)


def relax_all_colors(
    grid: ARCGrid,
    potential: CompositePotential,
    config: ARCPhase8Config
) -> ARCGrid:
    """Relax all non-background colors."""
    result = grid.clone()
    
    for color in range(1, config.num_colors):
        # Check if this color exists
        if (result.data == color).any():
            result = relax_system(result, potential, color, config)
    
    return result


# =============================================================================
# TASK 3: WEIGHT OPTIMIZATION (Coordinate Descent)
# =============================================================================

def compute_defect_energy(pred: ARCGrid, target: ARCGrid) -> float:
    """Compute pixel-wise error."""
    if pred.shape != target.shape:
        return 1000.0 + abs(pred.height - target.height) + abs(pred.width - target.width)
    return (pred.data != target.data).float().sum().item() / target.data.numel()


def evaluate_weights(
    weights: np.ndarray,
    potentials: List[PotentialFunction],
    examples: List[ARCExample],
    config: ARCPhase8Config
) -> float:
    """Evaluate a weight vector on all training examples."""
    potential = CompositePotential(potentials, weights)
    total_energy = 0.0
    
    for ex in examples:
        result = relax_all_colors(ex.input_grid, potential, config)
        energy = compute_defect_energy(result, ex.output_grid)
        total_energy += energy
    
    return total_energy / len(examples)


def optimize_weights(
    potentials: List[PotentialFunction],
    examples: List[ARCExample],
    config: ARCPhase8Config,
    verbose: bool = False
) -> Tuple[np.ndarray, float]:
    """
    Find optimal weights using simple grid search (fast, with progress).
    """
    n_potentials = len(potentials)
    
    def objective(w):
        return evaluate_weights(w, potentials, examples, config)
    
    # Simple grid search over weight combinations (FAST with progress)
    best_weights = np.zeros(n_potentials)
    best_energy = objective(best_weights)
    
    if verbose:
        print(f"   Baseline energy: {best_energy:.4f}")
    
    # Try individual potentials first
    for i in range(n_potentials):
        for sign in [-1.0, 1.0, -0.5, 0.5]:
            w = np.zeros(n_potentials)
            w[i] = sign
            e = objective(w)
            if verbose and e < best_energy:
                print(f"   Found: w[{i}]={sign:.1f} -> E={e:.4f}")
            if e < best_energy:
                best_energy = e
                best_weights = w.copy()
    
    # Try pairs (limited for speed)
    if verbose:
        print(f"   Trying pairs...")
    
    for i in range(min(n_potentials, 5)):
        for j in range(i+1, min(n_potentials, 5)):
            for s1 in [-1.0, 1.0]:
                for s2 in [-1.0, 1.0]:
                    w = np.zeros(n_potentials)
                    w[i], w[j] = s1, s2
                    e = objective(w)
                    if e < best_energy:
                        if verbose:
                            print(f"   Found pair: w[{i}]={s1:.1f}, w[{j}]={s2:.1f} -> E={e:.4f}")
                        best_energy = e
                        best_weights = w.copy()
    
    if verbose:
        print(f"   Final: E={best_energy:.4f}")
    
    return best_weights, best_energy


# =============================================================================
# COMPOSITE DYNAMICS SOLVER
# =============================================================================

class CompositeDynamicsSolver:
    """
    The Phase 8 Solver: Finds the Hamiltonian (Composite Potential) that explains all examples.
    
    Instead of searching for actions, it searches for WEIGHTS on potential functions.
    The "Program" is H = Σ wᵢ Vᵢ
    """
    
    def __init__(self, config: ARCPhase8Config):
        self.config = config
        
        # Build potential library
        self.potentials: List[PotentialFunction] = [
            BoundaryDistPotential(),
            CenterDistPotential(),
            ContactDistPotential(),
            AlignHPotential(),
            AlignVPotential(),
        ]
        
        # Add color-specific potentials
        for color in range(1, 5):
            self.potentials.append(ColorDistPotential(color))
        
        print(f"   Potentials: {len(self.potentials)}")
        print(f"   Potential names: {[p.name() for p in self.potentials]}")
    
    def solve_task(
        self,
        task: ARCTask,
        verbose: bool = False
    ) -> Dict:
        """
        Find optimal weights for composite potential.
        """
        examples = task.train_examples
        
        if verbose:
            print(f"   Optimizing Hamiltonian for {len(examples)} examples...")
        
        # Optimize weights
        best_weights, best_energy = optimize_weights(
            self.potentials, examples, self.config, verbose
        )
        
        # Create best potential
        best_potential = CompositePotential(self.potentials, best_weights)
        
        # Evaluate on each example
        train_energies = []
        for ex in examples:
            result = relax_all_colors(ex.input_grid, best_potential, self.config)
            energy = compute_defect_energy(result, ex.output_grid)
            train_energies.append(energy)
        
        # Test
        test_energies = []
        for ex in task.test_examples:
            result = relax_all_colors(ex.input_grid, best_potential, self.config)
            energy = compute_defect_energy(result, ex.output_grid)
            test_energies.append(energy)
        
        avg_train = np.mean(train_energies)
        is_consistent = all(e < self.config.consistency_threshold for e in train_energies)
        is_perfect = avg_train < self.config.energy_threshold
        
        return {
            'task_id': task.task_id,
            'weights': best_weights,
            'program': best_potential.signature(),
            'avg_train_energy': avg_train,
            'train_energies': train_energies,
            'avg_test_energy': np.mean(test_energies) if test_energies else 0,
            'test_energies': test_energies,
            'is_consistent': is_consistent,
            'is_perfect': is_perfect
        }


# =============================================================================
# ALSO TRY SIMPLE SINGLE-POTENTIAL APPROACH
# =============================================================================

class SimplePotentialSolver:
    """
    Simpler approach: Try each potential individually, then try pairs.
    """
    
    def __init__(self, config: ARCPhase8Config):
        self.config = config
        self.potentials = [
            BoundaryDistPotential(),
            CenterDistPotential(),
            ContactDistPotential(),
            AlignHPotential(),
            AlignVPotential(),
        ]
    
    def solve_task(self, task: ARCTask, verbose: bool = False) -> Dict:
        examples = task.train_examples
        best_result = None
        best_energy = float('inf')
        
        # Try single potentials with weight = -1 (minimize)
        for pot in self.potentials:
            weights = np.zeros(len(self.potentials))
            idx = self.potentials.index(pot)
            
            for sign in [-1, 1]:  # Minimize or maximize
                weights[idx] = sign
                composite = CompositePotential(self.potentials, weights)
                
                energies = []
                for ex in examples:
                    result = relax_all_colors(ex.input_grid, composite, self.config)
                    energy = compute_defect_energy(result, ex.output_grid)
                    energies.append(energy)
                
                avg = np.mean(energies)
                if avg < best_energy:
                    best_energy = avg
                    best_result = {
                        'weights': weights.copy(),
                        'program': composite.signature(),
                        'train_energies': energies
                    }
        
        # Try pairs
        for i, p1 in enumerate(self.potentials):
            for j, p2 in enumerate(self.potentials):
                if i >= j:
                    continue
                
                for s1 in [-1, 1]:
                    for s2 in [-1, 1]:
                        weights = np.zeros(len(self.potentials))
                        weights[i] = s1
                        weights[j] = s2
                        
                        composite = CompositePotential(self.potentials, weights)
                        
                        energies = []
                        for ex in examples:
                            result = relax_all_colors(ex.input_grid, composite, self.config)
                            energy = compute_defect_energy(result, ex.output_grid)
                            energies.append(energy)
                        
                        avg = np.mean(energies)
                        if avg < best_energy:
                            best_energy = avg
                            best_result = {
                                'weights': weights.copy(),
                                'program': composite.signature(),
                                'train_energies': energies
                            }
        
        if best_result is None:
            best_result = {
                'weights': np.zeros(len(self.potentials)),
                'program': "identity",
                'train_energies': [1.0] * len(examples)
            }
        
        # Test
        composite = CompositePotential(self.potentials, best_result['weights'])
        test_energies = []
        for ex in task.test_examples:
            result = relax_all_colors(ex.input_grid, composite, self.config)
            energy = compute_defect_energy(result, ex.output_grid)
            test_energies.append(energy)
        
        avg_train = np.mean(best_result['train_energies'])
        is_consistent = all(e < self.config.consistency_threshold for e in best_result['train_energies'])
        
        if verbose and avg_train < 0.2:
            print(f"   Best: {best_result['program']} (E={avg_train:.4f})")
        
        return {
            'task_id': task.task_id,
            'weights': best_result['weights'],
            'program': best_result['program'],
            'avg_train_energy': avg_train,
            'train_energies': best_result['train_energies'],
            'avg_test_energy': np.mean(test_energies) if test_energies else 0,
            'test_energies': test_energies,
            'is_consistent': is_consistent,
            'is_perfect': avg_train < self.config.energy_threshold
        }


# =============================================================================
# HYBRID SOLVER (Combines both approaches)
# =============================================================================

class HybridSolver:
    """
    Combines simple grid search with differential evolution.
    """
    
    def __init__(self, config: ARCPhase8Config):
        self.config = config
        self.simple_solver = SimplePotentialSolver(config)
        self.composite_solver = CompositeDynamicsSolver(config)
    
    def solve_task(self, task: ARCTask, verbose: bool = False) -> Dict:
        # Try simple approach first (fast)
        simple_result = self.simple_solver.solve_task(task, verbose=False)
        
        if verbose:
            print(f"   Simple: {simple_result['program']} (E={simple_result['avg_train_energy']:.4f})")
        
        # If simple approach is good enough, use it
        if simple_result['is_consistent'] or simple_result['avg_train_energy'] < 0.02:
            return simple_result
        
        # Try full optimization for harder tasks
        if simple_result['avg_train_energy'] < 0.5:
            if verbose:
                print(f"   Trying full optimization...")
            composite_result = self.composite_solver.solve_task(task, verbose=verbose)
            
            if composite_result['avg_train_energy'] < simple_result['avg_train_energy']:
                return composite_result
        
        return simple_result


# =============================================================================
# EVALUATION
# =============================================================================

def run_evaluation(data_path: str, config: ARCPhase8Config, num_tasks: int = 10):
    print("=" * 70)
    print("ARC-SGC Phase 8: Composite Dynamics & Iterative Relaxation")
    print("=" * 70)
    print("Paradigm: The 'Program' is a Hamiltonian H = sum(w_i * V_i)")
    
    tasks = load_arc_tasks(data_path, config.device, num_tasks)
    print(f"\nLoaded {len(tasks)} tasks")
    
    if not tasks:
        return []
    
    print("\nBuilding Hybrid Solver...")
    solver = HybridSolver(config)
    
    all_results = []
    
    for i, task in enumerate(tasks):
        print(f"\n{'='*70}")
        print(f"Task {i+1}/{len(tasks)}: {task.task_id}")
        print(f"  Train: {len(task.train_examples)}, Test: {len(task.test_examples)}")
        
        result = solver.solve_task(task, verbose=True)
        all_results.append(result)
        
        status = "[PERFECT]" if result['is_perfect'] else ("[CONSISTENT]" if result['is_consistent'] else "[partial]")
        print(f"\n  {status} H = {result['program']}")
        print(f"  Train: avg={result['avg_train_energy']:.4f}, per-ex={[f'{e:.4f}' for e in result['train_energies']]}")
        if result['test_energies']:
            print(f"  Test:  avg={result['avg_test_energy']:.4f}")
    
    # Summary
    print("\n" + "=" * 70)
    print("FINAL SUMMARY: Phase 8 - Composite Dynamics")
    print("=" * 70)
    
    perfect = sum(1 for r in all_results if r['is_perfect'])
    consistent = sum(1 for r in all_results if r['is_consistent'] and not r['is_perfect'])
    partial = sum(1 for r in all_results if not r['is_consistent'] and r['avg_train_energy'] < 0.5)
    failed = sum(1 for r in all_results if r['avg_train_energy'] >= 0.5)
    
    avg_energy = np.mean([r['avg_train_energy'] for r in all_results])
    
    print(f"Tasks: {len(all_results)}")
    print(f"  PERFECT    (E < 0.0001):  {perfect}")
    print(f"  CONSISTENT (all < 0.005): {consistent}")
    print(f"  PARTIAL    (avg < 0.5):   {partial}")
    print(f"  FAILED     (avg >= 0.5):  {failed}")
    print(f"  Average energy: {avg_energy:.6f}")
    
    print(f"\n  Phase 7 baseline: 0 consistent, E=0.0499 on Task 8")
    print(f"  Phase 8 result:   {consistent} consistent, {perfect} perfect")
    
    if consistent > 0 or perfect > 0:
        print(f"\n  === BREAKTHROUGH ===")
        for r in all_results:
            if r['is_consistent'] or r['is_perfect']:
                status = "[PERFECT]" if r['is_perfect'] else "[CONSISTENT]"
                print(f"  {status} {r['task_id']}: H = {r['program']}")
                print(f"           energies = {[f'{e:.4f}' for e in r['train_energies']]}")
    
    # Show best results
    print("\n  Best Hamiltonians found:")
    for r in sorted(all_results, key=lambda x: x['avg_train_energy'])[:5]:
        print(f"    {r['task_id']}: H = {r['program'][:50]}... (E={r['avg_train_energy']:.4f})")
    
    return all_results


def main():
    config = ARCPhase8Config()
    paths = ["data/arc/training", "C:/Lean4 Projects/data/arc/training"]
    arc_path = next((p for p in paths if Path(p).exists()), None)
    
    if arc_path:
        return run_evaluation(arc_path, config, num_tasks=10)
    else:
        print("ARC data not found!")
        return []


if __name__ == "__main__":
    main()
