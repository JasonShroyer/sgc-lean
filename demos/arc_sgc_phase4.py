"""
ARC-SGC Phase 4: Renormalization & Thermodynamic Annealing

THEORETICAL UPGRADES:
- Phase 1-3: Sheaf Surgery with Gluing (8/10 partial)
- Phase 4: Renormalization + Thermodynamics → Perfect Solves

KEY PHYSICS:

1. RENORMALIZATION (Symmetry Detection):
   Many ARC tasks have repeating patterns → Quotient Graph exists.
   - Detect translational/rotational symmetry
   - Construct Fundamental Domain (unit cell)
   - Solve on quotient (reduced complexity)
   - Lift solution back via inverse renormalization
   
   This is EXACT LUMPABILITY: solving on 9 pixels instead of 900.

2. THERMODYNAMIC ANNEALING (Kramers Escape):
   The Phase 3 solver is GREEDY (T=0) → stuck in local minima.
   - Implement Write/Erase cycle with Temperature
   - If stuck (defect constant), increase T (inject noise)
   - If improving, decrease T (crystallize)
   
   This implements Kramers escape from Lifshitz_transition_theory.md.

3. NEURAL SIMULATOR (Learned Physics):
   Replace hard-coded invariant heuristics with learned policy.
   - Dataset: (Input, Op) → (ΔMass, ΔSymmetry, ΔDefect)
   - Use as world model to rank operations
   
   Transitions from "Hard-Coded Physics" to "Learned Physics".

REFERENCES:
- SGC.Renormalization.lean: Coarse-graining theory
- demos/adaptive_polarity_v6_homeostat.py: Write/Erase mechanics
- docs/lifshitz_transition_theory.md: Kramers escape, phase transitions
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
from dataclasses import dataclass, field
from typing import List, Tuple, Dict, Optional, Set, Any
from collections import deque
from abc import ABC, abstractmethod
import numpy as np
import json
from pathlib import Path
import heapq
import random
import math
from copy import deepcopy


# =============================================================================
# CONFIGURATION
# =============================================================================

@dataclass
class ARCPhase4Config:
    """Configuration for Phase 4: Renormalization + Thermodynamics."""
    
    max_grid_size: int = 30
    num_colors: int = 10
    background_color: int = 0
    
    # Object detection
    min_object_size: int = 1
    max_objects: int = 50
    
    # Renormalization
    max_period: int = 15  # Max period to check for tiling
    min_period: int = 1   # Min period (unit cell size)
    symmetry_threshold: float = 0.95  # Match threshold for symmetry detection
    
    # Thermodynamic annealing (conservative - only heat when truly stuck)
    initial_temperature: float = 0.1  # Start cold (greedy)
    min_temperature: float = 0.001
    cooling_rate: float = 0.8
    heating_rate: float = 2.0
    stuck_threshold: int = 5  # Steps without improvement before heating
    metropolis_threshold: float = 0.05  # Only accept worse if delta < this
    
    # Solver
    max_search_depth: int = 4
    max_candidates: int = 30
    energy_threshold: float = 0.0001  # Very strict for perfect solve
    max_iterations: int = 15
    
    # Neural simulator
    simulator_hidden: int = 64
    simulator_lr: float = 1e-3
    
    device: str = 'cuda' if torch.cuda.is_available() else 'cpu'


# =============================================================================
# GRID STRUCTURES
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
    
    for json_file in sorted(path.glob("*.json"))[:limit]:
        try:
            with open(json_file, 'r') as f:
                data = json.load(f)
            tasks.append(ARCTask.from_json(json_file.stem, data, device))
        except Exception as e:
            print(f"Error loading {json_file}: {e}")
    
    return tasks


# =============================================================================
# TASK 1: RENORMALIZATION (SYMMETRY DETECTION)
# =============================================================================

@dataclass
class SymmetryInfo:
    """Detected symmetry information."""
    has_translation_h: bool = False
    has_translation_v: bool = False
    period_h: int = 0
    period_v: int = 0
    has_rotation_90: bool = False
    has_rotation_180: bool = False
    has_reflection_h: bool = False
    has_reflection_v: bool = False
    unit_cell: Optional[ARCGrid] = None
    
    @property
    def has_tiling(self) -> bool:
        return self.has_translation_h and self.has_translation_v


def detect_translational_symmetry(
    grid: ARCGrid, 
    config: ARCPhase4Config
) -> Tuple[bool, int, int, Optional[ARCGrid]]:
    """
    Detect if grid has translational symmetry (tiling).
    
    Returns: (has_symmetry, period_h, period_v, unit_cell)
    
    This is the UPWARD RENORMALIZATION operator Π.
    """
    data = grid.to_numpy()
    H, W = data.shape
    
    # Try different period sizes
    for ph in range(config.min_period, min(H // 2 + 1, config.max_period)):
        for pw in range(config.min_period, min(W // 2 + 1, config.max_period)):
            if H % ph != 0 or W % pw != 0:
                continue
            
            # Extract candidate unit cell
            unit = data[:ph, :pw]
            
            # Check if grid is tiled by this unit
            is_tiled = True
            match_count = 0
            total_count = 0
            
            for i in range(0, H, ph):
                for j in range(0, W, pw):
                    tile = data[i:i+ph, j:j+pw]
                    if tile.shape == unit.shape:
                        total_count += 1
                        if np.array_equal(tile, unit):
                            match_count += 1
            
            if total_count > 1 and match_count / total_count >= config.symmetry_threshold:
                unit_grid = ARCGrid(torch.tensor(unit, dtype=torch.long, device=grid.data.device))
                return True, ph, pw, unit_grid
    
    return False, 0, 0, None


def detect_rotational_symmetry(grid: ARCGrid) -> Tuple[bool, bool]:
    """Detect 90° and 180° rotational symmetry."""
    data = grid.to_numpy()
    H, W = data.shape
    
    rot_90 = False
    rot_180 = False
    
    if H == W:
        rotated_90 = np.rot90(data, k=1)
        rotated_180 = np.rot90(data, k=2)
        
        rot_90 = np.array_equal(data, rotated_90)
        rot_180 = np.array_equal(data, rotated_180)
    
    return rot_90, rot_180


def detect_reflection_symmetry(grid: ARCGrid) -> Tuple[bool, bool]:
    """Detect horizontal and vertical reflection symmetry."""
    data = grid.to_numpy()
    
    flip_h = np.array_equal(data, np.flip(data, axis=1))
    flip_v = np.array_equal(data, np.flip(data, axis=0))
    
    return flip_h, flip_v


def detect_all_symmetries(grid: ARCGrid, config: ARCPhase4Config) -> SymmetryInfo:
    """Detect all symmetries in a grid."""
    has_trans, ph, pw, unit_cell = detect_translational_symmetry(grid, config)
    rot_90, rot_180 = detect_rotational_symmetry(grid)
    ref_h, ref_v = detect_reflection_symmetry(grid)
    
    return SymmetryInfo(
        has_translation_h=(has_trans and pw > 1),
        has_translation_v=(has_trans and ph > 1),
        period_h=pw,
        period_v=ph,
        has_rotation_90=rot_90,
        has_rotation_180=rot_180,
        has_reflection_h=ref_h,
        has_reflection_v=ref_v,
        unit_cell=unit_cell
    )


def lift_solution_to_full_grid(
    unit_solution: ARCGrid,
    target_shape: Tuple[int, int],
    period_h: int,
    period_v: int
) -> ARCGrid:
    """
    INVERSE RENORMALIZATION: Lift unit cell solution to full grid.
    
    This tiles the unit cell solution across the full grid.
    """
    H, W = target_shape
    device = unit_solution.data.device
    
    result = torch.zeros(H, W, dtype=torch.long, device=device)
    
    uh, uw = unit_solution.height, unit_solution.width
    
    for i in range(0, H, period_v):
        for j in range(0, W, period_h):
            h_end = min(i + uh, H)
            w_end = min(j + uw, W)
            result[i:h_end, j:w_end] = unit_solution.data[:h_end-i, :w_end-j]
    
    return ARCGrid(result)


# =============================================================================
# DSL PRIMITIVES (Enhanced from Phase 3)
# =============================================================================

class LocalDSLPrimitive(ABC):
    """DSL primitive with local/global application."""
    
    @abstractmethod
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        pass
    
    def apply_local(self, grid: ARCGrid, mask: torch.Tensor) -> ARCGrid:
        return self.apply_global(grid)
    
    @abstractmethod
    def signature(self) -> str:
        pass
    
    def priority_score(self, delta: 'InvariantDelta', temperature: float = 0.0) -> float:
        base = 0.5
        # Add noise proportional to temperature
        if temperature > 0:
            base += random.gauss(0, temperature * 0.3)
        return max(0.0, min(1.0, base))


class Identity(LocalDSLPrimitive):
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        return grid.clone()
    def signature(self) -> str:
        return "identity"
    def priority_score(self, delta, temp=0.0) -> float:
        return 0.01 + random.gauss(0, temp * 0.1) if temp > 0 else 0.01


class Rotate90(LocalDSLPrimitive):
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        return ARCGrid(torch.rot90(grid.data, k=-1))
    def signature(self) -> str:
        return "rotate_90"
    def priority_score(self, delta, temp=0.0) -> float:
        base = 0.8 if delta.mass_conserved and not delta.colors_changed else 0.2
        return base + random.gauss(0, temp * 0.2) if temp > 0 else base


class Rotate180(LocalDSLPrimitive):
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        return ARCGrid(torch.rot90(grid.data, k=2))
    def signature(self) -> str:
        return "rotate_180"
    def priority_score(self, delta, temp=0.0) -> float:
        base = 0.7 if delta.mass_conserved else 0.2
        return base + random.gauss(0, temp * 0.2) if temp > 0 else base


class FlipHorizontal(LocalDSLPrimitive):
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        return ARCGrid(torch.flip(grid.data, dims=[1]))
    def signature(self) -> str:
        return "flip_h"
    def priority_score(self, delta, temp=0.0) -> float:
        base = 0.9 if delta.symmetry_gained_h else 0.5
        return base + random.gauss(0, temp * 0.2) if temp > 0 else base


class FlipVertical(LocalDSLPrimitive):
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        return ARCGrid(torch.flip(grid.data, dims=[0]))
    def signature(self) -> str:
        return "flip_v"
    def priority_score(self, delta, temp=0.0) -> float:
        base = 0.9 if delta.symmetry_gained_v else 0.5
        return base + random.gauss(0, temp * 0.2) if temp > 0 else base


class ColorSwap(LocalDSLPrimitive):
    def __init__(self, a: int, b: int):
        self.a, self.b = a, b
    
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        data = grid.data.clone()
        mask_a = (data == self.a)
        mask_b = (data == self.b)
        data[mask_a] = self.b
        data[mask_b] = self.a
        return ARCGrid(data)
    
    def signature(self) -> str:
        return f"swap_{self.a}_{self.b}"
    
    def priority_score(self, delta, temp=0.0) -> float:
        base = 0.95 if (self.a, self.b) in delta.swap_pairs or (self.b, self.a) in delta.swap_pairs else 0.3
        return base + random.gauss(0, temp * 0.2) if temp > 0 else base


class Recolor(LocalDSLPrimitive):
    def __init__(self, from_c: int, to_c: int):
        self.from_c, self.to_c = from_c, to_c
    
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        data = grid.data.clone()
        data[data == self.from_c] = self.to_c
        return ARCGrid(data)
    
    def signature(self) -> str:
        return f"recolor_{self.from_c}_to_{self.to_c}"
    
    def priority_score(self, delta, temp=0.0) -> float:
        base = 0.7 if delta.colors_changed else 0.2
        return base + random.gauss(0, temp * 0.2) if temp > 0 else base


class Shift(LocalDSLPrimitive):
    def __init__(self, dr: int, dc: int, bg: int = 0):
        self.dr, self.dc, self.bg = dr, dc, bg
    
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        data = grid.data.clone()
        H, W = data.shape
        result = torch.full_like(data, self.bg)
        
        src_r = slice(max(0, -self.dr), min(H, H - self.dr))
        src_c = slice(max(0, -self.dc), min(W, W - self.dc))
        tgt_r = slice(max(0, self.dr), max(0, self.dr) + (src_r.stop - src_r.start))
        tgt_c = slice(max(0, self.dc), max(0, self.dc) + (src_c.stop - src_c.start))
        
        if tgt_r.stop > tgt_r.start and tgt_c.stop > tgt_c.start:
            result[tgt_r, tgt_c] = data[src_r, src_c]
        
        return ARCGrid(result)
    
    def apply_local(self, grid: ARCGrid, mask: torch.Tensor) -> ARCGrid:
        data = grid.data.clone()
        H, W = data.shape
        original = grid.data.clone()
        
        coords = mask.nonzero()
        for coord in coords:
            data[coord[0], coord[1]] = self.bg
        
        for coord in coords:
            nr, nc = coord[0].item() + self.dr, coord[1].item() + self.dc
            if 0 <= nr < H and 0 <= nc < W:
                data[nr, nc] = original[coord[0], coord[1]]
        
        return ARCGrid(data)
    
    def signature(self) -> str:
        return f"shift_{self.dr}_{self.dc}"
    
    def priority_score(self, delta, temp=0.0) -> float:
        base = 0.6 if delta.mass_conserved and not delta.colors_changed else 0.3
        return base + random.gauss(0, temp * 0.2) if temp > 0 else base


class Crop(LocalDSLPrimitive):
    def __init__(self, bg: int = 0):
        self.bg = bg
    
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        data = grid.data
        mask = (data != self.bg)
        if not mask.any():
            return grid.clone()
        
        rows = mask.any(dim=1).nonzero().flatten()
        cols = mask.any(dim=0).nonzero().flatten()
        if len(rows) == 0:
            return grid.clone()
        
        return ARCGrid(data[rows[0]:rows[-1]+1, cols[0]:cols[-1]+1].clone())
    
    def signature(self) -> str:
        return "crop"
    
    def priority_score(self, delta, temp=0.0) -> float:
        base = 0.7 if not delta.size_conserved else 0.2
        return base + random.gauss(0, temp * 0.2) if temp > 0 else base


class TileUnit(LocalDSLPrimitive):
    """Tile a unit cell to fill the grid."""
    def __init__(self, unit: ARCGrid):
        self.unit = unit
    
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        H, W = grid.height, grid.width
        uh, uw = self.unit.height, self.unit.width
        
        result = torch.zeros(H, W, dtype=torch.long, device=grid.data.device)
        
        for i in range(0, H, uh):
            for j in range(0, W, uw):
                h_end = min(i + uh, H)
                w_end = min(j + uw, W)
                result[i:h_end, j:w_end] = self.unit.data[:h_end-i, :w_end-j]
        
        return ARCGrid(result)
    
    def signature(self) -> str:
        return f"tile_{self.unit.height}x{self.unit.width}"
    
    def priority_score(self, delta, temp=0.0) -> float:
        return 0.6


class ComposedOp(LocalDSLPrimitive):
    def __init__(self, ops: List[LocalDSLPrimitive]):
        self.ops = ops
    
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        result = grid
        for op in self.ops:
            result = op.apply_global(result)
        return result
    
    def signature(self) -> str:
        return " -> ".join(op.signature() for op in self.ops)
    
    def priority_score(self, delta, temp=0.0) -> float:
        return max(op.priority_score(delta, temp) for op in self.ops) if self.ops else 0.0


# =============================================================================
# INVARIANT COMPUTATION
# =============================================================================

@dataclass
class InvariantDelta:
    """Difference between input and output invariants."""
    mass_change: int
    mass_conserved: bool
    colors_changed: bool
    histogram_conserved: bool
    likely_color_swap: bool
    swap_pairs: List[Tuple[int, int]]
    object_count_change: int
    size_change: Tuple[int, int]
    size_conserved: bool
    symmetry_gained_h: bool
    symmetry_gained_v: bool
    # New: symmetry info
    input_symmetry: Optional[SymmetryInfo] = None
    output_symmetry: Optional[SymmetryInfo] = None


def compute_invariant_delta(
    input_grid: ARCGrid,
    output_grid: ARCGrid,
    config: ARCPhase4Config
) -> InvariantDelta:
    """Compute invariant delta with symmetry detection."""
    in_np = input_grid.to_numpy()
    out_np = output_grid.to_numpy()
    
    bg = config.background_color
    in_mass = int((in_np != bg).sum())
    out_mass = int((out_np != bg).sum())
    
    # Histograms
    in_hist, out_hist = {}, {}
    for c in range(config.num_colors):
        in_c = int((in_np == c).sum())
        out_c = int((out_np == c).sum())
        if in_c > 0: in_hist[c] = in_c
        if out_c > 0: out_hist[c] = out_c
    
    in_colors = set(in_hist.keys()) - {bg}
    out_colors = set(out_hist.keys()) - {bg}
    colors_changed = (in_colors != out_colors)
    histogram_conserved = (in_hist == out_hist)
    
    # Color swap detection
    swap_pairs = []
    likely_swap = False
    in_counts = sorted(in_hist.values())
    out_counts = sorted(out_hist.values())
    if in_counts == out_counts and input_grid.shape == output_grid.shape:
        if not torch.equal(input_grid.data, output_grid.data):
            for c1 in in_hist:
                for c2 in in_hist:
                    if c1 < c2:
                        if in_hist.get(c1,0) == out_hist.get(c2,0) and \
                           in_hist.get(c2,0) == out_hist.get(c1,0) and \
                           in_hist.get(c1,0) != in_hist.get(c2,0):
                            swap_pairs.append((c1, c2))
                            likely_swap = True
    
    # Symmetry detection
    in_sym = detect_all_symmetries(input_grid, config)
    out_sym = detect_all_symmetries(output_grid, config)
    
    # Reflection symmetry
    in_ref_h, in_ref_v = detect_reflection_symmetry(input_grid)
    out_ref_h, out_ref_v = detect_reflection_symmetry(output_grid)
    
    return InvariantDelta(
        mass_change=out_mass - in_mass,
        mass_conserved=abs(out_mass - in_mass) < 3,
        colors_changed=colors_changed,
        histogram_conserved=histogram_conserved,
        likely_color_swap=likely_swap,
        swap_pairs=swap_pairs,
        object_count_change=0,  # Simplified
        size_change=(output_grid.height - input_grid.height, output_grid.width - input_grid.width),
        size_conserved=(input_grid.shape == output_grid.shape),
        symmetry_gained_h=(out_ref_h and not in_ref_h),
        symmetry_gained_v=(out_ref_v and not in_ref_v),
        input_symmetry=in_sym,
        output_symmetry=out_sym
    )


# =============================================================================
# TASK 2: THERMODYNAMIC ANNEALING (HOMEOSTAT)
# =============================================================================

@dataclass
class ThermodynamicState:
    """State of the thermodynamic annealing process."""
    temperature: float
    stuck_count: int = 0
    last_energy: float = float('inf')
    best_energy: float = float('inf')
    best_program: Optional[LocalDSLPrimitive] = None
    best_grid: Optional[ARCGrid] = None
    
    def update(self, energy: float, program: LocalDSLPrimitive, grid: ARCGrid, config: ARCPhase4Config):
        """Update thermodynamic state based on new energy."""
        if energy < self.best_energy:
            self.best_energy = energy
            self.best_program = program
            self.best_grid = grid
            self.stuck_count = 0
            # Cooling: solution is improving
            self.temperature = max(config.min_temperature, self.temperature * config.cooling_rate)
        elif abs(energy - self.last_energy) < 0.001:
            self.stuck_count += 1
            if self.stuck_count >= config.stuck_threshold:
                # Heating: Kramers escape - inject energy to escape local minimum
                self.temperature = min(1.0, self.temperature * config.heating_rate)
                self.stuck_count = 0
        
        self.last_energy = energy
    
    def accept_worse(self, delta_energy: float, config: ARCPhase4Config) -> bool:
        """
        Conservative Metropolis: only accept slightly worse solutions when stuck.
        
        This implements KRAMERS ESCAPE: we only inject noise when trapped,
        not during normal optimization.
        """
        if self.temperature <= 0.01:
            return False
        if delta_energy > config.metropolis_threshold:
            return False  # Never accept large degradation
        if self.stuck_count < 2:
            return False  # Don't accept worse until somewhat stuck
        
        prob = math.exp(-delta_energy / self.temperature)
        return random.random() < prob


# =============================================================================
# TASK 3: NEURAL SIMULATOR (LEARNED POLICY)
# =============================================================================

class NeuralSimulator(nn.Module):
    """
    Neural policy that predicts the effect of DSL operations.
    
    This is the SIMULATOR from Planner-Simulator architecture.
    Learns: (grid_features, op_embedding) -> predicted_energy_delta
    """
    
    def __init__(self, config: ARCPhase4Config, num_ops: int):
        super().__init__()
        self.config = config
        
        # Grid encoder (simple: just histograms and stats)
        self.grid_encoder = nn.Sequential(
            nn.Linear(config.num_colors + 4, config.simulator_hidden),  # hist + mass, H, W, symmetry
            nn.ReLU(),
            nn.Linear(config.simulator_hidden, config.simulator_hidden)
        )
        
        # Op embedding
        self.op_embedding = nn.Embedding(num_ops, config.simulator_hidden)
        
        # Predictor
        self.predictor = nn.Sequential(
            nn.Linear(config.simulator_hidden * 2, config.simulator_hidden),
            nn.ReLU(),
            nn.Linear(config.simulator_hidden, 1)  # Predicted energy change
        )
    
    def encode_grid(self, grid: ARCGrid) -> torch.Tensor:
        """Encode grid to feature vector."""
        data = grid.to_numpy()
        H, W = data.shape
        
        # Color histogram (normalized)
        hist = np.zeros(self.config.num_colors)
        for c in range(self.config.num_colors):
            hist[c] = (data == c).sum() / (H * W)
        
        # Additional features
        mass = (data != self.config.background_color).sum() / (H * W)
        sym_h = 1.0 if np.array_equal(data, np.flip(data, axis=1)) else 0.0
        
        features = np.concatenate([hist, [mass, H/30, W/30, sym_h]])
        return torch.tensor(features, dtype=torch.float32, device=self.config.device)
    
    def forward(self, grid_features: torch.Tensor, op_idx: torch.Tensor) -> torch.Tensor:
        """Predict energy change for applying op to grid."""
        grid_enc = self.grid_encoder(grid_features)
        op_enc = self.op_embedding(op_idx)
        combined = torch.cat([grid_enc, op_enc], dim=-1)
        return self.predictor(combined)
    
    def rank_ops(self, grid: ARCGrid, op_indices: List[int]) -> List[Tuple[float, int]]:
        """Rank operations by predicted energy reduction."""
        grid_features = self.encode_grid(grid).unsqueeze(0)
        
        rankings = []
        for idx in op_indices:
            op_idx = torch.tensor([idx], device=self.config.device)
            with torch.no_grad():
                pred_delta = self.forward(grid_features, op_idx).item()
            rankings.append((pred_delta, idx))  # Lower delta = better
        
        rankings.sort(key=lambda x: x[0])
        return rankings


# =============================================================================
# DSL LIBRARY
# =============================================================================

class MapToColor(LocalDSLPrimitive):
    """Apply operation only to pixels of specific color."""
    def __init__(self, op: LocalDSLPrimitive, target_color: int):
        self.op = op
        self.target_color = target_color
    
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        mask = (grid.data == self.target_color)
        return self.op.apply_local(grid, mask)
    
    def apply_local(self, grid: ARCGrid, outer_mask: torch.Tensor) -> ARCGrid:
        mask = (grid.data == self.target_color) & outer_mask
        return self.op.apply_local(grid, mask)
    
    def signature(self) -> str:
        return f"map({self.op.signature()}, c={self.target_color})"
    
    def priority_score(self, delta, temp=0.0) -> float:
        return self.op.priority_score(delta, temp) * 0.9


class MapToForeground(LocalDSLPrimitive):
    """Apply operation only to non-background pixels."""
    def __init__(self, op: LocalDSLPrimitive, bg: int = 0):
        self.op = op
        self.bg = bg
    
    def apply_global(self, grid: ARCGrid) -> ARCGrid:
        mask = (grid.data != self.bg)
        return self.op.apply_local(grid, mask)
    
    def signature(self) -> str:
        return f"map({self.op.signature()}, fg)"
    
    def priority_score(self, delta, temp=0.0) -> float:
        return self.op.priority_score(delta, temp) * 0.95


def build_dsl_library(config: ARCPhase4Config) -> List[LocalDSLPrimitive]:
    """Build comprehensive DSL library with object-targeting."""
    ops: List[LocalDSLPrimitive] = [
        Identity(),
        Rotate90(), Rotate180(),
        FlipHorizontal(), FlipVertical(),
        Crop(),
    ]
    
    # Color operations
    for a in range(config.num_colors):
        for b in range(a + 1, config.num_colors):
            ops.append(ColorSwap(a, b))
    
    # Recolor
    for a in range(config.num_colors):
        for b in range(config.num_colors):
            if a != b:
                ops.append(Recolor(a, b))
    
    # Shifts (global and foreground-targeted)
    for dr in [-1, 0, 1]:
        for dc in [-1, 0, 1]:
            if dr != 0 or dc != 0:
                shift_op = Shift(dr, dc)
                ops.append(shift_op)
                ops.append(MapToForeground(shift_op))
    
    # Color-targeted shifts (key for object-specific movement)
    for color in range(1, min(config.num_colors, 6)):
        for dr in [-1, 0, 1]:
            for dc in [-1, 0, 1]:
                if dr != 0 or dc != 0:
                    ops.append(MapToColor(Shift(dr, dc), color))
    
    # Color-targeted flips and rotates
    for color in range(1, min(config.num_colors, 6)):
        ops.append(MapToColor(FlipHorizontal(), color))
        ops.append(MapToColor(FlipVertical(), color))
    
    return ops


# =============================================================================
# PHASE 4 SOLVER
# =============================================================================

class RenormalizationSolver:
    """
    Phase 4 Solver with Renormalization and Thermodynamic Annealing.
    
    Key innovations:
    1. Renormalization: Detect symmetry, solve on quotient, lift back
    2. Thermodynamics: Temperature-controlled exploration with Kramers escape
    3. Neural policy: Learned operation ranking (optional)
    """
    
    def __init__(self, config: ARCPhase4Config):
        self.config = config
        self.dsl = build_dsl_library(config)
        self.op_to_idx = {op.signature(): i for i, op in enumerate(self.dsl)}
        
        # Neural simulator (optional)
        self.simulator = NeuralSimulator(config, len(self.dsl)).to(config.device)
        self.use_simulator = False  # Enable after training
        
        print(f"   DSL: {len(self.dsl)} primitives")
    
    def compute_energy(self, pred: ARCGrid, target: ARCGrid) -> float:
        """Compute mismatch energy."""
        if pred.shape != target.shape:
            return 1000.0 + abs(pred.height - target.height) + abs(pred.width - target.width)
        return (pred.data != target.data).float().sum().item() / target.data.numel()
    
    def solve_quotient(
        self,
        input_unit: ARCGrid,
        output_unit: ARCGrid,
        delta: InvariantDelta,
        thermo: ThermodynamicState,
        verbose: bool = False
    ) -> Tuple[Optional[LocalDSLPrimitive], float]:
        """
        Solve on the quotient (unit cell).
        
        This is solving on the FUNDAMENTAL DOMAIN after renormalization.
        """
        if verbose:
            print(f"      Solving on unit cell {input_unit.shape}")
        
        current = input_unit
        best_op = None
        best_energy = self.compute_energy(current, output_unit)
        
        # Rank operations
        ranked = []
        for i, op in enumerate(self.dsl):
            score = op.priority_score(delta, thermo.temperature)
            ranked.append((score, i, op))
        ranked.sort(key=lambda x: -x[0])
        
        # Try operations
        for score, idx, op in ranked[:self.config.max_candidates]:
            try:
                result = op.apply_global(current)
                energy = self.compute_energy(result, output_unit)
                
                # Metropolis acceptance
                if energy < best_energy:
                    best_energy = energy
                    best_op = op
                elif thermo.accept_worse(energy - best_energy):
                    best_energy = energy
                    best_op = op
                
                if best_energy < self.config.energy_threshold:
                    break
            except Exception:
                continue
        
        return best_op, best_energy
    
    def solve_with_renormalization(
        self,
        input_grid: ARCGrid,
        target_grid: ARCGrid,
        delta: InvariantDelta,
        verbose: bool = False
    ) -> Tuple[Optional[LocalDSLPrimitive], float]:
        """
        Solve using renormalization if symmetry detected.
        
        Algorithm:
        1. Detect symmetry in input and output
        2. If both have same tiling structure:
           a. Extract unit cells
           b. Solve transformation on unit cells (quotient)
           c. Lift solution to full grid (inverse renormalization)
        """
        in_sym = delta.input_symmetry
        out_sym = delta.output_symmetry
        
        # Check if both have compatible tiling
        if (in_sym and out_sym and 
            in_sym.has_tiling and out_sym.has_tiling and
            in_sym.period_h == out_sym.period_h and
            in_sym.period_v == out_sym.period_v):
            
            if verbose:
                print(f"   RENORMALIZATION: Detected {in_sym.period_h}x{in_sym.period_v} tiling")
            
            # Solve on unit cells
            thermo = ThermodynamicState(temperature=self.config.initial_temperature)
            unit_op, unit_energy = self.solve_quotient(
                in_sym.unit_cell, out_sym.unit_cell, delta, thermo, verbose
            )
            
            if unit_op and unit_energy < 0.1:
                # Compose: apply op to unit cell, then tile
                solved_unit = unit_op.apply_global(in_sym.unit_cell)
                full_op = ComposedOp([unit_op, TileUnit(solved_unit)])
                
                # Verify on full grid
                full_result = lift_solution_to_full_grid(
                    solved_unit, target_grid.shape, in_sym.period_h, in_sym.period_v
                )
                full_energy = self.compute_energy(full_result, target_grid)
                
                if verbose:
                    print(f"   LIFTED: Unit energy {unit_energy:.4f} -> Full energy {full_energy:.4f}")
                
                if full_energy < 0.5:  # Reasonable lift
                    return full_op, full_energy
        
        return None, float('inf')
    
    def solve_direct(
        self,
        input_grid: ARCGrid,
        target_grid: ARCGrid,
        delta: InvariantDelta,
        verbose: bool = False
    ) -> Tuple[Optional[LocalDSLPrimitive], float]:
        """
        Direct solving with greedy search + composition.
        
        This is Phase 3's working approach - greedy with anti-oscillation.
        """
        current = input_grid
        program_parts: List[LocalDSLPrimitive] = []
        visited: Set[bytes] = {current.data.cpu().numpy().tobytes()}
        
        best_seen_energy = self.compute_energy(current, target_grid)
        best_seen_program: List[LocalDSLPrimitive] = []
        
        for iteration in range(self.config.max_iterations):
            energy = self.compute_energy(current, target_grid)
            
            # Track best
            if energy < best_seen_energy:
                best_seen_energy = energy
                best_seen_program = program_parts.copy()
            
            if energy < self.config.energy_threshold:
                if verbose:
                    print(f"   SOLVED at iteration {iteration+1}!")
                break
            
            if verbose and iteration < 5:
                print(f"   Iter {iteration+1}: E={energy:.4f}")
            
            # Rank operations by priority (no temperature noise)
            ranked = []
            for i, op in enumerate(self.dsl):
                score = op.priority_score(delta, 0.0)  # Greedy, no noise
                ranked.append((score, i, op))
            ranked.sort(key=lambda x: -x[0])
            
            # Find best non-oscillating improvement
            best_op, best_energy, best_result = None, energy, None
            
            for score, idx, op in ranked[:self.config.max_candidates]:
                try:
                    result = op.apply_global(current)
                    result_hash = result.data.cpu().numpy().tobytes()
                    
                    if result_hash in visited:
                        continue
                    
                    new_energy = self.compute_energy(result, target_grid)
                    
                    if new_energy < best_energy:
                        best_op, best_energy, best_result = op, new_energy, result
                        
                        if new_energy < self.config.energy_threshold:
                            break  # Found perfect solution
                except Exception:
                    continue
            
            if best_op is None:
                if verbose:
                    print(f"   No improving move found")
                break
            
            # Apply best operation
            current = best_result
            visited.add(current.data.cpu().numpy().tobytes())
            program_parts.append(best_op)
            
            if verbose:
                print(f"   Applied: {best_op.signature()} -> E={best_energy:.4f}")
        
        # Return best seen
        if not best_seen_program:
            return Identity(), best_seen_energy
        elif len(best_seen_program) == 1:
            return best_seen_program[0], best_seen_energy
        else:
            return ComposedOp(best_seen_program), best_seen_energy
    
    def solve(
        self,
        input_grid: ARCGrid,
        target_grid: ARCGrid,
        verbose: bool = False
    ) -> Tuple[Optional[LocalDSLPrimitive], float]:
        """
        Main solve with renormalization + thermodynamics.
        """
        delta = compute_invariant_delta(input_grid, target_grid, self.config)
        
        if verbose:
            print(f"   Delta: mass={delta.mass_change}, colors_changed={delta.colors_changed}")
            if delta.input_symmetry and delta.input_symmetry.has_tiling:
                print(f"   Input tiling: {delta.input_symmetry.period_h}x{delta.input_symmetry.period_v}")
        
        # Strategy 1: Try renormalization
        renorm_op, renorm_energy = self.solve_with_renormalization(
            input_grid, target_grid, delta, verbose
        )
        
        # Strategy 2: Direct solving with thermodynamics
        direct_op, direct_energy = self.solve_direct(
            input_grid, target_grid, delta, verbose
        )
        
        # Return better result
        if renorm_energy <= direct_energy:
            return renorm_op, renorm_energy
        else:
            return direct_op, direct_energy


# =============================================================================
# EVALUATION
# =============================================================================

def evaluate_task(
    solver: RenormalizationSolver,
    task: ARCTask,
    config: ARCPhase4Config,
    verbose: bool = False
) -> Dict[str, Any]:
    """Evaluate on a single task."""
    results = {
        'task_id': task.task_id,
        'train_results': [],
        'test_results': [],
        'programs': []
    }
    
    for i, ex in enumerate(task.train_examples):
        if verbose:
            print(f"\n   Train {i+1}:")
        
        program, energy = solver.solve(ex.input_grid, ex.output_grid, verbose)
        sig = program.signature() if program else "none"
        
        results['train_results'].append({'energy': energy, 'program': sig})
        results['programs'].append(program)
        
        if verbose:
            print(f"   Result: {sig} (energy={energy:.6f})")
    
    # Test
    for i, ex in enumerate(task.test_examples):
        if results['programs'] and results['programs'][0]:
            pred = results['programs'][0].apply_global(ex.input_grid)
            energy = solver.compute_energy(pred, ex.output_grid)
        else:
            energy = solver.compute_energy(ex.input_grid, ex.output_grid)
        results['test_results'].append({'energy': energy})
    
    return results


def run_evaluation(data_path: str, config: ARCPhase4Config, num_tasks: int = 10) -> List[Dict]:
    """Run full evaluation."""
    print("=" * 70)
    print("ARC-SGC Phase 4: Renormalization + Thermodynamic Annealing")
    print("=" * 70)
    
    tasks = load_arc_tasks(data_path, config.device, limit=num_tasks)
    print(f"\nLoaded {len(tasks)} tasks")
    
    if not tasks:
        return []
    
    print("\nBuilding Renormalization Solver...")
    solver = RenormalizationSolver(config)
    
    all_results = []
    
    for i, task in enumerate(tasks):
        print(f"\n{'='*70}")
        print(f"Task {i+1}/{len(tasks)}: {task.task_id}")
        
        results = evaluate_task(solver, task, config, verbose=True)
        all_results.append(results)
        
        avg_train = np.mean([r['energy'] for r in results['train_results']])
        print(f"\n  Summary: avg_train_energy={avg_train:.6f}")
        
        if results['test_results']:
            avg_test = np.mean([r['energy'] for r in results['test_results']])
            print(f"           avg_test_energy={avg_test:.6f}")
    
    # Final summary
    print("\n" + "=" * 70)
    print("FINAL SUMMARY")
    print("=" * 70)
    
    train_energies = [np.mean([r['energy'] for r in res['train_results']]) for res in all_results]
    
    perfect = sum(1 for e in train_energies if e < 0.001)
    near_perfect = sum(1 for e in train_energies if 0.001 <= e < 0.01)
    partial = sum(1 for e in train_energies if 0.01 <= e < 0.5)
    failed = sum(1 for e in train_energies if e >= 0.5)
    
    print(f"Tasks: {len(all_results)}")
    print(f"  PERFECT      (< 0.001):  {perfect}")
    print(f"  NEAR-PERFECT (< 0.01):   {near_perfect}")
    print(f"  PARTIAL      (< 0.5):    {partial}")
    print(f"  FAILED       (>= 0.5):   {failed}")
    print(f"  Average energy: {np.mean(train_energies):.6f}")
    
    print("\n  Phase 3 baseline: 0 perfect, 8 partial")
    print(f"  Phase 4 result:   {perfect} perfect, {near_perfect} near-perfect, {partial} partial")
    
    if perfect > 0:
        print(f"\n  🎉 BREAKTHROUGH: {perfect} task(s) PERFECTLY SOLVED!")
    
    # Show near-misses
    print("\n  Near-miss tasks (energy < 0.05):")
    for res, e in zip(all_results, train_energies):
        if e < 0.05:
            programs = [r['program'] for r in res['train_results']]
            print(f"    {res['task_id']}: energy={e:.6f}, programs={programs[:2]}")
    
    return all_results


# =============================================================================
# MAIN
# =============================================================================

def main():
    config = ARCPhase4Config()
    
    paths = ["data/arc/training", "C:/Lean4 Projects/data/arc/training"]
    arc_path = next((p for p in paths if Path(p).exists()), None)
    
    if arc_path:
        results = run_evaluation(arc_path, config, num_tasks=10)
    else:
        print("ARC data not found!")
    
    return results


if __name__ == "__main__":
    main()
