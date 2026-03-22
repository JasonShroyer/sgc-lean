"""
ARC-SGC: Sheaf-Theoretic Program Synthesis for ARC

THEORY (Physics-First Approach):

This implementation treats ARC as a PHYSICS problem:
- Unsolved grid = High-energy configuration
- Solved grid = Ground state (minimum energy)
- DSL primitives = Sheaf restriction maps L_uv: V_u → V_v
- Learning = Relaxing the field via sheaf diffusion

THE THREE PILLARS (from SGC):

1. TERRITORY (Physics):
   - ARC grid as a cellular sheaf over a graph
   - Each cell has a stalk (color + features)
   - Edges encode spatial/semantic relationships
   - DSL operations are restriction maps

2. SHEAF LAPLACIAN (Loss):
   - L_F = D - A where D = degree, A = weighted adjacency
   - Loss = <x, L_F x> = sum of squared "inconsistencies"
   - NOT MSE - this is local-to-global consistency

3. FUNCTIONAL BLANKET (Symmetry):
   - DSL primitives grouped by algebraic equivalence
   - "Rotate90" and "Rotate270 ∘ Rotate180" are equivalent
   - Prevents wasted exploration

REFERENCES:
- SGC.FunctionalBlanket.lean: Functional defect theory
- SGC.Bridge.Quantum.lean: Sheaf-theoretic connections
- docs/lifshitz_transition_theory.md: Phase transition framework
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
from dataclasses import dataclass, field
from typing import List, Tuple, Dict, Optional, Callable, Set
from enum import Enum, auto
from abc import ABC, abstractmethod
import numpy as np
import json
import os
from pathlib import Path


# =============================================================================
# CONFIGURATION
# =============================================================================

@dataclass
class ARCSheafConfig:
    """Configuration for ARC-SGC Sheaf Network."""
    
    # Grid properties
    max_grid_size: int = 30  # ARC grids up to 30x30
    num_colors: int = 10     # 0-9 colors in ARC
    
    # Sheaf structure
    stalk_dim: int = 32      # Dimension of stalk vector at each cell
    edge_dim: int = 16       # Dimension of edge features
    
    # Diffusion
    diffusion_steps: int = 5
    diffusion_dt: float = 0.1
    
    # DSL
    max_program_length: int = 5  # Max DSL operations to compose
    
    # Training
    epochs: int = 100
    batch_size: int = 16
    lr: float = 1e-3
    
    # Functional blanket
    equivalence_threshold: float = 0.01  # DSL ops with defect < this are equivalent
    
    device: str = 'cuda' if torch.cuda.is_available() else 'cpu'


# =============================================================================
# ARC DATA STRUCTURES
# =============================================================================

@dataclass
class ARCGrid:
    """
    An ARC grid represented as a tensor.
    
    Internally stored as (H, W) tensor with integer color values 0-9.
    """
    data: torch.Tensor  # Shape: (H, W), dtype: long
    
    @property
    def height(self) -> int:
        return self.data.shape[0]
    
    @property
    def width(self) -> int:
        return self.data.shape[1]
    
    @property
    def shape(self) -> Tuple[int, int]:
        return (self.height, self.width)
    
    def to_onehot(self, num_colors: int = 10) -> torch.Tensor:
        """Convert to one-hot encoding: (H, W, C)."""
        return F.one_hot(self.data, num_classes=num_colors).float()
    
    @classmethod
    def from_list(cls, grid_list: List[List[int]], device: str = 'cpu') -> 'ARCGrid':
        """Create from nested list (ARC JSON format)."""
        return cls(torch.tensor(grid_list, dtype=torch.long, device=device))
    
    def clone(self) -> 'ARCGrid':
        return ARCGrid(self.data.clone())


@dataclass
class ARCExample:
    """A single input-output example from an ARC task."""
    input_grid: ARCGrid
    output_grid: ARCGrid


@dataclass  
class ARCTask:
    """
    An ARC task with training and test examples.
    
    The goal is to learn the transformation from training examples
    and apply it to test inputs.
    """
    task_id: str
    train_examples: List[ARCExample]
    test_examples: List[ARCExample]
    
    @classmethod
    def from_json(cls, task_id: str, data: dict, device: str = 'cpu') -> 'ARCTask':
        """Load from ARC JSON format."""
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


class ARCDataset:
    """
    Dataset of ARC tasks.
    
    Loads from the standard ARC directory structure:
    - training/: 400 training tasks
    - evaluation/: 400 evaluation tasks
    """
    
    def __init__(self, data_dir: str, device: str = 'cpu'):
        self.data_dir = Path(data_dir)
        self.device = device
        self.tasks: Dict[str, ARCTask] = {}
        
    def load_training(self) -> 'ARCDataset':
        """Load training tasks."""
        train_dir = self.data_dir / 'training'
        if train_dir.exists():
            self._load_dir(train_dir)
        return self
    
    def load_evaluation(self) -> 'ARCDataset':
        """Load evaluation tasks."""
        eval_dir = self.data_dir / 'evaluation'
        if eval_dir.exists():
            self._load_dir(eval_dir)
        return self
    
    def _load_dir(self, dir_path: Path):
        """Load all tasks from a directory."""
        for json_file in dir_path.glob('*.json'):
            task_id = json_file.stem
            with open(json_file, 'r') as f:
                data = json.load(f)
            self.tasks[task_id] = ARCTask.from_json(task_id, data, self.device)
    
    def __len__(self) -> int:
        return len(self.tasks)
    
    def __getitem__(self, task_id: str) -> ARCTask:
        return self.tasks[task_id]
    
    def items(self):
        return self.tasks.items()


# =============================================================================
# SHEAF STRUCTURE
# =============================================================================

class CellularSheaf:
    """
    A Cellular Sheaf over an ARC grid.
    
    MATHEMATICAL STRUCTURE:
    - Base space: Graph G = (V, E) where V = grid cells
    - Stalks: F(v) = R^d (feature vector at each cell)
    - Restriction maps: F_{uv}: F(u) → F(v) (linear maps on edges)
    
    The Sheaf Laplacian L_F generalizes the graph Laplacian to
    vector-valued signals on nodes.
    """
    
    def __init__(self, grid: ARCGrid, stalk_dim: int, config: ARCSheafConfig):
        self.grid = grid
        self.stalk_dim = stalk_dim
        self.config = config
        self.device = grid.data.device
        
        # Build graph structure
        self.num_nodes = grid.height * grid.width
        self.edges, self.edge_types = self._build_edges()
        self.num_edges = len(self.edges)
        
        # Initialize stalks (node features)
        self.stalks = self._init_stalks()
        
        # Initialize restriction maps (edge transformations)
        # These will be learned or set by DSL operations
        self.restriction_maps = self._init_restriction_maps()
    
    def _build_edges(self) -> Tuple[List[Tuple[int, int]], Dict[str, List[int]]]:
        """
        Build edge list for 4-connected grid graph.
        
        Returns:
            edges: List of (u, v) pairs
            edge_types: Dict mapping type names to edge indices
        """
        edges = []
        edge_types = {'horizontal': [], 'vertical': []}
        
        H, W = self.grid.height, self.grid.width
        
        for r in range(H):
            for c in range(W):
                node = r * W + c
                
                # Horizontal edge (right neighbor)
                if c + 1 < W:
                    neighbor = r * W + (c + 1)
                    edge_types['horizontal'].append(len(edges))
                    edges.append((node, neighbor))
                
                # Vertical edge (down neighbor)
                if r + 1 < H:
                    neighbor = (r + 1) * W + c
                    edge_types['vertical'].append(len(edges))
                    edges.append((node, neighbor))
        
        return edges, edge_types
    
    def _init_stalks(self) -> torch.Tensor:
        """
        Initialize stalk vectors from grid colors.
        
        Maps each cell's color to a learned embedding.
        Shape: (num_nodes, stalk_dim)
        """
        # One-hot encode colors, then project to stalk dimension
        onehot = self.grid.to_onehot(self.config.num_colors)  # (H, W, 10)
        flat = onehot.view(-1, self.config.num_colors)  # (num_nodes, 10)
        
        # Simple linear projection (in practice, this would be learned)
        # For now, pad to stalk_dim
        stalks = torch.zeros(self.num_nodes, self.stalk_dim, device=self.device)
        stalks[:, :self.config.num_colors] = flat
        
        return stalks
    
    def _init_restriction_maps(self) -> torch.Tensor:
        """
        Initialize restriction maps as identity (no transformation).
        
        Shape: (num_edges, stalk_dim, stalk_dim)
        
        F_{uv}: F(u) → F(v) is the restriction map on edge (u,v).
        For identity initialization: F_{uv} = I (signals pass unchanged)
        """
        return torch.eye(
            self.stalk_dim, device=self.device
        ).unsqueeze(0).expand(self.num_edges, -1, -1).clone()
    
    def compute_coboundary(self, x: torch.Tensor) -> torch.Tensor:
        """
        Compute the coboundary operator δ: C^0 → C^1.
        
        For each edge (u, v): (δx)_e = F_{vu} x_v - F_{uv} x_u
        
        This measures the "inconsistency" across each edge.
        
        Args:
            x: Node signals, shape (num_nodes, stalk_dim)
            
        Returns:
            Edge signals, shape (num_edges, stalk_dim)
        """
        coboundary = torch.zeros(self.num_edges, self.stalk_dim, device=self.device)
        
        for e, (u, v) in enumerate(self.edges):
            # F_{uv} @ x_u
            Fu_x = self.restriction_maps[e] @ x[u]
            # For undirected graph, F_{vu} = F_{uv}^T (adjoint)
            Fv_x = self.restriction_maps[e].T @ x[v]
            coboundary[e] = Fv_x - Fu_x
        
        return coboundary
    
    def compute_laplacian_energy(self, x: torch.Tensor) -> torch.Tensor:
        """
        Compute the Sheaf Laplacian quadratic form: <x, L_F x>.
        
        This is THE LOSS FUNCTION for SGC-ARC.
        
        L_F = δ^T δ (Hodge Laplacian)
        <x, L_F x> = ||δx||² = sum of squared inconsistencies
        
        Physical interpretation:
        - High energy = signals don't match across edges
        - Ground state (energy = 0) = globally consistent section
        
        Args:
            x: Node signals, shape (num_nodes, stalk_dim)
            
        Returns:
            Scalar energy value
        """
        coboundary = self.compute_coboundary(x)
        energy = (coboundary ** 2).sum()
        return energy
    
    def diffuse(self, x: torch.Tensor, steps: int, dt: float) -> torch.Tensor:
        """
        Sheaf diffusion: evolve signals toward consistency.
        
        dx/dt = -L_F x (heat equation on sheaf)
        
        This naturally smooths inconsistencies.
        
        Args:
            x: Initial node signals
            steps: Number of diffusion steps
            dt: Time step size
            
        Returns:
            Diffused signals
        """
        for _ in range(steps):
            # Compute gradient of energy
            # ∇_x <x, L_F x> = 2 L_F x = 2 δ^T δ x
            coboundary = self.compute_coboundary(x)
            
            # Accumulate gradient at each node
            grad = torch.zeros_like(x)
            for e, (u, v) in enumerate(self.edges):
                # Contribution to node u
                grad[u] -= self.restriction_maps[e].T @ coboundary[e]
                # Contribution to node v
                grad[v] += self.restriction_maps[e] @ coboundary[e]
            
            # Gradient descent step
            x = x - dt * grad
        
        return x


# =============================================================================
# DSL PRIMITIVES AS SHEAF RESTRICTION MAPS
# =============================================================================

class DSLPrimitive(ABC):
    """
    Abstract base class for DSL primitives.
    
    Each primitive is a SHEAF MORPHISM: a way to transform one sheaf
    into another while preserving (or modifying) the restriction maps.
    
    The key insight: DSL operations aren't just grid transformations,
    they're TRANSPORT of the sheaf structure.
    """
    
    @abstractmethod
    def apply(self, grid: ARCGrid) -> ARCGrid:
        """Apply the transformation to a grid."""
        pass
    
    @abstractmethod
    def get_restriction_map(self, sheaf: CellularSheaf) -> torch.Tensor:
        """
        Get the induced restriction maps for this operation.
        
        This encodes how the operation "transports" information
        across the sheaf structure.
        """
        pass
    
    @abstractmethod
    def signature(self) -> str:
        """Unique signature for equivalence class computation."""
        pass


class IdentityOp(DSLPrimitive):
    """Identity operation: do nothing."""
    
    def apply(self, grid: ARCGrid) -> ARCGrid:
        return grid.clone()
    
    def get_restriction_map(self, sheaf: CellularSheaf) -> torch.Tensor:
        return sheaf.restriction_maps.clone()
    
    def signature(self) -> str:
        return "identity"


class ShiftRight(DSLPrimitive):
    """
    Shift grid contents right by 1.
    
    As a sheaf map: transports stalk at (x,y) to (x+1,y).
    The restriction map encodes this spatial translation.
    """
    
    def __init__(self, amount: int = 1, wrap: bool = False):
        self.amount = amount
        self.wrap = wrap
    
    def apply(self, grid: ARCGrid) -> ARCGrid:
        H, W = grid.height, grid.width
        new_data = torch.zeros_like(grid.data)
        
        for c in range(W):
            src_c = (c - self.amount) % W if self.wrap else c - self.amount
            if 0 <= src_c < W:
                new_data[:, c] = grid.data[:, src_c]
        
        return ARCGrid(new_data)
    
    def get_restriction_map(self, sheaf: CellularSheaf) -> torch.Tensor:
        """
        Shift changes which nodes are connected.
        The restriction map becomes a permutation.
        """
        # For shift, the restriction maps themselves don't change,
        # but the STALKS move to different nodes
        return sheaf.restriction_maps.clone()
    
    def signature(self) -> str:
        return f"shift_right_{self.amount}_{'wrap' if self.wrap else 'nowrap'}"


class ShiftDown(DSLPrimitive):
    """Shift grid contents down by 1."""
    
    def __init__(self, amount: int = 1, wrap: bool = False):
        self.amount = amount
        self.wrap = wrap
    
    def apply(self, grid: ARCGrid) -> ARCGrid:
        H, W = grid.height, grid.width
        new_data = torch.zeros_like(grid.data)
        
        for r in range(H):
            src_r = (r - self.amount) % H if self.wrap else r - self.amount
            if 0 <= src_r < H:
                new_data[r, :] = grid.data[src_r, :]
        
        return ARCGrid(new_data)
    
    def get_restriction_map(self, sheaf: CellularSheaf) -> torch.Tensor:
        return sheaf.restriction_maps.clone()
    
    def signature(self) -> str:
        return f"shift_down_{self.amount}_{'wrap' if self.wrap else 'nowrap'}"


class Rotate90(DSLPrimitive):
    """Rotate grid 90 degrees clockwise."""
    
    def apply(self, grid: ARCGrid) -> ARCGrid:
        # torch.rot90 rotates counter-clockwise, so k=-1 for clockwise
        new_data = torch.rot90(grid.data, k=-1)
        return ARCGrid(new_data)
    
    def get_restriction_map(self, sheaf: CellularSheaf) -> torch.Tensor:
        """
        Rotation permutes both nodes and edges.
        The restriction maps must be permuted accordingly.
        """
        # For rotation, we need to reindex the restriction maps
        # This is a non-trivial sheaf morphism
        return sheaf.restriction_maps.clone()  # Simplified for now
    
    def signature(self) -> str:
        return "rotate_90"


class Rotate180(DSLPrimitive):
    """Rotate grid 180 degrees."""
    
    def apply(self, grid: ARCGrid) -> ARCGrid:
        new_data = torch.rot90(grid.data, k=2)
        return ARCGrid(new_data)
    
    def get_restriction_map(self, sheaf: CellularSheaf) -> torch.Tensor:
        return sheaf.restriction_maps.clone()
    
    def signature(self) -> str:
        return "rotate_180"


class Rotate270(DSLPrimitive):
    """Rotate grid 270 degrees clockwise (= 90 counter-clockwise)."""
    
    def apply(self, grid: ARCGrid) -> ARCGrid:
        new_data = torch.rot90(grid.data, k=1)
        return ARCGrid(new_data)
    
    def get_restriction_map(self, sheaf: CellularSheaf) -> torch.Tensor:
        return sheaf.restriction_maps.clone()
    
    def signature(self) -> str:
        return "rotate_270"


class FlipHorizontal(DSLPrimitive):
    """Flip grid horizontally."""
    
    def apply(self, grid: ARCGrid) -> ARCGrid:
        new_data = torch.flip(grid.data, dims=[1])
        return ARCGrid(new_data)
    
    def get_restriction_map(self, sheaf: CellularSheaf) -> torch.Tensor:
        return sheaf.restriction_maps.clone()
    
    def signature(self) -> str:
        return "flip_horizontal"


class FlipVertical(DSLPrimitive):
    """Flip grid vertically."""
    
    def apply(self, grid: ARCGrid) -> ARCGrid:
        new_data = torch.flip(grid.data, dims=[0])
        return ARCGrid(new_data)
    
    def get_restriction_map(self, sheaf: CellularSheaf) -> torch.Tensor:
        return sheaf.restriction_maps.clone()
    
    def signature(self) -> str:
        return "flip_vertical"


class ColorSwap(DSLPrimitive):
    """Swap two colors throughout the grid."""
    
    def __init__(self, color1: int, color2: int):
        self.color1 = color1
        self.color2 = color2
    
    def apply(self, grid: ARCGrid) -> ARCGrid:
        new_data = grid.data.clone()
        mask1 = grid.data == self.color1
        mask2 = grid.data == self.color2
        new_data[mask1] = self.color2
        new_data[mask2] = self.color1
        return ARCGrid(new_data)
    
    def get_restriction_map(self, sheaf: CellularSheaf) -> torch.Tensor:
        """
        Color swap is a LOCAL operation on stalks.
        It induces a permutation matrix on the color channels.
        """
        # Create permutation that swaps color1 and color2
        perm = torch.eye(sheaf.stalk_dim, device=sheaf.device)
        if self.color1 < sheaf.stalk_dim and self.color2 < sheaf.stalk_dim:
            perm[self.color1, self.color1] = 0
            perm[self.color2, self.color2] = 0
            perm[self.color1, self.color2] = 1
            perm[self.color2, self.color1] = 1
        
        # Apply to all restriction maps
        new_maps = sheaf.restriction_maps.clone()
        for e in range(sheaf.num_edges):
            new_maps[e] = perm @ new_maps[e] @ perm.T
        
        return new_maps
    
    def signature(self) -> str:
        c1, c2 = min(self.color1, self.color2), max(self.color1, self.color2)
        return f"color_swap_{c1}_{c2}"


class FillColor(DSLPrimitive):
    """Fill entire grid with a single color."""
    
    def __init__(self, color: int):
        self.color = color
    
    def apply(self, grid: ARCGrid) -> ARCGrid:
        new_data = torch.full_like(grid.data, self.color)
        return ARCGrid(new_data)
    
    def get_restriction_map(self, sheaf: CellularSheaf) -> torch.Tensor:
        return sheaf.restriction_maps.clone()
    
    def signature(self) -> str:
        return f"fill_color_{self.color}"


# =============================================================================
# DSL EQUIVALENCE CLASSES (FUNCTIONAL BLANKET)
# =============================================================================

class ComposedOp(DSLPrimitive):
    """
    Composition of multiple DSL primitives: op1 ∘ op2 ∘ ... ∘ opN.
    
    This is the key to PROGRAM SYNTHESIS: finding sequences of
    primitives that together achieve the transformation.
    """
    
    def __init__(self, ops: List[DSLPrimitive]):
        self.ops = ops
    
    def apply(self, grid: ARCGrid) -> ARCGrid:
        result = grid
        for op in self.ops:
            result = op.apply(result)
        return result
    
    def get_restriction_map(self, sheaf: CellularSheaf) -> torch.Tensor:
        """Compose restriction maps: F_composed = F_n ∘ ... ∘ F_1."""
        result = sheaf.restriction_maps.clone()
        for op in self.ops:
            # Each op modifies the restriction maps
            result = op.get_restriction_map(
                CellularSheaf(sheaf.grid, sheaf.stalk_dim, sheaf.config)
            )
        return result
    
    def signature(self) -> str:
        return " -> ".join(op.signature() for op in self.ops)


class DSLEquivalenceChecker:
    """
    Computes equivalence classes of DSL operations using Functional Blanket theory.
    
    Two operations are equivalent if they produce the same output for all inputs
    (or equivalently, if their functional defect is below threshold).
    
    This prevents the planner from testing redundant operations like:
    - Rotate90 ∘ Rotate90 ∘ Rotate90 ∘ Rotate90 = Identity
    - FlipH ∘ FlipH = Identity
    """
    
    def __init__(self, config: ARCSheafConfig):
        self.config = config
        self.equivalence_classes: Dict[str, Set[str]] = {}
        self.canonical_ops: Dict[str, DSLPrimitive] = {}
    
    def compute_functional_defect(
        self, 
        op1: DSLPrimitive, 
        op2: DSLPrimitive,
        test_grids: List[ARCGrid]
    ) -> float:
        """
        Compute functional defect between two operations.
        
        defect = (1/N) * sum_i ||op1(grid_i) - op2(grid_i)||² / ||grid_i||²
        
        Low defect = operations are functionally equivalent.
        """
        if not test_grids:
            return float('inf')
        
        total_defect = 0.0
        for grid in test_grids:
            out1 = op1.apply(grid)
            out2 = op2.apply(grid)
            
            # Compute normalized difference
            diff = (out1.data.float() - out2.data.float()) ** 2
            norm = (grid.data.float() ** 2).sum() + 1e-10
            total_defect += diff.sum().item() / norm.item()
        
        return total_defect / len(test_grids)
    
    def build_equivalence_classes(
        self, 
        operations: List[DSLPrimitive],
        test_grids: List[ARCGrid]
    ) -> Dict[str, List[DSLPrimitive]]:
        """
        Group operations into equivalence classes.
        
        Uses union-find with functional defect as the similarity metric.
        """
        signatures = [op.signature() for op in operations]
        parent = {sig: sig for sig in signatures}
        
        def find(x):
            if parent[x] != x:
                parent[x] = find(parent[x])
            return parent[x]
        
        def union(x, y):
            px, py = find(x), find(y)
            if px != py:
                parent[px] = py
        
        # Check all pairs for equivalence
        for i, op1 in enumerate(operations):
            for j, op2 in enumerate(operations[i+1:], i+1):
                defect = self.compute_functional_defect(op1, op2, test_grids)
                if defect < self.config.equivalence_threshold:
                    union(signatures[i], signatures[j])
        
        # Build class dictionary
        classes: Dict[str, List[DSLPrimitive]] = {}
        for i, op in enumerate(operations):
            root = find(signatures[i])
            if root not in classes:
                classes[root] = []
            classes[root].append(op)
        
        # Store canonical (first) operation for each class
        self.equivalence_classes = {k: set(op.signature() for op in v) for k, v in classes.items()}
        self.canonical_ops = {k: v[0] for k, v in classes.items()}
        
        return classes
    
    def get_canonical_operations(self) -> List[DSLPrimitive]:
        """Get one representative from each equivalence class."""
        return list(self.canonical_ops.values())


# =============================================================================
# SHEAF NEURAL NETWORK
# =============================================================================

class SheafEncoder(nn.Module):
    """
    Encodes an ARC grid into a sheaf representation.
    
    Maps: Grid → (Stalk vectors, Restriction maps)
    """
    
    def __init__(self, config: ARCSheafConfig):
        super().__init__()
        self.config = config
        
        # Color embedding
        self.color_embed = nn.Embedding(config.num_colors, config.stalk_dim)
        
        # Position encoding
        self.pos_embed = nn.Linear(2, config.stalk_dim)
        
        # Stalk refinement
        self.stalk_mlp = nn.Sequential(
            nn.Linear(config.stalk_dim * 2, config.stalk_dim),
            nn.ReLU(),
            nn.Linear(config.stalk_dim, config.stalk_dim)
        )
        
        # Restriction map generator
        self.restriction_mlp = nn.Sequential(
            nn.Linear(config.stalk_dim * 2, config.edge_dim),
            nn.ReLU(),
            nn.Linear(config.edge_dim, config.stalk_dim * config.stalk_dim)
        )
    
    def forward(self, grid: ARCGrid) -> Tuple[torch.Tensor, torch.Tensor, List[Tuple[int, int]]]:
        """
        Encode grid into sheaf structure.
        
        Returns:
            stalks: (num_nodes, stalk_dim)
            restriction_maps: (num_edges, stalk_dim, stalk_dim)
            edges: List of (u, v) pairs
        """
        H, W = grid.height, grid.width
        device = grid.data.device
        
        # Build node features
        colors = grid.data.contiguous().view(-1)  # (H*W,)
        color_feats = self.color_embed(colors)  # (H*W, stalk_dim)
        
        # Position features
        positions = torch.stack([
            torch.arange(H, device=device).unsqueeze(1).expand(H, W).reshape(-1).float() / H,
            torch.arange(W, device=device).unsqueeze(0).expand(H, W).reshape(-1).float() / W
        ], dim=1)  # (H*W, 2)
        pos_feats = self.pos_embed(positions)  # (H*W, stalk_dim)
        
        # Combine and refine
        combined = torch.cat([color_feats, pos_feats], dim=1)  # (H*W, stalk_dim*2)
        stalks = self.stalk_mlp(combined)  # (H*W, stalk_dim)
        
        # Build edges and restriction maps
        edges = []
        edge_features = []
        
        for r in range(H):
            for c in range(W):
                node = r * W + c
                
                # Right neighbor
                if c + 1 < W:
                    neighbor = r * W + (c + 1)
                    edges.append((node, neighbor))
                    edge_features.append(torch.cat([stalks[node], stalks[neighbor]]))
                
                # Down neighbor
                if r + 1 < H:
                    neighbor = (r + 1) * W + c
                    edges.append((node, neighbor))
                    edge_features.append(torch.cat([stalks[node], stalks[neighbor]]))
        
        if edge_features:
            edge_stack = torch.stack(edge_features)  # (num_edges, stalk_dim*2)
            restriction_flat = self.restriction_mlp(edge_stack)  # (num_edges, stalk_dim²)
            restriction_maps = restriction_flat.view(-1, self.config.stalk_dim, self.config.stalk_dim)
        else:
            restriction_maps = torch.zeros(0, self.config.stalk_dim, self.config.stalk_dim, device=device)
        
        return stalks, restriction_maps, edges


class SheafDecoder(nn.Module):
    """
    Decodes sheaf stalks back to a grid.
    
    Maps: Stalk vectors → Color predictions
    """
    
    def __init__(self, config: ARCSheafConfig):
        super().__init__()
        self.config = config
        
        self.decoder = nn.Sequential(
            nn.Linear(config.stalk_dim, config.stalk_dim),
            nn.ReLU(),
            nn.Linear(config.stalk_dim, config.num_colors)
        )
    
    def forward(self, stalks: torch.Tensor, H: int, W: int) -> torch.Tensor:
        """
        Decode stalks to color logits.
        
        Args:
            stalks: (H*W, stalk_dim)
            H, W: Grid dimensions
            
        Returns:
            logits: (H, W, num_colors)
        """
        logits = self.decoder(stalks)  # (H*W, num_colors)
        return logits.view(H, W, self.config.num_colors)


class SheafDiffusionModule(nn.Module):
    """
    Learnable sheaf diffusion for relaxing to ground state.
    """
    
    def __init__(self, config: ARCSheafConfig):
        super().__init__()
        self.config = config
        
        # Learnable diffusion rate per edge type
        self.diffusion_rate = nn.Parameter(torch.ones(2) * 0.1)  # [horizontal, vertical]
    
    def forward(
        self, 
        stalks: torch.Tensor, 
        restriction_maps: torch.Tensor,
        edges: List[Tuple[int, int]],
        edge_types: List[int],  # 0 = horizontal, 1 = vertical
        steps: int
    ) -> torch.Tensor:
        """
        Perform sheaf diffusion.
        
        dx/dt = -L_F x with learnable rates.
        """
        x = stalks.clone()
        
        for _ in range(steps):
            grad = torch.zeros_like(x)
            
            for e, (u, v) in enumerate(edges):
                rate = self.diffusion_rate[edge_types[e]].abs()
                
                # Coboundary contribution
                F_uv = restriction_maps[e]
                Fu_x = F_uv @ x[u]
                Fv_x = F_uv.T @ x[v]
                coboundary = Fv_x - Fu_x
                
                # Gradient accumulation
                grad[u] -= rate * F_uv.T @ coboundary
                grad[v] += rate * F_uv @ coboundary
            
            x = x - self.config.diffusion_dt * grad
        
        return x


# =============================================================================
# MAIN ARC-SGC MODEL
# =============================================================================

class ARCSheafModel(nn.Module):
    """
    Main ARC-SGC model using Sheaf Neural Networks.
    
    Architecture:
    1. Encode input grid to sheaf
    2. Apply DSL operation (as sheaf morphism)
    3. Diffuse to relax inconsistencies
    4. Decode to output grid
    5. Loss = Sheaf Laplacian energy (not MSE!)
    """
    
    def __init__(self, config: ARCSheafConfig):
        super().__init__()
        self.config = config
        
        self.encoder = SheafEncoder(config)
        self.diffusion = SheafDiffusionModule(config)
        self.decoder = SheafDecoder(config)
        
        # DSL primitives
        self.dsl_ops = self._build_dsl()
    
    def _build_dsl(self) -> List[DSLPrimitive]:
        """Build the DSL primitive library."""
        ops = [
            IdentityOp(),
            ShiftRight(1), ShiftRight(2),
            ShiftDown(1), ShiftDown(2),
            Rotate90(), Rotate180(), Rotate270(),
            FlipHorizontal(), FlipVertical(),
        ]
        
        # Add color swaps for common colors
        for c1 in range(self.config.num_colors):
            for c2 in range(c1 + 1, self.config.num_colors):
                ops.append(ColorSwap(c1, c2))
        
        return ops
    
    def compute_sheaf_loss(
        self,
        stalks: torch.Tensor,
        restriction_maps: torch.Tensor,
        edges: List[Tuple[int, int]],
        target_grid: ARCGrid
    ) -> torch.Tensor:
        """
        Compute Sheaf Laplacian energy loss.
        
        Loss = <x, L_F x> + λ * ||decode(x) - target||²
        
        The first term ensures local consistency.
        The second term ensures global correctness.
        """
        # Sheaf Laplacian energy
        laplacian_energy = torch.tensor(0.0, device=stalks.device)
        for e, (u, v) in enumerate(edges):
            F_uv = restriction_maps[e]
            Fu_x = F_uv @ stalks[u]
            Fv_x = F_uv.T @ stalks[v]
            coboundary = Fv_x - Fu_x
            laplacian_energy = laplacian_energy + (coboundary ** 2).sum()
        
        # Reconstruction loss (auxiliary)
        H, W = target_grid.height, target_grid.width
        logits = self.decoder(stalks, H, W)
        target_flat = target_grid.data.contiguous().view(-1)
        recon_loss = F.cross_entropy(logits.view(-1, self.config.num_colors), target_flat)
        
        # Combined loss: Laplacian is primary, reconstruction is auxiliary
        total_loss = laplacian_energy + 0.5 * recon_loss
        
        return total_loss, laplacian_energy, recon_loss
    
    def forward_with_op(
        self, 
        input_grid: ARCGrid,
        target_grid: ARCGrid,
        dsl_op: DSLPrimitive
    ) -> Tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
        """
        Forward pass with explicit DSL operation.
        
        Args:
            input_grid: Input ARC grid
            target_grid: Target output grid
            dsl_op: DSL operation to apply (may be ComposedOp)
            
        Returns:
            total_loss, laplacian_energy, recon_loss
        """
        transformed = dsl_op.apply(input_grid)
        
        # Encode to sheaf
        stalks, restriction_maps, edges = self.encoder(transformed)
        
        # Diffuse
        edge_types = []
        H, W = transformed.height, transformed.width
        for r in range(H):
            for c in range(W):
                if c + 1 < W:
                    edge_types.append(0)  # horizontal
                if r + 1 < H:
                    edge_types.append(1)  # vertical
        
        diffused = self.diffusion(stalks, restriction_maps, edges, edge_types, self.config.diffusion_steps)
        
        # Compute loss
        return self.compute_sheaf_loss(diffused, restriction_maps, edges, target_grid)
    
    def predict_with_op(self, input_grid: ARCGrid, dsl_op: DSLPrimitive) -> ARCGrid:
        """Generate output prediction using specified DSL operation."""
        transformed = dsl_op.apply(input_grid)
        
        stalks, restriction_maps, edges = self.encoder(transformed)
        
        edge_types = []
        H, W = transformed.height, transformed.width
        for r in range(H):
            for c in range(W):
                if c + 1 < W:
                    edge_types.append(0)
                if r + 1 < H:
                    edge_types.append(1)
        
        diffused = self.diffusion(stalks, restriction_maps, edges, edge_types, self.config.diffusion_steps)
        
        logits = self.decoder(diffused, H, W)
        pred_colors = logits.argmax(dim=-1)
        
        return ARCGrid(pred_colors)


# =============================================================================
# TRAINING
# =============================================================================

def evaluate_operation(
    op: DSLPrimitive,
    task: ARCTask,
    stalk_dim: int,
    config: ARCSheafConfig
) -> Tuple[float, float]:
    """Evaluate a single operation on a task. Returns (accuracy, energy)."""
    total_correct = 0
    total_cells = 0
    total_energy = 0.0
    
    for example in task.train_examples:
        transformed = op.apply(example.input_grid)
        
        if transformed.shape != example.output_grid.shape:
            continue
        
        correct = (transformed.data == example.output_grid.data).sum().item()
        total_correct += correct
        total_cells += example.output_grid.data.numel()
        
        sheaf = CellularSheaf(transformed, stalk_dim, config)
        energy = sheaf.compute_laplacian_energy(sheaf.stalks).item()
        total_energy += energy
    
    if total_cells == 0:
        return 0.0, float('inf')
    
    return total_correct / total_cells, total_energy


def find_best_dsl_operation(
    model: ARCSheafModel,
    task: ARCTask,
    verbose: bool = True,
    max_composition_depth: int = 2
) -> Tuple[DSLPrimitive, float]:
    """
    Find the DSL operation (or composition) that best transforms inputs to outputs.
    
    This is PROGRAM SYNTHESIS via exhaustive search over primitives and
    their compositions up to max_composition_depth.
    
    The Sheaf Laplacian energy breaks ties when accuracy is equal.
    
    Returns:
        best_op: The best DSL operation (may be ComposedOp)
        best_accuracy: Grid-level accuracy of that operation
    """
    best_op = model.dsl_ops[0]
    best_accuracy = 0.0
    best_energy = float('inf')
    
    # Phase 1: Try single primitives
    if verbose:
        print(f"   Searching {len(model.dsl_ops)} primitives...")
    
    for op in model.dsl_ops:
        accuracy, energy = evaluate_operation(op, task, model.config.stalk_dim, model.config)
        
        if accuracy > best_accuracy or (accuracy == best_accuracy and energy < best_energy):
            best_accuracy = accuracy
            best_energy = energy
            best_op = op
    
    # Early exit if perfect
    if best_accuracy == 1.0:
        if verbose:
            print(f"   Found perfect primitive: {best_op.signature()}")
        return best_op, best_accuracy
    
    # Phase 2: Try 2-compositions (if needed and allowed)
    if max_composition_depth >= 2 and best_accuracy < 1.0:
        if verbose:
            print(f"   Searching 2-compositions ({len(model.dsl_ops)**2} combinations)...")
        
        for op1 in model.dsl_ops:
            for op2 in model.dsl_ops:
                composed = ComposedOp([op1, op2])
                accuracy, energy = evaluate_operation(composed, task, model.config.stalk_dim, model.config)
                
                if accuracy > best_accuracy or (accuracy == best_accuracy and energy < best_energy):
                    best_accuracy = accuracy
                    best_energy = energy
                    best_op = composed
        
        if best_accuracy == 1.0:
            if verbose:
                print(f"   Found perfect 2-composition: {best_op.signature()}")
            return best_op, best_accuracy
    
    if verbose:
        print(f"   Best operation: {best_op.signature()}")
        print(f"   Accuracy: {best_accuracy*100:.1f}%")
    
    return best_op, best_accuracy


def train_on_task(
    model: ARCSheafModel,
    task: ARCTask,
    config: ARCSheafConfig,
    verbose: bool = True
) -> Tuple[Dict[str, float], DSLPrimitive]:
    """
    Train model on a single ARC task.
    
    Phase 1: Find best DSL operation (program synthesis)
    Phase 2: Train encoder/decoder with that operation (sheaf refinement)
    
    Returns:
        history: Training metrics
        best_op: The selected DSL operation (may be composed)
    """
    # Phase 1: Program Synthesis - find best DSL operation
    if verbose:
        print("   Phase 1: Program Synthesis...")
    best_op, dsl_accuracy = find_best_dsl_operation(model, task, verbose)
    
    # If DSL perfectly solves it, we're done
    if dsl_accuracy == 1.0:
        if verbose:
            print("   DSL operation achieves 100% - no training needed!")
        return {'laplacian': [0], 'recon': [0], 'total': [0]}, best_op
    
    # Phase 2: Train encoder/decoder to refine the transformation
    if verbose:
        print("   Phase 2: Sheaf Refinement...")
    
    optimizer = torch.optim.Adam(model.parameters(), lr=config.lr)
    history = {'laplacian': [], 'recon': [], 'total': []}
    
    for epoch in range(config.epochs):
        model.train()
        epoch_loss = 0.0
        epoch_lap = 0.0
        epoch_recon = 0.0
        
        for example in task.train_examples:
            optimizer.zero_grad()
            
            # Train with the selected DSL operation
            loss, lap, recon = model.forward_with_op(example.input_grid, example.output_grid, best_op)
            loss.backward()
            optimizer.step()
            
            epoch_loss += loss.item()
            epoch_lap += lap.item()
            epoch_recon += recon.item()
        
        n = len(task.train_examples)
        history['total'].append(epoch_loss / n)
        history['laplacian'].append(epoch_lap / n)
        history['recon'].append(epoch_recon / n)
        
        if verbose and (epoch + 1) % 20 == 0:
            print(f"   Epoch {epoch+1}: Loss={epoch_loss/n:.4f} (Lap={epoch_lap/n:.4f}, Recon={epoch_recon/n:.4f})")
    
    return history, best_op


# =============================================================================
# MAIN
# =============================================================================

def main():
    """Demo: test the ARC-SGC sheaf model."""
    print("=" * 60)
    print("ARC-SGC: Sheaf-Theoretic Program Synthesis")
    print("=" * 60)
    
    config = ARCSheafConfig()
    
    # =================================================================
    # TEST 1: Simple rotation (DSL should solve perfectly)
    # =================================================================
    print("\n" + "=" * 60)
    print("TEST 1: Simple Rotation (DSL-solvable)")
    print("=" * 60)
    
    print("\n1. Creating rotation test task...")
    
    # Input: 3x3 grid with pattern
    input_data = torch.tensor([
        [1, 2, 3],
        [4, 5, 6],
        [7, 8, 9]
    ], dtype=torch.long)
    
    # Output: rotated 90 degrees
    output_data = torch.rot90(input_data, k=-1)
    
    input_grid = ARCGrid(input_data.to(config.device))
    output_grid = ARCGrid(output_data.to(config.device))
    
    example = ARCExample(input_grid, output_grid)
    task = ARCTask(
        task_id="test_rotation",
        train_examples=[example],
        test_examples=[example]
    )
    
    print(f"   Input:\n{input_grid.data}")
    print(f"   Output:\n{output_grid.data}")
    
    # Build and test sheaf
    print("\n2. Building cellular sheaf...")
    sheaf = CellularSheaf(input_grid, config.stalk_dim, config)
    print(f"   Nodes: {sheaf.num_nodes}")
    print(f"   Edges: {sheaf.num_edges}")
    
    # Compute initial Laplacian energy
    energy = sheaf.compute_laplacian_energy(sheaf.stalks)
    print(f"   Initial Laplacian energy: {energy.item():.4f}")
    
    # Test diffusion
    print("\n3. Testing sheaf diffusion...")
    diffused = sheaf.diffuse(sheaf.stalks, steps=10, dt=0.1)
    energy_after = sheaf.compute_laplacian_energy(diffused)
    print(f"   Energy after diffusion: {energy_after.item():.4f}")
    
    # Test DSL equivalence
    print("\n4. Computing DSL equivalence classes...")
    equiv_checker = DSLEquivalenceChecker(config)
    
    ops = [
        IdentityOp(),
        Rotate90(),
        Rotate180(),
        Rotate270(),
        FlipHorizontal(),
        FlipVertical(),
    ]
    
    # Generate test grids
    test_grids = [
        ARCGrid(torch.randint(0, 10, (3, 3), dtype=torch.long))
        for _ in range(5)
    ]
    
    classes = equiv_checker.build_equivalence_classes(ops, test_grids)
    print(f"   Found {len(classes)} equivalence classes:")
    for canonical, members in classes.items():
        print(f"   - {canonical}: {[m.signature() for m in members]}")
    
    # Build and train model
    print("\n5. Building ARCSheafModel...")
    model = ARCSheafModel(config).to(config.device)
    print(f"   Parameters: {sum(p.numel() for p in model.parameters()):,}")
    
    print("\n6. Training on test task...")
    history, best_op = train_on_task(model, task, config, verbose=True)
    
    # Test prediction using the selected DSL operation
    print("\n7. Testing prediction...")
    print(f"   Using DSL operation: {best_op.signature()}")
    
    # Direct DSL application (ground truth of what we learned)
    dsl_pred = best_op.apply(input_grid)
    print(f"   DSL output:\n{dsl_pred.data}")
    
    dsl_correct = (dsl_pred.data == output_grid.data).sum().item()
    dsl_total = output_grid.data.numel()
    print(f"   DSL Accuracy: {dsl_correct}/{dsl_total} = {100*dsl_correct/dsl_total:.1f}%")
    
    # Neural refinement (encoder → diffusion → decoder)
    with torch.no_grad():
        pred = model.predict_with_op(input_grid, best_op)
        print(f"   Neural output:\n{pred.data}")
        
        correct = (pred.data == output_grid.data).sum().item()
        total = output_grid.data.numel()
        print(f"   Neural Accuracy: {correct}/{total} = {100*correct/total:.1f}%")
    
    # =================================================================
    # TEST 2: Complex transformation (DSL partial match + refinement)
    # =================================================================
    print("\n" + "=" * 60)
    print("TEST 2: Complex Transformation (requires refinement)")
    print("=" * 60)
    
    # This tests a transformation that DSL can't perfectly solve:
    # Rotate + change one color
    input_data2 = torch.tensor([
        [1, 2, 3],
        [4, 5, 6],
        [7, 8, 9]
    ], dtype=torch.long)
    
    # Output: rotate 90 AND change all 5s to 0s
    output_data2 = torch.rot90(input_data2, k=-1).clone()
    output_data2[output_data2 == 5] = 0  # Change center
    
    input_grid2 = ARCGrid(input_data2.to(config.device))
    output_grid2 = ARCGrid(output_data2.to(config.device))
    
    print(f"\n   Input:\n{input_grid2.data}")
    print(f"   Output:\n{output_grid2.data}")
    
    example2 = ARCExample(input_grid2, output_grid2)
    task2 = ARCTask(
        task_id="test_rotate_and_recolor",
        train_examples=[example2],
        test_examples=[example2]
    )
    
    # Build and train model for complex task
    print("\n   Building model...")
    model2 = ARCSheafModel(config).to(config.device)
    
    print("\n   Training...")
    config.epochs = 50  # More epochs for complex task
    history2, best_op2 = train_on_task(model2, task2, config, verbose=True)
    
    # Test prediction
    print("\n   Testing prediction...")
    print(f"   Best DSL operation: {best_op2.signature()}")
    
    dsl_pred2 = best_op2.apply(input_grid2)
    print(f"   DSL output:\n{dsl_pred2.data}")
    
    dsl_correct2 = (dsl_pred2.data == output_grid2.data).sum().item()
    dsl_total2 = output_grid2.data.numel()
    print(f"   DSL Accuracy: {dsl_correct2}/{dsl_total2} = {100*dsl_correct2/dsl_total2:.1f}%")
    
    with torch.no_grad():
        pred2 = model2.predict_with_op(input_grid2, best_op2)
        print(f"   Neural output:\n{pred2.data}")
        
        correct2 = (pred2.data == output_grid2.data).sum().item()
        total2 = output_grid2.data.numel()
        print(f"   Neural Accuracy: {correct2}/{total2} = {100*correct2/total2:.1f}%")
    
    print("\n" + "=" * 60)
    print("ARC-SGC Pipeline Tests Complete")
    print("=" * 60)
    
    # Summary
    print("\n### SUMMARY ###")
    print(f"Test 1 (Rotation): DSL solves 100% - no neural refinement needed")
    print(f"Test 2 (Rotate+Recolor): DSL={100*dsl_correct2/dsl_total2:.1f}%, Neural={100*correct2/total2:.1f}%")
    print("\nKey insight: DSL primitives are the PHYSICS. Neural network refines when physics is incomplete.")


if __name__ == "__main__":
    main()
