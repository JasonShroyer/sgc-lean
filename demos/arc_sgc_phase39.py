"""
Phase 39: Flow on the Compositional Manifold
============================================

Diagnosis from Phase 38:
- Phase 38 had correct PHYSICS (Madelung equations, quantum potential)
- Phase 38 had wrong TOPOLOGY (single operators, not compositions)
- Result: Fluid pooled at best single node (local minimum)

Phase 39 Fix:
- Define manifold as a DIRECTED GRAPH of operator compositions
- Flow on EDGES (transitions), not NODES (operators)
- Use DISCRETE VECTOR CALCULUS (graph gradient, divergence)
- Extract STREAMLINES to get operator sequences

Architecture:
- 0-simplex (Node): Single operator f
- 1-simplex (Edge): Composition g ∘ f
- 2-simplex (Face): Associativity (h ∘ g) ∘ f

Key Insight:
- "Depth" corresponds to TIME
- t=1: Fluid reaches neighbors (Depth 1)
- t=k: Fluid explores compositions of length k

This is effectively a GFlowNet using SGC operators as building blocks.

References:
- Geometric Deep Learning (Bronstein et al.)
- Neural ODEs (Chen et al.)
- GFlowNets (Bengio et al.)
"""

import numpy as np
import torch
from dataclasses import dataclass, field
from typing import List, Dict, Tuple, Optional, Set, Any
from collections import defaultdict, Counter
from pathlib import Path
import json
import time
from scipy.sparse import csr_matrix, lil_matrix
from scipy.sparse.linalg import spsolve

# Import from Phase 21 (the main SGC implementation)
from arc_sgc_phase21 import (
    ARCGrid,
    CanonicalOperator,
    ContentAddressedOperatorMemory,
    AdaptiveFisherRaoMetric,
    SheafStructure,
    UnifiedExecutive,
    ConsolidationEngine,
    WorkingMemory,
    ResidualCompiler,
    ConservationGate,
)

from arc_sgc_phase20 import (
    ARCGrid, ARCTask, ARCExample, load_arc_tasks
)


def numpy_to_arcgrid(arr: np.ndarray) -> ARCGrid:
    """Convert numpy array to ARCGrid for compatibility with metric.compute()."""
    arr_copy = np.ascontiguousarray(arr)
    return ARCGrid(torch.tensor(arr_copy, dtype=torch.long))


# =============================================================================
# PHASE 39: COMPOSITION GRAPH
# =============================================================================

@dataclass
class OperatorType:
    """Type signature of an operator for composability checking."""
    input_type: str   # e.g., 'grid', 'object', 'region'
    output_type: str  # e.g., 'grid', 'object', 'region'
    preserves: Set[str] = field(default_factory=set)  # Conservation properties
    
    def can_compose_with(self, other: 'OperatorType') -> bool:
        """Check if self ∘ other is valid (self applied after other)."""
        return self.input_type in {'grid', 'any', other.output_type}


def infer_operator_type(op: CanonicalOperator) -> OperatorType:
    """Infer the type signature of an operator."""
    op_type = op.op_type.lower()
    
    # Grid → Grid operators
    if op_type in {'identity', 'rotate', 'rot90', 'rot180', 'rot270', 
                   'flip_h', 'flip_v', 'transpose', 'translate', 'scale'}:
        return OperatorType('grid', 'grid', {'shape'} if 'rotate' not in op_type else set())
    
    # Grid → Grid (color operations)
    if 'color' in op_type or 'swap' in op_type or 'fill' in op_type:
        return OperatorType('grid', 'grid', {'shape', 'topology'})
    
    # Grid → Region operations
    if op_type in {'crop', 'extract', 'detect'}:
        return OperatorType('grid', 'region', set())
    
    # Region → Grid operations
    if op_type in {'embed', 'place', 'tile'}:
        return OperatorType('region', 'grid', set())
    
    # Fix operations (Grid → Grid)
    if 'fix' in op_type:
        return OperatorType('grid', 'grid', set())
    
    # Default: flexible
    return OperatorType('any', 'grid', set())


class CompositionGraph:
    """
    Directed graph of valid operator compositions.
    
    This is the CORRECT TOPOLOGY for hydrodynamic flow:
    - Nodes = Operators
    - Edges = Valid compositions (type-compatible transitions)
    - Edge weights = Transition probabilities / costs
    
    The Sheaf Laplacian becomes the diffusion operator on this graph.
    """
    
    def __init__(self, 
                 memory: ContentAddressedOperatorMemory,
                 metric: AdaptiveFisherRaoMetric):
        self.memory = memory
        self.metric = metric
        
        # Build operator list with types
        self.operators: List[CanonicalOperator] = list(memory.operators.values())
        self.op_types: List[OperatorType] = [infer_operator_type(op) for op in self.operators]
        self.n_ops = len(self.operators)
        
        # Index mappings
        self.op_to_idx: Dict[str, int] = {
            op.content_hash(): i for i, op in enumerate(self.operators)
        }
        
        # Add special "Source" and "Sink" nodes
        # Source = Identity (start state)
        # Sink = Perfect solution (target state)
        self.source_idx = self._find_or_create_identity()
        self.sink_idx = self.n_ops  # Virtual sink node
        
        # Build the graph structure
        self.adj_matrix: Optional[csr_matrix] = None  # Node adjacency
        self.edge_list: List[Tuple[int, int]] = []    # List of (src, dst) edges
        self.edge_to_idx: Dict[Tuple[int, int], int] = {}
        self.edge_weights: np.ndarray = None          # Weights on edges
        
        self._build_type_compatible_adjacency()
        
        # Discrete calculus operators
        self.incidence_matrix: Optional[csr_matrix] = None  # Nodes → Edges
        self.graph_laplacian: Optional[csr_matrix] = None   # L = D - A
        
        self._build_calculus_operators()
        
        print(f"[GRAPH] Built composition graph: {self.n_ops} operators, {len(self.edge_list)} edges")
    
    def _find_or_create_identity(self) -> int:
        """Find the identity operator or return index 0."""
        for i, op in enumerate(self.operators):
            if op.op_type.lower() == 'identity':
                return i
        return 0  # Default to first operator
    
    def _build_type_compatible_adjacency(self):
        """Build directed adjacency matrix based on type compatibility."""
        # Limit operators to avoid O(n²) blowup
        max_ops = min(50, self.n_ops)
        
        # Use sparse matrix for efficiency
        adj = lil_matrix((max_ops, max_ops), dtype=np.float32)
        
        # Update operator list to limited set (prioritize by energy)
        if self.n_ops > max_ops:
            energies = [(i, self.operators[i].energy()) for i in range(self.n_ops)]
            energies.sort(key=lambda x: x[1])
            kept_indices = [e[0] for e in energies[:max_ops]]
            self.operators = [self.operators[i] for i in kept_indices]
            self.op_types = [self.op_types[i] for i in kept_indices]
            self.n_ops = max_ops
            self.op_to_idx = {op.content_hash(): i for i, op in enumerate(self.operators)}
        
        edge_idx = 0
        for i in range(self.n_ops):
            for j in range(self.n_ops):
                # Can we apply op[j] after op[i]?
                # That is: j ∘ i is valid if j.input_type accepts i.output_type
                if self.op_types[j].can_compose_with(self.op_types[i]):
                    # Weight based on operator energies
                    energy_i = self.operators[i].energy()
                    energy_j = self.operators[j].energy()
                    weight = np.exp(-(energy_i + energy_j) / 2)
                    
                    adj[i, j] = weight
                    self.edge_list.append((i, j))
                    self.edge_to_idx[(i, j)] = edge_idx
                    edge_idx += 1
        
        self.adj_matrix = csr_matrix(adj)
        self.n_edges = len(self.edge_list)
        
        # Convert edge list to weights array
        self.edge_weights = np.array([
            self.adj_matrix[e[0], e[1]] for e in self.edge_list
        ], dtype=np.float32)
    
    def _build_calculus_operators(self):
        """Build discrete vector calculus operators on the graph."""
        # Incidence matrix B: nodes × edges
        # B[i, e] = -1 if edge e starts at node i
        # B[i, e] = +1 if edge e ends at node i
        B = lil_matrix((self.n_ops, self.n_edges), dtype=np.float32)
        
        for e_idx, (src, dst) in enumerate(self.edge_list):
            B[src, e_idx] = -1.0
            B[dst, e_idx] = +1.0
        
        self.incidence_matrix = csr_matrix(B)
        
        # Graph Laplacian: L = D - A
        # Where D is the degree matrix (diagonal)
        out_degree = np.array(self.adj_matrix.sum(axis=1)).flatten()
        D = np.diag(out_degree)
        
        # Convert adj to dense for Laplacian (small enough)
        A_dense = self.adj_matrix.toarray()
        L = D - A_dense
        
        # Add small regularization for stability
        L += 1e-6 * np.eye(self.n_ops)
        
        self.graph_laplacian = csr_matrix(L)
    
    def gradient(self, node_field: np.ndarray) -> np.ndarray:
        """
        Compute gradient of a scalar field on nodes → vector field on edges.
        
        (∇f)_e = f[dst(e)] - f[src(e)]
        
        This is the discrete exterior derivative d: Ω⁰ → Ω¹
        """
        edge_field = np.zeros(self.n_edges, dtype=np.float64)
        
        for e_idx, (src, dst) in enumerate(self.edge_list):
            edge_field[e_idx] = node_field[dst] - node_field[src]
        
        return edge_field
    
    def divergence(self, edge_field: np.ndarray) -> np.ndarray:
        """
        Compute divergence of a vector field on edges → scalar field on nodes.
        
        (div F)_i = Σ_j F[j→i] - Σ_k F[i→k]
                  = (incoming flux) - (outgoing flux)
        
        This is the discrete codifferential δ: Ω¹ → Ω⁰
        """
        node_field = np.zeros(self.n_ops, dtype=np.float64)
        
        for e_idx, (src, dst) in enumerate(self.edge_list):
            # Flux from src to dst
            flux = edge_field[e_idx]
            node_field[src] -= flux  # Outgoing from src
            node_field[dst] += flux  # Incoming to dst
        
        return node_field
    
    def apply_operator(self, op_idx: int, grid: np.ndarray) -> Optional[np.ndarray]:
        """Apply an operator to a grid."""
        if op_idx < 0 or op_idx >= self.n_ops:
            return None
        
        op = self.operators[op_idx]
        op_type = op.op_type.lower()
        
        try:
            if op_type == 'identity':
                return grid.copy()
            elif op_type in {'rot90', 'rotate_90'}:
                return np.rot90(grid, k=1)
            elif op_type in {'rot180', 'rotate_180'}:
                return np.rot90(grid, k=2)
            elif op_type in {'rot270', 'rotate_270'}:
                return np.rot90(grid, k=3)
            elif op_type == 'flip_h':
                return np.fliplr(grid)
            elif op_type == 'flip_v':
                return np.flipud(grid)
            elif op_type == 'transpose':
                return grid.T
            elif 'color_swap' in op_type or 'swap' in op_type:
                c1 = op.params.get('from_color', 0)
                c2 = op.params.get('to_color', 1)
                result = grid.copy()
                mask1 = result == c1
                mask2 = result == c2
                result[mask1] = c2
                result[mask2] = c1
                return result
            elif 'fill' in op_type:
                color = op.params.get('color', 0)
                mask = op.params.get('mask', None)
                result = grid.copy()
                if mask is not None:
                    result[mask] = color
                return result
            elif 'fix_pixel' in op_type:
                r = op.params.get('row', 0)
                c = op.params.get('col', 0)
                color = op.params.get('color', 0)
                result = grid.copy()
                if 0 <= r < result.shape[0] and 0 <= c < result.shape[1]:
                    result[r, c] = color
                return result
            else:
                # Unknown operator - return unchanged
                return grid.copy()
        except:
            return None
    
    def compute_transition_energy(self, 
                                   src_idx: int, 
                                   dst_idx: int,
                                   current_grid: np.ndarray,
                                   target: np.ndarray) -> float:
        """
        Compute the energy cost of transitioning from src to dst.
        
        Energy = Distance(Apply(dst, Apply(src, grid)), target)
        """
        # Apply source operator
        after_src = self.apply_operator(src_idx, current_grid)
        if after_src is None:
            return 100.0
        
        # Apply destination operator
        after_dst = self.apply_operator(dst_idx, after_src)
        if after_dst is None:
            return 100.0
        
        # Compute Fisher-Rao distance to target
        try:
            result_grid = numpy_to_arcgrid(after_dst)
            target_grid = numpy_to_arcgrid(target)
            dist_result = self.metric.compute(result_grid, target_grid)
            distance = dist_result['total'] if isinstance(dist_result, dict) else float(dist_result)
            return distance
        except:
            return 100.0


# =============================================================================
# PHASE 39: EDGE-BASED HYDRODYNAMIC STATE
# =============================================================================

@dataclass
class EdgeFlowState:
    """
    Hydrodynamic state defined on EDGES (transitions), not nodes.
    
    This is the KEY FIX from Phase 38:
    - ρ[e] = Probability flux through edge e
    - v[e] = Velocity of flow through edge e
    - The fluid represents "probability of taking this transition"
    
    A "path" is a streamline in this flow.
    """
    n_edges: int
    n_nodes: int
    
    # Flux on edges (probability of taking each transition)
    rho: np.ndarray = field(default_factory=lambda: np.array([]))
    
    # Phase field on nodes (for velocity = ∇S)
    S: np.ndarray = field(default_factory=lambda: np.array([]))
    
    # Energy on edges
    energy: np.ndarray = field(default_factory=lambda: np.array([]))
    
    # Quantum parameters
    hbar: float = 0.1
    mass: float = 1.0
    
    def __post_init__(self):
        if len(self.rho) == 0:
            # Initialize uniform flux
            self.rho = np.ones(self.n_edges, dtype=np.float64) / max(1, self.n_edges)
        if len(self.S) == 0:
            self.S = np.zeros(self.n_nodes, dtype=np.float64)
        if len(self.energy) == 0:
            self.energy = np.ones(self.n_edges, dtype=np.float64)
    
    def normalize(self):
        """Normalize flux to be a probability distribution."""
        total = self.rho.sum()
        if total > 1e-10:
            self.rho = self.rho / total
        else:
            self.rho = np.ones_like(self.rho) / len(self.rho)
    
    def entropy(self) -> float:
        """Shannon entropy of the edge flux distribution."""
        rho_safe = np.maximum(self.rho, 1e-10)
        return -np.sum(rho_safe * np.log(rho_safe))
    
    def max_flux_edge(self) -> int:
        """Index of edge with maximum flux."""
        return int(np.argmax(self.rho))
    
    def has_concentrated(self, threshold: float = 0.5) -> bool:
        """Check if flux has concentrated on a small subset of edges."""
        sorted_rho = np.sort(self.rho)[::-1]
        cumsum = np.cumsum(sorted_rho)
        # How many edges contain 50% of the flux?
        n_significant = np.searchsorted(cumsum, threshold) + 1
        return n_significant <= max(3, 0.1 * len(self.rho))


# =============================================================================
# PHASE 39: GRAPH MADELUNG FLOW ENGINE
# =============================================================================

class GraphMadelungFlow:
    """
    Madelung equations on the composition graph.
    
    This is the CORRECT DYNAMICS for compositional flow:
    
    Continuity: ∂ρ/∂t + div(ρv) = 0
    Euler:      ∂v/∂t + (v·∇)v = -∇(V + Q)
    
    Where all operators are DISCRETE GRAPH OPERATORS:
    - ∇ = gradient on graph (node → edge)
    - div = divergence on graph (edge → node)
    - V = potential energy (from Fisher-Rao distance)
    - Q = quantum potential (prevents collapse to single edge)
    """
    
    def __init__(self,
                 graph: CompositionGraph,
                 dt: float = 0.1,
                 dissipation: float = 0.1,
                 hbar: float = 0.1,
                 mass: float = 1.0,
                 verbose: bool = False):
        self.graph = graph
        self.dt = dt
        self.dissipation = dissipation
        self.hbar = hbar
        self.mass = mass
        self.verbose = verbose
        
        self.stats = {
            'total_steps': 0,
            'converged': False,
            'convergence_step': -1
        }
    
    def initialize_flow(self, 
                        input_grid: np.ndarray,
                        target: np.ndarray) -> EdgeFlowState:
        """
        Initialize the flow state.
        
        The fluid starts concentrated at edges leaving the Source node (Identity).
        """
        state = EdgeFlowState(
            n_edges=self.graph.n_edges,
            n_nodes=self.graph.n_ops,
            hbar=self.hbar,
            mass=self.mass
        )
        
        # Initialize flux: concentrate on edges from source
        source_idx = self.graph.source_idx
        state.rho = np.zeros(self.graph.n_edges, dtype=np.float64)
        
        # Find edges leaving the source
        source_edges = []
        for e_idx, (src, dst) in enumerate(self.graph.edge_list):
            if src == source_idx:
                source_edges.append(e_idx)
        
        if source_edges:
            # Uniform distribution on source edges
            for e_idx in source_edges:
                state.rho[e_idx] = 1.0 / len(source_edges)
        else:
            # Fallback: uniform over all edges
            state.rho = np.ones(self.graph.n_edges) / self.graph.n_edges
        
        # Compute initial energy landscape
        state.energy = self._compute_edge_energies(input_grid, target)
        
        return state
    
    def _compute_edge_energies(self, 
                                grid: np.ndarray, 
                                target: np.ndarray) -> np.ndarray:
        """Compute the potential energy V for each edge."""
        V = np.ones(self.graph.n_edges, dtype=np.float64) * 10.0
        
        for e_idx, (src, dst) in enumerate(self.graph.edge_list):
            V[e_idx] = self.graph.compute_transition_energy(src, dst, grid, target)
        
        return V
    
    def compute_quantum_potential(self, state: EdgeFlowState) -> np.ndarray:
        """
        Compute quantum potential Q on edges.
        
        Q = -ℏ²/(2m) · Δ√ρ / √ρ
        
        On a graph, we approximate this using the graph structure.
        """
        # sqrt(rho) on edges
        sqrt_rho = np.sqrt(np.maximum(state.rho, 1e-8))
        
        # Laplacian of sqrt_rho (approximate using edge neighbors)
        # Two edges are "neighbors" if they share a node
        laplacian_sqrt_rho = np.zeros_like(sqrt_rho)
        
        for e_idx, (src, dst) in enumerate(self.graph.edge_list):
            # Find neighboring edges (edges that share src or dst)
            neighbor_values = []
            for e2_idx, (s2, d2) in enumerate(self.graph.edge_list):
                if e2_idx != e_idx:
                    if src == s2 or src == d2 or dst == s2 or dst == d2:
                        neighbor_values.append(sqrt_rho[e2_idx])
            
            if neighbor_values:
                mean_neighbor = np.mean(neighbor_values)
                laplacian_sqrt_rho[e_idx] = mean_neighbor - sqrt_rho[e_idx]
        
        # Q = -ℏ²/(2m) · Δ√ρ / √ρ
        Q = -(self.hbar**2 / (2 * self.mass)) * laplacian_sqrt_rho / sqrt_rho
        Q = np.clip(Q, -10.0, 10.0)
        Q = np.nan_to_num(Q, nan=0.0)
        
        return Q
    
    def step(self, state: EdgeFlowState, grid: np.ndarray, target: np.ndarray) -> EdgeFlowState:
        """
        Perform one timestep of the graph Madelung equations.
        
        Optimized version with vectorized operations.
        """
        n_edges = self.graph.n_edges
        if n_edges <= 1:
            return state
        
        # ===== Compute potentials =====
        V = state.energy  # Potential energy (Fisher-Rao distance)
        Q = self.compute_quantum_potential(state)  # Quantum potential
        
        # Total potential
        U = V + Q
        
        # ===== Compute velocity from phase gradient =====
        grad_S = self.graph.gradient(state.S)
        v = np.clip(grad_S, -10.0, 10.0)
        
        # ===== Euler equation: update velocity =====
        dv_dt = -U - self.dissipation * v  # Simplified gradient
        dv_dt = np.nan_to_num(dv_dt, nan=0.0)
        
        # Update phase S
        div_v = self.graph.divergence(v)
        state.S -= div_v * self.dt
        state.S = np.clip(state.S, -100.0, 100.0)
        
        # ===== Continuity equation: vectorized update =====
        # Build edge neighbor structure once (precompute for efficiency)
        # Use vectorized energy-based diffusion
        drho_dt = -0.1 * U * state.rho  # Flow away from high energy
        
        # Add diffusion toward low-energy neighbors
        # This is a simplified version - full version would use edge adjacency
        mean_rho = np.mean(state.rho)
        drho_dt += 0.05 * (mean_rho - state.rho)  # Regularization
        
        # Update flux
        state.rho += drho_dt * self.dt
        
        # Enforce positivity and normalize
        state.rho = np.maximum(state.rho, 1e-10)
        state.rho = np.nan_to_num(state.rho, nan=1e-10)
        state.normalize()
        
        self.stats['total_steps'] += 1
        
        return state
    
    def flow(self,
             input_grid: np.ndarray,
             target: np.ndarray,
             max_steps: int = 100,
             convergence_threshold: float = 0.5) -> Tuple[EdgeFlowState, List[Dict]]:
        """
        Run the flow until convergence or max_steps.
        
        Returns the final state and a trace of the evolution.
        """
        state = self.initialize_flow(input_grid, target)
        trace = []
        
        prev_entropy = state.entropy()
        
        for step in range(max_steps):
            # Evolve
            state = self.step(state, input_grid, target)
            
            # Record trace
            entropy = state.entropy()
            max_flux = np.max(state.rho)
            trace.append({
                'step': step,
                'entropy': entropy,
                'max_flux': max_flux,
                'concentrated': state.has_concentrated()
            })
            
            # Check convergence
            if state.has_concentrated(threshold=convergence_threshold):
                self.stats['converged'] = True
                self.stats['convergence_step'] = step
                if self.verbose:
                    print(f"[FLOW] Converged at step {step}, entropy={entropy:.4f}")
                break
            
            # Check entropy stagnation
            if abs(entropy - prev_entropy) < 1e-6:
                # Entropy not changing - might be stuck
                pass
            
            prev_entropy = entropy
        
        return state, trace
    
    def extract_path(self, state: EdgeFlowState, max_depth: int = 10) -> List[int]:
        """
        Extract the operator sequence by tracing the maximum flux streamline.
        
        This converts the continuous flow back into a discrete path.
        """
        path = []
        current_node = self.graph.source_idx
        visited_nodes = {current_node}
        
        for _ in range(max_depth):
            # Find the maximum-flux edge leaving current_node
            best_edge = -1
            best_flux = -1.0
            
            for e_idx, (src, dst) in enumerate(self.graph.edge_list):
                if src == current_node and dst not in visited_nodes:
                    if state.rho[e_idx] > best_flux:
                        best_flux = state.rho[e_idx]
                        best_edge = e_idx
            
            if best_edge < 0:
                break  # No valid outgoing edges
            
            # Get destination operator
            _, dst = self.graph.edge_list[best_edge]
            path.append(dst)
            visited_nodes.add(dst)
            current_node = dst
            
            # Stop if flux becomes negligible
            if best_flux < 1e-4:
                break
        
        return path
    
    def apply_path(self, path: List[int], grid: np.ndarray) -> np.ndarray:
        """Apply a sequence of operators to a grid."""
        result = grid.copy()
        for op_idx in path:
            applied = self.graph.apply_operator(op_idx, result)
            if applied is not None:
                result = applied
        return result


# =============================================================================
# PHASE 39: COMPOSITIONAL FLOW SOLVER
# =============================================================================

class CompositionalFlowSolver:
    """
    Solver that uses graph-based hydrodynamic flow to find operator compositions.
    
    This replaces A* search with continuous flow on the composition graph.
    """
    
    def __init__(self, verbose: bool = False):
        self.metric = AdaptiveFisherRaoMetric()
        self.memory = ContentAddressedOperatorMemory()
        self.graph: Optional[CompositionGraph] = None
        self.flow_engine: Optional[GraphMadelungFlow] = None
        self.verbose = verbose
        
        self.stats = {
            'tasks_attempted': 0,
            'perfect_solves': 0,
            'near_misses': 0,
            'flow_converged': 0,
            'total_flow_steps': 0,
            'avg_path_length': 0.0
        }
    
    def _initialize(self):
        """Initialize the composition graph and flow engine."""
        if self.graph is None:
            self.graph = CompositionGraph(self.memory, self.metric)
            self.flow_engine = GraphMadelungFlow(
                self.graph,
                dt=0.1,
                dissipation=0.1,
                verbose=self.verbose
            )
    
    def solve(self, task: ARCTask) -> Optional[Tuple[np.ndarray, float]]:
        """
        Solve an ARC task using compositional flow.
        
        Returns (solution_grid, distance) or None.
        """
        self._initialize()
        self.stats['tasks_attempted'] += 1
        
        if not task.test_examples:
            return None
        
        # Get grids
        test_input = task.test_examples[0].input_grid.to_numpy()
        test_output = task.test_examples[0].output_grid.to_numpy() if task.test_examples[0].output_grid is not None else None
        train_outputs = [ex.output_grid.to_numpy() for ex in task.train_examples]
        
        if not train_outputs:
            return None
        
        # Use last training output as target reference
        target_ref = train_outputs[-1]
        
        if self.verbose:
            print(f"\n[SOLVE] Task {task.task_id}: input {test_input.shape}")
        
        # Run flow
        state, trace = self.flow_engine.flow(
            test_input,
            target_ref,
            max_steps=100,
            convergence_threshold=0.5
        )
        
        if self.flow_engine.stats['converged']:
            self.stats['flow_converged'] += 1
        
        self.stats['total_flow_steps'] += self.flow_engine.stats['total_steps']
        
        # Extract operator path
        path = self.flow_engine.extract_path(state, max_depth=6)
        self.stats['avg_path_length'] = (
            (self.stats['avg_path_length'] * (self.stats['tasks_attempted'] - 1) + len(path))
            / self.stats['tasks_attempted']
        )
        
        if self.verbose:
            op_names = [self.graph.operators[i].op_type for i in path]
            print(f"[SOLVE] Path: {' -> '.join(op_names)}")
        
        # Apply path
        result = self.flow_engine.apply_path(path, test_input)
        
        # Compute distance
        if test_output is not None:
            try:
                result_grid = numpy_to_arcgrid(result)
                target_grid = numpy_to_arcgrid(test_output)
                dist_result = self.metric.compute(result_grid, target_grid)
                distance = dist_result['total'] if isinstance(dist_result, dict) else float(dist_result)
            except:
                distance = 1.0
            
            if distance < 0.001:
                self.stats['perfect_solves'] += 1
                if self.verbose:
                    print(f"[SOLVE] PERFECT! Distance={distance:.6f}")
            elif distance < 0.1:
                self.stats['near_misses'] += 1
                if self.verbose:
                    print(f"[SOLVE] NEAR: Distance={distance:.4f}")
            else:
                if self.verbose:
                    print(f"[SOLVE] APPROX: Distance={distance:.4f}")
            
            return result, distance
        else:
            try:
                result_grid = numpy_to_arcgrid(result)
                ref_grid = numpy_to_arcgrid(target_ref)
                dist_result = self.metric.compute(result_grid, ref_grid)
                distance = dist_result['total'] if isinstance(dist_result, dict) else float(dist_result)
            except:
                distance = 1.0
            return result, distance
    
    def solve_batch(self, tasks: List[ARCTask]) -> Dict[str, Any]:
        """Solve a batch of tasks."""
        results = {}
        
        for i, task in enumerate(tasks):
            result = self.solve(task)
            if result:
                grid, distance = result
                results[task.task_id] = {
                    'grid': grid,
                    'distance': distance,
                    'perfect': distance < 0.001
                }
            
            if (i + 1) % 10 == 0:
                print(f"[BATCH] Progress: {i+1}/{len(tasks)}, "
                      f"perfect={self.stats['perfect_solves']}, "
                      f"converged={self.stats['flow_converged']}")
        
        return results


# =============================================================================
# COMPARISON AND MAIN
# =============================================================================

def run_comparison(tasks: List[ARCTask], n_tasks: int = 20, verbose: bool = True):
    """Run Phase 39 and compare with baseline."""
    print("=" * 70)
    print("PHASE 39 vs PHASE 37 COMPARISON")
    print("=" * 70)
    
    # Phase 39: Compositional Flow
    print("\n[1] Running Phase 39 (Compositional Flow on Graph)...")
    solver = CompositionalFlowSolver(verbose=verbose)
    
    start_time = time.time()
    results = solver.solve_batch(tasks[:n_tasks])
    elapsed = time.time() - start_time
    
    print(f"\nPhase 39 Results:")
    print(f"  Perfect solves: {solver.stats['perfect_solves']}")
    print(f"  Near misses: {solver.stats['near_misses']}")
    print(f"  Flow converged: {solver.stats['flow_converged']}")
    print(f"  Total flow steps: {solver.stats['total_flow_steps']}")
    print(f"  Avg path length: {solver.stats['avg_path_length']:.2f}")
    print(f"  Time: {elapsed:.2f}s")
    
    # Baseline comparison
    print(f"\nPhase 37 Baseline (from previous runs):")
    print(f"  Perfect solves: ~26 (reference)")
    print(f"  Near misses: ~4 (reference)")
    
    # Summary table
    print("\n" + "=" * 70)
    print("COMPARISON SUMMARY")
    print("=" * 70)
    print(f"{'Metric':<30} {'Phase 37 (A*)':<20} {'Phase 39 (GraphFlow)':<20}")
    print("-" * 70)
    print(f"{'Perfect Solves':<30} {'~26 (baseline)':<20} {solver.stats['perfect_solves']:<20}")
    print(f"{'Near Misses':<30} {'~4 (baseline)':<20} {solver.stats['near_misses']:<20}")
    print(f"{'Flow Converged':<30} {'N/A':<20} {solver.stats['flow_converged']:<20}")
    print(f"{'Avg Path Length':<30} {'~3 (estimate)':<20} {solver.stats['avg_path_length']:.2f}")
    
    return solver.stats


def run_standalone_test():
    """Run a standalone test with synthetic data."""
    print("=" * 70)
    print("STANDALONE COMPOSITIONAL FLOW TEST")
    print("=" * 70)
    
    # Create synthetic test
    input_grid = np.array([
        [0, 0, 0, 0, 0],
        [0, 1, 1, 0, 0],
        [0, 1, 1, 0, 0],
        [0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0]
    ])
    
    target = np.array([
        [0, 0, 0, 0, 0],
        [0, 0, 0, 1, 1],
        [0, 0, 0, 1, 1],
        [0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0]
    ])
    
    print(f"Input:\n{input_grid}\n")
    print(f"Target:\n{target}\n")
    
    # Initialize
    metric = AdaptiveFisherRaoMetric()
    memory = ContentAddressedOperatorMemory()
    graph = CompositionGraph(memory, metric)
    flow_engine = GraphMadelungFlow(graph, verbose=True)
    
    # Run flow
    print("[TEST] Running compositional flow...")
    state, trace = flow_engine.flow(input_grid, target, max_steps=50)
    
    print(f"\n[TEST] Flow completed in {len(trace)} steps")
    print(f"[TEST] Converged: {flow_engine.stats['converged']}")
    print(f"[TEST] Final entropy: {state.entropy():.4f}")
    
    # Extract path
    path = flow_engine.extract_path(state)
    op_names = [graph.operators[i].op_type for i in path]
    print(f"[TEST] Extracted path: {' -> '.join(op_names)}")
    
    # Apply path
    result = flow_engine.apply_path(path, input_grid)
    print(f"[TEST] Result:\n{result}")
    
    # Compare
    try:
        result_grid = numpy_to_arcgrid(result)
        target_grid = numpy_to_arcgrid(target)
        dist_result = metric.compute(result_grid, target_grid)
        distance = dist_result['total'] if isinstance(dist_result, dict) else float(dist_result)
        print(f"\n[TEST] Distance to target: {distance:.4f}")
        
        if distance < 0.001:
            print("[TEST] SUCCESS: Perfect match!")
        elif distance < 0.1:
            print("[TEST] NEAR: Close match")
        else:
            print("[TEST] APPROX: Partial match")
    except Exception as e:
        print(f"[TEST] Error computing distance: {e}")
    
    print("\n" + "=" * 70)
    print("STANDALONE TEST COMPLETE")
    print("=" * 70)


def main():
    """Run Phase 39 Compositional Flow Solver."""
    print("=" * 70)
    print("PHASE 39: FLOW ON THE COMPOSITIONAL MANIFOLD")
    print("=" * 70)
    print()
    print("Key Innovation: Flow on EDGES (transitions), not NODES (operators)")
    print("Topology: Directed composition graph with type-compatible adjacency")
    print("Dynamics: Graph Madelung equations with discrete calculus")
    print()
    
    # Load tasks
    paths = ["data/arc/training", "C:/Lean4 Projects/data/arc/training"]
    arc_path = next((p for p in paths if Path(p).exists() and list(Path(p).glob("*.json"))), None)
    
    if arc_path:
        tasks = load_arc_tasks(arc_path, 'cpu')
    else:
        tasks = []
    
    if not tasks:
        print("[INFO] No ARC tasks found. Running standalone test...")
        run_standalone_test()
        return
    
    print(f"Loaded {len(tasks)} tasks\n")
    
    # Run comparison
    comparison = run_comparison(tasks, n_tasks=20, verbose=False)
    
    print("\n" + "=" * 70)
    print("PHASE 39 COMPLETE")
    print("=" * 70)
    
    return comparison


if __name__ == "__main__":
    main()
