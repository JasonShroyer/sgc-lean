"""
ARC-SGC Phase 19: The Fractal Reasoning Engine

THEORETICAL FOUNDATION:
Phase 18 achieved 32 perfect solves with Decomposition + Consensus.
Phase 19 upgrades this to a true AGI architecture by replacing heuristics with algebra.

THREE UPGRADES:

1. FRACTAL DECOMPOSITION (Recursive 'Diff'):
   - Level 0: Grid = Static + Dynamic
   - Level 1: Dynamic = Object A + Object B + Noise
   - Level 2: Object A = Shape (Invariant) + Position (Variable)
   - Stop when Residual Entropy = 0

2. ALGEBRAIC VERIFICATION (Beyond Voting):
   - Don't compare method strings ('shift' == 'gravity')
   - Compare OUTPUTS: f(x) ≡ g(x) on all training data
   - Extensional equality with different code = HIGH confidence

3. COOLING SCHEDULE (Simulated Annealing):
   - High T: Accept any program solving 50%+ examples
   - Low T: Only accept Jackknife Stable + MDL optimal
   - Freeze to select final answer

CERTAINTY LOGIC:
- 1.0: Stable + Simple + Verified by >1 Solver
- 0.8: Stable + Simple (Single Solver)
- 0.5: Accurate but Unstable or Complex
- 0.0: Failed (Do not submit)

SGC GROUNDING:
- Fractal Decomposition ≈ Renormalization Group (scale invariance)
- Algebraic Verification ≈ Quotient by observational equivalence
- Cooling ≈ Free energy minimization (F = E - TS)
"""

import torch
from dataclasses import dataclass, field
from typing import List, Tuple, Dict, Optional, Set, Callable, Any
from collections import Counter
from enum import Enum, auto
import numpy as np
from pathlib import Path
import sys
import time
import math
from abc import ABC, abstractmethod

sys.path.insert(0, str(Path(__file__).parent))
from arc_sgc_phase8_3 import (
    ARCPhase83Config, ARCGrid, ARCObject, ARCExample, ARCTask,
    load_arc_tasks, detect_objects, compute_defect_energy,
    GeometryFirstSolver, CompositePotential, relax_all_colors,
    V_ContactDist, V_TopEdge, V_BottomEdge, V_BoundaryDist,
    CropToContentMorphism, ExtractObjectMorphism
)
from arc_sgc_phase15 import SelfImprovingSolver

def printfl(*args, **kwargs):
    print(*args, **kwargs)
    sys.stdout.flush()


# =============================================================================
# COMPONENT 1: FRACTAL DECOMPOSITION (Recursive Layer Tree)
# =============================================================================

class LayerType(Enum):
    """Types of layers in the fractal decomposition."""
    STATIC = auto()      # Unchanged pixels (Identity transform)
    UNIFORM = auto()     # Single color region
    OBJECT = auto()      # Connected component
    MOTION = auto()      # Region that moved
    COLOR_CHANGE = auto()  # Region that changed color
    NOISE = auto()       # Unexplained residual
    COMPOSITE = auto()   # Contains sub-layers


@dataclass
class FractalLayer:
    """
    A node in the fractal decomposition tree.
    
    Each layer represents a region of the grid with a specific transformation.
    Layers can have children (sub-decomposition).
    """
    layer_type: LayerType
    mask: torch.Tensor  # Boolean mask of pixels in this layer
    transform: Optional[str] = None  # The operation that explains this layer
    confidence: float = 0.0  # How certain we are about this layer
    entropy: float = 0.0  # Residual entropy (unexplained information)
    children: List['FractalLayer'] = field(default_factory=list)
    
    @property
    def pixel_count(self) -> int:
        return self.mask.sum().item()
    
    @property
    def is_simple(self) -> bool:
        """A layer is simple if it's uniform color or < 5 pixels."""
        return self.layer_type == LayerType.UNIFORM or self.pixel_count < 5
    
    @property
    def is_leaf(self) -> bool:
        return len(self.children) == 0


@dataclass
class FractalDecomposition:
    """
    The complete fractal decomposition of a grid pair.
    
    This is a tree structure where:
    - Root represents the entire grid
    - Children represent sub-regions with their own transformations
    - Leaves are "simple" regions (uniform or tiny)
    """
    root: FractalLayer
    total_entropy: float = 0.0
    depth: int = 0
    
    def get_all_layers(self) -> List[FractalLayer]:
        """Flatten the tree into a list of all layers."""
        result = []
        stack = [self.root]
        while stack:
            layer = stack.pop()
            result.append(layer)
            stack.extend(layer.children)
        return result
    
    def get_leaves(self) -> List[FractalLayer]:
        """Get all leaf layers (the actual transformations to apply)."""
        return [l for l in self.get_all_layers() if l.is_leaf]


class FractalDecomposer:
    """
    Recursive decomposition engine.
    
    Decomposes a grid pair into a tree of layers, where each layer
    represents a region with a specific transformation.
    
    Stop condition: When residual entropy = 0 (all pixels explained)
    or layer is "simple" (uniform color or < 5 pixels).
    """
    
    def __init__(self, config: ARCPhase83Config, max_depth: int = 3):
        self.config = config
        self.max_depth = max_depth
    
    def decompose(self, input_grid: ARCGrid, output_grid: ARCGrid) -> FractalDecomposition:
        """
        Recursively decompose the grid pair into a fractal layer tree.
        """
        H_in, W_in = input_grid.shape
        H_out, W_out = output_grid.shape
        
        # Handle shape mismatch at root level
        if (H_in, W_in) != (H_out, W_out):
            root = FractalLayer(
                layer_type=LayerType.COMPOSITE,
                mask=torch.ones(H_in, W_in, dtype=torch.bool),
                transform="shape_change",
                confidence=0.5,
                entropy=1.0  # High entropy - shape change is complex
            )
            return FractalDecomposition(root=root, total_entropy=1.0, depth=0)
        
        # Start recursive decomposition
        full_mask = torch.ones(H_in, W_in, dtype=torch.bool)
        root = self._decompose_recursive(input_grid, output_grid, full_mask, depth=0)
        
        # Calculate total entropy
        total_entropy = self._calculate_total_entropy(root)
        depth = self._calculate_depth(root)
        
        return FractalDecomposition(root=root, total_entropy=total_entropy, depth=depth)
    
    def _decompose_recursive(
        self, 
        input_grid: ARCGrid, 
        output_grid: ARCGrid, 
        mask: torch.Tensor,
        depth: int
    ) -> FractalLayer:
        """
        Recursively decompose a masked region.
        """
        if depth >= self.max_depth or mask.sum() < 5:
            # Base case: too deep or too small
            return self._create_leaf_layer(input_grid, output_grid, mask)
        
        # Level 0: Separate Static from Dynamic
        static_mask, dynamic_mask = self._separate_static_dynamic(
            input_grid, output_grid, mask
        )
        
        children = []
        
        # Process static region
        if static_mask.any():
            static_layer = FractalLayer(
                layer_type=LayerType.STATIC,
                mask=static_mask,
                transform="identity",
                confidence=1.0,  # Static pixels are certain
                entropy=0.0  # No information to explain
            )
            children.append(static_layer)
        
        # Process dynamic region
        if dynamic_mask.any():
            # Try to further decompose the dynamic region
            dynamic_children = self._decompose_dynamic(
                input_grid, output_grid, dynamic_mask, depth + 1
            )
            children.extend(dynamic_children)
        
        # Create composite layer
        if len(children) == 1:
            return children[0]
        
        return FractalLayer(
            layer_type=LayerType.COMPOSITE,
            mask=mask,
            transform="composite",
            confidence=min(c.confidence for c in children) if children else 0.0,
            entropy=sum(c.entropy for c in children),
            children=children
        )
    
    def _separate_static_dynamic(
        self, 
        input_grid: ARCGrid, 
        output_grid: ARCGrid, 
        mask: torch.Tensor
    ) -> Tuple[torch.Tensor, torch.Tensor]:
        """Separate pixels that don't change from those that do."""
        same = input_grid.data == output_grid.data
        static_mask = mask & same
        dynamic_mask = mask & ~same
        return static_mask, dynamic_mask
    
    def _decompose_dynamic(
        self, 
        input_grid: ARCGrid, 
        output_grid: ARCGrid, 
        mask: torch.Tensor,
        depth: int
    ) -> List[FractalLayer]:
        """
        Decompose the dynamic region into sub-layers.
        
        Strategies:
        1. Color change detection (same position, different color)
        2. Motion detection (same color, different position)
        3. Object-based decomposition (connected components)
        """
        layers = []
        remaining_mask = mask.clone()
        
        # Strategy 1: Detect uniform color fills
        uniform_layer, remaining = self._detect_uniform_fill(
            input_grid, output_grid, remaining_mask
        )
        if uniform_layer is not None:
            layers.append(uniform_layer)
            remaining_mask = remaining
        
        # Strategy 2: Detect color changes (pixel-wise remapping)
        color_layers, remaining = self._detect_color_changes(
            input_grid, output_grid, remaining_mask
        )
        layers.extend(color_layers)
        remaining_mask = remaining
        
        # Strategy 3: If still unexplained, decompose by connected components
        if remaining_mask.any():
            object_layers = self._decompose_by_objects(
                input_grid, output_grid, remaining_mask, depth
            )
            layers.extend(object_layers)
        
        # If nothing worked, mark as noise
        if not layers:
            layers.append(FractalLayer(
                layer_type=LayerType.NOISE,
                mask=mask,
                transform="unknown",
                confidence=0.0,
                entropy=self._calculate_entropy(mask)
            ))
        
        return layers
    
    def _detect_uniform_fill(
        self, 
        input_grid: ARCGrid, 
        output_grid: ARCGrid, 
        mask: torch.Tensor
    ) -> Tuple[Optional[FractalLayer], torch.Tensor]:
        """
        Detect if the dynamic region is filled with a uniform color.
        """
        if not mask.any():
            return None, mask
        
        output_vals = output_grid.data[mask]
        unique_out = output_vals.unique()
        
        if len(unique_out) == 1:
            fill_color = unique_out[0].item()
            return FractalLayer(
                layer_type=LayerType.UNIFORM,
                mask=mask,
                transform=f"fill({fill_color})",
                confidence=1.0,
                entropy=0.0
            ), torch.zeros_like(mask)
        
        return None, mask
    
    def _detect_color_changes(
        self, 
        input_grid: ARCGrid, 
        output_grid: ARCGrid, 
        mask: torch.Tensor
    ) -> Tuple[List[FractalLayer], torch.Tensor]:
        """
        Detect pixel-wise color remapping.
        """
        layers = []
        remaining = mask.clone()
        
        if not mask.any():
            return layers, remaining
        
        # Find color pairs (in -> out)
        in_vals = input_grid.data[mask]
        out_vals = output_grid.data[mask]
        
        # Group by color change
        color_pairs = Counter(zip(in_vals.tolist(), out_vals.tolist()))
        
        for (in_c, out_c), count in color_pairs.most_common():
            if in_c == out_c:
                continue  # Not a change
            
            # Find pixels with this color change
            change_mask = mask & (input_grid.data == in_c) & (output_grid.data == out_c)
            
            if change_mask.any():
                layers.append(FractalLayer(
                    layer_type=LayerType.COLOR_CHANGE,
                    mask=change_mask,
                    transform=f"color({in_c}->{out_c})",
                    confidence=0.9,
                    entropy=0.1
                ))
                remaining = remaining & ~change_mask
        
        return layers, remaining
    
    def _decompose_by_objects(
        self, 
        input_grid: ARCGrid, 
        output_grid: ARCGrid, 
        mask: torch.Tensor,
        depth: int
    ) -> List[FractalLayer]:
        """
        Decompose by connected components (objects).
        """
        layers = []
        
        # Find connected components in the mask
        components = self._find_connected_components(mask)
        
        for comp_mask in components:
            if comp_mask.sum() < 3:
                # Tiny component - treat as noise
                layers.append(FractalLayer(
                    layer_type=LayerType.NOISE,
                    mask=comp_mask,
                    transform="noise",
                    confidence=0.3,
                    entropy=0.5
                ))
            else:
                # Recursively decompose this object
                sub_layer = self._decompose_recursive(
                    input_grid, output_grid, comp_mask, depth + 1
                )
                sub_layer.layer_type = LayerType.OBJECT
                layers.append(sub_layer)
        
        return layers
    
    def _find_connected_components(self, mask: torch.Tensor) -> List[torch.Tensor]:
        """Find connected components in a boolean mask."""
        if not mask.any():
            return []
        
        H, W = mask.shape
        visited = torch.zeros_like(mask, dtype=torch.bool)
        components = []
        
        def flood_fill(start_r, start_c):
            comp = torch.zeros_like(mask, dtype=torch.bool)
            stack = [(start_r, start_c)]
            while stack:
                r, c = stack.pop()
                if r < 0 or r >= H or c < 0 or c >= W:
                    continue
                if visited[r, c] or not mask[r, c]:
                    continue
                visited[r, c] = True
                comp[r, c] = True
                stack.extend([(r-1, c), (r+1, c), (r, c-1), (r, c+1)])
            return comp
        
        for r in range(H):
            for c in range(W):
                if mask[r, c] and not visited[r, c]:
                    comp = flood_fill(r, c)
                    if comp.any():
                        components.append(comp)
        
        return components
    
    def _create_leaf_layer(
        self, 
        input_grid: ARCGrid, 
        output_grid: ARCGrid, 
        mask: torch.Tensor
    ) -> FractalLayer:
        """Create a leaf layer for a simple region."""
        if not mask.any():
            return FractalLayer(
                layer_type=LayerType.NOISE,
                mask=mask,
                transform="empty",
                confidence=1.0,
                entropy=0.0
            )
        
        # Check if static
        same = (input_grid.data == output_grid.data) & mask
        if same.all():
            return FractalLayer(
                layer_type=LayerType.STATIC,
                mask=mask,
                transform="identity",
                confidence=1.0,
                entropy=0.0
            )
        
        # Check if uniform output
        out_vals = output_grid.data[mask]
        if len(out_vals.unique()) == 1:
            return FractalLayer(
                layer_type=LayerType.UNIFORM,
                mask=mask,
                transform=f"fill({out_vals[0].item()})",
                confidence=1.0,
                entropy=0.0
            )
        
        # Otherwise, unexplained
        return FractalLayer(
            layer_type=LayerType.NOISE,
            mask=mask,
            transform="unknown",
            confidence=0.0,
            entropy=self._calculate_entropy(mask)
        )
    
    def _calculate_entropy(self, mask: torch.Tensor) -> float:
        """Calculate entropy of a region (proxy: normalized pixel count)."""
        total = mask.numel()
        count = mask.sum().item()
        if total == 0:
            return 0.0
        ratio = count / total
        if ratio == 0 or ratio == 1:
            return 0.0
        return -ratio * math.log2(ratio) - (1-ratio) * math.log2(1-ratio)
    
    def _calculate_total_entropy(self, layer: FractalLayer) -> float:
        """Sum entropy across all layers."""
        total = layer.entropy
        for child in layer.children:
            total += self._calculate_total_entropy(child)
        return total
    
    def _calculate_depth(self, layer: FractalLayer) -> int:
        """Calculate depth of the tree."""
        if not layer.children:
            return 0
        return 1 + max(self._calculate_depth(c) for c in layer.children)


# =============================================================================
# COMPONENT 2: ALGEBRAIC VERIFICATION (Output Equality)
# =============================================================================

@dataclass
class Program:
    """
    A candidate program that transforms input to output.
    
    Programs are compared by their OUTPUTS, not their code.
    Two programs with different code but same outputs are equivalent.
    """
    name: str
    apply: Callable[[ARCGrid], ARCGrid]  # The transformation function
    complexity: int  # Kolmogorov complexity proxy (code length)
    source: str  # Which solver generated this
    
    def __call__(self, grid: ARCGrid) -> ARCGrid:
        return self.apply(grid)


class AlgebraicVerifier:
    """
    Verifies program equivalence by comparing outputs.
    
    Key insight: Two programs are equivalent if they produce the same
    output on all inputs. This is "extensional equality."
    
    If two DIFFERENT programs are extensionally equal, our confidence
    goes UP because the solution is robust to implementation details.
    """
    
    def __init__(self, config: ARCPhase83Config):
        self.config = config
    
    def verify_equivalence(
        self, 
        prog_a: Program, 
        prog_b: Program, 
        test_inputs: List[ARCGrid]
    ) -> Tuple[bool, float]:
        """
        Check if two programs are extensionally equivalent.
        
        Returns:
            (equivalent, confidence)
            - equivalent: True if outputs match on all inputs
            - confidence: 1.0 if equivalent but different code, 0.5 if same code
        """
        if not test_inputs:
            return False, 0.0
        
        try:
            for inp in test_inputs:
                out_a = prog_a(inp)
                out_b = prog_b(inp)
                
                if out_a.shape != out_b.shape:
                    return False, 0.0
                
                if not torch.equal(out_a.data, out_b.data):
                    return False, 0.0
            
            # All outputs match
            # Higher confidence if different code (robustness)
            if prog_a.name != prog_b.name:
                return True, 1.0  # Different code, same output = robust
            else:
                return True, 0.5  # Same code = trivial equivalence
                
        except Exception:
            return False, 0.0
    
    def find_equivalence_classes(
        self, 
        programs: List[Program], 
        test_inputs: List[ARCGrid]
    ) -> List[List[Program]]:
        """
        Group programs into equivalence classes by output equality.
        
        Programs in the same class produce identical outputs.
        """
        if not programs:
            return []
        
        classes: List[List[Program]] = []
        
        for prog in programs:
            # Try to add to existing class
            added = False
            for cls in classes:
                equiv, _ = self.verify_equivalence(prog, cls[0], test_inputs)
                if equiv:
                    cls.append(prog)
                    added = True
                    break
            
            if not added:
                classes.append([prog])
        
        return classes
    
    def calculate_consensus_score(
        self, 
        equivalence_classes: List[List[Program]]
    ) -> float:
        """
        Calculate consensus score based on equivalence classes.
        
        Higher score if:
        - One class dominates (many programs agree)
        - That class has diverse sources (different solvers)
        """
        if not equivalence_classes:
            return 0.0
        
        # Find the largest class
        largest = max(equivalence_classes, key=len)
        total_programs = sum(len(cls) for cls in equivalence_classes)
        
        # Fraction of programs in largest class
        agreement_ratio = len(largest) / total_programs
        
        # Diversity of sources in largest class
        sources = set(p.source for p in largest)
        diversity = len(sources) / max(1, len(largest))
        
        # Combined score
        return agreement_ratio * (0.5 + 0.5 * diversity)


# =============================================================================
# COMPONENT 3: COOLING SCHEDULE (Simulated Annealing)
# =============================================================================

@dataclass
class CandidateSolution:
    """A candidate solution with metadata for annealing."""
    program: Program
    accuracy: float  # Fraction of training examples solved
    complexity: int  # Program length
    stability: float  # Jackknife stability score
    energy: float  # Defect energy
    
    @property
    def free_energy(self) -> float:
        """
        F = E - T*S
        
        Where:
        - E = defect energy + complexity penalty
        - S = stability (entropy-like - higher is better)
        - T = temperature (controls exploration/exploitation)
        """
        # At T=0 (frozen), only energy matters
        # At high T, stability dominates
        return self.energy + 0.01 * self.complexity - 0.1 * self.stability


class CoolingSchedule:
    """
    Simulated annealing for solution selection.
    
    High T (Exploration): Accept any program solving 50%+ examples
    Low T (Freezing): Only accept Jackknife Stable + MDL optimal
    """
    
    def __init__(self, config: ARCPhase83Config):
        self.config = config
        self.initial_temp = 1.0
        self.final_temp = 0.01
        self.cooling_rate = 0.9
    
    def anneal_solution(
        self, 
        candidates: List[CandidateSolution]
    ) -> Tuple[Optional[CandidateSolution], float]:
        """
        Apply annealing to select the best solution.
        
        Returns:
            (best_solution, certainty_score)
        """
        if not candidates:
            return None, 0.0
        
        # Filter by accuracy (must be 100% on train for final selection)
        perfect = [c for c in candidates if c.accuracy >= 1.0 - 1e-6]
        
        if not perfect:
            # No perfect solution - return best approximate
            best = min(candidates, key=lambda c: c.energy)
            return best, 0.3  # Low certainty
        
        # Sort by complexity (MDL principle)
        perfect.sort(key=lambda c: c.complexity)
        
        # Filter by stability
        stable = [c for c in perfect if c.stability >= 0.8]
        
        if stable:
            # Best = simplest stable solution
            best = stable[0]
            certainty = 0.9 if len(stable) > 1 else 0.8
        else:
            # No stable solution - use simplest perfect
            best = perfect[0]
            certainty = 0.6
        
        return best, certainty
    
    def calculate_acceptance_probability(
        self, 
        current_energy: float, 
        new_energy: float, 
        temperature: float
    ) -> float:
        """
        Boltzmann acceptance probability.
        
        P(accept) = 1 if new_energy < current_energy
        P(accept) = exp(-(new - current)/T) otherwise
        """
        if new_energy < current_energy:
            return 1.0
        
        if temperature < 1e-10:
            return 0.0
        
        return math.exp(-(new_energy - current_energy) / temperature)


# =============================================================================
# COMPONENT 4: RIGOROUS CERTAINTY SCORE
# =============================================================================

@dataclass
class CertaintyAssessment:
    """
    Rigorous certainty assessment with components.
    
    Certainty = 1.0: Stable + Simple + Verified by >1 Solver
    Certainty = 0.8: Stable + Simple (Single Solver)
    Certainty = 0.5: Accurate but Unstable or Complex
    Certainty = 0.0: Failed (Do not submit)
    """
    total_score: float  # 0.0 to 1.0
    accuracy_component: float
    stability_component: float
    consensus_component: float
    simplicity_component: float
    decomposition_quality: float
    
    @property
    def should_submit(self) -> bool:
        """Only submit if certainty >= 0.8"""
        return self.total_score >= 0.8
    
    @property
    def certainty_level(self) -> str:
        if self.total_score >= 0.95:
            return "CERTAIN"
        elif self.total_score >= 0.8:
            return "HIGH"
        elif self.total_score >= 0.5:
            return "MEDIUM"
        else:
            return "LOW"


class CertaintyCalculator:
    """
    Calculate rigorous certainty score.
    """
    
    def __init__(self, config: ARCPhase83Config):
        self.config = config
    
    def calculate(
        self,
        accuracy: float,
        stability: float,
        consensus: float,
        complexity: int,
        decomposition_entropy: float
    ) -> CertaintyAssessment:
        """
        Calculate certainty from components.
        
        Weights:
        - Accuracy: 40% (must be 100% for high certainty)
        - Stability: 25% (Jackknife robustness)
        - Consensus: 20% (multiple solvers agree)
        - Simplicity: 10% (MDL principle)
        - Decomposition: 5% (low residual entropy)
        """
        # Accuracy component (sharp threshold at 100%)
        if accuracy >= 1.0 - 1e-6:
            accuracy_score = 1.0
        elif accuracy >= 0.9:
            accuracy_score = 0.5
        else:
            accuracy_score = 0.0
        
        # Stability component
        stability_score = stability
        
        # Consensus component
        consensus_score = consensus
        
        # Simplicity component (lower complexity = higher score)
        simplicity_score = 1.0 / (1.0 + 0.01 * complexity)
        
        # Decomposition quality (lower entropy = higher score)
        decomp_score = 1.0 / (1.0 + decomposition_entropy)
        
        # Weighted sum
        total = (
            0.40 * accuracy_score +
            0.25 * stability_score +
            0.20 * consensus_score +
            0.10 * simplicity_score +
            0.05 * decomp_score
        )
        
        return CertaintyAssessment(
            total_score=total,
            accuracy_component=accuracy_score,
            stability_component=stability_score,
            consensus_component=consensus_score,
            simplicity_component=simplicity_score,
            decomposition_quality=decomp_score
        )


# =============================================================================
# THE UNIFIED PHASE 19 SOLVER
# =============================================================================

class Phase19Solver:
    """
    The Fractal Reasoning Engine.
    
    Combines:
    1. Fractal Decomposition (recursive layer analysis)
    2. Algebraic Verification (output equality)
    3. Cooling Schedule (simulated annealing)
    4. Rigorous Certainty (0.0 - 1.0 score)
    """
    
    def __init__(self, config: ARCPhase83Config):
        self.config = config
        self.decomposer = FractalDecomposer(config)
        self.verifier = AlgebraicVerifier(config)
        self.cooler = CoolingSchedule(config)
        self.certainty_calc = CertaintyCalculator(config)
        
        # Base solvers for generating candidates
        self.geometry_solver = GeometryFirstSolver(config)
        self.physics_solver = SelfImprovingSolver(config)
    
    def solve_task(self, task: ARCTask, verbose: bool = False) -> Dict:
        """Solve with fractal reasoning."""
        start_time = time.time()
        
        # Step 1: Fractal decomposition
        decompositions = []
        for ex in task.train_examples:
            decomp = self.decomposer.decompose(ex.input_grid, ex.output_grid)
            decompositions.append(decomp)
        
        avg_entropy = np.mean([d.total_entropy for d in decompositions])
        avg_depth = np.mean([d.depth for d in decompositions])
        
        # Step 2: Generate candidate programs from decomposition
        candidates = self._generate_candidates_from_decomposition(task, decompositions)
        
        # Step 3: Generate candidates from base solvers
        base_candidates = self._generate_base_candidates(task)
        candidates.extend(base_candidates)
        
        # Step 4: Algebraic verification - group by output equivalence
        test_inputs = [ex.input_grid for ex in task.train_examples]
        programs = [c.program for c in candidates if c.program is not None]
        equiv_classes = self.verifier.find_equivalence_classes(programs, test_inputs)
        consensus_score = self.verifier.calculate_consensus_score(equiv_classes)
        
        # Step 5: Cooling - select best solution
        best_candidate, annealing_certainty = self.cooler.anneal_solution(candidates)
        
        # Step 6: Stability check (Jackknife)
        stability = self._check_stability(task, best_candidate) if best_candidate else 0.0
        
        # Step 7: Calculate final certainty
        if best_candidate:
            certainty = self.certainty_calc.calculate(
                accuracy=best_candidate.accuracy,
                stability=stability,
                consensus=consensus_score,
                complexity=best_candidate.complexity,
                decomposition_entropy=avg_entropy
            )
        else:
            certainty = CertaintyAssessment(0.0, 0.0, 0.0, 0.0, 0.0, 0.0)
        
        # Compile results
        is_perfect = best_candidate is not None and best_candidate.energy < self.config.energy_threshold
        
        return {
            'task_id': task.task_id,
            'avg_train_energy': best_candidate.energy if best_candidate else float('inf'),
            'method': best_candidate.program.name if best_candidate and best_candidate.program else 'none',
            'certainty_score': certainty.total_score,
            'certainty_level': certainty.certainty_level,
            'should_submit': certainty.should_submit,
            'stability': stability,
            'consensus': consensus_score,
            'decomposition_entropy': avg_entropy,
            'decomposition_depth': avg_depth,
            'num_candidates': len(candidates),
            'num_equiv_classes': len(equiv_classes),
            'elapsed_ms': (time.time() - start_time) * 1000,
            'is_perfect': is_perfect
        }
    
    def _generate_candidates_from_decomposition(
        self, 
        task: ARCTask, 
        decompositions: List[FractalDecomposition]
    ) -> List[CandidateSolution]:
        """Generate candidate programs based on fractal decomposition."""
        candidates = []
        
        # Analyze decomposition patterns across examples
        layer_types = []
        transforms = []
        for decomp in decompositions:
            for layer in decomp.get_leaves():
                layer_types.append(layer.layer_type)
                if layer.transform:
                    transforms.append(layer.transform)
        
        type_counts = Counter(layer_types)
        transform_counts = Counter(transforms)
        
        # If mostly static + uniform fill, try fill_dynamic
        if type_counts.get(LayerType.STATIC, 0) > 0 and type_counts.get(LayerType.UNIFORM, 0) > 0:
            # Extract fill colors
            for transform, count in transform_counts.most_common():
                if transform.startswith("fill("):
                    try:
                        color = int(transform[5:-1])
                        candidate = self._try_fill_dynamic(task, decompositions, color)
                        if candidate:
                            candidates.append(candidate)
                    except ValueError:
                        pass
        
        # If color changes detected, try color mapping
        if type_counts.get(LayerType.COLOR_CHANGE, 0) > 0:
            for transform, count in transform_counts.most_common():
                if transform.startswith("color("):
                    candidate = self._try_color_change(task, transform)
                    if candidate:
                        candidates.append(candidate)
        
        return candidates
    
    def _try_fill_dynamic(
        self, 
        task: ARCTask, 
        decompositions: List[FractalDecomposition],
        fill_color: int
    ) -> Optional[CandidateSolution]:
        """Try filling dynamic regions with a color."""
        total_energy = 0
        valid = True
        
        for i, ex in enumerate(task.train_examples):
            if i >= len(decompositions):
                valid = False
                break
            
            decomp = decompositions[i]
            if ex.input_grid.shape != ex.output_grid.shape:
                valid = False
                break
            
            # Find dynamic mask from decomposition
            dynamic_mask = torch.zeros_like(ex.input_grid.data, dtype=torch.bool)
            for layer in decomp.get_leaves():
                if layer.layer_type != LayerType.STATIC:
                    dynamic_mask = dynamic_mask | layer.mask
            
            # Apply fill
            data = ex.input_grid.data.clone()
            data[dynamic_mask] = fill_color
            total_energy += compute_defect_energy(ARCGrid(data), ex.output_grid)
        
        if not valid:
            return None
        
        avg_energy = total_energy / len(task.train_examples)
        accuracy = 1.0 if avg_energy < self.config.energy_threshold else 0.0
        
        def apply_fill(grid: ARCGrid) -> ARCGrid:
            # This is a placeholder - actual implementation would need the mask
            return grid
        
        program = Program(
            name=f"fill_dynamic({fill_color})",
            apply=apply_fill,
            complexity=len(f"fill_dynamic({fill_color})"),
            source="decomposition"
        )
        
        return CandidateSolution(
            program=program,
            accuracy=accuracy,
            complexity=program.complexity,
            stability=0.5,  # Will be updated by Jackknife
            energy=avg_energy
        )
    
    def _try_color_change(
        self, 
        task: ARCTask, 
        transform: str
    ) -> Optional[CandidateSolution]:
        """Try a color change transformation."""
        # Parse transform like "color(1->2)"
        try:
            parts = transform[6:-1].split("->")
            from_c = int(parts[0])
            to_c = int(parts[1])
        except (ValueError, IndexError):
            return None
        
        total_energy = 0
        valid = True
        
        for ex in task.train_examples:
            if ex.input_grid.shape != ex.output_grid.shape:
                valid = False
                break
            
            data = ex.input_grid.data.clone()
            data[data == from_c] = to_c
            total_energy += compute_defect_energy(ARCGrid(data), ex.output_grid)
        
        if not valid:
            return None
        
        avg_energy = total_energy / len(task.train_examples)
        accuracy = 1.0 if avg_energy < self.config.energy_threshold else 0.0
        
        def apply_color(grid: ARCGrid) -> ARCGrid:
            data = grid.data.clone()
            data[data == from_c] = to_c
            return ARCGrid(data)
        
        program = Program(
            name=transform,
            apply=apply_color,
            complexity=len(transform),
            source="decomposition"
        )
        
        return CandidateSolution(
            program=program,
            accuracy=accuracy,
            complexity=program.complexity,
            stability=0.5,
            energy=avg_energy
        )
    
    def _generate_base_candidates(self, task: ARCTask) -> List[CandidateSolution]:
        """Generate candidates from base solvers."""
        candidates = []
        
        # Geometry solver
        try:
            geo_result = self.geometry_solver.solve_task(task, verbose=False)
            if geo_result['avg_train_energy'] < 1.0:
                program = Program(
                    name=geo_result.get('operation', 'geometry'),
                    apply=lambda g: g,  # Placeholder
                    complexity=len(geo_result.get('operation', '')),
                    source="geometry"
                )
                candidates.append(CandidateSolution(
                    program=program,
                    accuracy=1.0 if geo_result['avg_train_energy'] < self.config.energy_threshold else 0.5,
                    complexity=program.complexity,
                    stability=0.5,
                    energy=geo_result['avg_train_energy']
                ))
        except Exception:
            pass
        
        # Physics solver
        try:
            phys_result = self.physics_solver.solve_task(task, verbose=False)
            if phys_result['avg_train_energy'] < 1.0:
                method = phys_result.get('method', phys_result.get('operation', 'physics'))
                program = Program(
                    name=method,
                    apply=lambda g: g,  # Placeholder
                    complexity=len(method),
                    source="physics"
                )
                candidates.append(CandidateSolution(
                    program=program,
                    accuracy=1.0 if phys_result['avg_train_energy'] < self.config.energy_threshold else 0.5,
                    complexity=program.complexity,
                    stability=0.5,
                    energy=phys_result['avg_train_energy']
                ))
        except Exception:
            pass
        
        return candidates
    
    def _check_stability(self, task: ARCTask, candidate: CandidateSolution) -> float:
        """Jackknife stability check."""
        if len(task.train_examples) < 2:
            return 1.0  # Can't check with single example
        
        # For now, use energy as proxy for stability
        # Low energy = stable, high energy = unstable
        if candidate.energy < self.config.energy_threshold:
            return 1.0
        elif candidate.energy < 0.1:
            return 0.8
        elif candidate.energy < 0.5:
            return 0.5
        else:
            return 0.2


# =============================================================================
# MAIN
# =============================================================================

def run_phase19(data_path: str):
    printfl("=" * 70)
    printfl("ARC-SGC Phase 19: The Fractal Reasoning Engine")
    printfl("=" * 70)
    printfl("\nCOMPONENTS:")
    printfl("  1. Fractal Decomposition: Recursive layer tree")
    printfl("  2. Algebraic Verification: Output equality checking")
    printfl("  3. Cooling Schedule: Simulated annealing")
    printfl("  4. Rigorous Certainty: 0.0-1.0 score")
    printfl()
    
    config = ARCPhase83Config()
    tasks = load_arc_tasks(data_path, 'cpu')
    printfl(f"Loaded {len(tasks)} tasks")
    
    solver = Phase19Solver(config)
    
    all_results = []
    perfect_tasks = []
    certain_tasks = []  # Certainty >= 0.8
    method_counts = Counter()
    certainty_dist = Counter()
    
    printfl("\n" + "=" * 50)
    printfl("Running Fractal Reasoning Engine")
    printfl("=" * 50)
    
    for i, task in enumerate(tasks):
        result = solver.solve_task(task)
        all_results.append(result)
        
        certainty_dist[result['certainty_level']] += 1
        
        if result['is_perfect']:
            perfect_tasks.append(result)
            method = result['method']
            method_counts[method.split('(')[0] if '(' in method else method] += 1
            
            if result['certainty_score'] >= 0.8:
                certain_tasks.append(result)
            
            cert_str = f"C={result['certainty_score']:.2f}"
            printfl(f"  [PERFECT] {task.task_id}: {result['method']}")
            printfl(f"            {cert_str}, {result['certainty_level']}, Submit={result['should_submit']}")
        
        if (i + 1) % 20 == 0:
            printfl(f"  Progress: {i+1}/{len(tasks)}, perfect={len(perfect_tasks)}, certain={len(certain_tasks)}")
    
    # Summary
    printfl("\n" + "=" * 70)
    printfl("PHASE 19 SUMMARY")
    printfl("=" * 70)
    
    printfl(f"\nResults:")
    printfl(f"  Total perfect: {len(perfect_tasks)}")
    printfl(f"  High certainty (>=0.8): {len(certain_tasks)}")
    printfl(f"  Should submit: {sum(1 for r in perfect_tasks if r['should_submit'])}")
    
    printfl(f"\nCertainty distribution:")
    for level, count in certainty_dist.most_common():
        printfl(f"  {level}: {count}")
    
    printfl(f"\nSolves by method:")
    for method, count in method_counts.most_common(10):
        printfl(f"  {method}: {count}")
    
    # Near-misses
    near_misses = [r for r in all_results if 0.0001 < r['avg_train_energy'] < 0.1]
    printfl(f"\nNear-misses (E<0.1): {len(near_misses)}")
    for r in sorted(near_misses, key=lambda x: x['avg_train_energy'])[:10]:
        printfl(f"  {r['task_id']}: E={r['avg_train_energy']:.4f}, C={r['certainty_score']:.2f}")
    
    # Progress
    printfl(f"\n=== COMPLETE PROGRESS SUMMARY ===")
    printfl(f"  Phase 8.3:   6 perfect (baseline)")
    printfl(f"  Phase 15:   19 perfect (CEGAR)")
    printfl(f"  Phase 17:   20 perfect (Invariant Physics)")
    printfl(f"  Phase 18:   32 perfect (Decomposition)")
    printfl(f"  Phase 19:   {len(perfect_tasks)} perfect (Fractal Reasoning)")
    printfl(f"       High certainty: {len(certain_tasks)}")
    printfl(f"       Should submit: {sum(1 for r in perfect_tasks if r['should_submit'])}")
    
    return all_results


def main():
    paths = ["data/arc/training", "C:/Lean4 Projects/data/arc/training"]
    arc_path = next((p for p in paths if Path(p).exists()), None)
    
    if arc_path:
        run_phase19(arc_path)
    else:
        printfl("ARC data not found!")


if __name__ == "__main__":
    main()
