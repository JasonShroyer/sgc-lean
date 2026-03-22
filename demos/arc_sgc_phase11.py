"""
ARC-SGC Phase 11: Phenotype Registry & Concept Sheaf

THEORETICAL FOUNDATION:
Move from "Supervised Learning of Physics" to "Unsupervised Discovery of Physics".
Instead of hard-coded labels (movement, color, topology), use emergent SIGNATURES.

THE CONCEPT SHEAF:
Every transformation has a "Type Signature" in the Sheaf Category:
    Symbol(L) = ⟨ΔM, ΔC, ΔS, T ⟩

    ΔM (Mass):     0=Conserved, +=Increases, -=Decreases, *=Multiplies
    ΔC (Color):    ID=Identity, PERM=Permutation, NEW=New colors, MONO=Collapse
    ΔS (Symmetry): INV=Invariant, BROK=Broken, SYMM=Created
    T (Topology):  Euler characteristic change, Connectivity preservation

WHY THIS IS ELEGANT:
1. Human-Readable: You can decode "Mass:+, Sym:BROK" = "Something grew asymmetrically"
2. Universal: Applies to ANY grid transformation
3. Collisions are Good: Similar operations cluster together (same physical class)
4. SGC Aligned: Constructs the Cohomology Group of the task space

THE REGISTRY:
    Signature → List[Prototype Operators]
    
When a new task appears:
1. Compute REQUIRED signature from training pairs (must be consistent)
2. Retrieve candidate operators matching that signature
3. Execute candidates with verification

This is ZERO-SHOT GENERALIZATION: If a task requires "Mass Conserved, Symmetry Broken",
predict that signature and retrieve "Gravity" even if never seen in this context.
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
from dataclasses import dataclass, field
from typing import List, Tuple, Dict, Optional, Set, NamedTuple
from collections import Counter, defaultdict
from enum import Enum, auto
import numpy as np
import json
from pathlib import Path
import sys
import time

sys.path.insert(0, str(Path(__file__).parent))
from arc_sgc_phase8_3 import (
    ARCPhase83Config, ARCGrid, ARCObject, ARCExample, ARCTask,
    load_arc_tasks, detect_objects, compute_defect_energy,
    GeometryFirstSolver, ContentSolver,
    IdentityMorphism, CropToContentMorphism, ExtractObjectMorphism,
    ScaleMorphism, DownscaleMorphism,
    CompositePotential, relax_all_colors,
    V_BoundaryDist, V_TopEdge, V_BottomEdge, V_ContactDist
)

def printfl(*args, **kwargs):
    print(*args, **kwargs)
    sys.stdout.flush()


# =============================================================================
# PHENOTYPE SIGNATURE (The "Type as Symbol" System)
# =============================================================================

class MassChange(Enum):
    """How does the total non-background mass change?"""
    CONSERVED = 0      # Same number of colored pixels
    INCREASED = 1      # More colored pixels
    DECREASED = 2      # Fewer colored pixels
    SCALED = 3         # Multiplied/divided by integer factor


class ColorChange(Enum):
    """How does the color distribution change?"""
    IDENTITY = 0       # Same colors in same proportions
    PERMUTATION = 1    # Colors swapped/remapped
    NEW_COLORS = 2     # Colors appear that weren't in input
    COLLAPSED = 3      # Fewer unique colors in output


class SymmetryChange(Enum):
    """How does the symmetry structure change?"""
    INVARIANT = 0      # Symmetry preserved
    BROKEN = 1         # Symmetry reduced (e.g., vertical reflection lost)
    CREATED = 2        # New symmetry added


class TopologyChange(Enum):
    """How does the topological structure change?"""
    PRESERVED = 0      # Same number of connected components
    MERGED = 1         # Components merged (fewer objects)
    SPLIT = 2          # Components split (more objects)
    EULER_CHANGED = 3  # Holes filled or created


@dataclass(frozen=True)
class PhenotypeSignature:
    """
    The SGC Signature of a transformation.
    This is the "Symbol" in the Concept Sheaf.
    
    Immutable and hashable for use as dictionary key.
    """
    mass: MassChange
    color: ColorChange
    symmetry: SymmetryChange
    topology: TopologyChange
    
    # Additional properties for finer discrimination
    shape_preserved: bool = True      # Same grid dimensions?
    object_count_delta: int = 0       # Change in number of objects
    
    def __str__(self):
        return (f"<M:{self.mass.name}, C:{self.color.name}, "
                f"S:{self.symmetry.name}, T:{self.topology.name}>")
    
    def to_tuple(self) -> Tuple:
        """Convert to tuple for hashing/comparison."""
        return (self.mass.value, self.color.value, 
                self.symmetry.value, self.topology.value,
                self.shape_preserved, self.object_count_delta)
    
    def to_vector(self) -> np.ndarray:
        """Convert to numeric vector for neural network."""
        return np.array([
            self.mass.value / 3.0,
            self.color.value / 3.0,
            self.symmetry.value / 2.0,
            self.topology.value / 3.0,
            1.0 if self.shape_preserved else 0.0,
            np.clip(self.object_count_delta / 10.0, -1.0, 1.0)
        ], dtype=np.float32)
    
    @classmethod
    def from_vector(cls, v: np.ndarray) -> 'PhenotypeSignature':
        """Reconstruct from vector (with rounding)."""
        return cls(
            mass=MassChange(int(round(v[0] * 3))),
            color=ColorChange(int(round(v[1] * 3))),
            symmetry=SymmetryChange(int(round(v[2] * 2))),
            topology=TopologyChange(int(round(v[3] * 3))),
            shape_preserved=v[4] > 0.5,
            object_count_delta=int(round(v[5] * 10))
        )


class SignatureComputer:
    """Computes the Phenotype Signature from input/output grids."""
    
    def __init__(self, config: ARCPhase83Config):
        self.config = config
    
    def compute(self, input_grid: ARCGrid, output_grid: ARCGrid) -> PhenotypeSignature:
        """Compute the signature of the transformation input → output."""
        
        # Mass analysis
        mass_change = self._analyze_mass(input_grid, output_grid)
        
        # Color analysis
        color_change = self._analyze_color(input_grid, output_grid)
        
        # Symmetry analysis
        symmetry_change = self._analyze_symmetry(input_grid, output_grid)
        
        # Topology analysis
        topology_change, obj_delta = self._analyze_topology(input_grid, output_grid)
        
        # Shape preserved?
        shape_preserved = input_grid.shape == output_grid.shape
        
        return PhenotypeSignature(
            mass=mass_change,
            color=color_change,
            symmetry=symmetry_change,
            topology=topology_change,
            shape_preserved=shape_preserved,
            object_count_delta=obj_delta
        )
    
    def _analyze_mass(self, inp: ARCGrid, out: ARCGrid) -> MassChange:
        """Analyze how the total mass (non-background pixels) changes."""
        in_mass = (inp.data != self.config.background_color).sum().item()
        out_mass = (out.data != self.config.background_color).sum().item()
        
        if in_mass == 0:
            return MassChange.INCREASED if out_mass > 0 else MassChange.CONSERVED
        
        ratio = out_mass / in_mass
        
        if 0.95 <= ratio <= 1.05:
            return MassChange.CONSERVED
        elif ratio > 1.05:
            # Check if it's a scale factor
            if abs(ratio - 4) < 0.1 or abs(ratio - 9) < 0.1:
                return MassChange.SCALED
            return MassChange.INCREASED
        else:
            if abs(ratio - 0.25) < 0.1 or abs(ratio - 0.11) < 0.1:
                return MassChange.SCALED
            return MassChange.DECREASED
    
    def _analyze_color(self, inp: ARCGrid, out: ARCGrid) -> ColorChange:
        """Analyze how the color distribution changes."""
        in_colors = set(inp.data.unique().tolist()) - {self.config.background_color}
        out_colors = set(out.data.unique().tolist()) - {self.config.background_color}
        
        if not in_colors and not out_colors:
            return ColorChange.IDENTITY
        
        # New colors appeared?
        new_colors = out_colors - in_colors
        if new_colors:
            return ColorChange.NEW_COLORS
        
        # Colors collapsed?
        if len(out_colors) < len(in_colors):
            return ColorChange.COLLAPSED
        
        # Check for permutation
        if in_colors == out_colors:
            # Same colors - check if distribution changed
            in_hist = Counter(inp.data.flatten().tolist())
            out_hist = Counter(out.data.flatten().tolist())
            
            # Remove background
            in_hist.pop(self.config.background_color, None)
            out_hist.pop(self.config.background_color, None)
            
            # Check if it's a permutation (same counts, different colors)
            if sorted(in_hist.values()) == sorted(out_hist.values()):
                if in_hist != out_hist:
                    return ColorChange.PERMUTATION
            return ColorChange.IDENTITY
        
        return ColorChange.PERMUTATION
    
    def _analyze_symmetry(self, inp: ARCGrid, out: ARCGrid) -> SymmetryChange:
        """Analyze how symmetry changes."""
        in_sym = self._detect_symmetries(inp)
        out_sym = self._detect_symmetries(out)
        
        if out_sym > in_sym:
            return SymmetryChange.CREATED
        elif out_sym < in_sym:
            return SymmetryChange.BROKEN
        return SymmetryChange.INVARIANT
    
    def _detect_symmetries(self, grid: ARCGrid) -> int:
        """Count number of symmetries (higher = more symmetric)."""
        data = grid.data
        score = 0
        
        # Horizontal reflection
        if torch.equal(data, data.flip(1)):
            score += 1
        
        # Vertical reflection
        if torch.equal(data, data.flip(0)):
            score += 1
        
        # 180° rotation
        if data.shape[0] == data.shape[1]:
            if torch.equal(data, data.rot90(2, [0, 1])):
                score += 1
        
        return score
    
    def _analyze_topology(self, inp: ARCGrid, out: ARCGrid) -> Tuple[TopologyChange, int]:
        """Analyze topological changes (connected components)."""
        in_objects = detect_objects(inp, self.config)
        out_objects = detect_objects(out, self.config)
        
        in_count = len(in_objects)
        out_count = len(out_objects)
        delta = out_count - in_count
        
        if delta == 0:
            return TopologyChange.PRESERVED, 0
        elif delta < 0:
            return TopologyChange.MERGED, delta
        else:
            return TopologyChange.SPLIT, delta


# =============================================================================
# CONCEPT REGISTRY (The "Memetic Memory")
# =============================================================================

@dataclass
class PrototypeOperator:
    """A prototype operator stored in the registry."""
    name: str                    # Human-readable name
    operation_type: str          # geometry, movement, color, pattern, topology
    parameters: Dict             # Any parameters (e.g., color=3)
    solve_count: int = 0         # How many tasks solved with this
    avg_energy: float = 0.0      # Average energy achieved


class ConceptRegistry:
    """
    The Registry maps Signatures → List[Prototype Operators].
    This is the "Memetic Memory" of the system.
    """
    
    def __init__(self):
        self.registry: Dict[PhenotypeSignature, List[PrototypeOperator]] = defaultdict(list)
        self.signature_computer = SignatureComputer(ARCPhase83Config())
    
    def register(self, signature: PhenotypeSignature, operator: PrototypeOperator):
        """Register an operator under its signature."""
        # Check if operator already exists
        for existing in self.registry[signature]:
            if existing.name == operator.name:
                existing.solve_count += 1
                return
        
        self.registry[signature].append(operator)
    
    def lookup(self, signature: PhenotypeSignature) -> List[PrototypeOperator]:
        """Retrieve operators matching a signature."""
        return self.registry.get(signature, [])
    
    def lookup_similar(self, signature: PhenotypeSignature, 
                       max_distance: int = 2) -> List[Tuple[PhenotypeSignature, List[PrototypeOperator]]]:
        """Retrieve operators with similar signatures (for generalization)."""
        results = []
        target = signature.to_tuple()
        
        for sig, ops in self.registry.items():
            # Compute "distance" as number of differing fields
            sig_tuple = sig.to_tuple()
            distance = sum(1 for a, b in zip(target[:4], sig_tuple[:4]) if a != b)
            
            if distance <= max_distance:
                results.append((sig, ops))
        
        # Sort by distance (closest first)
        results.sort(key=lambda x: sum(1 for a, b in zip(target[:4], x[0].to_tuple()[:4]) if a != b))
        return results
    
    def get_all_signatures(self) -> List[PhenotypeSignature]:
        """Get all registered signatures."""
        return list(self.registry.keys())
    
    def summary(self) -> str:
        """Human-readable summary of the registry."""
        lines = ["=== Concept Registry ==="]
        for sig, ops in self.registry.items():
            lines.append(f"\n{sig}")
            for op in ops:
                lines.append(f"  - {op.name} (solved: {op.solve_count})")
        return "\n".join(lines)


# =============================================================================
# SIGNATURE-BASED SOLVER
# =============================================================================

class SignatureBasedSolver:
    """
    Solver that uses Signature-Based Retrieval:
    1. Infer required signature from training examples
    2. Retrieve candidate operators from Registry
    3. Execute candidates with verification
    """
    
    def __init__(self, registry: ConceptRegistry, config: ARCPhase83Config):
        self.registry = registry
        self.config = config
        self.sig_computer = SignatureComputer(config)
        
        # Phase 8.3 executor components
        self.movement_potentials = [V_ContactDist(), V_TopEdge(), V_BottomEdge(), V_BoundaryDist()]
        self.morphisms = [
            IdentityMorphism(),
            CropToContentMorphism(),
            ExtractObjectMorphism('largest'),
            ExtractObjectMorphism('smallest'),
            ScaleMorphism(2),
            DownscaleMorphism(2),
        ]
    
    def infer_required_signature(self, examples: List[ARCExample]) -> Optional[PhenotypeSignature]:
        """
        Infer the CONSISTENT required signature from training examples.
        Returns None if examples have inconsistent signatures.
        """
        if not examples:
            return None
        
        signatures = []
        for ex in examples:
            sig = self.sig_computer.compute(ex.input_grid, ex.output_grid)
            signatures.append(sig)
        
        # Check consistency (all signatures should be the same)
        first = signatures[0]
        for sig in signatures[1:]:
            if sig.to_tuple()[:4] != first.to_tuple()[:4]:  # Core signature must match
                printfl(f"   Inconsistent signatures: {first} vs {sig}")
                return None
        
        return first
    
    def solve_task(self, task: ARCTask, verbose: bool = False) -> Dict:
        """Solve task using signature-based retrieval."""
        start_time = time.time()
        examples = task.train_examples
        
        # Step 1: Infer required signature
        required_sig = self.infer_required_signature(examples)
        
        if verbose:
            printfl(f"\n   Required signature: {required_sig}")
        
        best_energy = float('inf')
        best_morphism = "identity"
        best_method = "identity"
        
        # Step 2: Retrieve candidate operators from registry
        if required_sig:
            candidates = self.registry.lookup(required_sig)
            if verbose and candidates:
                printfl(f"   Retrieved {len(candidates)} candidates from registry")
            
            # Also get similar signatures for generalization
            similar = self.registry.lookup_similar(required_sig, max_distance=2)
            for sig, ops in similar:
                for op in ops:
                    if op not in candidates:
                        candidates.append(op)
        else:
            candidates = []
        
        # Step 3: Try retrieved candidates first (fast path)
        for candidate in candidates:
            energy = self._try_operator(candidate, examples)
            if energy < best_energy:
                best_energy = energy
                best_method = candidate.name
                best_morphism = "identity"
            
            if best_energy < self.config.energy_threshold:
                break
        
        # Step 4: If no perfect solve, fall back to full search
        if best_energy >= self.config.energy_threshold:
            energy, morphism, method = self._full_search(examples)
            if energy < best_energy:
                best_energy = energy
                best_morphism = morphism
                best_method = method
        
        elapsed = time.time() - start_time
        is_perfect = best_energy < self.config.energy_threshold
        
        # Step 5: If solved, register the operator
        if is_perfect and required_sig:
            self.registry.register(required_sig, PrototypeOperator(
                name=f"{best_morphism} + {best_method}",
                operation_type=self._classify_op_type(best_method),
                parameters={},
                solve_count=1
            ))
        
        return {
            'task_id': task.task_id,
            'morphism': best_morphism,
            'method': best_method,
            'operation': f"{best_morphism} + {best_method}",
            'energy': best_energy,
            'elapsed_ms': elapsed * 1000,
            'is_perfect': is_perfect,
            'signature': str(required_sig) if required_sig else "inconsistent"
        }
    
    def _try_operator(self, op: PrototypeOperator, examples: List[ARCExample]) -> float:
        """Try a registered operator on examples."""
        # Parse operator and execute
        name = op.name.lower()
        total_e = 0
        
        for ex in examples:
            result = ex.input_grid.clone()
            
            if 'v_contact' in name:
                weights = np.array([1.0, 0, 0, 0])
                if '-' in name: weights[0] = -1.0
                potential = CompositePotential(self.movement_potentials, weights)
                result = relax_all_colors(ex.input_grid, potential, self.config)
            elif 'v_top' in name:
                weights = np.array([0, 1.0 if '+' in name else -1.0, 0, 0])
                potential = CompositePotential(self.movement_potentials, weights)
                result = relax_all_colors(ex.input_grid, potential, self.config)
            elif 'rot180' in name:
                result = ARCGrid(ex.input_grid.data.rot90(2, [0, 1]))
            elif 'crop' in name:
                from arc_sgc_phase8_3 import CropToContentMorphism
                morph = CropToContentMorphism()
                result = morph.apply(ex.input_grid, self.config)
            elif 'extract' in name:
                selector = 'largest' if 'largest' in name else 'smallest'
                morph = ExtractObjectMorphism(selector)
                result = morph.apply(ex.input_grid, self.config)
            
            total_e += compute_defect_energy(result, ex.output_grid)
        
        return total_e / len(examples)
    
    def _full_search(self, examples: List[ARCExample]) -> Tuple[float, str, str]:
        """Fall back to full search (Phase 8.3 style)."""
        best_energy = float('inf')
        best_morphism = "identity"
        best_method = "identity"
        
        for morphism in self.morphisms:
            # Check consistency
            consistent = True
            for ex in examples:
                try:
                    result = morphism.apply(ex.input_grid, self.config)
                    if result.shape != ex.output_grid.shape:
                        consistent = False
                        break
                except:
                    consistent = False
                    break
            
            if not consistent:
                continue
            
            # Try movement potentials
            for i, pot in enumerate(self.movement_potentials):
                for sign in [-1.0, 1.0]:
                    weights = np.zeros(4)
                    weights[i] = sign
                    potential = CompositePotential(self.movement_potentials, weights)
                    
                    total_e = 0
                    for ex in examples:
                        transformed = morphism.apply(ex.input_grid, self.config)
                        result = relax_all_colors(transformed, potential, self.config)
                        total_e += compute_defect_energy(result, ex.output_grid)
                    
                    avg_e = total_e / len(examples)
                    if avg_e < best_energy:
                        best_energy = avg_e
                        best_morphism = morphism.name()
                        best_method = f"{'+' if sign > 0 else '-'}1.0*{pot.name()}"
            
            # Try pattern ops
            for name, rot in [('rot180', 2), ('rot90', 1)]:
                total_e = 0
                valid = True
                for ex in examples:
                    try:
                        transformed = morphism.apply(ex.input_grid, self.config)
                        result = ARCGrid(transformed.data.rot90(rot, [0, 1]))
                        if result.shape != ex.output_grid.shape:
                            valid = False
                            break
                        total_e += compute_defect_energy(result, ex.output_grid)
                    except:
                        valid = False
                        break
                
                if valid:
                    avg_e = total_e / len(examples)
                    if avg_e < best_energy:
                        best_energy = avg_e
                        best_morphism = morphism.name()
                        best_method = name
            
            # Try color ops
            for from_c in range(1, 6):
                for to_c in range(0, 6):
                    if from_c == to_c:
                        continue
                    total_e = 0
                    for ex in examples:
                        transformed = morphism.apply(ex.input_grid, self.config)
                        data = transformed.data.clone()
                        data[data == from_c] = to_c
                        total_e += compute_defect_energy(ARCGrid(data), ex.output_grid)
                    
                    avg_e = total_e / len(examples)
                    if avg_e < best_energy:
                        best_energy = avg_e
                        best_morphism = morphism.name()
                        best_method = f"color_map({from_c}->{to_c})"
            
            # Try identity
            total_e = 0
            for ex in examples:
                transformed = morphism.apply(ex.input_grid, self.config)
                total_e += compute_defect_energy(transformed, ex.output_grid)
            avg_e = total_e / len(examples)
            if avg_e < best_energy:
                best_energy = avg_e
                best_morphism = morphism.name()
                best_method = "identity"
        
        return best_energy, best_morphism, best_method
    
    def _classify_op_type(self, method: str) -> str:
        m = method.lower()
        if 'v_' in m or 'contact' in m or 'top' in m:
            return 'movement'
        if 'color' in m or 'map' in m:
            return 'color'
        if 'rot' in m or 'flip' in m:
            return 'pattern'
        if 'crop' in m or 'extract' in m:
            return 'geometry'
        return 'other'


# =============================================================================
# EVALUATION
# =============================================================================

def run_phase11(data_path: str):
    printfl("=" * 70)
    printfl("ARC-SGC Phase 11: Phenotype Registry & Concept Sheaf")
    printfl("=" * 70)
    
    config = ARCPhase83Config()
    tasks = load_arc_tasks(data_path, 'cpu')
    printfl(f"\nLoaded {len(tasks)} tasks")
    
    # Initialize empty registry
    registry = ConceptRegistry()
    solver = SignatureBasedSolver(registry, config)
    
    # Phase 1: Bootstrap registry with known solves
    printfl("\n" + "=" * 50)
    printfl("PHASE 1: Bootstrap Registry")
    printfl("=" * 50)
    
    all_results = []
    perfect_tasks = []
    signature_stats = Counter()
    
    for i, task in enumerate(tasks):
        result = solver.solve_task(task, verbose=False)
        all_results.append(result)
        
        if result['is_perfect']:
            perfect_tasks.append(result)
            printfl(f"  [PERFECT] {task.task_id}: {result['operation']}")
            printfl(f"            Signature: {result['signature']}")
        
        signature_stats[result['signature']] += 1
        
        if (i + 1) % 20 == 0:
            printfl(f"  Progress: {i+1}/{len(tasks)}, perfect={len(perfect_tasks)}")
    
    # Summary
    printfl("\n" + "=" * 70)
    printfl("PHASE 11 SUMMARY")
    printfl("=" * 70)
    
    printfl(f"\nResults:")
    printfl(f"  Perfect solves: {len(perfect_tasks)}")
    printfl(f"  Registry size: {len(registry.get_all_signatures())} signatures")
    
    printfl(f"\n=== Registry Contents ===")
    printfl(registry.summary())
    
    printfl(f"\n=== Signature Distribution ===")
    for sig, count in signature_stats.most_common(10):
        printfl(f"  {sig}: {count} tasks")
    
    printfl(f"\n=== Perfect Solves by Signature ===")
    sig_perfect = defaultdict(list)
    for r in perfect_tasks:
        sig_perfect[r['signature']].append(r['task_id'])
    
    for sig, tasks_list in sig_perfect.items():
        printfl(f"\n  {sig}")
        for t in tasks_list:
            r = next(x for x in perfect_tasks if x['task_id'] == t)
            printfl(f"    {t}: {r['operation']}")
    
    return all_results, registry


def main():
    paths = ["data/arc/training", "C:/Lean4 Projects/data/arc/training"]
    arc_path = next((p for p in paths if Path(p).exists()), None)
    
    if arc_path:
        run_phase11(arc_path)
    else:
        printfl("ARC data not found!")


if __name__ == "__main__":
    main()
