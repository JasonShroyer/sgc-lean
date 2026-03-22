"""
ARC-SGC Phase 11b: Object-Centric Sheaf & Conditional Physics

THEORETICAL INSIGHT:
Phase 11 found 28% of tasks have "inconsistent" global signatures.
This means the transformation is NOT a simple Grid->Grid functor.

Instead, it's a NATURAL TRANSFORMATION on the OBJECT CATEGORY:
- Global View: "The grid changed in a weird, variable way" (Inconsistent)
- Local View: "Every RED object grew by 1 pixel" (Consistent!)

The invariance is at the OBJECT CLASS level, not the Grid level.

ARCHITECTURE:
1. Object Matching: Pair input/output objects by IoU or Color
2. Per-Object Signatures: Sig(obj_in, obj_out) for each matched pair
3. Invariant Discovery: Find what Discriminator defines consistent subsets
4. Conditional Registry: (Discriminator, Signature) -> Operator

This moves from UNIVERSAL LAWS to SPECIFIC RULES:
- Universal: "Gravity affects everything"
- Specific: "Only blue objects grow; red objects stay fixed"

PROGRAM SYNTHESIS:
If Blue objects -> <M:EXPAND> and Red objects -> <M:CONST>,
synthesize:
    solve(grid) = merge(expand(blue_objs), identity(red_objs))
"""

import torch
import torch.nn as nn
from dataclasses import dataclass, field
from typing import List, Tuple, Dict, Optional, Set, NamedTuple
from collections import Counter, defaultdict
from enum import Enum, auto
import numpy as np
from pathlib import Path
import sys
import time
from scipy.optimize import linear_sum_assignment

sys.path.insert(0, str(Path(__file__).parent))
from arc_sgc_phase8_3 import (
    ARCPhase83Config, ARCGrid, ARCObject, ARCExample, ARCTask,
    load_arc_tasks, detect_objects, compute_defect_energy,
    GeometryFirstSolver
)
from arc_sgc_phase11 import (
    MassChange, ColorChange, SymmetryChange, TopologyChange,
    PhenotypeSignature, SignatureComputer
)

def printfl(*args, **kwargs):
    print(*args, **kwargs)
    sys.stdout.flush()


# =============================================================================
# OBJECT-LEVEL SIGNATURES
# =============================================================================

@dataclass
class ObjectSignature:
    """Signature of a single object's transformation."""
    mass_change: str       # 'grew', 'shrank', 'same', 'disappeared', 'appeared'
    color_change: str      # 'same', 'changed', 'new'
    position_change: str   # 'same', 'moved', 'merged', 'split'
    shape_change: str      # 'same', 'rotated', 'scaled', 'deformed'
    
    def __str__(self):
        return f"<mass:{self.mass_change}, color:{self.color_change}, pos:{self.position_change}, shape:{self.shape_change}>"
    
    def to_tuple(self):
        return (self.mass_change, self.color_change, self.position_change, self.shape_change)


@dataclass
class ObjectProperties:
    """Properties of an object used for matching and discrimination."""
    color: int
    mass: int              # Number of pixels
    centroid: Tuple[float, float]
    bbox: Tuple[int, int, int, int]  # r1, c1, r2, c2
    is_enclosed: bool = False
    is_on_edge: bool = False
    aspect_ratio: float = 1.0
    
    def __str__(self):
        return f"[c={self.color}, m={self.mass}, pos=({self.centroid[0]:.1f},{self.centroid[1]:.1f})]"


@dataclass
class MatchedObjectPair:
    """A matched pair of input/output objects."""
    input_obj: Optional[ObjectProperties]
    output_obj: Optional[ObjectProperties]
    signature: ObjectSignature
    iou: float = 0.0


# =============================================================================
# OBJECT MATCHING
# =============================================================================

class ObjectMatcher:
    """Match input objects to output objects using IoU and color."""
    
    def __init__(self, config: ARCPhase83Config):
        self.config = config
    
    def extract_object_properties(self, grid: ARCGrid) -> List[ObjectProperties]:
        """Extract properties for all objects in grid."""
        objects = detect_objects(grid, self.config)
        props = []
        
        H, W = grid.shape
        
        for obj in objects:
            pixels = obj.pixels
            rows = [p[0] for p in pixels]
            cols = [p[1] for p in pixels]
            
            r1, r2 = min(rows), max(rows) + 1
            c1, c2 = min(cols), max(cols) + 1
            
            centroid = (sum(rows) / len(rows), sum(cols) / len(cols))
            
            # Check if on edge
            is_on_edge = r1 == 0 or c1 == 0 or r2 == H or c2 == W
            
            # Aspect ratio
            height = r2 - r1
            width = c2 - c1
            aspect_ratio = height / width if width > 0 else 1.0
            
            props.append(ObjectProperties(
                color=obj.color,
                mass=len(pixels),
                centroid=centroid,
                bbox=(r1, c1, r2, c2),
                is_on_edge=is_on_edge,
                aspect_ratio=aspect_ratio
            ))
        
        return props
    
    def compute_iou(self, obj1: ObjectProperties, obj2: ObjectProperties) -> float:
        """Compute IoU between two objects based on bounding boxes."""
        r1_1, c1_1, r2_1, c2_1 = obj1.bbox
        r1_2, c1_2, r2_2, c2_2 = obj2.bbox
        
        # Intersection
        r1_i = max(r1_1, r1_2)
        c1_i = max(c1_1, c1_2)
        r2_i = min(r2_1, r2_2)
        c2_i = min(c2_1, c2_2)
        
        if r2_i <= r1_i or c2_i <= c1_i:
            return 0.0
        
        intersection = (r2_i - r1_i) * (c2_i - c1_i)
        
        # Union
        area1 = (r2_1 - r1_1) * (c2_1 - c1_1)
        area2 = (r2_2 - r1_2) * (c2_2 - c1_2)
        union = area1 + area2 - intersection
        
        return intersection / union if union > 0 else 0.0
    
    def match_objects(self, input_props: List[ObjectProperties], 
                      output_props: List[ObjectProperties]) -> List[MatchedObjectPair]:
        """Match input to output objects using Hungarian algorithm."""
        
        if not input_props and not output_props:
            return []
        
        # Handle edge cases
        if not input_props:
            # All objects are new (appeared)
            return [MatchedObjectPair(
                input_obj=None,
                output_obj=out_obj,
                signature=ObjectSignature('appeared', 'new', 'appeared', 'new'),
                iou=0.0
            ) for out_obj in output_props]
        
        if not output_props:
            # All objects disappeared
            return [MatchedObjectPair(
                input_obj=in_obj,
                output_obj=None,
                signature=ObjectSignature('disappeared', 'gone', 'gone', 'gone'),
                iou=0.0
            ) for in_obj in input_props]
        
        # Build cost matrix (negative IoU + color penalty)
        n_in = len(input_props)
        n_out = len(output_props)
        
        # Pad to make square
        n = max(n_in, n_out)
        cost_matrix = np.ones((n, n)) * 1000  # High cost for unmatched
        
        for i, in_obj in enumerate(input_props):
            for j, out_obj in enumerate(output_props):
                iou = self.compute_iou(in_obj, out_obj)
                color_match = 1.0 if in_obj.color == out_obj.color else 0.5
                cost_matrix[i, j] = -iou * color_match
        
        # Hungarian algorithm
        row_ind, col_ind = linear_sum_assignment(cost_matrix)
        
        matched_pairs = []
        matched_inputs = set()
        matched_outputs = set()
        
        for i, j in zip(row_ind, col_ind):
            if i < n_in and j < n_out:
                in_obj = input_props[i]
                out_obj = output_props[j]
                iou = self.compute_iou(in_obj, out_obj)
                
                if iou > 0.1 or in_obj.color == out_obj.color:
                    sig = self._compute_object_signature(in_obj, out_obj)
                    matched_pairs.append(MatchedObjectPair(
                        input_obj=in_obj,
                        output_obj=out_obj,
                        signature=sig,
                        iou=iou
                    ))
                    matched_inputs.add(i)
                    matched_outputs.add(j)
        
        # Handle unmatched inputs (disappeared)
        for i, in_obj in enumerate(input_props):
            if i not in matched_inputs:
                matched_pairs.append(MatchedObjectPair(
                    input_obj=in_obj,
                    output_obj=None,
                    signature=ObjectSignature('disappeared', 'gone', 'gone', 'gone'),
                    iou=0.0
                ))
        
        # Handle unmatched outputs (appeared)
        for j, out_obj in enumerate(output_props):
            if j not in matched_outputs:
                matched_pairs.append(MatchedObjectPair(
                    input_obj=None,
                    output_obj=out_obj,
                    signature=ObjectSignature('appeared', 'new', 'appeared', 'new'),
                    iou=0.0
                ))
        
        return matched_pairs
    
    def _compute_object_signature(self, in_obj: ObjectProperties, 
                                   out_obj: ObjectProperties) -> ObjectSignature:
        """Compute the signature of a single object transformation."""
        
        # Mass change
        mass_ratio = out_obj.mass / in_obj.mass if in_obj.mass > 0 else float('inf')
        if 0.9 <= mass_ratio <= 1.1:
            mass_change = 'same'
        elif mass_ratio > 1.1:
            mass_change = 'grew'
        else:
            mass_change = 'shrank'
        
        # Color change
        if in_obj.color == out_obj.color:
            color_change = 'same'
        else:
            color_change = 'changed'
        
        # Position change
        dist = ((in_obj.centroid[0] - out_obj.centroid[0])**2 + 
                (in_obj.centroid[1] - out_obj.centroid[1])**2) ** 0.5
        if dist < 0.5:
            position_change = 'same'
        else:
            position_change = 'moved'
        
        # Shape change (simplified)
        ar_ratio = out_obj.aspect_ratio / in_obj.aspect_ratio if in_obj.aspect_ratio > 0 else 1.0
        if 0.8 <= ar_ratio <= 1.2 and 0.8 <= mass_ratio <= 1.2:
            shape_change = 'same'
        elif 0.8 <= ar_ratio <= 1.2:
            shape_change = 'scaled'
        else:
            shape_change = 'deformed'
        
        return ObjectSignature(mass_change, color_change, position_change, shape_change)


# =============================================================================
# INVARIANT DISCOVERY (The "Scientist")
# =============================================================================

@dataclass(frozen=True)
class Discriminator:
    """A condition that identifies a subset of objects."""
    property_name: str   # 'color', 'mass', 'is_on_edge', 'aspect_ratio'
    operator: str        # '==', '>', '<', 'in'
    value: int           # The value to compare against (use int for hashability)
    
    def __str__(self):
        return f"{self.property_name} {self.operator} {self.value}"
    
    def matches(self, obj: ObjectProperties) -> bool:
        """Check if object matches this discriminator."""
        val = getattr(obj, self.property_name, None)
        if val is None:
            return False
        
        if self.operator == '==':
            return val == self.value
        elif self.operator == '>':
            return val > self.value
        elif self.operator == '<':
            return val < self.value
        elif self.operator == 'in':
            return val in self.value
        return False


class InvariantDiscoverer:
    """Discover discriminators that define consistent object subsets."""
    
    def __init__(self):
        pass
    
    def discover_invariants(self, matched_pairs: List[MatchedObjectPair]) -> Dict[Discriminator, ObjectSignature]:
        """
        Find discriminators that partition objects into groups with consistent signatures.
        Returns mapping from Discriminator -> shared Signature for that group.
        """
        
        # Filter to pairs with input objects
        pairs_with_input = [p for p in matched_pairs if p.input_obj is not None]
        
        if not pairs_with_input:
            return {}
        
        # Candidate discriminators to try
        colors = list(set(p.input_obj.color for p in pairs_with_input))
        
        candidates = []
        
        # Color-based discriminators
        for c in colors:
            candidates.append(Discriminator('color', '==', c))
        
        # Size-based discriminators
        masses = [p.input_obj.mass for p in pairs_with_input]
        if masses:
            median_mass = sorted(masses)[len(masses) // 2]
            candidates.append(Discriminator('mass', '>', median_mass))
            candidates.append(Discriminator('mass', '<', median_mass))
        
        # Edge-based discriminator
        candidates.append(Discriminator('is_on_edge', '==', True))
        candidates.append(Discriminator('is_on_edge', '==', False))
        
        # Find discriminators that give consistent signatures
        invariants = {}
        
        for disc in candidates:
            matching_pairs = [p for p in pairs_with_input if disc.matches(p.input_obj)]
            
            if len(matching_pairs) < 2:
                continue
            
            # Check if all matching pairs have the same signature
            signatures = [p.signature.to_tuple() for p in matching_pairs]
            if len(set(signatures)) == 1:
                # Consistent!
                invariants[disc] = matching_pairs[0].signature
        
        return invariants
    
    def analyze_task(self, input_grid: ARCGrid, output_grid: ARCGrid, 
                     config: ARCPhase83Config) -> Dict:
        """Full analysis of a single example."""
        
        matcher = ObjectMatcher(config)
        
        in_props = matcher.extract_object_properties(input_grid)
        out_props = matcher.extract_object_properties(output_grid)
        
        matched = matcher.match_objects(in_props, out_props)
        invariants = self.discover_invariants(matched)
        
        return {
            'input_objects': len(in_props),
            'output_objects': len(out_props),
            'matched_pairs': len(matched),
            'invariants': invariants,
            'all_signatures': [p.signature for p in matched]
        }


# =============================================================================
# CONDITIONAL REGISTRY
# =============================================================================

@dataclass
class ConditionalOperator:
    """An operator with its condition (discriminator)."""
    discriminator: Optional[Discriminator]
    signature: ObjectSignature
    operator_name: str
    solve_count: int = 0


class ConditionalRegistry:
    """
    Registry with (Discriminator, Signature) -> Operator mapping.
    Supports conditional physics: "Only blue objects get this treatment."
    """
    
    def __init__(self):
        # Key: (discriminator_str, signature_tuple) -> List[operator_name]
        self.registry: Dict[Tuple, List[ConditionalOperator]] = defaultdict(list)
    
    def register(self, discriminator: Optional[Discriminator], 
                 signature: ObjectSignature, operator_name: str):
        disc_str = str(discriminator) if discriminator else "ALL"
        key = (disc_str, signature.to_tuple())
        
        # Check if already exists
        for op in self.registry[key]:
            if op.operator_name == operator_name:
                op.solve_count += 1
                return
        
        self.registry[key].append(ConditionalOperator(
            discriminator=discriminator,
            signature=signature,
            operator_name=operator_name,
            solve_count=1
        ))
    
    def lookup(self, discriminator: Optional[Discriminator], 
               signature: ObjectSignature) -> List[ConditionalOperator]:
        disc_str = str(discriminator) if discriminator else "ALL"
        key = (disc_str, signature.to_tuple())
        return self.registry.get(key, [])
    
    def summary(self) -> str:
        lines = ["=== Conditional Registry ==="]
        for key, ops in self.registry.items():
            disc_str, sig_tuple = key
            lines.append(f"\n  Condition: {disc_str}")
            lines.append(f"  Signature: {sig_tuple}")
            for op in ops:
                lines.append(f"    -> {op.operator_name} (solved: {op.solve_count})")
        return "\n".join(lines)


# =============================================================================
# EVALUATION
# =============================================================================

def analyze_inconsistent_tasks(tasks: List[ARCTask], config: ARCPhase83Config):
    """Deep analysis of tasks with inconsistent global signatures."""
    
    global_sig_computer = SignatureComputer(config)
    discoverer = InvariantDiscoverer()
    matcher = ObjectMatcher(config)
    
    results = {
        'consistent_global': [],
        'consistent_conditional': [],
        'truly_inconsistent': []
    }
    
    for task in tasks:
        examples = task.train_examples
        
        # Check global consistency
        global_sigs = []
        for ex in examples:
            sig = global_sig_computer.compute(ex.input_grid, ex.output_grid)
            global_sigs.append(sig.to_tuple()[:4])
        
        if len(set(global_sigs)) == 1:
            results['consistent_global'].append(task.task_id)
            continue
        
        # Check conditional consistency
        all_invariants = []
        for ex in examples:
            analysis = discoverer.analyze_task(ex.input_grid, ex.output_grid, config)
            all_invariants.append(analysis['invariants'])
        
        # Find invariants that appear in ALL examples
        if all_invariants:
            common_discriminators = set(all_invariants[0].keys())
            for inv in all_invariants[1:]:
                common_discriminators &= set(inv.keys())
            
            if common_discriminators:
                # Found consistent conditional invariants!
                results['consistent_conditional'].append({
                    'task_id': task.task_id,
                    'discriminators': [str(d) for d in common_discriminators],
                    'invariants': {str(d): str(all_invariants[0][d]) for d in common_discriminators}
                })
                continue
        
        # Truly inconsistent
        results['truly_inconsistent'].append(task.task_id)
    
    return results


def run_phase11b(data_path: str):
    printfl("=" * 70)
    printfl("ARC-SGC Phase 11b: Object-Centric Sheaf & Conditional Physics")
    printfl("=" * 70)
    
    config = ARCPhase83Config()
    tasks = load_arc_tasks(data_path, 'cpu')
    printfl(f"\nLoaded {len(tasks)} tasks")
    
    # Analyze all tasks
    printfl("\n" + "=" * 50)
    printfl("ANALYSIS: Global vs Conditional Consistency")
    printfl("=" * 50)
    
    results = analyze_inconsistent_tasks(tasks, config)
    
    printfl(f"\n=== Results ===")
    printfl(f"  Consistent Global: {len(results['consistent_global'])} tasks")
    printfl(f"  Consistent Conditional: {len(results['consistent_conditional'])} tasks")
    printfl(f"  Truly Inconsistent: {len(results['truly_inconsistent'])} tasks")
    
    printfl(f"\n=== Conditional Tasks (The Breakthrough) ===")
    for item in results['consistent_conditional'][:10]:
        printfl(f"\n  Task: {item['task_id']}")
        printfl(f"    Discriminators: {item['discriminators']}")
        for disc, sig in item['invariants'].items():
            printfl(f"      {disc} -> {sig}")
    
    # Deep dive on one example
    if results['consistent_conditional']:
        printfl("\n" + "=" * 50)
        printfl("DEEP DIVE: Example Conditional Task")
        printfl("=" * 50)
        
        task_id = results['consistent_conditional'][0]['task_id']
        task = next(t for t in tasks if t.task_id == task_id)
        
        discoverer = InvariantDiscoverer()
        
        for i, ex in enumerate(task.train_examples):
            printfl(f"\n--- Example {i+1} ---")
            analysis = discoverer.analyze_task(ex.input_grid, ex.output_grid, config)
            
            printfl(f"  Input objects: {analysis['input_objects']}")
            printfl(f"  Output objects: {analysis['output_objects']}")
            printfl(f"  Object signatures:")
            for sig in analysis['all_signatures']:
                printfl(f"    {sig}")
            
            printfl(f"  Discovered invariants:")
            for disc, sig in analysis['invariants'].items():
                printfl(f"    {disc} -> {sig}")
    
    # Summary statistics
    printfl("\n" + "=" * 70)
    printfl("PHASE 11b SUMMARY")
    printfl("=" * 70)
    
    total = len(tasks)
    global_consistent = len(results['consistent_global'])
    conditional = len(results['consistent_conditional'])
    truly_inc = len(results['truly_inconsistent'])
    
    printfl(f"\nTask Classification:")
    printfl(f"  Global Laws (Universal):     {global_consistent}/{total} ({100*global_consistent/total:.1f}%)")
    printfl(f"  Conditional Laws (Specific): {conditional}/{total} ({100*conditional/total:.1f}%)")
    printfl(f"  Truly Complex:               {truly_inc}/{total} ({100*truly_inc/total:.1f}%)")
    
    printfl(f"\nTheoretical Interpretation:")
    printfl(f"  - {global_consistent} tasks: F: Grid -> Grid is a simple functor")
    printfl(f"  - {conditional} tasks: F is a Natural Transformation on Object Category")
    printfl(f"  - {truly_inc} tasks: Require higher-order abstractions")
    
    # Common discriminators
    disc_counter = Counter()
    for item in results['consistent_conditional']:
        for d in item['discriminators']:
            disc_counter[d] += 1
    
    printfl(f"\nMost Common Discriminators:")
    for disc, count in disc_counter.most_common(10):
        printfl(f"  {disc}: {count} tasks")
    
    return results


def main():
    paths = ["data/arc/training", "C:/Lean4 Projects/data/arc/training"]
    arc_path = next((p for p in paths if Path(p).exists()), None)
    
    if arc_path:
        run_phase11b(arc_path)
    else:
        printfl("ARC data not found!")


if __name__ == "__main__":
    main()
