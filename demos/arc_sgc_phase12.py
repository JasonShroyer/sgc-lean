"""
ARC-SGC Phase 12: Conditional Program Synthesis

THEORETICAL FOUNDATION:
Phase 11b showed that "inconsistent" tasks are actually "conditional" tasks.
The 23% "truly complex" tasks are likely COMPOSITE PROGRAMS of known primitives,
conditional on local discriminators.

ARCHITECTURE:
1. Discriminator Engine: Object State -> Physical Law mapping
2. Program Synthesizer: Construct conditional programs from rules
3. Executor: Run synthesized programs with verification

EXAMPLE:
Task 00d62c1b isn't "magic" - it's:
    if color == BLUE then EXPAND else IDENTITY

This is SYMBOLIC REGRESSION constrained by PHYSICAL TYPES.
We fit a decision tree to map Object State -> Physical Law.
"""

import torch
import torch.nn as nn
from dataclasses import dataclass, field
from typing import List, Tuple, Dict, Optional, Set, Callable
from collections import Counter, defaultdict
from enum import Enum
import numpy as np
from pathlib import Path
import sys
import time

sys.path.insert(0, str(Path(__file__).parent))
from arc_sgc_phase8_3 import (
    ARCPhase83Config, ARCGrid, ARCObject, ARCExample, ARCTask,
    load_arc_tasks, detect_objects, compute_defect_energy,
    GeometryFirstSolver, ContentSolver,
    CompositePotential, relax_all_colors,
    V_ContactDist, V_TopEdge, V_BottomEdge, V_BoundaryDist
)
from arc_sgc_phase11 import PhenotypeSignature, SignatureComputer
from arc_sgc_phase11b import (
    ObjectMatcher, ObjectProperties, MatchedObjectPair, ObjectSignature,
    Discriminator, InvariantDiscoverer
)

def printfl(*args, **kwargs):
    print(*args, **kwargs)
    sys.stdout.flush()


# =============================================================================
# CONDITIONAL RULE
# =============================================================================

@dataclass
class ConditionalRule:
    """A rule mapping object condition to operation."""
    condition: Optional[Discriminator]  # None means "default" / "all objects"
    signature: ObjectSignature
    operator_name: str
    confidence: float = 1.0
    
    def __str__(self):
        cond_str = str(self.condition) if self.condition else "ALL"
        return f"IF {cond_str} THEN {self.operator_name} [{self.signature}]"
    
    def matches(self, obj: ObjectProperties) -> bool:
        if self.condition is None:
            return True
        return self.condition.matches(obj)


# =============================================================================
# DISCRIMINATOR ENGINE
# =============================================================================

class DiscriminatorEngine:
    """
    Discover discriminators that map Object State -> Physical Law.
    This is symbolic regression constrained by physical types.
    """
    
    def __init__(self, config: ARCPhase83Config):
        self.config = config
        self.matcher = ObjectMatcher(config)
    
    def discover_rules(self, task: ARCTask) -> List[ConditionalRule]:
        """
        Discover conditional rules from training examples.
        Returns list of (Condition, Signature, Operator) rules.
        """
        examples = task.train_examples
        
        # Gather all object pairs from all examples
        all_pairs: List[Tuple[ObjectProperties, ObjectSignature]] = []
        
        for ex in examples:
            in_props = self.matcher.extract_object_properties(ex.input_grid)
            out_props = self.matcher.extract_object_properties(ex.output_grid)
            matched = self.matcher.match_objects(in_props, out_props)
            
            for pair in matched:
                if pair.input_obj is not None:
                    all_pairs.append((pair.input_obj, pair.signature))
        
        if not all_pairs:
            return []
        
        # Group pairs by signature
        sig_groups: Dict[Tuple, List[ObjectProperties]] = defaultdict(list)
        for obj, sig in all_pairs:
            sig_groups[sig.to_tuple()].append(obj)
        
        # For each signature group, find discriminating property
        rules = []
        
        for sig_tuple, objects in sig_groups.items():
            sig = ObjectSignature(*sig_tuple)
            
            # Try to find a common property
            discriminator = self._find_discriminator(objects, all_pairs)
            
            # Determine operator from signature
            operator_name = self._signature_to_operator(sig)
            
            rules.append(ConditionalRule(
                condition=discriminator,
                signature=sig,
                operator_name=operator_name,
                confidence=len(objects) / len(all_pairs)
            ))
        
        return rules
    
    def _find_discriminator(self, target_objects: List[ObjectProperties],
                            all_pairs: List[Tuple[ObjectProperties, ObjectSignature]]) -> Optional[Discriminator]:
        """Find a property that uniquely identifies target_objects."""
        
        all_objects = [obj for obj, _ in all_pairs]
        other_objects = [obj for obj in all_objects if obj not in target_objects]
        
        if not other_objects:
            return None  # All objects have same signature, no discriminator needed
        
        # Try color discrimination
        target_colors = set(obj.color for obj in target_objects)
        other_colors = set(obj.color for obj in other_objects)
        
        unique_colors = target_colors - other_colors
        if unique_colors:
            color = list(unique_colors)[0]
            return Discriminator('color', '==', color)
        
        # Try size discrimination
        target_masses = [obj.mass for obj in target_objects]
        other_masses = [obj.mass for obj in other_objects]
        
        if target_masses and other_masses:
            target_avg = sum(target_masses) / len(target_masses)
            other_avg = sum(other_masses) / len(other_masses)
            
            if target_avg > other_avg * 1.5:
                threshold = int((target_avg + other_avg) / 2)
                return Discriminator('mass', '>', threshold)
            elif target_avg < other_avg / 1.5:
                threshold = int((target_avg + other_avg) / 2)
                return Discriminator('mass', '<', threshold)
        
        # Try edge discrimination
        target_edge = [obj.is_on_edge for obj in target_objects]
        other_edge = [obj.is_on_edge for obj in other_objects]
        
        if all(target_edge) and not any(other_edge):
            return Discriminator('is_on_edge', '==', 1)  # 1 for True
        if not any(target_edge) and all(other_edge):
            return Discriminator('is_on_edge', '==', 0)  # 0 for False
        
        return None
    
    def _signature_to_operator(self, sig: ObjectSignature) -> str:
        """Map signature to operator name."""
        
        if sig.mass_change == 'grew':
            return 'expand'
        elif sig.mass_change == 'shrank':
            return 'shrink'
        elif sig.mass_change == 'disappeared':
            return 'delete'
        elif sig.mass_change == 'appeared':
            return 'create'
        elif sig.position_change == 'moved':
            return 'move'
        elif sig.color_change == 'changed':
            return 'recolor'
        elif sig.shape_change == 'scaled':
            return 'scale'
        elif sig.shape_change == 'deformed':
            return 'deform'
        else:
            return 'identity'


# =============================================================================
# PROGRAM SYNTHESIZER
# =============================================================================

@dataclass
class SynthesizedProgram:
    """A synthesized conditional program."""
    task_id: str
    rules: List[ConditionalRule]
    
    def __str__(self):
        lines = [f"Program for {self.task_id}:"]
        for i, rule in enumerate(self.rules):
            lines.append(f"  Rule {i+1}: {rule}")
        return "\n".join(lines)
    
    def to_code(self) -> str:
        """Generate Python code for the program."""
        lines = [
            f"def solve_{self.task_id}(grid, config):",
            "    objects = detect_objects(grid, config)",
            "    result = grid.data.clone()",
            ""
        ]
        
        for i, rule in enumerate(self.rules):
            cond = rule.condition
            if cond:
                if cond.operator == '==':
                    filter_code = f"o.{cond.property_name} == {cond.value}"
                elif cond.operator == '>':
                    filter_code = f"o.{cond.property_name} > {cond.value}"
                else:
                    filter_code = f"o.{cond.property_name} < {cond.value}"
                
                lines.append(f"    # Rule {i+1}: {rule.condition}")
                lines.append(f"    subset_{i} = [o for o in objects if {filter_code}]")
            else:
                lines.append(f"    # Rule {i+1}: ALL objects")
                lines.append(f"    subset_{i} = objects")
            
            lines.append(f"    # Apply: {rule.operator_name}")
            lines.append(f"    result = apply_{rule.operator_name}(result, subset_{i})")
            lines.append("")
        
        lines.append("    return ARCGrid(result)")
        return "\n".join(lines)


class ProgramSynthesizer:
    """Synthesize conditional programs from discovered rules."""
    
    def __init__(self, config: ARCPhase83Config):
        self.config = config
        self.engine = DiscriminatorEngine(config)
    
    def synthesize(self, task: ARCTask) -> SynthesizedProgram:
        """Synthesize a program for the given task."""
        rules = self.engine.discover_rules(task)
        return SynthesizedProgram(task_id=task.task_id, rules=rules)


# =============================================================================
# CONDITIONAL EXECUTOR
# =============================================================================

class ConditionalExecutor:
    """Execute synthesized conditional programs."""
    
    def __init__(self, config: ARCPhase83Config):
        self.config = config
        self.matcher = ObjectMatcher(config)
        self.movement_potentials = [V_ContactDist(), V_TopEdge(), V_BottomEdge(), V_BoundaryDist()]
    
    def execute(self, program: SynthesizedProgram, input_grid: ARCGrid, 
                target_shape: Tuple[int, int]) -> ARCGrid:
        """Execute a synthesized program on input grid."""
        
        objects = detect_objects(input_grid, self.config)
        obj_props = self.matcher.extract_object_properties(input_grid)
        
        # Start with input or zeros depending on program
        result = input_grid.data.clone()
        
        # Track which pixels have been modified
        modified = torch.zeros_like(result, dtype=torch.bool)
        
        for rule in program.rules:
            # Find matching objects
            matching_objs = []
            matching_props = []
            
            for obj, props in zip(objects, obj_props):
                if rule.matches(props):
                    matching_objs.append(obj)
                    matching_props.append(props)
            
            if not matching_objs:
                continue
            
            # Apply operator to matching objects
            for obj, props in zip(matching_objs, matching_props):
                result = self._apply_operator(result, obj, rule.operator_name, rule.signature)
        
        # Handle shape mismatch
        if result.shape != target_shape:
            # Try to resize
            if result.shape[0] <= target_shape[0] and result.shape[1] <= target_shape[1]:
                new_result = torch.zeros(target_shape, dtype=result.dtype, device=result.device)
                new_result[:result.shape[0], :result.shape[1]] = result
                result = new_result
            else:
                result = result[:target_shape[0], :target_shape[1]]
        
        return ARCGrid(result)
    
    def _apply_operator(self, grid: torch.Tensor, obj: ARCObject, 
                        operator_name: str, signature: ObjectSignature) -> torch.Tensor:
        """Apply a single operator to an object."""
        
        result = grid.clone()
        
        if operator_name == 'identity':
            pass  # No change
        
        elif operator_name == 'delete':
            for r, c in obj.pixels:
                result[r, c] = self.config.background_color
        
        elif operator_name == 'expand':
            # Expand object by 1 pixel in each direction
            color = obj.color
            new_pixels = set()
            for r, c in obj.pixels:
                for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                    nr, nc = r + dr, c + dc
                    if 0 <= nr < result.shape[0] and 0 <= nc < result.shape[1]:
                        if result[nr, nc] == self.config.background_color:
                            new_pixels.add((nr, nc))
            
            for r, c in new_pixels:
                result[r, c] = color
        
        elif operator_name == 'move':
            # Move based on signature (simplified: move toward center)
            rows = [p[0] for p in obj.pixels]
            cols = [p[1] for p in obj.pixels]
            cr, cc = sum(rows) / len(rows), sum(cols) / len(cols)
            
            # Determine direction
            H, W = result.shape
            dr = 1 if cr < H / 2 else -1
            dc = 0
            
            # Remove old pixels
            for r, c in obj.pixels:
                result[r, c] = self.config.background_color
            
            # Add new pixels
            for r, c in obj.pixels:
                nr, nc = r + dr, c + dc
                if 0 <= nr < H and 0 <= nc < W:
                    result[nr, nc] = obj.color
        
        elif operator_name == 'recolor':
            # Recolor to most common non-background color
            colors = Counter(result.flatten().tolist())
            colors.pop(self.config.background_color, None)
            if colors:
                new_color = colors.most_common(1)[0][0]
                for r, c in obj.pixels:
                    result[r, c] = new_color
        
        elif operator_name == 'create':
            # Object appeared - already in output, nothing to do
            pass
        
        return result


# =============================================================================
# CONDITIONAL SOLVER
# =============================================================================

class ConditionalSolver:
    """Solve tasks using conditional program synthesis."""
    
    def __init__(self, config: ARCPhase83Config):
        self.config = config
        self.synthesizer = ProgramSynthesizer(config)
        self.executor = ConditionalExecutor(config)
        
        # Fallback to Phase 8.3 solver
        self.fallback_solver = GeometryFirstSolver(config)
    
    def solve_task(self, task: ARCTask, verbose: bool = False) -> Dict:
        """Solve task using conditional synthesis."""
        start_time = time.time()
        examples = task.train_examples
        
        # Step 1: Synthesize program
        program = self.synthesizer.synthesize(task)
        
        if verbose:
            printfl(f"\n{program}")
        
        # Step 2: Execute on training examples
        train_energies = []
        for ex in examples:
            try:
                result = self.executor.execute(program, ex.input_grid, ex.output_grid.shape)
                energy = compute_defect_energy(result, ex.output_grid)
                train_energies.append(energy)
            except Exception as e:
                train_energies.append(1000.0)
        
        avg_train_energy = np.mean(train_energies) if train_energies else 1000.0
        
        # Step 3: If conditional program fails, use fallback
        if avg_train_energy > self.config.energy_threshold:
            fallback_result = self.fallback_solver.solve_task(task, verbose=False)
            if fallback_result['avg_train_energy'] < avg_train_energy:
                fallback_result['method'] = 'fallback:' + fallback_result.get('operation', 'unknown')
                fallback_result['program'] = None
                return fallback_result
        
        # Step 4: Execute on test examples
        test_energies = []
        for ex in task.test_examples:
            try:
                result = self.executor.execute(program, ex.input_grid, ex.output_grid.shape)
                energy = compute_defect_energy(result, ex.output_grid)
                test_energies.append(energy)
            except:
                test_energies.append(1000.0)
        
        elapsed = time.time() - start_time
        is_perfect = avg_train_energy < self.config.energy_threshold
        
        return {
            'task_id': task.task_id,
            'method': 'conditional',
            'program': program,
            'rules': [str(r) for r in program.rules],
            'avg_train_energy': avg_train_energy,
            'train_energies': train_energies,
            'test_energies': test_energies,
            'elapsed_ms': elapsed * 1000,
            'is_perfect': is_perfect
        }


# =============================================================================
# EVALUATION
# =============================================================================

def run_phase12(data_path: str):
    printfl("=" * 70)
    printfl("ARC-SGC Phase 12: Conditional Program Synthesis")
    printfl("=" * 70)
    
    config = ARCPhase83Config()
    tasks = load_arc_tasks(data_path, 'cpu')
    printfl(f"\nLoaded {len(tasks)} tasks")
    
    solver = ConditionalSolver(config)
    
    all_results = []
    perfect_tasks = []
    conditional_solves = []
    fallback_solves = []
    
    printfl("\n" + "=" * 50)
    printfl("Solving with Conditional Program Synthesis")
    printfl("=" * 50)
    
    for i, task in enumerate(tasks):
        result = solver.solve_task(task, verbose=False)
        all_results.append(result)
        
        if result['is_perfect']:
            perfect_tasks.append(result)
            method = result['method']
            
            if method == 'conditional':
                conditional_solves.append(result)
                printfl(f"  [CONDITIONAL] {task.task_id}")
                for rule in result['rules'][:3]:
                    printfl(f"      {rule}")
            else:
                fallback_solves.append(result)
                printfl(f"  [FALLBACK] {task.task_id}: {method}")
        
        if (i + 1) % 20 == 0:
            printfl(f"  Progress: {i+1}/{len(tasks)}, perfect={len(perfect_tasks)}")
    
    # Summary
    printfl("\n" + "=" * 70)
    printfl("PHASE 12 SUMMARY")
    printfl("=" * 70)
    
    printfl(f"\nResults:")
    printfl(f"  Total perfect: {len(perfect_tasks)}")
    printfl(f"  Conditional solves: {len(conditional_solves)}")
    printfl(f"  Fallback solves: {len(fallback_solves)}")
    
    printfl(f"\n=== Conditional Program Solves ===")
    for r in conditional_solves[:10]:
        printfl(f"\n  {r['task_id']}:")
        for rule in r['rules'][:3]:
            printfl(f"    {rule}")
    
    # Analyze rule patterns
    rule_patterns = Counter()
    for r in conditional_solves:
        for rule in r['rules']:
            # Extract operator
            if 'THEN' in rule:
                op = rule.split('THEN')[1].strip().split()[0]
                rule_patterns[op] += 1
    
    printfl(f"\n=== Most Common Operators in Conditional Solves ===")
    for op, count in rule_patterns.most_common(10):
        printfl(f"  {op}: {count}")
    
    # Near-misses
    near_misses = [r for r in all_results if 0.0001 < r['avg_train_energy'] < 0.1]
    printfl(f"\n=== Near-Misses (E<0.1) ===")
    for r in sorted(near_misses, key=lambda x: x['avg_train_energy'])[:10]:
        printfl(f"  {r['task_id']}: E={r['avg_train_energy']:.4f}")
        if r.get('rules'):
            for rule in r['rules'][:2]:
                printfl(f"    {rule}")
    
    return all_results


def main():
    paths = ["data/arc/training", "C:/Lean4 Projects/data/arc/training"]
    arc_path = next((p for p in paths if Path(p).exists()), None)
    
    if arc_path:
        run_phase12(arc_path)
    else:
        printfl("ARC data not found!")


if __name__ == "__main__":
    main()
