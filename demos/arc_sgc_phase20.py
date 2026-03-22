"""
ARC-SGC Phase 20: The Abstraction Engine

THEORETICAL FOUNDATION:
Phase 19 achieved 36 perfect solves with Fractal Reasoning.
But it "solves from scratch" every time - no memory of discovered physics.

Phase 20 introduces META-LEARNING via ABSTRACTION.

THE MISSING PIECE: THE "AKASHIC RECORD" (RULE REGISTRY)

We transition from Hardcoded Solvers to a Dynamic Registry that catalogs
phenomena as they are discovered.

SGC PRINCIPLE FOR GENERALIZATION:
1. SYMMETRY (Invariant): A rule like "Gravity" is invariant across MULTIPLE TASKS
   (not just multiple examples within a task).
2. GROUP (Catalog): Valid ARC transformations form a group. We catalog generators.
3. COMPOSITION (Unpacking): Complex rules = chains of cataloged primitives.

THREE OPERATIONS:

1. ABSTRACTION (Lifting):
   Specific: shift(1, 0) -> Abstract: Translation(dx, dy) -> Meta: Isometry
   
2. CATALOGING (Persistence):
   Rule: Gravity
   Prerequisites: [Objects, Direction, StopCondition]
   Status: Discovered (frequency=5)
   
3. RETRIEVAL (Transfer):
   Query: "Do cataloged rules apply to this task's dynamic layer?"
   Result: "Matches Gravity pattern from Task A"

WHY THIS IS BETTER:
- Efficiency: Stops rediscovering "Gravity" every time
- Generalization: Compose known rules (Gravity + ColorChange)
- Discovery: Identifies truly NEW phenomena as novel registry entries

SGC GROUNDING:
- Abstraction ≈ Quotient by observational equivalence (morphisms)
- Registry ≈ Lie algebra generators of transformation group
- Composition ≈ Free monoid on generators (word problem)
- Transfer ≈ Functorial mapping between task categories
"""

import torch
import numpy as np
import json
import os
import time
import math
import re
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple, Set, Any, Callable
from collections import Counter, defaultdict
from enum import Enum
from pathlib import Path

# Import Phase 19 components
from arc_sgc_phase19 import (
    ARCGrid, ARCTask, ARCExample, ARCPhase83Config,
    Phase19Solver, Program, CandidateSolution,
    FractalDecomposer, FractalDecomposition, LayerType,
    AlgebraicVerifier, CoolingSchedule, CertaintyCalculator,
    CertaintyAssessment, load_arc_tasks
)


# =============================================================================
# COMPONENT 1: GENERIC RULE REPRESENTATION
# =============================================================================

class RuleCategory(Enum):
    """Fundamental categories of ARC transformations (Lie algebra generators)."""
    IDENTITY = "identity"           # Do nothing (trivial)
    TRANSLATION = "translation"     # Rigid motion dx, dy
    ROTATION = "rotation"           # 90°, 180°, 270°
    REFLECTION = "reflection"       # Flip horizontal/vertical
    SCALING = "scaling"             # Resize by factor
    COLOR_MAP = "color_map"         # Permute colors
    FILL = "fill"                   # Fill region with color
    CROP = "crop"                   # Extract subgrid
    GRAVITY = "gravity"             # Move until collision
    PATTERN = "pattern"             # Tile/repeat
    EXTRACT = "extract"             # Select object by property
    COMPOSITE = "composite"         # Chain of primitives


@dataclass
class RuleSignature:
    """
    The 'type signature' of a rule - what inputs it requires.
    
    This is the PREREQUISITE structure that must be present
    in a task for this rule to apply.
    """
    requires_objects: bool = False      # Needs identifiable objects
    requires_direction: bool = False    # Needs directional parameter
    requires_color: bool = False        # Needs color parameter
    requires_position: bool = False     # Needs position parameter
    requires_shape_match: bool = False  # Input/output same shape
    requires_size_change: bool = False  # Input/output different size
    parameter_types: List[str] = field(default_factory=list)
    
    def matches(self, task_signature: 'TaskSignature') -> float:
        """Return match score [0, 1] between rule signature and task."""
        score = 1.0
        
        # Hard requirements
        if self.requires_shape_match and not task_signature.same_shape:
            return 0.0
        if self.requires_size_change and task_signature.same_shape:
            return 0.0
        
        # Soft preferences (weighted)
        if self.requires_objects and not task_signature.has_objects:
            score *= 0.5
        if self.requires_color and not task_signature.has_color_changes:
            score *= 0.7
            
        return score


@dataclass
class TaskSignature:
    """
    The 'fingerprint' of a task that determines applicable rules.
    Computed once per task for efficient registry lookup.
    """
    same_shape: bool = True
    has_objects: bool = False
    has_color_changes: bool = False
    has_position_changes: bool = False
    input_colors: Set[int] = field(default_factory=set)
    output_colors: Set[int] = field(default_factory=set)
    avg_object_count: float = 0.0
    entropy_ratio: float = 1.0  # output_entropy / input_entropy


@dataclass
class GenericRule:
    """
    An abstract rule discovered from previous successes.
    
    This is an entry in the "Akashic Record" - the long-term memory
    of discovered ARC physics.
    """
    name: str                           # e.g., "Gravity_Down", "Fill_MostFrequent"
    category: RuleCategory              # Fundamental category
    signature: RuleSignature            # Prerequisites for application
    confidence: float = 0.5             # Bayesian confidence [0, 1]
    frequency: int = 0                  # How many tasks has this solved?
    success_rate: float = 0.0           # successes / attempts
    
    # The abstract program template
    template: Optional[str] = None      # e.g., "fill_dynamic({color})"
    parameters: Dict[str, str] = field(default_factory=dict)  # Parameter bindings
    
    # Discovery metadata
    discovered_from: List[str] = field(default_factory=list)  # Task IDs
    discovered_time: float = 0.0
    
    def instantiate(self, bindings: Dict[str, Any]) -> Optional[Program]:
        """
        Create a concrete Program by binding parameters.
        
        Example: Fill_MostFrequent.instantiate({color: 3}) -> fill_dynamic(3)
        """
        if not self.template:
            return None
            
        try:
            concrete_name = self.template.format(**bindings)
            return Program(name=concrete_name, transform=lambda x: x)
        except KeyError:
            return None
    
    def update_stats(self, success: bool):
        """Update Bayesian statistics after an attempt."""
        self.frequency += 1
        if success:
            # Bayesian update: confidence moves toward success rate
            self.success_rate = (self.success_rate * (self.frequency - 1) + 1.0) / self.frequency
        else:
            self.success_rate = (self.success_rate * (self.frequency - 1)) / self.frequency
        
        # Confidence = weighted combination of prior and observed rate
        prior_weight = 2.0  # Equivalent to 2 pseudo-observations
        self.confidence = (prior_weight * 0.5 + self.frequency * self.success_rate) / (prior_weight + self.frequency)


# =============================================================================
# COMPONENT 2: THE RULE REGISTRY (AKASHIC RECORD)
# =============================================================================

class RuleRegistry:
    """
    The 'Akashic Record' of discovered ARC physics.
    
    This is the long-term memory that enables meta-learning.
    Rules are:
    1. Seeded with first principles (axioms)
    2. Discovered from successful solves
    3. Retrieved to suggest hypotheses for new tasks
    4. Composed to create complex behaviors
    """
    
    REGISTRY_PATH = "data/arc_rule_registry.json"
    
    def __init__(self, persist: bool = True):
        self.rules: Dict[str, GenericRule] = {}
        self.persist = persist
        
        # Attempt statistics for Bayesian learning
        self.attempt_log: List[Dict] = []
        
        # Initialize with axioms (first principles)
        self._seed_axioms()
        
        # Load persisted rules if available
        if persist:
            self._load()
    
    def _seed_axioms(self):
        """
        Seed the registry with fundamental symmetries.
        
        These are the GENERATORS of the ARC transformation group.
        All complex rules should be expressible as compositions.
        """
        # Identity (trivial symmetry - always valid)
        self.register_axiom(GenericRule(
            name="Identity",
            category=RuleCategory.IDENTITY,
            signature=RuleSignature(requires_shape_match=True),
            confidence=1.0,  # Axiom - certain
            template="identity"
        ))
        
        # Translation (rigid motion)
        self.register_axiom(GenericRule(
            name="Translation",
            category=RuleCategory.TRANSLATION,
            signature=RuleSignature(requires_shape_match=True, requires_direction=True),
            confidence=0.8,
            template="shift({dx},{dy})"
        ))
        
        # Rotation (discrete rotational symmetry)
        for angle in [90, 180, 270]:
            self.register_axiom(GenericRule(
                name=f"Rotation_{angle}",
                category=RuleCategory.ROTATION,
                signature=RuleSignature(requires_shape_match=(angle == 180)),
                confidence=0.8,
                template=f"rot{angle}"
            ))
        
        # Reflection (mirror symmetry)
        for axis in ["horizontal", "vertical"]:
            self.register_axiom(GenericRule(
                name=f"Reflect_{axis}",
                category=RuleCategory.REFLECTION,
                signature=RuleSignature(requires_shape_match=True),
                confidence=0.8,
                template=f"flip_{axis}"
            ))
        
        # Color Mapping (permutation group S_10)
        self.register_axiom(GenericRule(
            name="ColorPermutation",
            category=RuleCategory.COLOR_MAP,
            signature=RuleSignature(requires_shape_match=True, requires_color=True),
            confidence=0.7,
            template="color_map({mapping})"
        ))
        
        # Fill (constant function on region)
        self.register_axiom(GenericRule(
            name="Fill_Region",
            category=RuleCategory.FILL,
            signature=RuleSignature(requires_shape_match=True, requires_color=True),
            confidence=0.7,
            template="fill_dynamic({color})"
        ))
        
        # Crop (projection to subspace)
        self.register_axiom(GenericRule(
            name="Crop",
            category=RuleCategory.CROP,
            signature=RuleSignature(requires_size_change=True, requires_position=True),
            confidence=0.7,
            template="crop_to({size})"
        ))
        
        # Extract (selection by predicate)
        for pred in ["largest", "smallest", "most_frequent"]:
            self.register_axiom(GenericRule(
                name=f"Extract_{pred}",
                category=RuleCategory.EXTRACT,
                signature=RuleSignature(requires_objects=True),
                confidence=0.6,
                template=f"extract({pred})"
            ))
        
        # Gravity (dynamics with collision)
        for direction in ["down", "up", "left", "right"]:
            self.register_axiom(GenericRule(
                name=f"Gravity_{direction}",
                category=RuleCategory.GRAVITY,
                signature=RuleSignature(requires_objects=True, requires_direction=True),
                confidence=0.5,
                template=f"gravity_{direction}"
            ))
    
    def register_axiom(self, rule: GenericRule):
        """Register a fundamental axiom (first principle)."""
        rule.discovered_time = time.time()
        self.rules[rule.name] = rule
    
    def abstract_and_register(self, program: Program, task: ARCTask, energy: float) -> Optional[GenericRule]:
        """
        Take a concrete winning program and abstract it.
        
        LIFTING: specific -> generic
        E.g., "fill_dynamic(3)" -> "Fill_MostFrequent(color)"
        
        This is the key meta-learning step.
        """
        if program is None:
            return None
            
        program_name = program.name
        
        # Parse the program name to extract category and parameters
        generic_form = self._lift_program(program_name, task)
        
        if generic_form is None:
            return None
        
        # Check if rule already exists
        if generic_form.name in self.rules:
            # Update existing rule
            existing = self.rules[generic_form.name]
            existing.frequency += 1
            existing.discovered_from.append(task.task_id)
            # Bayesian confidence update
            existing.update_stats(success=True)
            print(f"  [+] Rule strengthened: {generic_form.name} (freq={existing.frequency}, conf={existing.confidence:.2f})")
        else:
            # Register new rule
            generic_form.discovered_from = [task.task_id]
            generic_form.discovered_time = time.time()
            generic_form.frequency = 1
            generic_form.confidence = 0.6  # Initial confidence for discovered rule
            self.rules[generic_form.name] = generic_form
            print(f"  [NEW] PHYSICAL LAW: {generic_form.name}")
        
        # Persist
        if self.persist:
            self._save()
        
        return generic_form
    
    def _lift_program(self, program_name: str, task: ARCTask) -> Optional[GenericRule]:
        """
        Lift a concrete program to its generic form.
        
        This implements the ABSTRACTION step.
        """
        # Pattern: fill_dynamic(N)
        match = re.match(r'fill_dynamic\((\d+)\)', program_name)
        if match:
            color = int(match.group(1))
            # Determine the semantic meaning of this color
            color_meaning = self._analyze_fill_color(color, task)
            return GenericRule(
                name=f"Fill_{color_meaning}",
                category=RuleCategory.FILL,
                signature=RuleSignature(requires_shape_match=True, requires_color=True),
                template="fill_dynamic({color})",
                parameters={"color_semantic": color_meaning}
            )
        
        # Pattern: cegar:color_map({...})
        match = re.match(r'cegar:color_map\(\{(.+)\}\)', program_name)
        if match:
            mapping_str = match.group(1)
            # Abstract the color mapping
            mapping_type = self._analyze_color_mapping(mapping_str, task)
            return GenericRule(
                name=f"ColorMap_{mapping_type}",
                category=RuleCategory.COLOR_MAP,
                signature=RuleSignature(requires_shape_match=True, requires_color=True),
                template="color_map({mapping})",
                parameters={"mapping_type": mapping_type}
            )
        
        # Pattern: cegar:crop_to((H, W))
        match = re.match(r'cegar:crop_to\(\((\d+),\s*(\d+)\)\)', program_name)
        if match:
            h, w = int(match.group(1)), int(match.group(2))
            crop_type = self._analyze_crop(h, w, task)
            return GenericRule(
                name=f"Crop_{crop_type}",
                category=RuleCategory.CROP,
                signature=RuleSignature(requires_size_change=True),
                template="crop_to({size})",
                parameters={"crop_type": crop_type}
            )
        
        # Pattern: extract(predicate)
        match = re.match(r'extract\((\w+)\)', program_name)
        if match:
            pred = match.group(1)
            return GenericRule(
                name=f"Extract_{pred}",
                category=RuleCategory.EXTRACT,
                signature=RuleSignature(requires_objects=True),
                template=f"extract({pred})"
            )
        
        # Pattern: rotation
        match = re.match(r'rot(\d+)', program_name)
        if match:
            angle = int(match.group(1))
            return GenericRule(
                name=f"Rotation_{angle}",
                category=RuleCategory.ROTATION,
                signature=RuleSignature(),
                template=f"rot{angle}"
            )
        
        # Pattern: shift/translation
        match = re.match(r'shift\((-?\d+),\s*(-?\d+)\)', program_name)
        if match:
            dx, dy = int(match.group(1)), int(match.group(2))
            direction = self._direction_name(dx, dy)
            return GenericRule(
                name=f"Translation_{direction}",
                category=RuleCategory.TRANSLATION,
                signature=RuleSignature(requires_shape_match=True, requires_direction=True),
                template="shift({dx},{dy})"
            )
        
        # Pattern: V_* (physics potentials)
        match = re.match(r'[+-]?\d*\.?\d*\*?V_(\w+)', program_name)
        if match:
            potential = match.group(1)
            return GenericRule(
                name=f"Physics_{potential}",
                category=RuleCategory.GRAVITY,
                signature=RuleSignature(requires_objects=True, requires_direction=True),
                template=f"V_{potential}"
            )
        
        # Pattern: crop_to_content
        if program_name == "crop_to_content":
            return GenericRule(
                name="Crop_ToContent",
                category=RuleCategory.CROP,
                signature=RuleSignature(requires_size_change=True),
                template="crop_to_content"
            )
        
        # Pattern: identity
        if program_name in ["identity", "fallback:identity"]:
            return GenericRule(
                name="Identity",
                category=RuleCategory.IDENTITY,
                signature=RuleSignature(requires_shape_match=True),
                template="identity"
            )
        
        # Unknown pattern - create generic entry
        return GenericRule(
            name=f"Unknown_{program_name[:20]}",
            category=RuleCategory.COMPOSITE,
            signature=RuleSignature(),
            template=program_name
        )
    
    def _analyze_fill_color(self, color: int, task: ARCTask) -> str:
        """Determine semantic meaning of fill color."""
        # Collect color frequencies across examples
        input_colors = []
        output_colors = []
        for ex in task.train_examples:
            input_colors.extend(ex.input_grid.data.flatten().tolist())
            output_colors.extend(ex.output_grid.data.flatten().tolist())
        
        input_counts = Counter(input_colors)
        output_counts = Counter(output_colors)
        
        # Is it the most frequent input color?
        if input_counts.most_common(1)[0][0] == color:
            return "MostFreqInput"
        
        # Is it the most frequent output color?
        if output_counts.most_common(1)[0][0] == color:
            return "MostFreqOutput"
        
        # Is it a new color (only in output)?
        if color not in input_counts and color in output_counts:
            return "NewColor"
        
        # Is it the background color (0)?
        if color == 0:
            return "Background"
        
        return f"Color{color}"
    
    def _analyze_color_mapping(self, mapping_str: str, task: ARCTask) -> str:
        """Determine type of color mapping."""
        # Count how many colors are mapped
        mappings = mapping_str.split(',')
        num_mappings = len(mappings)
        
        # Check if it's a swap
        if num_mappings == 2:
            return "Swap"
        
        # Check if multiple colors map to same target
        targets = [m.split(':')[1].strip() for m in mappings if ':' in m]
        if len(set(targets)) == 1:
            return "Merge"
        
        # General permutation
        return f"Permutation_{num_mappings}"
    
    def _analyze_crop(self, h: int, w: int, task: ARCTask) -> str:
        """Determine type of crop operation."""
        # Check if output is a fixed small size
        if h <= 3 and w <= 3:
            return "ToSmall"
        
        # Check if it's a common ratio
        for ex in task.train_examples:
            ih, iw = ex.input_grid.shape
            if ih > 0 and iw > 0:
                if h == ih // 2 and w == iw // 2:
                    return "ToHalf"
                if h == ih // 3 and w == iw // 3:
                    return "ToThird"
        
        return f"To_{h}x{w}"
    
    def _direction_name(self, dx: int, dy: int) -> str:
        """Convert delta to direction name."""
        if dx > 0 and dy == 0:
            return "Right"
        if dx < 0 and dy == 0:
            return "Left"
        if dx == 0 and dy > 0:
            return "Down"
        if dx == 0 and dy < 0:
            return "Up"
        return f"({dx},{dy})"
    
    def suggest_hypotheses(self, task: ARCTask, task_sig: TaskSignature, top_k: int = 10) -> List[Tuple[GenericRule, float]]:
        """
        Propose candidate rules based on what has worked before.
        
        RETRIEVAL: Query the registry for applicable rules.
        
        Returns rules sorted by expected utility:
        utility = confidence * signature_match * frequency_bonus
        """
        suggestions = []
        
        for rule in self.rules.values():
            # Check signature compatibility
            match_score = rule.signature.matches(task_sig)
            if match_score < 0.1:
                continue
            
            # Calculate utility
            frequency_bonus = math.log1p(rule.frequency) / 5.0  # Diminishing returns
            utility = rule.confidence * match_score * (1.0 + frequency_bonus)
            
            suggestions.append((rule, utility))
        
        # Sort by utility (descending)
        suggestions.sort(key=lambda x: -x[1])
        
        return suggestions[:top_k]
    
    def compose_rules(self, rule_a: GenericRule, rule_b: GenericRule) -> Optional[GenericRule]:
        """
        Compose two rules into a new rule.
        
        COMPOSITION: chain primitives to create complex behaviors.
        
        This implements the free monoid on generators.
        """
        # Check compatibility (output type of A matches input type of B)
        # For now, use simple heuristics
        
        composite = GenericRule(
            name=f"{rule_a.name}_{rule_b.name}",
            category=RuleCategory.COMPOSITE,
            signature=RuleSignature(
                requires_objects=rule_a.signature.requires_objects or rule_b.signature.requires_objects,
                requires_color=rule_a.signature.requires_color or rule_b.signature.requires_color,
                requires_shape_match=rule_a.signature.requires_shape_match and rule_b.signature.requires_shape_match
            ),
            confidence=rule_a.confidence * rule_b.confidence,  # Product of confidences
            template=f"{rule_a.template} | {rule_b.template}" if rule_a.template and rule_b.template else None
        )
        
        return composite
    
    def _save(self):
        """Persist registry to disk."""
        try:
            data = {
                name: {
                    "name": rule.name,
                    "category": rule.category.value,
                    "confidence": rule.confidence,
                    "frequency": rule.frequency,
                    "success_rate": rule.success_rate,
                    "template": rule.template,
                    "discovered_from": rule.discovered_from,
                    "discovered_time": rule.discovered_time
                }
                for name, rule in self.rules.items()
                if rule.frequency > 0  # Only save discovered rules
            }
            
            os.makedirs(os.path.dirname(self.REGISTRY_PATH), exist_ok=True)
            with open(self.REGISTRY_PATH, 'w') as f:
                json.dump(data, f, indent=2)
        except Exception as e:
            print(f"Warning: Could not save registry: {e}")
    
    def _load(self):
        """Load persisted registry from disk."""
        try:
            if os.path.exists(self.REGISTRY_PATH):
                with open(self.REGISTRY_PATH, 'r') as f:
                    data = json.load(f)
                
                for name, rule_data in data.items():
                    if name in self.rules:
                        # Update existing rule with persisted stats
                        self.rules[name].confidence = rule_data.get("confidence", 0.5)
                        self.rules[name].frequency = rule_data.get("frequency", 0)
                        self.rules[name].success_rate = rule_data.get("success_rate", 0.0)
                        self.rules[name].discovered_from = rule_data.get("discovered_from", [])
                    else:
                        # Create rule from persisted data
                        rule = GenericRule(
                            name=rule_data["name"],
                            category=RuleCategory(rule_data.get("category", "composite")),
                            signature=RuleSignature(),
                            confidence=rule_data.get("confidence", 0.5),
                            frequency=rule_data.get("frequency", 0),
                            success_rate=rule_data.get("success_rate", 0.0),
                            template=rule_data.get("template"),
                            discovered_from=rule_data.get("discovered_from", [])
                        )
                        self.rules[name] = rule
                
                print(f"  Loaded {len(data)} rules from registry")
        except Exception as e:
            print(f"Warning: Could not load registry: {e}")
    
    def get_statistics(self) -> Dict:
        """Return registry statistics."""
        discovered = [r for r in self.rules.values() if r.frequency > 0]
        return {
            "total_rules": len(self.rules),
            "discovered_rules": len(discovered),
            "total_applications": sum(r.frequency for r in self.rules.values()),
            "high_confidence": len([r for r in discovered if r.confidence >= 0.8]),
            "by_category": Counter(r.category.value for r in discovered)
        }


# =============================================================================
# COMPONENT 3: TASK SIGNATURE EXTRACTOR
# =============================================================================

class TaskSignatureExtractor:
    """
    Extract the 'fingerprint' of a task for registry lookup.
    """
    
    def extract(self, task: ARCTask) -> TaskSignature:
        """Extract signature from task."""
        sig = TaskSignature()
        
        # Shape analysis
        shapes_same = all(
            ex.input_grid.shape == ex.output_grid.shape 
            for ex in task.train_examples
        )
        sig.same_shape = shapes_same
        
        # Color analysis
        for ex in task.train_examples:
            sig.input_colors.update(ex.input_grid.data.unique().tolist())
            sig.output_colors.update(ex.output_grid.data.unique().tolist())
        
        sig.has_color_changes = sig.input_colors != sig.output_colors
        
        # Object detection (simple: connected non-zero regions)
        object_counts = []
        for ex in task.train_examples:
            num_objects = self._count_objects(ex.input_grid)
            object_counts.append(num_objects)
        
        sig.has_objects = any(c > 1 for c in object_counts)
        sig.avg_object_count = np.mean(object_counts) if object_counts else 0.0
        
        # Position change detection
        sig.has_position_changes = self._detect_position_changes(task)
        
        # Entropy ratio
        input_entropy = np.mean([self._grid_entropy(ex.input_grid) for ex in task.train_examples])
        output_entropy = np.mean([self._grid_entropy(ex.output_grid) for ex in task.train_examples])
        sig.entropy_ratio = output_entropy / (input_entropy + 1e-6)
        
        return sig
    
    def _count_objects(self, grid: ARCGrid) -> int:
        """Count connected non-zero regions."""
        data = grid.data.numpy()
        visited = np.zeros_like(data, dtype=bool)
        count = 0
        
        for i in range(data.shape[0]):
            for j in range(data.shape[1]):
                if data[i, j] != 0 and not visited[i, j]:
                    self._flood_fill(data, visited, i, j, data[i, j])
                    count += 1
        
        return count
    
    def _flood_fill(self, data, visited, i, j, color):
        """Flood fill to mark connected region."""
        stack = [(i, j)]
        while stack:
            ci, cj = stack.pop()
            if ci < 0 or ci >= data.shape[0] or cj < 0 or cj >= data.shape[1]:
                continue
            if visited[ci, cj] or data[ci, cj] != color:
                continue
            visited[ci, cj] = True
            stack.extend([(ci+1, cj), (ci-1, cj), (ci, cj+1), (ci, cj-1)])
    
    def _detect_position_changes(self, task: ARCTask) -> bool:
        """Detect if objects move between input and output."""
        for ex in task.train_examples:
            if ex.input_grid.shape != ex.output_grid.shape:
                continue
            
            inp = ex.input_grid.data.numpy()
            out = ex.output_grid.data.numpy()
            
            # Find non-zero positions
            inp_pos = set(zip(*np.where(inp != 0)))
            out_pos = set(zip(*np.where(out != 0)))
            
            # If positions differ significantly
            if len(inp_pos.symmetric_difference(out_pos)) > 0.3 * len(inp_pos | out_pos):
                return True
        
        return False
    
    def _grid_entropy(self, grid: ARCGrid) -> float:
        """Calculate Shannon entropy of grid."""
        data = grid.data.flatten().numpy()
        counts = Counter(data)
        total = len(data)
        
        entropy = 0.0
        for count in counts.values():
            p = count / total
            if p > 0:
                entropy -= p * math.log2(p)
        
        return entropy


# =============================================================================
# COMPONENT 4: THE PHASE 20 SOLVER
# =============================================================================

class Phase20Solver(Phase19Solver):
    """
    The Abstraction Engine: Phase 19 + Meta-Learning.
    
    System 1 (Fast): Query registry for known rules
    System 2 (Slow): Run fractal reasoning if System 1 fails
    System 3 (Learn): Abstract and register new discoveries
    """
    
    def __init__(self, config: ARCPhase83Config, registry: Optional[RuleRegistry] = None):
        super().__init__(config)
        
        # The Akashic Record
        self.registry = registry if registry else RuleRegistry(persist=True)
        
        # Task signature extractor
        self.sig_extractor = TaskSignatureExtractor()
        
        # Statistics
        self.system1_hits = 0
        self.system2_solves = 0
        self.new_discoveries = 0
    
    def solve_task(self, task: ARCTask, verbose: bool = False) -> Dict:
        """
        Solve with meta-learning.
        
        1. System 1 (Fast): Check if cataloged rules apply
        2. System 2 (Slow): Run fractal reasoning if needed
        3. System 3 (Learn): Abstract and register successes
        """
        start_time = time.time()
        
        # Extract task signature for registry lookup
        task_sig = self.sig_extractor.extract(task)
        
        # =====================================================================
        # SYSTEM 1: FAST RETRIEVAL
        # =====================================================================
        # Query registry for applicable rules
        hypotheses = self.registry.suggest_hypotheses(task, task_sig, top_k=5)
        
        system1_result = None
        for rule, utility in hypotheses:
            # Try to apply this rule
            result = self._try_rule(task, rule)
            if result and result.get('is_perfect', False):
                system1_result = result
                system1_result['method'] = f"registry:{rule.name}"
                system1_result['retrieval_utility'] = utility
                self.system1_hits += 1
                
                # Strengthen the rule
                rule.update_stats(success=True)
                
                if verbose:
                    print(f"  [FAST] System 1 hit: {rule.name} (utility={utility:.2f})")
                break
        
        # =====================================================================
        # SYSTEM 2: SLOW REASONING
        # =====================================================================
        if system1_result is None:
            # Fall back to Phase 19 fractal reasoning
            result = super().solve_task(task, verbose)
            self.system2_solves += 1
        else:
            result = system1_result
        
        # =====================================================================
        # SYSTEM 3: LEARNING
        # =====================================================================
        if result.get('is_perfect', False):
            # Abstract and register the winning program
            program_name = result.get('method', '')
            if program_name and not program_name.startswith('registry:'):
                program = Program(name=program_name, apply=lambda x: x, complexity=len(program_name), source='phase20')
                new_rule = self.registry.abstract_and_register(program, task, result.get('avg_train_energy', 0))
                if new_rule and new_rule.frequency == 1:
                    self.new_discoveries += 1
        
        # Add meta-learning stats
        result['system1_hit'] = system1_result is not None
        result['registry_size'] = len(self.registry.rules)
        result['elapsed_ms'] = (time.time() - start_time) * 1000
        
        return result
    
    def _try_rule(self, task: ARCTask, rule: GenericRule) -> Optional[Dict]:
        """
        Try to apply a generic rule to a task.
        
        This requires instantiating the rule with concrete parameters.
        """
        if rule.template is None:
            return None
        
        # Determine parameter bindings from task
        bindings = self._infer_bindings(task, rule)
        
        for binding in bindings:
            # Instantiate the rule
            try:
                program_name = rule.template.format(**binding)
            except KeyError:
                continue
            
            # Try to execute
            result = self._execute_program(task, program_name)
            if result and result.get('is_perfect', False):
                # Compute certainty for System 1 hit
                # Certainty = rule_confidence * frequency_bonus * accuracy
                frequency_bonus = min(1.0, 0.5 + 0.1 * rule.frequency)
                base_certainty = rule.confidence * frequency_bonus
                
                # High certainty if rule has proven itself
                if rule.frequency >= 3 and rule.confidence >= 0.5:
                    certainty_score = max(0.85, base_certainty)
                    certainty_level = "HIGH" if certainty_score >= 0.8 else "MEDIUM"
                else:
                    certainty_score = max(0.6, base_certainty)
                    certainty_level = "MEDIUM" if certainty_score >= 0.5 else "LOW"
                
                result['certainty_score'] = certainty_score
                result['certainty_level'] = certainty_level
                result['should_submit'] = certainty_score >= 0.8
                
                return result
        
        return None
    
    def _infer_bindings(self, task: ARCTask, rule: GenericRule) -> List[Dict[str, Any]]:
        """
        Infer parameter bindings for a rule template.
        
        Returns a list of possible bindings to try.
        """
        bindings = []
        
        # For fill rules: try common colors
        if rule.category == RuleCategory.FILL:
            # Collect all colors from examples
            colors = set()
            for ex in task.train_examples:
                colors.update(ex.input_grid.data.unique().tolist())
                colors.update(ex.output_grid.data.unique().tolist())
            
            for color in colors:
                bindings.append({"color": color})
        
        # For crop rules: try output sizes
        elif rule.category == RuleCategory.CROP:
            sizes_seen = set()
            for ex in task.train_examples:
                h, w = ex.output_grid.shape
                sizes_seen.add((h, w))
            
            for size in sizes_seen:
                bindings.append({"size": size})
        
        # For translation: try small shifts
        elif rule.category == RuleCategory.TRANSLATION:
            for dx in range(-3, 4):
                for dy in range(-3, 4):
                    if dx != 0 or dy != 0:
                        bindings.append({"dx": dx, "dy": dy})
        
        # For color mapping: analyze mappings
        elif rule.category == RuleCategory.COLOR_MAP:
            mapping = self._infer_color_mapping(task)
            if mapping:
                bindings.append({"mapping": mapping})
        
        # Default: return empty binding (template is complete)
        else:
            bindings.append({})
        
        return bindings
    
    def _infer_color_mapping(self, task: ARCTask) -> Optional[str]:
        """Infer color mapping from examples."""
        mappings = {}
        
        for ex in task.train_examples:
            if ex.input_grid.shape != ex.output_grid.shape:
                return None
            
            inp = ex.input_grid.data
            out = ex.output_grid.data
            
            for i in range(inp.shape[0]):
                for j in range(inp.shape[1]):
                    ic = inp[i, j].item()
                    oc = out[i, j].item()
                    
                    if ic != oc:
                        if ic in mappings and mappings[ic] != oc:
                            return None  # Inconsistent
                        mappings[ic] = oc
        
        if mappings:
            return str(mappings)
        return None
    
    def _execute_program(self, task: ARCTask, program_name: str) -> Optional[Dict]:
        """
        Execute a named program and return result.
        
        Uses Phase 19's solver infrastructure.
        """
        # Identity
        if program_name == "identity":
            energy = 0.0
            for ex in task.train_examples:
                if ex.input_grid.shape != ex.output_grid.shape:
                    return None
                diff = (ex.input_grid.data != ex.output_grid.data).float().mean().item()
                energy += diff
            energy /= len(task.train_examples)
            
            return {
                'is_perfect': energy < self.config.energy_threshold,
                'avg_train_energy': energy,
                'method': 'identity'
            }
        
        # Fill dynamic
        match = re.match(r'fill_dynamic\((\d+)\)', program_name)
        if match:
            color = int(match.group(1))
            return self._try_fill_from_registry(task, color)
        
        # Crop
        match = re.match(r'crop_to\(\((\d+),\s*(\d+)\)\)', program_name)
        if match:
            h, w = int(match.group(1)), int(match.group(2))
            return self._try_crop_from_registry(task, h, w)
        
        # Rotation
        match = re.match(r'rot(\d+)', program_name)
        if match:
            angle = int(match.group(1))
            return self._try_rotation_from_registry(task, angle)
        
        return None
    
    def _try_fill_from_registry(self, task: ARCTask, fill_color: int) -> Optional[Dict]:
        """Try fill_dynamic with a specific color."""
        total_energy = 0.0
        
        for ex in task.train_examples:
            if ex.input_grid.shape != ex.output_grid.shape:
                return None
            
            inp = ex.input_grid.data
            out = ex.output_grid.data
            
            # Find dynamic mask (pixels that differ)
            diff_mask = inp != out
            
            # Predict: fill differences with color
            pred = inp.clone()
            pred[diff_mask] = fill_color
            
            # Energy
            energy = (pred != out).float().mean().item()
            total_energy += energy
        
        total_energy /= len(task.train_examples)
        
        return {
            'is_perfect': total_energy < self.config.energy_threshold,
            'avg_train_energy': total_energy,
            'method': f'fill_dynamic({fill_color})'
        }
    
    def _try_crop_from_registry(self, task: ARCTask, h: int, w: int) -> Optional[Dict]:
        """Try cropping to specific size."""
        total_energy = 0.0
        
        for ex in task.train_examples:
            oh, ow = ex.output_grid.shape
            if oh != h or ow != w:
                return None
            
            # Try all crop positions
            best_energy = float('inf')
            inp = ex.input_grid.data
            ih, iw = ex.input_grid.shape
            
            for si in range(ih - h + 1):
                for sj in range(iw - w + 1):
                    crop = inp[si:si+h, sj:sj+w]
                    energy = (crop != ex.output_grid.data).float().mean().item()
                    best_energy = min(best_energy, energy)
            
            total_energy += best_energy
        
        total_energy /= len(task.train_examples)
        
        return {
            'is_perfect': total_energy < self.config.energy_threshold,
            'avg_train_energy': total_energy,
            'method': f'crop_to(({h}, {w}))'
        }
    
    def _try_rotation_from_registry(self, task: ARCTask, angle: int) -> Optional[Dict]:
        """Try rotation."""
        total_energy = 0.0
        k = angle // 90
        
        for ex in task.train_examples:
            rotated = torch.rot90(ex.input_grid.data, k=k)
            if rotated.shape != ex.output_grid.shape:
                return None
            
            energy = (rotated != ex.output_grid.data).float().mean().item()
            total_energy += energy
        
        total_energy /= len(task.train_examples)
        
        return {
            'is_perfect': total_energy < self.config.energy_threshold,
            'avg_train_energy': total_energy,
            'method': f'rot{angle}'
        }
    
    def get_meta_stats(self) -> Dict:
        """Return meta-learning statistics."""
        return {
            'system1_hits': self.system1_hits,
            'system2_solves': self.system2_solves,
            'new_discoveries': self.new_discoveries,
            'registry_stats': self.registry.get_statistics()
        }


# =============================================================================
# MAIN RUNNER
# =============================================================================

def run_phase20(data_path: str, verbose: bool = False):
    """Run Phase 20 on ARC training tasks."""
    config = ARCPhase83Config()
    
    # Create registry (will load persisted rules if available)
    registry = RuleRegistry(persist=True)
    
    # Create solver
    solver = Phase20Solver(config, registry)
    
    # Load tasks
    tasks = load_arc_tasks(data_path, 'cpu')
    print(f"Loaded {len(tasks)} tasks")
    
    # Initial registry stats
    initial_stats = registry.get_statistics()
    print(f"\nInitial Registry: {initial_stats['total_rules']} rules, "
          f"{initial_stats['discovered_rules']} discovered")
    
    print("\n" + "=" * 50)
    print("Running Abstraction Engine")
    print("=" * 50)
    
    results = []
    perfect_count = 0
    certain_count = 0
    
    for i, task in enumerate(tasks):
        result = solver.solve_task(task, verbose)
        results.append(result)
        
        if result['is_perfect']:
            perfect_count += 1
            marker = "[PERFECT]"
            if result.get('system1_hit', False):
                marker += " [S1]"  # System 1 hit
        else:
            marker = "         "
        
        if result.get('certainty_level', 'LOW') in ['CERTAIN', 'HIGH']:
            certain_count += 1
        
        should_submit = "Submit" if result.get('should_submit', False) else "Skip"
        
        if result['is_perfect']:
            print(f"  {marker} {task.task_id}: {result['method']}")
            print(f"            C={result.get('certainty_score', 0):.2f}, "
                  f"{result.get('certainty_level', 'LOW')}, {should_submit}")
        
        if (i + 1) % 20 == 0:
            print(f"  Progress: {i+1}/{len(tasks)}, perfect={perfect_count}, "
                  f"system1={solver.system1_hits}, new={solver.new_discoveries}")
    
    # Final summary
    print("\n" + "=" * 70)
    print("PHASE 20 SUMMARY")
    print("=" * 70)
    
    # Results breakdown
    certainty_dist = Counter(r.get('certainty_level', 'LOW') for r in results)
    method_dist = Counter(r['method'] for r in results if r['is_perfect'])
    should_submit = sum(1 for r in results if r.get('should_submit', False))
    
    print(f"\nResults:")
    print(f"  Total perfect: {perfect_count}")
    print(f"  High certainty (>=0.8): {certain_count}")
    print(f"  Should submit: {should_submit}")
    
    print(f"\nMeta-Learning Stats:")
    meta_stats = solver.get_meta_stats()
    print(f"  System 1 hits (fast retrieval): {meta_stats['system1_hits']}")
    print(f"  System 2 solves (slow reasoning): {meta_stats['system2_solves']}")
    print(f"  New discoveries: {meta_stats['new_discoveries']}")
    
    print(f"\nRegistry Stats:")
    reg_stats = meta_stats['registry_stats']
    print(f"  Total rules: {reg_stats['total_rules']}")
    print(f"  Discovered rules: {reg_stats['discovered_rules']}")
    print(f"  Total applications: {reg_stats['total_applications']}")
    print(f"  High confidence rules: {reg_stats['high_confidence']}")
    
    print(f"\nCertainty distribution:")
    for level, count in sorted(certainty_dist.items()):
        print(f"  {level}: {count}")
    
    print(f"\nSolves by method:")
    for method, count in method_dist.most_common(10):
        print(f"  {method}: {count}")
    
    # Near misses
    near_misses = [(r['task_id'], r['avg_train_energy'], r.get('certainty_score', 0))
                   for r in results
                   if not r['is_perfect'] and r['avg_train_energy'] < 0.1]
    near_misses.sort(key=lambda x: x[1])
    
    if near_misses:
        print(f"\nNear-misses (E<0.1): {len(near_misses)}")
        for tid, energy, cert in near_misses[:10]:
            print(f"  {tid}: E={energy:.4f}, C={cert:.2f}")
    
    # Progress summary
    print("\n=== COMPLETE PROGRESS SUMMARY ===")
    print(f"  Phase 8.3:   6 perfect (baseline)")
    print(f"  Phase 15:   19 perfect (CEGAR)")
    print(f"  Phase 17:   20 perfect (Invariant Physics)")
    print(f"  Phase 18:   32 perfect (Decomposition)")
    print(f"  Phase 19:   36 perfect (Fractal Reasoning)")
    print(f"  Phase 20:   {perfect_count} perfect (Abstraction Engine)")
    print(f"       System 1 hits: {meta_stats['system1_hits']}")
    print(f"       New discoveries: {meta_stats['new_discoveries']}")
    print(f"       Should submit: {should_submit}")
    
    return results


def main():
    paths = ["data/arc/training", "C:/Lean4 Projects/data/arc/training"]
    arc_path = next((p for p in paths if Path(p).exists()), None)
    
    if arc_path:
        run_phase20(arc_path, verbose=False)
    else:
        print("ARC data not found!")


if __name__ == "__main__":
    main()
