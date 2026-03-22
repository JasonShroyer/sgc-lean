"""
Recursive Residual Solver for ARC
==================================

CORE INSIGHT (from SGC Theory + Program Synthesis literature):
  Residuals are Discrete Gradients.

  In continuous learning, grad(L) tells weights where to move.
  In discrete program synthesis, the Residual Grid (Target - Output)
  encodes the semantic "direction" for the next compositional step.

  Current agent: f(x) != y => discard f.              (0th order)
  This solver:   f(x) != y => r = y - f(x) => solve r (1st order)

ARCHITECTURE:
  1. DiscreteGradient  - compute object-centric residuals (R+, R-, recolor)
  2. AtomicOp          - composable operation primitives
  3. OperatorLibrary   - proposes ops guided by gradient structure
  4. Synthesizer       - recursive beam search, depth <= 3

SGC GROUNDING:
  - Information Gain = defect(before) - defect(after) replaces pixel distance
  - Renormalization: successful chains collapse into new atomic ops
  - Verification: programs must be consistent across ALL training examples

Lean reference: SGC.ContinualLearning.AdiabaticInvariant (operator composition)
"""

import os
import numpy as np
import torch
import json
import time
import sys
import re
import hashlib
from pathlib import Path
from dataclasses import dataclass, field
from typing import List, Tuple, Optional, Dict, Callable, Any
from collections import Counter, deque
from copy import deepcopy

from scipy import ndimage

from arc_sgc_phase8_3 import (
    ARCGrid, ARCObject, ARCTask, ARCExample,
    detect_objects, compute_defect_energy, load_arc_tasks,
    ARCPhase83Config
)
from arc_sgc_phase21 import (
    SceneGraph, SceneGraphBuilder, SceneObject, SceneEdge
)

# Tensor Logic engine: differentiable predicate discovery (Domingos 2024)
try:
    from arc_tensor_logic import TensorPredicateLearner, make_tensor_predicate_expr, crystallize_tensor_predicate
    HAS_TENSOR_LOGIC = True
except ImportError:
    HAS_TENSOR_LOGIC = False

# SGFE engine: theory-grounded scoring (FunctionalBlanket.lean + sheaf verification)
try:
    from sgfe_engine import (
        functional_blanket_variance,
        sheaf_consistency_energy,
        sheaf_global_section_exists,
        sgfe_acceptance_gate,
        SGFEPrimitiveLibrary,
        # SGFE v2.0: Universal functional defect scorer
        sgfe_defect_delta,
        sgfe_defect_delta_multi,
        # SGFE v2.0: Refined acceptance gate
        sgfe_acceptance_gate_v2,
        # SGFE v2.2: Curriculum-aware cross-task validator
        CrossTaskPredicateValidator,
    )
    HAS_SGFE = True
except ImportError:
    HAS_SGFE = False

# Sheaf Atlas: Gauge-covariant predicate library (replaces flat SGFEPrimitiveLibrary)
try:
    from sheaf_atlas_adapter import SheafAtlasLibrary, compute_transformation_signature
    HAS_SHEAF_ATLAS = True
except ImportError:
    HAS_SHEAF_ATLAS = False

# LEM Architecture: Lattice-E-Graph-Morph for sheaf-first predicate synthesis
try:
    from arc_morph_algebra import (
        MorphologicalPredicateSynthesizer,
        MorphPredicate,
        MorphTerm,
        MorphOp,
        SE_CROSS,
        SE_SQUARE,
        SE_DIAG_L,
        SE_DIAG_R,
        SE_HORIZ,
        SE_VERT,
        CANONICAL_SES,
        apply_term,
    )
    HAS_MORPH_ALGEBRA = True
except ImportError:
    HAS_MORPH_ALGEBRA = False

BG = 0  # ARC background color


# =============================================================================
# 0. COLOR-ROLE NORMALIZATION (SGC.Renormalization: quotient by color group)
# =============================================================================
# Colors in ARC have geometric ROLES that survive across tasks:
#   - MAJORITY: most frequent non-bg color (canvas, frame)
#   - MINORITY: least frequent non-bg color (marker, signal)
#   - BG: background (color 0)
#   - ANCHOR_N: Nth most common color by frequency
#
# By storing predicates in role-space instead of color-space, they generalize
# across tasks with different color palettes but identical geometric structure.

def detect_color_roles(grid: np.ndarray) -> dict:
    """
    Map each color in a grid to its geometric role.
    
    Returns:
        Dict[int, str]: color -> role mapping
        
    Roles:
        'bg': background (color 0)
        'majority': most frequent non-bg color
        'minority': least frequent non-bg color  
        'anchor_N': Nth most common color (for middle colors)
    """
    bg = 0
    counts = Counter(grid.flat)
    counts.pop(bg, None)  # Exclude background
    if not counts:
        return {bg: 'bg'}
    
    sorted_colors = sorted(counts, key=counts.get, reverse=True)
    roles = {bg: 'bg'}
    
    for i, c in enumerate(sorted_colors):
        if i == 0:
            roles[c] = 'majority'
        elif i == len(sorted_colors) - 1 and len(sorted_colors) > 1:
            roles[c] = 'minority'
        else:
            roles[c] = f'anchor_{i}'
    
    return roles


def color_role_to_canonical(feat_name: str, color_roles: dict) -> str:
    """
    Replace color literal in feature name with its role.
    
    Example:
        'same_row_1' with roles={1:'minority'} -> 'same_row_MINORITY'
        'adj_to_5' with roles={5:'majority'} -> 'adj_to_MAJORITY'
    
    Theory (SGC.Renormalization):
        This is the quotient map π: ColorSpace → RoleSpace
        Predicates in RoleSpace are sheaf-consistent across color permutations.
    """
    def replace_color(match):
        c = int(match.group(1))
        role = color_roles.get(c, f'color_{c}')
        return f'_{role.upper()}'
    
    return re.sub(r'_(\d+)$', replace_color, feat_name)


def resolve_role_to_color(pred_name: str, grid: np.ndarray) -> str:
    """
    Resolve role placeholders in a predicate name to actual colors.
    
    Example:
        'same_row_MINORITY' on a grid where color 3 is minority -> 'same_row_3'
    
    This is the inverse of color_role_to_canonical, applied at predicate
    evaluation time to make role-based predicates concrete.
    """
    roles = detect_color_roles(grid)
    role_to_color = {v.upper(): k for k, v in roles.items()}
    
    resolved = pred_name
    for role in ['MAJORITY', 'MINORITY', 'BG'] + [f'ANCHOR_{i}' for i in range(1, 8)]:
        c = role_to_color.get(role)
        if c is not None:
            resolved = resolved.replace(f'_{role}', f'_{c}')
    
    return resolved


# =============================================================================
# 1. DISCRETE GRADIENT: The "Backward Pass"
# =============================================================================

@dataclass
class DiscreteGradient:
    """
    Object-centric residual between output and target.

    Three components (analogous to signed gradient):
      R+ (positive): pixels in target but not output (missing signal)
      R- (negative): pixels in output but not target (hallucinations)
      Recolor:       pixels present in both but wrong color

    Derived hints guide operator proposal.
    """
    diff_mask: np.ndarray          # where output != target
    positive_mask: np.ndarray      # bg->color (need to paint)
    negative_mask: np.ndarray      # color->bg (need to erase)
    recolor_mask: np.ndarray       # color->different color
    color_changes: Dict[Tuple[int,int], int]  # (from,to) -> count
    total_diff: int
    grid_size: int
    defect: float

    # Structural hints
    is_pure_recolor: bool          # only color changes, no add/remove
    is_pure_additive: bool         # only painting new pixels
    is_pure_subtractive: bool      # only erasing pixels
    is_localized: bool             # changes in < 25% of grid area
    change_bbox: Optional[Tuple[int,int,int,int]]  # bbox of changes
    dominant_color_map: Optional[Dict[int,int]]     # consistent from->to

    @classmethod
    def compute(cls, output: np.ndarray, target: np.ndarray) -> 'DiscreteGradient':
        """Compute the discrete gradient from output toward target."""
        if output.shape != target.shape:
            # Shape mismatch: entire grid is the gradient
            H, W = target.shape
            return cls(
                diff_mask=np.ones(target.shape, dtype=bool),
                positive_mask=target != BG,
                negative_mask=np.zeros(target.shape, dtype=bool),
                recolor_mask=np.zeros(target.shape, dtype=bool),
                color_changes={},
                total_diff=H * W,
                grid_size=H * W,
                defect=1.0,
                is_pure_recolor=False, is_pure_additive=False,
                is_pure_subtractive=False, is_localized=False,
                change_bbox=None, dominant_color_map=None,
            )

        diff = output != target
        out_bg = output == BG
        tgt_bg = target == BG
        out_fg = ~out_bg
        tgt_fg = ~tgt_bg

        positive = diff & out_bg & tgt_fg   # missing: need to add
        negative = diff & out_fg & tgt_bg   # extra:   need to remove
        recolor  = diff & out_fg & tgt_fg   # wrong color

        total_diff = int(diff.sum())
        grid_size = max(output.size, 1)

        # Color change map
        color_changes: Dict[Tuple[int,int], int] = {}
        if total_diff > 0:
            froms = output[diff]
            tos = target[diff]
            for f, t in zip(froms.flat, tos.flat):
                key = (int(f), int(t))
                color_changes[key] = color_changes.get(key, 0) + 1

        # Dominant color map: consistent 1-to-1 mapping?
        dominant_map = None
        if color_changes:
            fwd: Dict[int, Dict[int, int]] = {}
            for (f, t), cnt in color_changes.items():
                fwd.setdefault(f, {})[t] = fwd.get(f, {}).get(t, 0) + cnt
            candidate = {}
            consistent = True
            for f, targets in fwd.items():
                best_t = max(targets, key=targets.get)
                if targets[best_t] >= sum(targets.values()) * 0.8:
                    candidate[f] = best_t
                else:
                    consistent = False
                    break
            if consistent and candidate:
                dominant_map = candidate

        # Bbox of changes
        change_positions = np.argwhere(diff)
        bbox = None
        is_localized = False
        if len(change_positions) > 0:
            r1, c1 = change_positions.min(axis=0)
            r2, c2 = change_positions.max(axis=0) + 1
            bbox = (int(r1), int(c1), int(r2), int(c2))
            bbox_area = (r2 - r1) * (c2 - c1)
            is_localized = bbox_area < 0.25 * grid_size

        n_pos = int(positive.sum())
        n_neg = int(negative.sum())
        n_rec = int(recolor.sum())

        return cls(
            diff_mask=diff,
            positive_mask=positive,
            negative_mask=negative,
            recolor_mask=recolor,
            color_changes=color_changes,
            total_diff=total_diff,
            grid_size=grid_size,
            defect=total_diff / grid_size,
            is_pure_recolor=(n_rec == total_diff and total_diff > 0),
            is_pure_additive=(n_pos == total_diff and total_diff > 0),
            is_pure_subtractive=(n_neg == total_diff and total_diff > 0),
            is_localized=is_localized,
            change_bbox=bbox,
            dominant_color_map=dominant_map,
        )

    def describe(self) -> str:
        """Human-readable description of the gradient."""
        parts = [f"defect={self.defect:.3f} ({self.total_diff}/{self.grid_size} px)"]
        n_pos = int(self.positive_mask.sum())
        n_neg = int(self.negative_mask.sum())
        n_rec = int(self.recolor_mask.sum())
        if n_pos: parts.append(f"R+={n_pos}")
        if n_neg: parts.append(f"R-={n_neg}")
        if n_rec: parts.append(f"recolor={n_rec}")
        if self.is_pure_recolor: parts.append("PURE_RECOLOR")
        if self.is_localized: parts.append("LOCALIZED")
        if self.dominant_color_map: parts.append(f"cmap={self.dominant_color_map}")
        return " | ".join(parts)


def cluster_by_transformation_signature(
    gradients: List[DiscreteGradient],
    threshold: float = 0.3
) -> List[List[int]]:
    """
    SGFE v2.1: Cluster training examples by their transformation signature.
    
    Theory (positive_Ricci_tensorizes): A global section exists only if all
    stalks belong to the same geometric class. Clustering ensures each TL run
    operates within a uniform symmetry group (coset).
    
    Uses hierarchical agglomerative clustering with Ward linkage and distance
    threshold τ. K-means is degenerate for n ≤ 5 examples; Ward handles small
    n robustly. Singleton clusters are merged back to avoid degenerate runs.
    
    Args:
        gradients: List of DiscreteGradient for each training example
        threshold: Distance threshold for clustering (default 0.3)
    
    Returns:
        List of clusters, where each cluster is a list of example indices
    """
    if len(gradients) <= 1:
        return [[i for i in range(len(gradients))]]
    
    # SGFE v2.7: Coarsened 3D transformation signature
    # Theory (SGC.Renormalization.Lumpability): Coarsen signature to ensure
    # nonzero median degree in the peer graph. Discretize volumes into buckets
    # and use transformation TYPE (add/erase/recolor) rather than exact ratios.
    # Goal: cosets with enough peers for cross-task validation, not singletons.
    signatures = []
    for grad in gradients:
        # Discretize volumes into 4 buckets: none(0), small(<0.1), medium(<0.3), large(>=0.3)
        def bucket(frac):
            if frac < 0.01:
                return 0.0
            elif frac < 0.1:
                return 0.25
            elif frac < 0.3:
                return 0.5
            else:
                return 1.0
        
        pos_frac = grad.positive_mask.sum() / max(grad.grid_size, 1)
        neg_frac = grad.negative_mask.sum() / max(grad.grid_size, 1)
        recolor_frac = grad.recolor_mask.sum() / max(grad.grid_size, 1)
        
        # 3D signature: (add_bucket, erase_bucket, pure_recolor)
        # Dropped recolor_frac as separate dim - correlated with pure_recolor
        sig = (
            bucket(pos_frac),
            bucket(neg_frac),
            1.0 if grad.is_pure_recolor or grad.total_diff == 0 else 0.0
        )
        signatures.append(sig)
    
    # Convert to numpy array for clustering
    sig_array = np.array(signatures)
    
    # If all signatures are identical, return single cluster
    if np.allclose(sig_array, sig_array[0]):
        return [[i for i in range(len(gradients))]]
    
    # Hierarchical agglomerative clustering (Ward linkage)
    try:
        from scipy.cluster.hierarchy import linkage, fcluster
        Z = linkage(sig_array, method='ward')
        labels = fcluster(Z, t=threshold, criterion='distance')
    except Exception:
        # Fallback: single cluster if clustering fails
        return [[i for i in range(len(gradients))]]
    
    # Group example indices by cluster label
    clusters_dict: Dict[int, List[int]] = {}
    for idx, label in enumerate(labels):
        clusters_dict.setdefault(int(label), []).append(idx)
    
    # Merge singleton clusters back (no isolated examples)
    result = []
    singletons = []
    for label, indices in clusters_dict.items():
        if len(indices) == 1:
            singletons.extend(indices)
        else:
            result.append(indices)
    
    if singletons:
        if result:
            result[0].extend(singletons)  # Merge into largest cluster
        else:
            result.append(singletons)  # All singletons = one cluster
    
    return result if result else [[i for i in range(len(gradients))]]


# =============================================================================
# 2. PROGRAM REPRESENTATION: AtomicOp + CompositeOp
# =============================================================================

@dataclass
class AtomicOp:
    """A single composable operation on a grid (np.ndarray -> np.ndarray)."""
    name: str
    apply_fn: Callable[[np.ndarray], np.ndarray]
    description: str = ""

    def apply(self, grid: np.ndarray) -> np.ndarray:
        return self.apply_fn(grid)

    def __repr__(self):
        return f"AtomicOp({self.name})"


@dataclass
class CompositeOp:
    """A chain of operations (a program)."""
    steps: List[AtomicOp] = field(default_factory=list)

    def apply(self, grid: np.ndarray) -> np.ndarray:
        result = grid.copy()
        for op in self.steps:
            result = op.apply(result)
        return result

    @property
    def depth(self) -> int:
        return len(self.steps)

    def describe(self) -> str:
        if not self.steps:
            return "Identity"
        parts = []
        for op in self.steps:
            if isinstance(op, CompositeOp):
                parts.append(op.describe())
            else:
                parts.append(op.name)
        return " -> ".join(parts)

    def __repr__(self):
        return f"Program[{self.describe()}]"


def identity_op() -> AtomicOp:
    return AtomicOp("identity", lambda g: g.copy(), "no-op")


# =============================================================================
# ROLE-BASED ATOMIC OPS (Phase 10: Object-Level Cohomology)
# =============================================================================
# 
# These operators satisfy the Natural Transformation property:
#   Apply(Lift(G)) == Lift(Apply(G))
# 
# By operating purely on topological roles (MAJORITY, MINORITY, ANCHOR),
# they are translation-invariant and have sheaf_energy ≈ 0 by construction.
#
# Theory (SGC.Computable.ObjectLifting):
#   - Role = canonical color assignment (bg, majority, minority, anchor_n)
#   - MorphFilter = morphological operation in lifted lattice space
#   - The op is "lowered" to grid space by detecting roles at apply-time
#

@dataclass
class RoleBasedAtomicOp:
    """
    An atomic operation defined on object-level roles, not pixel coordinates.
    
    Properties:
      - Translation invariant: same result regardless of object position
      - Sheaf-consistent: low energy by construction (operates in quotient space)
      - Composable: inherits Galois structure from morphological algebra
    
    The apply() method:
      1. Detects roles in input grid (dynamic, not memorized)
      2. Applies morphological filter in role-space
      3. Executes action on filtered objects
    
    This satisfies: Apply(Lift(G)) == Lift(Apply(G))
    """
    name: str
    role: str  # Target role: 'MAJORITY', 'MINORITY', 'ANCHOR_1', etc.
    morph_term_name: str  # E.g., 'γ(+,X)' for opening with cross SE
    action: str  # 'fill', 'erase', 'recolor'
    action_role: Optional[str] = None  # Role to use for color (e.g., 'ANCHOR_1' for fill)
    action_color: Optional[int] = None  # Fixed color (fallback if action_role not found)
    description: str = ""
    
    def apply(self, grid: np.ndarray) -> np.ndarray:
        """
        Apply the role-based operation.
        
        Key invariant: roles are detected dynamically at apply-time,
        ensuring the operation transfers across examples/tasks.
        """
        # 1. Detect roles in current grid (dynamic, not memorized)
        roles = detect_color_roles(grid)
        
        # 2. Find color for target role
        target_color = None
        for color, role_name in roles.items():
            if role_name.upper() == self.role.upper():
                target_color = color
                break
        
        if target_color is None:
            return grid.copy()  # Role not present, no-op
        
        # 3. Build scene graph and lift
        from arc_sgc_phase21 import SceneGraphBuilder
        from arc_morph_algebra import SceneGraphLifting, ROLE_TO_CHANNEL, MorphTerm, MorphOp, CANONICAL_SES
        
        # Convert grid to ARCGrid for builder
        from arc_sgc_phase8_3 import ARCGrid
        arc_grid = ARCGrid(torch.tensor(grid, dtype=torch.int64))
        
        builder = SceneGraphBuilder()
        sg = builder.build(arc_grid)
        
        lifting = SceneGraphLifting(max_canonical_size=16)
        lattice, canonical_objects = lifting.lift(sg, roles)
        
        # 4. Apply morphological filter in lifted space
        channel_idx = ROLE_TO_CHANNEL.get(self.role.upper(), 1)
        
        # Parse morph term from name (simplified: just opening with cross for now)
        term = self._parse_morph_term()
        if term is not None:
            transformed = lifting.apply_morph_op(lattice, term, channel=channel_idx)
        else:
            transformed = lattice
        
        # 5. Lower to object predicates (which objects survive the filter?)
        object_predicates = lifting.lower(transformed, lattice, canonical_objects)
        
        # 6. Execute action on filtered objects
        result = grid.copy()
        
        # Determine fill color from action_role or action_color
        fill_color = self.action_color
        if self.action_role is not None:
            for color, role_name in roles.items():
                if role_name.upper() == self.action_role.upper():
                    fill_color = color
                    break
        
        if fill_color is None:
            fill_color = 0  # Default to background
        
        # Apply action to objects that pass the filter
        for obj_id, passes_filter in object_predicates.items():
            if not passes_filter:
                continue
            
            obj = sg.objects.get(obj_id)
            if obj is None:
                continue
            
            # Get object mask in grid coordinates
            r1, c1, r2, c2 = obj.bbox
            obj_mask = np.zeros(grid.shape, dtype=bool)
            obj_mask[r1:r2, c1:c2] = obj.mask
            
            if self.action == 'fill':
                # Fill where object is AND currently background
                fill_mask = obj_mask & (result == 0)
                result[fill_mask] = fill_color
            elif self.action == 'erase':
                # Erase object to background
                result[obj_mask] = 0
            elif self.action == 'recolor':
                # Recolor object pixels
                result[obj_mask] = fill_color
        
        return result
    
    def _parse_morph_term(self):
        """Parse morph term from name string."""
        from arc_morph_algebra import MorphTerm, MorphOp, SE_CROSS, SE_SQUARE
        
        # Simple parsing for common patterns
        name = self.morph_term_name.lower()
        
        if 'open' in name or 'γ' in name:
            se = SE_CROSS if '+' in name or 'cross' in name else SE_SQUARE
            return MorphTerm(op=MorphOp.OPEN, se=se)
        elif 'close' in name or 'φ' in name:
            se = SE_CROSS if '+' in name or 'cross' in name else SE_SQUARE
            return MorphTerm(op=MorphOp.CLOSE, se=se)
        elif 'erode' in name or 'ε' in name:
            se = SE_CROSS if '+' in name or 'cross' in name else SE_SQUARE
            return MorphTerm(op=MorphOp.ERODE, se=se)
        elif 'dilate' in name or 'δ' in name:
            se = SE_CROSS if '+' in name or 'cross' in name else SE_SQUARE
            return MorphTerm(op=MorphOp.DILATE, se=se)
        elif 'gradient' in name or '∂' in name:
            se = SE_CROSS if '+' in name or 'cross' in name else SE_SQUARE
            return MorphTerm(op=MorphOp.GRADIENT, se=se)
        
        # Identity (no filtering)
        return None
    
    def __repr__(self):
        return f"RoleBasedOp({self.name})"


def make_role_based_op(
    role: str,
    morph_term_name: str,
    action: str,
    action_role: Optional[str] = None,
    action_color: Optional[int] = None,
) -> AtomicOp:
    """
    Factory function to create an AtomicOp from a RoleBasedAtomicOp.
    
    This wraps the role-based logic in the standard AtomicOp interface
    for compatibility with CompositeOp and the existing solver infrastructure.
    """
    role_op = RoleBasedAtomicOp(
        name=f"role_{action}({role}|{morph_term_name})",
        role=role,
        morph_term_name=morph_term_name,
        action=action,
        action_role=action_role,
        action_color=action_color,
        description=f"Apply {action} to {role} objects filtered by {morph_term_name}",
    )
    
    return AtomicOp(
        name=role_op.name,
        apply_fn=role_op.apply,
        description=role_op.description,
    )


# =============================================================================
# 3. OPERATOR LIBRARY: Proposes AtomicOps guided by gradient hints
# =============================================================================

class OperatorLibrary:
    """
    Proposes atomic operations based on the discrete gradient.

    Unlike the HeuristicSolverAdapter (which tries every operation blindly),
    this library uses gradient HINTS to prioritize operations that are likely
    to reduce the residual.
    """

    def propose(
        self,
        current: np.ndarray,
        target: np.ndarray,
        gradient: DiscreteGradient,
        task: ARCTask,
    ) -> List[Tuple[AtomicOp, float]]:
        """
        Return list of (op, expected_information_gain) sorted by IG descending.

        Each proposed op is evaluated on the actual current->target pair
        to compute real IG, not just heuristic IG.
        """
        candidates: List[AtomicOp] = []

        # --- TRAINING-DERIVED OPS FIRST (most general, survive deduplication) ---
        # Training-consistent PREDICATED ops (consensus ILP across examples)
        # Only run on same-shape tasks with manageable color count to limit cost
        n_colors = len(set(current.flat) | set(target.flat)) if current.shape == target.shape else 99
        if n_colors <= 6:
            candidates.extend(self._training_predicated_ops(task))
        # Training-derived unconditional color maps
        candidates.extend(self._training_color_maps(task))

        # --- Gradient-guided proposals ---

        # Color maps from gradient (example-specific, less general)
        if gradient.dominant_color_map:
            candidates.append(self._make_color_map(gradient.dominant_color_map))
        for (f, t), cnt in gradient.color_changes.items():
            if cnt >= 2:
                candidates.append(self._make_single_recolor(f, t))

        # Geometric transforms (always worth trying)
        candidates.extend(self._geometric_ops())

        # Role-based ops (color-role invariant, fully abstract)
        candidates.append(_make_role_fill_cross())
        candidates.append(_make_role_fill_adj())
        candidates.append(_make_role_erase_minority())

        # Crop operations (if shapes differ or content bbox hints)
        if current.shape != target.shape:
            candidates.extend(self._crop_ops(current, target))
        candidates.extend(self._content_crop_ops(current, task))

        # Shift/translate (common in ARC)
        candidates.extend(self._shift_ops(current, target))

        # Fill operations (if gradient is mostly additive)
        if gradient.is_pure_additive or int(gradient.positive_mask.sum()) > 0:
            candidates.extend(self._fill_ops(current, target, gradient))

        # Erase operations (if gradient is mostly subtractive)
        if gradient.is_pure_subtractive or int(gradient.negative_mask.sum()) > 0:
            candidates.extend(self._erase_ops(current, target, gradient))

        # Object extraction
        candidates.extend(self._extract_ops(current))

        # Line-connect (ray-casting between objects)
        candidates.extend(self._line_connect_ops(current, target))

        # Scale/tile
        candidates.extend(self._scale_ops(current, target))

        # PREDICATED OPS (conditional logic via ILP on residual masks)
        if current.shape == target.shape and gradient.total_diff > 0:
            candidates.extend(self._predicated_ops(current, target, gradient))

        # --- Score each candidate by actual information gain ---
        scored: List[Tuple[AtomicOp, float]] = []
        current_defect = gradient.defect
        seen_results = set()

        for op in candidates:
            try:
                result = op.apply(current)
                if result.shape != target.shape:
                    continue
                result_key = result.tobytes()
                if result_key in seen_results:
                    continue
                seen_results.add(result_key)
                new_defect = np.sum(result != target) / max(target.size, 1)
                ig = current_defect - new_defect
                if ig > 1e-6:  # Only keep ops with positive IG
                    scored.append((op, ig))
            except Exception:
                continue

        scored.sort(key=lambda x: -x[1])
        return scored

    # --- Operation factories ---

    def _make_color_map(self, mapping: Dict[int, int]) -> AtomicOp:
        m = dict(mapping)
        def apply(grid):
            result = grid.copy()
            for f, t in m.items():
                result[grid == f] = t
            return result
        desc = ",".join(f"{f}->{t}" for f, t in m.items())
        return AtomicOp(f"cmap({desc})", apply, f"color map {m}")

    def _make_single_recolor(self, f: int, t: int) -> AtomicOp:
        def apply(grid):
            result = grid.copy()
            result[grid == f] = t
            return result
        return AtomicOp(f"recolor({f}->{t})", apply)

    def _geometric_ops(self) -> List[AtomicOp]:
        ops = []
        for k, name in [(1, "rot90"), (2, "rot180"), (3, "rot270")]:
            kk = k
            ops.append(AtomicOp(name, lambda g, _k=kk: np.rot90(g, _k).copy()))
        ops.append(AtomicOp("flip_h", lambda g: np.fliplr(g).copy()))
        ops.append(AtomicOp("flip_v", lambda g: np.flipud(g).copy()))
        if True:  # transpose only for square or when shapes might match
            ops.append(AtomicOp("transpose", lambda g: g.T.copy()))
        return ops

    def _crop_ops(self, current: np.ndarray, target: np.ndarray) -> List[AtomicOp]:
        """Propose crops when shapes differ."""
        ops = []
        tH, tW = target.shape
        cH, cW = current.shape

        # Crop to target shape from each corner/center
        if tH <= cH and tW <= cW:
            for r_off in [0, (cH - tH) // 2, cH - tH]:
                for c_off in [0, (cW - tW) // 2, cW - tW]:
                    if r_off < 0 or c_off < 0:
                        continue
                    ro, co = int(r_off), int(c_off)
                    h, w = tH, tW
                    ops.append(AtomicOp(
                        f"crop({ro},{co},{h},{w})",
                        lambda g, _r=ro, _c=co, _h=h, _w=w: g[_r:_r+_h, _c:_c+_w].copy()
                    ))

        # Content-based crop
        non_bg = np.argwhere(current != BG)
        if len(non_bg) > 0:
            r1, c1 = non_bg.min(axis=0)
            r2, c2 = non_bg.max(axis=0) + 1
            if (r2 - r1, c2 - c1) == (tH, tW):
                r1i, c1i, r2i, c2i = int(r1), int(c1), int(r2), int(c2)
                ops.append(AtomicOp(
                    f"crop_content({r1i},{c1i})",
                    lambda g, _r1=r1i, _c1=c1i, _r2=r2i, _c2=c2i: g[_r1:_r2, _c1:_c2].copy()
                ))
        return ops

    def _content_crop_ops(self, current: np.ndarray, task: ARCTask) -> List[AtomicOp]:
        """Crop to content bounding box — DYNAMIC (recomputed per grid)."""
        ops = []
        # Dynamic crop to non-bg content
        non_bg = np.argwhere(current != BG)
        if len(non_bg) > 0:
            ops.append(AtomicOp("crop_content", _dynamic_crop_content))
        # Dynamic per-color crops
        colors_present = set(current.flat) - {BG}
        for color in colors_present:
            cc = int(color)
            ops.append(AtomicOp(
                f"crop_color_{cc}",
                lambda g, _c=cc: _dynamic_crop_color(g, _c)
            ))
        return ops

    def _shift_ops(self, current: np.ndarray, target: np.ndarray) -> List[AtomicOp]:
        """Propose shift operations."""
        ops = []
        H, W = current.shape
        for dr in range(-min(H-1, 5), min(H, 6)):
            for dc in range(-min(W-1, 5), min(W, 6)):
                if dr == 0 and dc == 0:
                    continue
                ddr, ddc = dr, dc
                ops.append(AtomicOp(
                    f"shift({ddr},{ddc})",
                    lambda g, _dr=ddr, _dc=ddc: np.roll(np.roll(g, _dr, axis=0), _dc, axis=1)
                ))
        return ops

    def _fill_ops(self, current: np.ndarray, target: np.ndarray,
                  gradient: DiscreteGradient) -> List[AtomicOp]:
        """Propose fill operations for additive residuals."""
        ops = []
        # NOTE: We do NOT include fill_R+ (paint specific target pixels)
        # because it memorizes positions from one example and can't generalize.

        # Fill enclosed regions dynamically (computes from grid structure)
        ops.append(AtomicOp(
            "fill_holes",
            _dynamic_fill_holes,
            "fill enclosed bg regions with neighbor color"
        ))
        return ops

    def _erase_ops(self, current: np.ndarray, target: np.ndarray,
                   gradient: DiscreteGradient) -> List[AtomicOp]:
        """Propose erase operations for subtractive residuals."""
        # NOTE: We do NOT include erase_R- (erase specific positions)
        # because it memorizes positions from one example and can't generalize.
        # Color-based erasure (erase all pixels of a specific color) DOES generalize.
        ops = []
        if gradient.is_pure_subtractive and gradient.color_changes:
            # Find colors being erased (mapped to BG)
            for (f, t), cnt in gradient.color_changes.items():
                if t == BG and cnt >= 2:
                    ff = f
                    ops.append(AtomicOp(
                        f"erase_color({ff})",
                        lambda g, _c=ff: _fill_mask(g, g == _c, BG),
                        f"erase all pixels of color {ff}"
                    ))
        return ops

    def _extract_ops(self, current: np.ndarray) -> List[AtomicOp]:
        """Extract objects — DYNAMIC by property (color, largest, smallest)."""
        ops = []
        # Extract by color (dynamic: finds bbox of color at apply time)
        colors_present = set(current.flat) - {BG}
        for color in colors_present:
            cc = int(color)
            ops.append(AtomicOp(
                f"extract_color_{cc}",
                lambda g, _c=cc: _dynamic_crop_color(g, _c)
            ))
        # Extract largest / smallest object (dynamic)
        ops.append(AtomicOp("extract_largest", _dynamic_extract_largest))
        ops.append(AtomicOp("extract_smallest", _dynamic_extract_smallest))
        return ops

    def _scale_ops(self, current: np.ndarray, target: np.ndarray) -> List[AtomicOp]:
        """Propose scale/tile operations."""
        ops = []
        cH, cW = current.shape
        tH, tW = target.shape

        # Integer upscale
        for k in [2, 3, 4]:
            if tH == cH * k and tW == cW * k:
                kk = k
                ops.append(AtomicOp(
                    f"upscale_{kk}x",
                    lambda g, _k=kk: np.repeat(np.repeat(g, _k, axis=0), _k, axis=1)
                ))
            # Tile
            if tH == cH * k and tW == cW:
                kk = k
                ops.append(AtomicOp(
                    f"tile_v_{kk}",
                    lambda g, _k=kk: np.tile(g, (_k, 1))
                ))
            if tW == cW * k and tH == cH:
                kk = k
                ops.append(AtomicOp(
                    f"tile_h_{kk}",
                    lambda g, _k=kk: np.tile(g, (1, _k))
                ))

        # Integer downscale
        for k in [2, 3, 4]:
            if cH == tH * k and cW == tW * k:
                kk = k
                ops.append(AtomicOp(
                    f"downscale_{kk}x",
                    lambda g, _k=kk: g[::_k, ::_k].copy()
                ))
        return ops

    def _line_connect_ops(self, current: np.ndarray, target: np.ndarray) -> List[AtomicOp]:
        """
        Propose line-drawing operations that connect objects.

        Common ARC pattern: a small 'marker' object indicates where to draw
        a line toward a larger 'anchor' object. The line uses the marker's color.

        This generates DYNAMIC ops that:
          1. Detect objects in the grid
          2. Find small markers and large anchors
          3. Draw lines between aligned pairs
        """
        ops = []
        if current.shape != target.shape:
            return ops

        # Detect objects using dynamic bg detection (handles non-zero backgrounds)
        objects, bg = _detect_objects_np(current)
        if len(objects) < 2:
            return ops

        small_objs = [(c, bb, m, cen) for c, bb, m, cen in objects if m <= 3]
        large_objs = [(c, bb, m, cen) for c, bb, m, cen in objects if m > 3]

        if not small_objs or not large_objs:
            return ops

        # Generate dynamic line-connect ops
        # ALL first (most general, survives deduplication over directional variants)
        ops.append(AtomicOp(
            "line_connect_all",
            _dynamic_line_connect_all,
            "draw lines (h+v) from small markers toward large objects"
        ))
        ops.append(AtomicOp(
            "line_connect_h",
            _dynamic_line_connect_horizontal,
            "draw horizontal lines from small markers toward large objects"
        ))
        ops.append(AtomicOp(
            "line_connect_v",
            _dynamic_line_connect_vertical,
            "draw vertical lines from small markers toward large objects"
        ))
        return ops

    def _training_predicated_ops(
        self,
        task: ARCTask,
    ) -> List[AtomicOp]:
        """
        Synthesize predicated ops that are CONSISTENT across ALL training examples.

        Algorithm (consensus ILP):
          1. For each training example, compute gradient and change masks
          2. Group changes by type (recolor src->dst, fill with color, erase color)
          3. For each change group, run ILP on each example independently
          4. Find predicate NAMES that appear with F1 > threshold in ALL examples
          5. Create predicated ops from consensus predicates

        These are the most generalizable predicated ops because they
        explain the same spatial pattern across independent instances.
        """
        ops: List[AtomicOp] = []
        synth = PredicateSynthesizer(min_f1=0.5)

        if len(task.train_examples) < 2:
            return ops

        # Step 1-2: Collect change groups per example
        # Key = change_type (e.g., "recolor_1_3", "fill_2", "erase_5")
        # Value = list of (example_idx, change_mask, input_grid)
        change_groups: Dict[str, List[Tuple[int, np.ndarray, np.ndarray]]] = {}

        for idx, ex in enumerate(task.train_examples):
            inp = ex.input_grid.to_numpy()
            tgt = ex.output_grid.to_numpy()
            if inp.shape != tgt.shape:
                continue

            grad = DiscreteGradient.compute(inp, tgt)
            if grad.total_diff == 0:
                continue

            # Recolor groups
            if grad.recolor_mask.any():
                rc_pos = np.argwhere(grad.recolor_mask)
                for r, c in rc_pos:
                    key = f"recolor_{int(inp[r,c])}_{int(tgt[r,c])}"
                    change_groups.setdefault(key, [])
                    # Add to existing mask or create new
                    found = False
                    for entry in change_groups[key]:
                        if entry[0] == idx:
                            entry[1][r, c] = True
                            found = True
                            break
                    if not found:
                        mask = np.zeros(inp.shape, dtype=bool)
                        mask[r, c] = True
                        change_groups[key].append((idx, mask, inp))

            # Fill groups (bg -> color)
            if grad.positive_mask.any():
                pos = np.argwhere(grad.positive_mask)
                for r, c in pos:
                    key = f"fill_{int(tgt[r,c])}"
                    change_groups.setdefault(key, [])
                    found = False
                    for entry in change_groups[key]:
                        if entry[0] == idx:
                            entry[1][r, c] = True
                            found = True
                            break
                    if not found:
                        mask = np.zeros(inp.shape, dtype=bool)
                        mask[r, c] = True
                        change_groups[key].append((idx, mask, inp))

            # Erase groups (color -> bg)
            if grad.negative_mask.any():
                neg = np.argwhere(grad.negative_mask)
                for r, c in neg:
                    key = f"erase_{int(inp[r,c])}"
                    change_groups.setdefault(key, [])
                    found = False
                    for entry in change_groups[key]:
                        if entry[0] == idx:
                            entry[1][r, c] = True
                            found = True
                            break
                    if not found:
                        mask = np.zeros(inp.shape, dtype=bool)
                        mask[r, c] = True
                        change_groups[key].append((idx, mask, inp))

        n_examples = len(task.train_examples)

        # Step 3-4: For each change group, find consensus predicates
        for change_key, entries in change_groups.items():
            # Only consider groups present in ALL (or most) examples
            example_indices = set(e[0] for e in entries)
            if len(example_indices) < max(2, n_examples - 1):
                continue

            # Run ILP on each example independently
            pred_scores: Dict[str, List[float]] = {}  # pred_name -> [f1 per example]
            for ex_idx, mask, grid in entries:
                scored = synth.synthesize(grid, mask)
                for sp in scored[:10]:
                    pred_scores.setdefault(sp.name, []).append(sp.f1)

            # Find predicates with high F1 across ALL examples in this group
            for pred_name, f1_list in pred_scores.items():
                if len(f1_list) < len(example_indices):
                    continue  # predicate not found in all examples
                min_f1 = min(f1_list)
                avg_f1 = sum(f1_list) / len(f1_list)
                if min_f1 < 0.5 or avg_f1 < 0.7:
                    continue

                # Create the appropriate predicated op
                parts = change_key.split("_")
                if parts[0] == "recolor" and len(parts) >= 3:
                    src, dst = int(parts[1]), int(parts[2])
                    ops.append(_make_predicated_recolor(pred_name, src, dst))
                elif parts[0] == "fill" and len(parts) >= 2:
                    fc = int(parts[1])
                    ops.append(_make_predicated_fill(pred_name, fc))
                elif parts[0] == "erase" and len(parts) >= 2:
                    ec = int(parts[1])
                    ops.append(_make_predicated_erase(pred_name, ec))

        # =================================================================
        # COLOR-PARAMETRIC CONSENSUS (Phase 5)
        # =================================================================
        # The concrete pass above groups by exact color (fill_3, fill_2).
        # When the same PREDICATE appears with different colors across
        # examples, the concrete groups each have too few examples to
        # reach consensus. This second pass merges them.
        #
        # SGC Theory: The orbit (spatial predicate) is fixed; only the
        # representative (color) varies. We quotient by S_10 (color perm).
        # =================================================================
        
        # Collect per-example (change_type, predicate, color) triples
        # from the ILP runs we already did
        fill_pred_per_example: Dict[str, Dict[int, int]] = {}   # pred -> {ex_idx -> fill_color}
        erase_pred_per_example: Dict[str, Dict[int, int]] = {}  # pred -> {ex_idx -> erase_color}
        
        for change_key, entries in change_groups.items():
            parts = change_key.split("_")
            example_indices = set(e[0] for e in entries)
            
            # Run ILP on each example
            for ex_idx, mask, grid in entries:
                scored = synth.synthesize(grid, mask)
                for sp in scored[:5]:
                    if sp.f1 < 0.5:
                        continue
                    if parts[0] == "fill" and len(parts) >= 2:
                        fc = int(parts[1])
                        fill_pred_per_example.setdefault(sp.name, {})[ex_idx] = fc
                    elif parts[0] == "erase" and len(parts) >= 2:
                        ec = int(parts[1])
                        erase_pred_per_example.setdefault(sp.name, {})[ex_idx] = ec
        
        # Find predicates that appear in most examples but with DIFFERENT colors
        for pred_name, ex_colors in fill_pred_per_example.items():
            if len(ex_colors) < max(2, n_examples - 1):
                continue
            unique_colors = set(ex_colors.values())
            if len(unique_colors) > 1:
                # Same predicate, different colors => dynamic fill
                ops.append(_make_dynamic_fill(pred_name))
        
        for pred_name, ex_colors in erase_pred_per_example.items():
            if len(ex_colors) < max(2, n_examples - 1):
                continue
            unique_colors = set(ex_colors.values())
            if len(unique_colors) > 1:
                # Same predicate, different colors => dynamic erase
                ops.append(_make_dynamic_erase(pred_name))

        return ops

    def _predicated_ops(
        self,
        current: np.ndarray,
        target: np.ndarray,
        gradient: DiscreteGradient,
    ) -> List[AtomicOp]:
        """
        Synthesize CONDITIONAL operations via ILP on the residual mask.

        For each type of change (recolor, fill, erase), find spatial predicates
        that discriminate changed pixels from unchanged ones, then build
        predicated ops that apply the change only where the predicate is true.
        """
        ops: List[AtomicOp] = []
        synth = PredicateSynthesizer(min_f1=0.4)

        # Precompute predicates once for this grid
        predicates = _compute_pixel_predicates(current)

        # --- Predicated RECOLOR: for each (from_color, to_color) pair ---
        # Group changed pixels by their color transition
        recolor_groups: Dict[Tuple[int, int], np.ndarray] = {}
        if gradient.recolor_mask.any():
            rc_positions = np.argwhere(gradient.recolor_mask)
            for r, c in rc_positions:
                key = (int(current[r, c]), int(target[r, c]))
                if key not in recolor_groups:
                    recolor_groups[key] = np.zeros(current.shape, dtype=bool)
                recolor_groups[key][r, c] = True

        for (src, dst), change_mask in recolor_groups.items():
            # Find predicate explaining WHERE this recolor happens
            # Target mask: pixels of src color that SHOULD change
            scored = synth.synthesize(current, change_mask, predicates)
            for sp in scored[:3]:  # top 3 predicates
                ops.append(_make_predicated_recolor(sp.name, src, dst))

        # --- Predicated FILL: bg pixels that should become colored ---
        if gradient.positive_mask.any():
            # Group by target color
            fill_groups: Dict[int, np.ndarray] = {}
            pos_positions = np.argwhere(gradient.positive_mask)
            for r, c in pos_positions:
                tc = int(target[r, c])
                if tc not in fill_groups:
                    fill_groups[tc] = np.zeros(current.shape, dtype=bool)
                fill_groups[tc][r, c] = True

            for fill_color, fill_mask in fill_groups.items():
                scored = synth.synthesize(current, fill_mask, predicates)
                for sp in scored[:3]:
                    ops.append(_make_predicated_fill(sp.name, fill_color))

        # --- Predicated ERASE: colored pixels that should become bg ---
        if gradient.negative_mask.any():
            erase_groups: Dict[int, np.ndarray] = {}
            neg_positions = np.argwhere(gradient.negative_mask)
            for r, c in neg_positions:
                ec = int(current[r, c])
                if ec not in erase_groups:
                    erase_groups[ec] = np.zeros(current.shape, dtype=bool)
                erase_groups[ec][r, c] = True

            for erase_color, erase_mask in erase_groups.items():
                scored = synth.synthesize(current, erase_mask, predicates)
                for sp in scored[:3]:
                    ops.append(_make_predicated_erase(sp.name, erase_color))

        return ops

    def _training_color_maps(self, task: ARCTask) -> List[AtomicOp]:
        """Derive color mappings from training examples."""
        ops = []
        if not task.train_examples:
            return ops

        # Collect consistent color changes across training
        global_changes: Dict[Tuple[int,int], int] = {}
        for ex in task.train_examples:
            inp = ex.input_grid.to_numpy()
            out = ex.output_grid.to_numpy()
            if inp.shape != out.shape:
                continue
            diff = inp != out
            if not diff.any():
                continue
            for f, t in zip(inp[diff].flat, out[diff].flat):
                key = (int(f), int(t))
                global_changes[key] = global_changes.get(key, 0) + 1

        if not global_changes:
            return ops

        # Build a consistent mapping
        fwd: Dict[int, int] = {}
        for (f, t), cnt in sorted(global_changes.items(), key=lambda x: -x[1]):
            if f not in fwd:
                fwd[f] = t
        if fwd:
            ops.append(self._make_color_map(fwd))
        return ops


def _fill_mask(grid: np.ndarray, mask: np.ndarray, color: int) -> np.ndarray:
    result = grid.copy()
    result[mask] = color
    return result


def _dynamic_crop_content(grid: np.ndarray) -> np.ndarray:
    """Crop to bounding box of non-background content. Dynamic per grid."""
    non_bg = np.argwhere(grid != BG)
    if len(non_bg) == 0:
        return grid.copy()
    r1, c1 = non_bg.min(axis=0)
    r2, c2 = non_bg.max(axis=0) + 1
    return grid[r1:r2, c1:c2].copy()


def _dynamic_crop_color(grid: np.ndarray, color: int) -> np.ndarray:
    """Crop to bounding box of a specific color. Dynamic per grid."""
    positions = np.argwhere(grid == color)
    if len(positions) == 0:
        return grid.copy()
    r1, c1 = positions.min(axis=0)
    r2, c2 = positions.max(axis=0) + 1
    return grid[r1:r2, c1:c2].copy()


def _dynamic_extract_largest(grid: np.ndarray) -> np.ndarray:
    """Extract the largest non-background connected component."""
    config = ARCPhase83Config()
    arc_grid = ARCGrid(torch.tensor(grid, dtype=torch.long))
    objects = detect_objects(arc_grid, config)
    if not objects:
        return grid.copy()
    largest = max(objects, key=lambda o: o.mass)
    r1, c1, r2, c2 = largest.bbox
    return grid[r1:r2, c1:c2].copy()


def _dynamic_extract_smallest(grid: np.ndarray) -> np.ndarray:
    """Extract the smallest non-trivial connected component."""
    config = ARCPhase83Config()
    arc_grid = ARCGrid(torch.tensor(grid, dtype=torch.long))
    objects = detect_objects(arc_grid, config)
    non_trivial = [o for o in objects if o.mass > 1]
    if not non_trivial:
        return grid.copy()
    smallest = min(non_trivial, key=lambda o: o.mass)
    r1, c1, r2, c2 = smallest.bbox
    return grid[r1:r2, c1:c2].copy()


def _detect_objects_np(grid: np.ndarray):
    """Lightweight object detection returning list of (color, bbox, mass, centroid)."""
    objects = []
    colors = set(grid.flat)
    bg = 0
    # Find most common color as bg
    vals, counts = np.unique(grid, return_counts=True)
    bg = vals[np.argmax(counts)]

    for c in colors:
        if c == bg:
            continue
        mask = (grid == int(c)).astype(np.int32)
        labeled, n = ndimage.label(mask)
        for comp_id in range(1, n + 1):
            comp = labeled == comp_id
            mass = int(comp.sum())
            rows = np.any(comp, axis=1)
            cols = np.any(comp, axis=0)
            r_idx = np.where(rows)[0]
            c_idx = np.where(cols)[0]
            if len(r_idx) == 0:
                continue
            bbox = (r_idx[0], c_idx[0], r_idx[-1] + 1, c_idx[-1] + 1)
            ys, xs = np.where(comp)
            centroid = (float(ys.mean()), float(xs.mean()))
            objects.append((int(c), bbox, mass, centroid))
    return objects, bg


def _dynamic_line_connect_horizontal(grid: np.ndarray) -> np.ndarray:
    """Draw horizontal lines from small markers toward nearest large object."""
    objects, bg = _detect_objects_np(grid)
    if len(objects) < 2:
        return grid.copy()

    small = [(c, bb, m, cen) for c, bb, m, cen in objects if m <= 3]
    large = [(c, bb, m, cen) for c, bb, m, cen in objects if m > 3]
    if not small or not large:
        return grid.copy()

    result = grid.copy()
    for s_color, s_bbox, s_mass, s_cen in small:
        s_row = int(round(s_cen[0]))
        s_col = int(round(s_cen[1]))
        # Find nearest large object in the same row band
        best_large = None
        best_dist = float('inf')
        for l_color, l_bbox, l_mass, l_cen in large:
            lr1, lc1, lr2, lc2 = l_bbox
            # Check if marker row overlaps with large object row range
            if lr1 <= s_row < lr2:
                # Horizontal distance
                if s_col < lc1:
                    dist = lc1 - s_col
                elif s_col >= lc2:
                    dist = s_col - lc2 + 1
                else:
                    dist = 0
                if dist < best_dist and dist > 0:
                    best_dist = dist
                    best_large = (l_color, l_bbox)

        if best_large is not None:
            l_color, (lr1, lc1, lr2, lc2) = best_large
            if s_col < lc1:
                # Draw line from marker to left edge of large object
                for c in range(s_col, lc1):
                    if result[s_row, c] == bg:
                        result[s_row, c] = s_color
            elif s_col >= lc2:
                for c in range(lc2, s_col + 1):
                    if result[s_row, c] == bg:
                        result[s_row, c] = s_color
    return result


def _dynamic_line_connect_vertical(grid: np.ndarray) -> np.ndarray:
    """Draw vertical lines from small markers toward nearest large object."""
    objects, bg = _detect_objects_np(grid)
    if len(objects) < 2:
        return grid.copy()

    small = [(c, bb, m, cen) for c, bb, m, cen in objects if m <= 3]
    large = [(c, bb, m, cen) for c, bb, m, cen in objects if m > 3]
    if not small or not large:
        return grid.copy()

    result = grid.copy()
    for s_color, s_bbox, s_mass, s_cen in small:
        s_row = int(round(s_cen[0]))
        s_col = int(round(s_cen[1]))
        # Find nearest large object in the same column band
        best_large = None
        best_dist = float('inf')
        for l_color, l_bbox, l_mass, l_cen in large:
            lr1, lc1, lr2, lc2 = l_bbox
            if lc1 <= s_col < lc2:
                if s_row < lr1:
                    dist = lr1 - s_row
                elif s_row >= lr2:
                    dist = s_row - lr2 + 1
                else:
                    dist = 0
                if dist < best_dist and dist > 0:
                    best_dist = dist
                    best_large = (l_color, l_bbox)

        if best_large is not None:
            l_color, (lr1, lc1, lr2, lc2) = best_large
            if s_row < lr1:
                for r in range(s_row, lr1):
                    if result[r, s_col] == bg:
                        result[r, s_col] = s_color
            elif s_row >= lr2:
                for r in range(lr2, s_row + 1):
                    if result[r, s_col] == bg:
                        result[r, s_col] = s_color
    return result


def _dynamic_line_connect_all(grid: np.ndarray) -> np.ndarray:
    """Draw H+V lines from markers to objects, computed from ORIGINAL grid."""
    objects, bg = _detect_objects_np(grid)
    if len(objects) < 2:
        return grid.copy()

    small = [(c, bb, m, cen) for c, bb, m, cen in objects if m <= 3]
    large = [(c, bb, m, cen) for c, bb, m, cen in objects if m > 3]
    if not small or not large:
        return grid.copy()

    result = grid.copy()
    for s_color, s_bbox, s_mass, s_cen in small:
        s_row = int(round(s_cen[0]))
        s_col = int(round(s_cen[1]))
        # Try both H and V against ORIGINAL objects
        for l_color, l_bbox, l_mass, l_cen in large:
            lr1, lc1, lr2, lc2 = l_bbox
            # Horizontal: marker row overlaps with large object
            if lr1 <= s_row < lr2:
                if s_col < lc1:
                    for c in range(s_col, lc1):
                        if result[s_row, c] == bg:
                            result[s_row, c] = s_color
                elif s_col >= lc2:
                    for c in range(lc2, s_col + 1):
                        if result[s_row, c] == bg:
                            result[s_row, c] = s_color
            # Vertical: marker col overlaps with large object
            if lc1 <= s_col < lc2:
                if s_row < lr1:
                    for r in range(s_row, lr1):
                        if result[r, s_col] == bg:
                            result[r, s_col] = s_color
                elif s_row >= lr2:
                    for r in range(lr2, s_row + 1):
                        if result[r, s_col] == bg:
                            result[r, s_col] = s_color
    return result


def _dynamic_fill_holes(grid: np.ndarray) -> np.ndarray:
    """Fill enclosed background regions with the dominant neighbor color."""
    try:
        from scipy.ndimage import binary_fill_holes, label, binary_dilation
    except ImportError:
        return grid.copy()

    result = grid.copy()
    fg_mask = grid != BG
    if not fg_mask.any():
        return result

    filled = binary_fill_holes(fg_mask)
    holes = filled & ~fg_mask
    if not holes.any():
        return result

    labeled, n = label(holes)
    for region_id in range(1, min(n + 1, 20)):
        region = labeled == region_id
        border = binary_dilation(region) & ~region & fg_mask
        if border.any():
            neighbor_colors = grid[border]
            fg_neighbors = neighbor_colors[neighbor_colors > 0]
            if len(fg_neighbors) > 0:
                fill_color = int(np.bincount(fg_neighbors).argmax())
                result[region] = fill_color
    return result


# =============================================================================
# 3a. PREDICATE DSL: Open-Ended Predicate Synthesis
# =============================================================================
#
# SGC GROUNDING: The predicate vocabulary is the microstate space.
# A fixed vocabulary limits what macrostate partitions can be discovered.
# The DSL makes the predicate space generative (open-ended) by composing
# ~12 atomic primitives, enabling the renormalization functor to discover
# predicates that no hardcoded recipe anticipated.
#
# ARCHITECTURE:
#   PredicateExpr = a composable program: grid -> boolean mask
#   Beam search over DSL compositions: atoms -> unary(atom) -> binary(u,u)
#   Each level scored by F1 against residual mask, top-k kept
#
# This replaces the closed-world vocabulary search with an open-ended
# predicate synthesizer. The existing operation synthesis stays the same.
# =============================================================================


class PredicateExpr:
    """
    A composable predicate expression that can be evaluated on any grid.

    Unlike a static boolean mask, a PredicateExpr is a PROGRAM — a callable
    that takes a grid and returns a mask. This means:
    1. It can compute intermediate results (find objects, trace paths)
    2. It generalizes to unseen grids (not tied to training data)
    3. It composes: unary(atom), binary(expr, expr), etc.
    """
    __slots__ = ('name', '_fn')

    def __init__(self, name: str, fn: Callable[[np.ndarray], np.ndarray]):
        self.name = name
        self._fn = fn

    def evaluate(self, grid: np.ndarray) -> np.ndarray:
        """Evaluate this predicate on a grid, returning a boolean mask."""
        return self._fn(grid)

    def __repr__(self):
        return f"Pred({self.name})"


# ---- Atom constructors (Level 0) ----

def pred_color(c: int) -> PredicateExpr:
    """Pixels of color c."""
    return PredicateExpr(f"color_{c}", lambda g, _c=c: g == _c)

def pred_fg() -> PredicateExpr:
    """Foreground pixels (non-zero)."""
    return PredicateExpr("fg", lambda g: g != BG)

def pred_bg() -> PredicateExpr:
    """Background pixels (zero)."""
    return PredicateExpr("bg", lambda g: g == BG)

def pred_border(k: int = 0) -> PredicateExpr:
    """Pixels within k of the grid border."""
    def fn(g, _k=k):
        H, W = g.shape
        m = np.zeros((H, W), dtype=bool)
        m[:_k+1, :] = True; m[-(_k+1):, :] = True
        m[:, :_k+1] = True; m[:, -(_k+1):] = True
        return m
    return PredicateExpr(f"border_{k}" if k > 0 else "border", fn)

def pred_border_row() -> PredicateExpr:
    """Pixels on the first or last row."""
    def fn(g):
        m = np.zeros(g.shape, dtype=bool)
        m[0, :] = True; m[-1, :] = True
        return m
    return PredicateExpr("border_row", fn)

def pred_border_col() -> PredicateExpr:
    """Pixels on the first or last column."""
    def fn(g):
        m = np.zeros(g.shape, dtype=bool)
        m[:, 0] = True; m[:, -1] = True
        return m
    return PredicateExpr("border_col", fn)


# ---- Unary operators (Level 0 -> Level 1) ----

def pred_adjacent(p: PredicateExpr, conn: int = 8) -> PredicateExpr:
    """Pixels adjacent to P (not in P themselves)."""
    def fn(g, _p=p, _conn=conn):
        mask = _p.evaluate(g).astype(np.float32)
        if _conn == 4:
            kernel = np.array([[0,1,0],[1,0,1],[0,1,0]], dtype=np.float32)
        else:
            kernel = np.ones((3,3), dtype=np.float32)
            kernel[1,1] = 0
        adj = ndimage.convolve(mask, kernel, mode='constant', cval=0.0)
        return (adj > 0) & ~_p.evaluate(g)
    suffix = "" if conn == 8 else f",{conn}"
    return PredicateExpr(f"adj({p.name}{suffix})", fn)

def pred_dilate(p: PredicateExpr, conn: int = 8) -> PredicateExpr:
    """Morphological dilation: P union its neighbors."""
    def fn(g, _p=p, _conn=conn):
        mask = _p.evaluate(g).astype(np.float32)
        if _conn == 4:
            kernel = np.array([[0,1,0],[1,1,1],[0,1,0]], dtype=np.float32)
        else:
            kernel = np.ones((3,3), dtype=np.float32)
        return ndimage.convolve(mask, kernel, mode='constant', cval=0.0) > 0
    return PredicateExpr(f"dilate({p.name})", fn)

def pred_erode(p: PredicateExpr, conn: int = 8) -> PredicateExpr:
    """Morphological erosion: pixels in P whose entire neighborhood is in P."""
    def fn(g, _p=p, _conn=conn):
        mask = _p.evaluate(g).astype(np.float32)
        if _conn == 4:
            kernel = np.array([[0,1,0],[1,1,1],[0,1,0]], dtype=np.float32)
        else:
            kernel = np.ones((3,3), dtype=np.float32)
        n = float(kernel.sum())
        return ndimage.convolve(mask, kernel, mode='constant', cval=0.0) >= n
    return PredicateExpr(f"erode({p.name})", fn)

def pred_fill_holes(p: PredicateExpr) -> PredicateExpr:
    """Pixels enclosed by P (holes filled, P itself excluded)."""
    def fn(g, _p=p):
        mask = _p.evaluate(g)
        if not mask.any():
            return np.zeros(g.shape, dtype=bool)
        from scipy.ndimage import binary_fill_holes
        filled = binary_fill_holes(mask)
        return filled & ~mask
    return PredicateExpr(f"enclosed({p.name})", fn)

def pred_row_of(p: PredicateExpr) -> PredicateExpr:
    """All pixels in rows containing any P pixel (P excluded)."""
    def fn(g, _p=p):
        mask = _p.evaluate(g)
        rows = np.any(mask, axis=1)
        result = np.zeros(g.shape, dtype=bool)
        result[rows, :] = True
        return result & ~mask
    return PredicateExpr(f"row({p.name})", fn)

def pred_col_of(p: PredicateExpr) -> PredicateExpr:
    """All pixels in columns containing any P pixel (P excluded)."""
    def fn(g, _p=p):
        mask = _p.evaluate(g)
        cols = np.any(mask, axis=0)
        result = np.zeros(g.shape, dtype=bool)
        result[:, cols] = True
        return result & ~mask
    return PredicateExpr(f"col({p.name})", fn)

def pred_cross(p: PredicateExpr) -> PredicateExpr:
    """Pixels sharing a row OR column with any P pixel (P excluded)."""
    def fn(g, _p=p):
        mask = _p.evaluate(g)
        rows = np.any(mask, axis=1)
        cols = np.any(mask, axis=0)
        result = np.zeros(g.shape, dtype=bool)
        result[rows, :] = True
        result[:, cols] = True
        return result & ~mask
    return PredicateExpr(f"cross({p.name})", fn)

def pred_complement(p: PredicateExpr) -> PredicateExpr:
    """Complement of P."""
    return PredicateExpr(f"not({p.name})", lambda g, _p=p: ~_p.evaluate(g))

def pred_between(p: PredicateExpr, direction: str) -> PredicateExpr:
    """Pixels between two instances of P in given direction (h/v/any)."""
    def fn(g, _p=p, _dir=direction):
        mask = _p.evaluate(g)
        H, W = g.shape
        result = np.zeros((H, W), dtype=bool)
        if _dir in ('h', 'any'):
            for r in range(H):
                idxs = np.where(mask[r, :])[0]
                if len(idxs) >= 2:
                    result[r, idxs[0]+1:idxs[-1]] = True
        if _dir in ('v', 'any'):
            for c in range(W):
                idxs = np.where(mask[:, c])[0]
                if len(idxs) >= 2:
                    result[idxs[0]+1:idxs[-1], c] = True
        return result & ~mask
    return PredicateExpr(f"between({p.name},{direction})", fn)

def pred_count_neighbors(p: PredicateExpr, n: int, conn: int = 8) -> PredicateExpr:
    """Pixels with exactly n neighbors in P (not in P themselves)."""
    def fn(g, _p=p, _n=n, _conn=conn):
        mask = _p.evaluate(g).astype(np.float32)
        if _conn == 4:
            kernel = np.array([[0,1,0],[1,0,1],[0,1,0]], dtype=np.float32)
        else:
            kernel = np.ones((3,3), dtype=np.float32)
            kernel[1,1] = 0
        count = ndimage.convolve(mask, kernel, mode='constant', cval=0.0)
        return (np.round(count).astype(int) == _n) & ~_p.evaluate(g)
    return PredicateExpr(f"count_adj({p.name},{n})", fn)

def pred_largest_cc(p: PredicateExpr) -> PredicateExpr:
    """Pixels in the largest connected component of P."""
    def fn(g, _p=p):
        mask = _p.evaluate(g)
        if not mask.any():
            return np.zeros(g.shape, dtype=bool)
        from scipy.ndimage import label as ndlabel
        labeled, n_cc = ndlabel(mask)
        if n_cc <= 1:
            return mask
        sizes = np.bincount(labeled.flatten())[1:]
        largest = int(np.argmax(sizes)) + 1
        return labeled == largest
    return PredicateExpr(f"largest_cc({p.name})", fn)

def pred_smallest_cc(p: PredicateExpr) -> PredicateExpr:
    """Pixels NOT in the largest connected component of P."""
    def fn(g, _p=p):
        mask = _p.evaluate(g)
        if not mask.any():
            return np.zeros(g.shape, dtype=bool)
        from scipy.ndimage import label as ndlabel
        labeled, n_cc = ndlabel(mask)
        if n_cc <= 1:
            return np.zeros(g.shape, dtype=bool)
        sizes = np.bincount(labeled.flatten())[1:]
        largest = int(np.argmax(sizes)) + 1
        return mask & (labeled != largest)
    return PredicateExpr(f"small_cc({p.name})", fn)


# ---- Binary operators (Level 1 x Level 1 -> Level 2) ----

def pred_intersect(p: PredicateExpr, q: PredicateExpr) -> PredicateExpr:
    """Intersection of P and Q."""
    return PredicateExpr(
        f"and({p.name},{q.name})",
        lambda g, _p=p, _q=q: _p.evaluate(g) & _q.evaluate(g)
    )

def pred_difference(p: PredicateExpr, q: PredicateExpr) -> PredicateExpr:
    """P minus Q."""
    return PredicateExpr(
        f"diff({p.name},{q.name})",
        lambda g, _p=p, _q=q: _p.evaluate(g) & ~_q.evaluate(g)
    )

def pred_union(p: PredicateExpr, q: PredicateExpr) -> PredicateExpr:
    """Union of P and Q."""
    return PredicateExpr(
        f"or({p.name},{q.name})",
        lambda g, _p=p, _q=q: _p.evaluate(g) | _q.evaluate(g)
    )


# ---- Beam Search: Predicate Synthesis Engine ----

def _synthesize_predicate_beam(
    grids: List[np.ndarray],
    target_masks: List[np.ndarray],
    max_depth: int = 2,
    beam_width: int = 15,
    min_f1: float = 0.25,
) -> Optional[PredicateExpr]:
    """
    Synthesize a predicate via beam search over the DSL.

    This is the open-ended replacement for vocabulary lookup.
    Instead of "which existing predicate matches?", it asks
    "what PROGRAM computes a mask matching the residual?"

    Args:
        grids: input grids of training examples with residuals
        target_masks: boolean masks of residual pixels (what to match)
        max_depth: maximum composition depth (0=atoms, 1=unary, 2=binary)
        beam_width: how many candidates to keep at each level
        min_f1: minimum F1 to return a result

    Returns:
        Best PredicateExpr found, or None if nothing meets min_f1.
    """
    # Pool targets for scoring
    target_pool = np.concatenate([m.flatten().astype(bool) for m in target_masks])
    n_target = int(target_pool.sum())
    if n_target == 0:
        return None

    def score_expr(expr: PredicateExpr) -> Tuple[float, float, float]:
        """Score by pooled F1. Returns (f1, precision, recall)."""
        parts = []
        for g in grids:
            try:
                mask = expr.evaluate(g)
                if mask.shape != g.shape:
                    return (0.0, 0.0, 0.0)
                parts.append(mask.flatten().astype(bool))
            except Exception:
                return (0.0, 0.0, 0.0)
        pool = np.concatenate(parts)
        tp = int((pool & target_pool).sum())
        if tp == 0:
            return (0.0, 0.0, 0.0)
        fp = int(pool.sum()) - tp
        fn = n_target - tp
        prec = tp / max(tp + fp, 1)
        rec = tp / max(tp + fn, 1)
        f1 = 2 * prec * rec / max(prec + rec, 1e-10)
        return (f1, prec, rec)

    def per_example_check(expr: PredicateExpr, baseline_expr: Optional[PredicateExpr]) -> bool:
        """Verify expr doesn't lose >30% of true positives on any example vs baseline."""
        if baseline_expr is None:
            return True
        for g, m in zip(grids, target_masks):
            n_wrong = int(m.sum())
            if n_wrong == 0:
                continue
            try:
                base_tp = int((baseline_expr.evaluate(g) & m).sum())
                expr_tp = int((expr.evaluate(g) & m).sum())
                if base_tp > 0 and expr_tp < base_tp * 0.7:
                    return False
            except Exception:
                return False
        return True

    # --- Residual geometry analysis for search pruning ---
    # Analyze which colors are adjacent to the residual to prioritize atoms.
    priority_colors = set()
    for g, m in zip(grids, target_masks):
        if not m.any():
            continue
        for c in np.unique(g):
            if c == BG:
                continue
            c_mask = (g == int(c)).astype(np.float32)
            kernel = np.ones((3,3), dtype=np.float32); kernel[1,1] = 0
            adj = ndimage.convolve(c_mask, kernel, mode='constant', cval=0.0)
            if (adj > 0)[m].any():
                priority_colors.add(int(c))

    # --- Level 0: Atoms ---
    all_colors = set()
    for g in grids:
        all_colors.update(int(v) for v in np.unique(g))

    atoms = []
    # Priority: colors adjacent to residual first
    for c in sorted(priority_colors):
        atoms.append(pred_color(c))
    for c in sorted(all_colors - priority_colors):
        atoms.append(pred_color(c))
    atoms.append(pred_fg())
    atoms.append(pred_bg())
    atoms.append(pred_border())
    atoms.append(pred_border_row())
    atoms.append(pred_border_col())

    scored_atoms = [(score_expr(a), a) for a in atoms]
    scored_atoms.sort(key=lambda x: -x[0][0])

    best_f1 = scored_atoms[0][0][0] if scored_atoms else 0.0
    best_expr = scored_atoms[0][1] if scored_atoms and best_f1 > 0 else None

    if best_f1 >= 0.95 or max_depth < 1:
        return best_expr if best_expr and best_f1 >= min_f1 else None

    top_atoms = [a for (f1, _, _), a in scored_atoms[:beam_width] if f1 > 0]

    # --- Level 1: Unary operations on atoms ---
    level1_candidates = list(top_atoms)
    for atom in top_atoms:
        level1_candidates.append(pred_adjacent(atom))
        level1_candidates.append(pred_adjacent(atom, conn=4))
        level1_candidates.append(pred_fill_holes(atom))
        level1_candidates.append(pred_row_of(atom))
        level1_candidates.append(pred_col_of(atom))
        level1_candidates.append(pred_cross(atom))
        level1_candidates.append(pred_between(atom, 'h'))
        level1_candidates.append(pred_between(atom, 'v'))
        level1_candidates.append(pred_between(atom, 'any'))
        for n in [1, 2, 3]:
            level1_candidates.append(pred_count_neighbors(atom, n))
        level1_candidates.append(pred_largest_cc(atom))
        level1_candidates.append(pred_erode(atom))

    scored_l1 = [(score_expr(e), e) for e in level1_candidates]
    scored_l1.sort(key=lambda x: -x[0][0])

    best_single = best_expr  # best from level 0
    if scored_l1 and scored_l1[0][0][0] > best_f1:
        best_f1 = scored_l1[0][0][0]
        best_expr = scored_l1[0][1]

    if best_f1 >= 0.95 or max_depth < 2:
        return best_expr if best_expr and best_f1 >= min_f1 else None

    top_l1 = [e for (f1, _, _), e in scored_l1[:beam_width] if f1 > 0]

    # --- Level 2: Binary combinations of top level-1 predicates ---
    level2_candidates = []
    n_top = min(len(top_l1), 12)  # limit combinatorial explosion
    for i in range(n_top):
        for j in range(i + 1, n_top):
            p1, p2 = top_l1[i], top_l1[j]
            level2_candidates.append(pred_intersect(p1, p2))
            level2_candidates.append(pred_difference(p1, p2))
            level2_candidates.append(pred_difference(p2, p1))

    scored_l2 = [(score_expr(e), e) for e in level2_candidates]
    scored_l2.sort(key=lambda x: -x[0][0])

    # Accept level-2 only if substantially better (MDL penalty for complexity)
    best_l1_expr = best_expr
    if scored_l2 and scored_l2[0][0][0] > best_f1 + 0.05:
        candidate = scored_l2[0][1]
        # Per-example generalization check
        if per_example_check(candidate, best_l1_expr):
            best_f1 = scored_l2[0][0][0]
            best_expr = candidate

    return best_expr if best_expr and best_f1 >= min_f1 else None


# =============================================================================
# 3b. PREDICATED OPERATORS: Conditional Logic via Scene Graphs
# =============================================================================
#
# KEY INSIGHT: Most ARC tasks require CONDITIONAL operations:
#   "Recolor X WHERE adjacent_to(Y)" not just "Recolor X everywhere"
#
# A PredicatedOperator = Action + Predicate
#   - Action:    what to do (recolor, fill, erase)
#   - Predicate: WHERE to do it (spatial/relational condition)
#
# Predicate Synthesis = Inductive Logic Programming (ILP):
#   Given a residual mask M, find predicate P such that P ≈ M
#   Score by F1(P, M) = harmonic mean of precision and recall
# =============================================================================


def _canonical_shape(mask: np.ndarray, bbox: Tuple[int, int, int, int]) -> np.ndarray:
    """
    Extract the canonical (translation-invariant) shape of an object.

    Crops the boolean mask to its bounding box, producing a minimal
    representation at the origin. Two objects have the same shape iff
    their canonical shapes are identical numpy arrays.

    This is the orbit representative under the translation group:
      canonical(T_v(obj)) == canonical(obj) for all translation vectors v.
    """
    r1, c1, r2, c2 = bbox
    return mask[r1:r2, c1:c2].copy()


def _compute_pixel_predicates(grid: np.ndarray) -> Dict[str, np.ndarray]:
    """
    Compute a library of boolean pixel masks from grid structure.

    Each mask answers: "For each pixel, is this spatial predicate true?"
    These are the atoms of our ILP search.

    Returns dict mapping predicate_name -> boolean mask of same shape as grid.
    """
    H, W = grid.shape
    predicates: Dict[str, np.ndarray] = {}

    # --- Color-based predicates ---
    colors_present = set(grid.flat)
    for c in colors_present:
        predicates[f"is_color_{c}"] = (grid == c)

    # --- Adjacency predicates (4-connected) ---
    for c in colors_present:
        if c == BG:
            continue
        color_mask = (grid == int(c)).astype(np.float32)
        # Dilate by 1 pixel (4-connected kernel)
        kernel = np.array([[0, 1, 0], [1, 0, 1], [0, 1, 0]], dtype=np.float32)
        adj = ndimage.convolve(color_mask, kernel, mode='constant', cval=0.0)
        predicates[f"adj_to_{int(c)}"] = (adj > 0) & (grid != int(c))

    # --- Diagonal adjacency predicates (8-connected minus 4-connected) ---
    for c in colors_present:
        if c == BG:
            continue
        color_mask = (grid == int(c)).astype(np.float32)
        kernel8 = np.ones((3, 3), dtype=np.float32)
        kernel8[1, 1] = 0
        adj8 = ndimage.convolve(color_mask, kernel8, mode='constant', cval=0.0)
        predicates[f"near8_{int(c)}"] = (adj8 > 0) & (grid != int(c))

    # --- Row/Column sharing predicates ---
    for c in colors_present:
        if c == BG:
            continue
        color_mask = grid == int(c)
        rows_with_c = np.any(color_mask, axis=1)
        cols_with_c = np.any(color_mask, axis=0)
        row_mask = np.zeros_like(grid, dtype=bool)
        col_mask = np.zeros_like(grid, dtype=bool)
        row_mask[rows_with_c, :] = True
        col_mask[:, cols_with_c] = True
        predicates[f"same_row_{int(c)}"] = row_mask & ~color_mask
        predicates[f"same_col_{int(c)}"] = col_mask & ~color_mask
        # Cross: row AND column
        predicates[f"cross_{int(c)}"] = row_mask & col_mask & ~color_mask

    # --- Enclosure predicate (bg pixels enclosed by any fg) ---
    fg_mask = grid != BG
    if fg_mask.any():
        try:
            from scipy.ndimage import binary_fill_holes
            filled = binary_fill_holes(fg_mask)
            predicates["enclosed_by_fg"] = filled & ~fg_mask
        except Exception:
            pass

    # --- Per-color enclosure ---
    for c in colors_present:
        if c == BG:
            continue
        color_mask = grid == int(c)
        if color_mask.sum() < 4:
            continue
        try:
            from scipy.ndimage import binary_fill_holes
            filled = binary_fill_holes(color_mask)
            enclosed = filled & ~color_mask
            if enclosed.any():
                predicates[f"enclosed_by_{int(c)}"] = enclosed
        except Exception:
            pass

    # --- Border predicates ---
    border = np.zeros((H, W), dtype=bool)
    border[0, :] = True
    border[-1, :] = True
    border[:, 0] = True
    border[:, -1] = True
    predicates["on_border"] = border
    predicates["not_border"] = ~border

    # --- Decomposed border: row-border and col-border ---
    # Enables exhaustive conjunction search to discover corner (border_row & border_col),
    # top/bottom edge (border_row & !border_col), left/right edge (!border_row & border_col).
    border_row = np.zeros((H, W), dtype=bool)
    border_row[0, :] = True
    border_row[-1, :] = True
    border_col = np.zeros((H, W), dtype=bool)
    border_col[:, 0] = True
    border_col[:, -1] = True
    predicates["border_row"] = border_row
    predicates["border_col"] = border_col

    # --- Near any foreground pixel (color-agnostic adjacency) ---
    if fg_mask.any():
        fg_float = fg_mask.astype(np.float32)
        kernel8_fg = np.ones((3, 3), dtype=np.float32)
        kernel8_fg[1, 1] = 0
        adj_fg = ndimage.convolve(fg_float, kernel8_fg, mode='constant', cval=0.0)
        predicates["near_fg"] = (adj_fg > 0) & ~fg_mask

    # --- Between predicates (bg pixel between two fg regions on same row/col) ---
    if fg_mask.any():
        between_h = np.zeros((H, W), dtype=bool)
        between_v = np.zeros((H, W), dtype=bool)
        for r in range(H):
            row = fg_mask[r, :]
            if row.sum() >= 2:
                idxs = np.where(row)[0]
                for i in range(len(idxs) - 1):
                    between_h[r, idxs[i]+1:idxs[i+1]] = True
        for c_idx in range(W):
            col = fg_mask[:, c_idx]
            if col.sum() >= 2:
                idxs = np.where(col)[0]
                for i in range(len(idxs) - 1):
                    between_v[idxs[i]+1:idxs[i+1], c_idx] = True
        bg_between_h = between_h & (grid == BG)
        bg_between_v = between_v & (grid == BG)
        if bg_between_h.any():
            predicates["between_fg_h"] = bg_between_h
        if bg_between_v.any():
            predicates["between_fg_v"] = bg_between_v
        if bg_between_h.any() and bg_between_v.any():
            predicates["between_fg_hv"] = bg_between_h & bg_between_v

    # --- Per-color between predicates ---
    for c in colors_present:
        if c == BG:
            continue
        color_mask = grid == int(c)
        between_c_h = np.zeros((H, W), dtype=bool)
        between_c_v = np.zeros((H, W), dtype=bool)
        for r in range(H):
            row = color_mask[r, :]
            if row.sum() >= 2:
                idxs = np.where(row)[0]
                for i in range(len(idxs) - 1):
                    between_c_h[r, idxs[i]+1:idxs[i+1]] = True
        for c_idx in range(W):
            col = color_mask[:, c_idx]
            if col.sum() >= 2:
                idxs = np.where(col)[0]
                for i in range(len(idxs) - 1):
                    between_c_v[idxs[i]+1:idxs[i+1], c_idx] = True
        btw_h = between_c_h & (grid != int(c))
        btw_v = between_c_v & (grid != int(c))
        if btw_h.any():
            predicates[f"between_{int(c)}_h"] = btw_h
        if btw_v.any():
            predicates[f"between_{int(c)}_v"] = btw_v
        if btw_h.any() and btw_v.any():
            predicates[f"between_{int(c)}_hv"] = btw_h & btw_v
        # Union: between in EITHER direction (unlike hv which is intersection)
        btw_union = btw_h | btw_v
        if btw_union.any() and btw_union.sum() < grid.size * 0.5:
            predicates[f"between_{int(c)}_any"] = btw_union

    # --- Distance-2 adjacency (2-hop neighborhood) ---
    for c in colors_present:
        if c == BG:
            continue
        color_mask = (grid == int(c)).astype(np.float32)
        kernel_d2 = np.array([
            [0, 0, 1, 0, 0],
            [0, 1, 1, 1, 0],
            [1, 1, 0, 1, 1],
            [0, 1, 1, 1, 0],
            [0, 0, 1, 0, 0],
        ], dtype=np.float32)
        dist2 = ndimage.convolve(color_mask, kernel_d2, mode='constant', cval=0.0)
        predicates[f"within2_{int(c)}"] = (dist2 > 0) & (grid != int(c))

    # --- Exact adjacency count predicates ---
    for c in colors_present:
        if c == BG:
            continue
        color_mask = (grid == int(c)).astype(np.float32)
        kernel4 = np.array([[0, 1, 0], [1, 0, 1], [0, 1, 0]], dtype=np.float32)
        adj_count = ndimage.convolve(color_mask, kernel4, mode='constant', cval=0.0)
        for n in [1, 2, 3, 4]:
            exact = (adj_count == n) & (grid != int(c))
            if exact.any() and exact.sum() < grid.size * 0.3:
                predicates[f"exactly{n}_adj_{int(c)}"] = exact

    # ===================================================================
    # OBJECT-LEVEL PREDICATES (Scene Graph)
    # These operate on connected components rather than individual pixels.
    # Key addition: obj_span_h/v captures "between same-color objects"
    # at the object level, respecting grid structure that pixel-level
    # between predicates miss.
    # ===================================================================
    try:
        sg_grid = ARCGrid(torch.tensor(grid, dtype=torch.long))
        builder = SceneGraphBuilder(alignment_threshold=2.0, adjacency_threshold=3.0)
        sg = builder.build(sg_grid)
        objects = list(sg.objects.values())

        if objects:
            bg = sg.background_color

            # --- Object size predicates ---
            areas = [obj.area for obj in objects]
            median_area = float(np.median(areas)) if areas else 1.0

            small_mask = np.zeros((H, W), dtype=bool)
            large_mask = np.zeros((H, W), dtype=bool)
            for obj in objects:
                if obj.area <= max(4, median_area * 0.3):
                    small_mask |= obj.mask
                if obj.area >= max(median_area, 4):
                    large_mask |= obj.mask
            if small_mask.any() and small_mask.sum() < grid.size * 0.5:
                predicates["small_obj"] = small_mask
            if large_mask.any() and large_mask.sum() < grid.size * 0.5:
                predicates["large_obj"] = large_mask

            # --- Inside bounding box predicates (container interior) ---
            for c in set(obj.color for obj in objects):
                c_objects = [o for o in objects if o.color == c]
                bbox_interior = np.zeros((H, W), dtype=bool)
                for obj in c_objects:
                    r1, c1, r2, c2 = obj.bbox
                    bbox_interior[r1:r2, c1:c2] = True
                interior = bbox_interior & (grid != c)
                if interior.any() and interior.sum() < grid.size * 0.5:
                    predicates[f"inside_bbox_{c}"] = interior

            # --- Containment predicates (objects inside other objects) ---
            contains_edges = sg.get_edges_by_relation('contains')
            for edge in contains_edges:
                container = sg.objects.get(edge.src_id)
                contained = sg.objects.get(edge.dst_id)
                if container and contained:
                    pn = f"contained_by_{container.color}"
                    if pn not in predicates:
                        predicates[pn] = np.zeros((H, W), dtype=bool)
                    predicates[pn] |= contained.mask

            # --- Object span predicates (between same-color objects) ---
            # Groups objects by color; for each pair sharing a row/col band,
            # marks background pixels in the rectangular span between them.
            by_color: Dict[int, list] = {}
            for obj in objects:
                by_color.setdefault(obj.color, []).append(obj)

            for c, c_objs in by_color.items():
                if len(c_objs) < 2:
                    continue

                # Horizontal span between same-color objects
                h_span = np.zeros((H, W), dtype=bool)
                for i, a in enumerate(c_objs):
                    for b in c_objs[i+1:]:
                        # Check overlapping row ranges
                        row_lo = max(a.bbox[0], b.bbox[0])
                        row_hi = min(a.bbox[2], b.bbox[2])
                        if row_lo < row_hi:
                            # Horizontal gap between them
                            left_end = min(a.bbox[3], b.bbox[3])
                            right_start = max(a.bbox[1], b.bbox[1])
                            if left_end < right_start:
                                h_span[row_lo:row_hi, left_end:right_start] = True
                h_notc = h_span & (grid != c)
                if h_notc.any() and h_notc.sum() < grid.size * 0.5:
                    predicates[f"obj_span_h_{c}"] = h_notc

                # Vertical span between same-color objects
                v_span = np.zeros((H, W), dtype=bool)
                for i, a in enumerate(c_objs):
                    for b in c_objs[i+1:]:
                        # Check overlapping column ranges
                        col_lo = max(a.bbox[1], b.bbox[1])
                        col_hi = min(a.bbox[3], b.bbox[3])
                        if col_lo < col_hi:
                            top_end = min(a.bbox[2], b.bbox[2])
                            bot_start = max(a.bbox[0], b.bbox[0])
                            if top_end < bot_start:
                                v_span[top_end:bot_start, col_lo:col_hi] = True
                v_notc = v_span & (grid != c)
                if v_notc.any() and v_notc.sum() < grid.size * 0.5:
                    predicates[f"obj_span_v_{c}"] = v_notc

            # --- Object row/col band predicates ---
            for c in set(obj.color for obj in objects):
                c_objects = [o for o in objects if o.color == c]
                if not c_objects:
                    continue
                row_band = np.zeros((H, W), dtype=bool)
                col_band = np.zeros((H, W), dtype=bool)
                for obj in c_objects:
                    r1, c1, r2, c2 = obj.bbox
                    row_band[r1:r2, :] = True
                    col_band[:, c1:c2] = True
                rb = row_band & (grid != c)
                cb = col_band & (grid != c)
                if rb.any() and rb.sum() < grid.size * 0.5:
                    predicates[f"obj_row_{c}"] = rb
                if cb.any() and cb.sum() < grid.size * 0.5:
                    predicates[f"obj_col_{c}"] = cb

            # --- Shape isomorphism predicates (Geometric Blanket) ---
            # Detect orbits under translation: objects with same canonical shape.
            # This is the key SGC insight: "grokking" = learning the symmetry group.
            # canonical_shape(obj) = obj.mask cropped to bbox (translation-invariant)
            #
            # Predicates generated:
            #   same_shape_as_C: pixels of objects sharing shape with any color C object
            #   unique_shape:    pixels of objects with no shape-twin in the grid
            #   repeated_shape:  pixels of objects with at least one shape-twin
            #   shape_majority:  pixels of objects in the largest shape equivalence class
            #   shape_minority:  pixels of objects NOT in the largest shape class

            # Step 1: Compute canonical shapes
            obj_canonicals = {}  # obj_id -> canonical shape (np.ndarray)
            for obj in objects:
                obj_canonicals[obj.obj_id] = _canonical_shape(obj.mask, obj.bbox)

            # Step 2: Build shape equivalence classes
            # Two objects are equivalent if their canonical shapes are identical
            shape_classes: Dict[str, list] = {}  # shape_hash -> [obj_ids]
            for obj in objects:
                canon = obj_canonicals[obj.obj_id]
                shape_key = canon.tobytes() + bytes(canon.shape)
                shape_classes.setdefault(shape_key, []).append(obj.obj_id)

            # Step 3: same_shape_as_C — for each color, pixels of ALL objects
            # that share a canonical shape with any object of that color
            for c in set(obj.color for obj in objects):
                c_obj_ids = {o.obj_id for o in objects if o.color == c}
                # Find all shape keys that include a color-c object
                c_shape_keys = set()
                for sk, ids in shape_classes.items():
                    if any(oid in c_obj_ids for oid in ids):
                        c_shape_keys.add(sk)
                # Collect pixels of ALL objects (any color) sharing those shapes
                same_shape_mask = np.zeros((H, W), dtype=bool)
                for sk in c_shape_keys:
                    for oid in shape_classes[sk]:
                        obj = sg.objects[oid]
                        if obj.color != c:  # Only mark OTHER-color objects
                            same_shape_mask |= obj.mask
                if same_shape_mask.any() and same_shape_mask.sum() < grid.size * 0.5:
                    predicates[f"same_shape_as_{c}"] = same_shape_mask

            # Step 4: unique_shape vs repeated_shape
            unique_mask = np.zeros((H, W), dtype=bool)
            repeated_mask = np.zeros((H, W), dtype=bool)
            for sk, ids in shape_classes.items():
                for oid in ids:
                    obj = sg.objects[oid]
                    if len(ids) == 1:
                        unique_mask |= obj.mask
                    else:
                        repeated_mask |= obj.mask
            if unique_mask.any() and unique_mask.sum() < grid.size * 0.5:
                predicates["unique_shape"] = unique_mask
            if repeated_mask.any() and repeated_mask.sum() < grid.size * 0.5:
                predicates["repeated_shape"] = repeated_mask

            # Step 5: shape_majority / shape_minority
            if shape_classes:
                largest_class_size = max(len(ids) for ids in shape_classes.values())
                majority_mask = np.zeros((H, W), dtype=bool)
                minority_mask = np.zeros((H, W), dtype=bool)
                for sk, ids in shape_classes.items():
                    for oid in ids:
                        obj = sg.objects[oid]
                        if len(ids) == largest_class_size:
                            majority_mask |= obj.mask
                        else:
                            minority_mask |= obj.mask
                if majority_mask.any() and majority_mask.sum() < grid.size * 0.5:
                    predicates["shape_majority"] = majority_mask
                if minority_mask.any() and minority_mask.sum() < grid.size * 0.5:
                    predicates["shape_minority"] = minority_mask

    except Exception:
        pass  # Object predicates are optional; pixel predicates still work

    # ===================================================================
    # RELATIONAL PREDICATES (Vocabulary Expansion)
    # SGC GROUNDING: These predicates generate new coarse-grainings that
    # capture statistical and relational structure invisible to pure local
    # predicates. Each one extends the partition lattice with new atoms,
    # increasing the expressiveness of the hypothesis space.
    # ===================================================================

    # --- color_is_mode_of_row / color_is_mode_of_col ---
    # Pixel's color is the most common color in its row/column.
    # Captures "background of row" vs "foreground of row" distinction.
    mode_row = np.zeros((H, W), dtype=bool)
    mode_col = np.zeros((H, W), dtype=bool)
    for r in range(H):
        row_colors = grid[r, :]
        counts = np.bincount(row_colors, minlength=10)
        row_mode = int(np.argmax(counts))
        mode_row[r, :] = (row_colors == row_mode)
    for c_idx in range(W):
        col_colors = grid[:, c_idx]
        counts = np.bincount(col_colors, minlength=10)
        col_mode = int(np.argmax(counts))
        mode_col[:, c_idx] = (col_colors == col_mode)
    predicates["color_is_mode_of_row"] = mode_row
    predicates["color_is_mode_of_col"] = mode_col
    # NOT mode = minority color in row/col
    not_mode_row = ~mode_row
    not_mode_col = ~mode_col
    if not_mode_row.any() and not_mode_row.sum() < grid.size * 0.5:
        predicates["color_not_mode_of_row"] = not_mode_row
    if not_mode_col.any() and not_mode_col.sum() < grid.size * 0.5:
        predicates["color_not_mode_of_col"] = not_mode_col

    # --- color_differs_from_neighbor (left/right/up/down) ---
    # Pixel color differs from its immediate neighbor in that direction.
    # Captures edges/boundaries of color regions.
    if H > 1:
        diff_up = np.zeros((H, W), dtype=bool)
        diff_down = np.zeros((H, W), dtype=bool)
        diff_up[1:, :] = grid[1:, :] != grid[:-1, :]
        diff_down[:-1, :] = grid[:-1, :] != grid[1:, :]
        predicates["differs_from_up"] = diff_up
        predicates["differs_from_down"] = diff_down
    if W > 1:
        diff_left = np.zeros((H, W), dtype=bool)
        diff_right = np.zeros((H, W), dtype=bool)
        diff_left[:, 1:] = grid[:, 1:] != grid[:, :-1]
        diff_right[:, :-1] = grid[:, :-1] != grid[:, 1:]
        predicates["differs_from_left"] = diff_left
        predicates["differs_from_right"] = diff_right

    # --- is_boundary_of_region ---
    # Pixel is on the edge of its same-color connected component
    # (has at least one 4-connected neighbor of a different color or is on grid edge).
    # Captures region boundaries without knowing which color.
    boundary = np.zeros((H, W), dtype=bool)
    for r in range(H):
        for c_idx in range(W):
            color = grid[r, c_idx]
            is_edge = (r == 0 or r == H-1 or c_idx == 0 or c_idx == W-1)
            has_diff_neighbor = False
            for dr, dc in [(-1,0),(1,0),(0,-1),(0,1)]:
                nr, nc = r + dr, c_idx + dc
                if 0 <= nr < H and 0 <= nc < W:
                    if grid[nr, nc] != color:
                        has_diff_neighbor = True
                        break
                else:
                    has_diff_neighbor = True
                    break
            if has_diff_neighbor:
                boundary[r, c_idx] = True
    if boundary.any() and boundary.sum() < grid.size * 0.8:
        predicates["is_region_boundary"] = boundary
        interior = ~boundary
        if interior.any() and interior.sum() < grid.size * 0.5:
            predicates["is_region_interior"] = interior

    # --- color_count_N: pixel's color appears exactly N times in grid ---
    # Captures "singleton color", "pair color", etc.
    color_counts_global = np.bincount(grid.flatten(), minlength=10)
    for n_target in [1, 2, 3, 4]:
        mask_n = np.zeros((H, W), dtype=bool)
        for c_val in range(10):
            if color_counts_global[c_val] == n_target:
                mask_n |= (grid == c_val)
        if mask_n.any() and mask_n.sum() < grid.size * 0.5:
            predicates[f"color_count_{n_target}"] = mask_n

    # --- in_largest_cc: pixel belongs to the largest connected component ---
    # of its own color. Captures "main body" vs "satellite" distinction.
    try:
        from scipy.ndimage import label as ndimage_label
        largest_cc = np.zeros((H, W), dtype=bool)
        for c_val in colors_present:
            c_mask = (grid == c_val)
            if c_mask.sum() < 2:
                continue
            labeled, n_cc = ndimage_label(c_mask)
            if n_cc <= 1:
                continue
            # Find largest component
            cc_sizes = np.bincount(labeled.flatten())[1:]  # skip label 0
            if len(cc_sizes) == 0:
                continue
            largest_label = int(np.argmax(cc_sizes)) + 1
            largest_cc |= (labeled == largest_label)
        if largest_cc.any() and largest_cc.sum() < grid.size * 0.5:
            predicates["in_largest_cc"] = largest_cc
            not_largest = np.zeros((H, W), dtype=bool)
            for c_val in colors_present:
                c_mask = (grid == c_val)
                labeled, n_cc = ndimage_label(c_mask)
                if n_cc <= 1:
                    continue
                cc_sizes = np.bincount(labeled.flatten())[1:]
                largest_label = int(np.argmax(cc_sizes)) + 1
                not_largest |= (c_mask & (labeled != largest_label))
            if not_largest.any() and not_largest.sum() < grid.size * 0.5:
                predicates["not_in_largest_cc"] = not_largest
    except Exception:
        pass

    return predicates


@dataclass
class ScoredPredicate:
    """A predicate with its ILP score against a target mask."""
    name: str
    mask: np.ndarray
    precision: float   # |mask & target| / |mask|
    recall: float      # |mask & target| / |target|
    f1: float          # harmonic mean


class PredicateSynthesizer:
    """
    Inductive Logic Programming on pixel predicates.

    Given a residual mask (where changes happen), finds the predicate
    that best discriminates changed pixels from unchanged pixels.

    This is the "AI" of the system: it asks
      "What spatial relation is true for changed pixels but not others?"
    """

    def __init__(self, min_f1: float = 0.4):
        self.min_f1 = min_f1

    def synthesize(
        self,
        grid: np.ndarray,
        target_mask: np.ndarray,
        predicates: Optional[Dict[str, np.ndarray]] = None,
    ) -> List[ScoredPredicate]:
        """
        Find predicates that explain the target_mask.

        Args:
            grid: the current grid state
            target_mask: boolean mask of pixels we want to select
            predicates: precomputed predicates (or None to compute)

        Returns:
            List of ScoredPredicate sorted by F1 descending
        """
        if predicates is None:
            predicates = _compute_pixel_predicates(grid)

        target_count = int(target_mask.sum())
        if target_count == 0:
            return []

        results = []
        for name, pred_mask in predicates.items():
            if pred_mask.shape != target_mask.shape:
                continue

            intersection = int((pred_mask & target_mask).sum())
            pred_count = int(pred_mask.sum())

            if pred_count == 0 or intersection == 0:
                continue

            precision = intersection / pred_count
            recall = intersection / target_count
            f1 = 2 * precision * recall / (precision + recall) if (precision + recall) > 0 else 0.0

            if f1 >= self.min_f1:
                results.append(ScoredPredicate(
                    name=name, mask=pred_mask,
                    precision=precision, recall=recall, f1=f1
                ))

        results.sort(key=lambda sp: -sp.f1)

        # Also try conjunctions of top predicates for better F1
        # Strategy: if best has high recall but imperfect precision,
        # conjoin with ANY predicate that boosts precision
        # SGC: Skip O(N²) CPU conjunctions on large grids - rely on GPU Tensor Logic instead
        if len(results) >= 2 and target_mask.size <= 400:
            top = results[:8]
            for i, sp_a in enumerate(top):
                for sp_b in top[i+1:]:
                    conj_mask = sp_a.mask & sp_b.mask
                    intersection = int((conj_mask & target_mask).sum())
                    pred_count = int(conj_mask.sum())
                    if pred_count == 0 or intersection == 0:
                        continue
                    precision = intersection / pred_count
                    recall = intersection / target_count
                    f1 = 2 * precision * recall / (precision + recall) if (precision + recall) > 0 else 0.0
                    if f1 > self.min_f1:
                        results.append(ScoredPredicate(
                            name=f"{sp_a.name}&{sp_b.name}",
                            mask=conj_mask,
                            precision=precision, recall=recall, f1=f1
                        ))

        # COLOR-COHERENT conjunction search: pair the best predicate with
        # predicates that reference the SAME color. This prevents overfitting
        # from accidental refinements like not_border that happen to be true
        # on training but don't generalize. E.g., cross_5 & adj_to_5 (both
        # reference color 5) is allowed; cross_5 & not_border is not.
        # SGC: Skip on large grids - GPU Tensor Logic handles complex predicates
        if results and results[0].recall >= 0.8 and results[0].precision < 1.0 and target_mask.size <= 400:
            best = results[0]
            # Extract color reference from best predicate name
            color_refs = re.findall(r'_(\d+)', best.name)
            if color_refs:
                color_suffix = color_refs[-1]  # e.g., "5" from "cross_5"
                for name, pred_mask in predicates.items():
                    if pred_mask.shape != target_mask.shape:
                        continue
                    if name == best.name:
                        continue
                    # Only allow same-color predicates
                    if f"_{color_suffix}" not in name:
                        continue
                    conj_mask = best.mask & pred_mask
                    intersection = int((conj_mask & target_mask).sum())
                    pred_count = int(conj_mask.sum())
                    if pred_count == 0 or intersection == 0:
                        continue
                    precision = intersection / pred_count
                    recall = intersection / target_count
                    f1 = 2 * precision * recall / (precision + recall) if (precision + recall) > 0 else 0.0
                    if f1 > results[0].f1:
                        results.append(ScoredPredicate(
                            name=f"{best.name}&{name}",
                            mask=conj_mask,
                            precision=precision, recall=recall, f1=f1
                        ))

        results.sort(key=lambda sp: -sp.f1)
        return results


def _make_predicated_recolor(
    pred_name_or_expr,
    source_color,  # int or str role (e.g., 'MINORITY', 'MAJORITY')
    target_color,  # int or str role (e.g., 'MINORITY', 'MAJORITY')
) -> AtomicOp:
    """
    Create a DYNAMIC predicated recolor operation.

    Recolors source_color -> target_color ONLY WHERE predicate is true.
    The predicate mask is recomputed from the grid at apply time.

    Accepts either str (legacy) or PredicateExpr (DSL).
    
    SGFE v2.5: Both predicates AND action colors support role-based names.
    - source_color/target_color can be int (literal) or str role like 'MINORITY', 'MAJORITY'
    - Roles are resolved to actual colors at apply-time using detect_color_roles.
    """
    sc_spec, tc_spec = source_color, target_color  # May be int or str roles
    is_expr = hasattr(pred_name_or_expr, 'evaluate')  # PredicateExpr or TensorPredicate
    pn = pred_name_or_expr.name if is_expr else pred_name_or_expr
    pred_expr = pred_name_or_expr if is_expr else None

    def apply(grid: np.ndarray) -> np.ndarray:
        # SGFE v2.5: Resolve color roles to actual colors at apply-time
        roles = detect_color_roles(grid)
        role_to_color = {str(v).lower(): int(k) for k, v in roles.items()}
        
        if isinstance(sc_spec, str) and not sc_spec.isdigit():
            actual_sc = role_to_color.get(sc_spec.lower(), 0)
        else:
            actual_sc = int(sc_spec)
        
        if isinstance(tc_spec, str) and not tc_spec.isdigit():
            actual_tc = role_to_color.get(tc_spec.lower(), 0)
        else:
            actual_tc = int(tc_spec)
        
        if pred_expr is not None:
            try:
                mask = pred_expr.evaluate(grid)
                if mask.shape != grid.shape:
                    return grid.copy()
            except Exception:
                return grid.copy()
        else:
            # SGFE v2.4: Resolve role placeholders to actual colors
            resolved_pn = resolve_role_to_color(pn, grid)
            predicates = _compute_pixel_predicates(grid)
            parts = resolved_pn.split("&")
            mask = np.ones(grid.shape, dtype=bool)
            for part in parts:
                if part.startswith("!"):
                    neg_name = part[1:]
                    if neg_name in predicates:
                        mask = mask & ~predicates[neg_name]
                    else:
                        return grid.copy()
                elif part in predicates:
                    mask = mask & predicates[part]
                else:
                    return grid.copy()
        result = grid.copy()
        color_mask = grid == actual_sc
        result[color_mask & mask] = actual_tc
        return result

    return AtomicOp(
        f"recolor({sc_spec}->{tc_spec}|{pn})",
        apply,
        f"recolor {sc_spec}->{tc_spec} where {pn}"
    )


def _make_predicated_fill(
    pred_name_or_expr,
    fill_color,  # int or str role (e.g., 'MINORITY', 'MAJORITY')
) -> AtomicOp:
    """
    Fill background pixels WHERE predicate is true with fill_color.
    Predicate recomputed dynamically.

    Accepts either:
      - str: predicate name (looked up in _compute_pixel_predicates, supports & and !)
      - PredicateExpr: DSL expression (evaluated directly on grid)
    
    SGFE v2.5: Both predicates AND action colors support role-based names.
    - fill_color can be int (literal) or str role like 'MINORITY', 'MAJORITY'
    - Roles are resolved to actual colors at apply-time using detect_color_roles.
    """
    fc_spec = fill_color  # May be int or str role
    is_expr = hasattr(pred_name_or_expr, 'evaluate')  # PredicateExpr or TensorPredicate
    pn = pred_name_or_expr.name if is_expr else pred_name_or_expr
    pred_expr = pred_name_or_expr if is_expr else None

    def apply(grid: np.ndarray) -> np.ndarray:
        # SGFE v2.5: Resolve fill_color role to actual color at apply-time
        if isinstance(fc_spec, str) and not fc_spec.isdigit():
            roles = detect_color_roles(grid)
            role_to_color = {str(v).lower(): int(k) for k, v in roles.items()}
            actual_fc = role_to_color.get(fc_spec.lower(), 0)
        else:
            actual_fc = int(fc_spec)
        
        if pred_expr is not None:
            # DSL path: evaluate the predicate program directly
            try:
                mask = pred_expr.evaluate(grid)
                if mask.shape != grid.shape:
                    return grid.copy()
            except Exception:
                return grid.copy()
        else:
            # Legacy path: lookup in closed vocabulary
            # SGFE v2.4: Resolve role placeholders to actual colors
            resolved_pn = resolve_role_to_color(pn, grid)
            predicates = _compute_pixel_predicates(grid)
            parts = resolved_pn.split("&")
            mask = np.ones(grid.shape, dtype=bool)
            for part in parts:
                if part.startswith("!"):
                    neg_name = part[1:]
                    if neg_name in predicates:
                        mask = mask & ~predicates[neg_name]
                    else:
                        return grid.copy()
                elif part in predicates:
                    mask = mask & predicates[part]
                else:
                    return grid.copy()
        result = grid.copy()
        bg_mask = grid == BG
        result[bg_mask & mask] = actual_fc
        return result

    return AtomicOp(
        f"fill({fc_spec}|{pn})",
        apply,
        f"fill bg with {fc_spec} where {pn}"
    )


def _make_predicated_erase(
    pred_name_or_expr,
    erase_color,  # int or str role (e.g., 'MINORITY', 'MAJORITY')
) -> AtomicOp:
    """
    Erase (set to BG) pixels of erase_color WHERE predicate is true.
    Accepts either str (legacy) or PredicateExpr (DSL).
    
    SGFE v2.5: Both predicates AND action colors support role-based names.
    - erase_color can be int (literal) or str role like 'MINORITY', 'MAJORITY'
    - Roles are resolved to actual colors at apply-time using detect_color_roles.
    """
    ec_spec = erase_color  # May be int or str role
    is_expr = hasattr(pred_name_or_expr, 'evaluate')  # PredicateExpr or TensorPredicate
    pn = pred_name_or_expr.name if is_expr else pred_name_or_expr
    pred_expr = pred_name_or_expr if is_expr else None

    def apply(grid: np.ndarray) -> np.ndarray:
        # SGFE v2.5: Resolve erase_color role to actual color at apply-time
        if isinstance(ec_spec, str) and not ec_spec.isdigit():
            roles = detect_color_roles(grid)
            role_to_color = {str(v).lower(): int(k) for k, v in roles.items()}
            actual_ec = role_to_color.get(ec_spec.lower(), 0)
        else:
            actual_ec = int(ec_spec)
        
        if pred_expr is not None:
            try:
                mask = pred_expr.evaluate(grid)
                if mask.shape != grid.shape:
                    return grid.copy()
            except Exception:
                return grid.copy()
        else:
            # SGFE v2.4: Resolve role placeholders to actual colors
            resolved_pn = resolve_role_to_color(pn, grid)
            predicates = _compute_pixel_predicates(grid)
            parts = resolved_pn.split("&")
            mask = np.ones(grid.shape, dtype=bool)
            for part in parts:
                if part.startswith("!"):
                    neg_name = part[1:]
                    if neg_name in predicates:
                        mask = mask & ~predicates[neg_name]
                    else:
                        return grid.copy()
                elif part in predicates:
                    mask = mask & predicates[part]
                else:
                    return grid.copy()
        result = grid.copy()
        color_mask = grid == actual_ec
        result[color_mask & mask] = BG
        return result

    return AtomicOp(
        f"erase({ec_spec}|{pn})",
        apply,
        f"erase color {ec_spec} where {pn}"
    )


def _compute_change_mi(mask: np.ndarray, pred: np.ndarray, tgt: np.ndarray) -> float:
    """
    Compute MI(P_mask, C) where C is a per-pixel change label.

    Change labels (categorical):
      0: unchanged (pred == tgt)
      1+: changed, encoded as 10*pred_color + tgt_color (distinguishes
          fill(0->c), erase(c->0), recolor(a->b))

    MI = H(P) + H(C) - H(P,C)   [bits]

    High MI means the mask captures meaningful structure in the residual:
    knowing whether a pixel is "in the mask" tells you a lot about what
    change (if any) that pixel needs.
    """
    H, W = pred.shape
    n = H * W
    if n == 0:
        return 0.0

    # Flatten
    m = mask.ravel().astype(int)    # 0 or 1
    changed = (pred != tgt).ravel()
    # Change label: 0 = unchanged, else 10*src + dst
    c = np.where(changed, 10 * pred.ravel() + tgt.ravel() + 1, 0)

    # Joint histogram: (mask_val, change_label) pairs
    # Use a dict for sparse categorical labels
    from collections import Counter
    joint = Counter(zip(m.tolist(), c.tolist()))

    # Marginals
    p_m = np.array([np.sum(m == 0), np.sum(m == 1)], dtype=float) / n
    c_vals, c_counts = np.unique(c, return_counts=True)
    p_c = c_counts.astype(float) / n

    def _entropy(probs):
        probs = probs[probs > 0]
        return -float(np.sum(probs * np.log2(probs)))

    h_m = _entropy(p_m)
    h_c = _entropy(p_c)

    # Joint entropy
    joint_probs = np.array(list(joint.values()), dtype=float) / n
    h_mc = _entropy(joint_probs)

    mi = h_m + h_c - h_mc
    return max(mi, 0.0)  # Clamp numerical noise


# =============================================================================
# LEM ARCHITECTURE: Morphological Predicate Synthesis (Sheaf-First)
# =============================================================================
# 
# This provides an alternative to TensorPredicateLearner that guarantees
# sheaf consistency by construction. Morphological operations are topologically
# invariant, so their sheaf energy is naturally low (often 0.0).
#
# Theory (Native Encoding Architecture):
#   - Operations are Galois adjunctions on complete lattices
#   - The "name" of an operation IS its algebraic AST
#   - Predicates compose, simplify, and transfer algebraically

def _morph_residual_refine(
    task,
    program,
    active_indices: list,
    verbose: bool = False,
    sgfe_library=None,
) -> list:
    """
    LEM Architecture: Morphological predicate refinement.
    
    Uses lattice algebra (dilation, erosion, opening, closing, gradient)
    to discover predicates that are sheaf-consistent by construction.
    
    Theory (Native Encoding Architecture):
      - Morphological operations have sheaf_energy ≈ 0.0 because they
        operate on topological structure, not pixel coordinates
      - The canonical term name IS the mathematical description
      - No learned weights = no memorization = guaranteed generalization
    
    Returns:
        List of (AtomicOp, structured_log_dict) tuples for accepted ops.
    """
    if not HAS_MORPH_ALGEBRA:
        return []
    
    import time as _time
    _morph_start = _time.monotonic()
    _MORPH_BUDGET = 10.0  # seconds: morphological synthesis is fast
    
    n_ex = len(task.train_examples)
    if not active_indices:
        return []
    
    # Collect grids, targets, predictions for active examples
    grids = []
    targets = []
    predictions = []
    roles_list = []
    
    for i in active_indices:
        ex = task.train_examples[i]
        inp = ex.input_grid.data.numpy()
        tgt = ex.output_grid.data.numpy()
        
        try:
            pred = program.apply(inp)
        except Exception:
            pred = inp.copy()
        
        if pred.shape != tgt.shape:
            continue
        
        grids.append(pred)
        targets.append(tgt)
        predictions.append(pred)
        roles_list.append(detect_color_roles(pred))
    
    if not grids:
        return []
    
    # Check all grids have the same shape
    shapes = set(g.shape for g in grids)
    if len(shapes) > 1:
        return []
    
    # Synthesize morphological predicates
    synth = MorphologicalPredicateSynthesizer(
        ses=list(CANONICAL_SES.values()),
        max_depth=1,  # Start with simple terms
        min_f1=0.4,
        sheaf_threshold=0.6,
    )
    
    candidates = synth.synthesize(
        grids=grids,
        targets=targets,
        roles_list=roles_list,
        verbose=verbose,
    )
    
    if verbose:
        print(f"    [MORPH] Found {len(candidates)} morphological predicates", flush=True)
    
    # Don't return early - allow object-level synthesis to run
    accepted = []
    
    # Renormalization thresholds (defined here for both pixel and object level)
    RENORM_THRESHOLD = 0.3  # Strict: only near-perfect global sections
    SEVERE_REGRESSION = 0.2  # Max allowed defect increase ratio
    
    # Process pixel-level candidates if any exist
    for morph_pred, role in candidates[:5]:  # Top 5 candidates
        if _time.monotonic() - _morph_start > _MORPH_BUDGET:
            break
        
        # Determine action from residual analysis
        # Tally (from_color, to_color) on morphological mask
        n_colors = 10
        color_tally = np.zeros((n_colors, n_colors), dtype=int)
        
        for pred_grid, tgt, roles in zip(predictions, targets, roles_list):
            # Get color for this role
            color = None
            for c, r in roles.items():
                if r.upper() == role:
                    color = c
                    break
            
            if color is None:
                continue
            
            # Apply morphological predicate
            role_mask = (pred_grid == color).astype(np.float32)
            x_t = torch.tensor(role_mask, dtype=torch.float32)
            result = apply_term(morph_pred.term, x_t).cpu().numpy()
            mask = result > 0.5
            
            # Tally color changes in mask
            wrong_in_mask = mask & (pred_grid != tgt)
            if wrong_in_mask.any():
                for r_idx in range(tgt.shape[0]):
                    for c_idx in range(tgt.shape[1]):
                        if wrong_in_mask[r_idx, c_idx]:
                            color_tally[int(pred_grid[r_idx, c_idx]), int(tgt[r_idx, c_idx])] += 1
        
        total_transitions = int(color_tally.sum())
        if total_transitions == 0:
            continue
        
        # Classify residual type
        fill_from_bg = int(color_tally[0, :].sum())
        erase_to_bg = int(color_tally[:, 0].sum())
        
        # Create op based on dominant transition
        if fill_from_bg > erase_to_bg:
            # Fill operation
            to_color = int(np.argmax(color_tally[0, :]))
            if to_color == 0:
                continue
            
            # Create predicate name in role-normalized form
            pred_name = f"morph_{morph_pred.term.canonical_name}_{role}"
            
            def make_morph_fill(mp, rl, tc):
                def _apply(grid):
                    roles = detect_color_roles(grid)
                    color = None
                    for c, r in roles.items():
                        if r.upper() == rl:
                            color = c
                            break
                    if color is None:
                        return grid
                    
                    role_mask = (grid == color).astype(np.float32)
                    x_t = torch.tensor(role_mask, dtype=torch.float32)
                    result = apply_term(mp.term, x_t).cpu().numpy()
                    mask = result > 0.5
                    
                    out = grid.copy()
                    out[mask & (grid == 0)] = tc
                    return out
                return _apply
            
            op = AtomicOp(f"morph_fill({to_color}|{pred_name})", make_morph_fill(morph_pred, role, to_color))
            
        else:
            # Erase operation
            pred_name = f"morph_{morph_pred.term.canonical_name}_{role}"
            
            def make_morph_erase(mp, rl):
                def _apply(grid):
                    roles = detect_color_roles(grid)
                    color = None
                    for c, r in roles.items():
                        if r.upper() == rl:
                            color = c
                            break
                    if color is None:
                        return grid
                    
                    role_mask = (grid == color).astype(np.float32)
                    x_t = torch.tensor(role_mask, dtype=torch.float32)
                    result = apply_term(mp.term, x_t).cpu().numpy()
                    mask = result > 0.5
                    
                    out = grid.copy()
                    out[mask] = 0
                    return out
                return _apply
            
            op = AtomicOp(f"morph_erase(0|{pred_name})", make_morph_erase(morph_pred, role))
        
        # =================================================================
        # RENORMALIZATION ACCEPTANCE: Sheaf-monotone, not defect-strict
        # =================================================================
        # Theory: Morphological predicates are valid coarse-graining operators.
        # Accept based on sheaf energy (global consistency) rather than
        # strict per-example improvement. Composition does the work.
        #
        # Acceptance criteria:
        #   1. sheaf_energy ≤ RENORM_THRESHOLD (globally consistent)
        #   2. At least ONE example improves OR no example regresses severely
        #   3. Op is well-formed (no exceptions)
        
        # RENORM_THRESHOLD and SEVERE_REGRESSION defined at function scope above
        
        sheaf_ok = morph_pred.sheaf_energy <= RENORM_THRESHOLD
        
        # Compute per-example deltas
        deltas = []
        any_improve = False
        severe_regress = False
        
        for pred_grid, tgt in zip(predictions, targets):
            try:
                new_pred = op.apply(pred_grid)
                old_defect = (pred_grid != tgt).sum()
                new_defect = (new_pred != tgt).sum()
                delta = new_defect - old_defect
                deltas.append(delta)
                
                if delta < 0:
                    any_improve = True
                if old_defect > 0 and delta > old_defect * SEVERE_REGRESSION:
                    severe_regress = True
            except Exception:
                severe_regress = True
                break
        
        # Renormalization acceptance: sheaf-consistent + not catastrophic
        # SGFE v2.8: Sheaf bypass for morphological predicates (same principle as sgfe_engine.py)
        # Theory (SGC.Renormalization.Lumpability): Predicates with very low sheaf_energy
        # ARE valid coarse-graining operators by construction. The sheaf energy IS the
        # proof of global consistency - we don't need additional defect improvement.
        # dirichlet_gap_non_decrease: adding such ops can only increase expressive power.
        SHEAF_BYPASS_THRESHOLD = 0.1  # Morphological ops typically have sheaf_e ≈ 0.028
        sheaf_bypass = morph_pred.sheaf_energy <= SHEAF_BYPASS_THRESHOLD
        
        # Two acceptance paths:
        # 1. Sheaf bypass: sheaf_e ≤ 0.1 AND not catastrophic (regardless of improvement)
        # 2. Standard: sheaf_e ≤ 0.3 AND improves OR flat
        accept_as_renorm = (
            (sheaf_bypass and not severe_regress) or
            (sheaf_ok and not severe_regress and (any_improve or all(d <= 0 for d in deltas)))
        )
        
        if accept_as_renorm:
            log = {
                'op_name': op.name,
                'morph_term': morph_pred.term.canonical_name,
                'role': role,
                'sheaf_energy': morph_pred.sheaf_energy,
                'source': 'morph_algebra',
                'acceptance': 'renormalization',  # Not strict improvement
                'deltas': [int(d) for d in deltas],
            }
            accepted.append((op, log))
            
            if verbose:
                delta_str = ','.join(str(int(d)) for d in deltas)
                print(f"    [MORPH] RENORM ACCEPTED: {op.name} (sheaf={morph_pred.sheaf_energy:.3f}, deltas=[{delta_str}])", flush=True)
    
    # =========================================================================
    # OBJECT-LEVEL MORPHOLOGY (Phase 9: Object-Level Cohomology)
    # =========================================================================
    # If pixel-level morphology found nothing, try object-level.
    # This lifts to Shape-Role space where F(T_x(G)) = F(G).
    
    if not accepted and len(grids) > 0 and _time.monotonic() - _morph_start < _MORPH_BUDGET:
        if verbose:
            print(f"    [MORPH-OBJ] Attempting object-level morphology...", flush=True)
        try:
            from arc_morph_algebra import SceneGraphLifting, ROLE_TO_CHANNEL, MorphTerm, MorphOp
            from arc_sgc_phase21 import SceneGraphBuilder
            
            builder = SceneGraphBuilder()
            lifting = SceneGraphLifting(max_canonical_size=16)
            
            # Build scene graphs for all examples
            scene_graphs = []
            for i in active_indices:
                ex = task.train_examples[i]
                sg = builder.build(ex.input_grid)
                scene_graphs.append(sg)
            
            if scene_graphs:
                # Try object-level opening on each role
                for role_name in ['MAJORITY', 'MINORITY']:
                    if role_name not in ROLE_TO_CHANNEL:
                        continue
                    
                    channel_idx = ROLE_TO_CHANNEL[role_name]
                    
                    # Lift all examples and check consistency
                    lattices = []
                    obj_lists = []
                    for sg, roles in zip(scene_graphs, roles_list):
                        lattice, obj_list = lifting.lift(sg, roles)
                        lattices.append(lattice)
                        obj_lists.append(obj_list)
                    
                    # Check sheaf energy in canonical space
                    channel_sums = [lat[channel_idx].sum().item() for lat in lattices]
                    if all(s == 0 for s in channel_sums):
                        continue
                    
                    # Variance of normalized volumes = sheaf energy
                    mean_sum = np.mean(channel_sums)
                    if mean_sum > 0:
                        normalized = [s / mean_sum for s in channel_sums]
                        obj_sheaf_energy = np.var(normalized)
                    else:
                        obj_sheaf_energy = 0.0
                    
                    if obj_sheaf_energy <= RENORM_THRESHOLD:
                        if verbose:
                            print(f"    [MORPH-OBJ] {role_name} channel sheaf_energy={obj_sheaf_energy:.4f}", flush=True)
                        
                        # =============================================================
                        # Phase 10: Create executable RoleBasedAtomicOp
                        # =============================================================
                        # Analyze residuals to determine action (fill/erase/recolor)
                        
                        from arc_morph_algebra import SE_CROSS
                        
                        # Tally color transitions in residual NEAR this role's objects
                        # Key insight: we want to detect actions like "fill near MAJORITY"
                        n_colors = 10
                        role_tally = np.zeros((n_colors, n_colors), dtype=int)
                        
                        for pred_grid, tgt, roles, sg in zip(predictions, targets, roles_list, scene_graphs):
                            # Find color for this role
                            role_color = None
                            for c, r in roles.items():
                                if r.upper() == role_name:
                                    role_color = c
                                    break
                            
                            if role_color is None:
                                continue
                            
                            # Get all objects with this role
                            role_objects = [o for o in sg.objects.values() if o.color == role_color]
                            if not role_objects:
                                continue
                            
                            # Create expanded mask (dilate role objects to find "near" region)
                            role_mask = np.zeros(pred_grid.shape, dtype=bool)
                            for obj in role_objects:
                                r1, c1, r2, c2 = obj.bbox
                                # Expand bbox by 2 pixels
                                r1_exp = max(0, r1 - 2)
                                c1_exp = max(0, c1 - 2)
                                r2_exp = min(pred_grid.shape[0], r2 + 2)
                                c2_exp = min(pred_grid.shape[1], c2 + 2)
                                role_mask[r1_exp:r2_exp, c1_exp:c2_exp] = True
                            
                            # Tally transitions in residual NEAR role objects
                            wrong = pred_grid != tgt
                            for r_idx in range(tgt.shape[0]):
                                for c_idx in range(tgt.shape[1]):
                                    if wrong[r_idx, c_idx] and role_mask[r_idx, c_idx]:
                                        role_tally[int(pred_grid[r_idx, c_idx]), int(tgt[r_idx, c_idx])] += 1
                        
                        # Determine dominant action
                        fill_from_bg = int(role_tally[0, :].sum())
                        erase_to_bg = int(role_tally[:, 0].sum())
                        recolor_other = int(role_tally.sum()) - fill_from_bg - erase_to_bg
                        
                        # Choose action and create op
                        morph_filter = 'open_cross'  # Default: opening with cross SE
                        
                        if erase_to_bg >= fill_from_bg and erase_to_bg > 0:
                            # Erase action: remove objects that survive opening
                            action = 'erase'
                            action_role = None
                            action_color = 0
                            
                            role_op = make_role_based_op(
                                role=role_name,
                                morph_term_name=morph_filter,
                                action=action,
                                action_role=action_role,
                                action_color=action_color,
                            )
                            
                        elif fill_from_bg > 0:
                            # Fill action: determine fill color from target
                            to_color = int(np.argmax(role_tally[0, 1:]) + 1)  # Skip bg
                            
                            # Try to map to a role
                            fill_role = None
                            for ex_roles in roles_list:
                                for c, r in ex_roles.items():
                                    if c == to_color and r.upper() != 'BG':
                                        fill_role = r.upper()
                                        break
                                if fill_role:
                                    break
                            
                            role_op = make_role_based_op(
                                role=role_name,
                                morph_term_name=morph_filter,
                                action='fill',
                                action_role=fill_role,
                                action_color=to_color if fill_role is None else None,
                            )
                        else:
                            # No clear action, skip
                            continue
                        
                        # Test the op on all examples
                        deltas = []
                        any_improve = False
                        severe_regress = False
                        
                        for pred_grid, tgt in zip(predictions, targets):
                            try:
                                new_pred = role_op.apply(pred_grid)
                                old_defect = (pred_grid != tgt).sum()
                                new_defect = (new_pred != tgt).sum()
                                delta = new_defect - old_defect
                                deltas.append(delta)
                                
                                if delta < 0:
                                    any_improve = True
                                if old_defect > 0 and delta > old_defect * SEVERE_REGRESSION:
                                    severe_regress = True
                            except Exception as ex:
                                if verbose:
                                    print(f"    [MORPH-OBJ] Op apply error: {ex}", flush=True)
                                severe_regress = True
                                break
                        
                        # Accept if sheaf-consistent and not catastrophic
                        accept_obj_op = not severe_regress and (any_improve or all(d <= 0 for d in deltas))
                        
                        if accept_obj_op and deltas:
                            log = {
                                'op_name': role_op.name,
                                'morph_term': morph_filter,
                                'role': role_name,
                                'sheaf_energy': obj_sheaf_energy,
                                'source': 'object_cohomology',
                                'acceptance': 'role_based_renormalization',
                                'deltas': [int(d) for d in deltas],
                            }
                            accepted.append((role_op, log))
                            
                            if verbose:
                                delta_str = ','.join(str(int(d)) for d in deltas)
                                print(f"    [MORPH-OBJ] ACCEPTED: {role_op.name} (sheaf={obj_sheaf_energy:.4f}, deltas=[{delta_str}])", flush=True)
                        elif verbose:
                            print(f"    [MORPH-OBJ] Rejected {role_name} op: severe_regress={severe_regress}, any_improve={any_improve}", flush=True)
        
        except Exception as e:
            if verbose:
                print(f"    [MORPH-OBJ] Error in object-level synthesis: {e}", flush=True)
    
    return accepted


def _tensor_residual_refine(
    task,
    program,
    active_indices: list,
    seed: int = 42,
    verbose: bool = False,
    sgfe_library=None,
) -> list:
    """
    Tensor Logic refinement primitive: learn a residual predicate, infer
    the analytic color action, synthesize ops, accept only if IG > 0 on
    EVERY training example.

    SGC GROUNDING:
      1. WHERE (partition): discover_residual_predicate learns the
         optimal coarse-graining Π via gradient descent on class-weighted
         BCE against the residual mask.
      2. WHAT (macro-dynamics): tally (from_color, to_color) on the
         masked region across all examples → analytic color rule.
      3. ACCEPTANCE (information gain): apply the induced op and verify
         defect decreases on every example (worst-case, not mean).

    SGFE v2.0 (Renormalization.lean):
      4. RENORMALIZATION: accepted Π collapses into new AtomicOp in
         sgfe_library (dirichlet_gap_non_decrease).

    Returns:
        List of (AtomicOp, structured_log_dict) tuples for accepted ops.
        Empty list if no improvement found or tensor logic unavailable.
    """
    if not HAS_TENSOR_LOGIC:
        return []

    import time as _time
    _tl_start = _time.monotonic()
    _TL_BUDGET = 30.0  # seconds: hard time limit for tensor refinement

    n_ex = len(task.train_examples)
    if not active_indices:
        return []

    # Pre-compute predictions for ALL examples (cached for IG scoring)
    all_preds_cache = []
    all_targets_cache = []
    for ex in task.train_examples:
        inp = ex.input_grid.data.numpy()
        tgt = ex.output_grid.data.numpy()
        all_targets_cache.append(tgt)
        try:
            all_preds_cache.append(program.apply(inp))
        except Exception:
            all_preds_cache.append(inp.copy())

    # Collect targets, predictions for active examples (for learning)
    # NOTE: Features are computed from PREDICTIONS (not inputs), because
    # the predicate will be applied to the program's output at inference time.
    # When the program changes shape (crop/upscale), input != output space.
    grids = []  # prediction-space grids (used for feature encoding)
    targets = []
    predictions = []
    for i in active_indices:
        targets.append(all_targets_cache[i])
        predictions.append(all_preds_cache[i])
        grids.append(all_preds_cache[i])  # features from prediction space

    # Check pred/target shapes match per-example
    for p, t in zip(predictions, targets):
        if p.shape != t.shape:
            if verbose:
                print(f"    [TENSOR] shape mismatch: pred={p.shape} tgt={t.shape}", flush=True)
            return []

    # Check all grids have the same shape (required for tensor stacking)
    shapes = set(g.shape for g in grids)
    if len(shapes) > 1:
        if verbose:
            print(f"    [TENSOR] heterogeneous shapes: {shapes}", flush=True)
        return []

    # SGFE v2.1: Cluster examples by transformation signature before TL
    # Theory (positive_Ricci_tensorizes): global section exists only if all
    # stalks belong to same geometric class; clustering ensures uniform symmetry
    gradients = [DiscreteGradient.compute(p, t) for p, t in zip(predictions, targets)]
    clusters = cluster_by_transformation_signature(gradients, threshold=0.3)
    n_clusters = len(clusters)
    
    # Split TL budget across clusters (audit issue #7)
    _TL_BUDGET_PER_CLUSTER = _TL_BUDGET / max(n_clusters, 1)
    
    if verbose and n_clusters > 1:
        print(f"    [TENSOR] clustering: {n_clusters} clusters from {len(gradients)} examples", flush=True)
    
    # Run TL separately per cluster and merge results
    all_discovered = []
    for cluster_idx, cluster_indices in enumerate(clusters):
        # Check time budget
        if _time.monotonic() - _tl_start > _TL_BUDGET:
            break
        
        # Extract examples for this cluster
        cluster_grids = [grids[i] for i in cluster_indices]
        cluster_targets = [targets[i] for i in cluster_indices]
        cluster_preds = [predictions[i] for i in cluster_indices]
        
        if not cluster_grids:
            continue
        
        # Adjust steps based on cluster budget (fewer steps = faster, stay within budget)
        adjusted_steps = max(50, int(100 * _TL_BUDGET_PER_CLUSTER / 15.0))
        
        # Learn residual predicate for this cluster
        # SGFE v2.1: use_object_features=True enables translation-invariant predicates
        # SGFE v2.8: lumpable_only=True forces low sheaf_energy by excluding
        # position-dependent features (SGC.Renormalization.Lumpability)
        import os
        _LUMPABLE_ONLY = os.getenv('SGFE_LUMPABLE_ONLY', '0') == '1'
        learner = TensorPredicateLearner(
            n_factors=4, lr=0.05, steps=adjusted_steps, min_f1=0.30,
            use_hermite_features=False,
            use_object_features=True)
        learner.lumpable_only = _LUMPABLE_ONLY
        cluster_discovered = learner.discover_residual_predicate(
            cluster_grids, cluster_targets, cluster_preds, 
            seed=seed + cluster_idx, verbose=verbose)
        
        # Tag discovered predicates with cluster info for later merging
        for dp in cluster_discovered:
            dp._cluster_idx = cluster_idx
            dp._cluster_indices = cluster_indices
        
        all_discovered.extend(cluster_discovered)
    
    discovered = all_discovered

    if verbose:
        print(f"    [TENSOR] discovered={len(discovered)} predicates "
              f"(n_active={len(active_indices)}, clusters={n_clusters})", flush=True)

    if not discovered:
        return []

    # Check time budget after gradient descent
    if _time.monotonic() - _tl_start > _TL_BUDGET:
        return []

    # --- MI SCORING: rank predicates by information content ---
    # MI(P_mask, C) measures how well the mask separates "pixels that need
    # changing" from those that don't. Higher MI = more informative partition.
    for dp in discovered:
        mi_scores = []
        for e_idx in range(len(grids)):
            if e_idx < len(dp.masks):
                mi = _compute_change_mi(dp.masks[e_idx], predictions[e_idx], targets[e_idx])
                mi_scores.append(mi)
        dp._mi_avg = float(np.mean(mi_scores)) if mi_scores else 0.0
        dp._mi_min = float(np.min(mi_scores)) if mi_scores else 0.0

    # Sort by average MI (highest first) — process most informative predicates first
    discovered.sort(key=lambda d: -d._mi_avg)

    if verbose:
        for dp in discovered:
            print(f"    [TENSOR] predicate F1={dp.f1:.3f} MI_avg={dp._mi_avg:.4f} "
                  f"MI_min={dp._mi_min:.4f} top={dp.top_features[:2]}", flush=True)

    accepted = []

    for dp in discovered:
        if _time.monotonic() - _tl_start > _TL_BUDGET:
            break
        # Skip predicates with negligible MI (mask doesn't capture change structure)
        if dp._mi_avg < 0.01:
            if verbose:
                print(f"    [TENSOR] SKIP predicate MI_avg={dp._mi_avg:.4f} < 0.01", flush=True)
            continue
        # Wrap as callable predicate
        tp = make_tensor_predicate_expr(dp, dp.weights, dp.bias)

        # --- DECOUPLE WHERE / WHAT ---
        # Tally (from_color, to_color) on masked pixels across examples
        n_colors = 10
        color_tally = np.zeros((n_colors, n_colors), dtype=int)
        for e_idx in range(len(grids)):
            if e_idx >= len(dp.masks):
                continue
            mask = dp.masks[e_idx]
            pred_out = predictions[e_idx]
            tgt = targets[e_idx]
            wrong_in_mask = mask & (pred_out != tgt)
            if wrong_in_mask.any():
                for r in range(tgt.shape[0]):
                    for c in range(tgt.shape[1]):
                        if wrong_in_mask[r, c]:
                            color_tally[int(pred_out[r, c]), int(tgt[r, c])] += 1

        total_transitions = int(color_tally.sum())
        if total_transitions == 0:
            continue

        # Classify residual type from tallies:
        # R+ (fill): bg(0) -> color  (additive)
        # R- (erase): color -> bg(0) (subtractive)
        # Recolor:    color_a -> color_b
        fill_from_bg = int(color_tally[0, :].sum())
        erase_to_bg = int(color_tally[:, 0].sum())
        recolor_count = total_transitions - fill_from_bg - erase_to_bg

        # SGFE v2.5 CRITICAL FIX: Crystallize BEFORE building candidate ops
        # The tensor predicate uses neural network weights that don't generalize
        # across training examples. We must crystallize to discrete DSL first,
        # then evaluate the crystallized ops. This is the key to cross-task learning.
        # Use prediction-space grid (same space where predicate acts) for role extraction.
        first_input = grids[0]
        color_roles = detect_color_roles(first_input)
        crystal_pred = crystallize_tensor_predicate(dp, color_roles=color_roles, n_top=2)
        
        if not crystal_pred:
            # Fallback to tensor predicate if crystallization fails
            crystal_pred = None
            use_tensor_pred = True
            if verbose:
                print(f"    [SGFE] Crystallization FAILED for {tp.name}: top_features={dp.top_features[:3]}", flush=True)
        else:
            use_tensor_pred = False
            if verbose:
                print(f"    [SGFE] Crystallized {tp.name} -> {crystal_pred}", flush=True)

            # SGFE v2.6: verify role-based predicate round-trips into the
            # closed vocabulary on a real prediction-space grid.
            try:
                _probe_grid = grids[0]
                _resolved = resolve_role_to_color(crystal_pred, _probe_grid)
                _predicates = _compute_pixel_predicates(_probe_grid)
                _missing = []
                for _part in _resolved.split("&"):
                    _name = _part[1:] if _part.startswith("!") else _part
                    if _name not in _predicates:
                        _missing.append(_name)
                if _missing:
                    if verbose:
                        print(f"    [SGFE] Crystallized predicate key miss: {crystal_pred} -> {_resolved} "
                              f"missing={_missing[:3]}", flush=True)
                    crystal_pred = None
                    use_tensor_pred = True
            except Exception as _rt_exc:
                if verbose:
                    print(f"    [SGFE] Crystallized predicate probe exception: {_rt_exc}", flush=True)
                crystal_pred = None
                use_tensor_pred = True

        # Build candidate ops based on dominant transition type
        # SGFE v2.5: Use crystallized predicate (string) for evaluation
        candidate_ops = []

        if fill_from_bg > 0:
            # Fill: bg -> dominant target color
            fill_target_int = int(np.argmax(color_tally[0, 1:])) + 1
            if color_tally[0, fill_target_int] > 0:
                if use_tensor_pred:
                    op = _make_predicated_fill(tp, fill_target_int)
                    op_name = f"fill({fill_target_int}|{tp.name})"
                else:
                    # Use role-based crystallized op
                    fill_role = color_roles.get(fill_target_int, str(fill_target_int))
                    op = _make_predicated_fill(crystal_pred, fill_role)
                    op_name = f"fill({fill_role}|{crystal_pred})"
                candidate_ops.append(
                    (op, op_name,
                     f"R+: 0->{fill_target_int} x{color_tally[0, fill_target_int]}"))

        if erase_to_bg > 0:
            # Erase: each source color -> bg
            for src in range(1, n_colors):
                if color_tally[src, 0] > 0:
                    if use_tensor_pred:
                        op = _make_predicated_erase(tp, src)
                        op_name = f"erase({src}|{tp.name})"
                    else:
                        src_role = color_roles.get(src, str(src))
                        op = _make_predicated_erase(crystal_pred, src_role)
                        op_name = f"erase({src_role}|{crystal_pred})"
                    candidate_ops.append(
                        (op, op_name,
                         f"R-: {src}->0 x{color_tally[src, 0]}"))

        # Recolor: each (src, tgt) pair where src != 0, tgt != 0
        for src in range(1, n_colors):
            for tgt_c in range(1, n_colors):
                if src != tgt_c and color_tally[src, tgt_c] > 0:
                    if use_tensor_pred:
                        op = _make_predicated_recolor(tp, src, tgt_c)
                        op_name = f"recolor({src}->{tgt_c}|{tp.name})"
                    else:
                        src_role = color_roles.get(src, str(src))
                        tgt_role = color_roles.get(tgt_c, str(tgt_c))
                        op = _make_predicated_recolor(crystal_pred, src_role, tgt_role)
                        op_name = f"recolor({src_role}->{tgt_role}|{crystal_pred})"
                    candidate_ops.append(
                        (op, op_name,
                         f"recolor: {src}->{tgt_c} x{color_tally[src, tgt_c]}"))

        if not candidate_ops:
            continue

        # --- SHEAF VERIFICATION (Directive 6) ---
        # Check predicate forms a valid global section before synthesizing ops.
        # Theory: positive_Ricci_tensorizes — native sheaf → 100% compositional.
        _sheaf_e = 0.0
        if HAS_SGFE and len(dp.masks) >= 2:
            _sheaf_e = sheaf_consistency_energy(
                dp.masks, grids, targets, predictions)
            if verbose:
                print(f"    [SGFE] sheaf_energy={_sheaf_e:.4f} for {tp.name}", flush=True)

        # --- PER-EXAMPLE ACCEPTANCE (SGFE v2.0 Universal Scorer) ---
        # FunctionalBlanket.lean: ε_func = withinClassVariance / totalVariance
        # For discrete ARC: pixel mismatch IS ε_func (mode='discrete')
        # For continuous (Hermite features): ANOVA IS ε_func (mode='continuous')
        # sgfe_defect_delta is the SINGLE SOURCE OF TRUTH for Δε_func.
        for op, op_name, transition_desc in candidate_ops:
            per_ex_results = []
            all_positive = True

            for i in range(n_ex):
                try:
                    pred_before = all_preds_cache[i]
                    tgt = all_targets_cache[i]
                    if pred_before.shape != tgt.shape:
                        all_positive = False
                        break

                    # Apply the candidate op
                    pred_after = op.apply(pred_before)
                    if pred_after.shape != tgt.shape:
                        all_positive = False
                        break

                    # SGFE v2.0: Universal functional defect scorer
                    # mode='discrete' = pixel mismatch (for ARC grids)
                    if HAS_SGFE:
                        result = sgfe_defect_delta(
                            pred_before, pred_after, tgt, mode='discrete')
                    else:
                        # Fallback: manual computation
                        d_before = float(np.mean(pred_before != tgt))
                        d_after = float(np.mean(pred_after != tgt))
                        result = {
                            'eps_before': d_before,
                            'eps_after': d_after,
                            'delta': d_before - d_after,
                            'improved': d_before > d_after,
                            'mode': 'discrete',
                            'n_wrong_before': int((pred_before != tgt).sum()),
                            'n_wrong_after': int((pred_after != tgt).sum()),
                        }

                    per_ex_results.append(result)

                    # Track regression but don't break yet (v2.0 allows small regressions)
                    if result['delta'] < 0:
                        all_positive = False
                except Exception as _e:
                    all_positive = False
                    if verbose:
                        print(f"      [SGFE] REJECT {op_name}: ex{i} exception={_e}", flush=True)
                    break

            # SGFE v2.0: Use refined acceptance gate (allows gradual improvement)
            # Theory: grokking is gradual, early predicates may not be perfect on all examples
            if per_ex_results:
                total_delta = sum(r['delta'] for r in per_ex_results)
                worst_delta = min(r['delta'] for r in per_ex_results)

                # Use SGFE gate: net functional-defect decrease + MI + sheaf consistency.
                if HAS_SGFE:
                    gate_ok, gate_reason = sgfe_acceptance_gate_v2(
                        total_delta=total_delta,
                        worst_delta=worst_delta,
                        mi_score=dp._mi_avg,
                        sheaf_energy=_sheaf_e,
                        mi_threshold=0.10,  # Relaxed from 0.25
                        sheaf_threshold=1.0,  # Relaxed from 0.6
                    )
                else:
                    # Fallback: strict gate (all_positive required)
                    gate_ok = all_positive and total_delta > 1e-6
                    gate_reason = "all_positive" if gate_ok else "regression"
                
                if not gate_ok:
                    if verbose:
                        print(f"      [SGFE v2] REJECT {op_name}: {gate_reason}", flush=True)
                    continue

                if total_delta > 1e-6:
                    # Compute ANOVA defect for logging (supplementary diagnostic)
                    _eps_anova = 0.0
                    if HAS_SGFE:
                        try:
                            _eps_anova = functional_blanket_variance(
                                all_preds_cache[0], all_targets_cache[0])
                        except Exception:
                            pass

                    # Per-example detail for logging
                    per_ex_detail = [
                        (r['eps_before'], r['eps_after'],
                         r['n_wrong_before'], r['n_wrong_after'])
                        for r in per_ex_results
                    ]

                    log_entry = {
                        'op': op_name,
                        'transition': transition_desc,
                        'f1': dp.f1,
                        'precision': dp.precision,
                        'recall': dp.recall,
                        'mi_avg': dp._mi_avg,
                        'mi_min': dp._mi_min,
                        'sheaf_energy': _sheaf_e,
                        'eps_anova': _eps_anova,
                        'top_features': dp.top_features[:3],
                        'total_delta': total_delta,  # SGFE v2.0: renamed from total_ig
                        'worst_delta': worst_delta,  # SGFE v2.0: renamed from worst_ig
                        'per_example': per_ex_detail,
                    }
                    accepted.append((op, log_entry))

                    # SGFE v2.5: Add the ALREADY-CRYSTALLIZED op to the library
                    # Crystallization happened BEFORE the acceptance gate (line ~2865)
                    # so the op we're adding is already role-based and generalizable.
                    #
                    # SGFE v2.6: Strict Sheaf Energy Gate (per SGC theory)
                    # Theory (GlobalSection.lean): A predicate with high sheaf_energy
                    # is NOT a global section across training examples. It solves the
                    # immediate task by overfitting to spatial accidentals, and will
                    # cause negative transfer when applied to peer tasks.
                    # Gate: Only predicates forming valid global sections (sheaf_energy ≤ 0.6)
                    # may attempt cross-task validation.
                    SHEAF_ENERGY_STRICT_THRESHOLD = 0.6
                    if _sheaf_e > SHEAF_ENERGY_STRICT_THRESHOLD:
                        if verbose:
                            print(f"    [SGFE v2.6] SHEAF GATE REJECT {op_name}: "
                                  f"sheaf_energy={_sheaf_e:.3f} > {SHEAF_ENERGY_STRICT_THRESHOLD} "
                                  f"(not a global section)", flush=True)
                        # Still accept locally but DO NOT submit to cross-task validator
                        # This prevents spatial overfitting from poisoning the library
                        continue
                    
                    if sgfe_library is not None:
                        # Compute transformation signature for SheafAtlas chart assignment
                        _trans_sig = (0.5, 0.25, 0.25, 0.0, 0.5, 0.5)  # Default
                        if HAS_SHEAF_ATLAS:
                            try:
                                _trans_sig = compute_transformation_signature(
                                    all_preds_cache, all_targets_cache
                                )
                            except Exception:
                                pass
                        
                        sgfe_library.add_new_primitive(
                            name=op_name,
                            op=op,
                            metadata={
                                'f1': dp.f1,
                                'mi_avg': dp._mi_avg,
                                'sheaf_energy': _sheaf_e,
                                'total_delta': total_delta,
                                'task_id': task.task_id,
                                'crystallized': not use_tensor_pred,
                                'transformation_signature': _trans_sig,
                            }
                        )
                        if verbose:
                            tag = "CRYSTALLIZED" if not use_tensor_pred else "TENSOR"
                            print(f"    [SGFE] {tag} {op_name} -> library "
                                  f"(size={sgfe_library.size})", flush=True)

                    if verbose:
                        print(f"    [SGFE] ACCEPTED {op_name} "
                              f"F1={dp.f1:.3f} Δε={total_delta:.4f} "
                              f"worst={worst_delta:.4f}", flush=True)


                    # Take only the first accepted op per predicate
                    break

    # Return only the single best op (highest total Δε_func)
    # Composing multiple tensor ops from different factors can conflict.
    if accepted:
        accepted.sort(key=lambda x: -x[1]['total_delta'])
        return [accepted[0]]
    return []


def _make_dynamic_fill(pred_name: str) -> AtomicOp:
    """
    Fill bg pixels matching predicate with INFERRED color.
    
    Color inference: find the minority non-bg color in the input.
    This handles tasks where the fill color varies across examples
    but the spatial predicate is consistent (e.g., "fill cross of 8s
    with the OTHER color in the grid").
    
    SGC Theory: The orbit (predicate) is fixed; only the representative
    (color) varies. This is the quotient by the color permutation group.
    """
    pn = pred_name

    def apply(grid: np.ndarray) -> np.ndarray:
        predicates = _compute_pixel_predicates(grid)
        parts = pn.split("&")
        mask = np.ones(grid.shape, dtype=bool)
        for part in parts:
            if part in predicates:
                mask = mask & predicates[part]
            else:
                return grid.copy()
        
        # Infer fill color: minority non-bg color in the input
        bg_mask = grid == BG
        fill_region = bg_mask & mask
        if not fill_region.any():
            return grid.copy()
        
        # Find non-bg colors sorted by frequency (ascending = minority first)
        colors, counts = np.unique(grid[~bg_mask], return_counts=True)
        if len(colors) == 0:
            return grid.copy()
        
        # Use the minority non-bg color as fill
        minority_idx = np.argmin(counts)
        fill_color = int(colors[minority_idx])
        
        result = grid.copy()
        result[fill_region] = fill_color
        return result

    return AtomicOp(
        f"fill_dynamic({pn})",
        apply,
        f"fill bg with inferred color where {pn}"
    )


def _make_role_fill_cross() -> AtomicOp:
    """
    Fill the cross of the MAJORITY non-bg color with the MINORITY non-bg color.
    
    This is a fully role-based op: both the predicate anchor color (whose cross)
    and the fill color (what to fill with) are computed from the input's color
    statistics at apply time.
    
    SGC Theory: This quotients by the FULL color permutation group S_10.
    The orbit is "fill cross of majority with minority" — invariant under
    any color relabeling.
    """
    def apply(grid: np.ndarray) -> np.ndarray:
        # Classify colors by role
        non_bg = grid[grid != BG]
        if len(non_bg) == 0:
            return grid.copy()
        colors, counts = np.unique(non_bg, return_counts=True)
        if len(colors) < 2:
            return grid.copy()
        
        order = np.argsort(counts)
        minority_color = int(colors[order[0]])
        majority_color = int(colors[order[-1]])
        
        # Compute cross of majority color
        predicates = _compute_pixel_predicates(grid)
        cross_key = f"cross_{majority_color}"
        if cross_key not in predicates:
            return grid.copy()
        cross_mask = predicates[cross_key]
        
        # Fill bg pixels in cross with minority color
        result = grid.copy()
        fill_region = (grid == BG) & cross_mask
        result[fill_region] = minority_color
        return result
    
    return AtomicOp(
        "fill_role(minority|cross_majority)",
        apply,
        "fill cross of majority color with minority color"
    )


def _make_role_fill_adj() -> AtomicOp:
    """
    Fill bg pixels adjacent to the MAJORITY color with the MINORITY color.
    """
    def apply(grid: np.ndarray) -> np.ndarray:
        non_bg = grid[grid != BG]
        if len(non_bg) == 0:
            return grid.copy()
        colors, counts = np.unique(non_bg, return_counts=True)
        if len(colors) < 2:
            return grid.copy()
        
        order = np.argsort(counts)
        minority_color = int(colors[order[0]])
        majority_color = int(colors[order[-1]])
        
        predicates = _compute_pixel_predicates(grid)
        adj_key = f"adj_to_{majority_color}"
        if adj_key not in predicates:
            return grid.copy()
        adj_mask = predicates[adj_key]
        
        result = grid.copy()
        fill_region = (grid == BG) & adj_mask
        result[fill_region] = minority_color
        return result
    
    return AtomicOp(
        "fill_role(minority|adj_majority)",
        apply,
        "fill bg adjacent to majority color with minority color"
    )


def _make_role_erase_minority() -> AtomicOp:
    """
    Erase (set to BG) all pixels of the MINORITY non-bg color.
    """
    def apply(grid: np.ndarray) -> np.ndarray:
        non_bg = grid[grid != BG]
        if len(non_bg) == 0:
            return grid.copy()
        colors, counts = np.unique(non_bg, return_counts=True)
        if len(colors) < 2:
            return grid.copy()
        
        minority_color = int(colors[np.argmin(counts)])
        result = grid.copy()
        result[result == minority_color] = BG
        return result
    
    return AtomicOp(
        "erase_role(minority)",
        apply,
        "erase minority color"
    )


def _make_dynamic_erase(pred_name: str) -> AtomicOp:
    """
    Erase ALL non-bg pixels matching predicate (set to BG).
    
    Unlike _make_predicated_erase which targets a specific color,
    this erases any color matching the predicate. Handles tasks where
    the erase target color varies across examples.
    """
    pn = pred_name

    def apply(grid: np.ndarray) -> np.ndarray:
        predicates = _compute_pixel_predicates(grid)
        parts = pn.split("&")
        mask = np.ones(grid.shape, dtype=bool)
        for part in parts:
            if part in predicates:
                mask = mask & predicates[part]
            else:
                return grid.copy()
        result = grid.copy()
        non_bg = grid != BG
        result[non_bg & mask] = BG
        return result

    return AtomicOp(
        f"erase_dynamic({pn})",
        apply,
        f"erase all non-bg where {pn}"
    )


# =============================================================================
# 3c. DREAM CONSOLIDATION: Compile successful chains into reusable skills
# =============================================================================
#
# THE GROKKING MECHANISM:
#   When the beam search finds Op1 -> Op2 -> Op3 that solves a task,
#   we compile this chain into a single "macro" operator.
#
#   Key insight: Our predicated ops are ALREADY dynamically general
#   (predicates recompute at apply time). So "fill(4|enclosed_by_fg)"
#   transfers as-is to any grid. The main thing to parametrize is COLORS
#   in recolor/fill/erase ops.
#
#   STRUCTURAL SIGNATURE: Strip colors from op names to get a structural key.
#     "recolor(1->3|between_8_h) -> fill(2|cross_5)" 
#     becomes "recolor(?->?|between_?_h) -> fill(?|cross_?)"
#   Programs with the same structural signature share a Bayesian posterior.
#
# =============================================================================

def _structural_signature(program_desc: str) -> str:
    """
    Strip specific color numbers from a program description to get a
    structural signature for transfer learning.
    
    "recolor(1->3|between_8_h) -> fill(2|cross_5)"
    => "recolor(?->?|between_?_h) -> fill(?|cross_?)"
    """
    # Pass 1: Replace digits at word boundaries (op parameters like "fill(4|...")
    sig = re.sub(r'\b(\d+)\b', '?', program_desc)
    # Pass 2: Replace digits flanked by underscores in predicate names
    #   e.g. between_8_h -> between_?_h, adj_to_3 -> adj_to_?, near8_5 -> near?_?
    sig = re.sub(r'(?<=_)(\d+)(?=_)', '?', sig)   # _8_ -> _?_
    sig = re.sub(r'(?<=_)(\d+)\b', '?', sig)       # _5) -> _?)
    sig = re.sub(r'(\w)(\d+)(?=_)', r'\1?', sig)   # near8_ -> near?_
    return sig


# =============================================================================
# 5a. NEAR-MISS JOURNAL: The Information Gradient
# =============================================================================
#
# SGC GROUNDING: The residual IS the information gradient — it tells the
# system exactly where its compression (model) breaks down. Recording
# the geometry of failures across tasks enables:
#   1. Clustering: tasks that fail for the same geometric reason
#   2. Abstraction: synthesizing new primitives from failure clusters
#   3. Compression progress: measuring new solves per library addition
#
# This is the missing "sleep phase" — DreamCoder's wake/sleep but for
# predicate discovery, not just program reuse.
# =============================================================================


@dataclass
class ResidualAnalysis:
    """
    Detailed analysis of a near-miss failure.

    Captures the geometry of WHAT went wrong, providing the features
    needed to cluster failures and synthesize missing abstractions.
    """
    task_id: str
    defect: float
    n_wrong_pixels: int
    n_total_pixels: int

    # --- Geometry ---
    is_connected: bool              # wrong pixels form one connected component
    n_components: int               # number of connected components
    is_border_concentrated: bool    # >50% of wrong pixels on border
    border_fraction: float          # fraction of wrong pixels on border
    is_scattered: bool              # wrong pixels are isolated (no adjacency)
    centroid: Tuple[float, float]   # (row, col) centroid of wrong pixels
    spread: float                   # std dev of wrong pixel positions

    # --- Color structure ---
    residual_colors: List[int]      # output colors needed for wrong pixels
    adjacent_input_colors: List[int]  # input colors adjacent to wrong pixels
    is_single_color: bool           # all wrong pixels need same output color

    # --- Predicate info ---
    best_predicate: str             # name of best predicate found
    best_predicate_f1: float        # F1 score of best predicate
    predicate_gap: float            # 1.0 - best_f1 (room for improvement)

    # --- Program info ---
    program_description: str        # the program that was tried
    refinement_round: int           # which refinement round this analysis is from

    def feature_vector(self) -> List[float]:
        """Compact feature vector for clustering."""
        return [
            self.defect,
            float(self.is_connected),
            float(self.n_components),
            self.border_fraction,
            float(self.is_scattered),
            float(self.is_single_color),
            float(len(self.residual_colors)),
            float(len(self.adjacent_input_colors)),
            self.best_predicate_f1,
            self.predicate_gap,
            self.spread,
        ]

    def cluster_key(self) -> str:
        """Coarse clustering key based on dominant failure mode."""
        parts = []
        if self.is_border_concentrated:
            parts.append("border")
        if self.is_connected and self.n_components == 1:
            parts.append("connected")
        elif self.is_scattered:
            parts.append("scattered")
        else:
            parts.append(f"components_{min(self.n_components, 5)}")
        if self.is_single_color:
            parts.append("single_color")
        else:
            parts.append(f"multi_color_{len(self.residual_colors)}")
        if self.predicate_gap < 0.2:
            parts.append("near_solved")
        elif self.predicate_gap > 0.7:
            parts.append("no_predicate")
        else:
            parts.append("partial_pred")
        return "|".join(parts)


def _analyze_residual(
    task_id: str,
    grids: List[np.ndarray],
    targets: List[np.ndarray],
    predictions: List[np.ndarray],
    best_pred_name: str = "",
    best_pred_f1: float = 0.0,
    program_desc: str = "",
    refine_round: int = 0,
) -> Optional[ResidualAnalysis]:
    """
    Analyze the residual pattern of a near-miss.

    Args:
        grids: input grids for training examples
        targets: target output grids
        predictions: current predictions
        best_pred_name: name of best predicate found in refinement
        best_pred_f1: F1 score of that predicate

    Returns:
        ResidualAnalysis or None if not a near-miss.
    """
    # Pool residuals across examples
    all_wrong = []
    all_wrong_positions = []
    all_residual_colors = set()
    all_adjacent_colors = set()
    n_total = 0
    n_wrong = 0

    for g, t, p in zip(grids, targets, predictions):
        if p.shape != t.shape:
            return None
        wrong = (p != t)
        n_total += t.size
        n_wrong += int(wrong.sum())

        if wrong.any():
            all_wrong.append(wrong)
            # Residual colors (what output colors are needed)
            all_residual_colors.update(int(c) for c in np.unique(t[wrong]))
            # Wrong pixel positions
            rows, cols = np.where(wrong)
            for r, c in zip(rows, cols):
                all_wrong_positions.append((r, c))
            # Adjacent input colors
            kernel = np.ones((3, 3), dtype=np.float32)
            kernel[1, 1] = 0
            for c_val in np.unique(g):
                if c_val == 0:
                    continue
                c_mask = (g == int(c_val)).astype(np.float32)
                adj = ndimage.convolve(c_mask, kernel, mode='constant', cval=0.0)
                if ((adj > 0) & wrong).any():
                    all_adjacent_colors.add(int(c_val))

    if n_wrong == 0 or n_total == 0:
        return None

    defect = n_wrong / n_total

    # Geometry: connectivity on FIRST example with wrong pixels
    is_connected = False
    n_components = 0
    is_scattered = False
    for w in all_wrong:
        if w.any():
            from scipy.ndimage import label as ndlabel
            labeled, n_cc = ndlabel(w)
            n_components = n_cc
            is_connected = (n_cc == 1)
            # Scattered: each wrong pixel is isolated (no adjacent wrong pixel)
            w_float = w.astype(np.float32)
            k = np.ones((3, 3), dtype=np.float32); k[1, 1] = 0
            adj_count = ndimage.convolve(w_float, k, mode='constant', cval=0.0)
            is_scattered = bool(np.all(adj_count[w] == 0))
            break

    # Border concentration
    border_count = 0
    for w in all_wrong:
        H, W = w.shape
        border_mask = np.zeros_like(w)
        border_mask[0, :] = True; border_mask[-1, :] = True
        border_mask[:, 0] = True; border_mask[:, -1] = True
        border_count += int((w & border_mask).sum())
    border_fraction = border_count / max(n_wrong, 1)

    # Centroid and spread
    if all_wrong_positions:
        positions = np.array(all_wrong_positions, dtype=np.float64)
        centroid = (float(positions[:, 0].mean()), float(positions[:, 1].mean()))
        spread = float(np.std(positions))
    else:
        centroid = (0.0, 0.0)
        spread = 0.0

    return ResidualAnalysis(
        task_id=task_id,
        defect=defect,
        n_wrong_pixels=n_wrong,
        n_total_pixels=n_total,
        is_connected=is_connected,
        n_components=n_components,
        is_border_concentrated=(border_fraction > 0.5),
        border_fraction=border_fraction,
        is_scattered=is_scattered,
        centroid=centroid,
        spread=spread,
        residual_colors=sorted(all_residual_colors),
        adjacent_input_colors=sorted(all_adjacent_colors),
        is_single_color=(len(all_residual_colors) == 1),
        best_predicate=best_pred_name,
        best_predicate_f1=best_pred_f1,
        predicate_gap=1.0 - best_pred_f1,
        program_description=program_desc,
        refinement_round=refine_round,
    )


class NearMissJournal:
    """
    Persistent journal of near-miss failures for the learning loop.

    SGC GROUNDING: This is the persistent world model that updates through
    interaction. Each entry records the information gradient (residual geometry)
    for a task where the model almost succeeded. The sleep phase clusters
    these entries and synthesizes new primitives.

    The journal enables:
    1. Automatic clustering of failure modes
    2. Identification of missing abstractions (each cluster = one)
    3. Measurement of compression progress (new solves per cycle)
    4. Prioritization of tasks for re-solving (epistemic active inference)
    """

    def __init__(self):
        self.entries: Dict[str, ResidualAnalysis] = {}  # task_id -> analysis
        self.cycle_history: List[Dict] = []  # track compression progress

    def record(self, analysis: ResidualAnalysis):
        """Record a near-miss analysis. Keeps best per task."""
        existing = self.entries.get(analysis.task_id)
        if existing is None or analysis.defect < existing.defect:
            self.entries[analysis.task_id] = analysis

    def cluster(self) -> Dict[str, List[ResidualAnalysis]]:
        """
        Cluster near-misses by failure mode.

        Each cluster represents a MISSING ABSTRACTION — a predicate or
        operation that, if added to the library, would solve multiple tasks.
        """
        clusters: Dict[str, List[ResidualAnalysis]] = {}
        for analysis in self.entries.values():
            key = analysis.cluster_key()
            clusters.setdefault(key, []).append(analysis)
        # Sort clusters by size (largest = most impactful missing abstraction)
        return dict(sorted(clusters.items(), key=lambda x: -len(x[1])))

    def sleep_phase(self, verbose: bool = False) -> List[Dict]:
        """
        DreamCoder-style sleep phase: analyze failure clusters and
        propose new library primitives.

        Returns list of proposed abstractions, each a dict with:
          - cluster_key: the failure mode
          - n_tasks: how many tasks this would help
          - task_ids: which tasks
          - common_adjacent_colors: colors frequently adjacent to failures
          - common_residual_colors: colors frequently needed
          - suggested_primitive_type: what kind of primitive is needed
          - description: human-readable description
        """
        clusters = self.cluster()
        proposals = []

        for key, entries in clusters.items():
            if len(entries) < 2:
                continue  # Need at least 2 tasks to justify a new primitive

            # Analyze common features across cluster
            all_adj_colors = Counter()
            all_res_colors = Counter()
            all_best_preds = Counter()
            total_gap = 0.0

            for e in entries:
                for c in e.adjacent_input_colors:
                    all_adj_colors[c] += 1
                for c in e.residual_colors:
                    all_res_colors[c] += 1
                if e.best_predicate:
                    all_best_preds[e.best_predicate] += 1
                total_gap += e.predicate_gap

            avg_gap = total_gap / len(entries)

            # Determine suggested primitive type
            parts = key.split("|")
            if "border" in parts:
                prim_type = "boundary_predicate"
                desc = f"Border-related predicate needed for {len(entries)} tasks"
            elif "connected" in parts and "single_color" in parts:
                prim_type = "region_fill"
                desc = f"Connected region fill for {len(entries)} tasks"
            elif "scattered" in parts:
                prim_type = "relational_predicate"
                desc = f"Relational predicate for scattered pixels in {len(entries)} tasks"
            elif "no_predicate" in parts:
                prim_type = "novel_computation"
                desc = f"Novel computational predicate needed for {len(entries)} tasks (no existing predicate matches)"
            else:
                prim_type = "composition"
                desc = f"Predicate composition needed for {len(entries)} tasks"

            # Common adjacent colors suggest which DSL atoms to prioritize
            common_adj = [c for c, n in all_adj_colors.most_common(3) if n >= len(entries) // 2]
            common_res = [c for c, n in all_res_colors.most_common(3) if n >= len(entries) // 2]

            proposal = {
                'cluster_key': key,
                'n_tasks': len(entries),
                'task_ids': [e.task_id for e in entries],
                'avg_predicate_gap': avg_gap,
                'common_adjacent_colors': common_adj,
                'common_residual_colors': common_res,
                'common_best_predicates': dict(all_best_preds.most_common(5)),
                'suggested_primitive_type': prim_type,
                'description': desc,
            }
            proposals.append(proposal)

            if verbose:
                print(f"\n  [SLEEP] Cluster '{key}' ({len(entries)} tasks):")
                print(f"    Tasks: {[e.task_id[:8] for e in entries]}")
                print(f"    Avg predicate gap: {avg_gap:.3f}")
                print(f"    Common adj colors: {common_adj}")
                print(f"    Suggested: {prim_type}")
                print(f"    {desc}")

        # Record cycle
        self.cycle_history.append({
            'n_near_misses': len(self.entries),
            'n_clusters': len(clusters),
            'n_proposals': len(proposals),
            'proposals': proposals,
        })

        return proposals

    def compression_progress(self) -> float:
        """Rate of improvement across sleep cycles."""
        if len(self.cycle_history) < 2:
            return 0.0
        prev = self.cycle_history[-2]['n_near_misses']
        curr = self.cycle_history[-1]['n_near_misses']
        return (prev - curr) / max(prev, 1)

    def save_to_json(self, path: str):
        """Serialize journal for persistence across sessions."""
        data = {
            'entries': {},
            'cycle_history': self.cycle_history,
        }
        for tid, a in self.entries.items():
            data['entries'][tid] = {
                'task_id': a.task_id,
                'defect': a.defect,
                'n_wrong_pixels': a.n_wrong_pixels,
                'n_total_pixels': a.n_total_pixels,
                'is_connected': a.is_connected,
                'n_components': a.n_components,
                'border_fraction': a.border_fraction,
                'is_scattered': a.is_scattered,
                'centroid': list(a.centroid),
                'spread': a.spread,
                'residual_colors': a.residual_colors,
                'adjacent_input_colors': a.adjacent_input_colors,
                'is_single_color': a.is_single_color,
                'best_predicate': a.best_predicate,
                'best_predicate_f1': a.best_predicate_f1,
                'predicate_gap': a.predicate_gap,
                'program_description': a.program_description,
                'refinement_round': a.refinement_round,
                'cluster_key': a.cluster_key(),
            }
        with open(path, 'w') as f:
            json.dump(data, f, indent=2)

    @classmethod
    def load_from_json(cls, path: str) -> 'NearMissJournal':
        """Load journal from previous session."""
        journal = cls()
        try:
            with open(path) as f:
                data = json.load(f)
            journal.cycle_history = data.get('cycle_history', [])
            for tid, d in data.get('entries', {}).items():
                journal.entries[tid] = ResidualAnalysis(
                    task_id=d['task_id'],
                    defect=d['defect'],
                    n_wrong_pixels=d['n_wrong_pixels'],
                    n_total_pixels=d['n_total_pixels'],
                    is_connected=d['is_connected'],
                    n_components=d['n_components'],
                    is_border_concentrated=d.get('border_fraction', 0) > 0.5,
                    border_fraction=d.get('border_fraction', 0),
                    is_scattered=d.get('is_scattered', False),
                    centroid=tuple(d.get('centroid', [0, 0])),
                    spread=d.get('spread', 0),
                    residual_colors=d.get('residual_colors', []),
                    adjacent_input_colors=d.get('adjacent_input_colors', []),
                    is_single_color=d.get('is_single_color', False),
                    best_predicate=d.get('best_predicate', ''),
                    best_predicate_f1=d.get('best_predicate_f1', 0),
                    predicate_gap=d.get('predicate_gap', 1.0),
                    program_description=d.get('program_description', ''),
                    refinement_round=d.get('refinement_round', 0),
                )
        except (FileNotFoundError, json.JSONDecodeError):
            pass
        return journal


@dataclass
class CompiledProgram:
    """
    A compiled operator chain stored for reuse (Dream Consolidation).
    
    This is the "grokked" form of a successful search result:
    - The program object itself (executable)
    - Structural signature for transfer matching
    - Bayesian posterior (success/failure tracking)
    - Source task metadata
    """
    program: CompositeOp
    description: str                # e.g. "recolor(1->3|between_8_h)"
    structural_sig: str             # e.g. "recolor(?->?|between_?_h)"
    source_task_id: str
    task_signature: str             # coarse task context for bucketing
    success_count: int = 0
    failure_count: int = 0
    alpha_prior: float = 2.0       # Optimistic prior (it already solved one task)
    beta_prior: float = 1.0
    best_defect: float = 0.0      # Best training defect (0.0 = perfect, >0 = near-miss)
    is_near_miss: bool = False    # True if stored as near-miss (not proven perfect)
    
    def content_hash(self) -> str:
        """Content-addressed hash (structural signature)."""
        return hashlib.sha256(self.structural_sig.encode()).hexdigest()[:16]
    
    def posterior_mean(self) -> float:
        a = self.alpha_prior + self.success_count
        b = self.beta_prior + self.failure_count
        return a / (a + b)
    
    def apply(self, grid: np.ndarray) -> np.ndarray:
        return self.program.apply(grid)
    
    @property
    def depth(self) -> int:
        return self.program.depth


def _reconstruct_atomic_op(name: str) -> Optional[AtomicOp]:
    """
    Reconstruct an AtomicOp from its name string.

    This is the inverse of the OperatorLibrary factories: given the name
    that was stored, rebuild the executable closure.

    Supported formats:
      fill(C|pred)                  -> predicated fill
      recolor(S->T|pred)            -> predicated recolor
      recolor(S->T)                 -> simple recolor
      erase(C|pred)                 -> predicated erase
      cmap(A->B,C->D,...)          -> color map
      rot90, rot180, rot270         -> rotation
      flip_h, flip_v, transpose     -> reflection
      shift(dr,dc)                  -> shift
      line_connect_all/h/v          -> line connect
      fill_holes                    -> fill holes
      crop_content                  -> content crop
      crop_color_C                  -> color crop
      extract_largest/smallest      -> object extraction
      upscale_Kx, downscale_Kx      -> scaling
      tile_h_K, tile_v_K            -> tiling
    """
    try:
        # --- Predicated fill: fill(C|pred) ---
        m = re.match(r'^fill\((\d+)\|(.+)\)$', name)
        if m:
            return _make_predicated_fill(m.group(2), int(m.group(1)))

        # --- Predicated recolor: recolor(S->T|pred) ---
        m = re.match(r'^recolor\((\d+)->(\d+)\|(.+)\)$', name)
        if m:
            return _make_predicated_recolor(m.group(3), int(m.group(1)), int(m.group(2)))

        # --- Predicated erase: erase(C|pred) ---
        m = re.match(r'^erase\((\d+)\|(.+)\)$', name)
        if m:
            return _make_predicated_erase(m.group(2), int(m.group(1)))

        # --- Simple recolor: recolor(S->T) ---
        m = re.match(r'^recolor\((\d+)->(\d+)\)$', name)
        if m:
            f, t = int(m.group(1)), int(m.group(2))
            return AtomicOp(name, lambda g, _f=f, _t=t: _fill_mask(g, g == _f, _t))

        # --- Color map: cmap(A->B,C->D,...) ---
        m = re.match(r'^cmap\((.+)\)$', name)
        if m:
            mapping = {}
            for pair in m.group(1).split(','):
                parts = pair.strip().split('->')
                if len(parts) == 2:
                    mapping[int(parts[0])] = int(parts[1])
            mp = dict(mapping)
            def cmap_apply(g, _m=mp):
                result = g.copy()
                for f, t in _m.items():
                    result[g == f] = t
                return result
            return AtomicOp(name, cmap_apply)

        # --- Geometric transforms ---
        if name == 'rot90':
            return AtomicOp(name, lambda g: np.rot90(g, 1).copy())
        if name == 'rot180':
            return AtomicOp(name, lambda g: np.rot90(g, 2).copy())
        if name == 'rot270':
            return AtomicOp(name, lambda g: np.rot90(g, 3).copy())
        if name == 'flip_h':
            return AtomicOp(name, lambda g: np.fliplr(g).copy())
        if name == 'flip_v':
            return AtomicOp(name, lambda g: np.flipud(g).copy())
        if name == 'transpose':
            return AtomicOp(name, lambda g: g.T.copy())

        # --- Shift: shift(dr,dc) ---
        m = re.match(r'^shift\((-?\d+),(-?\d+)\)$', name)
        if m:
            dr, dc = int(m.group(1)), int(m.group(2))
            return AtomicOp(name, lambda g, _dr=dr, _dc=dc: np.roll(np.roll(g, _dr, axis=0), _dc, axis=1))

        # --- Line connect ---
        if name == 'line_connect_all':
            return AtomicOp(name, _dynamic_line_connect_all)
        if name == 'line_connect_h':
            return AtomicOp(name, _dynamic_line_connect_horizontal)
        if name == 'line_connect_v':
            return AtomicOp(name, _dynamic_line_connect_vertical)

        # --- Fill holes ---
        if name == 'fill_holes':
            return AtomicOp(name, _dynamic_fill_holes)

        # --- Crop ---
        if name == 'crop_content':
            return AtomicOp(name, _dynamic_crop_content)
        m = re.match(r'^crop_color_(\d+)$', name)
        if m:
            cc = int(m.group(1))
            return AtomicOp(name, lambda g, _c=cc: _dynamic_crop_color(g, _c))

        # --- Extract ---
        if name == 'extract_largest':
            return AtomicOp(name, _dynamic_extract_largest)
        if name == 'extract_smallest':
            return AtomicOp(name, _dynamic_extract_smallest)
        m = re.match(r'^extract_color_(\d+)$', name)
        if m:
            cc = int(m.group(1))
            return AtomicOp(name, lambda g, _c=cc: _dynamic_crop_color(g, _c))

        # --- Scale ---
        m = re.match(r'^upscale_(\d+)x$', name)
        if m:
            k = int(m.group(1))
            return AtomicOp(name, lambda g, _k=k: np.repeat(np.repeat(g, _k, axis=0), _k, axis=1))
        m = re.match(r'^downscale_(\d+)x$', name)
        if m:
            k = int(m.group(1))
            return AtomicOp(name, lambda g, _k=k: g[::_k, ::_k].copy())
        m = re.match(r'^tile_h_(\d+)$', name)
        if m:
            k = int(m.group(1))
            return AtomicOp(name, lambda g, _k=k: np.tile(g, (1, _k)))
        m = re.match(r'^tile_v_(\d+)$', name)
        if m:
            k = int(m.group(1))
            return AtomicOp(name, lambda g, _k=k: np.tile(g, (_k, 1)))

        # --- Role-based ops ---
        if name == "fill_role(minority|cross_majority)":
            return _make_role_fill_cross()
        if name == "fill_role(minority|adj_majority)":
            return _make_role_fill_adj()
        if name == "erase_role(minority)":
            return _make_role_erase_minority()

        # --- Dynamic fill: fill_dynamic(pred) ---
        m = re.match(r'^fill_dynamic\((.+)\)$', name)
        if m:
            return _make_dynamic_fill(m.group(1))

        # --- Dynamic erase: erase_dynamic(pred) ---
        m = re.match(r'^erase_dynamic\((.+)\)$', name)
        if m:
            return _make_dynamic_erase(m.group(1))

        # --- Erase color (unconditional): erase_color(C) ---
        m = re.match(r'^erase_color\((\d+)\)$', name)
        if m:
            ec = int(m.group(1))
            return AtomicOp(name, lambda g, _c=ec: _fill_mask(g, g == _c, BG))

    except Exception:
        pass

    return None


def _reconstruct_program(description: str) -> Optional[CompositeOp]:
    """
    Reconstruct a CompositeOp from its description string.

    Parses " -> "-delimited chains like:
      "recolor(1->3|between_8_h) -> fill(2|cross_5)"
    and rebuilds each AtomicOp from its name.
    """
    step_names = [s.strip() for s in description.split(' -> ')]
    steps = []
    for sn in step_names:
        op = _reconstruct_atomic_op(sn)
        if op is None:
            return None  # Can't reconstruct — unknown op format
        steps.append(op)
    if not steps:
        return None
    return CompositeOp(steps=steps)


class CompiledProgramLibrary:
    """
    Content-addressed store of compiled programs (Dream Memory).
    
    Programs are indexed by STRUCTURAL SIGNATURE so that color-variant
    programs share the same slot. When a new task arrives, we try all
    compiled programs whose task_signature matches, ordered by posterior.
    
    This converts System-2 search results into System-1 instant lookups.
    """
    
    def __init__(self):
        # structural_sig_hash -> CompiledProgram
        self.programs: Dict[str, CompiledProgram] = {}
        # Track which task signatures have yielded programs
        self.sig_to_programs: Dict[str, List[str]] = {}  # task_sig -> [prog_hashes]
        # Near-miss programs: task_id -> CompiledProgram (best partial solution)
        self.near_misses: Dict[str, CompiledProgram] = {}
    
    def store(self, program: CompositeOp, description: str,
              source_task_id: str, task_signature: str) -> str:
        """
        Store a successful program. Returns content hash.
        
        If a program with the same structural signature already exists,
        reinforce it instead of duplicating.
        """
        struct_sig = _structural_signature(description)
        cp = CompiledProgram(
            program=program,
            description=description,
            structural_sig=struct_sig,
            source_task_id=source_task_id,
            task_signature=task_signature,
        )
        h = cp.content_hash()
        
        if h in self.programs:
            # Reinforce existing — keep the newer program (might be better)
            existing = self.programs[h]
            existing.success_count += 1
            # Update program if from a different task (broader generality proven)
            if existing.source_task_id != source_task_id:
                existing.program = program
                existing.description = description
        else:
            cp.success_count = 1  # It already solved one task
            self.programs[h] = cp
        
        # Index by task signature
        if task_signature not in self.sig_to_programs:
            self.sig_to_programs[task_signature] = []
        if h not in self.sig_to_programs[task_signature]:
            self.sig_to_programs[task_signature].append(h)
        
        return h
    
    def store_near_miss(self, program: CompositeOp, description: str,
                        source_task_id: str, task_signature: str,
                        defect: float) -> bool:
        """
        Store a near-miss program (defect < 0.1 but not perfect).
        
        Near-misses are indexed by task_id (task-specific partial solutions).
        Only the best near-miss per task is kept. If a perfect solution is
        later found, the near-miss is promoted to the main library.
        
        Returns True if stored (new or improved), False if existing is better.
        """
        if defect >= 0.1 or defect < 0.001:
            return False  # Not a near-miss (too bad or already perfect)
        
        # Only keep the best near-miss per task
        if source_task_id in self.near_misses:
            existing = self.near_misses[source_task_id]
            if existing.best_defect <= defect:
                return False  # Existing is better or equal
        
        struct_sig = _structural_signature(description)
        cp = CompiledProgram(
            program=program,
            description=description,
            structural_sig=struct_sig,
            source_task_id=source_task_id,
            task_signature=task_signature,
            best_defect=defect,
            is_near_miss=True,
            alpha_prior=1.0,  # Weaker prior than proven programs
            beta_prior=1.0,
        )
        self.near_misses[source_task_id] = cp
        return True

    def recall_near_miss(self, task_id: str) -> Optional[CompiledProgram]:
        """Recall the best near-miss program for a specific task."""
        return self.near_misses.get(task_id)

    def promote_near_miss(self, task_id: str):
        """Promote a near-miss to proven program (it achieved perfection)."""
        if task_id in self.near_misses:
            cp = self.near_misses.pop(task_id)
            cp.is_near_miss = False
            cp.best_defect = 0.0
            cp.alpha_prior = 2.0  # Upgrade to proven prior
            h = cp.content_hash()
            if h not in self.programs:
                self.programs[h] = cp
                sig = cp.task_signature
                if sig not in self.sig_to_programs:
                    self.sig_to_programs[sig] = []
                if h not in self.sig_to_programs[sig]:
                    self.sig_to_programs[sig].append(h)

    def update(self, prog_hash: str, success: bool):
        """Update Bayesian posterior for a compiled program."""
        if prog_hash in self.programs:
            if success:
                self.programs[prog_hash].success_count += 1
            else:
                self.programs[prog_hash].failure_count += 1
    
    def recall(self, task_signature: str, 
               max_programs: int = 10) -> List[CompiledProgram]:
        """
        Recall compiled programs relevant to this task context.
        
        Strategy: 
        1. Programs from SAME task signature (highest relevance)
        2. Programs from SIMILAR signatures (partial match)
        3. All programs sorted by posterior (fallback)
        
        Returns programs sorted by posterior mean (best first).
        """
        candidates = []
        seen = set()
        
        # 1. Exact task signature match
        if task_signature in self.sig_to_programs:
            for h in self.sig_to_programs[task_signature]:
                if h in self.programs and h not in seen:
                    candidates.append(self.programs[h])
                    seen.add(h)
        
        # 2. Partial signature match (same shape/transform bins)
        if task_signature:
            sig_parts = set(task_signature.split('|'))
            for sig, prog_hashes in self.sig_to_programs.items():
                if sig == task_signature:
                    continue
                other_parts = set(sig.split('|'))
                # At least 2 bins in common
                if len(sig_parts & other_parts) >= 2:
                    for h in prog_hashes:
                        if h in self.programs and h not in seen:
                            candidates.append(self.programs[h])
                            seen.add(h)
        
        # 3. All remaining programs
        for h, cp in self.programs.items():
            if h not in seen:
                candidates.append(cp)
                seen.add(h)
        
        # Sort by posterior mean (best first)
        candidates.sort(key=lambda cp: -cp.posterior_mean())
        return candidates[:max_programs]
    
    def try_programs(self, task: 'ARCTask',
                     task_signature: str = '') -> Optional[Tuple[CompiledProgram, np.ndarray]]:
        """
        Try compiled programs on a task. Returns (program, test_prediction)
        if one solves all training examples perfectly, else None.
        
        This is the System-1 fast path: O(n_programs) instead of beam search.
        """
        compiled = self.recall(task_signature)
        
        for cp in compiled:
            # Quick check: apply to all training examples
            all_perfect = True
            for ex in task.train_examples:
                inp = ex.input_grid.to_numpy()
                tgt = ex.output_grid.to_numpy()
                try:
                    out = cp.apply(inp)
                    if out.shape != tgt.shape or np.any(out != tgt):
                        all_perfect = False
                        break
                except Exception:
                    all_perfect = False
                    break
            
            if all_perfect:
                # Winner! Apply to test
                return cp, cp.description
        
        return None
    
    @property
    def size(self) -> int:
        return len(self.programs)
    
    def stats(self) -> Dict:
        if not self.programs and not self.near_misses:
            return {'n_programs': 0, 'n_near_misses': 0, 'avg_posterior': 0.0}
        means = [cp.posterior_mean() for cp in self.programs.values()] if self.programs else [0.0]
        return {
            'n_programs': len(self.programs),
            'n_near_misses': len(self.near_misses),
            'avg_posterior': np.mean(means),
            'n_contexts': len(self.sig_to_programs),
        }

    def save_to_json(self, path: str):
        """
        Persist Dream Memory to disk.

        Programs are stored as metadata + description strings.
        The executable closures are NOT serialized; they are
        reconstructed from descriptions on load via _reconstruct_program.
        """
        data = {
            'version': 2,
            'programs': {},
            'near_misses': {},
            'sig_to_programs': self.sig_to_programs,
        }
        for h, cp in self.programs.items():
            data['programs'][h] = {
                'description': cp.description,
                'structural_sig': cp.structural_sig,
                'source_task_id': cp.source_task_id,
                'task_signature': cp.task_signature,
                'success_count': cp.success_count,
                'failure_count': cp.failure_count,
                'alpha_prior': cp.alpha_prior,
                'beta_prior': cp.beta_prior,
            }
        for task_id, cp in self.near_misses.items():
            data['near_misses'][task_id] = {
                'description': cp.description,
                'structural_sig': cp.structural_sig,
                'source_task_id': cp.source_task_id,
                'task_signature': cp.task_signature,
                'best_defect': cp.best_defect,
            }
        with open(path, 'w') as f:
            json.dump(data, f, indent=2)

    @classmethod
    def load_from_json(cls, path: str) -> 'CompiledProgramLibrary':
        """
        Load Dream Memory from disk.

        Programs are reconstructed from their description strings.
        Programs that can't be reconstructed (unknown op formats) are
        skipped with a warning.
        """
        lib = cls()
        try:
            with open(path, 'r') as f:
                data = json.load(f)
        except (FileNotFoundError, json.JSONDecodeError):
            return lib

        loaded = 0
        skipped = 0
        for h, pdata in data.get('programs', {}).items():
            desc = pdata['description']
            program = _reconstruct_program(desc)
            if program is None:
                skipped += 1
                continue
            cp = CompiledProgram(
                program=program,
                description=desc,
                structural_sig=pdata['structural_sig'],
                source_task_id=pdata['source_task_id'],
                task_signature=pdata['task_signature'],
                success_count=pdata.get('success_count', 0),
                failure_count=pdata.get('failure_count', 0),
                alpha_prior=pdata.get('alpha_prior', 2.0),
                beta_prior=pdata.get('beta_prior', 1.0),
            )
            lib.programs[h] = cp
            loaded += 1

        # Load near-misses
        nm_loaded = 0
        for task_id, nmdata in data.get('near_misses', {}).items():
            desc = nmdata['description']
            program = _reconstruct_program(desc)
            if program is None:
                continue
            cp = CompiledProgram(
                program=program,
                description=desc,
                structural_sig=nmdata['structural_sig'],
                source_task_id=nmdata['source_task_id'],
                task_signature=nmdata['task_signature'],
                best_defect=nmdata.get('best_defect', 0.05),
                is_near_miss=True,
                alpha_prior=1.0,
                beta_prior=1.0,
            )
            lib.near_misses[task_id] = cp
            nm_loaded += 1

        lib.sig_to_programs = {
            k: v for k, v in data.get('sig_to_programs', {}).items()
        }
        if loaded > 0 or skipped > 0 or nm_loaded > 0:
            print(f"  [DREAM-LOAD] Loaded {loaded} programs + {nm_loaded} near-misses, skipped {skipped}")
        return lib


# =============================================================================
# 4. RECURSIVE RESIDUAL SOLVER (The Synthesizer)
# =============================================================================

@dataclass
class SearchNode:
    """A node in the program search tree."""
    program: CompositeOp
    output: np.ndarray        # result of applying program to input
    defect: float             # defect(output, target)
    gradient: DiscreteGradient

    def __repr__(self):
        return f"Node(defect={self.defect:.4f}, program={self.program})"


class RecursiveResidualSolver:
    """
    Solves ARC tasks by recursive residual decomposition.

    Algorithm:
      1. Start with input grid
      2. Propose operations guided by gradient(current, target)
      3. Apply best op, compute new residual
      4. Recurse on residual (depth -= 1)
      5. Return the composed program if defect = 0

    Uses beam search to manage combinatorial explosion.
    Programs are verified across ALL training examples before test application.
    """

    def __init__(
        self,
        max_depth: int = 3,
        beam_width: int = 5,
        verbose: bool = False,
        compiled_library: Optional[CompiledProgramLibrary] = None,
        use_sie: bool = True,
        predicate_prior: Optional[Any] = None,
        temperature: float = 0.0,
        cross_task_validator: Optional['CrossTaskPredicateValidator'] = None,
    ):
        self.max_depth = max_depth
        self.beam_width = beam_width
        self.verbose = verbose
        self.library = OperatorLibrary()
        self.compiled_library = compiled_library
        self.use_sie = use_sie
        self.predicate_prior = predicate_prior  # PredicatePrior from arc_sgc_sie
        # SGFE v2.2: Curriculum-aware cross-task validator
        # Caches predictions/targets from near-miss tasks for cross-task predicate validation
        if cross_task_validator is not None:
            self.cross_task_validator = cross_task_validator
        elif HAS_SGFE:
            self.cross_task_validator = CrossTaskPredicateValidator()
        else:
            self.cross_task_validator = None
        
        # Legacy near-miss journal for failure clustering (separate from cross-task validation)
        self.near_miss_journal = NearMissJournal()
        
        # SGC GROUNDING: temperature = 1/β in the IB variational formulation.
        # At T=0, deterministic argmax (hard partition assignment).
        # At T>0, Boltzmann sampling explores alternative partitions on the
        # defect landscape, enabling multi-pass refinement to escape local minima.
        self.temperature = temperature
        
        # SGFE v3.0: Sheaf Atlas - gauge-covariant predicate library
        # Replaces flat SGFEPrimitiveLibrary with gauge-covariant SheafAtlas
        # Theory: Predicates stored in local charts, cross-task transfer via D4 gauge
        self.use_sheaf_atlas = HAS_SHEAF_ATLAS and os.environ.get('SGFE_USE_SHEAF_ATLAS', '1') == '1'
        
        if self.use_sheaf_atlas:
            self._sgfe_library = SheafAtlasLibrary(verbose=self.verbose)
            if self.verbose:
                print("[RESIDUAL] Using SheafAtlas (gauge-covariant library)", flush=True)
        elif HAS_SGFE:
            self._sgfe_library = SGFEPrimitiveLibrary(self.cross_task_validator)
            if self.verbose:
                print("[RESIDUAL] Using SGFEPrimitiveLibrary (flat library)", flush=True)
        else:
            self._sgfe_library = None

    def solve_task(self, task: ARCTask, task_signature: str = '') -> Dict:
        """
        Solve an ARC task.

        Returns dict with: task_id, predictions, method, energy, is_perfect, elapsed_ms
        """
        start = time.time()
        predictions = []
        _tensor_log = []  # Tensor logic instrumentation (always in scope)

        def _cache_cross_task_anchor(
            current_program: Optional['CompositeOp'],
            defect_hint: Optional[float] = None,
            context: str = '',
        ) -> bool:
            """
            Cache a task-local anchor for curriculum cross-task validation.

            Critical for SGFE pass-2: TL can fire on tasks outside the near-miss
            band; those tasks still need a current-task validator entry so
            add_new_primitive() doesn't get rejected as missing_current_task.
            """
            if self.cross_task_validator is None or current_program is None:
                return False

            try:
                j_targets = []
                j_preds = []
                for ex in task.train_examples:
                    inp = ex.input_grid.data.numpy()
                    tgt = ex.output_grid.data.numpy()
                    pred_out = current_program.apply(inp)
                    if pred_out.shape == tgt.shape:
                        j_targets.append(tgt)
                        j_preds.append(pred_out)

                if not j_targets:
                    return False

                pos_count = 0
                neg_count = 0
                recolor_count = 0
                all_wrong_masks = []
                for pred, tgt in zip(j_preds, j_targets):
                    wrong = (pred != tgt)
                    all_wrong_masks.append(wrong)
                    pos_count += int((wrong & (pred == 0) & (tgt != 0)).sum())
                    neg_count += int((wrong & (pred != 0) & (tgt == 0)).sum())
                    recolor_count += int((wrong & (pred != 0) & (tgt != 0)).sum())

                n_wrong = pos_count + neg_count + recolor_count
                pos_frac = pos_count / max(n_wrong, 1)
                neg_frac = neg_count / max(n_wrong, 1)
                recolor_frac = recolor_count / max(n_wrong, 1)
                pure_recolor = 1.0 if (pos_count == 0 and neg_count == 0 and recolor_count > 0) else 0.0

                # Compute topological features (is_connected, is_scattered) on first example with wrong pixels
                is_connected_f = 0.0
                is_scattered_f = 0.0
                for w in all_wrong_masks:
                    if w.any():
                        from scipy.ndimage import label as ndlabel
                        labeled, n_cc = ndlabel(w)
                        is_connected_f = 1.0 if n_cc == 1 else 0.0
                        # Scattered: each wrong pixel is isolated (no adjacent wrong pixel)
                        w_float = w.astype(np.float32)
                        k = np.ones((3, 3), dtype=np.float32); k[1, 1] = 0
                        adj_count = ndimage.convolve(w_float, k, mode='constant', cval=0.0)
                        is_scattered_f = 1.0 if bool(np.all(adj_count[w] == 0)) else 0.0
                        break

                train_defect = float(np.mean([
                    float(np.mean(pred != tgt))
                    for pred, tgt in zip(j_preds, j_targets)
                ])) if j_preds else 1.0

                # Compute structural program signature for cross-task coset matching
                prog_sig = ''
                try:
                    prog_desc = current_program.describe() if hasattr(current_program, 'describe') else str(current_program)
                    prog_sig = _structural_signature(prog_desc)
                except Exception:
                    pass

                self.cross_task_validator.add_near_miss(
                    task_id=task.task_id,
                    predictions=j_preds,
                    targets=j_targets,
                    transformation_signature=(pos_frac, neg_frac, recolor_frac, pure_recolor, is_connected_f, is_scattered_f),
                    defect=float(defect_hint) if defect_hint is not None else train_defect,
                    program_signature=prog_sig,
                )
                return True
            except Exception as _xval_exc:
                if self.verbose:
                    _ctx = f" ({context})" if context else ""
                    print(f"    [XVAL] cache anchor exception{_ctx}: {_xval_exc}", flush=True)
                return False

        # Infer target shape policy from training examples
        same_shape_task = all(
            ex.input_grid.shape == ex.output_grid.shape
            for ex in task.train_examples
        ) if task.train_examples else True
        # For shape-changing tasks, check if output shape is constant
        fixed_out_shape = None
        if not same_shape_task and task.train_examples:
            shapes = [ex.output_grid.shape for ex in task.train_examples]
            if len(set(shapes)) == 1:
                fixed_out_shape = shapes[0]

        # =================================================================
        # SHEAF ATLAS GAUGE-COVARIANT LOOKUP
        # Before synthesis, check if predicates from other tasks can help
        # via D4 gauge transport. This is the key to cross-task learning.
        # =================================================================
        atlas_transferred_ops = []
        if self.use_sheaf_atlas and self._sgfe_library is not None and self._sgfe_library.size > 0:
            try:
                # Prepare grids and initial predictions
                _grids = [ex.input_grid.data.numpy() for ex in task.train_examples]
                _targets = [ex.output_grid.data.numpy() for ex in task.train_examples]
                _predictions = [g.copy() for g in _grids]  # Start with identity
                
                # Compute transformation signature
                _sig = compute_transformation_signature(_predictions, _targets) if HAS_SHEAF_ATLAS else (0.5, 0.25, 0.25, 0.0, 0.5, 0.5)
                
                # Gauge-covariant lookup
                results = self._sgfe_library.gauge_covariant_lookup(
                    task_id=task.task_id,
                    grids=_grids,
                    targets=_targets,
                    predictions=_predictions,
                    transformation_signature=_sig,
                )
                
                if results and self.verbose:
                    print(f"    [ATLAS] Found {len(results)} transferable predicates via gauge transport", flush=True)
                    for name, g, se, di in results[:3]:  # Show top 3
                        print(f"      -> {name} via {g.name} (sheaf_e={se:.3f}, delta={di:.3f})", flush=True)
                
                atlas_transferred_ops = results
            except Exception as e:
                if self.verbose:
                    print(f"    [ATLAS] Lookup failed: {e}", flush=True)

        # SYSTEM-1 FAST PATH: Try compiled programs before beam search
        compiled_hit = False
        program = None
        if self.compiled_library and self.compiled_library.size > 0:
            result = self.compiled_library.try_programs(task, task_signature)
            if result is not None:
                cp, desc = result
                program = cp.program
                compiled_hit = True
                if self.verbose:
                    print(f"    [DREAM-RECALL] {desc} (System-1 hit)")

        # SYSTEM-2 SLOW PATH: Beam search synthesis
        # Warm-start: if we have a near-miss from a previous session, seed
        # the beam with it so the search can extend it by 1-2 more steps.
        # This is gradient descent from a better starting point.
        warm_start = None
        if program is None and self.compiled_library:
            nm = self.compiled_library.recall_near_miss(task.task_id)
            if nm is not None:
                warm_start = nm.program
                if self.verbose:
                    print(f"    [WARM-START] {nm.description} (defect={nm.best_defect:.4f})")
        # SIE FAST PATH: Top-down discovery before beam search
        # SIE only short-circuits if it finds a VERIFIED PERFECT solution.
        # Otherwise, its best candidate becomes a warm-start for beam search.
        sie_candidate = None
        if program is None and self.use_sie:
            sie_candidate = self._sie_synthesize(task)
            if sie_candidate is not None:
                # Verify: is it perfect on ALL training examples?
                sie_perfect = True
                for ex in task.train_examples:
                    inp = ex.input_grid.data.numpy()
                    tgt = ex.output_grid.data.numpy()
                    try:
                        out = sie_candidate.apply(inp)
                        if out.shape != tgt.shape or np.any(out != tgt):
                            sie_perfect = False
                            break
                    except Exception:
                        sie_perfect = False
                        break
                if sie_perfect:
                    program = sie_candidate
                    if self.verbose:
                        print(f"    [SIE] PERFECT: {program.describe()}")
                else:
                    # Use SIE candidate as warm-start for beam search
                    if warm_start is None:
                        warm_start = sie_candidate
                    if self.verbose:
                        print(f"    [SIE] Near-miss -> warm-start: {sie_candidate.describe()}")

        if program is None:
            program = self._synthesize_from_training(task, warm_start=warm_start)

        # =================================================================
        # TEST-TIME REFINEMENT LOOP (Gap 1: defect gradient descent)
        # SGC GROUNDING: Iterative defect minimization in partition space.
        # After initial solve, compute residual between prediction and
        # training output. The residual mask IS a new predicate — it tells
        # us exactly where the current model fails. Re-running synthesis
        # with this augmented vocabulary is gradient descent in theory space.
        # =================================================================
        if program is not None and self.use_sie:
            # Check if program is a near-miss on training (worth refining)
            train_defects = []
            train_residual_masks = []
            for ex in task.train_examples:
                inp = ex.input_grid.data.numpy()
                tgt = ex.output_grid.data.numpy()
                try:
                    pred_out = program.apply(inp)
                    if pred_out.shape == tgt.shape:
                        defect = np.mean(pred_out != tgt)
                        train_defects.append(defect)
                        residual_mask = (pred_out != tgt)
                        train_residual_masks.append(residual_mask)
                    else:
                        train_defects.append(1.0)
                except Exception:
                    train_defects.append(1.0)

            avg_defect = np.mean(train_defects) if train_defects else 1.0

            # Iterative refinement: up to 3 rounds of refine-recompute-refine
            # SGC GROUNDING: Each round is one step of gradient descent on the
            # partition lattice. Multiple rounds compose corrections for multi-
            # type residuals (e.g., fill missing color A, then recolor wrong B).
            _tensor_tried = False  # Tensor logic: at most once per task
            _tensor_log = []      # Tensor logic instrumentation
            for _refine_round in range(3):
                # Recompute defects for current program
                cur_defects = []
                cur_masks = []
                for ex in task.train_examples:
                    inp = ex.input_grid.data.numpy()
                    tgt = ex.output_grid.data.numpy()
                    try:
                        pred_out = program.apply(inp)
                        if pred_out.shape == tgt.shape:
                            cur_defects.append(np.mean(pred_out != tgt))
                            cur_masks.append(pred_out != tgt)
                        else:
                            cur_defects.append(1.0)
                    except Exception:
                        cur_defects.append(1.0)
                cur_avg = np.mean(cur_defects) if cur_defects else 1.0

                if not (0.001 < cur_avg < 0.15) or len(cur_masks) != len(task.train_examples):
                    break

                try:
                    # Compute residual transformation map
                    residual_t_maps = []
                    for ex_idx, ex in enumerate(task.train_examples):
                        inp = ex.input_grid.data.numpy()
                        tgt = ex.output_grid.data.numpy()
                        pred_out = program.apply(inp)
                        res_tmap = np.zeros_like(tgt, dtype=np.int32)
                        wrong = (pred_out != tgt)
                        res_tmap[wrong] = tgt[wrong] + 1
                        residual_t_maps.append(res_tmap)

                    # Compute predicates for each example
                    res_preds_per_example = []
                    for ex_idx, ex in enumerate(task.train_examples):
                        inp = ex.input_grid.data.numpy()
                        preds = _compute_pixel_predicates(inp)
                        res_preds_per_example.append(preds)

                    res_all_types = set()
                    for rtmap in residual_t_maps:
                        res_all_types.update(np.unique(rtmap).tolist())
                    res_all_types.discard(0)

                    # For each residual type, find best predicate
                    # SGC GROUNDING: For sparse residuals, NMI fails because
                    # H(T) ≈ 0. Use precision/recall: P(wrong|pred), P(pred|wrong).
                    refinement_ops = []
                    for rt in sorted(res_all_types):
                        out_color = rt - 1
                        rt_masks = [rtmap == rt for rtmap in residual_t_maps]

                        # KEY FIX: Only use examples that HAVE this residual type.
                        # Color-specific predicates (cross_8) only exist in examples
                        # containing that color. If example 1 has d=0 for this type,
                        # don't require its predicates to match.
                        active_indices = [i for i, m in enumerate(rt_masks)
                                          if m.sum() > 0]
                        if not active_indices:
                            continue

                        rt_pool = np.concatenate([rt_masks[i].flatten().astype(np.int32)
                                                   for i in active_indices])
                        n_wrong = rt_pool.sum()
                        if n_wrong < 2:
                            continue

                        # Compute common names only across ACTIVE examples
                        active_common = None
                        for i in active_indices:
                            names = set(res_preds_per_example[i].keys())
                            active_common = names if active_common is None else active_common & names
                        if not active_common:
                            continue

                        best_rp = None
                        best_rp_f1 = 0.0
                        generalizable = [pn for pn in sorted(active_common)
                                         if not pn.startswith('_') and
                                            not pn.startswith('ib_cluster')]

                        # Build pooled masks for ALL generalizable predicates
                        # (needed for exhaustive conjunction search below)
                        rt_target = (rt_pool == 1)
                        all_pred_pools = {}
                        for pn in generalizable:
                            pp_parts = []
                            ok = True
                            for eidx in active_indices:
                                preds = res_preds_per_example[eidx]
                                pm = preds[pn]
                                if pm.shape != rt_masks[eidx].shape:
                                    ok = False
                                    break
                                pp_parts.append(pm.flatten().astype(bool))
                            if ok:
                                all_pred_pools[pn] = np.concatenate(pp_parts)

                        # Score single predicates
                        best_single_name = None
                        best_single_f1 = 0.0
                        for pn, pp in all_pred_pools.items():
                            tp = int((pp & rt_target).sum())
                            fp = int((pp & ~rt_target).sum())
                            fn = int((~pp & rt_target).sum())
                            precision = tp / max(tp + fp, 1)
                            recall = tp / max(tp + fn, 1)
                            if precision >= 0.5 and recall >= 0.15:
                                f1 = 2 * precision * recall / max(precision + recall, 1e-10)
                                if f1 > best_single_f1:
                                    best_single_f1 = f1
                                    best_single_name = pn
                        best_rp = best_single_name
                        best_rp_f1 = best_single_f1

                        # Exhaustive pairwise conjunction search: ALL pairs
                        # SGC GROUNDING: Conjunction = lattice refinement.
                        # Exhaustive search guarantees the optimal 2-conjunction,
                        # unlike top-5×top-8 CEGAR which misses most of the lattice.
                        # Cost: O(n²) where n ≈ 60 predicates → ~5000 evals, <5ms.
                        best_conj_name = None
                        best_conj_f1 = 0.0
                        if best_rp_f1 < 0.95 and len(all_pred_pools) >= 2:
                            pred_names = sorted(all_pred_pools.keys())
                            n_preds = len(pred_names)
                            for i in range(n_preds):
                                pp_a = all_pred_pools[pred_names[i]]
                                for j in range(i + 1, n_preds):
                                    pp_b = all_pred_pools[pred_names[j]]
                                    for conj_pp, conj_name in [
                                        (pp_a & pp_b, f"{pred_names[i]}&{pred_names[j]}"),
                                        (pp_a & ~pp_b, f"{pred_names[i]}&!{pred_names[j]}"),
                                        (~pp_a & pp_b, f"!{pred_names[i]}&{pred_names[j]}"),
                                    ]:
                                        cs = int(conj_pp.sum())
                                        if cs < 1 or cs > len(rt_pool) * 0.5:
                                            continue
                                        tp = int((conj_pp & rt_target).sum())
                                        if tp == 0:
                                            continue
                                        fp = cs - tp
                                        fn = n_wrong - tp
                                        prec = tp / max(tp + fp, 1)
                                        rec = tp / max(tp + fn, 1)
                                        if prec < 0.5 or rec < 0.1:
                                            continue
                                        f1 = 2 * prec * rec / max(prec + rec, 1e-10)
                                        if f1 > max(best_rp_f1 + 0.05, best_conj_f1):
                                            best_conj_f1 = f1
                                            best_conj_name = conj_name

                        # Per-example generalization test for conjunctions
                        # SGC GROUNDING: A conjunction that improves pooled F1 but
                        # loses true positives on individual examples is a spurious
                        # correlation from pooling, not a genuine predicate.
                        if best_conj_name and best_single_name:
                            conj_generalizes = True
                            for eidx in active_indices:
                                preds = res_preds_per_example[eidx]
                                rt_mask = rt_masks[eidx]
                                n_wrong_ex = int(rt_mask.sum())
                                if n_wrong_ex == 0:
                                    continue
                                # Compute single predicate TP on this example
                                if best_single_name in preds:
                                    single_tp = int((preds[best_single_name] & rt_mask).sum())
                                else:
                                    single_tp = 0
                                # Compute conjunction TP on this example
                                conj_parts = best_conj_name.split("&")
                                conj_mask = np.ones(rt_mask.shape, dtype=bool)
                                for part in conj_parts:
                                    if part.startswith("!"):
                                        neg = part[1:]
                                        if neg in preds:
                                            conj_mask &= ~preds[neg]
                                        else:
                                            conj_mask[:] = False
                                    elif part in preds:
                                        conj_mask &= preds[part]
                                    else:
                                        conj_mask[:] = False
                                conj_tp = int((conj_mask & rt_mask).sum())
                                # Reject if conjunction loses >30% of true positives
                                if single_tp > 0 and conj_tp < single_tp * 0.7:
                                    conj_generalizes = False
                                    break
                            if conj_generalizes:
                                best_rp = best_conj_name
                                best_rp_f1 = best_conj_f1
                        elif best_conj_name and not best_single_name:
                            best_rp = best_conj_name
                            best_rp_f1 = best_conj_f1

                        # DSL beam search: open-ended predicate synthesis
                        # Runs alongside closed-vocabulary search; uses whichever
                        # finds the better predicate. The DSL can discover
                        # compositions that no hardcoded recipe anticipated.
                        if best_rp_f1 < 0.95:
                            try:
                                dsl_grids = [task.train_examples[i].input_grid.data.numpy()
                                             for i in active_indices]
                                dsl_targets = [rt_masks[i] for i in active_indices]
                                dsl_expr = _synthesize_predicate_beam(
                                    dsl_grids, dsl_targets,
                                    max_depth=2, beam_width=15, min_f1=0.25)
                                if dsl_expr is not None:
                                    # Score DSL predicate on pooled data for comparison
                                    dsl_parts = []
                                    for g in dsl_grids:
                                        dsl_parts.append(
                                            dsl_expr.evaluate(g).flatten().astype(bool))
                                    dsl_pool = np.concatenate(dsl_parts)
                                    dsl_tp = int((dsl_pool & rt_target).sum())
                                    dsl_fp = int(dsl_pool.sum()) - dsl_tp
                                    dsl_fn = n_wrong - dsl_tp
                                    dsl_prec = dsl_tp / max(dsl_tp + dsl_fp, 1)
                                    dsl_rec = dsl_tp / max(dsl_tp + dsl_fn, 1)
                                    dsl_f1 = 2 * dsl_prec * dsl_rec / max(dsl_prec + dsl_rec, 1e-10)
                                    if dsl_f1 > best_rp_f1:
                                        best_rp = dsl_expr  # PredicateExpr: program, not mask
                                        best_rp_f1 = dsl_f1
                            except Exception:
                                pass  # DSL synthesis is additive; never block closed-vocab results

                        # DSL beam search path: build ops from best closed-vocab predicate
                        if best_rp and best_rp_f1 >= 0.25:
                            ref_op = _make_predicated_fill(best_rp, out_color)
                            if ref_op:
                                refinement_ops.append(ref_op)
                            all_src = set()
                            for ex in task.train_examples:
                                inp = ex.input_grid.data.numpy()
                                try:
                                    pred_out = program.apply(inp)
                                    tgt = ex.output_grid.data.numpy()
                                    wrong_type = (pred_out != tgt) & (tgt == out_color)
                                    if wrong_type.any():
                                        for sc in np.unique(pred_out[wrong_type]):
                                            sc = int(sc)
                                            if sc != out_color and sc != 0:
                                                all_src.add(sc)
                                except Exception:
                                    pass
                            for src_c in sorted(all_src):
                                ref_op2 = _make_predicated_recolor(
                                    best_rp, src_c, out_color)
                                if ref_op2:
                                    refinement_ops.append(ref_op2)

                    # SGFE Tensor Logic: differentiable residual predicate discovery
                    # (Domingos 2024, arXiv:2510.12269)
                    #
                    # BROADENED TRIGGER (spec §3 "Trigger"):
                    #   Fire whenever functional_defect > 0.03 OR after every
                    #   DSL step on near-miss (not just when DSL found nothing).
                    #   Theory: validity horizon + information gradient law.
                    _tl_should_fire = (
                        HAS_TENSOR_LOGIC
                        and not _tensor_tried
                        and (not refinement_ops or cur_avg > 0.03)
                    )
                    if _tl_should_fire:
                        _tensor_tried = True
                        _tl_t0 = time.time()
                        try:
                            tl_all_active = [i for i, m in enumerate(cur_masks)
                                             if m.sum() > 0]
                            if tl_all_active:
                                _xval_cached = _cache_cross_task_anchor(
                                    program,
                                    defect_hint=cur_avg,
                                    context='tl_trigger',
                                )
                                tl_seed = hash(task.task_id) & 0x7FFFFFFF
                                
                                # LEM Architecture: Try morphological predicates FIRST
                                # Theory: Morphological ops have sheaf_energy ≈ 0.0 by construction
                                morph_accepted = []
                                if HAS_MORPH_ALGEBRA:
                                    if self.verbose:
                                        print(f"    [LEM] Trying morphological predicates...", flush=True)
                                    morph_accepted = _morph_residual_refine(
                                        task, program, tl_all_active,
                                        verbose=self.verbose,
                                        sgfe_library=self._sgfe_library)
                                    if self.verbose:
                                        print(f"    [LEM] Morphological predicates found: {len(morph_accepted)}", flush=True)
                                
                                # SGFE v2.0: pass library for renormalization inside function
                                tl_accepted = _tensor_residual_refine(
                                    task, program, tl_all_active,
                                    seed=tl_seed, verbose=self.verbose,
                                    sgfe_library=self._sgfe_library)
                                
                                # Combine morphological + tensor logic results
                                all_accepted = morph_accepted + tl_accepted
                                
                                _tl_dt = time.time() - _tl_t0
                                _tensor_log.append({
                                    'triggered': True,
                                    'round': _refine_round,
                                    'n_active': len(tl_all_active),
                                    'n_accepted': len(all_accepted),
                                    'n_morph': len(morph_accepted),
                                    'n_tensor': len(tl_accepted),
                                    'elapsed_s': round(_tl_dt, 2),
                                    'ops': [lg for _, lg in all_accepted],
                                    'library_size': self._sgfe_library.size if self._sgfe_library else 0,
                                    'xval_anchor_cached': _xval_cached,
                                })
                                for op, log in all_accepted:
                                    refinement_ops.append(op)
                        except Exception as _tl_exc:
                            _tl_dt = time.time() - _tl_t0
                            _tensor_log.append({
                                'triggered': True, 'error': True,
                                'elapsed_s': round(_tl_dt, 2),
                                'exception': str(_tl_exc),
                            })
                            if self.verbose:
                                print(f"    [TENSOR] EXCEPTION: {_tl_exc}", flush=True)

                    if not refinement_ops:
                        break

                    # Compose and verify
                    from copy import deepcopy
                    refined = deepcopy(program)
                    for rop in refinement_ops:
                        refined = CompositeOp([refined, rop])

                    ref_defects = []
                    for ex in task.train_examples:
                        inp = ex.input_grid.data.numpy()
                        tgt = ex.output_grid.data.numpy()
                        try:
                            rout = refined.apply(inp)
                            if rout.shape == tgt.shape:
                                ref_defects.append(np.mean(rout != tgt))
                            else:
                                ref_defects.append(1.0)
                        except Exception:
                            ref_defects.append(1.0)

                    ref_avg = np.mean(ref_defects) if ref_defects else 1.0
                    if ref_avg < cur_avg - 0.001:
                        program = refined
                        # Continue to next round
                    else:
                        break  # No improvement, stop

                except Exception:
                    break

        for test_idx, test_ex in enumerate(task.test_examples):
            test_input = test_ex.input_grid.to_numpy()

            if program is not None:
                pred = program.apply(test_input)
                # Smart shape adjustment
                if same_shape_task:
                    # Same-shape task: output should match input shape
                    if pred.shape != test_input.shape:
                        pred = self._adjust_shape(pred, test_input.shape)
                elif fixed_out_shape is not None:
                    # Fixed output shape across training
                    if pred.shape != fixed_out_shape:
                        pred = self._adjust_shape(pred, fixed_out_shape)
                # else: variable output shapes, trust the program's output
                predictions.append(pred)
            else:
                predictions.append(test_input.copy())

        # Evaluate
        avg_energy = 0.0
        is_perfect = True
        for i, test_ex in enumerate(task.test_examples):
            target = test_ex.output_grid.to_numpy()
            if i < len(predictions):
                pred = predictions[i]
                pred_grid = ARCGrid(torch.tensor(pred, dtype=torch.long))
                tgt_grid = ARCGrid(torch.tensor(target, dtype=torch.long))
                e = compute_defect_energy(pred_grid, tgt_grid)
                avg_energy += e
                if e > 0.001:
                    is_perfect = False
            else:
                avg_energy += 1.0
                is_perfect = False

        avg_energy /= max(len(task.test_examples), 1)
        elapsed = (time.time() - start) * 1000

        method = program.describe() if program else "failed"

        # Near-miss journal: analyze residual for the learning loop
        residual_analysis = None
        if program is not None and not is_perfect and avg_energy < 0.15:
            try:
                j_grids = []
                j_targets = []
                j_preds = []
                for ex in task.train_examples:
                    inp = ex.input_grid.data.numpy()
                    tgt = ex.output_grid.data.numpy()
                    pred_out = program.apply(inp)
                    if pred_out.shape == tgt.shape:
                        j_grids.append(inp)
                        j_targets.append(tgt)
                        j_preds.append(pred_out)
                if j_grids:
                    residual_analysis = _analyze_residual(
                        task_id=task.task_id,
                        grids=j_grids,
                        targets=j_targets,
                        predictions=j_preds,
                        program_desc=method,
                    )
                    if residual_analysis and self.near_miss_journal is not None:
                        self.near_miss_journal.record(residual_analysis)
                    
                    # SGFE v2.2: Populate cross-task validator for curriculum-aware acceptance
                    # This enables predicates discovered on later tasks to be tested against
                    # earlier near-misses, implementing cross-task generalization.
                    if self.cross_task_validator is not None:
                        _cache_cross_task_anchor(
                            program,
                            defect_hint=avg_energy,
                            context='near_miss',
                        )
            except Exception:
                pass

        return {
            'task_id': task.task_id,
            'predictions': predictions,
            'method': method,
            'avg_train_energy': avg_energy,
            'is_perfect': is_perfect,
            'elapsed_ms': elapsed,
            'depth': program.depth if program else 0,
            'program': program,  # Expose for Dream Consolidation
            'residual_analysis': residual_analysis,  # For learning loop
            'tensor_log': _tensor_log,
        }

    def _ib_discover_predicates(self, inp: np.ndarray, t_map: np.ndarray,
                                input_preds: Optional[Dict[str, np.ndarray]] = None
                                ) -> Dict[str, np.ndarray]:
        """
        Transformation-guided predicate discovery via IB projection.
        
        SGC GROUNDING (Koch-Janusz & Ringel 2018, sg.md):
          IB = optimal RG = minimum defect coarse-graining.
          This IS the functor F: Observations → Partitions.
          
          The extropic act: inventing new predicates (structure) from
          transformation residuals (disorder). Each discovered predicate
          reduces H(T|P), creating order from the raw pixel grid.
        
        Algorithm (Two-Step IB Projection):
          1. IDEAL PARTITION: Group pixels by transformation type — what
             the pixel BECOMES defines the partition we want to approximate.
          2. PROJECTION: For each transform group, find the best input-side
             predicate (or conjunction) that separates it from other pixels.
          3. Return named conjunctions that ARE recomputable on test inputs.
        
        Unlike the old approach (opaque ib_cluster_X masks), the returned
        predicates are NAMED compositions of vocabulary predicates (e.g.,
        "adj_to_5&!on_border") and can be dynamically recomputed.
        
        Returns dict of predicate_name -> boolean mask.
        """
        H, W = inp.shape
        n_pixels = H * W
        
        if n_pixels > 900:
            return {}
        
        # Use precomputed input predicates or compute them
        if input_preds is None:
            input_preds = _compute_pixel_predicates(inp)
        
        # --- STEP 1: Build ideal partition by transformation type ---
        t_flat = t_map.flatten()
        transform_groups = {}  # t_type -> list of pixel indices
        for px in range(n_pixels):
            t = int(t_flat[px])
            if t == 0:  # unchanged pixel — skip
                continue
            transform_groups.setdefault(t, []).append(px)
        
        if not transform_groups:
            return {}
        
        # --- STEP 2: For each transform group, find best input-side predicate ---
        discovered = {}
        
        for t_type, px_indices in transform_groups.items():
            n_group = len(px_indices)
            if n_group < 2 or n_group >= n_pixels * 0.8:
                continue
            
            # Build target mask for this transformation group
            target = np.zeros((H, W), dtype=bool)
            for px in px_indices:
                r, c = divmod(px, W)
                target[r, c] = True
            target_count = int(target.sum())
            
            # Score all single input-side predicates against this target
            scored = []
            for pn, pm in input_preds.items():
                # Skip predicates that are themselves IB-discovered
                if pn.startswith('ib_'):
                    continue
                tp = int((pm & target).sum())
                fp = int((pm & ~target).sum())
                fn = target_count - tp
                prec = tp / max(tp + fp, 1)
                rec = tp / max(tp + fn, 1)
                if prec >= 0.3 and rec >= 0.1:
                    f1 = 2 * prec * rec / max(prec + rec, 1e-10)
                    scored.append((pn, pm, f1, prec, rec))
            
            if not scored:
                continue
            
            scored.sort(key=lambda x: -x[2])
            best_name = scored[0][0]
            best_mask = scored[0][1]
            best_f1 = scored[0][2]
            
            # Try conjunction refinement: top-5 base × top-8 partners
            if best_f1 < 0.95 and len(scored) >= 2:
                top_base = scored[:5]
                top_partners = scored[:8]
                for pn_a, pm_a, _, _, _ in top_base:
                    for pn_b, pm_b, _, _, _ in top_partners:
                        if pn_a == pn_b:
                            continue
                        # Try P_a & P_b and P_a & !P_b
                        for conj_mask, conj_name in [
                            (pm_a & pm_b, f"{pn_a}&{pn_b}"),
                            (pm_a & ~pm_b, f"{pn_a}&!{pn_b}"),
                        ]:
                            cs = int(conj_mask.sum())
                            if cs < 2 or cs >= n_pixels:
                                continue
                            tp = int((conj_mask & target).sum())
                            fp = cs - tp
                            fn = target_count - tp
                            prec = tp / max(tp + fp, 1)
                            rec = tp / max(tp + fn, 1)
                            if prec < 0.5 or rec < 0.15:
                                continue
                            f1 = 2 * prec * rec / max(prec + rec, 1e-10)
                            if f1 > best_f1 + 0.02:  # require clear improvement
                                best_f1 = f1
                                best_name = conj_name
                                best_mask = conj_mask
            
            # Only keep predicates with meaningful discriminative power
            if best_f1 >= 0.4:
                discovered[best_name] = best_mask
        
        return discovered

    def _sie_synthesize(self, task: ARCTask) -> Optional[CompositeOp]:
        """
        SIE top-down synthesis: use information-theoretic defect scoring
        to discover predicated operations directly from transformation structure.

        SGC GROUNDING: This is the computational instantiation of the
        IB = RG equivalence (Gordon et al. 2021). The transformation map T
        is the observable; the predicate partition minimizes H(T|P)/H(T).

        Strategy:
          1. Compute transformation type map T per training example
          2. For each non-trivial transformation type (recolored to color c):
             a. Build the mask of pixels with T = c+1
             b. Score all predicates by NMI against this mask
             c. Create predicated operation: fill/recolor WHERE best_predicate
          3. Compose operations, verify across ALL training examples
        """
        try:
            from arc_sgc_sie import (
                compute_transformation_map, compute_nmi_defect,
                greedy_submodular_select, ScoredPredicateNMI,
                conjunction_refine_for_type, mdl_score,
            )
        except ImportError:
            return None

        train_examples = task.train_examples
        if not train_examples:
            return None

        # Only handle same-shape tasks for now
        if not all(ex.input_grid.shape == ex.output_grid.shape for ex in train_examples):
            return None

        # Step 1: Compute transformation maps
        t_maps = []
        for ex in train_examples:
            inp = ex.input_grid.data.numpy()
            out = ex.output_grid.data.numpy()
            t_maps.append(compute_transformation_map(inp, out))

        # Step 2: Identify distinct transformation types across all examples
        # T=0 means unchanged; T=c+1 means recolored to color c
        all_types = set()
        for tmap in t_maps:
            all_types.update(np.unique(tmap).tolist())
        all_types.discard(0)  # Remove "unchanged"

        if not all_types:
            return None  # No changes detected

        # Compute predicates ONCE for all types (avoid redundant computation)
        preds_per_example = []
        for ex in train_examples:
            inp = ex.input_grid.data.numpy()
            preds_per_example.append(_compute_pixel_predicates(inp))

        # IB PARTITION DISCOVERY: discover task-specific predicates
        # SGC GROUNDING (Koch-Janusz & Ringel 2018): IB = optimal RG.
        # The agglomerative IB discovers partitions directly from the
        # joint distribution of pixel features and transformation types,
        # capturing patterns NOT in the fixed predicate vocabulary.
        ib_pred_count = 0
        for ex_idx, ex in enumerate(train_examples):
            inp = ex.input_grid.data.numpy()
            try:
                ib_preds = self._ib_discover_predicates(
                    inp, t_maps[ex_idx], input_preds=preds_per_example[ex_idx])
                if ib_preds:
                    preds_per_example[ex_idx].update(ib_preds)
                    ib_pred_count += len(ib_preds)
            except Exception:
                pass
        if ib_pred_count > 0 and self.verbose:
            print(f"    [IB] Discovered {ib_pred_count} predicates via "
                  f"Information Bottleneck", flush=True)

        # Get common predicate names across all examples
        common_names = None
        for preds in preds_per_example:
            names = set(preds.keys())
            common_names = names if common_names is None else common_names & names
        if not common_names:
            return None

        # Step 3: For each transformation type, find the best predicate
        candidate_ops = []
        for t_type in sorted(all_types):
            output_color = t_type - 1  # T = output_color + 1

            # Build per-example masks for this transformation type
            type_masks = []
            for tmap in t_maps:
                type_masks.append(tmap == t_type)

            # --- POOLED NMI: concatenate pixels across examples ---
            # SGC GROUNDING: Treats all examples as samples from the same
            # joint distribution P(predicate, transformation). More statistical
            # power than per-example averaging, especially on small grids.
            type_pool = np.concatenate([m.flatten().astype(np.int32)
                                        for m in type_masks])

            # Use predicate prior to prioritize evaluation order
            if self.predicate_prior is not None:
                eval_order = self.predicate_prior.rank_predicates(
                    common_names, top_k=0)
            else:
                eval_order = sorted(common_names)

            # Score ALL predicates by pooled NMI
            pred_nmi_scores = {}
            for pred_name in eval_order:
                valid = True
                pred_pool_parts = []
                for ex_idx, preds in enumerate(preds_per_example):
                    pred_mask = preds[pred_name]
                    if pred_mask.shape != type_masks[ex_idx].shape:
                        valid = False
                        break
                    pred_pool_parts.append(pred_mask.flatten().astype(bool))
                if not valid:
                    continue
                pred_pool = np.concatenate(pred_pool_parts)

                # Pooled NMI computation
                n = len(type_pool)
                H_T = 0.0
                t_counts = np.bincount(type_pool, minlength=2)
                t_probs = t_counts / n
                t_probs = t_probs[t_probs > 0]
                H_T = -np.sum(t_probs * np.log2(t_probs))
                if H_T < 1e-12:
                    pred_nmi_scores[pred_name] = 1.0
                    continue
                H_T_given_P = 0.0
                for group_mask in [pred_pool, ~pred_pool]:
                    n_g = group_mask.sum()
                    if n_g == 0:
                        continue
                    g_t = type_pool[group_mask]
                    g_counts = np.bincount(g_t, minlength=2)
                    g_probs = g_counts / n_g
                    g_probs = g_probs[g_probs > 0]
                    H_T_given_P += (n_g / n) * (-np.sum(g_probs * np.log2(g_probs)))
                nmi = 1.0 - float(np.clip(H_T_given_P / H_T, 0.0, 1.0))
                pred_nmi_scores[pred_name] = nmi

            if not pred_nmi_scores:
                continue

            # --- MDL-weighted ranking: NMI - λ·complexity ---
            # SGC GROUNDING: MDL = IB with Occam regularizer.
            # Atomic predicates preferred over conjunctions at equal NMI.
            vocab_sz = len(common_names)
            
            # Gumbel-max trick for stochastic search (temperature > 0)
            # SGC GROUNDING: Boltzmann sampling on the partition lattice.
            # At T=0, deterministic argmax. At T>0, explores alternative
            # local minima of the defect function.
            T = getattr(self, 'temperature', 0.0)
            if T > 0:
                gumbel_noise = {name: -np.log(-np.log(np.random.uniform(1e-10, 1.0)))
                                for name in pred_nmi_scores}
                ranked = sorted(pred_nmi_scores.items(),
                              key=lambda kv: -(mdl_score(kv[1], kv[0],
                                                          vocab_size=vocab_sz)
                                                + T * gumbel_noise[kv[0]]))
            else:
                ranked = sorted(pred_nmi_scores.items(),
                              key=lambda kv: -mdl_score(kv[1], kv[0],
                                                         vocab_size=vocab_sz))
            best_pred_name = ranked[0][0]
            best_nmi = ranked[0][1]

            if best_nmi < 0.3:
                continue

            # --- TOP-K EXHAUSTIVE CONJUNCTION SEARCH ---
            # Instead of only refining the single best predicate, search all
            # pairwise conjunctions (P∧Q and P∧¬Q) from the top-k atomics.
            # SGC GROUNDING: Exploits submodularity guarantee — greedy over
            # top-k conjunctions is within (1-1/e) of optimal partition.
            TOP_K = 8
            top_k_names = [name for name, _ in ranked[:TOP_K]
                           if pred_nmi_scores[name] >= 0.2]

            if best_nmi < 0.995 and len(top_k_names) >= 2:
                best_conj_name = best_pred_name
                best_conj_nmi = best_nmi
                best_conj_mdl = mdl_score(best_nmi, best_pred_name,
                                          vocab_size=vocab_sz)

                for i, p_name in enumerate(top_k_names):
                    for q_name in top_k_names[i+1:]:
                        # Try P∧Q
                        for conj_name, negate_q in [(f"{p_name}&{q_name}", False),
                                                     (f"{p_name}&!{q_name}", True)]:
                            conj_pool_parts = []
                            valid = True
                            for ex_idx, preds in enumerate(preds_per_example):
                                if p_name not in preds or q_name not in preds:
                                    valid = False
                                    break
                                p_m = preds[p_name]
                                q_m = ~preds[q_name] if negate_q else preds[q_name]
                                conj_pool_parts.append(
                                    (p_m & q_m).flatten().astype(bool))
                            if not valid:
                                continue
                            conj_pool = np.concatenate(conj_pool_parts)
                            if conj_pool.sum() == 0 or conj_pool.all():
                                continue

                            # Pooled NMI for conjunction
                            n = len(type_pool)
                            H_T_c = 0.0
                            for gm in [conj_pool, ~conj_pool]:
                                ng = gm.sum()
                                if ng == 0:
                                    continue
                                gt = type_pool[gm]
                                gc = np.bincount(gt, minlength=2)
                                gp = gc / ng
                                gp = gp[gp > 0]
                                H_T_c += (ng / n) * (-np.sum(gp * np.log2(gp)))
                            conj_nmi = 1.0 - float(np.clip(H_T_c / H_T, 0.0, 1.0))
                            conj_mdl = mdl_score(conj_nmi, conj_name,
                                                  vocab_size=vocab_sz)

                            if conj_mdl > best_conj_mdl:
                                best_conj_mdl = conj_mdl
                                best_conj_name = conj_name
                                best_conj_nmi = conj_nmi

                if best_conj_name != best_pred_name:
                    if self.verbose:
                        print(f"    [SIE-TOPK] {best_pred_name} -> {best_conj_name} "
                              f"(NMI {best_nmi:.4f} -> {best_conj_nmi:.4f})")
                    best_pred_name = best_conj_name
                    best_nmi = best_conj_nmi

            # --- DEEP CONJUNCTION FALLBACK: best predicate vs ALL others ---
            # Top-k search is broad but shallow (only top-8). This fallback
            # searches the best predicate against ALL predicates, catching
            # cases like near8_2&!exactly1_adj_2 where the partner isn't in top-8.
            if best_nmi < 0.995:
                try:
                    refined_name, refined_nmi = conjunction_refine_for_type(
                        best_pred_name, best_nmi,
                        preds_per_example, type_masks, common_names
                    )
                    if refined_nmi > best_nmi + 0.005:
                        if self.verbose:
                            print(f"    [SIE-DEEP] {best_pred_name} -> {refined_name} "
                                  f"(NMI {best_nmi:.4f} -> {refined_nmi:.4f})")
                        best_pred_name = refined_name
                        best_nmi = refined_nmi
                except Exception:
                    pass

            # Update predicate prior with results from this type
            if self.predicate_prior is not None:
                from arc_sgc_sie import ScoredPredicateNMI as _SP
                self.predicate_prior.update([
                    _SP(name=best_pred_name, mask=np.zeros(1),
                        nmi_score=best_nmi, defect=1.0 - best_nmi)
                ])

            # Determine operation type based on what changes
            # Check if it's a fill (bg -> color) or recolor (color_a -> color_b)
            # by examining what input colors the affected pixels have
            input_colors_of_type = set()
            for ex_idx, ex in enumerate(train_examples):
                inp = ex.input_grid.data.numpy()
                mask = type_masks[ex_idx]
                if mask.any():
                    input_colors_of_type.update(inp[mask].tolist())

            if input_colors_of_type == {BG}:
                # All changed pixels were background -> this is a FILL
                op = _make_predicated_fill(best_pred_name, output_color)
            elif len(input_colors_of_type) == 1:
                # All changed pixels were one color -> this is a RECOLOR
                source_color = input_colors_of_type.pop()
                op = _make_predicated_recolor(best_pred_name, source_color, output_color)
            else:
                # Multiple input colors -> use fill (broader)
                op = _make_predicated_fill(best_pred_name, output_color)

            candidate_ops.append((op, best_nmi))

            if self.verbose:
                print(f"    [SIE-OP] {op.name} (NMI={best_nmi:.4f})")

        if not candidate_ops:
            return None

        # Step 4: Compose operations in order of NMI (best first)
        candidate_ops.sort(key=lambda x: -x[1])
        steps = [op for op, _ in candidate_ops]

        # Try single-op programs first, then multi-op
        for n_steps in range(1, min(len(steps) + 1, 4)):
            program = CompositeOp(steps[:n_steps])

            # Verify on ALL training examples
            all_match = True
            for ex in train_examples:
                inp = ex.input_grid.data.numpy()
                tgt = ex.output_grid.data.numpy()
                try:
                    out = program.apply(inp)
                except Exception:
                    all_match = False
                    break
                if out.shape != tgt.shape:
                    all_match = False
                    break
                if np.any(out != tgt):
                    all_match = False
                    break

            if all_match:
                return program

        # If no exact match, return best single-op if it's close
        if steps:
            best_single = CompositeOp([steps[0]])
            total_defect = 0.0
            for ex in train_examples:
                inp = ex.input_grid.data.numpy()
                tgt = ex.output_grid.data.numpy()
                try:
                    out = best_single.apply(inp)
                    if out.shape == tgt.shape:
                        total_defect += np.mean(out != tgt)
                    else:
                        total_defect += 1.0
                except Exception:
                    total_defect += 1.0
            avg_defect = total_defect / len(train_examples)
            if avg_defect < 0.3:
                return best_single

        return None

    def _synthesize_from_training(self, task: ARCTask,
                                    warm_start: Optional[CompositeOp] = None) -> Optional[CompositeOp]:
        """
        Find a program that works on ALL training examples.
        Uses first example for synthesis, rest for verification.
        
        If warm_start is provided (a near-miss program from a previous session),
        it is injected as an additional seed in the beam search, allowing the
        search to extend it by 1-2 more steps rather than starting from scratch.
        """
        if not task.train_examples:
            return None

        # Try synthesis on each training example, verify on all
        best_program = None
        best_train_defect = float('inf')

        for synth_idx in range(min(len(task.train_examples), 2)):
            ex = task.train_examples[synth_idx]
            inp = ex.input_grid.to_numpy()
            tgt = ex.output_grid.to_numpy()

            programs = self._beam_search(inp, tgt, task, warm_start=warm_start)

            for prog in programs:
                # Verify on ALL training examples
                total_defect = 0.0
                all_match = True
                for verify_ex in task.train_examples:
                    v_inp = verify_ex.input_grid.to_numpy()
                    v_tgt = verify_ex.output_grid.to_numpy()
                    try:
                        v_out = prog.apply(v_inp)
                    except Exception:
                        all_match = False
                        total_defect += 1.0
                        continue
                    if v_out.shape != v_tgt.shape:
                        v_out = self._adjust_shape(v_out, v_tgt.shape)
                    d = np.sum(v_out != v_tgt) / max(v_tgt.size, 1)
                    total_defect += d
                    if d > 0.001:
                        all_match = False

                avg_defect = total_defect / len(task.train_examples)

                if all_match:
                    if self.verbose:
                        print(f"    [SYNTH] Verified program: {prog.describe()}")
                    return prog

                if avg_defect < best_train_defect:
                    best_train_defect = avg_defect
                    best_program = prog

        # Return best even if not perfect (partial credit)
        if best_program and best_train_defect < 0.5:
            if self.verbose:
                print(f"    [SYNTH] Best partial: {best_program.describe()} "
                      f"(avg_defect={best_train_defect:.4f})")
            return best_program

        return None

    def _beam_search(
        self,
        input_grid: np.ndarray,
        target_grid: np.ndarray,
        task: ARCTask,
        warm_start: Optional[CompositeOp] = None,
    ) -> List[CompositeOp]:
        """
        Beam search over program space.

        Returns list of programs sorted by defect (best first).
        If warm_start is provided, seeds the beam with that program
        in addition to identity, enabling refinement of near-misses.
        """
        # Initialize beam with empty program
        initial_gradient = DiscreteGradient.compute(input_grid, target_grid)
        if initial_gradient.defect < 0.001:
            return [CompositeOp()]  # Already perfect (identity)

        beam: List[SearchNode] = [SearchNode(
            program=CompositeOp(),
            output=input_grid.copy(),
            defect=initial_gradient.defect,
            gradient=initial_gradient,
        )]

        # Warm-start: inject near-miss program as additional beam seed
        if warm_start is not None:
            try:
                ws_output = warm_start.apply(input_grid)
                if ws_output.shape != target_grid.shape:
                    ws_output = self._adjust_shape(ws_output, target_grid.shape)
                ws_gradient = DiscreteGradient.compute(ws_output, target_grid)
                if ws_gradient.defect < initial_gradient.defect:
                    beam.append(SearchNode(
                        program=warm_start,
                        output=ws_output,
                        defect=ws_gradient.defect,
                        gradient=ws_gradient,
                    ))
                    if self.verbose:
                        print(f"      [WARM] Seeded beam: defect {initial_gradient.defect:.4f} -> {ws_gradient.defect:.4f}")
            except Exception:
                pass  # Warm-start failed on this example, proceed normally

        all_programs: List[Tuple[float, CompositeOp]] = []

        # SGFE v2.1: Tsallis double-transition temperature annealing
        # Theory (grokking_is_lifshitz): Dream→Crystallize→Consolidate arc
        # Depth 0: High T (Dream) - explore diverse operators
        # Depth 1: Critical T (Crystallize) - balanced exploration
        # Depth 2+: Low T (Consolidate) - greedy selection
        base_T = self.temperature if self.temperature > 0 else 0.0
        
        for depth in range(self.max_depth):
            # Tsallis schedule: T_dream=1.0 → T_crystallize=0.3 → T_consolidate=0.05
            if base_T > 0 and self.max_depth > 1:
                frac = depth / max(self.max_depth - 1, 1)
                if frac < 0.5:
                    # Dream → Crystallize: linear decay
                    T_cur = base_T * (1.0 - frac * 1.4)  # 1.0 → 0.3
                else:
                    # Crystallize → Consolidate: continue decay
                    T_cur = base_T * 0.3 * (1.0 - (frac - 0.5) * 1.6)  # 0.3 → 0.05
                T_cur = max(T_cur, 0.01)
                self._current_temperature = T_cur  # Store for beam pruning
            else:
                self._current_temperature = base_T
            
            next_beam: List[SearchNode] = []

            for node in beam:
                # Propose operations for this node
                proposals = self.library.propose(
                    node.output, target_grid, node.gradient, task
                )

                for op, ig in proposals[:self.beam_width]:
                    # Apply operation
                    new_output = op.apply(node.output)
                    if new_output.shape != target_grid.shape:
                        new_output = self._adjust_shape(new_output, target_grid.shape)

                    new_gradient = DiscreteGradient.compute(new_output, target_grid)
                    new_program = CompositeOp(node.program.steps + [op])

                    if self.verbose and depth == 0:
                        print(f"      d={depth} {op.name}: "
                              f"defect {node.defect:.4f} -> {new_gradient.defect:.4f} "
                              f"(IG={ig:.4f})")

                    # Perfect solution found
                    if new_gradient.defect < 0.001:
                        all_programs.append((0.0, new_program))
                        if self.verbose:
                            print(f"    [PERFECT] {new_program.describe()} at depth {depth+1}")
                        # Don't stop — keep searching for shorter programs

                    next_beam.append(SearchNode(
                        program=new_program,
                        output=new_output,
                        defect=new_gradient.defect,
                        gradient=new_gradient,
                    ))

            # Prune beam: keep top-K by lowest defect
            # SGFE v2.1: Thermodynamic beam search with Gumbel-max in log-space
            # Theory (grokking_is_lifshitz): Temperature enables phase transition
            # by allowing traversal of saddle points in operator space.
            # Formula: noisy_score = -defect/T + G where G ~ Gumbel(0,1)
            # This preserves ranking at low T, approaches uniform at high T.
            T = getattr(self, '_current_temperature', getattr(self, 'temperature', 0.0))
            if T > 0.01 and len(next_beam) > self.beam_width:
                for node in next_beam:
                    # Gumbel-max in log-space: -defect/T + G
                    # Lower defect = higher score, so we negate defect
                    gumbel_noise = -np.log(-np.log(np.random.uniform(1e-10, 1.0)))
                    # Use -defect as "score" so lower defect = better
                    node._noisy_score = -node.defect / max(T, 0.01) + gumbel_noise
                next_beam.sort(key=lambda n: -n._noisy_score)  # Higher score = better
            else:
                next_beam.sort(key=lambda n: n.defect)
            beam = next_beam[:self.beam_width]

            # Collect partial programs
            for node in beam:
                all_programs.append((node.defect, node.program))

            # Early exit if we found a perfect solution
            if any(d < 0.001 for d, _ in all_programs):
                break

        # Sort by defect, return unique programs
        all_programs.sort(key=lambda x: x[0])
        seen = set()
        result = []
        for defect, prog in all_programs:
            key = prog.describe()
            if key not in seen:
                seen.add(key)
                result.append(prog)
            if len(result) >= self.beam_width * 2:
                break
        return result

    def _adjust_shape(self, grid: np.ndarray, target_shape: Tuple[int, int]) -> np.ndarray:
        """Pad or crop grid to match target shape."""
        tH, tW = target_shape
        cH, cW = grid.shape

        if (cH, cW) == (tH, tW):
            return grid

        result = np.full((tH, tW), BG, dtype=grid.dtype)
        copy_H = min(cH, tH)
        copy_W = min(cW, tW)
        result[:copy_H, :copy_W] = grid[:copy_H, :copy_W]
        return result


# =============================================================================
# 5. MAIN: Run solver on ARC tasks, compare to baseline
# =============================================================================

def run_evaluation(
    data_path: str,
    limit: int = None,
    verbose: bool = False,
    max_depth: int = 3,
    beam_width: int = 5,
):
    """Run the Recursive Residual Solver on ARC tasks and report results."""
    print("=" * 70)
    print("RECURSIVE RESIDUAL SOLVER - ARC Evaluation")
    print("=" * 70)
    print(f"Data:       {data_path}")
    print(f"Max Depth:  {max_depth}")
    print(f"Beam Width: {beam_width}")

    tasks = load_arc_tasks(data_path, limit=limit)
    if not tasks:
        print(f"No tasks found at {data_path}")
        return

    print(f"Tasks:      {len(tasks)}")
    print()

    solver = RecursiveResidualSolver(
        max_depth=max_depth,
        beam_width=beam_width,
        verbose=verbose,
    )

    perfect = 0
    near_miss = 0
    total = 0
    results = []

    for i, task in enumerate(tasks):
        result = solver.solve_task(task)
        results.append(result)
        total += 1

        e = result['avg_train_energy']
        is_p = result['is_perfect']
        if is_p:
            perfect += 1
            tag = "PERFECT"
        elif e < 0.1:
            near_miss += 1
            tag = f"NEAR({e:.4f})"
        else:
            tag = f"MISS({e:.4f})"

        depth = result['depth']
        method = result['method'][:60]
        elapsed = result['elapsed_ms']

        if verbose or is_p or (e < 0.1 and e > 0.001):
            print(f"  [{i+1:3d}/{len(tasks)}] {task.task_id[:12]:>12} "
                  f"{tag:>14} d={depth} {elapsed:6.0f}ms  {method}")

        # Progress update every 25 tasks
        if (i + 1) % 25 == 0 or (i + 1) == len(tasks):
            print(f"  --- Progress: {i+1}/{len(tasks)} | "
                  f"Perfect: {perfect} | Near: {near_miss} | "
                  f"Rate: {perfect/(i+1):.1%} ---")

    # Final summary
    print()
    print("=" * 70)
    print("RESULTS SUMMARY")
    print("=" * 70)
    print(f"  Total tasks:    {total}")
    print(f"  Perfect solves: {perfect} ({perfect/max(total,1):.1%})")
    print(f"  Near misses:    {near_miss} ({near_miss/max(total,1):.1%})")
    print(f"  Total fails:    {total - perfect - near_miss}")
    print()

    # Breakdown by depth
    depth_counts = Counter(r['depth'] for r in results if r['is_perfect'])
    if depth_counts:
        print("  Perfect solves by program depth:")
        for d in sorted(depth_counts):
            print(f"    Depth {d}: {depth_counts[d]} tasks")
    print()

    # Show best near-misses (most promising for next iteration)
    near_results = [(r['avg_train_energy'], r) for r in results
                    if not r['is_perfect'] and r['avg_train_energy'] < 0.15]
    near_results.sort(key=lambda x: x[0])
    if near_results:
        print("  Closest near-misses (next targets for depth expansion):")
        for e, r in near_results[:10]:
            print(f"    {r['task_id'][:12]:>12}: E={e:.4f} depth={r['depth']} "
                  f"method={r['method'][:50]}")
    print()

    return results


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description="ARC Recursive Residual Solver")
    parser.add_argument("data_path", help="Path to ARC task directory (JSON files)")
    parser.add_argument("--limit", type=int, default=None, help="Max tasks to evaluate")
    parser.add_argument("--depth", type=int, default=3, help="Max recursion depth")
    parser.add_argument("--beam", type=int, default=5, help="Beam width")
    parser.add_argument("--verbose", "-v", action="store_true", help="Verbose output")
    args = parser.parse_args()

    run_evaluation(
        data_path=args.data_path,
        limit=args.limit,
        max_depth=args.depth,
        beam_width=args.beam,
        verbose=args.verbose,
    )
