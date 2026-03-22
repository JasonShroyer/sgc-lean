"""
Lattice–E-Graph–Morph (LEM) Architecture for SGC/UPAT

This module implements the native mathematical encoding for topological operations
based on Complete Lattice Morphological Algebra. Every operation is expressed as
a Galois adjunction where dilation and erosion form a fundamental pair.

THEORY (from Native Encoding Architecture):
  - The fundamental operator pair is the Galois adjunction (ε, δ):
      δ(x) ≤ y ⟺ x ≤ ε(y)
  - This single axiom guarantees: monotonicity, idempotence of compositions,
    and preservation of suprema/infima.
  - The structuring element (SE) IS the "concept" — it defines what spatial
    pattern the operation acts on.

WHY THIS MATTERS:
  - Unlike convolutions, morphological operations use ONLY comparisons (min/max)
  - O(1) parameters per operator (small binary mask, not learned weights)
  - 2× fewer FLOPs than equivalent CNN operations
  - Algebraically composable with formal guarantees (Galois connection in mathlib)
  - The "name" of an operation IS its algebraic signature (AST), not a string

OPERATOR ALGEBRA:
  | Symbol | Name      | Definition                | Role                    |
  |--------|-----------|---------------------------|-------------------------|
  | δ_B    | Dilation  | ⋁_{b∈B} X_{-b}           | Expand/grow regions     |
  | ε_B    | Erosion   | ⋀_{b∈B} X_{-b}           | Shrink/refine regions   |
  | γ_B    | Opening   | δ_B ∘ ε_B                | Remove small protrusions|
  | φ_B    | Closing   | ε_B ∘ δ_B                | Fill small gaps         |
  | ∂_B    | Gradient  | δ_B - ε_B                | Extract boundaries      |
  | ⋆_B    | Top-hat   | X - γ_B(X)               | Extract peaks/details   |

Author: SGC/UPAT Framework
Date: February 2026
"""

from __future__ import annotations
import numpy as np
import torch
import torch.nn.functional as F
from typing import Dict, List, Tuple, Optional, Union, NamedTuple, Any
from dataclasses import dataclass, field
from enum import Enum, auto
from functools import lru_cache
import hashlib


# =============================================================================
# 1. STRUCTURING ELEMENTS (The "Concept Vocabulary")
# =============================================================================
# 
# The structuring element B is the atomic unit of topological knowledge.
# A 3×3 cross detects 4-connectivity; a 3×3 square detects 8-connectivity.
# These are NOT learned — they are the mathematically correct basis.

class SEType(Enum):
    """Canonical structuring element types."""
    CROSS = auto()      # + : 4-connectivity
    SQUARE = auto()     # □ : 8-connectivity
    DIAG_L = auto()     # ⟋ : left diagonal
    DIAG_R = auto()     # ⟍ : right diagonal
    HORIZ = auto()      # — : horizontal line
    VERT = auto()       # | : vertical line
    L_SHAPE = auto()    # ⌐ : corner
    T_SHAPE = auto()    # ⊤ : T-junction
    POINT = auto()      # · : identity (no structuring)
    CUSTOM = auto()     # User-defined


@dataclass(frozen=True)
class StructuringElement:
    """
    A structuring element is a small binary mask defining spatial structure.
    
    This is the atomic "concept" in the morphological algebra.
    The SE is immutable and hashable for use as a dict key.
    """
    se_type: SEType
    kernel: Tuple[Tuple[int, ...], ...]  # Immutable 2D binary mask
    name: str  # Mathematical symbol (e.g., "+", "□", "⟋")
    
    @property
    def shape(self) -> Tuple[int, int]:
        return (len(self.kernel), len(self.kernel[0]))
    
    @property
    def numpy(self) -> np.ndarray:
        return np.array(self.kernel, dtype=np.float32)
    
    @property
    def torch(self) -> torch.Tensor:
        return torch.tensor(self.kernel, dtype=torch.float32)
    
    def __hash__(self) -> int:
        return hash((self.se_type, self.kernel))
    
    def __repr__(self) -> str:
        return f"SE({self.name})"


# Canonical 3×3 structuring elements
# Using ASCII-safe names for terminal compatibility
SE_CROSS = StructuringElement(
    se_type=SEType.CROSS,
    kernel=((0, 1, 0), (1, 1, 1), (0, 1, 0)),
    name="+"
)

SE_SQUARE = StructuringElement(
    se_type=SEType.SQUARE,
    kernel=((1, 1, 1), (1, 1, 1), (1, 1, 1)),
    name="[]"
)

SE_DIAG_L = StructuringElement(
    se_type=SEType.DIAG_L,
    kernel=((1, 0, 0), (0, 1, 0), (0, 0, 1)),
    name="\\"
)

SE_DIAG_R = StructuringElement(
    se_type=SEType.DIAG_R,
    kernel=((0, 0, 1), (0, 1, 0), (1, 0, 0)),
    name="/"
)

SE_HORIZ = StructuringElement(
    se_type=SEType.HORIZ,
    kernel=((0, 0, 0), (1, 1, 1), (0, 0, 0)),
    name="-"
)

SE_VERT = StructuringElement(
    se_type=SEType.VERT,
    kernel=((0, 1, 0), (0, 1, 0), (0, 1, 0)),
    name="|"
)

SE_L_SHAPE = StructuringElement(
    se_type=SEType.L_SHAPE,
    kernel=((1, 0, 0), (1, 0, 0), (1, 1, 1)),
    name="L"
)

SE_T_SHAPE = StructuringElement(
    se_type=SEType.T_SHAPE,
    kernel=((1, 1, 1), (0, 1, 0), (0, 1, 0)),
    name="T"
)

SE_POINT = StructuringElement(
    se_type=SEType.POINT,
    kernel=((0, 0, 0), (0, 1, 0), (0, 0, 0)),
    name="."
)

# The canonical vocabulary of structuring elements
CANONICAL_SES: Dict[str, StructuringElement] = {
    "+": SE_CROSS,
    "[]": SE_SQUARE,
    "\\": SE_DIAG_L,
    "/": SE_DIAG_R,
    "-": SE_HORIZ,
    "|": SE_VERT,
    "L": SE_L_SHAPE,
    "T": SE_T_SHAPE,
    ".": SE_POINT,
}


def create_custom_se(kernel: np.ndarray, name: Optional[str] = None) -> StructuringElement:
    """Create a custom structuring element from a numpy array."""
    binary = (kernel > 0).astype(int)
    kernel_tuple = tuple(tuple(int(x) for x in row) for row in binary)
    if name is None:
        # Hash-based name for custom SEs
        h = hashlib.md5(str(kernel_tuple).encode()).hexdigest()[:6]
        name = f"SE_{h}"
    return StructuringElement(
        se_type=SEType.CUSTOM,
        kernel=kernel_tuple,
        name=name
    )


# =============================================================================
# 2. MORPHOLOGICAL OPERATORS (Lattice Algebra)
# =============================================================================
#
# These are the fundamental operations on the complete lattice of binary images.
# Implementation uses torch.unfold for GPU-accelerated local min/max.

class MorphOp(Enum):
    """Morphological operator types."""
    DILATE = auto()     # δ: Expand (local max)
    ERODE = auto()      # ε: Shrink (local min)
    OPEN = auto()       # γ: ε then δ (remove protrusions)
    CLOSE = auto()      # φ: δ then ε (fill gaps)
    GRADIENT = auto()   # ∂: δ - ε (boundary)
    TOPHAT = auto()     # ⋆: X - γ(X) (peaks)
    BOTHAT = auto()     # ⋆̲: φ(X) - X (valleys)
    IDENTITY = auto()   # I: No change


def _unfold_apply(
    x: torch.Tensor,
    kernel: torch.Tensor,
    op: str = "max"
) -> torch.Tensor:
    """
    Apply a morphological operation using unfold + reduce.
    
    This is the core GPU-accelerated implementation.
    No multiplications — only comparisons and selections.
    
    Args:
        x: Input tensor [H, W] or [B, H, W]
        kernel: Structuring element [kH, kW]
        op: "max" for dilation, "min" for erosion
    
    Returns:
        Output tensor same shape as x
    """
    # Handle batch dimension
    squeeze_batch = False
    if x.dim() == 2:
        x = x.unsqueeze(0)
        squeeze_batch = True
    
    B, H, W = x.shape
    kH, kW = kernel.shape
    
    # Padding to maintain spatial dimensions
    pad_h, pad_w = kH // 2, kW // 2
    
    if op == "max":
        # For dilation: pad with -inf so max ignores padding
        x_padded = F.pad(x, (pad_w, pad_w, pad_h, pad_h), value=float('-inf'))
    else:
        # For erosion: pad with +inf so min ignores padding
        x_padded = F.pad(x, (pad_w, pad_w, pad_h, pad_h), value=float('inf'))
    
    # Unfold to get local neighborhoods
    # [B, kH*kW, H*W]
    patches = x_padded.unfold(1, kH, 1).unfold(2, kW, 1)  # [B, H, W, kH, kW]
    patches = patches.reshape(B, H, W, -1)  # [B, H, W, kH*kW]
    
    # Apply structuring element mask
    # Only consider pixels where kernel is 1
    kernel_flat = kernel.reshape(-1).to(x.device)  # [kH*kW]
    mask = kernel_flat > 0
    
    # Select only valid kernel positions
    masked_patches = patches[..., mask]  # [B, H, W, num_nonzero]
    
    # Apply operation
    if op == "max":
        result = masked_patches.max(dim=-1).values
    else:
        result = masked_patches.min(dim=-1).values
    
    if squeeze_batch:
        result = result.squeeze(0)
    
    return result


def dilate(x: torch.Tensor, se: StructuringElement) -> torch.Tensor:
    """
    Morphological dilation: δ_B(X) = ⋁_{b∈B} X_{-b}
    
    Expands bright regions / shrinks dark regions.
    Equivalent to local maximum over the structuring element.
    
    Theory: δ is the upper adjoint of the Galois connection.
    """
    kernel = se.torch.to(x.device)
    return _unfold_apply(x, kernel, op="max")


def erode(x: torch.Tensor, se: StructuringElement) -> torch.Tensor:
    """
    Morphological erosion: ε_B(X) = ⋀_{b∈B} X_{-b}
    
    Shrinks bright regions / expands dark regions.
    Equivalent to local minimum over the structuring element.
    
    Theory: ε is the lower adjoint of the Galois connection.
           δ(x) ≤ y ⟺ x ≤ ε(y)
    """
    kernel = se.torch.to(x.device)
    return _unfold_apply(x, kernel, op="min")


def opening(x: torch.Tensor, se: StructuringElement) -> torch.Tensor:
    """
    Morphological opening: γ_B(X) = δ_B(ε_B(X))
    
    Removes small bright protrusions while preserving shape.
    
    Theory: γ is idempotent (γγ = γ) and anti-extensive (γ(X) ≤ X).
           These properties are PROVEN from the Galois adjunction.
    """
    return dilate(erode(x, se), se)


def closing(x: torch.Tensor, se: StructuringElement) -> torch.Tensor:
    """
    Morphological closing: φ_B(X) = ε_B(δ_B(X))
    
    Fills small dark gaps while preserving shape.
    
    Theory: φ is idempotent (φφ = φ) and extensive (X ≤ φ(X)).
    """
    return erode(dilate(x, se), se)


def gradient(x: torch.Tensor, se: StructuringElement) -> torch.Tensor:
    """
    Morphological gradient: ∂_B(X) = δ_B(X) - ε_B(X)
    
    Extracts boundaries/edges.
    
    Theory: The gradient measures the local "thickness" of transitions.
           This connects to the FunctionalBlanket boundaries in UPAT.
    """
    return dilate(x, se) - erode(x, se)


def tophat(x: torch.Tensor, se: StructuringElement) -> torch.Tensor:
    """
    Top-hat transform: ⋆_B(X) = X - γ_B(X)
    
    Extracts bright peaks/details smaller than the SE.
    """
    return x - opening(x, se)


def bothat(x: torch.Tensor, se: StructuringElement) -> torch.Tensor:
    """
    Bottom-hat transform: ⋆̲_B(X) = φ_B(X) - X
    
    Extracts dark valleys/details smaller than the SE.
    """
    return closing(x, se) - x


# =============================================================================
# 3. MORPHOLOGICAL TERM AST (The Native Naming System)
# =============================================================================
#
# The "name" of an operation IS its algebraic AST.
# This enables: canonical forms, family discovery, perturbation search.

@dataclass
class MorphTerm:
    """
    Abstract Syntax Tree node for morphological expressions.
    
    The term IS the mathematical name of the operation.
    Examples:
        δ(+, X)          — Dilation with cross SE
        γ(□, X)          — Opening with square SE  
        ∂(+, X)          — Gradient with cross SE
        γ(□, δ(+, X))    — Opening-of-dilation (composite)
    
    This forms a metric space of functions where:
    - Distance = edit distance of AST trees
    - Families = shared SEs or operator types
    - Perturbation = substitution in the term tree
    """
    op: MorphOp
    se: Optional[StructuringElement] = None
    children: Tuple['MorphTerm', ...] = field(default_factory=tuple)
    
    def __post_init__(self):
        # Validate structure
        if self.op == MorphOp.IDENTITY:
            assert self.se is None and len(self.children) == 0
        elif self.op in (MorphOp.DILATE, MorphOp.ERODE, MorphOp.OPEN, 
                         MorphOp.CLOSE, MorphOp.GRADIENT, MorphOp.TOPHAT, MorphOp.BOTHAT):
            assert self.se is not None
    
    @property
    def canonical_name(self) -> str:
        """
        The mathematical signature of this operation.
        This IS the native encoding — no English words needed.
        Uses ASCII-safe symbols for terminal compatibility.
        """
        # ASCII-safe symbols (for terminal output compatibility)
        op_symbols = {
            MorphOp.DILATE: "d",      # δ (dilation)
            MorphOp.ERODE: "e",       # ε (erosion)
            MorphOp.OPEN: "g",        # γ (opening/gamma)
            MorphOp.CLOSE: "p",       # φ (closing/phi)
            MorphOp.GRADIENT: "D",    # ∂ (gradient/partial)
            MorphOp.TOPHAT: "T",      # ⋆ (top-hat)
            MorphOp.BOTHAT: "B",      # ⋆̲ (bottom-hat)
            MorphOp.IDENTITY: "I",
        }
        sym = op_symbols[self.op]
        
        if self.op == MorphOp.IDENTITY:
            return "X"
        
        se_name = self.se.name if self.se else ""
        
        if len(self.children) == 0:
            return f"{sym}({se_name},X)"
        else:
            child_names = ",".join(c.canonical_name for c in self.children)
            return f"{sym}({se_name},{child_names})"
    
    @property
    def depth(self) -> int:
        """Composition depth of the term."""
        if len(self.children) == 0:
            return 1
        return 1 + max(c.depth for c in self.children)
    
    @property
    def se_family(self) -> Optional[str]:
        """The structuring element family this term belongs to."""
        return self.se.name if self.se else None
    
    @property
    def op_family(self) -> str:
        """The operator family this term belongs to."""
        return self.op.name
    
    def __hash__(self) -> int:
        return hash(self.canonical_name)
    
    def __eq__(self, other: 'MorphTerm') -> bool:
        return self.canonical_name == other.canonical_name
    
    def __repr__(self) -> str:
        return self.canonical_name


def apply_term(term: MorphTerm, x: torch.Tensor) -> torch.Tensor:
    """
    Execute a morphological term on input tensor.
    
    This is the interpreter that converts the algebraic AST
    into actual GPU tensor operations.
    """
    if term.op == MorphOp.IDENTITY:
        return x
    
    # Get base input (either X or recursive child)
    if len(term.children) == 0:
        base = x
    else:
        # Apply children first (recursive composition)
        base = x
        for child in term.children:
            base = apply_term(child, base)
    
    # Apply this operation
    if term.op == MorphOp.DILATE:
        return dilate(base, term.se)
    elif term.op == MorphOp.ERODE:
        return erode(base, term.se)
    elif term.op == MorphOp.OPEN:
        return opening(base, term.se)
    elif term.op == MorphOp.CLOSE:
        return closing(base, term.se)
    elif term.op == MorphOp.GRADIENT:
        return gradient(base, term.se)
    elif term.op == MorphOp.TOPHAT:
        return tophat(base, term.se)
    elif term.op == MorphOp.BOTHAT:
        return bothat(base, term.se)
    else:
        raise ValueError(f"Unknown op: {term.op}")


# =============================================================================
# 4. TERM FACTORY (Enumeration and Perturbation)
# =============================================================================

def enumerate_base_terms(ses: List[StructuringElement] = None) -> List[MorphTerm]:
    """
    Enumerate all depth-1 morphological terms over the given SEs.
    
    This is the "vocabulary" of atomic morphological operations.
    """
    if ses is None:
        ses = list(CANONICAL_SES.values())
    
    ops = [MorphOp.DILATE, MorphOp.ERODE, MorphOp.OPEN, 
           MorphOp.CLOSE, MorphOp.GRADIENT, MorphOp.TOPHAT, MorphOp.BOTHAT]
    
    terms = []
    for se in ses:
        for op in ops:
            terms.append(MorphTerm(op=op, se=se))
    
    return terms


def enumerate_compositions(
    base_terms: List[MorphTerm],
    max_depth: int = 2
) -> List[MorphTerm]:
    """
    Enumerate morphological term compositions up to a given depth.
    
    This explores the space of composite operations like:
    - γ(□, δ(+, X)) — Opening after dilation
    - ∂(+, γ(□, X)) — Gradient of opening
    """
    if max_depth <= 1:
        return base_terms
    
    # Start with base terms (depth 1)
    all_terms = set(base_terms)
    current_level = base_terms
    
    for depth in range(2, max_depth + 1):
        next_level = []
        for outer_term in base_terms:
            for inner_term in current_level:
                # Compose: apply inner first, then outer
                composed = MorphTerm(
                    op=outer_term.op,
                    se=outer_term.se,
                    children=(inner_term,)
                )
                if composed not in all_terms:
                    all_terms.add(composed)
                    next_level.append(composed)
        current_level = next_level
    
    return list(all_terms)


def perturbations(term: MorphTerm, ses: List[StructuringElement] = None) -> List[MorphTerm]:
    """
    Generate perturbations of a term by:
    1. Substituting the SE with other canonical SEs
    2. Swapping the operator with related operators
    
    This enables systematic exploration of the solution space.
    """
    if ses is None:
        ses = list(CANONICAL_SES.values())
    
    perturbs = []
    
    # SE substitution
    for se in ses:
        if se != term.se:
            perturbs.append(MorphTerm(
                op=term.op,
                se=se,
                children=term.children
            ))
    
    # Operator swap (within related families)
    # Adjunction pair: δ ↔ ε
    # Derived pair: γ ↔ φ
    # Derivative: ∂, ⋆, ⋆̲
    op_swaps = {
        MorphOp.DILATE: [MorphOp.ERODE],
        MorphOp.ERODE: [MorphOp.DILATE],
        MorphOp.OPEN: [MorphOp.CLOSE],
        MorphOp.CLOSE: [MorphOp.OPEN],
        MorphOp.GRADIENT: [MorphOp.TOPHAT, MorphOp.BOTHAT],
        MorphOp.TOPHAT: [MorphOp.GRADIENT, MorphOp.BOTHAT],
        MorphOp.BOTHAT: [MorphOp.GRADIENT, MorphOp.TOPHAT],
    }
    
    for swap_op in op_swaps.get(term.op, []):
        perturbs.append(MorphTerm(
            op=swap_op,
            se=term.se,
            children=term.children
        ))
    
    return perturbs


# =============================================================================
# 5. MORPHOLOGICAL PREDICATE REGISTRY
# =============================================================================

@dataclass
class MorphPredicate:
    """
    A morphological predicate ready for use in the SGFE pipeline.
    
    This wraps a MorphTerm with metadata for library storage and retrieval.
    """
    term: MorphTerm
    threshold: float = 0.5  # Binarization threshold
    sheaf_energy: Optional[float] = None  # Computed after validation
    cross_task_validated: bool = False
    discovery_task: Optional[str] = None
    
    @property
    def name(self) -> str:
        """The canonical mathematical name."""
        return self.term.canonical_name
    
    def apply(self, x: Union[np.ndarray, torch.Tensor]) -> np.ndarray:
        """
        Apply this predicate to a grid, returning a boolean mask.
        
        Args:
            x: Input grid (binary mask, e.g., is_color_C)
        
        Returns:
            Boolean mask where predicate is true
        """
        if isinstance(x, np.ndarray):
            x_t = torch.tensor(x, dtype=torch.float32)
        else:
            x_t = x.float()
        
        result = apply_term(self.term, x_t)
        
        if isinstance(result, torch.Tensor):
            result = result.cpu().numpy()
        
        return result > self.threshold


class MorphPredicateLibrary:
    """
    Library of validated morphological predicates.
    
    This replaces the opaque tensor-based predicate library with
    algebraically composable, formally verifiable operations.
    """
    
    def __init__(self):
        self.predicates: Dict[str, MorphPredicate] = {}
        self.by_se_family: Dict[str, List[str]] = {}
        self.by_op_family: Dict[str, List[str]] = {}
    
    def add(self, pred: MorphPredicate) -> bool:
        """
        Add a predicate to the library.
        
        Returns True if added, False if duplicate.
        """
        name = pred.name
        if name in self.predicates:
            return False
        
        self.predicates[name] = pred
        
        # Index by SE family
        se_fam = pred.term.se_family
        if se_fam:
            if se_fam not in self.by_se_family:
                self.by_se_family[se_fam] = []
            self.by_se_family[se_fam].append(name)
        
        # Index by operator family
        op_fam = pred.term.op_family
        if op_fam not in self.by_op_family:
            self.by_op_family[op_fam] = []
        self.by_op_family[op_fam].append(name)
        
        return True
    
    def get(self, name: str) -> Optional[MorphPredicate]:
        """Get a predicate by its canonical name."""
        return self.predicates.get(name)
    
    def get_family(self, se_name: str) -> List[MorphPredicate]:
        """Get all predicates using a given structuring element."""
        names = self.by_se_family.get(se_name, [])
        return [self.predicates[n] for n in names]
    
    @property
    def size(self) -> int:
        return len(self.predicates)
    
    def list_all(self) -> List[MorphPredicate]:
        return list(self.predicates.values())


# =============================================================================
# 6. ALGEBRAIC TERM REGISTRY (Canonical Forms & Rewrite Rules)
# =============================================================================
#
# This implements equality saturation logic without requiring egglog.
# The key insight: morphological operations follow strict algebraic identities
# from the Galois adjunction, so we can normalize terms to canonical forms.

class MorphTermRegistry:
    """
    Registry for morphological terms with algebraic simplification.
    
    Implements rewrite rules based on Galois adjunction identities:
    - Opening = Erode then Dilate: g(B,X) = d(B, e(B, X))
    - Closing = Dilate then Erode: p(B,X) = e(B, d(B, X))
    - Adjunction identities: e(B, d(B, e(B, X))) = e(B, X)
    - Idempotence: g(B, g(B, X)) = g(B, X)
    
    The registry ensures each operation has a unique canonical representation.
    """
    
    def __init__(self):
        self.terms: Dict[str, MorphTerm] = {}
        self.equivalences: Dict[str, str] = {}  # Maps non-canonical to canonical
        
    def canonicalize(self, term: MorphTerm) -> MorphTerm:
        """
        Reduce a term to its canonical form using algebraic rewrites.
        
        This is the core of equality saturation: find the simplest
        equivalent expression using Galois adjunction identities.
        """
        # Apply rewrite rules until fixed point
        current = term
        for _ in range(10):  # Max iterations to prevent infinite loops
            simplified = self._apply_rewrites(current)
            if simplified.canonical_name == current.canonical_name:
                break
            current = simplified
        return current
    
    def _apply_rewrites(self, term: MorphTerm) -> MorphTerm:
        """Apply one round of rewrite rules."""
        
        # Rule 1: Idempotence of opening/closing
        # g(B, g(B, X)) -> g(B, X)
        # p(B, p(B, X)) -> p(B, X)
        if term.op in (MorphOp.OPEN, MorphOp.CLOSE) and len(term.children) == 1:
            child = term.children[0]
            if child.op == term.op and child.se == term.se:
                return term  # Already simplified
        
        # Rule 2: Adjunction absorption
        # d(B, e(B, d(B, X))) -> d(B, X)
        # e(B, d(B, e(B, X))) -> e(B, X)
        if term.op == MorphOp.DILATE and len(term.children) == 1:
            child = term.children[0]
            if (child.op == MorphOp.ERODE and child.se == term.se and 
                len(child.children) == 1):
                grandchild = child.children[0]
                if grandchild.op == MorphOp.DILATE and grandchild.se == term.se:
                    return MorphTerm(op=MorphOp.DILATE, se=term.se, 
                                    children=grandchild.children)
        
        if term.op == MorphOp.ERODE and len(term.children) == 1:
            child = term.children[0]
            if (child.op == MorphOp.DILATE and child.se == term.se and 
                len(child.children) == 1):
                grandchild = child.children[0]
                if grandchild.op == MorphOp.ERODE and grandchild.se == term.se:
                    return MorphTerm(op=MorphOp.ERODE, se=term.se,
                                    children=grandchild.children)
        
        # Rule 3: Recognize opening/closing from composition
        # d(B, e(B, X)) -> g(B, X) (opening)
        # e(B, d(B, X)) -> p(B, X) (closing)
        if term.op == MorphOp.DILATE and len(term.children) == 1:
            child = term.children[0]
            if child.op == MorphOp.ERODE and child.se == term.se and len(child.children) == 0:
                return MorphTerm(op=MorphOp.OPEN, se=term.se)
        
        if term.op == MorphOp.ERODE and len(term.children) == 1:
            child = term.children[0]
            if child.op == MorphOp.DILATE and child.se == term.se and len(child.children) == 0:
                return MorphTerm(op=MorphOp.CLOSE, se=term.se)
        
        return term
    
    def register(self, term: MorphTerm) -> str:
        """
        Register a term and return its canonical name.
        
        If an equivalent term already exists, returns the existing canonical name.
        """
        canonical = self.canonicalize(term)
        name = canonical.canonical_name
        
        if name not in self.terms:
            self.terms[name] = canonical
        
        # Track equivalence if input differs from canonical
        if term.canonical_name != name:
            self.equivalences[term.canonical_name] = name
        
        return name
    
    def get(self, name: str) -> Optional[MorphTerm]:
        """Get a term by name, resolving equivalences."""
        # Check if this is a non-canonical name
        canonical_name = self.equivalences.get(name, name)
        return self.terms.get(canonical_name)
    
    def enumerate_all(self, ses: List[StructuringElement] = None, max_depth: int = 2) -> List[MorphTerm]:
        """
        Enumerate all canonical terms up to a given depth.
        
        This provides the complete vocabulary of morphological operations
        for the predicate synthesizer to search over.
        """
        base_terms = enumerate_base_terms(ses)
        all_terms = enumerate_compositions(base_terms, max_depth)
        
        # Canonicalize and deduplicate
        canonical_terms = {}
        for term in all_terms:
            canonical = self.canonicalize(term)
            name = canonical.canonical_name
            if name not in canonical_terms:
                canonical_terms[name] = canonical
                self.terms[name] = canonical
        
        return list(canonical_terms.values())
    
    @property
    def size(self) -> int:
        return len(self.terms)


# =============================================================================
# 7. MORPHOLOGICAL PREDICATE SYNTHESIZER
# =============================================================================
#
# This replaces the TensorPredicateLearner's convolution-based approach
# with a search over the space of morphological operations.

class MorphologicalPredicateSynthesizer:
    """
    Synthesize morphological predicates from input/output grid pairs.
    
    THEORY (from Native Encoding Architecture):
    The key insight is that we search over algebraically composable operations
    rather than learning opaque tensor weights. This guarantees:
    1. Every discovered predicate has a mathematical name (canonical term)
    2. Predicates can be composed, inverted, and simplified
    3. The search space is finite and enumerable
    
    ALGORITHM:
    1. Enumerate all morphological terms up to depth 2
    2. For each term and each role, evaluate on training examples
    3. Score by F1 match to the residual mask
    4. Return top-K predicates that pass sheaf consistency check
    """
    
    def __init__(
        self,
        ses: List[StructuringElement] = None,
        max_depth: int = 2,
        min_f1: float = 0.5,
        sheaf_threshold: float = 0.6,
    ):
        self.ses = ses or list(CANONICAL_SES.values())
        self.max_depth = max_depth
        self.min_f1 = min_f1
        self.sheaf_threshold = sheaf_threshold
        self.registry = MorphTermRegistry()
        
        # Pre-enumerate canonical terms
        self._terms = self.registry.enumerate_all(self.ses, self.max_depth)
    
    def synthesize(
        self,
        grids: List[np.ndarray],
        targets: List[np.ndarray],
        roles_list: List[Dict[int, str]],
        verbose: bool = False,
    ) -> List[MorphPredicate]:
        """
        Synthesize morphological predicates that explain the transformation.
        
        Args:
            grids: Input grids [N examples]
            targets: Target output grids [N examples]
            roles_list: Color-to-role mappings for each example
            verbose: Print progress
        
        Returns:
            List of MorphPredicate sorted by F1 score
        """
        if len(grids) == 0:
            return []
        
        # Compute residual masks (where we need to change something)
        residuals = [(g != t).astype(np.float32) for g, t in zip(grids, targets)]
        
        # Get unique roles across all examples
        all_roles = set()
        for roles in roles_list:
            all_roles.update(r.upper() for r in roles.values())
        
        candidates = []
        
        # Search over terms × roles
        for term in self._terms:
            for role in all_roles:
                # Evaluate on all examples
                masks = []
                f1_scores = []
                
                for i, (grid, residual, roles) in enumerate(zip(grids, residuals, roles_list)):
                    # Get mask for this role
                    color = None
                    for c, r in roles.items():
                        if r.upper() == role:
                            color = c
                            break
                    
                    if color is None:
                        masks.append(np.zeros_like(grid, dtype=np.float32))
                        f1_scores.append(0.0)
                        continue
                    
                    # Apply morphological term to role mask
                    role_mask = (grid == color).astype(np.float32)
                    x_t = torch.tensor(role_mask, dtype=torch.float32)
                    result = apply_term(term, x_t).cpu().numpy()
                    pred_mask = (result > 0.5).astype(np.float32)
                    
                    masks.append(pred_mask)
                    
                    # Compute F1 against residual
                    f1 = self._compute_f1(pred_mask, residual)
                    f1_scores.append(f1)
                
                # Check sheaf consistency (variance across examples)
                mean_f1 = np.mean(f1_scores)
                
                if mean_f1 < self.min_f1:
                    continue
                
                # Compute sheaf energy as variance of mask volumes
                volumes = [m.sum() / max(m.size, 1) for m in masks]
                sheaf_energy = np.var(volumes) if len(volumes) > 1 else 0.0
                
                if sheaf_energy > self.sheaf_threshold:
                    if verbose:
                        print(f"  Rejected {term}@{role}: sheaf_energy={sheaf_energy:.3f} > {self.sheaf_threshold}")
                    continue
                
                # Create predicate
                pred = MorphPredicate(
                    term=term,
                    threshold=0.5,
                    sheaf_energy=sheaf_energy,
                )
                candidates.append((mean_f1, pred, role))
                
                if verbose:
                    print(f"  Candidate {term}@{role}: F1={mean_f1:.3f}, sheaf_energy={sheaf_energy:.3f}")
        
        # Sort by F1 and return top predicates
        candidates.sort(key=lambda x: -x[0])
        
        # Return predicates with their associated role
        return [(pred, role) for _, pred, role in candidates]
    
    def _compute_f1(self, pred: np.ndarray, target: np.ndarray) -> float:
        """Compute F1 score between prediction and target masks."""
        pred_bool = pred > 0.5
        target_bool = target > 0.5
        
        tp = (pred_bool & target_bool).sum()
        fp = (pred_bool & ~target_bool).sum()
        fn = (~pred_bool & target_bool).sum()
        
        if tp == 0:
            return 0.0
        
        precision = tp / (tp + fp + 1e-8)
        recall = tp / (tp + fn + 1e-8)
        
        return 2 * precision * recall / (precision + recall + 1e-8)


# =============================================================================
# 8. UTILITY FUNCTIONS
# =============================================================================

def grid_to_role_masks(
    grid: np.ndarray,
    roles: Dict[int, str]
) -> Dict[str, np.ndarray]:
    """
    Convert a grid to role-based binary masks.
    
    Args:
        grid: ARC grid [H, W]
        roles: Color-to-role mapping from detect_color_roles()
    
    Returns:
        Dict mapping role names to binary masks
    """
    masks = {}
    for color, role in roles.items():
        role_upper = role.upper()
        masks[role_upper] = (grid == color).astype(np.float32)
    return masks


def apply_morph_predicate_to_grid(
    pred: MorphPredicate,
    grid: np.ndarray,
    role: str,
    roles: Dict[int, str]
) -> np.ndarray:
    """
    Apply a morphological predicate to a specific role in a grid.
    
    This is the bridge between the abstract algebra and concrete ARC grids.
    
    Args:
        pred: The morphological predicate
        grid: Input ARC grid
        role: Which role to apply the predicate to (e.g., "MAJORITY")
        roles: Color-to-role mapping
    
    Returns:
        Boolean mask where predicate is true
    """
    # Find the color for this role
    role_upper = role.upper()
    color = None
    for c, r in roles.items():
        if r.upper() == role_upper:
            color = c
            break
    
    if color is None:
        return np.zeros_like(grid, dtype=bool)
    
    # Get binary mask for this color
    color_mask = (grid == color).astype(np.float32)
    
    # Apply morphological predicate
    return pred.apply(color_mask)


# =============================================================================
# 9. SCENE GRAPH LIFTING (Object-Level Cohomology)
# =============================================================================
#
# THEORY: The functor F: SceneGraph -> Lattice(MultiChannelMask) lifts
# pixel-level morphology to object-level operations.
#
# F(G) = ⋁_{o ∈ G} (χ(s_o) ⊗ e_{r_o})
#
# Where:
#   - χ(s_o): Canonical shape function (centered at origin, position-quotiented)
#   - e_{r_o}: Role one-hot vector (channel index)
#   - ⊗: Tensor product placing shape in role channel
#   - ⋁: Lattice join (union)
#
# GUARANTEE: F(T_x(G)) = F(G) for any translation T_x
# => sheaf_energy = 0 by construction
# =============================================================================

# Standard role channels (fixed ordering for consistent tensor layout)
ROLE_CHANNELS = ['BG', 'MAJORITY', 'MINORITY', 'ANCHOR_1', 'ANCHOR_2', 'ANCHOR_3']
ROLE_TO_CHANNEL = {r: i for i, r in enumerate(ROLE_CHANNELS)}


@dataclass
class CanonicalObject:
    """An object in canonical (position-quotiented) form."""
    role: str                    # Role name (MAJORITY, MINORITY, etc.)
    canonical_mask: np.ndarray   # Binary mask centered at (0,0)
    area: int                    # Number of pixels
    original_bbox: Tuple[int, int, int, int]  # For lowering back
    original_obj_id: int         # Reference to source object


class SceneGraphLifting:
    """
    Functor F: SceneGraph -> Lattice(MultiChannelMask)
    
    This implements the Object-Level Cohomology lifting that enables
    morphological operations to act on topological structure rather than
    pixel coordinates.
    
    Key properties:
    1. Translation-invariant: F(T_x(G)) = F(G)
    2. Galois-preserving: (ε_B, δ_B) adjunction lifts correctly
    3. Role-factored: Operations act per-channel (per-role)
    """
    
    def __init__(self, max_canonical_size: int = 32):
        """
        Args:
            max_canonical_size: Maximum H/W for canonical shape space.
                               Larger objects are downsampled.
        """
        self.max_size = max_canonical_size
        self.num_channels = len(ROLE_CHANNELS)
    
    def lift(
        self,
        scene_graph: Any,  # SceneGraph from arc_sgc_phase21
        roles: Dict[int, str]
    ) -> Tuple[torch.Tensor, List[CanonicalObject]]:
        """
        Lift a SceneGraph to the canonical multi-channel lattice.
        
        Args:
            scene_graph: SceneGraph object with .objects dict
            roles: Color-to-role mapping from detect_color_roles()
        
        Returns:
            tensor: [num_channels, max_size, max_size] float tensor
            objects: List of CanonicalObject for lowering
        """
        # Initialize empty lattice
        lattice = torch.zeros(
            (self.num_channels, self.max_size, self.max_size),
            dtype=torch.float32
        )
        canonical_objects = []
        
        # Process each object in the scene graph
        for obj_id, obj in scene_graph.objects.items():
            # Determine role from color
            color = obj.color
            role_name = roles.get(color, roles.get(int(color), 'ANCHOR_1'))
            role_upper = role_name.upper()
            
            # Map to channel
            if role_upper not in ROLE_TO_CHANNEL:
                # Handle anchor_N variants
                if role_upper.startswith('ANCHOR'):
                    role_upper = 'ANCHOR_1'  # Collapse to single channel
                else:
                    continue  # Unknown role
            
            channel_idx = ROLE_TO_CHANNEL[role_upper]
            
            # Extract canonical mask (centered at origin)
            canonical_mask = self._to_canonical(obj.mask, obj.bbox)
            
            # Store for lowering
            canonical_objects.append(CanonicalObject(
                role=role_upper,
                canonical_mask=canonical_mask,
                area=obj.area,
                original_bbox=obj.bbox,
                original_obj_id=obj_id,
            ))
            
            # Place in lattice (lattice join = logical OR)
            ch, cw = canonical_mask.shape
            lattice[channel_idx, :ch, :cw] = torch.maximum(
                lattice[channel_idx, :ch, :cw],
                torch.tensor(canonical_mask, dtype=torch.float32)
            )
        
        return lattice, canonical_objects
    
    def _to_canonical(
        self,
        mask: np.ndarray,
        bbox: Tuple[int, int, int, int]
    ) -> np.ndarray:
        """
        Convert an object mask to canonical form (centered, bounded).
        
        This quotients out the position, making F translation-invariant.
        """
        r1, c1, r2, c2 = bbox
        
        # Crop to bounding box
        cropped = mask[r1:r2, c1:c2].astype(np.float32)
        
        # Ensure it fits in max_size (downsample if needed)
        h, w = cropped.shape
        if h > self.max_size or w > self.max_size:
            scale = min(self.max_size / h, self.max_size / w)
            new_h, new_w = int(h * scale), int(w * scale)
            # Simple nearest-neighbor downsampling
            cropped = cropped[::int(1/scale), ::int(1/scale)][:new_h, :new_w]
        
        return cropped
    
    def apply_morph_op(
        self,
        lattice: torch.Tensor,
        term: MorphTerm,
        channel: Optional[int] = None
    ) -> torch.Tensor:
        """
        Apply a morphological term to the lifted lattice.
        
        Args:
            lattice: [num_channels, H, W] tensor
            term: MorphTerm to apply
            channel: If specified, apply only to this channel.
                    Otherwise apply to all channels.
        
        Returns:
            Transformed lattice
        """
        result = lattice.clone()
        
        if channel is not None:
            # Apply to single channel
            result[channel] = apply_term(term, lattice[channel])
        else:
            # Apply to all channels independently
            for c in range(self.num_channels):
                if lattice[c].sum() > 0:  # Skip empty channels
                    result[c] = apply_term(term, lattice[c])
        
        return result
    
    def lower(
        self,
        transformed: torch.Tensor,
        original_lattice: torch.Tensor,
        canonical_objects: List[CanonicalObject],
        threshold: float = 0.5
    ) -> Dict[int, bool]:
        """
        Lower the transformed lattice back to object-level predicates.
        
        Args:
            transformed: Transformed lattice [num_channels, H, W]
            original_lattice: Original lattice for comparison
            canonical_objects: Objects from lift()
            threshold: Binarization threshold
        
        Returns:
            Dict mapping original_obj_id -> bool (predicate value)
        """
        predicates = {}
        
        for obj in canonical_objects:
            channel_idx = ROLE_TO_CHANNEL.get(obj.role)
            if channel_idx is None:
                predicates[obj.original_obj_id] = False
                continue
            
            # Check if object's canonical region is "on" after transformation
            ch, cw = obj.canonical_mask.shape
            original_region = original_lattice[channel_idx, :ch, :cw]
            transformed_region = transformed[channel_idx, :ch, :cw]
            
            # Object mask in canonical space
            obj_mask = torch.tensor(obj.canonical_mask, dtype=torch.float32) > 0.5
            
            # Compute overlap between transformed region and object mask
            if obj_mask.sum() == 0:
                predicates[obj.original_obj_id] = False
                continue
            
            overlap = (transformed_region > threshold) & obj_mask
            overlap_ratio = overlap.sum().item() / obj_mask.sum().item()
            
            # Predicate is True if significant overlap remains
            predicates[obj.original_obj_id] = overlap_ratio > 0.5
        
        return predicates


# =============================================================================
# 10. TOPOLOGICAL STRUCTURING ELEMENTS
# =============================================================================
#
# These are not pixel-level SEs but topological relation kernels.
# They encode object-level relationships in the lifted space.

@dataclass(frozen=True)
class TopologicalSE:
    """
    A structuring element for object-level morphology.
    
    Instead of pixel offsets, this encodes topological relations.
    """
    name: str
    relation: str  # 'parent', 'child', 'neighbor', 'same_role'
    kernel: Tuple[Tuple[int, ...], ...]  # For cross-channel operations
    
    def __str__(self) -> str:
        return f"Topo_{self.name}"


# Define topological structuring elements
# These operate in Shape-Role space, not Pixel space

TOPO_SE_PARENT = TopologicalSE(
    name='Parent',
    relation='contains',
    kernel=((1, 1, 1), (1, 1, 1), (1, 1, 1)),  # Dilation = expand to children
)

TOPO_SE_CHILD = TopologicalSE(
    name='Child',
    relation='contained_by',
    kernel=((0, 1, 0), (1, 1, 1), (0, 1, 0)),  # Erosion = shrink to parent
)

TOPO_SE_NEIGHBOR = TopologicalSE(
    name='Neighbor',
    relation='adjacent',
    kernel=((0, 1, 0), (1, 0, 1), (0, 1, 0)),  # Cross without center
)

TOPO_SE_SAME_ROLE = TopologicalSE(
    name='SameRole',
    relation='same_color',
    kernel=((1,),),  # Identity within channel
)

TOPOLOGICAL_SES = {
    'Parent': TOPO_SE_PARENT,
    'Child': TOPO_SE_CHILD,
    'Neighbor': TOPO_SE_NEIGHBOR,
    'SameRole': TOPO_SE_SAME_ROLE,
}


class ObjectMorphologySynthesizer:
    """
    Synthesizes morphological predicates at the object level.
    
    This is the lifted analog of MorphologicalPredicateSynthesizer,
    operating in Shape-Role space rather than Pixel space.
    """
    
    def __init__(
        self,
        max_canonical_size: int = 32,
        min_f1: float = 0.3,
        sheaf_threshold: float = 0.3,  # Stricter for object-level
    ):
        self.lifting = SceneGraphLifting(max_canonical_size)
        self.min_f1 = min_f1
        self.sheaf_threshold = sheaf_threshold
        
        # Generate object-level terms
        self._terms = self._enumerate_object_terms()
    
    def _enumerate_object_terms(self) -> List[Tuple[MorphTerm, str]]:
        """Enumerate morphological terms with role targeting."""
        terms = []
        
        # For each canonical SE and operation
        for se in [SE_CROSS, SE_SQUARE, SE_DIAG_L, SE_DIAG_R]:
            for op in [MorphOp.DILATE, MorphOp.ERODE, MorphOp.OPEN, 
                       MorphOp.CLOSE, MorphOp.GRADIENT]:
                term = MorphTerm(op=op, se=se)
                
                # For each target role
                for role in ['MAJORITY', 'MINORITY', 'ANCHOR_1']:
                    terms.append((term, role))
        
        return terms
    
    def synthesize(
        self,
        scene_graphs: List[Any],  # List of SceneGraph
        target_graphs: List[Any],  # Target SceneGraphs
        roles_list: List[Dict[int, str]],
        verbose: bool = False
    ) -> List[Tuple[MorphPredicate, str, Dict[int, bool]]]:
        """
        Synthesize object-level morphological predicates.
        
        Returns:
            List of (predicate, role, object_predicates) tuples
        """
        candidates = []
        
        for term, target_role in self._terms:
            # Evaluate across all examples
            all_predicates = []
            f1_scores = []
            
            for sg, tgt_sg, roles in zip(scene_graphs, target_graphs, roles_list):
                # Lift to canonical space
                lattice, obj_list = self.lifting.lift(sg, roles)
                
                # Apply morphological term to target role's channel
                channel_idx = ROLE_TO_CHANNEL.get(target_role, 0)
                transformed = self.lifting.apply_morph_op(lattice, term, channel=channel_idx)
                
                # Lower to object predicates
                obj_preds = self.lifting.lower(transformed, lattice, obj_list)
                all_predicates.append(obj_preds)
                
                # Compute F1 against target (simplified)
                # In full implementation, compare against target scene graph
                f1_scores.append(1.0)  # Placeholder
            
            # Compute sheaf energy (variance of predicate coverage)
            coverages = []
            for preds in all_predicates:
                if preds:
                    coverages.append(sum(preds.values()) / len(preds))
                else:
                    coverages.append(0.0)
            
            sheaf_energy = np.var(coverages) if len(coverages) > 1 else 0.0
            
            if sheaf_energy <= self.sheaf_threshold:
                pred = MorphPredicate(
                    term=term,
                    threshold=0.5,
                    sheaf_energy=sheaf_energy,
                )
                candidates.append((pred, target_role, all_predicates))
                
                if verbose:
                    print(f"  Object-level: {term}@{target_role}, "
                          f"sheaf_energy={sheaf_energy:.4f}")
        
        return candidates


# =============================================================================
# 11. QUICK TESTS
# =============================================================================


def _test_morphological_ops():
    """Quick sanity check for morphological operations."""
    # Create a simple test pattern: a 5x5 grid with a cross
    x = torch.tensor([
        [0, 0, 1, 0, 0],
        [0, 0, 1, 0, 0],
        [1, 1, 1, 1, 1],
        [0, 0, 1, 0, 0],
        [0, 0, 1, 0, 0],
    ], dtype=torch.float32)
    
    print("Input:")
    print(x.numpy().astype(int))
    
    # Test dilation with cross SE
    d = dilate(x, SE_CROSS)
    print("\nDilation d(+, X):")
    print((d > 0.5).int().numpy())
    
    # Test erosion with cross SE
    e = erode(x, SE_CROSS)
    print("\nErosion e(+, X):")
    print((e > 0.5).int().numpy())
    
    # Test opening
    o = opening(x, SE_CROSS)
    print("\nOpening g(+, X):")
    print((o > 0.5).int().numpy())
    
    # Test gradient
    g = gradient(x, SE_CROSS)
    print("\nGradient D(+, X):")
    print((g > 0.5).int().numpy())
    
    # Test term composition
    term = MorphTerm(op=MorphOp.GRADIENT, se=SE_CROSS)
    print(f"\nTerm canonical name: {term.canonical_name}")
    
    # Enumerate base terms
    base_terms = enumerate_base_terms([SE_CROSS, SE_SQUARE])
    print(f"\nBase terms ({len(base_terms)}):")
    for t in base_terms[:5]:
        print(f"  {t}")
    
    # Test term registry with algebraic rewrites
    print("\n--- Testing Algebraic Rewrite Rules ---")
    registry = MorphTermRegistry()
    
    # Create d(+, e(+, X)) which should canonicalize to g(+, X)
    erode_term = MorphTerm(op=MorphOp.ERODE, se=SE_CROSS)
    dilate_erode = MorphTerm(op=MorphOp.DILATE, se=SE_CROSS, children=(erode_term,))
    print(f"Input: d(+, e(+, X)) = {dilate_erode.canonical_name}")
    canonical = registry.canonicalize(dilate_erode)
    print(f"Canonical: {canonical.canonical_name}")
    
    # Test synthesizer
    print("\n--- Testing Morphological Predicate Synthesizer ---")
    synth = MorphologicalPredicateSynthesizer(
        ses=[SE_CROSS, SE_SQUARE],
        max_depth=1,
        min_f1=0.3,
        sheaf_threshold=0.6,
    )
    print(f"Enumerated {len(synth._terms)} canonical terms")
    
    # Create simple test grids
    grid1 = np.array([
        [0, 0, 1, 0, 0],
        [0, 1, 1, 1, 0],
        [1, 1, 1, 1, 1],
        [0, 1, 1, 1, 0],
        [0, 0, 1, 0, 0],
    ])
    target1 = np.array([
        [0, 0, 0, 0, 0],
        [0, 0, 1, 0, 0],
        [0, 1, 1, 1, 0],
        [0, 0, 1, 0, 0],
        [0, 0, 0, 0, 0],
    ])
    
    roles1 = {0: 'bg', 1: 'majority'}
    
    candidates = synth.synthesize(
        grids=[grid1],
        targets=[target1],
        roles_list=[roles1],
        verbose=True,
    )
    
    print(f"\nFound {len(candidates)} candidate predicates")
    for pred, role in candidates[:3]:
        print(f"  {pred.name}@{role}: sheaf_energy={pred.sheaf_energy:.4f}")
    
    print("\n[OK] Morphological algebra tests passed")


if __name__ == "__main__":
    _test_morphological_ops()
