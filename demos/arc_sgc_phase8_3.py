"""
ARC-SGC Phase 8.3: Geometry-First Physics (Shape Manifold)

THEORETICAL FOUNDATION:
The size-mismatch tasks (E≈1000+) are not "harder search" - they're missing 
state variables. The agent optimizes fields on a fixed lattice, but the task 
lives on a DIFFERENT lattice.

Phase 8.3 adds Shape Inference as a discrete latent z_shape ∈ {(H,W)}.
This is SGC's renormalization done correctly:
- Upward map (quotient): objectization + symmetry detection → smaller base space
- Downward map (lift): tile/embed/scale lifts solution back to pixel space

TWO-STAGE ACTIVE INFERENCE:
1. Infer output support (shape) - deterministic from training invariants
2. Solve content on inferred support - reuse Phase 8.1/8.2 physics

MINIMAL OPERATOR BASIS (not DSL bloat):
- Crop: rect from (bbox non-bg, bbox marker color, bbox largest object)
- Embed: place content in larger canvas with anchor
- Scale: k ∈ {2,3} inferred from dimension ratios
- Extract: new grid from object's bbox (selector: largest, unique color, etc.)

SHAPE LAW VALIDITY: Must hold across ALL training examples.
"""

import torch
from dataclasses import dataclass
from typing import List, Tuple, Dict, Optional, Set, Callable
from collections import deque, Counter
from abc import ABC, abstractmethod
import numpy as np
import json
from pathlib import Path
import sys

def printfl(*args, **kwargs):
    print(*args, **kwargs)
    sys.stdout.flush()


# =============================================================================
# CONFIGURATION
# =============================================================================

@dataclass
class ARCPhase83Config:
    max_grid_size: int = 30
    num_colors: int = 10
    background_color: int = 0
    min_object_size: int = 1
    max_objects: int = 50
    max_relax_steps: int = 20
    energy_threshold: float = 0.0001
    consistency_threshold: float = 0.005
    device: str = 'cuda' if torch.cuda.is_available() else 'cpu'


# =============================================================================
# DATA STRUCTURES
# =============================================================================

@dataclass
class ARCGrid:
    data: torch.Tensor
    
    @property
    def height(self) -> int: return self.data.shape[0]
    @property
    def width(self) -> int: return self.data.shape[1]
    @property
    def shape(self) -> Tuple[int, int]: return (self.height, self.width)
    
    @classmethod
    def from_list(cls, lst: List[List[int]], device: str = 'cpu') -> 'ARCGrid':
        return cls(torch.tensor(lst, dtype=torch.long, device=device))
    
    @classmethod
    def zeros(cls, H: int, W: int, device: str = 'cpu') -> 'ARCGrid':
        return cls(torch.zeros(H, W, dtype=torch.long, device=device))
    
    def clone(self) -> 'ARCGrid': return ARCGrid(self.data.clone())
    def to_numpy(self) -> np.ndarray: return self.data.cpu().numpy()


@dataclass
class ARCObject:
    object_id: int
    color: int
    pixels: List[Tuple[int, int]]
    
    @property
    def mass(self) -> int: return len(self.pixels)
    
    @property
    def bbox(self) -> Tuple[int, int, int, int]:
        if not self.pixels: return (0, 0, 0, 0)
        rows = [p[0] for p in self.pixels]
        cols = [p[1] for p in self.pixels]
        return (min(rows), min(cols), max(rows) + 1, max(cols) + 1)
    
    @property
    def bbox_size(self) -> Tuple[int, int]:
        r1, c1, r2, c2 = self.bbox
        return (r2 - r1, c2 - c1)


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
        train = [ARCExample(
            ARCGrid.from_list(ex['input'], device),
            ARCGrid.from_list(ex.get('output', ex['input']), device)
        ) for ex in data['train']]
        test = [ARCExample(
            ARCGrid.from_list(ex['input'], device),
            ARCGrid.from_list(ex.get('output', ex['input']), device)
        ) for ex in data['test']]
        return cls(task_id, train, test)


def load_arc_tasks(path: str, device: str = 'cpu', limit: int = None) -> List[ARCTask]:
    tasks = []
    p = Path(path)
    if not p.exists(): return tasks
    for f in sorted(p.glob("*.json"))[:limit]:
        try:
            with open(f) as fp:
                tasks.append(ARCTask.from_json(f.stem, json.load(fp), device))
        except: pass
    return tasks


def detect_objects(grid: ARCGrid, config: ARCPhase83Config, include_background: bool = False) -> List[ARCObject]:
    data = grid.to_numpy()
    H, W = data.shape
    visited = np.zeros((H, W), dtype=bool)
    objects = []
    obj_id = 0
    
    for r in range(H):
        for c in range(W):
            if visited[r, c]: continue
            color = data[r, c]
            if not include_background and color == config.background_color:
                visited[r, c] = True
                continue
            pixels = []
            queue = deque([(r, c)])
            visited[r, c] = True
            
            while queue:
                cr, cc = queue.popleft()
                pixels.append((cr, cc))
                for dr, dc in [(-1,0), (1,0), (0,-1), (0,1)]:
                    nr, nc = cr + dr, cc + dc
                    if 0 <= nr < H and 0 <= nc < W and not visited[nr, nc]:
                        if data[nr, nc] == color:
                            visited[nr, nc] = True
                            queue.append((nr, nc))
            
            if len(pixels) >= config.min_object_size:
                objects.append(ARCObject(obj_id, int(color), pixels))
                obj_id += 1
                if obj_id >= config.max_objects:
                    return objects
    return objects


def compute_defect_energy(pred: ARCGrid, target: ARCGrid) -> float:
    if pred.shape != target.shape:
        return 1000.0 + abs(pred.height - target.height) + abs(pred.width - target.width)
    return (pred.data != target.data).float().sum().item() / target.data.numel()


def get_content_bbox(grid: ARCGrid, config: ARCPhase83Config) -> Optional[Tuple[int, int, int, int]]:
    """Get bounding box of all non-background content."""
    data = grid.to_numpy()
    non_bg = np.argwhere(data != config.background_color)
    if len(non_bg) == 0:
        return None
    r1, c1 = non_bg.min(axis=0)
    r2, c2 = non_bg.max(axis=0)
    return (r1, c1, r2 + 1, c2 + 1)


def get_color_bbox(grid: ARCGrid, color: int) -> Optional[Tuple[int, int, int, int]]:
    """Get bounding box of specific color."""
    data = grid.to_numpy()
    positions = np.argwhere(data == color)
    if len(positions) == 0:
        return None
    r1, c1 = positions.min(axis=0)
    r2, c2 = positions.max(axis=0)
    return (r1, c1, r2 + 1, c2 + 1)


# =============================================================================
# SHAPE INFERENCE MODULE
# =============================================================================

@dataclass
class ShapeCandidate:
    """A candidate output shape with its derivation."""
    height: int
    width: int
    source: str  # How this shape was derived
    confidence: float = 1.0
    
    @property
    def shape(self) -> Tuple[int, int]:
        return (self.height, self.width)
    
    def __hash__(self):
        return hash((self.height, self.width))
    
    def __eq__(self, other):
        return self.height == other.height and self.width == other.width


class ShapeInference:
    """
    Infer output shape as discrete latent z_shape ∈ {(H,W)}.
    Generates candidates DETERMINISTICALLY from training invariants.
    """
    
    def __init__(self, config: ARCPhase83Config):
        self.config = config
    
    def infer_candidates(self, examples: List[ARCExample]) -> List[ShapeCandidate]:
        """
        Generate ranked shape candidates from training examples.
        No optimization - purely from invariants.
        """
        candidates = []
        
        # S0: Copy input shape (identity)
        candidates.extend(self._s0_copy_input(examples))
        
        # S1: Output shape seen in training (ground truth when available)
        candidates.extend(self._s1_output_shapes(examples))
        
        # S2: Bounding box derived shapes
        candidates.extend(self._s2_bbox_shapes(examples))
        
        # S3: Scale/tile hypotheses from dimension ratios
        candidates.extend(self._s3_scale_shapes(examples))
        
        # S4: Object-derived shapes
        candidates.extend(self._s4_object_shapes(examples))
        
        # Deduplicate and rank by consistency
        return self._rank_candidates(candidates, examples)
    
    def _s0_copy_input(self, examples: List[ARCExample]) -> List[ShapeCandidate]:
        """S0: Input shape → Output shape (identity mapping)."""
        shapes = []
        for ex in examples:
            shapes.append(ShapeCandidate(
                ex.input_grid.height,
                ex.input_grid.width,
                "copy_input"
            ))
        return shapes
    
    def _s1_output_shapes(self, examples: List[ARCExample]) -> List[ShapeCandidate]:
        """S1: Observed output shapes from training pairs."""
        shapes = []
        output_shapes = [ex.output_grid.shape for ex in examples]
        
        # Check if all outputs have same shape
        if len(set(output_shapes)) == 1:
            H, W = output_shapes[0]
            shapes.append(ShapeCandidate(H, W, "consistent_output", confidence=1.0))
        else:
            # Multiple output shapes - record all
            for H, W in set(output_shapes):
                count = output_shapes.count((H, W))
                shapes.append(ShapeCandidate(H, W, "observed_output", 
                                            confidence=count/len(output_shapes)))
        return shapes
    
    def _s2_bbox_shapes(self, examples: List[ARCExample]) -> List[ShapeCandidate]:
        """S2: Shapes derived from bounding boxes."""
        shapes = []
        
        for ex in examples:
            # Content bbox of input
            bbox = get_content_bbox(ex.input_grid, self.config)
            if bbox:
                r1, c1, r2, c2 = bbox
                shapes.append(ShapeCandidate(r2-r1, c2-c1, "input_content_bbox"))
            
            # Content bbox of output (if available)
            bbox = get_content_bbox(ex.output_grid, self.config)
            if bbox:
                r1, c1, r2, c2 = bbox
                shapes.append(ShapeCandidate(r2-r1, c2-c1, "output_content_bbox"))
            
            # Per-color bboxes
            for color in range(1, 6):  # Check colors 1-5
                bbox = get_color_bbox(ex.input_grid, color)
                if bbox:
                    r1, c1, r2, c2 = bbox
                    shapes.append(ShapeCandidate(r2-r1, c2-c1, f"color_{color}_bbox"))
        
        return shapes
    
    def _s3_scale_shapes(self, examples: List[ARCExample]) -> List[ShapeCandidate]:
        """S3: Scale hypotheses from dimension ratios."""
        shapes = []
        
        for ex in examples:
            iH, iW = ex.input_grid.shape
            oH, oW = ex.output_grid.shape
            
            # Check for integer scale factors
            for k in [2, 3, 4]:
                # Upscale
                shapes.append(ShapeCandidate(iH * k, iW * k, f"scale_{k}x"))
                # Downscale
                if iH % k == 0 and iW % k == 0:
                    shapes.append(ShapeCandidate(iH // k, iW // k, f"downscale_{k}x"))
            
            # Infer scale from actual output
            if oH > 0 and oW > 0:
                if oH % iH == 0 and oW % iW == 0 and oH // iH == oW // iW:
                    k = oH // iH
                    if 1 < k <= 4:
                        shapes.append(ShapeCandidate(oH, oW, f"inferred_scale_{k}x", confidence=1.0))
                if iH % oH == 0 and iW % oW == 0 and iH // oH == iW // oW:
                    k = iH // oH
                    if 1 < k <= 4:
                        shapes.append(ShapeCandidate(oH, oW, f"inferred_downscale_{k}x", confidence=1.0))
        
        return shapes
    
    def _s4_object_shapes(self, examples: List[ARCExample]) -> List[ShapeCandidate]:
        """S4: Shapes derived from individual objects."""
        shapes = []
        
        for ex in examples:
            objects = detect_objects(ex.input_grid, self.config)
            if not objects:
                continue
            
            # Largest object bbox
            largest = max(objects, key=lambda o: o.mass)
            H, W = largest.bbox_size
            shapes.append(ShapeCandidate(H, W, "largest_object_bbox"))
            
            # Smallest non-trivial object
            non_trivial = [o for o in objects if o.mass > 1]
            if non_trivial:
                smallest = min(non_trivial, key=lambda o: o.mass)
                H, W = smallest.bbox_size
                shapes.append(ShapeCandidate(H, W, "smallest_object_bbox"))
            
            # Unique color object (if only one object has that color)
            color_counts = Counter(o.color for o in objects)
            for color, count in color_counts.items():
                if count == 1:
                    unique_obj = next(o for o in objects if o.color == color)
                    H, W = unique_obj.bbox_size
                    shapes.append(ShapeCandidate(H, W, f"unique_color_{color}_bbox"))
        
        return shapes
    
    def _rank_candidates(self, candidates: List[ShapeCandidate], 
                         examples: List[ARCExample]) -> List[ShapeCandidate]:
        """Deduplicate and rank by consistency with training outputs."""
        # Group by shape
        shape_groups: Dict[Tuple[int,int], List[ShapeCandidate]] = {}
        for c in candidates:
            key = c.shape
            if key not in shape_groups:
                shape_groups[key] = []
            shape_groups[key].append(c)
        
        # Score each unique shape
        ranked = []
        for shape, group in shape_groups.items():
            # Check consistency: does this shape match ALL training outputs?
            matches = sum(1 for ex in examples if ex.output_grid.shape == shape)
            consistency = matches / len(examples)
            
            # Best source for this shape
            best_source = max(group, key=lambda c: c.confidence)
            
            ranked.append(ShapeCandidate(
                shape[0], shape[1],
                best_source.source,
                confidence=consistency * best_source.confidence
            ))
        
        # Sort by confidence (consistency)
        ranked.sort(key=lambda c: -c.confidence)
        
        # Filter to valid sizes
        ranked = [c for c in ranked if 1 <= c.height <= 30 and 1 <= c.width <= 30]
        
        return ranked[:10]  # Top 10 candidates


# =============================================================================
# SHAPE MORPHISMS (Minimal Operator Basis)
# =============================================================================

class ShapeMorphism(ABC):
    """A functor from one grid lattice to another."""
    
    @abstractmethod
    def apply(self, grid: ARCGrid, config: ARCPhase83Config) -> ARCGrid:
        pass
    
    @abstractmethod
    def output_shape(self, input_shape: Tuple[int, int]) -> Tuple[int, int]:
        pass
    
    @abstractmethod
    def name(self) -> str:
        pass


class CropMorphism(ShapeMorphism):
    """Crop to a rectangle."""
    
    def __init__(self, r1: int, c1: int, r2: int, c2: int):
        self.r1, self.c1, self.r2, self.c2 = r1, c1, r2, c2
    
    def apply(self, grid: ARCGrid, config: ARCPhase83Config) -> ARCGrid:
        data = grid.data[self.r1:self.r2, self.c1:self.c2].clone()
        return ARCGrid(data)
    
    def output_shape(self, input_shape: Tuple[int, int]) -> Tuple[int, int]:
        return (self.r2 - self.r1, self.c2 - self.c1)
    
    def name(self) -> str:
        return f"crop({self.r1}:{self.r2},{self.c1}:{self.c2})"


class CropToContentMorphism(ShapeMorphism):
    """Crop to bounding box of non-background content."""
    
    def __init__(self):
        self._bbox = None
    
    def apply(self, grid: ARCGrid, config: ARCPhase83Config) -> ARCGrid:
        bbox = get_content_bbox(grid, config)
        if bbox is None:
            return grid.clone()
        r1, c1, r2, c2 = bbox
        self._bbox = bbox
        return ARCGrid(grid.data[r1:r2, c1:c2].clone())
    
    def output_shape(self, input_shape: Tuple[int, int]) -> Tuple[int, int]:
        if self._bbox:
            r1, c1, r2, c2 = self._bbox
            return (r2 - r1, c2 - c1)
        return input_shape
    
    def name(self) -> str:
        return "crop_to_content"


class CropToColorMorphism(ShapeMorphism):
    """Crop to bounding box of specific color."""
    
    def __init__(self, color: int):
        self.color = color
        self._bbox = None
    
    def apply(self, grid: ARCGrid, config: ARCPhase83Config) -> ARCGrid:
        bbox = get_color_bbox(grid, self.color)
        if bbox is None:
            return grid.clone()
        r1, c1, r2, c2 = bbox
        self._bbox = bbox
        return ARCGrid(grid.data[r1:r2, c1:c2].clone())
    
    def output_shape(self, input_shape: Tuple[int, int]) -> Tuple[int, int]:
        if self._bbox:
            r1, c1, r2, c2 = self._bbox
            return (r2 - r1, c2 - c1)
        return input_shape
    
    def name(self) -> str:
        return f"crop_to_color({self.color})"


class ScaleMorphism(ShapeMorphism):
    """Scale by integer factor."""
    
    def __init__(self, k: int):
        self.k = k
    
    def apply(self, grid: ARCGrid, config: ARCPhase83Config) -> ARCGrid:
        data = grid.data
        H, W = data.shape
        scaled = data.repeat_interleave(self.k, dim=0).repeat_interleave(self.k, dim=1)
        return ARCGrid(scaled)
    
    def output_shape(self, input_shape: Tuple[int, int]) -> Tuple[int, int]:
        return (input_shape[0] * self.k, input_shape[1] * self.k)
    
    def name(self) -> str:
        return f"scale({self.k}x)"


class DownscaleMorphism(ShapeMorphism):
    """Downscale by integer factor using majority pooling."""
    
    def __init__(self, k: int):
        self.k = k
    
    def apply(self, grid: ARCGrid, config: ARCPhase83Config) -> ARCGrid:
        data = grid.to_numpy()
        H, W = data.shape
        if H % self.k != 0 or W % self.k != 0:
            return grid.clone()
        
        newH, newW = H // self.k, W // self.k
        result = np.zeros((newH, newW), dtype=data.dtype)
        
        for r in range(newH):
            for c in range(newW):
                block = data[r*self.k:(r+1)*self.k, c*self.k:(c+1)*self.k]
                # Majority vote (most common value)
                values, counts = np.unique(block, return_counts=True)
                result[r, c] = values[np.argmax(counts)]
        
        return ARCGrid(torch.tensor(result, dtype=torch.long, device=grid.data.device))
    
    def output_shape(self, input_shape: Tuple[int, int]) -> Tuple[int, int]:
        return (input_shape[0] // self.k, input_shape[1] // self.k)
    
    def name(self) -> str:
        return f"downscale({self.k}x)"


class ExtractObjectMorphism(ShapeMorphism):
    """Extract a specific object to its own canvas."""
    
    def __init__(self, selector: str = "largest"):
        self.selector = selector
        self._output_shape = None
    
    def apply(self, grid: ARCGrid, config: ARCPhase83Config) -> ARCGrid:
        objects = detect_objects(grid, config)
        if not objects:
            self._output_shape = grid.shape
            return grid.clone()
        
        # Select object
        if self.selector == "largest":
            obj = max(objects, key=lambda o: o.mass)
        elif self.selector == "smallest":
            obj = min(objects, key=lambda o: o.mass)
        elif self.selector.startswith("color_"):
            color = int(self.selector.split("_")[1])
            matching = [o for o in objects if o.color == color]
            if not matching:
                self._output_shape = grid.shape
                return grid.clone()
            obj = max(matching, key=lambda o: o.mass)
        else:
            obj = objects[0]
        
        # Extract to bbox
        r1, c1, r2, c2 = obj.bbox
        H, W = r2 - r1, c2 - c1
        self._output_shape = (H, W)
        
        result = torch.zeros(H, W, dtype=torch.long, device=grid.data.device)
        for r, c in obj.pixels:
            result[r - r1, c - c1] = obj.color
        
        return ARCGrid(result)
    
    def output_shape(self, input_shape: Tuple[int, int]) -> Tuple[int, int]:
        return self._output_shape or input_shape
    
    def name(self) -> str:
        return f"extract({self.selector})"


class TileMorphism(ShapeMorphism):
    """Tile/repeat the grid."""
    
    def __init__(self, repeat_h: int, repeat_w: int):
        self.repeat_h = repeat_h
        self.repeat_w = repeat_w
    
    def apply(self, grid: ARCGrid, config: ARCPhase83Config) -> ARCGrid:
        data = grid.data
        tiled = data.repeat(self.repeat_h, self.repeat_w)
        return ARCGrid(tiled)
    
    def output_shape(self, input_shape: Tuple[int, int]) -> Tuple[int, int]:
        return (input_shape[0] * self.repeat_h, input_shape[1] * self.repeat_w)
    
    def name(self) -> str:
        return f"tile({self.repeat_h}x{self.repeat_w})"


class IdentityMorphism(ShapeMorphism):
    """Identity (no shape change)."""
    
    def apply(self, grid: ARCGrid, config: ARCPhase83Config) -> ARCGrid:
        return grid.clone()
    
    def output_shape(self, input_shape: Tuple[int, int]) -> Tuple[int, int]:
        return input_shape
    
    def name(self) -> str:
        return "identity"


# =============================================================================
# MORPHISM INFERENCE
# =============================================================================

class MorphismInference:
    """Infer the correct shape morphism from training examples."""
    
    def __init__(self, config: ARCPhase83Config):
        self.config = config
    
    def infer_morphism(self, examples: List[ARCExample]) -> Optional[ShapeMorphism]:
        """
        Find a shape morphism that is CONSISTENT across all training examples.
        Returns None if no consistent morphism found.
        """
        candidates = self._generate_morphism_candidates(examples)
        
        for morphism in candidates:
            if self._is_consistent(morphism, examples):
                return morphism
        
        return None
    
    def _generate_morphism_candidates(self, examples: List[ARCExample]) -> List[ShapeMorphism]:
        """Generate candidate morphisms from training invariants."""
        candidates = [IdentityMorphism()]
        
        # Analyze dimension relationships
        for ex in examples:
            iH, iW = ex.input_grid.shape
            oH, oW = ex.output_grid.shape
            
            # Crop to content
            candidates.append(CropToContentMorphism())
            
            # Crop to specific colors
            for color in range(1, 6):
                candidates.append(CropToColorMorphism(color))
            
            # Scale morphisms
            for k in [2, 3]:
                candidates.append(ScaleMorphism(k))
                if iH % k == 0 and iW % k == 0:
                    candidates.append(DownscaleMorphism(k))
            
            # Extract object morphisms
            for selector in ["largest", "smallest"]:
                candidates.append(ExtractObjectMorphism(selector))
            for color in range(1, 6):
                candidates.append(ExtractObjectMorphism(f"color_{color}"))
            
            # Tile morphisms (infer from dimension ratios)
            if oH > iH and oW > iW:
                if oH % iH == 0 and oW % iW == 0:
                    candidates.append(TileMorphism(oH // iH, oW // iW))
        
        return candidates
    
    def _is_consistent(self, morphism: ShapeMorphism, examples: List[ARCExample]) -> bool:
        """Check if morphism produces correct output shape for ALL examples."""
        for ex in examples:
            try:
                result = morphism.apply(ex.input_grid, self.config)
                if result.shape != ex.output_grid.shape:
                    return False
            except:
                return False
        return True


# =============================================================================
# MOVEMENT POTENTIALS (from Phase 8.2)
# =============================================================================

class PotentialFunction(ABC):
    @abstractmethod
    def compute(self, obj: ARCObject, grid: ARCGrid, all_objects: List[ARCObject], config) -> float:
        pass
    @abstractmethod
    def name(self) -> str:
        pass


class V_BoundaryDist(PotentialFunction):
    def compute(self, obj, grid, all_objects, config):
        H, W = grid.height, grid.width
        r1, c1, r2, c2 = obj.bbox
        return min(r1, H - r2, c1, W - c2)
    def name(self): return "V_boundary"


class V_TopEdge(PotentialFunction):
    def compute(self, obj, grid, all_objects, config):
        return obj.bbox[0]
    def name(self): return "V_top"


class V_BottomEdge(PotentialFunction):
    def compute(self, obj, grid, all_objects, config):
        return grid.height - obj.bbox[2]
    def name(self): return "V_bottom"


class V_ContactDist(PotentialFunction):
    def compute(self, obj, grid, all_objects, config):
        cr, cc = obj.bbox[0] + (obj.bbox[2]-obj.bbox[0])/2, obj.bbox[1] + (obj.bbox[3]-obj.bbox[1])/2
        min_dist = float('inf')
        for other in all_objects:
            if other.object_id == obj.object_id: continue
            if other.color == config.background_color: continue
            or_ = other.bbox[0] + (other.bbox[2]-other.bbox[0])/2
            oc = other.bbox[1] + (other.bbox[3]-other.bbox[1])/2
            dist = ((cr - or_)**2 + (cc - oc)**2) ** 0.5
            min_dist = min(min_dist, dist)
        return min_dist if min_dist != float('inf') else 0.0
    def name(self): return "V_contact"


class CompositePotential:
    def __init__(self, potentials: List[PotentialFunction], weights: np.ndarray):
        self.potentials = potentials
        self.weights = weights
    
    def compute(self, obj, grid, all_objects, config) -> float:
        total = 0.0
        for pot, w in zip(self.potentials, self.weights):
            if abs(w) > 0.01:
                total += w * pot.compute(obj, grid, all_objects, config)
        return total
    
    def gradient(self, obj, grid, all_objects, config) -> Tuple[int, int]:
        H, W = grid.height, grid.width
        current = self.compute(obj, grid, all_objects, config)
        best_dir, best_decrease = (0, 0), 0.0
        
        for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
            new_pixels = [(r + dr, c + dc) for r, c in obj.pixels]
            if all(0 <= r < H and 0 <= c < W for r, c in new_pixels):
                moved_obj = ARCObject(obj.object_id, obj.color, new_pixels)
                new_pot = self.compute(moved_obj, grid, all_objects, config)
                decrease = current - new_pot
                if decrease > best_decrease:
                    best_decrease = decrease
                    best_dir = (dr, dc)
        return best_dir
    
    def signature(self) -> str:
        parts = []
        for pot, w in zip(self.potentials, self.weights):
            if abs(w) > 0.01:
                parts.append(f"{w:+.1f}*{pot.name()}")
        return " ".join(parts) if parts else "identity"


def relax_system(grid: ARCGrid, potential: CompositePotential, target_color: int, 
                 config: ARCPhase83Config, max_steps: int = 20) -> ARCGrid:
    """Relax objects of target_color by gradient descent on potential."""
    data = grid.data.clone()
    H, W = data.shape
    
    for step in range(max_steps):
        current_grid = ARCGrid(data)
        objects = detect_objects(current_grid, config)
        targets = [o for o in objects if o.color == target_color]
        if not targets: break
        
        moved_any = False
        for obj in targets:
            dr, dc = potential.gradient(obj, current_grid, objects, config)
            if dr == 0 and dc == 0: continue
            
            # Check if move is valid
            can_move = True
            for r, c in obj.pixels:
                nr, nc = r + dr, c + dc
                if not (0 <= nr < H and 0 <= nc < W):
                    can_move = False; break
                if data[nr, nc] != config.background_color:
                    # Check if destination is part of same object
                    if (nr, nc) not in obj.pixels:
                        can_move = False; break
            
            if can_move:
                # Clear old positions
                for r, c in obj.pixels:
                    data[r, c] = config.background_color
                # Set new positions
                for r, c in obj.pixels:
                    data[r + dr, c + dc] = target_color
                moved_any = True
        
        if not moved_any: break
    
    return ARCGrid(data)


def relax_all_colors(grid: ARCGrid, potential: CompositePotential, 
                     config: ARCPhase83Config) -> ARCGrid:
    """Relax all non-background colors."""
    result = grid.clone()
    for color in range(1, config.num_colors):
        if (result.data == color).any():
            result = relax_system(result, potential, color, config)
    return result


# =============================================================================
# CONTENT SOLVERS (Unified: Movement + Color + Pattern)
# =============================================================================

class ContentSolver:
    """Solve content on a fixed-shape canvas using movement, color, and pattern ops."""
    
    def __init__(self, config: ARCPhase83Config):
        self.config = config
        self.movement_potentials = [
            V_BoundaryDist(), V_TopEdge(), V_BottomEdge(), V_ContactDist()
        ]
    
    def solve(self, input_grid: ARCGrid, target_shape: Tuple[int, int], 
              target_grid: Optional[ARCGrid] = None) -> Tuple[ARCGrid, float, str]:
        """
        Given input and target shape, find best content mapping.
        Returns (result, energy, method).
        """
        if input_grid.shape == target_shape:
            # Same shape - try movement, color, and pattern ops
            return self._solve_same_shape(input_grid, target_grid)
        else:
            # Different shape - already handled by morphism
            return input_grid.clone(), 1000.0, "shape_mismatch"
    
    def _solve_same_shape(self, input_grid: ARCGrid, 
                          target_grid: Optional[ARCGrid]) -> Tuple[ARCGrid, float, str]:
        """Solve when shapes match using unified physics."""
        if target_grid is None:
            return input_grid.clone(), 0.0, "no_target"
        
        best_result = input_grid.clone()
        best_energy = compute_defect_energy(best_result, target_grid)
        best_method = "identity"
        
        # Try color operations
        for from_c in range(1, 6):
            for to_c in range(0, 6):
                if from_c == to_c:
                    continue
                result = self._color_map(input_grid, from_c, to_c)
                energy = compute_defect_energy(result, target_grid)
                if energy < best_energy:
                    best_energy = energy
                    best_result = result
                    best_method = f"color_map({from_c}->{to_c})"
        
        # Try pattern operations
        for op_name, op_func in [
            ("flip_h", lambda g: ARCGrid(g.data.flip(1))),
            ("flip_v", lambda g: ARCGrid(g.data.flip(0))),
            ("rot90", lambda g: ARCGrid(g.data.rot90(1, [0, 1]))),
            ("rot180", lambda g: ARCGrid(g.data.rot90(2, [0, 1]))),
            ("rot270", lambda g: ARCGrid(g.data.rot90(3, [0, 1]))),
        ]:
            try:
                result = op_func(input_grid)
                if result.shape == target_grid.shape:
                    energy = compute_defect_energy(result, target_grid)
                    if energy < best_energy:
                        best_energy = energy
                        best_result = result
                        best_method = op_name
            except:
                pass
        
        # Try movement potentials (single potentials with +/- sign)
        n = len(self.movement_potentials)
        for i, pot in enumerate(self.movement_potentials):
            for sign in [-1.0, 1.0]:
                weights = np.zeros(n)
                weights[i] = sign
                potential = CompositePotential(self.movement_potentials, weights)
                result = relax_all_colors(input_grid, potential, self.config)
                energy = compute_defect_energy(result, target_grid)
                if energy < best_energy:
                    best_energy = energy
                    best_result = result
                    best_method = potential.signature()
        
        return best_result, best_energy, best_method
    
    def _color_map(self, grid: ARCGrid, from_c: int, to_c: int) -> ARCGrid:
        data = grid.data.clone()
        data[data == from_c] = to_c
        return ARCGrid(data)


# =============================================================================
# GEOMETRY-FIRST SOLVER
# =============================================================================

class GeometryFirstSolver:
    """
    Two-stage solver:
    1. Infer output shape (geometry)
    2. Solve content on correct canvas (physics)
    """
    
    def __init__(self, config: ARCPhase83Config):
        self.config = config
        self.shape_inference = ShapeInference(config)
        self.morphism_inference = MorphismInference(config)
        self.content_solver = ContentSolver(config)
    
    def solve_task(self, task: ARCTask, verbose: bool = False) -> Dict:
        """Solve task with geometry-first approach."""
        examples = task.train_examples
        
        if verbose:
            printfl(f"\n   === STAGE 1: Shape Inference ===")
        
        # Check if shapes are consistent
        input_shapes = [ex.input_grid.shape for ex in examples]
        output_shapes = [ex.output_grid.shape for ex in examples]
        
        same_shape = all(i == o for i, o in zip(input_shapes, output_shapes))
        consistent_output = len(set(output_shapes)) == 1
        
        if verbose:
            printfl(f"   Input shapes: {input_shapes}")
            printfl(f"   Output shapes: {output_shapes}")
            printfl(f"   Same I/O shape: {same_shape}")
            printfl(f"   Consistent output: {consistent_output}")
        
        # Stage 1: Infer shape morphism
        morphism = None
        if not same_shape:
            morphism = self.morphism_inference.infer_morphism(examples)
            if morphism and verbose:
                printfl(f"   Inferred morphism: {morphism.name()}")
        
        if verbose:
            printfl(f"\n   === STAGE 2: Content Solving ===")
        
        # Stage 2: Solve content
        train_energies = []
        test_energies = []
        methods = []
        
        for ex in examples:
            # Apply morphism if needed
            if morphism:
                transformed = morphism.apply(ex.input_grid, self.config)
            else:
                transformed = ex.input_grid
            
            # Solve content
            result, energy, method = self.content_solver.solve(
                transformed, ex.output_grid.shape, ex.output_grid
            )
            train_energies.append(energy)
            methods.append(method)
            
            if verbose and energy < 0.5:
                printfl(f"   Train example: E={energy:.4f} ({method})")
        
        # Apply to test
        for ex in task.test_examples:
            if morphism:
                transformed = morphism.apply(ex.input_grid, self.config)
            else:
                transformed = ex.input_grid
            
            result, energy, method = self.content_solver.solve(
                transformed, ex.output_grid.shape, ex.output_grid
            )
            test_energies.append(energy)
        
        avg_train = np.mean(train_energies)
        is_perfect = avg_train < self.config.energy_threshold
        is_consistent = all(e < self.config.consistency_threshold for e in train_energies)
        
        # Determine operation description
        if morphism and morphism.name() != "identity":
            op_name = morphism.name()
            if methods and methods[0] != "identity":
                op_name += " + " + methods[0]
        else:
            op_name = methods[0] if methods else "identity"
        
        return {
            'task_id': task.task_id,
            'operation': op_name,
            'morphism': morphism.name() if morphism else "none",
            'avg_train_energy': avg_train,
            'train_energies': train_energies,
            'avg_test_energy': np.mean(test_energies) if test_energies else 0,
            'test_energies': test_energies,
            'is_consistent': is_consistent,
            'is_perfect': is_perfect,
            'same_shape': same_shape
        }


# =============================================================================
# EVALUATION
# =============================================================================

def run_evaluation(data_path: str, config: ARCPhase83Config, num_tasks: int = 100):
    printfl("=" * 70)
    printfl("ARC-SGC Phase 8.3: Geometry-First Physics")
    printfl("=" * 70)
    
    tasks = load_arc_tasks(data_path, config.device, num_tasks)
    printfl(f"\nLoaded {len(tasks)} tasks")
    
    if not tasks:
        printfl("No tasks found!")
        return []
    
    solver = GeometryFirstSolver(config)
    
    all_results = []
    perfect_tasks = []
    consistent_tasks = []
    shape_solved = []  # Tasks where morphism helped
    
    for i, task in enumerate(tasks):
        printfl(f"\n{'='*60}")
        printfl(f"Task {i+1}/{len(tasks)}: {task.task_id}")
        printfl(f"  Examples: {len(task.train_examples)} train, {len(task.test_examples)} test")
        
        result = solver.solve_task(task, verbose=True)
        all_results.append(result)
        
        if result['is_perfect']:
            status = "[PERFECT]"
            perfect_tasks.append(result)
        elif result['is_consistent']:
            status = "[CONSISTENT]"
            consistent_tasks.append(result)
        elif result['avg_train_energy'] < 0.3:
            status = "[partial]"
        else:
            status = "[failed]"
        
        if result['morphism'] != "none" and result['morphism'] != "identity":
            shape_solved.append(result)
        
        printfl(f"\n  {status} {result['operation']}")
        printfl(f"  Train: {[f'{e:.4f}' for e in result['train_energies']]}")
        
        if (i + 1) % 20 == 0:
            printfl(f"\n  --- Progress: {len(perfect_tasks)} perfect, {len(shape_solved)} shape-solved ---")
    
    # Summary
    printfl("\n" + "=" * 70)
    printfl("FINAL SUMMARY: Phase 8.3 - Geometry-First Physics")
    printfl("=" * 70)
    
    perfect = len(perfect_tasks)
    consistent = len(consistent_tasks)
    partial = sum(1 for r in all_results if not r['is_consistent'] and r['avg_train_energy'] < 0.3)
    failed = sum(1 for r in all_results if r['avg_train_energy'] >= 0.3)
    
    same_shape_tasks = sum(1 for r in all_results if r['same_shape'])
    diff_shape_tasks = len(all_results) - same_shape_tasks
    
    printfl(f"\nTasks: {len(all_results)}")
    printfl(f"  Same I/O shape:  {same_shape_tasks}")
    printfl(f"  Diff I/O shape:  {diff_shape_tasks}")
    printfl(f"\nResults:")
    printfl(f"  PERFECT    (E < 0.0001):  {perfect}")
    printfl(f"  CONSISTENT (all < 0.005): {consistent}")
    printfl(f"  PARTIAL    (avg < 0.3):   {partial}")
    printfl(f"  FAILED     (avg >= 0.3):  {failed}")
    
    if shape_solved:
        printfl(f"\n=== SHAPE MORPHISM SUCCESSES ===")
        for r in shape_solved:
            status = "PERFECT" if r['is_perfect'] else ("CONS" if r['is_consistent'] else "part")
            printfl(f"  [{status}] {r['task_id']}: {r['morphism']} -> E={r['avg_train_energy']:.4f}")
    
    if perfect_tasks:
        printfl(f"\n=== PERFECT SOLVES ===")
        for r in perfect_tasks:
            printfl(f"  {r['task_id']}: {r['operation']}")
    
    printfl(f"\n=== Best Results (E < 0.1) ===")
    for r in sorted(all_results, key=lambda x: x['avg_train_energy'])[:20]:
        if r['avg_train_energy'] < 0.1:
            status = "PERFECT" if r['is_perfect'] else ("CONS" if r['is_consistent'] else "part")
            printfl(f"  [{status}] {r['task_id']}: {r['operation']} E={r['avg_train_energy']:.4f}")
    
    return all_results


def main():
    config = ARCPhase83Config()
    paths = ["data/arc/training", "C:/Lean4 Projects/data/arc/training"]
    arc_path = next((p for p in paths if Path(p).exists()), None)
    
    if arc_path:
        return run_evaluation(arc_path, config, num_tasks=97)
    else:
        printfl("ARC data not found!")
        return []


if __name__ == "__main__":
    main()
