"""
Symmetry Perception Layer

The missing layer in our architecture. This module detects global symmetries
BEFORE predicate enumeration, enabling direct application of group-equivariant
operations.

From SGC Theory:
- The gauge group G represents the symmetries of the problem
- Detecting G first reduces search complexity from O(|predicates|) to O(|G-invariant predicates|)
- This is why humans solve symmetric puzzles instantly - we perceive G first

Supported Symmetries:
1. Translation (tiling/periodicity) - via 2D autocorrelation
2. Reflection (mirror) - via cross-correlation with flips
3. Rotation (90°, 180°, 270°) - via rotation correlation
4. Scale/Dilation - via multi-scale correlation
"""

import numpy as np
from scipy import ndimage, signal
from scipy.fft import fft2, ifft2
from dataclasses import dataclass
from typing import List, Tuple, Optional, Dict, Any
from enum import Enum
import warnings


class SymmetryType(Enum):
    TRANSLATION = "translation"
    REFLECTION = "reflection"
    ROTATION = "rotation"
    SCALE = "scale"
    POINT = "point"  # Central point symmetry


@dataclass
class Symmetry:
    """Base class for detected symmetries."""
    type: SymmetryType
    confidence: float
    params: Dict[str, Any]
    
    def describe(self) -> str:
        return f"{self.type.value} (conf={self.confidence:.2f})"


@dataclass
class TranslationSymmetry(Symmetry):
    """Translation/tiling symmetry with periods (px, py)."""
    def __init__(self, period_x: int, period_y: int, confidence: float):
        super().__init__(
            type=SymmetryType.TRANSLATION,
            confidence=confidence,
            params={'period_x': period_x, 'period_y': period_y}
        )
        self.period_x = period_x
        self.period_y = period_y
    
    def describe(self) -> str:
        return f"Translation period=({self.period_x}, {self.period_y}) conf={self.confidence:.2f}"


@dataclass  
class ReflectionSymmetry(Symmetry):
    """Reflection symmetry across an axis."""
    def __init__(self, axis: str, position: float, confidence: float):
        super().__init__(
            type=SymmetryType.REFLECTION,
            confidence=confidence,
            params={'axis': axis, 'position': position}
        )
        self.axis = axis  # 'horizontal', 'vertical', 'diagonal_main', 'diagonal_anti'
        self.position = position  # Position of axis (row for h, col for v)
    
    def describe(self) -> str:
        return f"Reflection axis={self.axis} pos={self.position:.1f} conf={self.confidence:.2f}"


@dataclass
class RotationSymmetry(Symmetry):
    """Rotation symmetry around a center point."""
    def __init__(self, order: int, center: Tuple[float, float], confidence: float):
        super().__init__(
            type=SymmetryType.ROTATION,
            confidence=confidence,
            params={'order': order, 'center': center}
        )
        self.order = order  # 2 for 180°, 4 for 90°
        self.center = center
    
    def describe(self) -> str:
        return f"Rotation order={self.order} center={self.center} conf={self.confidence:.2f}"


class SymmetryPerception:
    """
    Spectral perception layer that detects global symmetries FIRST.
    
    This is the missing layer in our architecture. By detecting the symmetry
    group G before searching for predicates, we can:
    1. Use G-equivariant operations directly (no search needed)
    2. Constrain predicate search to G-invariant predicates only
    3. Reduce complexity from O(|predicates|) to O(|G-invariant predicates|)
    """
    
    def __init__(self, min_confidence: float = 0.7):
        self.min_confidence = min_confidence
    
    def perceive(self, grid: np.ndarray) -> List[Symmetry]:
        """
        Main entry point: detect all symmetries in the grid.
        
        Returns symmetries sorted by confidence (highest first).
        """
        symmetries = []
        
        # Convert to float for FFT operations
        grid_float = grid.astype(float)
        
        # 1. Detect translation symmetry (tiling)
        trans = self._detect_translation(grid_float)
        if trans and trans.confidence >= self.min_confidence:
            symmetries.append(trans)
        
        # 2. Detect reflection symmetries
        for refl in self._detect_reflections(grid_float):
            if refl.confidence >= self.min_confidence:
                symmetries.append(refl)
        
        # 3. Detect rotation symmetries
        for rot in self._detect_rotations(grid_float):
            if rot.confidence >= self.min_confidence:
                symmetries.append(rot)
        
        # Sort by confidence
        symmetries.sort(key=lambda s: s.confidence, reverse=True)
        
        return symmetries
    
    def _detect_translation(self, grid: np.ndarray) -> Optional[TranslationSymmetry]:
        """
        Detect translation/tiling symmetry using 2D autocorrelation.
        
        The autocorrelation of a periodic signal has peaks at the period.
        We use FFT for efficient computation: autocorr = IFFT(|FFT(x)|²)
        """
        h, w = grid.shape
        if h < 4 or w < 4:
            return None
        
        # Compute 2D autocorrelation via FFT
        f = fft2(grid)
        autocorr = np.real(ifft2(f * np.conj(f)))
        
        # Normalize
        autocorr = autocorr / autocorr[0, 0] if autocorr[0, 0] > 0 else autocorr
        
        # Find peaks (excluding origin)
        # We look for the first significant peak in each direction
        period_x, conf_x = self._find_period_1d(autocorr[0, 1:w//2+1])
        period_y, conf_y = self._find_period_1d(autocorr[1:h//2+1, 0])
        
        if period_x is None and period_y is None:
            return None
        
        # Use found periods, default to grid size if not found
        px = period_x + 1 if period_x is not None else w
        py = period_y + 1 if period_y is not None else h
        
        confidence = max(conf_x or 0, conf_y or 0)
        
        if confidence > 0.5:
            return TranslationSymmetry(px, py, confidence)
        return None
    
    def _find_period_1d(self, autocorr_1d: np.ndarray) -> Tuple[Optional[int], Optional[float]]:
        """Find the dominant period in a 1D autocorrelation signal."""
        if len(autocorr_1d) < 2:
            return None, None
        
        # Find local maxima
        peaks = []
        for i in range(1, len(autocorr_1d) - 1):
            if autocorr_1d[i] > autocorr_1d[i-1] and autocorr_1d[i] > autocorr_1d[i+1]:
                peaks.append((i, autocorr_1d[i]))
        
        if not peaks:
            return None, None
        
        # Return the peak with highest correlation
        best_peak = max(peaks, key=lambda x: x[1])
        period, correlation = best_peak
        
        # Confidence based on correlation strength
        confidence = min(1.0, correlation)
        
        return period, confidence
    
    def _detect_reflections(self, grid: np.ndarray) -> List[ReflectionSymmetry]:
        """
        Detect reflection symmetries by comparing grid with its flipped versions.
        """
        reflections = []
        h, w = grid.shape
        
        # Vertical reflection (left-right flip)
        flipped_lr = np.fliplr(grid)
        for offset in range(-w//4, w//4 + 1):
            shifted = self._shift_horizontal(flipped_lr, offset)
            similarity = self._compute_similarity(grid, shifted)
            if similarity > 0.7:
                axis_pos = w / 2 + offset / 2
                reflections.append(ReflectionSymmetry('vertical', axis_pos, similarity))
                break  # Take best match
        
        # Horizontal reflection (top-bottom flip)
        flipped_ud = np.flipud(grid)
        for offset in range(-h//4, h//4 + 1):
            shifted = self._shift_vertical(flipped_ud, offset)
            similarity = self._compute_similarity(grid, shifted)
            if similarity > 0.7:
                axis_pos = h / 2 + offset / 2
                reflections.append(ReflectionSymmetry('horizontal', axis_pos, similarity))
                break
        
        return reflections
    
    def _detect_rotations(self, grid: np.ndarray) -> List[RotationSymmetry]:
        """
        Detect rotation symmetries by comparing grid with rotated versions.
        """
        rotations = []
        h, w = grid.shape
        
        if h != w:
            # Non-square grids can only have 180° rotation symmetry
            rotated_180 = np.rot90(grid, 2)
            similarity = self._compute_similarity(grid, rotated_180)
            if similarity > 0.8:
                center = (h / 2, w / 2)
                rotations.append(RotationSymmetry(2, center, similarity))
        else:
            # Square grids: check 90°, 180°, 270°
            center = (h / 2, w / 2)
            
            # 180° rotation
            rotated_180 = np.rot90(grid, 2)
            sim_180 = self._compute_similarity(grid, rotated_180)
            
            # 90° rotation (implies 180° and 270°)
            rotated_90 = np.rot90(grid, 1)
            sim_90 = self._compute_similarity(grid, rotated_90)
            
            if sim_90 > 0.8:
                rotations.append(RotationSymmetry(4, center, sim_90))
            elif sim_180 > 0.8:
                rotations.append(RotationSymmetry(2, center, sim_180))
        
        return rotations
    
    def _shift_horizontal(self, grid: np.ndarray, offset: int) -> np.ndarray:
        """Shift grid horizontally with zero padding."""
        if offset == 0:
            return grid
        result = np.zeros_like(grid)
        if offset > 0:
            result[:, offset:] = grid[:, :-offset]
        else:
            result[:, :offset] = grid[:, -offset:]
        return result
    
    def _shift_vertical(self, grid: np.ndarray, offset: int) -> np.ndarray:
        """Shift grid vertically with zero padding."""
        if offset == 0:
            return grid
        result = np.zeros_like(grid)
        if offset > 0:
            result[offset:, :] = grid[:-offset, :]
        else:
            result[:offset, :] = grid[-offset:, :]
        return result
    
    def _compute_similarity(self, grid1: np.ndarray, grid2: np.ndarray) -> float:
        """Compute normalized similarity between two grids."""
        if grid1.shape != grid2.shape:
            return 0.0
        
        # Mask out zeros (background) for more meaningful comparison
        mask = (grid1 != 0) | (grid2 != 0)
        if not mask.any():
            return 1.0  # Both all zeros
        
        matches = (grid1 == grid2) & mask
        return matches.sum() / mask.sum()


class SymmetryOperations:
    """
    Operations that exploit detected symmetries directly.
    
    When a symmetry is detected with high confidence, we can apply
    the corresponding operation WITHOUT predicate search.
    """
    
    @staticmethod
    def apply_translation_fill(grid: np.ndarray, symmetry: TranslationSymmetry) -> np.ndarray:
        """
        Fill holes in a grid using translation symmetry.
        
        For each zero pixel, find its value from the tile template.
        """
        h, w = grid.shape
        px, py = symmetry.period_x, symmetry.period_y
        
        # Extract the template tile (non-zero region of first period)
        template = np.zeros((py, px), dtype=grid.dtype)
        
        # Build template from all instances of the tile
        counts = np.zeros((py, px), dtype=int)
        for i in range(h):
            for j in range(w):
                if grid[i, j] != 0:
                    ti, tj = i % py, j % px
                    if template[ti, tj] == 0:
                        template[ti, tj] = grid[i, j]
                        counts[ti, tj] += 1
        
        # Fill the grid using the template
        result = grid.copy()
        for i in range(h):
            for j in range(w):
                if result[i, j] == 0:
                    ti, tj = i % py, j % px
                    if template[ti, tj] != 0:
                        result[i, j] = template[ti, tj]
        
        return result
    
    @staticmethod
    def apply_reflection(grid: np.ndarray, symmetry: ReflectionSymmetry, 
                         source_color: int, target_color: int) -> np.ndarray:
        """
        Apply a reflection operation: mirror source_color region and fill with target_color.
        """
        h, w = grid.shape
        result = grid.copy()
        
        if symmetry.axis == 'vertical':
            axis_col = int(symmetry.position)
            # Find source region (right of axis)
            for i in range(h):
                for j in range(axis_col, w):
                    if grid[i, j] == source_color:
                        # Mirror position
                        mirror_j = 2 * axis_col - j - 1
                        if 0 <= mirror_j < w and result[i, mirror_j] == 0:
                            result[i, mirror_j] = target_color
        
        elif symmetry.axis == 'horizontal':
            axis_row = int(symmetry.position)
            for i in range(axis_row, h):
                for j in range(w):
                    if grid[i, j] == source_color:
                        mirror_i = 2 * axis_row - i - 1
                        if 0 <= mirror_i < h and result[mirror_i, j] == 0:
                            result[mirror_i, j] = target_color
        
        return result


def detect_reflection_transform(input_grid: np.ndarray, output_grid: np.ndarray) -> Optional[Dict]:
    """
    Detect if the transformation is creating a reflection of input content.
    
    Human perception: "The output adds a mirror of the shape"
    
    Key insight: The reflection axis is typically at the EDGE of the source shape,
    not in the center of the grid.
    """
    h, w = input_grid.shape
    if output_grid.shape != (h, w):
        return None
    
    # Find what was added (output - input)
    added_mask = (output_grid != 0) & (input_grid == 0)
    if not added_mask.any():
        return None
    
    added_color = output_grid[added_mask][0] if added_mask.any() else 0
    
    # Find the source shape (what exists in input)
    source_mask = (input_grid != 0)
    source_colors = set(input_grid[source_mask])
    
    if not source_colors:
        return None
    
    source_color = max(source_colors, key=lambda c: (input_grid == c).sum())
    source_shape = (input_grid == source_color)
    
    # Find bounding box of source shape
    rows_with_source = np.where(source_shape.any(axis=1))[0]
    cols_with_source = np.where(source_shape.any(axis=0))[0]
    
    if len(cols_with_source) == 0 or len(rows_with_source) == 0:
        return None
    
    min_col, max_col = cols_with_source.min(), cols_with_source.max()
    min_row, max_row = rows_with_source.min(), rows_with_source.max()
    
    best_match = None
    best_confidence = 0
    
    # Vertical reflection - axis at LEFT edge of source (reflect to the left)
    axis_col = min_col
    reflected = np.zeros_like(source_shape)
    for i in range(h):
        for j in range(axis_col, w):
            if source_shape[i, j]:
                mirror_j = 2 * axis_col - j - 1
                if 0 <= mirror_j < w:
                    reflected[i, mirror_j] = True
    
    if reflected.any():
        overlap = (reflected & added_mask).sum()
        union = (reflected | added_mask).sum()
        confidence = overlap / union if union > 0 else 0
        
        if confidence > best_confidence:
            best_confidence = confidence
            best_match = {
                'type': 'reflection',
                'axis': 'vertical',
                'axis_position': axis_col,
                'direction': 'left',
                'source_color': int(source_color),
                'target_color': int(added_color),
                'confidence': confidence
            }
    
    # Vertical reflection - axis at RIGHT edge of source (reflect to the right)
    axis_col = max_col + 1
    reflected = np.zeros_like(source_shape)
    for i in range(h):
        for j in range(0, axis_col):
            if source_shape[i, j]:
                mirror_j = 2 * axis_col - j - 1
                if 0 <= mirror_j < w:
                    reflected[i, mirror_j] = True
    
    if reflected.any():
        overlap = (reflected & added_mask).sum()
        union = (reflected | added_mask).sum()
        confidence = overlap / union if union > 0 else 0
        
        if confidence > best_confidence:
            best_confidence = confidence
            best_match = {
                'type': 'reflection',
                'axis': 'vertical',
                'axis_position': axis_col,
                'direction': 'right',
                'source_color': int(source_color),
                'target_color': int(added_color),
                'confidence': confidence
            }
    
    # Horizontal reflection - axis at TOP edge
    axis_row = min_row
    reflected = np.zeros_like(source_shape)
    for i in range(axis_row, h):
        for j in range(w):
            if source_shape[i, j]:
                mirror_i = 2 * axis_row - i - 1
                if 0 <= mirror_i < h:
                    reflected[mirror_i, j] = True
    
    if reflected.any():
        overlap = (reflected & added_mask).sum()
        union = (reflected | added_mask).sum()
        confidence = overlap / union if union > 0 else 0
        
        if confidence > best_confidence:
            best_confidence = confidence
            best_match = {
                'type': 'reflection',
                'axis': 'horizontal',
                'axis_position': axis_row,
                'direction': 'up',
                'source_color': int(source_color),
                'target_color': int(added_color),
                'confidence': confidence
            }
    
    # Horizontal reflection - axis at BOTTOM edge
    axis_row = max_row + 1
    reflected = np.zeros_like(source_shape)
    for i in range(0, axis_row):
        for j in range(w):
            if source_shape[i, j]:
                mirror_i = 2 * axis_row - i - 1
                if 0 <= mirror_i < h:
                    reflected[mirror_i, j] = True
    
    if reflected.any():
        overlap = (reflected & added_mask).sum()
        union = (reflected | added_mask).sum()
        confidence = overlap / union if union > 0 else 0
        
        if confidence > best_confidence:
            best_confidence = confidence
            best_match = {
                'type': 'reflection',
                'axis': 'horizontal',
                'axis_position': axis_row,
                'direction': 'down',
                'source_color': int(source_color),
                'target_color': int(added_color),
                'confidence': confidence
            }
    
    return best_match if best_confidence > 0.3 else None


def detect_symmetry_completion(input_grid: np.ndarray, output_grid: np.ndarray) -> Optional[Dict]:
    """
    Detect if the transformation is COMPLETING a shape's symmetry.
    
    Human perception: "The shape is almost symmetric, and we add what's missing"
    
    This is different from reflection - we only add the parts needed to make
    the shape symmetric, not reflect the entire shape.
    """
    h, w = input_grid.shape
    if output_grid.shape != (h, w):
        return None
    
    # Find source shape
    source_colors = set(input_grid[input_grid != 0])
    if not source_colors:
        return None
    
    source_color = max(source_colors, key=lambda c: (input_grid == c).sum())
    source = (input_grid == source_color)
    
    # Find what was added
    added_mask = (output_grid != 0) & (input_grid == 0)
    if not added_mask.any():
        return None
    
    added_color = output_grid[added_mask][0]
    
    # Find bounding box of source
    rows = np.where(source.any(axis=1))[0]
    cols = np.where(source.any(axis=0))[0]
    if len(rows) == 0 or len(cols) == 0:
        return None
    
    min_row, max_row = rows.min(), rows.max()
    min_col, max_col = cols.min(), cols.max()
    
    # Try to find a symmetry axis within the shape
    best_match = None
    best_confidence = 0
    
    # Try each possible vertical axis within the shape's bounding box
    for axis_col in range(min_col, max_col + 1):
        # For this axis, compute what a symmetric completion would look like
        completion = np.zeros_like(source)
        
        for i in range(h):
            for j in range(w):
                if source[i, j]:
                    # This pixel exists - check if its mirror exists
                    mirror_j = 2 * axis_col - j
                    if 0 <= mirror_j < w and not source[i, mirror_j]:
                        # Mirror pixel is missing - it should be added
                        completion[i, mirror_j] = True
        
        if completion.any():
            # Check how well this matches the added region
            overlap = (completion & added_mask).sum()
            union = (completion | added_mask).sum()
            confidence = overlap / union if union > 0 else 0
            
            if confidence > best_confidence:
                best_confidence = confidence
                best_match = {
                    'type': 'symmetry_completion',
                    'axis': 'vertical',
                    'axis_position': axis_col,
                    'source_color': int(source_color),
                    'target_color': int(added_color),
                    'confidence': confidence
                }
    
    # Try horizontal axes
    for axis_row in range(min_row, max_row + 1):
        completion = np.zeros_like(source)
        
        for i in range(h):
            for j in range(w):
                if source[i, j]:
                    mirror_i = 2 * axis_row - i
                    if 0 <= mirror_i < h and not source[mirror_i, j]:
                        completion[mirror_i, j] = True
        
        if completion.any():
            overlap = (completion & added_mask).sum()
            union = (completion | added_mask).sum()
            confidence = overlap / union if union > 0 else 0
            
            if confidence > best_confidence:
                best_confidence = confidence
                best_match = {
                    'type': 'symmetry_completion',
                    'axis': 'horizontal',
                    'axis_position': axis_row,
                    'source_color': int(source_color),
                    'target_color': int(added_color),
                    'confidence': confidence
                }
    
    return best_match if best_confidence > 0.5 else None


def detect_protrusion_reflection(input_grid: np.ndarray, output_grid: np.ndarray) -> Optional[Dict]:
    """
    Detect if transformation reflects only the PROTRUSIONS of a shape.
    
    Human perception: "The shape has a main body and protrusions. Mirror the protrusions."
    
    This is object-level perception - we decompose the shape into:
    1. Main vertical/horizontal spine
    2. Protrusions that extend beyond the spine
    3. The transformation mirrors only the protrusions
    """
    h, w = input_grid.shape
    if output_grid.shape != (h, w):
        return None
    
    # Find source shape
    source_colors = set(input_grid[input_grid != 0])
    if not source_colors:
        return None
    
    source_color = max(source_colors, key=lambda c: (input_grid == c).sum())
    source = (input_grid == source_color)
    
    # Find what was added
    added_mask = (output_grid != 0) & (input_grid == 0)
    if not added_mask.any():
        return None
    
    added_color = output_grid[added_mask][0]
    
    # Analyze shape structure - find the "spine" (most common extent per row/col)
    rows_extent = []
    for i in range(h):
        cols = np.where(source[i])[0]
        if len(cols) > 0:
            rows_extent.append((i, cols.min(), cols.max()))
    
    if len(rows_extent) < 3:
        return None
    
    # Find median column extent (the "spine")
    min_cols = [r[1] for r in rows_extent]
    max_cols = [r[2] for r in rows_extent]
    spine_min = int(np.median(min_cols))
    spine_max = int(np.median(max_cols))
    
    # Find protrusion rows (rows that extend beyond the spine)
    protrusion_rows = []
    for i, min_c, max_c in rows_extent:
        if max_c > spine_max:  # Protrudes right
            protrusion_rows.append((i, 'right', max_c - spine_max))
        elif min_c < spine_min:  # Protrudes left
            protrusion_rows.append((i, 'left', spine_min - min_c))
    
    if not protrusion_rows:
        return None
    
    # Check if the transformation mirrors the protrusions
    # Compute expected reflection for protrusion rows only
    best_match = None
    best_confidence = 0
    
    # Try reflecting right protrusions to the left
    right_protrusion_rows = [r[0] for r in protrusion_rows if r[1] == 'right']
    if right_protrusion_rows:
        # Use spine_min as the reflection axis
        axis = spine_min
        completion = np.zeros_like(source)
        
        for i in right_protrusion_rows:
            for j in range(w):
                if source[i, j]:
                    mirror_j = 2 * axis - j - 1
                    if 0 <= mirror_j < w and not source[i, mirror_j]:
                        completion[i, mirror_j] = True
        
        if completion.any():
            overlap = (completion & added_mask).sum()
            union = (completion | added_mask).sum()
            confidence = overlap / union if union > 0 else 0
            
            if confidence > best_confidence:
                best_confidence = confidence
                best_match = {
                    'type': 'protrusion_reflection',
                    'direction': 'right_to_left',
                    'axis': axis,
                    'protrusion_rows': right_protrusion_rows,
                    'source_color': int(source_color),
                    'target_color': int(added_color),
                    'confidence': confidence
                }
    
    # Try reflecting left protrusions to the right
    left_protrusion_rows = [r[0] for r in protrusion_rows if r[1] == 'left']
    if left_protrusion_rows:
        axis = spine_max
        completion = np.zeros_like(source)
        
        for i in left_protrusion_rows:
            for j in range(w):
                if source[i, j]:
                    mirror_j = 2 * axis - j + 1
                    if 0 <= mirror_j < w and not source[i, mirror_j]:
                        completion[i, mirror_j] = True
        
        if completion.any():
            overlap = (completion & added_mask).sum()
            union = (completion | added_mask).sum()
            confidence = overlap / union if union > 0 else 0
            
            if confidence > best_confidence:
                best_confidence = confidence
                best_match = {
                    'type': 'protrusion_reflection',
                    'direction': 'left_to_right',
                    'axis': axis,
                    'protrusion_rows': left_protrusion_rows,
                    'source_color': int(source_color),
                    'target_color': int(added_color),
                    'confidence': confidence
                }
    
    return best_match if best_confidence > 0.5 else None


def analyze_task_symmetry(input_grid: np.ndarray, output_grid: np.ndarray, 
                          verbose: bool = True) -> Dict[str, Any]:
    """
    Analyze an ARC task to detect what symmetry operations are being used.
    
    This is the diagnostic function that reveals what humans perceive instantly.
    
    Two modes of perception:
    1. Input has symmetry → use it to fill/complete
    2. Transformation creates symmetry → detect the reflection/rotation being applied
    """
    perception = SymmetryPerception(min_confidence=0.5)
    
    # Detect symmetries in input
    input_symmetries = perception.perceive(input_grid)
    
    # Detect symmetries in output
    output_symmetries = perception.perceive(output_grid)
    
    # Compute the difference (what changed)
    diff = (output_grid != input_grid).astype(int)
    diff_symmetries = perception.perceive(diff.astype(float))
    
    # Analyze the transformation
    analysis = {
        'input_symmetries': [s.describe() for s in input_symmetries],
        'output_symmetries': [s.describe() for s in output_symmetries],
        'diff_symmetries': [s.describe() for s in diff_symmetries],
        'transformation_type': 'unknown',
        'confidence': 0.0,
        'operation': None
    }
    
    # MODE 1: Input has translation symmetry → tile fill
    if input_symmetries:
        main_sym = input_symmetries[0]
        
        if main_sym.type == SymmetryType.TRANSLATION:
            filled = SymmetryOperations.apply_translation_fill(input_grid, main_sym)
            match = np.mean(filled == output_grid)
            if match > 0.9:
                analysis['transformation_type'] = 'tile_fill'
                analysis['confidence'] = match
                analysis['operation'] = {
                    'type': 'tile_fill',
                    'period_x': main_sym.period_x,
                    'period_y': main_sym.period_y
                }
    
    # MODE 2: Transformation creates reflection
    if analysis['transformation_type'] == 'unknown':
        reflection = detect_reflection_transform(input_grid, output_grid)
        if reflection and reflection['confidence'] > analysis['confidence']:
            analysis['transformation_type'] = 'reflection_create'
            analysis['confidence'] = reflection['confidence']
            analysis['operation'] = reflection
    
    # MODE 3: Symmetry completion (add what's missing to make shape symmetric)
    if analysis['transformation_type'] == 'unknown' or analysis['confidence'] < 0.7:
        completion = detect_symmetry_completion(input_grid, output_grid)
        if completion and completion['confidence'] > analysis['confidence']:
            analysis['transformation_type'] = 'symmetry_completion'
            analysis['confidence'] = completion['confidence']
            analysis['operation'] = completion
    
    # MODE 4: Protrusion reflection (object-level: reflect only the protrusions)
    if analysis['transformation_type'] == 'unknown' or analysis['confidence'] < 0.7:
        protrusion = detect_protrusion_reflection(input_grid, output_grid)
        if protrusion and protrusion['confidence'] > analysis['confidence']:
            analysis['transformation_type'] = 'protrusion_reflection'
            analysis['confidence'] = protrusion['confidence']
            analysis['operation'] = protrusion
    
    if verbose:
        print("=" * 60)
        print("SYMMETRY PERCEPTION ANALYSIS")
        print("=" * 60)
        print(f"\nInput symmetries:")
        for s in input_symmetries[:3]:
            print(f"  - {s.describe()}")
        if not input_symmetries:
            print("  (none detected)")
        print(f"\nOutput symmetries:")
        for s in output_symmetries[:3]:
            print(f"  - {s.describe()}")
        if not output_symmetries:
            print("  (none detected)")
        print(f"\nDiff symmetries:")
        for s in diff_symmetries[:3]:
            print(f"  - {s.describe()}")
        if not diff_symmetries:
            print("  (none detected)")
        print(f"\n>>> INFERRED TRANSFORMATION: {analysis['transformation_type']}")
        print(f">>> CONFIDENCE: {analysis['confidence']:.2f}")
        if analysis['operation']:
            print(f">>> OPERATION: {analysis['operation']}")
        print("=" * 60)
    
    return analysis


# Test with puzzle 0dfd9992 (the tiled pattern)
if __name__ == "__main__":
    import json
    from pathlib import Path
    
    print("Testing Symmetry Perception Layer")
    print("=" * 60)
    
    # Load a tiled puzzle
    arc_dir = Path(__file__).parent.parent / "data" / "arc" / "training"
    
    test_tasks = ['0dfd9992', '1b60fb0c']  # Tiled and reflection tasks
    
    for task_id in test_tasks:
        task_file = arc_dir / f"{task_id}.json"
        if not task_file.exists():
            print(f"Task {task_id} not found")
            continue
        
        with open(task_file) as f:
            task = json.load(f)
        
        print(f"\n{'='*60}")
        print(f"TASK: {task_id}")
        print(f"{'='*60}")
        
        for i, example in enumerate(task.get('train', [])[:1]):
            input_grid = np.array(example['input'])
            output_grid = np.array(example['output'])
            
            print(f"\nExample {i+1}:")
            print(f"Input shape: {input_grid.shape}")
            
            # Run symmetry perception
            perception = SymmetryPerception(min_confidence=0.5)
            symmetries = perception.perceive(input_grid)
            
            print(f"\nDetected symmetries:")
            for sym in symmetries:
                print(f"  - {sym.describe()}")
            
            # Full analysis
            print("\n")
            analyze_task_symmetry(input_grid, output_grid, verbose=True)
