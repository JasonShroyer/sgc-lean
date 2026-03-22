# Perception-First Architecture: The Missing Layer

## The Fundamental Error

Our current algorithm operates **bottom-up**:
```
Pixels → Enumerate Predicates → Search for Operations → Hope to find structure
```

Humans operate **top-down**:
```
Perceive Global Structure → Identify Symmetry Group → Derive Pixel Transformation
```

This is not a bug to fix. It is an **architectural gap**.

## The SGC Interpretation

From Spectral Geometry of Consolidation theory:

1. **The gauge group G represents the symmetries of the problem**
   - Puzzle 1b60fb0c: G = Z₂ (reflection)
   - Puzzle 0dfd9992: G = Z_n × Z_m (translation/tiling)
   - Many ARC puzzles: G = D₄ (dihedral group of square)

2. **The connection A tells us how information parallel-transports**
   - Within a symmetric region, A is flat (zero curvature)
   - Across symmetry boundaries, A encodes the group action

3. **The curvature F = dA + A∧A measures where symmetry breaks**
   - High curvature = boundary between symmetric regions
   - Zero curvature = within a coherent symmetric domain

**Key Insight:** We're searching in predicate-space when we should first identify
the symmetry group, THEN use it to guide predicate construction.

## Why Predicate Search Fails on Symmetric Tasks

Consider puzzle 0dfd9992 (tiled pattern with holes):
- The correct answer at position (i,j) depends on (i mod p, j mod q) where p,q are tile periods
- This is a **translation symmetry** with group G = Z_p × Z_q

Our current approach:
1. Tries predicates like `is_adjacent_to_color_5`
2. These predicates are **position-dependent** (not invariant under translation)
3. Sheaf energy is high because they don't form global sections
4. We waste compute trying every color at every position

What we should do:
1. **Detect the translation group** via autocorrelation/Fourier
2. The period (p,q) is found by spectral analysis
3. Construct the predicate: `fill(color_at[i mod p, j mod q])`
4. This predicate is **G-invariant** by construction

## The Perception Layer We're Missing

### Layer 0: Spectral Perception (NEW)

Before any predicate search, we need a perception layer that detects:

1. **Translation Symmetry** (Fourier/Autocorrelation)
   - Input: Grid
   - Output: Period vectors (p_x, p_y) and confidence
   - If detected: Use `tile_fill(period, template)` operation

2. **Reflection Symmetry** (Cross-correlation with flips)
   - Input: Grid
   - Output: Axis of symmetry (horizontal, vertical, diagonal)
   - If detected: Use `mirror(axis, source_region)` operation

3. **Rotation Symmetry** (Angular autocorrelation)
   - Input: Grid
   - Output: Rotation center and order (90°, 180°, etc.)
   - If detected: Use `rotate_fill(center, angle)` operation

4. **Scale Symmetry** (Multi-scale correlation)
   - Input: Grid
   - Output: Scaling factor and anchor
   - If detected: Use `scale(factor, region)` operation

### Implementation Sketch

```python
class SymmetryPerception:
    """Spectral perception layer - detects global symmetries FIRST."""
    
    def detect_symmetries(self, grid: np.ndarray) -> List[Symmetry]:
        symmetries = []
        
        # 1. Translation symmetry via 2D autocorrelation
        autocorr = self._autocorrelation_2d(grid)
        periods = self._find_peaks(autocorr)  # Non-origin peaks = periods
        if periods:
            symmetries.append(TranslationSymmetry(periods))
        
        # 2. Reflection symmetry via cross-correlation with flips
        for axis in ['horizontal', 'vertical', 'diagonal']:
            flipped = self._flip(grid, axis)
            corr = self._cross_correlation(grid, flipped)
            if self._has_strong_peak(corr):
                symmetries.append(ReflectionSymmetry(axis, corr.argmax()))
        
        # 3. Rotation symmetry via angular correlation
        for angle in [90, 180, 270]:
            rotated = np.rot90(grid, k=angle//90)
            if self._grids_match(grid, rotated):
                symmetries.append(RotationSymmetry(angle))
        
        return symmetries
    
    def _autocorrelation_2d(self, grid):
        """FFT-based autocorrelation detects translation periods."""
        f = np.fft.fft2(grid)
        return np.fft.ifft2(f * np.conj(f)).real
```

## The Architectural Change

### Current Architecture (Bottom-Up)
```
Input Grid
    ↓
Pixel-level predicates (is_color_X, is_adjacent_Y, ...)
    ↓
Operation enumeration (recolor, fill, ...)
    ↓
Beam search over operation sequences
    ↓
Hope to find the transformation
```

### Proposed Architecture (Top-Down, Perception-First)
```
Input Grid
    ↓
┌─────────────────────────────────────┐
│  SPECTRAL PERCEPTION LAYER          │
│  - Detect translation symmetry      │
│  - Detect reflection symmetry       │
│  - Detect rotation symmetry         │
│  - Detect object repetitions        │
│  OUTPUT: Symmetry group G, params   │
└─────────────────────────────────────┘
    ↓
If G detected with high confidence:
    → Use G-equivariant operations directly
    → No predicate search needed
    
Else (no clear symmetry):
    ↓
┌─────────────────────────────────────┐
│  EXISTING PREDICATE SEARCH          │
│  (with G-invariance regularization) │
└─────────────────────────────────────┘
```

## Connection to SGC Theory

This architecture is **mathematically necessary** from the gauge theory perspective:

1. **Principal Bundle Structure**
   - The base space M is the space of ARC tasks
   - The fiber G is the symmetry group
   - Different tasks may have different structure groups

2. **The Perception Layer = Bundle Identification**
   - Detecting the symmetry group = identifying which bundle we're in
   - This must happen BEFORE searching for sections (predicates)

3. **G-Equivariant Predicates**
   - Once G is known, predicates must be G-invariant to form global sections
   - This is why position-dependent predicates have high sheaf energy

4. **The Gauge Connection**
   - When we transport a predicate across a symmetric region, it must transform covariantly
   - The connection tells us HOW it transforms
   - Flat connection (zero curvature) = the predicate is truly G-invariant

## Concrete Example: Puzzle 1b60fb0c

Human perception:
1. "I see a shape with a vertical edge"
2. "The output adds a mirror reflection"
3. "The reflection axis is at the left edge of the 1s"

Spectral perception should detect:
```python
symmetry = ReflectionSymmetry(
    axis='vertical',
    axis_position=3,  # x-coordinate of the reflection axis
    confidence=0.95
)
```

The solver then applies:
```python
operation = MirrorFill(
    source_color=1,
    target_color=2,
    axis=symmetry.axis_position,
    direction='left'
)
```

No predicate enumeration needed. The symmetry tells us exactly what to do.

## Implementation Priority

1. **Immediate**: Add `detect_translation_symmetry()` using FFT
   - This alone would solve puzzle 0dfd9992 and similar tiling tasks
   
2. **Next**: Add `detect_reflection_symmetry()` 
   - Solves puzzle 1b60fb0c class
   
3. **Then**: Add `detect_rotation_symmetry()`
   - Handles D₄ tasks

4. **Finally**: Integrate with existing solver as a bypass layer
   - If symmetry detected → use direct operation
   - If not → fall back to predicate search

## The Deeper Principle

**Emergence requires the right level of abstraction.**

Our current algorithm operates at the wrong level:
- Pixels are too fine-grained
- Predicates over pixels miss the forest for the trees

Intelligence emerges when the algorithm can perceive at multiple scales:
- Pixel level (existing)
- Object level (partially exists via connected components)
- **Symmetry level (MISSING)** ← This is the gap
- Task-family level (partially exists via cross-task transfer)

The symmetry level is where humans immediately perceive structure.
Adding this layer is not an optimization - it's a **necessary condition for emergent intelligence**.

## Formal Statement (for Lean 4 formalization)

**Theorem (Perception Necessity):**
Let M be the moduli space of pattern-completion tasks. If the structure group G_m varies 
across tasks m ∈ M, then any algorithm that does not first identify G_m before searching 
for G_m-equivariant solutions will have complexity O(|G_max| · |predicate_space|) instead 
of O(|G_m| · log|predicate_space|) where G_m is the actual structure group.

**Proof sketch:** Without knowing G_m, we must search over all possible groups and all 
predicates. With G_m known, we only search over G_m-invariant predicates, which is an 
exponentially smaller space.

This is why humans solve these puzzles instantly - we perceive G first.
