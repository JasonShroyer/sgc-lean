"""
ARC Tensor Logic Engine: Differentiable Predicate Discovery
============================================================

Implements Pedro Domingos's Tensor Logic (arXiv:2510.12269) adapted for
the SGC information gradient architecture.

CORE INSIGHT (Domingos 2024):
  Logical rules and Einstein summation are the same operation.
  A Datalog rule like Ancestor(x,z) <- Ancestor(x,y), Parent(y,z)
  is mathematically identical to: A_xz = H(Σ_y A_xy · P_yz)
  Logical databases are sparse Boolean tensors. Inference is contraction.

SGC CONNECTION:
  min_Π ε(Π, L) = min_{M,C} ||A - M·C·M^T|| = max_Π I(X_Π; X_∂Π)
  (SGC defect)      (Tucker decomposition)        (RSMI-RG)

SGFE v1.0: Tsallis double-transition temperature schedule for annealing.

  All three are the same optimization. This module implements it as
  differentiable tensor factorization:

  1. Encode grid as feature tensor F[e, r, c, f]
  2. Parameterize predicates: P[e,r,c,k] = σ(Σ_f F[e,r,c,f] · W[f,k] + b[k])
  3. Parameterize rules: Rule[k,i,o] = σ(V[k,i,o])
  4. Predicted output: Pred[e,r,c] = Σ_k P[e,r,c,k] · Σ_i Input_OH[e,r,c,i] · Rule[k,i,o]
  5. Loss = defect = ||Pred - Target||²
  6. Gradient descent on W, V, b → discovered predicates
  7. Threshold P > 0.5 → Boolean masks → new PredicateExpr atoms

THE TEMPERATURE KNOB:
  T=0 (Boolean): exact current system (step function)
  T>0 (continuous): differentiable, learnable (sigmoid with temperature)
  The learning loop: warm start (T=0) → relax (T>0) → gradient descent →
  anneal (T→0) → verify. This IS simulated annealing in predicate space.

References:
  [1] Domingos (2024). Tensor Logic: The Language of AI. arXiv:2510.12269
  [2] Koch-Janusz & Ringel (2018). RSMI-RG. Nature Physics 14, 578-582
  [3] Raju, Machta & Sethna (2018). Info loss under coarse graining.
  [4] Ellis et al. (2021). DreamCoder. PLDI 2021.
"""

import numpy as np
import torch
import torch.nn.functional as F

# SGFE: Tsallis double-transition temperature schedule + Hermite-Gaussian wavelets
try:
    from sgfe_engine import tsallis_temperature_schedule, hermite_gaussian_encode
    _HAS_SGFE_SCHEDULE = True
    _HAS_HERMITE_WAVELETS = True
except ImportError:
    _HAS_SGFE_SCHEDULE = False
    _HAS_HERMITE_WAVELETS = False
from scipy import ndimage
from scipy.ndimage import binary_fill_holes, label as ndlabel
from typing import List, Dict, Optional, Tuple, Any
from dataclasses import dataclass


# =============================================================================
# FEATURE EXTRACTION: Grid → Feature Tensor
# =============================================================================
# These features form the basis of the differentiable predicate space.
# Each feature is a known geometric/chromatic property of pixels.
# Gradient descent discovers which COMBINATIONS of these features
# form the optimal partition (coarse-graining) for each task.

# Feature name registry for interpretability
# SGFE v2.1: Extended with object-level features (indices 74+)
FEATURE_NAMES = (
    # 0-9: color channels (one-hot)
    [f'is_color_{i}' for i in range(10)] +
    # 10: foreground
    ['foreground'] +
    # 11-13: border features
    ['on_border', 'border_row', 'border_col'] +
    # 14: adjacent to any foreground (8-connected)
    ['adj_fg'] +
    # 15-23: adjacent to specific colors 1-9
    [f'adj_to_{i}' for i in range(1, 10)] +
    # 24: enclosed by foreground
    ['enclosed'] +
    # 25-33: same_row as color 1-9
    [f'same_row_{i}' for i in range(1, 10)] +
    # 34-42: same_col as color 1-9
    [f'same_col_{i}' for i in range(1, 10)] +
    # 43-44: row_position, col_position (normalized)
    ['row_pos', 'col_pos'] +
    # 45-53: between two pixels of color C horizontally
    [f'between_{i}_h' for i in range(1, 10)] +
    # 54-62: between two pixels of color C vertically
    [f'between_{i}_v' for i in range(1, 10)] +
    # 63: between any foreground horizontally
    ['between_fg_h'] +
    # 64: between any foreground vertically
    ['between_fg_v'] +
    # 65-73: cross pattern (same row AND same col as color C)
    [f'cross_{i}' for i in range(1, 10)] +
    # ---------- SGFE v2.1: Object-Level Features (74+) ----------
    # These features are topological invariants that survive translation,
    # enabling predicates like "the largest object" or "pixels in contained objects"
    # Theory: SceneGraph functor preserves structure under spatial transforms
    # 74-77: object size rank (largest=rank 0, 2nd=rank 1, etc.)
    [f'obj_size_rank_{i}' for i in range(4)] +
    # 78: containment depth (0=not contained, 1=contained in 1 obj, etc.)
    ['containment_depth'] +
    # 79-80: morphological features (SGFE v2.7: replaced local_row/col)
    ['morph_boundary', 'morph_skeleton'] +
    # 81: object aspect ratio (width/height, clamped to [0,1])
    ['obj_aspect_ratio'] +
    # 82: object relative area (object area / grid area)
    ['obj_relative_area'] +
    # 83: is in largest object
    ['in_largest_obj'] +
    # 84: is in smallest foreground object
    ['in_smallest_obj'] +
    # 85: number of adjacent objects (connectivity degree)
    ['obj_adjacency_count']
)


def encode_pixel_features(grid: np.ndarray, n_colors: int = 10) -> np.ndarray:
    """
    Extract per-pixel features from an ARC grid.

    Returns: [n_features, H, W] float32 tensor.

    These features reuse the geometric vocabulary from _compute_pixel_predicates
    but in continuous tensor form, enabling gradient-based learning.
    """
    H, W = grid.shape
    features = []
    kernel_8 = np.ones((3, 3), dtype=np.float32)
    kernel_8[1, 1] = 0

    # --- Color channels (one-hot) ---
    for c in range(n_colors):
        features.append((grid == c).astype(np.float32))

    # --- Foreground ---
    fg = (grid != 0).astype(np.float32)
    features.append(fg)

    # --- Border features ---
    border = np.zeros((H, W), dtype=np.float32)
    border[0, :] = 1; border[-1, :] = 1; border[:, 0] = 1; border[:, -1] = 1
    features.append(border)
    br = np.zeros((H, W), dtype=np.float32)
    br[0, :] = 1; br[-1, :] = 1
    features.append(br)
    bc = np.zeros((H, W), dtype=np.float32)
    bc[:, 0] = 1; bc[:, -1] = 1
    features.append(bc)

    # --- Adjacency to foreground ---
    adj_fg = ndimage.convolve(fg, kernel_8, mode='constant', cval=0)
    features.append((adj_fg > 0).astype(np.float32))

    # --- Adjacency to specific colors ---
    for c in range(1, n_colors):
        c_mask = (grid == c).astype(np.float32)
        adj_c = ndimage.convolve(c_mask, kernel_8, mode='constant', cval=0)
        features.append((adj_c > 0).astype(np.float32))

    # --- Enclosed by foreground ---
    fg_bool = grid != 0
    try:
        filled = binary_fill_holes(fg_bool)
        enclosed = (filled & ~fg_bool).astype(np.float32)
    except Exception:
        enclosed = np.zeros((H, W), dtype=np.float32)
    features.append(enclosed)

    # --- Same row/col as specific colors ---
    for c in range(1, n_colors):
        c_mask = (grid == c)
        row_has = c_mask.any(axis=1)  # [H]
        features.append(np.outer(row_has, np.ones(W)).astype(np.float32))
    for c in range(1, n_colors):
        c_mask = (grid == c)
        col_has = c_mask.any(axis=0)  # [W]
        features.append(np.outer(np.ones(H), col_has).astype(np.float32))

    # --- Normalized position ---
    row_pos = np.linspace(0, 1, H).reshape(-1, 1).repeat(W, axis=1).astype(np.float32)
    col_pos = np.linspace(0, 1, W).reshape(1, -1).repeat(H, axis=0).astype(np.float32)
    features.append(row_pos)
    features.append(col_pos)

    # --- Between-color features (horizontal & vertical) ---
    # between_C_h[r,c] = True if pixel is between two C-colored pixels in same row
    # between_C_v[r,c] = True if pixel is between two C-colored pixels in same col
    # These are the KEY predicates that solve most ARC fill tasks.
    for c in range(1, n_colors):
        c_mask = (grid == c)
        bh = np.zeros((H, W), dtype=np.float32)
        for r in range(H):
            cols = np.where(c_mask[r])[0]
            if len(cols) >= 2:
                bh[r, cols[0]:cols[-1]+1] = 1.0
                # Exclude the C pixels themselves
                bh[r, c_mask[r]] = 0.0
        features.append(bh)
    for c in range(1, n_colors):
        c_mask = (grid == c)
        bv = np.zeros((H, W), dtype=np.float32)
        for col in range(W):
            rows = np.where(c_mask[:, col])[0]
            if len(rows) >= 2:
                bv[rows[0]:rows[-1]+1, col] = 1.0
                bv[c_mask[:, col], col] = 0.0
        features.append(bv)

    # --- Between foreground (any non-zero) h/v ---
    fg_bool = grid != 0
    bfg_h = np.zeros((H, W), dtype=np.float32)
    for r in range(H):
        cols = np.where(fg_bool[r])[0]
        if len(cols) >= 2:
            bfg_h[r, cols[0]:cols[-1]+1] = 1.0
            bfg_h[r, fg_bool[r]] = 0.0
    features.append(bfg_h)
    bfg_v = np.zeros((H, W), dtype=np.float32)
    for col in range(W):
        rows = np.where(fg_bool[:, col])[0]
        if len(rows) >= 2:
            bfg_v[rows[0]:rows[-1]+1, col] = 1.0
            bfg_v[fg_bool[:, col], col] = 0.0
    features.append(bfg_v)

    # --- Cross patterns (same row AND same col as color C) ---
    for c in range(1, n_colors):
        c_mask = (grid == c)
        row_has = c_mask.any(axis=1)  # [H]
        col_has = c_mask.any(axis=0)  # [W]
        cross = (np.outer(row_has, np.ones(W)) *
                 np.outer(np.ones(H), col_has)).astype(np.float32)
        # Exclude the C pixels themselves
        cross[c_mask] = 0.0
        features.append(cross)

    return np.stack(features, axis=0)  # [F, H, W]


def encode_object_features(grid: np.ndarray, n_colors: int = 10) -> np.ndarray:
    """
    SGFE v2.1: Extract object-level features from an ARC grid.
    
    Returns: [12, H, W] float32 tensor with object-derived features.
    
    Theory (positive_Ricci_tensorizes): Object features are topological invariants
    that survive translation. Predicates on objects naturally commute with the
    translation group, reducing E_sheaf variance across examples.
    
    Features:
      - obj_size_rank_0..3: Is pixel in the k-th largest object?
      - containment_depth: How many objects contain this pixel's object?
      - obj_local_row/col: Normalized position within object's bbox
      - obj_aspect_ratio: Object width/height ratio
      - obj_relative_area: Object area / grid area
      - in_largest_obj: Is in the single largest object?
      - in_smallest_obj: Is in the single smallest foreground object?
      - obj_adjacency_count: How many other objects touch this object?
    """
    H, W = grid.shape
    grid_area = H * W
    
    # Extract connected components (lightweight scene graph)
    fg_mask = (grid != 0)
    labeled, n_objects = ndlabel(fg_mask)
    
    if n_objects == 0:
        # No foreground objects - return zeros
        return np.zeros((12, H, W), dtype=np.float32)
    
    # Compute object properties
    objects = []
    for obj_id in range(1, n_objects + 1):
        obj_mask = (labeled == obj_id)
        area = int(obj_mask.sum())
        if area == 0:
            continue
        
        # Bounding box
        rows = np.any(obj_mask, axis=1)
        cols = np.any(obj_mask, axis=0)
        r_idx = np.where(rows)[0]
        c_idx = np.where(cols)[0]
        if len(r_idx) == 0 or len(c_idx) == 0:
            continue
        r1, r2 = r_idx[0], r_idx[-1] + 1
        c1, c2 = c_idx[0], c_idx[-1] + 1
        
        objects.append({
            'id': obj_id,
            'mask': obj_mask,
            'area': area,
            'bbox': (r1, c1, r2, c2),
            'height': r2 - r1,
            'width': c2 - c1,
        })
    
    if not objects:
        return np.zeros((12, H, W), dtype=np.float32)
    
    # Sort by area (largest first)
    objects.sort(key=lambda o: -o['area'])
    
    # Compute containment relationships
    for i, obj_a in enumerate(objects):
        obj_a['containment_depth'] = 0
        obj_a['adjacency_count'] = 0
        for j, obj_b in enumerate(objects):
            if i == j:
                continue
            # Check if obj_a is contained in obj_b (bbox containment)
            a_r1, a_c1, a_r2, a_c2 = obj_a['bbox']
            b_r1, b_c1, b_r2, b_c2 = obj_b['bbox']
            if b_r1 <= a_r1 and b_c1 <= a_c1 and b_r2 >= a_r2 and b_c2 >= a_c2:
                obj_a['containment_depth'] += 1
            # Check adjacency (dilate mask and check overlap)
            kernel = np.ones((3, 3), dtype=np.uint8)
            dilated_a = ndimage.binary_dilation(obj_a['mask'], kernel)
            if (dilated_a & obj_b['mask']).any():
                obj_a['adjacency_count'] += 1
    
    # Build feature maps
    features = []
    
    # obj_size_rank_0..3: Is pixel in the k-th largest object?
    for rank in range(4):
        rank_map = np.zeros((H, W), dtype=np.float32)
        if rank < len(objects):
            rank_map[objects[rank]['mask']] = 1.0
        features.append(rank_map)
    
    # containment_depth: Normalized by max possible depth
    containment_map = np.zeros((H, W), dtype=np.float32)
    max_depth = max(o['containment_depth'] for o in objects) if objects else 1
    max_depth = max(max_depth, 1)
    for obj in objects:
        containment_map[obj['mask']] = obj['containment_depth'] / max_depth
    features.append(containment_map)
    
    # SGFE v2.7: Replace position-dependent local_row/col with morphological features
    # Theory (SGC.Renormalization.Lumpability): Strong Lumpability requires features
    # to be constant within equivalence classes. Morphological operations (erosion,
    # dilation, boundary) depend on SHAPE, not POSITION, satisfying this requirement.
    
    # morph_boundary: Pixels on object boundary (erosion residual)
    boundary_map = np.zeros((H, W), dtype=np.float32)
    kernel_cross = np.array([[0,1,0],[1,1,1],[0,1,0]], dtype=np.uint8)
    for obj in objects:
        eroded = ndimage.binary_erosion(obj['mask'], kernel_cross)
        boundary = obj['mask'] & ~eroded
        boundary_map[boundary] = 1.0
    features.append(boundary_map)
    
    # morph_skeleton: Approximate medial axis (multiple erosions)
    skeleton_map = np.zeros((H, W), dtype=np.float32)
    for obj in objects:
        # Iteratively erode until nothing left, track last non-empty
        current = obj['mask'].copy()
        for _ in range(min(obj['height'], obj['width']) // 2):
            eroded = ndimage.binary_erosion(current, kernel_cross)
            if not eroded.any():
                break
            current = eroded
        skeleton_map[current] = 1.0
    features.append(skeleton_map)
    
    # obj_aspect_ratio: width/height, clamped to [0, 1]
    aspect_map = np.zeros((H, W), dtype=np.float32)
    for obj in objects:
        aspect = obj['width'] / max(obj['height'], 1)
        aspect = min(aspect, 1.0 / max(aspect, 0.01))  # Ensure <= 1
        aspect_map[obj['mask']] = aspect
    features.append(aspect_map)
    
    # obj_relative_area: object area / grid area
    rel_area_map = np.zeros((H, W), dtype=np.float32)
    for obj in objects:
        rel_area_map[obj['mask']] = obj['area'] / grid_area
    features.append(rel_area_map)
    
    # in_largest_obj: Is in the single largest object?
    largest_map = np.zeros((H, W), dtype=np.float32)
    largest_map[objects[0]['mask']] = 1.0
    features.append(largest_map)
    
    # in_smallest_obj: Is in the single smallest foreground object?
    smallest_map = np.zeros((H, W), dtype=np.float32)
    smallest_map[objects[-1]['mask']] = 1.0
    features.append(smallest_map)
    
    # obj_adjacency_count: Normalized adjacency degree
    max_adj = max(o['adjacency_count'] for o in objects) if objects else 1
    max_adj = max(max_adj, 1)
    adj_map = np.zeros((H, W), dtype=np.float32)
    for obj in objects:
        adj_map[obj['mask']] = obj['adjacency_count'] / max_adj
    features.append(adj_map)
    
    return np.stack(features, axis=0)  # [12, H, W]


def encode_pixel_features_v2(
    grid: np.ndarray,
    n_colors: int = 10,
    include_object_features: bool = True
) -> np.ndarray:
    """
    SGFE v2.1: Extended feature encoding with optional object-level features.
    
    Returns: [n_features, H, W] float32 tensor.
    
    When include_object_features=True, appends 12 object-derived features
    to the base 74 pixel features, yielding 86 total features.
    """
    base_features = encode_pixel_features(grid, n_colors)
    
    if include_object_features:
        obj_features = encode_object_features(grid, n_colors)
        return np.concatenate([base_features, obj_features], axis=0)
    
    return base_features


# =============================================================================
# TENSOR LOGIC PREDICATE LEARNER
# =============================================================================

@dataclass
class DiscoveredPredicate:
    """A predicate discovered by tensor factorization."""
    factor_idx: int
    masks: List[np.ndarray]       # Boolean mask per training example
    f1: float                     # F1 score against residual
    precision: float
    recall: float
    weights: np.ndarray           # Feature weights W[:, k]
    bias: float                   # Bias b[k]
    top_features: List[Tuple[str, float]]  # Interpretable feature contributions
    rule_matrix: Optional[np.ndarray] = None  # Color rule Rule[i, o]


def _inject_wavelet_noise(
    W: torch.Tensor,
    noise_scale: float,
    wavelet_a: float = 1.0,
    wavelet_b: float = 1.0,
) -> None:
    """
    SGFE v2.6: Gauge-adapted Langevin noise in SVD coordinates.

    Theory (WAVELET_ENHANCED_NOISE_GAUGE_THEORY.md):
      Isotropic noise weakly couples to loss-relevant modes. Projecting noise
      through a Hermite-Gaussian spectral envelope biases perturbations toward
      the fine-scale singular directions where role-invariant structure emerges.
    """
    if noise_scale < 1e-8:
        return

    with torch.no_grad():
        if W.dim() == 2:
            try:
                U, S, Vh = torch.linalg.svd(W, full_matrices=False)
                n_sv = int(S.shape[0])
                if n_sv == 0:
                    return

                u = torch.linspace(0.0, 1.0, n_sv, device=W.device, dtype=W.dtype) + 0.01
                weights = (u ** wavelet_a) * torch.exp(-wavelet_b * (u ** 2))
                weights = weights / (weights.norm() + 1e-8)

                z = torch.randn(n_sv, device=W.device, dtype=W.dtype) * weights * noise_scale
                W.add_(U @ torch.diag(z) @ Vh)
            except Exception:
                # Numerical fallback keeps dynamics alive without crashing solve path.
                W.add_(torch.randn_like(W) * noise_scale * 0.01)
        else:
            W.add_(torch.randn_like(W) * noise_scale * 0.1)


class TensorPredicateLearner:
    """
    Differentiable predicate discovery via tensor factorization.

    SGC GROUNDING:
      The defect ε(Π, L) = ||(I - Π)LΠ|| becomes a differentiable loss.
      The partition Π becomes a set of learnable soft predicate masks.
      Gradient descent replaces combinatorial search.
      Thresholding (annealing T→0) recovers Boolean predicates.

    TENSOR LOGIC CONNECTION:
      Predicates P[r,c,k] = σ(Σ_f Feature[r,c,f] · W[f,k] + b[k])
      Rules Rule[k,i,o] = σ(V[k,i,o])
      The entire predicate discovery pipeline is ~10 tensor equations,
      differentiable end-to-end.
    """

    def __init__(
        self,
        n_factors: int = 4,
        n_colors: int = 10,
        lr: float = 0.05,
        steps: int = 300,
        temperature: float = 1.0,
        min_f1: float = 0.25,
        use_hermite_features: bool = False,
        use_object_features: bool = False,
    ):
        self.n_factors = n_factors
        self.n_colors = n_colors
        self.lr = lr
        self.steps = steps
        self.temperature = temperature
        self.min_f1 = min_f1
        # SGFE v2.0: Hermite-Gaussian wavelet features (Renormalization.lean)
        # When True, uses continuous spectral features instead of discrete
        self.use_hermite_features = use_hermite_features and _HAS_HERMITE_WAVELETS
        # SGFE v2.1: Object-level features (positive_Ricci_tensorizes)
        # When True, appends 12 topological object features to reduce E_sheaf
        self.use_object_features = use_object_features
        # SGFE v2.8: Lumpable-only mode (SGC.Renormalization.Lumpability)
        # When True, masks out position-dependent features to force predicates
        # that satisfy Strong Lumpability and achieve low sheaf_energy.
        self.lumpable_only = False
        # SGFE v2.2: GPU acceleration for tensor contractions
        # Theory: einsum operations on GPU are 10-100x faster than CPU
        self.device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')

    def discover_predicates(
        self,
        grids: List[np.ndarray],
        targets: List[np.ndarray],
        predictions: Optional[List[np.ndarray]] = None,
        verbose: bool = False,
    ) -> List[DiscoveredPredicate]:
        """
        Learn spatial predicates by gradient descent on the defect.

        THE ALGORITHM:
          1. ENCODE: pixel features F[e, r, c, f] from input grids
          2. PARAMETERIZE: soft predicates P = σ(F @ W + b) / T
          3. PARAMETERIZE: color rules Rule = σ(V)
          4. PREDICT: Out = Σ_k P[k] · (Input_OH @ Rule[k])
          5. LOSS: defect = ||Out - Target_OH||² + regularization
          6. OPTIMIZE: Adam on W, V, b for `steps` iterations
          7. THRESHOLD: P > 0.5 → Boolean masks
          8. SCORE: F1 of Boolean masks vs residual
          9. RETURN: predicates with F1 > min_f1

        Args:
            grids: input grids [E examples]
            targets: target output grids
            predictions: current predictions (optional; if None, uses grids)
            verbose: print learning progress

        Returns:
            List of DiscoveredPredicate sorted by F1
        """
        n_ex = len(grids)
        if n_ex == 0:
            return []

        # All examples must have same shape for batching
        shapes = set(g.shape for g in grids)
        if len(shapes) > 1:
            return []
        GH, GW = grids[0].shape  # Grid Height/Width (avoid shadowing weight param W)

        # --- ENCODE ---
        # SGFE v2.1: Use object features when enabled for translation-invariant predicates
        if self.use_object_features:
            feat_list = [encode_pixel_features_v2(g, self.n_colors, include_object_features=True) for g in grids]
        else:
            feat_list = [encode_pixel_features(g, self.n_colors) for g in grids]
        feat_np = np.stack(feat_list)  # [E, F, H, W]
        n_feat = feat_np.shape[1]

        # One-hot encode inputs and targets
        inp_oh = np.zeros((n_ex, GH, GW, self.n_colors), dtype=np.float32)
        tgt_oh = np.zeros((n_ex, GH, GW, self.n_colors), dtype=np.float32)
        for e in range(n_ex):
            for c in range(self.n_colors):
                inp_oh[e, :, :, c] = (grids[e] == c)
                tgt_oh[e, :, :, c] = (targets[e] == c)

        # Residual mask (where we still need to fix)
        if predictions is not None:
            res_np = np.stack([(p != t).astype(np.float32)
                               for p, t in zip(predictions, targets)])
        else:
            res_np = np.stack([(g != t).astype(np.float32)
                               for g, t in zip(grids, targets)])

        # --- SGFE v2.8: Lumpable-only feature mask ---
        # Theory (SGC.Renormalization.Lumpability): Position-dependent features violate
        # Strong Lumpability, causing high sheaf_energy. Mask them out to force TL
        # to discover predicates using only topologically-invariant features.
        # Position-dependent indices (base features only):
        #   12-13: border_row, border_col (edge-specific)
        #   25-42: same_row_C, same_col_C (relative position)
        #   43-44: row_pos, col_pos (absolute position)
        #   45-64: between_C_h, between_C_v, between_fg_h, between_fg_v (positional)
        #   65-73: cross_C (row+column alignment)
        if self.lumpable_only:
            position_dependent_indices = list(range(12, 14)) + list(range(25, 74))
            for idx in position_dependent_indices:
                if idx < n_feat:
                    feat_np[:, idx, :, :] = 0.0
        
        # --- Convert to tensors (force float32) and move to GPU ---
        feat_t = torch.tensor(feat_np, dtype=torch.float32, device=self.device)   # [E, F, H, W]
        inp_t = torch.tensor(inp_oh, dtype=torch.float32, device=self.device)     # [E, H, W, C]
        tgt_t = torch.tensor(tgt_oh, dtype=torch.float32, device=self.device)     # [E, H, W, C]
        res_t = torch.tensor(res_np, dtype=torch.float32, device=self.device)     # [E, H, W]

        K = self.n_factors
        C = self.n_colors

        # --- PARAMETERIZE (on GPU) ---
        # W[f, k]: which features compose each predicate
        W = (torch.randn(n_feat, K, device=self.device) * 0.1).detach().requires_grad_(True)
        # b[k]: predicate bias
        b = torch.zeros(K, device=self.device).detach().requires_grad_(True)
        # V[k, i, o]: color transformation rule per predicate region
        # Initialize V near identity (region k maps color i to color i)
        V_init = torch.zeros(K, C, C, device=self.device)
        for k in range(K):
            V_init[k] = torch.eye(C, device=self.device) * 2.0  # sigmoid(2) ≈ 0.88
        V = V_init.detach().requires_grad_(True)

        optimizer = torch.optim.Adam([W, V, b], lr=self.lr)

        best_loss = float('inf')
        best_state = None

        # --- OPTIMIZE with temperature annealing ---
        # SGC GROUNDING: The temperature controls the sharpness of the
        # step function. High T = soft exploration (sigmoid ≈ linear),
        # low T = sharp Boolean decisions (sigmoid ≈ step).
        # Annealing schedule: T_start → T_end over `steps` iterations.
        # This matches the grokking dynamics: explore → crystallize.
        T_start = max(self.temperature, 0.5)
        T_min = 0.1
        T_end = T_min * 2.0
        transition_point = 0.7
        n_pixels = int(n_ex) * int(GH) * int(GW)

        for step in range(self.steps):
            optimizer.zero_grad()

            frac = step / max(self.steps - 1, 1)
            if _HAS_SGFE_SCHEDULE:
                T_cur = tsallis_temperature_schedule(
                    step,
                    self.steps,
                    T_start=T_start,
                    T_min=T_min,
                    T_end=T_end,
                    transition_point=transition_point,
                )
            else:
                # Fallback: monotone anneal if SGFE scheduler is unavailable.
                T_cur = T_start * (1.0 - frac) + T_min * frac

            # Soft predicates: P[e,r,c,k] = σ((F @ W + b) / T)
            logits = torch.einsum('efhw,fk->ehwk', feat_t, W) + b
            P = torch.sigmoid(logits / T_cur)

            # Color rules: Rule[k,i,o] = σ(V[k,i,o])
            rules = torch.sigmoid(V)  # [K, C, C]

            # Predicted output: combine predicates with rules
            mapped = torch.einsum('ehwi,kio->ehwko', inp_t, rules)
            pred = torch.einsum('ehwk,ehwko->ehwo', P, mapped)
            pred = pred / (pred.sum(dim=-1, keepdim=True) + 1e-8)

            # --- LOSS = defect ---
            # Residual-weighted cross-entropy (5x weight on wrong pixels)
            residual_weight = 1.0 + 4.0 * res_t
            log_pred = torch.log(pred + 1e-8)
            per_pixel = residual_weight.unsqueeze(-1) * tgt_t * log_pred
            xent_scalar = -per_pixel.sum() / max(n_pixels, 1)

            # Sparsity: L1 on W encourages few features per predicate
            # Ramp up sparsity as T decreases (crystallization pressure)
            sparse_coeff = 0.005 + 0.02 * frac
            sparse_scalar = sparse_coeff * W.abs().sum()

            # Decorrelation: predicates should partition space, not overlap
            P_flat = P.reshape(-1, K)
            P_c = P_flat - P_flat.mean(0, keepdim=True)
            P_n = P_c / (P_c.norm(dim=0, keepdim=True) + 1e-8)
            gram = P_n.t() @ P_n / max(int(P_flat.shape[0]), 1)
            decorr_scalar = 0.01 * (gram - torch.eye(K, device=self.device)).pow(2).sum()

            total_loss = xent_scalar + sparse_scalar + decorr_scalar

            total_loss.backward()
            optimizer.step()

            # SGFE v2.6: Wavelet-coupled Langevin kick during Dream phase only.
            if frac < transition_point and T_cur > T_min:
                noise_scale = (T_cur - T_min) * 0.02
                _inject_wavelet_noise(W, noise_scale)
                with torch.no_grad():
                    V.add_(torch.randn_like(V) * noise_scale * 0.1)

            loss_val = total_loss.item()
            if loss_val < best_loss:
                best_loss = loss_val
                best_state = {
                    'W': W.detach().clone(),
                    'V': V.detach().clone(),
                    'b': b.detach().clone(),
                }

            if verbose and step % 50 == 0:
                print(f"    step {step:3d}: loss={loss_val:.4f} T={T_cur:.3f}")

        if best_state is None:
            return []

        # --- THRESHOLD: anneal T→0 ---
        with torch.no_grad():
            W_best = best_state['W']
            V_best = best_state['V']
            b_best = best_state['b']

            logits = torch.einsum('efhw,fk->ehwk', feat_t, W_best) + b_best
            P_soft = torch.sigmoid(logits)       # [E, H, W, K]
            P_bool = (P_soft > 0.5).cpu().numpy()      # Boolean masks (move to CPU)
            rules_bool = torch.sigmoid(V_best).cpu().numpy()  # [K, C, C]

        # --- SCORE each discovered predicate ---
        discovered = []
        for k in range(K):
            masks_k = [P_bool[e, :, :, k] for e in range(n_ex)]

            # F1 against residual
            tp = fp = fn = 0
            for e in range(n_ex):
                pmask = masks_k[e]
                rmask = res_np[e] > 0.5
                tp += int((pmask & rmask).sum())
                fp += int((pmask & ~rmask).sum())
                fn += int((~pmask & rmask).sum())

            prec = tp / max(tp + fp, 1)
            rec = tp / max(tp + fn, 1)
            f1 = 2 * prec * rec / max(prec + rec, 1e-10)

            if f1 >= self.min_f1:
                w_np = W_best[:, k].cpu().numpy()
                top_feats = self._interpret_weights(w_np)

                discovered.append(DiscoveredPredicate(
                    factor_idx=k,
                    masks=masks_k,
                    f1=f1,
                    precision=prec,
                    recall=rec,
                    weights=w_np,
                    bias=float(b_best[k]),
                    top_features=top_feats,
                    rule_matrix=rules_bool[k],
                ))

        discovered.sort(key=lambda x: -x.f1)

        if verbose and discovered:
            print(f"\n    Discovered {len(discovered)} predicates (F1 >= {self.min_f1}):")
            for d in discovered:
                print(f"      Factor {d.factor_idx}: F1={d.f1:.3f} "
                      f"(P={d.precision:.3f}, R={d.recall:.3f})")
                print(f"        Top features: "
                      f"{[(n, f'{w:.2f}') for n, w in d.top_features[:5]]}")

        return discovered

    def discover_residual_predicate(
        self,
        grids: List[np.ndarray],
        targets: List[np.ndarray],
        predictions: List[np.ndarray],
        seed: int = 42,
        verbose: bool = False,
    ) -> List[DiscoveredPredicate]:
        """
        Directly learn a predicate that covers the RESIDUAL (wrong pixels).

        SGC GROUNDING: This is the minimal tensor logic application:
          mask[r,c] = sigma(sum_f Feature[r,c,f] * w[f] + b)
        optimized to maximize F1 against residual = (prediction != target).

        Hardened version:
          - Deterministic seeding per factor for reproducibility
          - Total-variation compactness penalty for coherent regions
          - Class-weighted BCE with capped pos_weight
          - Per-example F1 tracked for stability verification

        SGFE (v1.0): Tsallis double-transition temperature schedule
          Phase 1: T_start → T_min  (Dream → Crystallize, q: 2.53 → 2.09)
          Phase 2: T_min → T_end    (Crystallize → Consolidate, q: 2.09 → 2.76)
        """
        n_ex = len(grids)
        if n_ex == 0:
            return []

        GH, GW = grids[0].shape

        # Encode features: discrete (default) or Hermite-Gaussian wavelets (SGFE v2.0)
        # Theory (Renormalization.lean): Hermite-Gaussian basis is the canonical
        # choice for multiscale spectral analysis. Provides continuous features
        # that capture structure at multiple spatial scales.
        if self.use_hermite_features:
            # SGFE v2.0: Hermite-Gaussian wavelet encoding
            # hermite_gaussian_encode returns (H, W, n_features)
            # We need (E, F, H, W) for tensor logic
            feat_list = []
            for g in grids:
                hg_feat = hermite_gaussian_encode(g, max_order=3, scales=(1.0, 2.0, 4.0))
                # Transpose from (H, W, F) to (F, H, W)
                feat_list.append(hg_feat.transpose(2, 0, 1))
            feat_np = np.stack(feat_list)  # [E, F, H, W]
        elif self.use_object_features:
            # SGFE v2.1: Object-level features for translation-invariant predicates
            # Theory (positive_Ricci_tensorizes): Object features are topological
            # invariants that reduce E_sheaf variance across examples
            feat_list = [encode_pixel_features_v2(g, self.n_colors, include_object_features=True) for g in grids]
            feat_np = np.stack(feat_list)  # [E, F, H, W]
        else:
            # Default: discrete feature encoding
            feat_list = [encode_pixel_features(g, self.n_colors) for g in grids]
            feat_np = np.stack(feat_list)  # [E, F, H, W]
        n_feat = feat_np.shape[1]

        # Compute residual masks
        res_masks = []
        for p, t in zip(predictions, targets):
            if p.shape != t.shape:
                return []
            res_masks.append((p != t).astype(np.float32))
        res_np = np.stack(res_masks)  # [E, H, W]

        n_pos = int(res_np.sum())
        n_total = n_ex * GH * GW
        if n_pos < 2:
            return []

        # Class weight: balance positive (wrong) vs negative (correct)
        pos_weight = max((n_total - n_pos) / max(n_pos, 1), 1.0)
        pos_weight = min(pos_weight, 50.0)  # Cap to avoid instability

        feat_t = torch.tensor(feat_np, dtype=torch.float32, device=self.device)
        res_t = torch.tensor(res_np, dtype=torch.float32, device=self.device)

        # Learn K separate binary predictors (each with deterministic seed)
        K = self.n_factors
        results = []

        for k in range(K):
            # Deterministic seed: reproducible across runs
            torch.manual_seed(seed * K + k)

            # Parameters: one weight vector + bias per predictor (on GPU)
            w = (torch.randn(n_feat, device=self.device) * 0.02).detach().requires_grad_(True)
            b = torch.zeros(1, device=self.device).detach().requires_grad_(True)

            optimizer = torch.optim.Adam([w, b], lr=self.lr)
            T_start = max(self.temperature, 0.5)
            T_min = 0.05
            T_end = T_min * 2.0
            transition_point = 0.7
            best_f1 = 0.0
            best_w = None
            best_b = None
            current_f1 = 0.0
            
            for step in range(self.steps):
                optimizer.zero_grad()

                frac = step / max(self.steps - 1, 1)  # For sparse penalty scaling
                if _HAS_SGFE_SCHEDULE:
                    T_cur = tsallis_temperature_schedule(
                        step,
                        self.steps,
                        T_start=T_start,
                        T_min=T_min,
                        T_end=T_end,
                        transition_point=transition_point,
                    )
                else:
                    T_cur = T_start * (1.0 - frac) + T_min * frac
                
                # Predict: P[e,r,c] = sigma((F . w + b) / T)
                logits = torch.einsum('efhw,f->ehw', feat_t, w) + b
                P = torch.sigmoid(logits / T_cur)

                # Weighted BCE loss
                bce = -(pos_weight * res_t * torch.log(P + 1e-8) +
                        (1.0 - res_t) * torch.log(1.0 - P + 1e-8))
                loss = bce.mean()

                # L1 sparsity on weights (encourage few features)
                sparse_pen = (0.005 + 0.03 * frac) * w.abs().sum()

                # Total-variation compactness penalty:
                # Prefer coherent spatial regions over scattered pixels.
                # TV(P) = |P[r,c] - P[r+1,c]| + |P[r,c] - P[r,c+1]|
                tv_h = (P[:, 1:, :] - P[:, :-1, :]).abs().mean()
                tv_v = (P[:, :, 1:] - P[:, :, :-1]).abs().mean()
                compact_pen = 0.01 * (tv_h + tv_v)

                total = loss + sparse_pen + compact_pen

                total.backward()
                optimizer.step()

                # SGFE v2.6: Gauge-adapted exploration during Dream phase.
                if frac < transition_point and T_cur > T_min:
                    noise_scale = (T_cur - T_min) * 0.02
                    _inject_wavelet_noise(w, noise_scale)
                    with torch.no_grad():
                        b.add_(torch.randn_like(b) * noise_scale * 0.1)

                # Compute hard F1 for checkpointing best
                if step % 20 == 0 or step == self.steps - 1:
                    with torch.no_grad():
                        hard = (P > 0.5).float()
                        tp = (hard * res_t).sum().item()
                        fp = (hard * (1.0 - res_t)).sum().item()
                        fn = ((1.0 - hard) * res_t).sum().item()
                        prec = tp / max(tp + fp, 1)
                        rec = tp / max(tp + fn, 1)
                        current_f1 = 2 * prec * rec / max(prec + rec, 1e-10)

                        if current_f1 > best_f1:
                            best_f1 = current_f1
                            best_w = w.detach().clone()
                            best_b = b.detach().clone()

                    if verbose and step % 100 == 0:
                        phase = "DREAM" if frac < transition_point else "CONSOLIDATE"
                        print(f"    k={k} step {step:3d}: loss={total.item():.4f} "
                              f"F1={current_f1:.3f} T={T_cur:.3f} [{phase}]", flush=True)

            if best_f1 >= self.min_f1 and best_w is not None:
                # Threshold at T->0
                with torch.no_grad():
                    logits = torch.einsum('efhw,f->ehw', feat_t, best_w) + best_b
                    masks = (logits > 0).cpu().numpy()

                masks_list = [masks[e] for e in range(n_ex)]
                w_np = best_w.cpu().numpy()
                top_feats = self._interpret_weights(w_np)

                # Recompute final pooled F1 + per-example F1s
                tp = fp = fn = 0
                per_ex_f1 = []
                for e in range(n_ex):
                    pmask = masks_list[e]
                    rmask = res_np[e] > 0.5
                    e_tp = int((pmask & rmask).sum())
                    e_fp = int((pmask & ~rmask).sum())
                    e_fn = int((~pmask & rmask).sum())
                    tp += e_tp; fp += e_fp; fn += e_fn
                    e_prec = e_tp / max(e_tp + e_fp, 1)
                    e_rec = e_tp / max(e_tp + e_fn, 1)
                    e_f1 = 2 * e_prec * e_rec / max(e_prec + e_rec, 1e-10)
                    per_ex_f1.append(e_f1)

                prec = tp / max(tp + fp, 1)
                rec = tp / max(tp + fn, 1)
                f1 = 2 * prec * rec / max(prec + rec, 1e-10)

                if f1 >= self.min_f1:
                    dp = DiscoveredPredicate(
                        factor_idx=k,
                        masks=masks_list,
                        f1=f1,
                        precision=prec,
                        recall=rec,
                        weights=w_np,
                        bias=float(best_b.item()),
                        top_features=top_feats,
                        rule_matrix=None,
                    )
                    dp.per_example_f1 = per_ex_f1  # type: ignore
                    results.append(dp)

                    if verbose:
                        n_sel = sum(int(m.sum()) for m in masks_list)
                        worst_ef1 = min(per_ex_f1) if per_ex_f1 else 0.0
                        print(f"    k={k}: F1={f1:.3f} (P={prec:.3f} R={rec:.3f}) "
                              f"{n_sel}px worst_ex={worst_ef1:.2f} {top_feats[0][0]}",
                              flush=True)

        results.sort(key=lambda x: -x.f1)
        return results

    @staticmethod
    def _interpret_weights(weights: np.ndarray) -> List[Tuple[str, float]]:
        """Map weight vector to interpretable feature names."""
        n = min(len(weights), len(FEATURE_NAMES))
        indexed = [(FEATURE_NAMES[i], float(weights[i])) for i in range(n)]
        indexed.sort(key=lambda x: -abs(x[1]))
        return indexed[:8]


# =============================================================================
# TENSOR PREDICATE → PredicateExpr BRIDGE
# =============================================================================
# The discovered tensor predicates must be wrapped as PredicateExpr objects
# so they integrate seamlessly with the existing solver infrastructure.

def make_tensor_predicate_expr(
    discovered: DiscoveredPredicate,
    feature_weights: np.ndarray,
    feature_bias: float,
    n_colors: int = 10,
):
    """
    Wrap a tensor-discovered predicate as a callable predicate expression.

    The returned object has the same interface as PredicateExpr:
      .evaluate(grid) → bool mask
      .name → human-readable description

    The predicate is defined by:
      mask[r,c] = (Σ_f Feature[r,c,f] · W[f] + b) > 0

    This is a learned linear combination of geometric features,
    discovered by gradient descent on the defect.
    """
    w = feature_weights.copy()
    b = feature_bias

    # Build interpretable name from top features
    top = discovered.top_features[:3]
    parts = []
    for name, weight in top:
        sign = '+' if weight > 0 else '-'
        parts.append(f"{sign}{name}")
    expr_name = f"tensor_pred({'&'.join(parts)})"

    class TensorPredicate:
        """A predicate learned by tensor factorization."""

        def __init__(self, weights, bias, name, n_col):
            self._w = weights
            self._b = bias
            self.name = name
            self._n_colors = n_col

        def evaluate(self, grid: np.ndarray) -> np.ndarray:
            """Evaluate predicate on a grid → Boolean mask."""
            features = encode_pixel_features(grid, self._n_colors)
            # features: [F, H, W], weights: [F]
            n_feat = min(len(self._w), features.shape[0])
            logit = np.tensordot(self._w[:n_feat], features[:n_feat], axes=([0], [0]))
            logit += self._b
            return logit > 0

        def __repr__(self):
            return f"TensorPredicate({self.name})"

    return TensorPredicate(w, b, expr_name, n_colors)


def crystallize_tensor_predicate(
    discovered: DiscoveredPredicate,
    color_roles: dict = None,
    n_top: int = 2,
) -> str:
    """
    Crystallize a tensor predicate into a discrete DSL string.

    SGC GROUNDING (Phase 2 Consolidation):
      The GPU discovers continuous weights over 86 geometric features.
      These weights are task-specific (stalk-level). To promote to a
      global section (sheaf-level), we must project the continuous
      representation into the discrete DSL vocabulary.

      This is the exact software instantiation of "grokking":
        continuous neural weights → discrete symbolic topology

    SGFE v2.4 (Color-Role Normalization):
      Color-specific features like 'same_row_1' are converted to
      role-based features like 'same_row_MINORITY'. This enables
      cross-task generalization because the role (MAJORITY/MINORITY)
      is resolved to actual colors at apply-time.

    Theory:
      - Landauer's principle: continuous → discrete is information erasure
      - The top features ARE the compressed representation
      - Negation (weight < 0) maps to ! prefix in DSL
      - Conjunction (&) preserves the AND structure of linear threshold
      - Color → Role quotient enables sheaf consistency across tasks

    Args:
        discovered: DiscoveredPredicate with top_features list
        color_roles: Dict mapping colors to roles (from detect_color_roles)
        n_top: Number of top features to include (default 2)

    Returns:
        DSL string like "!cross_MINORITY&same_row_MAJORITY" or "between_fg_h"
    """
    import re

    # SGFE v2.5: crystallization must project onto sheaf-consistent DSL atoms.
    # Keep rich object features for learning, but only crystallize features that
    # are evaluable by _compute_pixel_predicates at apply-time.
    dsl_exact_tokens = {
        'on_border', 'not_border', 'border_row', 'border_col',
        'near_fg', 'between_fg_h', 'between_fg_v', 'between_fg_hv',
        'enclosed_by_fg',
    }
    # Tensor feature names that correspond to existing DSL tokens.
    dsl_aliases = {
        'adj_fg': 'near_fg',
        'enclosed': 'enclosed_by_fg',
    }

    def color_role_to_canonical(feat_name: str, roles: dict) -> str:
        """
        Replace color literals with role labels only for color-indexed families.

        This prevents mangling object-feature suffixes like obj_size_rank_0,
        which are stalk-local indices rather than color coordinates.
        """
        # Families with suffix color slot (..._<color>)
        m = re.match(r'^(is_color|adj_to|same_row|same_col|cross)_(\d+)$', feat_name)
        if m:
            prefix, color_s = m.group(1), m.group(2)
            c = int(color_s)
            role = str(roles.get(c, str(c))).upper()
            return f"{prefix}_{role}"

        # Families with infix color slot (between_<color>_h / _v / _hv / _any)
        m = re.match(r'^between_(\d+)_(h|v|hv|any)$', feat_name)
        if m:
            color_s, axis = m.group(1), m.group(2)
            c = int(color_s)
            role = str(roles.get(c, str(c))).upper()
            return f"between_{role}_{axis}"

        # Extra color-indexed helper families (kept for compatibility)
        m = re.match(r'^(enclosed_by|within2|near8)_(\d+)$', feat_name)
        if m:
            prefix, color_s = m.group(1), m.group(2)
            c = int(color_s)
            role = str(roles.get(c, str(c))).upper()
            return f"{prefix}_{role}"

        # SGFE v2.6: Topological/Object-centric predicate families
        # Theory (TopologicalAbstraction.lean): These predicates operate on
        # connected components and bounding boxes rather than raw pixels,
        # enabling structural transfer across tasks with different grid layouts.
        #
        # Families: inside_bbox_X, contained_by_X, obj_span_h/v_X, obj_row/col_X,
        # same_shape_as_X, exactly{N}_adj_X
        m = re.match(r'^(inside_bbox|contained_by|obj_row|obj_col|same_shape_as)_(\d+)$', feat_name)
        if m:
            prefix, color_s = m.group(1), m.group(2)
            c = int(color_s)
            role = str(roles.get(c, str(c))).upper()
            return f"{prefix}_{role}"

        # obj_span with axis suffix: obj_span_h_X, obj_span_v_X
        m = re.match(r'^obj_span_(h|v)_(\d+)$', feat_name)
        if m:
            axis, color_s = m.group(1), m.group(2)
            c = int(color_s)
            role = str(roles.get(c, str(c))).upper()
            return f"obj_span_{axis}_{role}"

        # exactlyN_adj_X: exact adjacency count predicates
        m = re.match(r'^exactly(\d+)_adj_(\d+)$', feat_name)
        if m:
            n_adj, color_s = m.group(1), m.group(2)
            c = int(color_s)
            role = str(roles.get(c, str(c))).upper()
            return f"exactly{n_adj}_adj_{role}"

        # Non-color families (including object features) are unchanged.
        return feat_name

    def is_dsl_evaluable(feat_name: str) -> bool:
        if feat_name in dsl_exact_tokens:
            return True
        if re.match(r'^(is_color|adj_to|same_row|same_col|cross)_[A-Z0-9_]+$', feat_name):
            return True
        if re.match(r'^between_[A-Z0-9_]+_(h|v|hv|any)$', feat_name):
            return True
        if re.match(r'^(enclosed_by|within2|near8)_[A-Z0-9_]+$', feat_name):
            return True
        # SGFE v2.6: Topological predicate families
        if re.match(r'^(inside_bbox|contained_by|obj_row|obj_col|same_shape_as)_[A-Z0-9_]+$', feat_name):
            return True
        if re.match(r'^obj_span_(h|v)_[A-Z0-9_]+$', feat_name):
            return True
        if re.match(r'^exactly\d+_adj_[A-Z0-9_]+$', feat_name):
            return True
        return False

    # Oversample and then filter so object/continuous-only features do not block
    # crystallization when geometric DSL features are present lower in rank.
    top = discovered.top_features[:max(n_top * 4, 12)]
    if not top:
        return None

    parts = []
    for feat_name, weight in top:
        clean_name = feat_name.lstrip('+-')

        # Normalize tensor-only aliases into DSL token names.
        clean_name = dsl_aliases.get(clean_name, clean_name)

        if color_roles:
            clean_name = color_role_to_canonical(clean_name, color_roles)

        if not is_dsl_evaluable(clean_name):
            continue

        parts.append(f"!{clean_name}" if weight < 0 else clean_name)
        if len(parts) >= n_top:
            break

    if not parts:
        return None

    return "&".join(parts)


# =============================================================================
# TENSOR DREAM PHASE: Cluster-Level Predicate Discovery
# =============================================================================

def tensor_dream_phase(
    near_miss_tasks: List[Dict],
    n_factors: int = 4,
    lr: float = 0.05,
    steps: int = 300,
    verbose: bool = True,
) -> List[Dict]:
    """
    Sleep phase: apply tensor factorization to near-miss tasks.

    For each task, factorize the transformation tensor to discover
    predicates that the combinatorial search missed.

    SGC GROUNDING:
      This is the DreamCoder sleep phase implemented via tensor logic.
      Instead of syntactic compression (extracting common subroutines),
      we do SEMANTIC compression (finding the low-rank structure of
      the transformation tensor). The factors aren't code patterns;
      they're geometric invariants of the transformation space.

    Args:
        near_miss_tasks: list of dicts with keys:
            'task_id', 'grids', 'targets', 'predictions'
        n_factors: number of latent spatial regions to discover
        lr: learning rate for gradient descent
        steps: number of optimization steps
        verbose: print progress

    Returns:
        List of dicts, each with:
            'task_id': which task
            'predicates': list of DiscoveredPredicate
            'tensor_predicates': list of callable TensorPredicate objects
            'improvement': best F1 achieved
    """
    learner = TensorPredicateLearner(
        n_factors=n_factors,
        lr=lr,
        steps=steps,
    )

    results = []

    for task_info in near_miss_tasks:
        task_id = task_info['task_id']
        grids = task_info['grids']
        targets = task_info['targets']
        predictions = task_info.get('predictions')

        if verbose:
            print(f"\n  [TENSOR] Task {task_id[:8]}:", flush=True)

        try:
            discovered = learner.discover_predicates(
                grids, targets, predictions,
                verbose=verbose,
            )
        except Exception as e:
            if verbose:
                print(f"    Error: {e}")
            continue

        if not discovered:
            if verbose:
                print(f"    No predicates found above threshold")
            continue

        # Wrap as callable TensorPredicate objects
        tensor_preds = []
        for d in discovered:
            tp = make_tensor_predicate_expr(
                d, d.weights, d.bias,
            )
            tensor_preds.append(tp)

        results.append({
            'task_id': task_id,
            'predicates': discovered,
            'tensor_predicates': tensor_preds,
            'best_f1': discovered[0].f1 if discovered else 0.0,
        })

        if verbose:
            print(f"    Best F1: {discovered[0].f1:.3f} "
                  f"({discovered[0].top_features[0][0]})")

    if verbose:
        n_improved = sum(1 for r in results if r['best_f1'] > 0.5)
        print(f"\n  [TENSOR DREAM] {len(results)} tasks analyzed, "
              f"{n_improved} with strong predicates (F1 > 0.5)")

    return results


# =============================================================================
# STANDALONE DEMO: Run tensor logic on the ARC training set
# =============================================================================

if __name__ == "__main__":
    import sys
    import time
    sys.path.insert(0, '.')

    from arc_sgc_phase8_3 import load_arc_tasks, ARCGrid, compute_defect_energy
    from arc_sgc_residual_solver import RecursiveResidualSolver

    print("=" * 70)
    print("TENSOR LOGIC PREDICATE DISCOVERY DEMO")
    print("=" * 70)
    print()
    print("Theory: Domingos (2024) Tensor Logic × SGC defect minimization")
    print("Method: Gradient descent on differentiable predicate space")
    print("Goal:   Discover predicates that beam search cannot find")
    print()

    # Load tasks
    import os
    data_path = os.path.join(os.path.dirname(__file__), '..', 'data', 'arc', 'training')
    tasks = load_arc_tasks(data_path)
    print(f"Loaded {len(tasks)} tasks")

    # Create solver (no journal needed for demo)
    solver = RecursiveResidualSolver(max_depth=3, beam_width=8, verbose=False)

    # Find near-miss tasks
    near_misses = []
    print("\n--- Phase 1: WAKE (finding near-misses) ---")
    for i, task in enumerate(tasks[:50]):  # First 50 for demo speed
        try:
            result = solver.solve_task(task)
            d = result['avg_train_energy']
            if 0.001 < d < 0.15:  # Near-miss
                # Collect grids and predictions
                grids = [ex.input_grid.data.numpy() for ex in task.train_examples]
                targets = [ex.output_grid.data.numpy() for ex in task.train_examples]
                preds = []
                for ex in task.train_examples:
                    inp = ex.input_grid.data.numpy()
                    preds.append(result['program'].apply(inp))

                near_misses.append({
                    'task_id': task.task_id,
                    'grids': grids,
                    'targets': targets,
                    'predictions': preds,
                    'defect': d,
                    'method': result['method'],
                })
                print(f"  {task.task_id[:8]} d={d:.4f} {result['method'][:50]}")
        except Exception:
            pass

    print(f"\nFound {len(near_misses)} near-misses in first 50 tasks")

    if not near_misses:
        print("No near-misses found. Try more tasks.")
        sys.exit(0)

    # Phase 2: DREAM (tensor logic predicate discovery)
    print("\n--- Phase 2: DREAM (tensor factorization) ---")
    t0 = time.time()
    dream_results = tensor_dream_phase(
        near_misses,
        n_factors=4,
        lr=0.05,
        steps=200,
        verbose=True,
    )
    dream_time = time.time() - t0

    print(f"\n--- Phase 3: RESULTS ---")
    print(f"Dream phase took {dream_time:.1f}s")
    print(f"Tasks analyzed: {len(dream_results)}")

    for r in dream_results:
        print(f"\n  Task {r['task_id'][:8]}: best F1 = {r['best_f1']:.3f}")
        for tp in r['tensor_predicates']:
            print(f"    {tp.name}")

    print(f"\n{'=' * 70}")
    print("TENSOR LOGIC DEMO COMPLETE")
    print("=" * 70)
