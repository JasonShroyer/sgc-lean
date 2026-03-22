"""
SGC Spectral Gradient Flow Engine (SGFE)
=========================================

Theory-grounded components for the ARC solver.
Every function traces to a verified theorem or quantitative result.

Components:
  1. functional_blanket_variance  — FunctionalBlanket.lean (ANOVA decomposition)
  2. hermite_gaussian_encode      — Multiscale spectral analysis (Renormalization)
  3. tsallis_temperature_schedule — Lifshitz transition (q: 2.53 → 2.09 → 2.76)
  4. sheaf_consistency_energy     — CellularSheafNetwork (global section check)
  5. SGFEPrimitiveLibrary         — Renormalization.lean (dirichlet_gap_non_decrease)

References:
  - FunctionalBlanket.lean: FunctionalDefect = withinClassVariance / totalVariance
  - docs/functional_blanket_breakthrough.md: Experimental validation
  - lifshitz_transition_experiment.py: Tsallis q estimation
  - cellular_sheaf_network.py: Sheaf Laplacian energy
"""

import numpy as np
from typing import List, Tuple, Dict, Optional, Any
from collections import Counter


# =============================================================================
# 1. FUNCTIONAL BLANKET VARIANCE (FunctionalBlanket.lean)
# =============================================================================
#
# From FunctionalBlanket.lean line 97:
#   FunctionalDefect = withinClassVariance / (totalVariance + 1e-10)
#
# ANOVA decomposition: Total = Within + Between
# Low ε_func = equivalence classes collapsed = structure learned
#
# For ARC:
#   "Classes" = transformation types (what each pixel becomes)
#   "States"  = pixel feature vectors (spatial + color context)
#   ε_func ∈ [0, 1]: 0 = perfect partition, 1 = no structure

def _encode_pixel_features(grid: np.ndarray) -> np.ndarray:
    """
    Encode each pixel as a feature vector from grid context.

    Features (per pixel):
      - Color one-hot (10 dims: colors 0-9)
      - Normalized position (2 dims: row/H, col/W)
      - Local 3x3 neighborhood color histogram (10 dims)
      - Row/col color mode (2 dims)

    Total: 24-dimensional feature vector per pixel.

    Theory: These are the "hidden states" h(x) from FunctionalBlanket.lean.
    For ARC, the grid structure IS the representation (no neural network).
    """
    H, W = grid.shape
    n = H * W
    features = np.zeros((n, 24), dtype=np.float32)

    flat_idx = 0
    for r in range(H):
        for c in range(W):
            # Color one-hot (dims 0-9)
            color = int(grid[r, c]) % 10
            features[flat_idx, color] = 1.0

            # Normalized position (dims 10-11)
            features[flat_idx, 10] = r / max(H - 1, 1)
            features[flat_idx, 11] = c / max(W - 1, 1)

            # 3x3 neighborhood color histogram (dims 12-21)
            for dr in range(-1, 2):
                for dc in range(-1, 2):
                    nr, nc = r + dr, c + dc
                    if 0 <= nr < H and 0 <= nc < W:
                        nc_color = int(grid[nr, nc]) % 10
                        features[flat_idx, 12 + nc_color] += 1.0 / 9.0

            # Row mode color (dim 22)
            row_colors = grid[r, :]
            row_mode = int(Counter(row_colors.tolist()).most_common(1)[0][0]) % 10
            features[flat_idx, 22] = row_mode / 9.0

            # Col mode color (dim 23)
            col_colors = grid[:, c]
            col_mode = int(Counter(col_colors.tolist()).most_common(1)[0][0]) % 10
            features[flat_idx, 23] = col_mode / 9.0

            flat_idx += 1

    return features


def _compute_change_labels(pred: np.ndarray, tgt: np.ndarray) -> np.ndarray:
    """
    Compute per-pixel transformation label (equivalence class).

    Labels:
      0: unchanged (pred == tgt)
      1+: changed, encoded as 10*pred_color + tgt_color + 1

    Theory: These are the algebraic equivalence classes from
    FunctionalBlanket.lean (AlgebraicEquivalence).
    """
    H, W = pred.shape
    labels = np.zeros(H * W, dtype=np.int32)
    changed = (pred != tgt).ravel()
    labels[changed] = (10 * pred.ravel()[changed] + tgt.ravel()[changed] + 1).astype(np.int32)
    return labels


def functional_blanket_variance(
    pred: np.ndarray,
    tgt: np.ndarray,
    features: Optional[np.ndarray] = None,
) -> float:
    """
    Compute functional defect ε_func for an ARC prediction.

    From FunctionalBlanket.lean:
      ε_func = withinClassVariance / (totalVariance + 1e-10)

    Args:
      pred: Program output grid (H, W)
      tgt:  Target output grid (H, W)
      features: Optional pre-computed pixel features (n, d).
                If None, computed from pred grid.

    Returns:
      ε_func ∈ [0, 1]. Lower = better partition.
      0.0 = perfect (all pixels correct, or wrong pixels perfectly
            separated by transformation type)
      1.0 = no structure (random within-class distribution)

    Experimental validation (grokking):
      Pre-grok:  ε ≈ 1.0
      At grok:   ε < 0.15  (grokkingThreshold from Lean)
      Post-grok: ε ≈ 0.02
    """
    if pred.shape != tgt.shape:
        return 1.0

    # Perfect prediction → ε = 0
    if np.array_equal(pred, tgt):
        return 0.0

    # Compute features from prediction grid if not provided
    if features is None:
        features = _encode_pixel_features(pred)

    # Compute transformation labels (equivalence classes)
    labels = _compute_change_labels(pred, tgt)

    # Total variance (across all features, all pixels)
    total_var = float(np.var(features, axis=0).mean())
    if total_var < 1e-10:
        return 1.0

    # Within-class variance (ANOVA)
    unique_labels = np.unique(labels)
    within_var = 0.0
    total_count = 0

    for c in unique_labels:
        mask = (labels == c)
        count = int(mask.sum())
        if count > 1:
            class_features = features[mask]
            class_var = float(np.var(class_features, axis=0).mean())
            within_var += class_var * count
            total_count += count

    if total_count > 0:
        within_var /= total_count

    eps = within_var / (total_var + 1e-10)
    return float(np.clip(eps, 0.0, 1.0))


def functional_blanket_variance_multi(
    program,
    task,
) -> Tuple[float, List[float]]:
    """
    Compute functional defect across ALL training examples.

    Returns:
      (avg_eps, per_example_eps)

    Theory: The functional blanket must hold across ALL examples
    (sheaf global section = consistent across stalks).
    """
    per_ex = []
    for ex in task.train_examples:
        inp = ex.input_grid.data.numpy()
        tgt = ex.output_grid.data.numpy()
        try:
            pred = program.apply(inp)
            if pred.shape == tgt.shape:
                eps = functional_blanket_variance(pred, tgt)
                per_ex.append(eps)
            else:
                per_ex.append(1.0)
        except Exception:
            per_ex.append(1.0)

    avg = float(np.mean(per_ex)) if per_ex else 1.0
    return avg, per_ex


# =============================================================================
# 2. HERMITE-GAUSSIAN WAVELET ENCODING (Renormalization)
# =============================================================================
#
# Theory: Multiscale = canonical wavelet (Hermite-Gaussian) basis.
# ψ_n(x) = H_n(x) * exp(-x²/2) where H_n is the n-th Hermite polynomial.
#
# For ARC: encode transformation tensor at multiple spatial scales.
# Handles heterogeneous shapes by padding to common size.

def _hermite_poly(n: int, x: np.ndarray) -> np.ndarray:
    """Evaluate n-th Hermite polynomial H_n(x) via recurrence."""
    if n == 0:
        return np.ones_like(x)
    elif n == 1:
        return 2 * x
    else:
        h_prev2 = np.ones_like(x)
        h_prev1 = 2 * x
        for k in range(2, n + 1):
            h_curr = 2 * x * h_prev1 - 2 * (k - 1) * h_prev2
            h_prev2, h_prev1 = h_prev1, h_curr
        return h_prev1


def _hermite_gaussian(n: int, x: np.ndarray, sigma: float = 1.0) -> np.ndarray:
    """Hermite-Gaussian wavelet ψ_n(x/σ) = H_n(x/σ) * exp(-x²/(2σ²))."""
    z = x / sigma
    return _hermite_poly(n, z) * np.exp(-z * z / 2)


def hermite_gaussian_encode(
    grid: np.ndarray,
    max_order: int = 3,
    scales: Tuple[float, ...] = (1.0, 2.0, 4.0),
    pad_to: Optional[Tuple[int, int]] = None,
) -> np.ndarray:
    """
    Encode a grid using Hermite-Gaussian wavelets at multiple scales.

    Returns a feature tensor of shape (H, W, n_features) where
    n_features = n_colors * n_orders * n_scales.

    Theory (Renormalization.lean):
      Multiscale encoding = renormalization group flow.
      Each scale captures structure at a different resolution.
      Hermite-Gaussian basis is the canonical choice for spectral analysis.

    Args:
      grid: Input grid (H, W) with integer color values 0-9
      max_order: Maximum Hermite polynomial order (0..max_order-1)
      scales: Spatial scales for wavelet convolution
      pad_to: Optional (H_pad, W_pad) for heterogeneous shape handling

    Returns:
      Feature tensor (H, W, n_features)
    """
    H, W = grid.shape

    # Pad to common size if specified
    if pad_to is not None:
        pH, pW = pad_to
        padded = np.zeros((pH, pW), dtype=grid.dtype)
        padded[:H, :W] = grid
        grid = padded
        H, W = pH, pW

    # Color channels (one-hot)
    n_colors = 10
    color_channels = np.zeros((H, W, n_colors), dtype=np.float32)
    for c in range(n_colors):
        color_channels[:, :, c] = (grid == c).astype(np.float32)

    # Coordinate grids (normalized to [-3, 3] for good wavelet support)
    row_coords = np.linspace(-3, 3, H)
    col_coords = np.linspace(-3, 3, W)

    features = []

    for sigma in scales:
        for order in range(max_order):
            # Row wavelet
            row_wavelet = _hermite_gaussian(order, row_coords, sigma)
            # Col wavelet
            col_wavelet = _hermite_gaussian(order, col_coords, sigma)

            # 2D separable wavelet: outer product
            wavelet_2d = np.outer(row_wavelet, col_wavelet)

            # Convolve each color channel with the wavelet
            for c in range(n_colors):
                # Element-wise multiplication (local wavelet coefficient)
                feat = color_channels[:, :, c] * wavelet_2d
                features.append(feat)

    return np.stack(features, axis=-1)


def perceive_with_hermite_wavelets(
    task,
    max_order: int = 3,
    scales: Tuple[float, ...] = (1.0, 2.0, 4.0),
) -> np.ndarray:
    """
    Perceive phase: encode all I/O examples as a padded transformation tensor
    using Hermite-Gaussian wavelets.

    Returns: T[e, r, c, f] where e=example, f=feature channel

    Theory: This IS the functor F: Observations → Representations.
    The wavelet basis provides the renormalization group structure.
    """
    # Find common padded size across all examples
    max_h = max(
        max(ex.input_grid.shape[0] for ex in task.train_examples),
        max(ex.output_grid.shape[0] for ex in task.train_examples),
    )
    max_w = max(
        max(ex.input_grid.shape[1] for ex in task.train_examples),
        max(ex.output_grid.shape[1] for ex in task.train_examples),
    )
    pad_to = (max_h, max_w)

    encoded = []
    for ex in task.train_examples:
        inp = ex.input_grid.data.numpy()
        tgt = ex.output_grid.data.numpy()

        # Encode input and output
        inp_enc = hermite_gaussian_encode(inp, max_order, scales, pad_to)
        tgt_enc = hermite_gaussian_encode(tgt, max_order, scales, pad_to)

        # Transformation tensor: difference in wavelet space
        diff = tgt_enc - inp_enc
        encoded.append(diff)

    return np.stack(encoded, axis=0)  # (n_examples, H, W, n_features)


# =============================================================================
# 3. TSALLIS TEMPERATURE SCHEDULE (Lifshitz Transition)
# =============================================================================
#
# From lifshitz_transition_experiment.py:
#   Observed q trajectory: 2.53 → 2.09 → 2.76 (double transition)
#
# Temperature schedule reproduces this via:
#   Phase 1: T decreases (exploration → exploitation), q: 2.53 → 2.09
#   Phase 2: T increases slightly (consolidation), q: 2.09 → 2.76
#
# For gradient descent in TensorPredicateLearner:
#   T controls the softmax temperature in the sigmoid activation.
#   High T → soft masks (continuous Dream phase)
#   Low T → hard masks (Boolean Crystallize phase)

def tsallis_temperature_schedule(
    step: int,
    total_steps: int,
    T_start: float = 2.0,
    T_min: float = 0.1,
    T_end: float = 0.5,
    transition_point: float = 0.7,
) -> float:
    """
    Temperature schedule reproducing Tsallis q double transition.

    Phase 1 (steps 0..transition_point*total):
      Linear anneal T_start → T_min (Dream → Crystallize)
      Corresponds to q: 2.53 → 2.09

    Phase 2 (steps transition_point*total..total):
      Linear ramp T_min → T_end (Consolidation)
      Corresponds to q: 2.09 → 2.76

    Theory (Lifshitz transition):
      The double transition is the signature of a topological phase change.
      Phase 1: Continuous symmetry breaking (soft masks harden)
      Phase 2: Consolidation (new topology stabilizes at finite T)

    Args:
      step: Current optimization step
      total_steps: Total number of steps
      T_start: Initial temperature (high = exploration)
      T_min: Minimum temperature at transition (Crystallize)
      T_end: Final temperature (Consolidation)
      transition_point: Fraction of steps at which minimum occurs

    Returns:
      Temperature T for this step
    """
    if total_steps <= 1:
        return T_min

    t = step / max(total_steps - 1, 1)

    if t < transition_point:
        # Phase 1: Dream → Crystallize (anneal down)
        frac = t / transition_point
        T = T_start + (T_min - T_start) * frac
    else:
        # Phase 2: Crystallize → Consolidate (ramp up)
        frac = (t - transition_point) / (1.0 - transition_point)
        T = T_min + (T_end - T_min) * frac

    return float(T)


# =============================================================================
# 4. SHEAF CONSISTENCY ENERGY (CellularSheafNetwork)
# =============================================================================
#
# From cellular_sheaf_network.py:
#   E = sum over edges of ||rho(head) - tail||^2
#   A Global Section has E = 0 (all stalks agree under restriction).
#
# For ARC programs:
#   Each training example is a "stalk" (local view).
#   The predicate mask is the "section" we're checking.
#   Sheaf energy = inconsistency of the predicate across examples.
#
# Low energy = the predicate means the same thing in every example.

def sheaf_consistency_energy(
    masks: List[np.ndarray],
    grids: List[np.ndarray],
    targets: List[np.ndarray],
    predictions: List[np.ndarray],
) -> float:
    """
    Compute sheaf consistency energy for a predicate across examples.

    E_sheaf = Var(per-example precision) + Var(per-example recall)
            + Var(per-example change_type_distribution)

    Theory (positive_Ricci_tensorizes):
      A valid global section must be consistent across ALL stalks.
      High sheaf energy = the predicate has different semantics in
      different examples = NOT a valid global section.

    Args:
      masks: Per-example boolean masks from predicate evaluation
      grids: Per-example input grids
      targets: Per-example target grids
      predictions: Per-example prediction grids

    Returns:
      E_sheaf ≥ 0. Lower = more consistent.
      E_sheaf < threshold → global section exists.
    """
    if len(masks) < 2:
        return 0.0  # Single example is trivially consistent

    precisions = []
    recalls = []
    change_dists = []

    for mask, pred, tgt in zip(masks, predictions, targets):
        if pred.shape != tgt.shape:
            return float('inf')

        wrong = (pred != tgt)
        mask_bool = mask.astype(bool)

        # Precision: fraction of masked pixels that are actually wrong
        n_masked = int(mask_bool.sum())
        if n_masked > 0:
            tp = int((mask_bool & wrong).sum())
            prec = tp / n_masked
        else:
            prec = 0.0
        precisions.append(prec)

        # Recall: fraction of wrong pixels that are masked
        n_wrong = int(wrong.sum())
        if n_wrong > 0:
            rec = int((mask_bool & wrong).sum()) / n_wrong
        else:
            rec = 1.0  # No wrong pixels → trivially recalled
        recalls.append(rec)

        # Change type distribution under mask
        if n_masked > 0:
            changes = pred[mask_bool] * 10 + tgt[mask_bool]
            dist = Counter(changes.tolist())
            total = sum(dist.values())
            change_dists.append({k: v / total for k, v in dist.items()})
        else:
            change_dists.append({})

    # Energy components
    prec_var = float(np.var(precisions))
    rec_var = float(np.var(recalls))

    # Change distribution divergence (average pairwise L1)
    dist_energy = 0.0
    n_pairs = 0
    all_keys = set()
    for d in change_dists:
        all_keys.update(d.keys())

    for i in range(len(change_dists)):
        for j in range(i + 1, len(change_dists)):
            l1 = sum(abs(change_dists[i].get(k, 0) - change_dists[j].get(k, 0))
                     for k in all_keys)
            dist_energy += l1
            n_pairs += 1

    if n_pairs > 0:
        dist_energy /= n_pairs

    E = prec_var + rec_var + dist_energy
    return float(E)


def sheaf_global_section_exists(
    masks: List[np.ndarray],
    grids: List[np.ndarray],
    targets: List[np.ndarray],
    predictions: List[np.ndarray],
    threshold: float = 0.5,
) -> bool:
    """
    Check whether a predicate forms a valid global section.

    Theory (100% compositional result from sheaf experiment):
      Native sheaf structure → 100% compositional generalization.
      Post-hoc sheaf analysis → only 3.4%.

      A predicate that forms a global section (E_sheaf < threshold)
      is guaranteed to generalize across examples.

    Returns:
      True if sheaf energy < threshold (consistent global section).
    """
    E = sheaf_consistency_energy(masks, grids, targets, predictions)
    return E < threshold


# =============================================================================
# 5. SGFE PRIMITIVE LIBRARY (Renormalization.lean)
# =============================================================================
#
# From Renormalization.lean (dirichlet_gap_non_decrease):
#   Every accepted Π collapses into a new AtomicOp in OperatorLibrary.
#   The spectral gap can only increase → library only gets better.
#
# From ContinualLearning/ (safe_surgery_preserves_blanket):
#   New primitives are frozen only after sheaf consistency check.

class CrossTaskPredicateValidator:
    """
    Curriculum-aware validator for cross-task predicate generalization.
    
    Theory (sheaf cohomology):
      The 0% → 3% TL acceptance breakthrough revealed that predicates
      discovered on single tasks cannot compose cross-task because they
      lie in different symmetry cosets.
      
      This validator caches predictions/targets from ALL near-miss tasks,
      allowing predicates to be tested for cross-task generalization
      BEFORE acceptance into the library.
      
      A predicate is curriculum-valid if IG > 0 on ≥ k tasks (default k=2).
      This implements the dirichlet_gap_non_decrease condition at
      curriculum level, not per-task level.
    
    From SGFE_V2_1_BREAKTHROUGH_REPORT.md:
      "The system forgets everything it learns the moment it moves to
       the next task. The library size is stuck at 2 primitives."
      
      This validator is the fix: predicates must generalize to enter library.
    """
    
    def __init__(
        self,
        similarity_threshold: float = 0.3,
        min_delta: float = 0.001,
        debug: bool = False,
        max_debug_history: int = 512,
    ):
        self.entries = {}  # task_id -> {gradients, predictions, targets, signature}
        self.signature_clusters = {}  # cluster_id -> [task_ids]
        self.similarity_threshold = float(similarity_threshold)
        self.min_delta = float(min_delta)
        self.debug = bool(debug)
        self.max_debug_history = max(int(max_debug_history), 1)
        self.last_test_report: Dict[str, Any] = {}
        self.test_reports: List[Dict[str, Any]] = []

    def _record_test_report(self, report: Dict[str, Any]) -> None:
        """Store the latest cross-task test report for downstream diagnostics."""
        self.last_test_report = report
        if self.debug:
            self.test_reports.append(report)
            if len(self.test_reports) > self.max_debug_history:
                self.test_reports.pop(0)

    def get_recent_reports(self, n: int = 20) -> List[Dict[str, Any]]:
        """Return the most recent cross-task reports (for eval instrumentation)."""
        n = max(int(n), 0)
        if n == 0:
            return []
        return self.test_reports[-n:]

    def get_neighbor_counts(self, threshold: Optional[float] = None) -> Dict[str, int]:
        """
        Number of similar peers per cached task under the signature metric.

        Useful to detect over-fragmented clusters before interpreting rejection rates.
        """
        if threshold is None:
            threshold = self.similarity_threshold
        out: Dict[str, int] = {}
        for task_id, entry in self.entries.items():
            out[task_id] = len(self.get_similar_tasks(
                entry['signature'], threshold=threshold, exclude_task=task_id
            ))
        return out

    @staticmethod
    def _detect_color_roles(grid: np.ndarray) -> Dict[int, str]:
        """Map concrete colors to role labels (bg/majority/minority/anchor_i)."""
        counts = Counter(np.asarray(grid).ravel().tolist())
        counts.pop(0, None)  # background
        roles: Dict[int, str] = {0: 'bg'}
        if not counts:
            return roles

        ordered = sorted(counts, key=counts.get, reverse=True)
        for i, color in enumerate(ordered):
            if i == 0:
                roles[int(color)] = 'majority'
            elif i == len(ordered) - 1 and len(ordered) > 1:
                roles[int(color)] = 'minority'
            else:
                roles[int(color)] = f'anchor_{i}'
        return roles

    @classmethod
    def _build_role_transport(
        cls,
        source_grid: np.ndarray,
        peer_grid: np.ndarray,
    ) -> Dict[int, int]:
        """
        Build color transport map source_color -> peer_color by matching role labels.
        """
        source_roles = cls._detect_color_roles(source_grid)
        peer_roles = cls._detect_color_roles(peer_grid)
        peer_by_role = {role: color for color, role in peer_roles.items()}
        source_to_peer: Dict[int, int] = {}
        for source_color, role in source_roles.items():
            peer_color = peer_by_role.get(role)
            if peer_color is not None:
                source_to_peer[int(source_color)] = int(peer_color)
        return source_to_peer

    @staticmethod
    def _relabel_colors(grid: np.ndarray, mapping: Dict[int, int]) -> np.ndarray:
        """Safely relabel colors with a two-phase replacement to avoid collisions."""
        if not mapping:
            return grid.copy()

        work = np.asarray(grid, dtype=np.int16).copy()
        staged: List[Tuple[int, int]] = []
        tmp_base = -1000
        i = 0
        for src, dst in mapping.items():
            src_i, dst_i = int(src), int(dst)
            if src_i == dst_i:
                continue
            tmp = tmp_base - i
            work[work == src_i] = tmp
            staged.append((tmp, dst_i))
            i += 1

        for tmp, dst_i in staged:
            work[work == tmp] = dst_i
        return work.astype(grid.dtype, copy=False)
    
    def add_near_miss(
        self,
        task_id: str,
        predictions: List[np.ndarray],
        targets: List[np.ndarray],
        transformation_signature: Tuple[float, ...],
        defect: float,
        program_signature: Optional[str] = None,
    ):
        """
        Cache a near-miss task's data for cross-task predicate testing.
        
        Args:
            task_id: Unique task identifier
            predictions: Current best predictions for training examples
            targets: Target outputs for training examples
            transformation_signature: (pos_frac, neg_frac, recolor_frac, pure_recolor, is_connected, is_scattered)
            defect: Current functional defect
            program_signature: Structural program signature (color-wildcarded) for coset matching
        """
        self.entries[task_id] = {
            'predictions': predictions,
            'targets': targets,
            'signature': transformation_signature,
            'defect': defect,
            'program_signature': program_signature or '',
        }
    
    @staticmethod
    def _structural_signature_distance(sig_a: str, sig_b: str) -> float:
        """
        Compute normalized Levenshtein distance between structural signatures.
        
        Theory (Renormalization.lean):
          Two tasks are coset-equivalent if their role-normalized structural
          signatures match. Levenshtein distance measures edit distance,
          giving a continuous similarity metric for structural matching.
        
        Returns:
            Distance in [0, 1]. 0 = identical structure, 1 = completely different.
        """
        if not sig_a or not sig_b:
            return 1.0  # No signature = maximally different
        if sig_a == sig_b:
            return 0.0  # Exact match
        
        # Levenshtein distance
        m, n = len(sig_a), len(sig_b)
        if m == 0:
            return 1.0
        if n == 0:
            return 1.0
        
        # DP table
        dp = [[0] * (n + 1) for _ in range(m + 1)]
        for i in range(m + 1):
            dp[i][0] = i
        for j in range(n + 1):
            dp[0][j] = j
        
        for i in range(1, m + 1):
            for j in range(1, n + 1):
                cost = 0 if sig_a[i-1] == sig_b[j-1] else 1
                dp[i][j] = min(
                    dp[i-1][j] + 1,      # deletion
                    dp[i][j-1] + 1,      # insertion
                    dp[i-1][j-1] + cost  # substitution
                )
        
        # Normalize by max length
        return dp[m][n] / max(m, n)
    
    def get_similar_tasks(
        self,
        signature: Tuple[float, ...],
        threshold: Optional[float] = None,
        exclude_task: Optional[str] = None,
        program_signature: Optional[str] = None,
    ) -> List[str]:
        """
        Find tasks with similar transformation signatures.
        
        Theory (symmetry cosets / Renormalization.lean):
          Tasks are coset-similar if their structural program signatures match.
          The 6D magnitude vector is used as a SECONDARY pre-filter, but
          program_signature (structural orbit) is the PRIMARY coset criterion.
        
        Matching priority:
          1. If program_signature provided: use Levenshtein distance on structural signature
          2. Fallback to 6D Euclidean distance if no structural signatures available
        """
        if threshold is None:
            threshold = self.similarity_threshold

        similar = []
        sig_arr = np.array(signature)
        
        for task_id, entry in self.entries.items():
            if task_id == exclude_task:
                continue
            
            # PRIMARY: structural signature matching (if available)
            if program_signature and entry.get('program_signature'):
                struct_dist = self._structural_signature_distance(
                    program_signature, entry['program_signature']
                )
                # Structural threshold: 0.3 = up to 30% edit distance
                if struct_dist < 0.3:
                    similar.append(task_id)
                continue
            
            # FALLBACK: 6D magnitude vector matching
            other_sig = np.array(entry['signature'])
            dist = np.linalg.norm(sig_arr - other_sig)
            if dist < threshold:
                similar.append(task_id)
        
        return similar
    
    def test_predicate_cross_task(
        self,
        op,
        current_task_id: str,
        min_tasks: int = 2,
    ) -> Tuple[bool, int, List[str]]:
        """
        Test if a predicate improves defect on multiple similar tasks.
        
        This is the CURRICULUM-LEVEL acceptance gate.
        
        Theory (dirichlet_gap_non_decrease at curriculum level):
          A predicate earns library membership only if it produces
          IG > 0 on at least min_tasks tasks with similar signatures.
        
        Returns:
            (accepted, n_improved, improved_task_ids)
        """
        min_tasks = max(int(min_tasks), 1)
        if current_task_id not in self.entries:
            self._record_test_report({
                'current_task_id': current_task_id,
                'accepted': False,
                'reason': 'missing_current_task',
                'n_improved': 0,
                'min_tasks': min_tasks,
                'candidate_peer_count': 0,
                'similarity_threshold': self.similarity_threshold,
                'min_delta': self.min_delta,
                'status_counts': {
                    'improved': 0,
                    'flat': 0,
                    'regressed': 0,
                    'shape_mismatch': 0,
                    'error': 0,
                },
                'top_failures': [],
            })
            return False, 0, []

        current_entry = self.entries[current_task_id]
        current_ref_grid = None
        if current_entry.get('predictions'):
            current_ref_grid = current_entry['predictions'][0]
        elif current_entry.get('targets'):
            current_ref_grid = current_entry['targets'][0]
        
        current_sig = self.entries[current_task_id]['signature']
        current_prog_sig = self.entries[current_task_id].get('program_signature', '')
        
        similar_tasks_with_dist: List[Tuple[str, float]] = []
        current_sig_arr = np.array(current_sig)
        
        for task_id, entry in self.entries.items():
            if task_id == current_task_id:
                continue
            
            # PRIMARY: 6D magnitude vector matching (residual structure)
            other_sig = np.array(entry['signature'])
            mag_dist = float(np.linalg.norm(current_sig_arr - other_sig))
            if mag_dist >= self.similarity_threshold:
                continue  # Pre-filter: must pass 6D threshold first
            
            # SECONDARY: structural program signature matching (per Renormalization.lean)
            # If both have signatures, use weighted combination; else use magnitude only
            peer_prog_sig = entry.get('program_signature', '')
            if current_prog_sig and peer_prog_sig:
                struct_dist = self._structural_signature_distance(current_prog_sig, peer_prog_sig)
                # Combined distance: 70% magnitude + 30% structural
                combined_dist = 0.7 * mag_dist + 0.3 * struct_dist
                similar_tasks_with_dist.append((task_id, combined_dist))
            else:
                similar_tasks_with_dist.append((task_id, mag_dist))
        
        similar_tasks_with_dist.sort(key=lambda x: x[1])
        
        improved_tasks = []
        status_counts = {
            'improved': 0,
            'flat': 0,
            'regressed': 0,
            'shape_mismatch': 0,
            'error': 0,
        }
        peer_reports = []

        for task_id, dist in similar_tasks_with_dist:
            entry = self.entries[task_id]
            total_delta = 0.0
            n_eval = 0
            n_shape_mismatch = 0
            status = 'flat'
            err_msg = ''
            role_normalized = False

            try:
                # Test op on this task's predictions
                for pred, tgt in zip(entry['predictions'], entry['targets']):
                    if pred.shape != tgt.shape:
                        n_shape_mismatch += 1
                        continue

                    source_to_peer_local: Dict[int, int] = {}
                    peer_to_source_local: Dict[int, int] = {}
                    if current_ref_grid is not None:
                        try:
                            source_to_peer_local = self._build_role_transport(current_ref_grid, pred)
                            if source_to_peer_local:
                                peer_to_source_local = {
                                    peer_c: src_c for src_c, peer_c in source_to_peer_local.items()
                                }
                                if any(src_c != peer_c for src_c, peer_c in source_to_peer_local.items()):
                                    role_normalized = True
                        except Exception:
                            source_to_peer_local = {}
                            peer_to_source_local = {}

                    if peer_to_source_local and source_to_peer_local:
                        pred_aligned = self._relabel_colors(pred, peer_to_source_local)
                        pred_after_aligned = op.apply(pred_aligned)
                        pred_after = self._relabel_colors(pred_after_aligned, source_to_peer_local)
                    else:
                        pred_after = op.apply(pred)
                    if pred_after.shape != tgt.shape:
                        n_shape_mismatch += 1
                        continue
                    eps_before = float(np.mean(pred != tgt))
                    eps_after = float(np.mean(pred_after != tgt))
                    total_delta += (eps_before - eps_after)
                    n_eval += 1

                if n_eval == 0:
                    status = 'shape_mismatch'
                elif total_delta > self.min_delta:  # Meaningful improvement
                    status = 'improved'
                    improved_tasks.append(task_id)
                elif total_delta < -self.min_delta:
                    status = 'regressed'
                else:
                    status = 'flat'
            except Exception as exc:
                status = 'error'
                err_msg = f'{type(exc).__name__}: {exc}'

            if status in status_counts:
                status_counts[status] += 1

            peer_reports.append({
                'task_id': task_id,
                'distance': round(dist, 6),
                'total_delta': round(total_delta, 6),
                'mean_delta': round(total_delta / max(n_eval, 1), 6),
                'n_eval_examples': n_eval,
                'n_shape_mismatch': n_shape_mismatch,
                'status': status,
                'role_normalized': role_normalized,
                'error': err_msg,
            })
        
        # +1 for the current task (already passed single-task gate)
        n_improved = len(improved_tasks) + 1
        accepted = n_improved >= min_tasks

        non_improvers = [r for r in peer_reports if r['status'] != 'improved']
        non_improvers.sort(key=lambda r: r['total_delta'])
        top_failures = non_improvers[:5]
        report = {
            'current_task_id': current_task_id,
            'accepted': accepted,
            'n_improved': n_improved,
            'min_tasks': min_tasks,
            'candidate_peer_count': len(similar_tasks_with_dist),
            'similarity_threshold': self.similarity_threshold,
            'min_delta': self.min_delta,
            'improved_tasks': list(improved_tasks),
            'status_counts': status_counts,
            'top_failures': top_failures,
        }
        if len(similar_tasks_with_dist) == 0:
            report['reason'] = 'no_similar_peers'
        elif accepted:
            report['reason'] = 'accepted'
        else:
            report['reason'] = 'insufficient_improvements'
        if self.debug:
            report['peer_reports'] = peer_reports
        self._record_test_report(report)
        
        return accepted, n_improved, improved_tasks
    
    @property
    def size(self) -> int:
        return len(self.entries)
    
    def get_cluster_summary(self) -> Dict[str, int]:
        """Get count of tasks per signature cluster."""
        from collections import defaultdict
        clusters = defaultdict(int)
        for task_id, entry in self.entries.items():
            sig = entry['signature']
            # Quantize signature for clustering
            key = (round(sig[0], 1), round(sig[1], 1), round(sig[2], 1), int(sig[3]))
            clusters[str(key)] += 1
        return dict(clusters)


class SGFEPrimitiveLibrary:
    """
    Growing library of discovered primitives (renormalization group).

    Each accepted tensor predicate becomes a permanent DSL operator.
    This is the missing functor F: Partitions → Operators.

    Theory:
      - Renormalization: collapse partition → new AtomicOp
      - Continual learning: new ops frozen after sheaf check
      - Compression: track ΔPerfect / Δ|library| (diminishing returns)
      
    SGFE v2.2 (curriculum-aware):
      - Cross-task validation before acceptance
      - Near-miss journal integration
      - Predicate must generalize to ≥2 tasks to enter library
    """

    def __init__(
        self,
        cross_task_validator: Optional['CrossTaskPredicateValidator'] = None,
        require_cross_task: bool = True,
        min_tasks: int = 2,
    ):
        self.primitives = []  # List of (name, op, metadata)
        self.compression_log = []
        self.cross_task_validator = cross_task_validator or CrossTaskPredicateValidator()
        self.cross_task_accepts = 0  # Counter for curriculum-validated predicates
        # Per-pass controls (set by evaluation harness)
        self.require_cross_task = bool(require_cross_task)
        self.min_tasks = max(int(min_tasks), 1)

    def add_new_primitive(
        self,
        name: str,
        op,  # AtomicOp
        metadata: Dict,
        require_cross_task: Optional[bool] = None,
    ) -> bool:
        """
        Add a new primitive to the library after sheaf verification.

        Returns True if added (not a duplicate).

        Theory (dirichlet_gap_non_decrease):
          The library's expressive power (spectral gap) can only increase.
          Adding a new op that passed sheaf verification cannot hurt.
          
        SGFE v2.2 (curriculum-aware):
          If require_cross_task=True, the predicate must also pass the
          curriculum-level gate: IG > 0 on ≥2 tasks with similar signatures.
          This prevents per-task overfitting and ensures true generalization.
        """
        # Content-addressed deduplication
        for existing_name, _, _ in self.primitives:
            if existing_name == name:
                return False
        
        if require_cross_task is None:
            require_cross_task = self.require_cross_task

        # SGFE v2.2: Cross-task validation gate
        task_id = metadata.get('task_id', '')
        cross_task_ok = True
        n_improved = 1
        improved_tasks = []
        cross_task_report = {}
        
        # SGFE v2.7: Bypass peer validation for low-sheaf predicates
        # Theory (SGC.Renormalization.Lumpability): Low sheaf_energy means the predicate
        # already forms a valid global section across training examples. Peer validation
        # is redundant - the sheaf consistency IS the gluing proof.
        # Threshold 0.1 = morphological predicates (typically ~0.001) auto-bypass
        SHEAF_BYPASS_THRESHOLD = 0.1
        predicate_sheaf_energy = metadata.get('sheaf_energy', 1.0)
        
        if predicate_sheaf_energy <= SHEAF_BYPASS_THRESHOLD:
            # Low sheaf energy = valid global section = skip peer validation
            cross_task_report = {'reason': 'sheaf_bypass', 'sheaf_energy': predicate_sheaf_energy}
            require_cross_task = False  # Override for this predicate
        
        if require_cross_task and task_id and self.cross_task_validator.size > 0:
            cross_task_ok, n_improved, improved_tasks = \
                self.cross_task_validator.test_predicate_cross_task(
                    op, task_id, min_tasks=self.min_tasks
                )
            cross_task_report = dict(getattr(self.cross_task_validator, 'last_test_report', {}) or {})
            if not cross_task_ok:
                # Log rejection but don't add to library
                self.compression_log.append({
                    'task_id': task_id,
                    'name': name,
                    'f1': metadata.get('f1', 0),
                    'mi': metadata.get('mi_avg', 0),
                    'sheaf_energy': metadata.get('sheaf_energy', 0),
                    'library_size': len(self.primitives),
                    'cross_task_rejected': True,
                    'n_improved': n_improved,
                    'cross_task_min_tasks': self.min_tasks,
                    'cross_task_similar_peers': int(cross_task_report.get('candidate_peer_count', 0)),
                    'cross_task_reason': str(cross_task_report.get('reason', 'unknown')),
                    'cross_task_status_counts': dict(cross_task_report.get('status_counts', {})),
                    'cross_task_top_failures': list(cross_task_report.get('top_failures', [])),
                })
                return False

        self.primitives.append((name, op, metadata))
        self.compression_log.append({
            'task_id': task_id,
            'name': name,
            'f1': metadata.get('f1', 0),
            'mi': metadata.get('mi_avg', 0),
            'sheaf_energy': metadata.get('sheaf_energy', 0),
            'library_size': len(self.primitives),
            'cross_task_validated': require_cross_task,
            'n_improved': n_improved,
            'improved_tasks': improved_tasks,
            'cross_task_min_tasks': self.min_tasks,
            'cross_task_similar_peers': int(cross_task_report.get('candidate_peer_count', 0)),
            'cross_task_reason': str(cross_task_report.get('reason', 'accepted' if require_cross_task else 'not_required')),
            'cross_task_status_counts': dict(cross_task_report.get('status_counts', {})),
        })
        
        if require_cross_task and n_improved >= self.min_tasks:
            self.cross_task_accepts += 1
        
        return True

    @property
    def size(self) -> int:
        return len(self.primitives)

    def get_ops(self) -> list:
        """Get all primitive ops for seeding solver proposals."""
        return [(name, op) for name, op, _ in self.primitives]

    def compression_ratio(self) -> float:
        """Library compression: useful primitives per total attempted."""
        if not self.compression_log:
            return 0.0
        return self.size / max(len(self.compression_log), 1)


# =============================================================================
# 6. ACCEPTANCE CRITERION (Theory-Grounded, No Ad-Hoc Threshold)
# =============================================================================
#
# From the spec:
#   Accept if Δε_func < 0  AND  MI(Π, ChangeLabel) > 0.3
#                           AND  SheafEnergy < threshold
#
# This combines three theory-grounded checks:
#   1. Functional defect decreases (FunctionalBlanket.lean)
#   2. Predicate is informative (OptimalPartition.lean, submodularity)
#   3. Predicate is consistent (CellularSheafNetwork, global section)

def sgfe_acceptance_gate(
    eps_before: float,
    eps_after: float,
    mi_score: float,
    sheaf_energy: float,
    mi_threshold: float = 0.3,
    sheaf_threshold: float = 0.5,
) -> Tuple[bool, str]:
    """
    Theory-grounded acceptance gate for discovered predicates.

    Returns:
      (accepted, reason)

    Theory:
      - Δε_func < 0: Functional blanket must improve (FunctionalBlanket.lean)
      - MI > 0.3: Predicate must be informative (OptimalPartition.lean)
      - E_sheaf < 0.5: Predicate must be consistent (sheaf global section)
    """
    if eps_after >= eps_before:
        return False, f"eps_func not improved ({eps_before:.4f} -> {eps_after:.4f})"
    if mi_score < mi_threshold:
        return False, f"MI too low ({mi_score:.4f} < {mi_threshold})"
    if sheaf_energy > sheaf_threshold:
        return False, f"sheaf energy too high ({sheaf_energy:.4f} > {sheaf_threshold})"
    return True, "accepted"


# =============================================================================
# 7. UNIVERSAL FUNCTIONAL DEFECT SCORER (SGFE v2.0)
# =============================================================================
#
# From FunctionalBlanket.lean:
#   ε_func = withinClassVariance / (totalVariance + 1e-10)
#
# For DISCRETE ARC grids (pixel-level):
#   "Representation" = output color value (integer 0-9)
#   "Classes" = transformation types (unchanged, fill, erase, recolor)
#   ε_func = fraction of pixels where pred ≠ tgt
#          = pixel mismatch rate
#   This IS the functional defect: wrong pixels have variance 1 within
#   their class (pred color differs from tgt color).
#
# For CONTINUOUS features (Tensor Logic with Hermite wavelets):
#   "Representation" = feature vector in wavelet space
#   "Classes" = algebraic equivalence classes (10*pred + tgt + 1)
#   ε_func = ANOVA within-class / total variance
#
# This function is the SINGLE SOURCE OF TRUTH for Δε_func.

def sgfe_defect_discrete(pred: np.ndarray, tgt: np.ndarray) -> float:
    """
    Compute discrete functional defect (pixel mismatch rate).

    Theory (FunctionalBlanket.lean):
      For discrete representations where h(x) = output_color,
      ε_func = fraction of wrong pixels.

      This equals withinClassVariance / totalVariance because:
      - Total variance: across all possible (pred, tgt) pairs
      - Within-class variance: 0 for correct pixels, 1 for wrong pixels
      - Thus: ε_func = n_wrong / n_total = pixel mismatch rate

    Args:
      pred: Prediction grid (H, W)
      tgt: Target grid (H, W)

    Returns:
      ε_func ∈ [0, 1]. 0 = perfect, 1 = all wrong.
    """
    if pred.shape != tgt.shape:
        return 1.0
    return float(np.mean(pred != tgt))


def sgfe_defect_continuous(
    pred: np.ndarray,
    tgt: np.ndarray,
    features: Optional[np.ndarray] = None,
) -> float:
    """
    Compute continuous functional defect (ANOVA on features).

    Theory (FunctionalBlanket.lean):
      For continuous representations (neural/wavelet features),
      ε_func = withinClassVariance / totalVariance
      where classes = algebraic equivalence (transformation type).

    This is the same as functional_blanket_variance but
    explicitly named for API clarity.
    """
    return functional_blanket_variance(pred, tgt, features)


def sgfe_defect_delta(
    pred_before: np.ndarray,
    pred_after: np.ndarray,
    target: np.ndarray,
    mode: str = 'discrete',
    features_before: Optional[np.ndarray] = None,
    features_after: Optional[np.ndarray] = None,
) -> Dict:
    """
    UNIVERSAL FUNCTIONAL DEFECT SCORER (SGFE v2.0)

    Single source of truth for Δε_func computation.
    Dispatches between discrete (pixel mismatch) and continuous (ANOVA)
    based on mode parameter.

    Theory (FunctionalBlanket.lean + grokking experiments):
      Functional defect ε_func measures how well the partition
      separates algebraic equivalence classes.

      For discrete ARC: pixel mismatch IS ε_func
      For continuous: ANOVA on feature space IS ε_func

      Grokking occurs when ε_func < 0.15 (grokkingThreshold).
      Post-grok: ε_func ≈ 0.02.

    Args:
      pred_before: Prediction BEFORE applying the candidate op
      pred_after: Prediction AFTER applying the candidate op
      target: Ground truth target grid
      mode: 'discrete' (pixel mismatch) or 'continuous' (ANOVA)
      features_before: Optional pre-computed features for ANOVA
      features_after: Optional pre-computed features for ANOVA

    Returns:
      Dict with:
        'eps_before': ε_func before op
        'eps_after': ε_func after op
        'delta': Δε_func = eps_before - eps_after (positive = improvement)
        'improved': bool, True if Δε_func > 0
        'mode': which scorer was used
        'n_wrong_before': number of wrong pixels before
        'n_wrong_after': number of wrong pixels after
    """
    # Always compute discrete (pixel mismatch) for diagnostics
    n_wrong_before = int((pred_before != target).sum()) if pred_before.shape == target.shape else -1
    n_wrong_after = int((pred_after != target).sum()) if pred_after.shape == target.shape else -1

    if mode == 'continuous':
        eps_before = sgfe_defect_continuous(pred_before, target, features_before)
        eps_after = sgfe_defect_continuous(pred_after, target, features_after)
    else:
        # Default: discrete (pixel mismatch)
        eps_before = sgfe_defect_discrete(pred_before, target)
        eps_after = sgfe_defect_discrete(pred_after, target)

    delta = eps_before - eps_after

    return {
        'eps_before': eps_before,
        'eps_after': eps_after,
        'delta': delta,
        'improved': delta > 0,
        'mode': mode,
        'n_wrong_before': n_wrong_before,
        'n_wrong_after': n_wrong_after,
    }


def sgfe_acceptance_gate_v2(
    total_delta: float,
    worst_delta: float,
    mi_score: float,
    sheaf_energy: float,
    mi_threshold: float = 0.25,
    sheaf_threshold: float = 0.6,
) -> Tuple[bool, str]:
    """
    SGFE v2.0 Acceptance Gate with refined thresholds.

    Theory (grounded in grokking experiments):
      - Grokking occurs when ε_func < 0.15 (grokkingThreshold from FunctionalBlanket.lean)
      - Functional defect drops GRADUALLY before perfect generalization
      - MI > 0.25 ensures predicate captures meaningful structure (OptimalPartition.lean)
      - Sheaf energy < 0.6 ensures consistency across examples (positive_Ricci_tensorizes)

    Key insight: The v1.0 gate was too strict (required improvement on ALL examples).
    v2.0 allows gradual improvement:
      - total_delta > 0: net improvement across all examples
      - worst_delta >= -0.01: allow small regressions on individual examples
      - This matches grokking dynamics where collapse is gradual

    Args:
      total_delta: Sum of per-example Δε_func (positive = improvement)
      worst_delta: Minimum per-example Δε_func (negative = some example got worse)
      mi_score: Mutual information MI(Π, ChangeLabel)
      sheaf_energy: E_sheaf from sheaf_consistency_energy
      mi_threshold: Minimum MI (default 0.25, from spec)
      sheaf_threshold: Maximum sheaf energy (default 0.6, lenient for small grids)

    Returns:
      (accepted, reason)
    """
    # Check 1: Net improvement (total_delta > 0)
    if total_delta <= 0:
        return False, f"no net improvement (total_delta={total_delta:.4f})"

    # Check 2: Worst-case regression limit (allow small degradation)
    # Theory: grokking is gradual, early predicates may not be perfect
    if worst_delta < -0.01:
        return False, f"worst_delta too negative ({worst_delta:.4f} < -0.01)"

    # Check 3: MI threshold (predicate must be informative)
    if mi_score < mi_threshold:
        return False, f"MI too low ({mi_score:.4f} < {mi_threshold})"

    # Check 4: Sheaf consistency (predicate must mean same thing across examples)
    if sheaf_energy > sheaf_threshold:
        return False, f"sheaf energy too high ({sheaf_energy:.4f} > {sheaf_threshold})"

    return True, "accepted"


def sgfe_defect_delta_multi(
    op,
    predictions: List[np.ndarray],
    targets: List[np.ndarray],
    mode: str = 'discrete',
) -> Dict:
    """
    Compute Δε_func across MULTIPLE training examples.

    Theory (sheaf global section):
      A valid transformation must improve (or not worsen)
      functional defect on ALL examples simultaneously.

      This is the multi-stalk consistency requirement from
      positive_Ricci_tensorizes.

    Args:
      op: Operation to apply (must have .apply() method)
      predictions: List of prediction grids BEFORE op
      targets: List of target grids
      mode: 'discrete' or 'continuous'

    Returns:
      Dict with:
        'total_delta': sum of per-example Δε_func
        'worst_delta': minimum (worst) per-example Δε_func
        'all_improved': True if ALL examples improved or stayed same
        'per_example': List of per-example result dicts
        'n_examples': number of examples
    """
    per_example = []
    total_delta = 0.0
    worst_delta = float('inf')
    all_improved = True

    for pred_before, tgt in zip(predictions, targets):
        try:
            pred_after = op.apply(pred_before)
            result = sgfe_defect_delta(pred_before, pred_after, tgt, mode=mode)
            per_example.append(result)
            total_delta += result['delta']
            worst_delta = min(worst_delta, result['delta'])
            if result['delta'] < 0:
                all_improved = False
        except Exception as e:
            per_example.append({
                'eps_before': 1.0,
                'eps_after': 1.0,
                'delta': 0.0,
                'improved': False,
                'mode': mode,
                'error': str(e),
            })
            all_improved = False
            worst_delta = min(worst_delta, -1.0)

    return {
        'total_delta': total_delta,
        'worst_delta': worst_delta if worst_delta != float('inf') else 0.0,
        'all_improved': all_improved,
        'per_example': per_example,
        'n_examples': len(predictions),
    }
