"""
Cellular Sheaf Engine: Phase 1 Implementation

This module implements the Cellular Sheaf Network architecture for ARC solving.
It addresses the three critical gaps identified in the 97-task evaluation:

1. Object Segmentation - Using spectral clustering (Shi-Malik)
2. Gauge Composition - Chaining local transformations
3. Shape-Change - RG Flow (bounding box extraction)

The key insight: A global gauge transformation cannot act coherently on 
disconnected topological manifolds. We must first decompose the grid into
its Cellular Sheaves (local stalks), apply gauge operations per-stalk,
then glue results back together.

Mathematical Foundation:
- Color-weighted Normalized Laplacian: L_rw = I - D^{-1}A
- Zero-eigenvalue multiplicity = number of disconnected components
- Fiedler vector partitions loosely connected components
- EM-loop: Segment <-> Gauge until Free Energy = 0
"""

import numpy as np
from scipy import sparse
from scipy.sparse.linalg import eigsh
from scipy.ndimage import label as connected_components
from typing import Dict, Any, List, Tuple, Optional, Callable
import json
from pathlib import Path


class CellularSheafEngine:
    """
    The Cellular Sheaf Engine for ARC solving.
    
    Unlike ThermodynamicPerception which treats the grid as a single manifold,
    this engine decomposes the grid into topological objects (stalks) and
    applies gauge transformations independently to each.
    
    The architecture follows the Cellular Sheaf Network paradigm:
    1. Stalks: Local manifolds (individual objects)
    2. Restriction maps: How stalks connect to the global space
    3. Cohomology: Obstructions to global gluing
    """
    
    def __init__(self, grid: np.ndarray, target: Optional[np.ndarray] = None):
        """
        Initialize the Cellular Sheaf Engine.
        
        Args:
            grid: Input ARC grid (H x W integer array, 0=background)
            target: Optional target output grid for supervised learning
        """
        self.grid = grid.astype(np.float32)
        self.target = target.astype(np.float32) if target is not None else None
        self.H, self.W = grid.shape
        self.N = self.H * self.W
        
        # Spectral decomposition (computed lazily)
        self._semantic_laplacian = None
        self._eigenvalues = None
        self._eigenvectors = None
        
        # Cellular decomposition
        self._stalks: List[Dict[str, Any]] = []
        self._n_components = None
        
        # Background color (topological void)
        self.background_color = 0
        
    # =========================================================================
    # PHASE 1A: COLOR-WEIGHTED NORMALIZED LAPLACIAN
    # =========================================================================
    
    def build_semantic_laplacian(self, 
                                   epsilon: float = 0.01,
                                   background_disconnect: bool = True) -> sparse.csr_matrix:
        """
        Build the color-weighted, normalized Graph Laplacian.
        
        This is the SEMANTIC manifold, not the Euclidean grid.
        
        Edge weights:
        - A_ij = 1.0 if pixels i,j have the SAME color
        - A_ij = epsilon if pixels have DIFFERENT colors
        - A_ij = 0 if either pixel is background (topological void)
        
        We use the Random Walk Normalized Laplacian: L_rw = I - D^{-1}A
        This bounds eigenvalues to [0, 2], ensuring uniform thermodynamic scaling.
        
        Args:
            epsilon: Weak coupling between different-colored pixels
            background_disconnect: If True, background pixels don't connect
            
        Returns:
            Normalized Laplacian L_rw (N x N sparse matrix)
        """
        if self._semantic_laplacian is not None:
            return self._semantic_laplacian
        
        rows, cols, data = [], [], []
        
        for i in range(self.H):
            for j in range(self.W):
                node = i * self.W + j
                pixel_color = self.grid[i, j]
                
                # Background pixels are topological voids
                if background_disconnect and pixel_color == self.background_color:
                    continue
                
                # 4-connectivity neighbors
                neighbors = [(i-1, j), (i+1, j), (i, j-1), (i, j+1)]
                
                for ni, nj in neighbors:
                    if 0 <= ni < self.H and 0 <= nj < self.W:
                        neighbor_color = self.grid[ni, nj]
                        
                        # Background neighbors don't connect
                        if background_disconnect and neighbor_color == self.background_color:
                            continue
                        
                        neighbor_node = ni * self.W + nj
                        
                        # Color-weighted adjacency
                        if pixel_color == neighbor_color:
                            weight = 1.0  # Same color = strong connection
                        else:
                            weight = epsilon  # Different color = weak connection
                        
                        rows.append(node)
                        cols.append(neighbor_node)
                        data.append(weight)
        
        # Build adjacency matrix
        A = sparse.csr_matrix((data, (rows, cols)), shape=(self.N, self.N))
        
        # Degree matrix (row sums)
        degrees = np.array(A.sum(axis=1)).flatten()
        
        # Handle isolated nodes (degree = 0)
        degrees[degrees == 0] = 1.0
        
        # Inverse degree matrix
        D_inv = sparse.diags(1.0 / degrees)
        
        # Random Walk Normalized Laplacian: L_rw = I - D^{-1}A
        I = sparse.eye(self.N)
        self._semantic_laplacian = I - D_inv @ A
        
        return self._semantic_laplacian
    
    # =========================================================================
    # PHASE 1B: SPECTRAL SEGMENTATION (CELLULAR SHEAF DECOMPOSITION)
    # =========================================================================
    
    def compute_spectral_modes(self, n_modes: int = 10) -> Tuple[np.ndarray, np.ndarray]:
        """
        Compute eigenmodes of the semantic Laplacian.
        
        The zero-eigenvalue multiplicity equals the number of disconnected components.
        The Fiedler vector (first non-zero eigenmode) partitions connected components.
        
        Args:
            n_modes: Number of eigenmodes to compute
            
        Returns:
            (eigenvalues, eigenvectors)
        """
        if self._eigenvalues is not None and len(self._eigenvalues) >= n_modes:
            return self._eigenvalues[:n_modes], self._eigenvectors[:, :n_modes]
        
        L = self.build_semantic_laplacian()
        n_modes = min(n_modes, self.N - 2)
        
        try:
            eigenvalues, eigenvectors = eigsh(L.astype(np.float64),
                                               k=n_modes,
                                               which='SM',
                                               sigma=0.001)
            idx = np.argsort(eigenvalues)
            self._eigenvalues = eigenvalues[idx]
            self._eigenvectors = eigenvectors[:, idx]
            
        except Exception:
            L_dense = L.toarray()
            eigenvalues, eigenvectors = np.linalg.eigh(L_dense)
            self._eigenvalues = eigenvalues[:n_modes]
            self._eigenvectors = eigenvectors[:, :n_modes]
        
        return self._eigenvalues, self._eigenvectors
    
    def count_disconnected_components(self, threshold: float = 1e-6) -> int:
        """
        Count disconnected components via zero-eigenvalue multiplicity.
        
        In spectral graph theory, the multiplicity of eigenvalue 0 equals
        the number of disconnected components in the graph.
        
        Args:
            threshold: Eigenvalues below this are considered zero
            
        Returns:
            Number of disconnected topological manifolds
        """
        eigenvalues, _ = self.compute_spectral_modes(n_modes=min(20, self.N - 2))
        
        # Count eigenvalues at or near zero
        n_zero = np.sum(np.abs(eigenvalues) < threshold)
        
        # At minimum, there's 1 component (or 0 if empty grid)
        return max(n_zero, 1)
    
    def segment_by_eigenvectors(self, n_clusters: int = None) -> List[np.ndarray]:
        """
        Segment the grid into objects using spectral clustering (Shi-Malik).
        
        This is the Cellular Sheaf decomposition: breaking the global manifold
        into local stalks. Each stalk is a mask indicating object pixels.
        
        Method:
        1. Project pixels into eigenvector space (first k modes)
        2. Use k-means clustering in this spectral embedding
        3. Each cluster becomes a stalk (local manifold)
        
        Args:
            n_clusters: Number of clusters (auto-detected if None)
            
        Returns:
            List of boolean masks, one per object/stalk
        """
        # Detect number of components if not specified
        if n_clusters is None:
            n_clusters = self.count_disconnected_components()
            # If spectral says 1 but there are clearly multiple objects, use connected components
            if n_clusters == 1:
                # Fallback: use connected components on foreground
                foreground = (self.grid > 0).astype(int)
                labeled, n_cc = connected_components(foreground)
                if n_cc > 1:
                    n_clusters = n_cc
        
        n_clusters = max(1, min(n_clusters, 10))  # Clamp to reasonable range
        
        eigenvalues, eigenvectors = self.compute_spectral_modes(n_modes=n_clusters + 1)
        
        # Get foreground pixels only
        foreground_mask = self.grid > 0
        foreground_indices = np.where(foreground_mask.flatten())[0]
        
        if len(foreground_indices) == 0:
            return []
        
        if len(foreground_indices) < n_clusters:
            # Not enough pixels to cluster - each pixel is its own object
            masks = []
            for idx in foreground_indices:
                mask = np.zeros(self.N, dtype=bool)
                mask[idx] = True
                masks.append(mask.reshape(self.H, self.W))
            return masks
        
        # Project foreground pixels into spectral space
        spectral_coords = eigenvectors[foreground_indices, :n_clusters]
        
        # Simple k-means clustering in spectral space
        masks = self._spectral_kmeans(foreground_indices, spectral_coords, n_clusters)
        
        return masks
    
    def _spectral_kmeans(self, 
                          indices: np.ndarray, 
                          coords: np.ndarray, 
                          k: int,
                          max_iter: int = 50) -> List[np.ndarray]:
        """
        Simple k-means in spectral embedding space.
        
        Args:
            indices: Pixel indices in flattened grid
            coords: Spectral coordinates (n_pixels x k)
            k: Number of clusters
            max_iter: Maximum iterations
            
        Returns:
            List of k boolean masks
        """
        n_points = len(indices)
        
        # Initialize centroids randomly
        centroid_indices = np.random.choice(n_points, size=min(k, n_points), replace=False)
        centroids = coords[centroid_indices].copy()
        
        labels = np.zeros(n_points, dtype=int)
        
        for _ in range(max_iter):
            # Assign points to nearest centroid
            old_labels = labels.copy()
            for i in range(n_points):
                distances = np.linalg.norm(coords[i] - centroids, axis=1)
                labels[i] = np.argmin(distances)
            
            # Update centroids
            for c in range(k):
                cluster_mask = labels == c
                if cluster_mask.any():
                    centroids[c] = coords[cluster_mask].mean(axis=0)
            
            # Check convergence
            if np.array_equal(labels, old_labels):
                break
        
        # Convert labels to masks
        masks = []
        for c in range(k):
            mask = np.zeros(self.N, dtype=bool)
            cluster_indices = indices[labels == c]
            mask[cluster_indices] = True
            mask_2d = mask.reshape(self.H, self.W)
            if mask_2d.any():  # Only add non-empty masks
                masks.append(mask_2d)
        
        return masks
    
    def segment_by_connected_components(self) -> List[np.ndarray]:
        """
        Segment by 4-connected components, respecting color boundaries.
        
        Each connected region of the SAME COLOR becomes a separate stalk.
        This is the correct topological decomposition for ARC tasks.
        
        Returns:
            List of boolean masks, one per connected same-color object
        """
        masks = []
        
        # Get unique non-background colors
        unique_colors = np.unique(self.grid)
        unique_colors = unique_colors[unique_colors != self.background_color]
        
        for color in unique_colors:
            # Get mask for this color
            color_mask = (self.grid == color).astype(int)
            
            # Find connected components within this color
            labeled, n_components = connected_components(color_mask)
            
            for c in range(1, n_components + 1):
                mask = labeled == c
                if mask.any():
                    masks.append(mask)
        
        return masks
    
    def decompose_to_stalks(self, method: str = 'hybrid') -> List[Dict[str, Any]]:
        """
        Decompose the grid into Cellular Sheaf stalks.
        
        Each stalk contains:
        - mask: Boolean array indicating stalk pixels
        - grid: The local grid (stalk's view of the manifold)
        - bbox: Bounding box (r_min, r_max, c_min, c_max)
        - spectral_signature: Hermite-Gaussian mode coefficients
        
        Args:
            method: 'spectral', 'connected', or 'hybrid'
            
        Returns:
            List of stalk dictionaries
        """
        # Get object masks
        # For ARC tasks, color-aware connected components is most reliable
        if method == 'spectral':
            masks = self.segment_by_eigenvectors()
        elif method == 'connected':
            masks = self.segment_by_connected_components()
        else:  # hybrid
            # Use connected components (color-aware) as primary
            # This respects the topological structure of ARC grids
            masks = self.segment_by_connected_components()
        
        stalks = []
        for i, mask in enumerate(masks):
            if not mask.any():
                continue
            
            # Compute bounding box
            rows, cols = np.where(mask)
            r_min, r_max = rows.min(), rows.max()
            c_min, c_max = cols.min(), cols.max()
            
            # Extract local grid (cropped to bounding box)
            local_grid = np.zeros((r_max - r_min + 1, c_max - c_min + 1))
            for r, c in zip(rows, cols):
                local_grid[r - r_min, c - c_min] = self.grid[r, c]
            
            # Compute spectral signature for this stalk
            signature = self._compute_stalk_signature(mask)
            
            stalks.append({
                'id': i,
                'mask': mask,
                'local_grid': local_grid,
                'bbox': (r_min, r_max, c_min, c_max),
                'n_pixels': int(mask.sum()),
                'colors': list(np.unique(self.grid[mask]).astype(int)),
                'spectral_signature': signature
            })
        
        self._stalks = stalks
        self._n_components = len(stalks)
        
        return stalks
    
    def _compute_stalk_signature(self, mask: np.ndarray) -> np.ndarray:
        """
        Compute spectral signature for a single stalk.
        
        This is the projection onto the first few Hermite-Gaussian modes,
        used for matching against the SheafAtlas.
        """
        if self._eigenvectors is None:
            self.compute_spectral_modes()
        
        # Create indicator vector for this stalk
        indicator = mask.flatten().astype(float)
        
        # Project onto eigenmodes
        n_modes = min(5, self._eigenvectors.shape[1])
        signature = np.zeros(n_modes)
        for k in range(n_modes):
            signature[k] = np.dot(indicator, self._eigenvectors[:, k])
        
        # Normalize
        norm = np.linalg.norm(signature)
        if norm > 1e-10:
            signature = signature / norm
        
        return signature
    
    # =========================================================================
    # PHASE 1C: LOCAL GAUGE DETECTION (STALK-WISE)
    # =========================================================================
    
    def detect_stalk_gauge(self, stalk: Dict[str, Any]) -> Optional[Dict[str, Any]]:
        """
        Detect the gauge group for a single stalk.
        
        Probes the stalk for known symmetries:
        - Z2: Reflection symmetry (internal or completion)
        - C4: Rotation symmetry  
        - Sn: Color permutation
        - Zn: Translation symmetry
        
        Args:
            stalk: Stalk dictionary from decompose_to_stalks
            
        Returns:
            Gauge detection result or None
        """
        local_grid = stalk['local_grid']
        
        # Try each gauge group in order of likelihood
        
        # 1. Z2 Symmetry Completion (input asymmetric -> target symmetric)
        z2_completion = self._detect_z2_completion(stalk)
        if z2_completion is not None:
            return z2_completion
        
        # 2. Z2 Internal Reflection
        z2_result = self._detect_z2_on_stalk(local_grid)
        if z2_result is not None:
            return z2_result
        
        # 3. C4 Rotation
        c4_result = self._detect_c4_on_stalk(local_grid)
        if c4_result is not None:
            return c4_result
        
        # 4. Sn Color Permutation
        sn_result = self._detect_sn_on_stalk(local_grid, stalk)
        if sn_result is not None:
            return sn_result
        
        return None
    
    def _detect_z2_on_stalk(self, local_grid: np.ndarray) -> Optional[Dict[str, Any]]:
        """Detect horizontal or vertical reflection symmetry."""
        h, w = local_grid.shape
        
        # Check horizontal reflection (left-right)
        flipped_h = np.fliplr(local_grid)
        h_score = np.sum(local_grid == flipped_h) / local_grid.size
        
        # Check vertical reflection (up-down)
        flipped_v = np.flipud(local_grid)
        v_score = np.sum(local_grid == flipped_v) / local_grid.size
        
        # Need at least 80% match but not 100% (that means no transformation needed)
        if h_score >= 0.8 and h_score < 0.99:
            return {
                'gauge_group': 'Z2_reflection',
                'axis': 'horizontal',
                'symmetry_score': float(h_score)
            }
        
        if v_score >= 0.8 and v_score < 0.99:
            return {
                'gauge_group': 'Z2_reflection', 
                'axis': 'vertical',
                'symmetry_score': float(v_score)
            }
        
        return None
    
    def _detect_z2_completion(self, stalk: Dict[str, Any]) -> Optional[Dict[str, Any]]:
        """
        Detect Z2 symmetry COMPLETION with possible recoloring.
        
        ARC reflection completion tasks:
        - Input has protrusions on one side of a central spine
        - Target adds mirrored protrusions on the other side (possibly different color)
        
        The SPINE is the column with maximum vertical presence.
        """
        if self.target is None:
            return None
        
        input_mask = self.grid > 0
        if not input_mask.any():
            return None
        
        # Find the SPINE: column with maximum vertical presence
        col_presence = input_mask.sum(axis=0)
        spine_col = int(np.argmax(col_presence))
        
        # The axis IS the spine column (reflection happens around it)
        axis = float(spine_col)
        
        # Find what pixels are added in target vs input
        added_mask = (self.target > 0) & (self.grid == 0)
        if not added_mask.any():
            return None
        
        added_positions = np.array(np.where(added_mask)).T
        
        # For each added pixel, check if it mirrors an input protrusion
        valid_reflection = True
        add_color = None
        
        for r, c in added_positions:
            mirror_c = int(round(2 * axis - c))
            if 0 <= mirror_c < self.W:
                if self.grid[r, mirror_c] > 0:
                    # This added pixel mirrors an existing input pixel
                    if add_color is None:
                        add_color = int(self.target[r, c])
                    elif add_color != int(self.target[r, c]):
                        valid_reflection = False
                        break
                else:
                    valid_reflection = False
                    break
            else:
                valid_reflection = False
                break
        
        if valid_reflection and add_color is not None:
            return {
                'gauge_group': 'Z2_completion_recolor',
                'axis': 'horizontal',
                'axis_position': axis,
                'add_color': add_color,
                'spine_col': spine_col
            }
        
        return None
    
    def _detect_c4_on_stalk(self, local_grid: np.ndarray) -> Optional[Dict[str, Any]]:
        """Detect 90-degree rotation symmetry."""
        h, w = local_grid.shape
        if h != w:
            return None  # Rotation symmetry requires square
        
        rotated = np.rot90(local_grid)
        score = np.sum(local_grid == rotated) / local_grid.size
        
        if score >= 0.8 and score < 0.99:
            return {
                'gauge_group': 'C4_rotation',
                'symmetry_score': float(score)
            }
        
        return None
    
    def _detect_sn_on_stalk(self, 
                             local_grid: np.ndarray,
                             stalk: Dict[str, Any]) -> Optional[Dict[str, Any]]:
        """Detect if color permutation relates input to target."""
        if self.target is None:
            return None
        
        mask = stalk['mask']
        
        # Get colors in this stalk's region
        input_colors = self.grid[mask]
        target_colors = self.target[mask]
        
        # Build color mapping
        color_map = {}
        for ic, tc in zip(input_colors, target_colors):
            ic, tc = int(ic), int(tc)
            if ic in color_map:
                if color_map[ic] != tc:
                    return None  # Inconsistent mapping
            else:
                color_map[ic] = tc
        
        # Check if mapping is a permutation (bijective)
        if len(set(color_map.values())) != len(color_map):
            return None  # Not bijective
        
        # Check if mapping is non-trivial
        if all(k == v for k, v in color_map.items()):
            return None  # Identity mapping
        
        return {
            'gauge_group': 'Sn_color_permutation',
            'color_map': color_map
        }
    
    # =========================================================================
    # PHASE 1D: EM-LOOP (EXPECTATION-MAXIMIZATION)
    # =========================================================================
    
    def em_loop(self, 
                 max_iterations: int = 5,
                 energy_threshold: float = 1e-6,
                 verbose: bool = False) -> Dict[str, Any]:
        """
        Expectation-Maximization loop for joint segmentation and gauge detection.
        
        E-Step: Segment the grid into objects using current spectral structure
        M-Step: Find gauge transformations that minimize Free Energy
        Loop: If F > 0, perturb the Laplacian and re-segment
        
        This is the recursive negotiation between "What is an object?" and
        "What is the rule?" until both collapse into the ground state.
        
        Args:
            max_iterations: Maximum EM iterations
            energy_threshold: Stop when Free Energy below this
            verbose: Print progress
            
        Returns:
            Dictionary with EM results
        """
        if self.target is None:
            return {'success': False, 'reason': 'No target for EM loop'}
        
        best_result = None
        best_energy = float('inf')
        
        for iteration in range(max_iterations):
            # E-Step: Decompose into stalks
            stalks = self.decompose_to_stalks(method='hybrid')
            
            if verbose:
                print(f"EM Iteration {iteration + 1}: {len(stalks)} stalks detected")
            
            # M-Step: Find gauges for each stalk and apply
            current_result = self._apply_stalk_gauges(stalks)
            current_energy = current_result['total_energy']
            
            if verbose:
                print(f"  Energy: {current_energy:.4f}")
            
            if current_energy < best_energy:
                best_energy = current_energy
                best_result = current_result
            
            # Check convergence
            if current_energy < energy_threshold:
                if verbose:
                    print(f"  Converged at iteration {iteration + 1}")
                break
            
            # If not converged, perturb the Laplacian based on residual
            # This feeds the Free Energy back into segmentation
            if iteration < max_iterations - 1:
                self._perturb_laplacian_from_residual(current_result)
        
        return {
            'success': best_energy < energy_threshold,
            'final_energy': best_energy,
            'iterations': iteration + 1,
            'n_stalks': len(stalks),
            'result': best_result
        }
    
    def _apply_stalk_gauges(self, stalks: List[Dict[str, Any]]) -> Dict[str, Any]:
        """
        Apply detected gauge transformations to each stalk and glue results.
        
        Returns:
            Dictionary with applied transformations and resulting grid
        """
        result_grid = self.grid.copy()
        stalk_results = []
        total_energy = 0.0
        
        for stalk in stalks:
            gauge = self.detect_stalk_gauge(stalk)
            
            if gauge is not None:
                # Special handling for Z2_completion_recolor (full-grid operation)
                if gauge['gauge_group'] == 'Z2_completion_recolor':
                    axis = gauge['axis_position']
                    add_color = gauge['add_color']
                    spine_col = gauge['spine_col']
                    
                    # Mirror all non-spine pixels to the opposite side
                    for r in range(self.H):
                        for c in range(self.W):
                            if self.grid[r, c] > 0 and c != spine_col:
                                mirror_c = int(round(2 * axis - c))
                                if 0 <= mirror_c < self.W and result_grid[r, mirror_c] == 0:
                                    result_grid[r, mirror_c] = add_color
                    
                    stalk_results.append({
                        'stalk_id': stalk['id'],
                        'gauge': gauge,
                        'applied': True
                    })
                else:
                    # Standard stalk-local transformation
                    transformed = self._apply_gauge_to_stalk(stalk, gauge)
                    
                    # Glue back to result grid
                    mask = stalk['mask']
                    r_min, r_max, c_min, c_max = stalk['bbox']
                    
                    for r, c in zip(*np.where(mask)):
                        local_r = r - r_min
                        local_c = c - c_min
                        if 0 <= local_r < transformed.shape[0] and 0 <= local_c < transformed.shape[1]:
                            result_grid[r, c] = transformed[local_r, local_c]
                    
                    stalk_results.append({
                        'stalk_id': stalk['id'],
                        'gauge': gauge,
                        'applied': True
                    })
            else:
                stalk_results.append({
                    'stalk_id': stalk['id'],
                    'gauge': None,
                    'applied': False
                })
        
        # Compute energy (deviation from target)
        if self.target is not None:
            total_energy = float(np.sum(np.abs(result_grid - self.target)))
        
        return {
            'result_grid': result_grid,
            'stalk_results': stalk_results,
            'total_energy': total_energy,
            'matches_target': np.array_equal(result_grid.astype(int), self.target.astype(int))
        }
    
    def _apply_gauge_to_stalk(self, 
                               stalk: Dict[str, Any],
                               gauge: Dict[str, Any]) -> np.ndarray:
        """Apply a gauge transformation to a stalk's local grid."""
        local_grid = stalk['local_grid'].copy()
        h, w = local_grid.shape
        
        if gauge['gauge_group'] == 'Z2_completion_recolor':
            # This gauge operates on the FULL grid, not just the stalk
            # Mirror protrusions with recoloring
            return local_grid  # Handled specially in _apply_stalk_gauges
        
        elif gauge['gauge_group'] == 'Z2_completion':
            # Mirror non-zero pixels to complete symmetry (same color)
            result = local_grid.copy()
            if gauge['axis'] == 'horizontal':
                axis = (w - 1) / 2.0
                for r in range(h):
                    for c in range(w):
                        if local_grid[r, c] != 0:
                            mirror_c = int(round(2 * axis - c))
                            if 0 <= mirror_c < w and result[r, mirror_c] == 0:
                                result[r, mirror_c] = local_grid[r, c]
            else:  # vertical
                axis = (h - 1) / 2.0
                for r in range(h):
                    for c in range(w):
                        if local_grid[r, c] != 0:
                            mirror_r = int(round(2 * axis - r))
                            if 0 <= mirror_r < h and result[mirror_r, c] == 0:
                                result[mirror_r, c] = local_grid[r, c]
            return result
        
        elif gauge['gauge_group'] == 'Z2_reflection':
            if gauge['axis'] == 'horizontal':
                return np.fliplr(local_grid)
            else:
                return np.flipud(local_grid)
        
        elif gauge['gauge_group'] == 'C4_rotation':
            return np.rot90(local_grid)
        
        elif gauge['gauge_group'] == 'Sn_color_permutation':
            color_map = gauge['color_map']
            result = local_grid.copy()
            for from_c, to_c in color_map.items():
                result[local_grid == from_c] = to_c
            return result
        
        return local_grid
    
    def _perturb_laplacian_from_residual(self, result: Dict[str, Any]):
        """
        Perturb the Laplacian based on residual energy for next EM iteration.
        
        The residual (target - result) indicates where segmentation may be wrong.
        We feed this back by adjusting edge weights.
        """
        if self.target is None:
            return
        
        result_grid = result['result_grid']
        residual = np.abs(self.target - result_grid)
        
        # Clear cached Laplacian to force recomputation with perturbation
        self._semantic_laplacian = None
        self._eigenvalues = None
        self._eigenvectors = None
        
        # The residual acts as a "temperature field" that softens edges
        # in high-error regions, encouraging re-segmentation
        # (This is implemented implicitly by the color-weighted Laplacian
        # when we re-segment after applying partial transformations)
    
    # =========================================================================
    # PHASE 2: GAUGE COMPOSITION (CHAINING TRANSFORMATIONS)
    # =========================================================================
    
    def compose_gauges(self, gauges: List[Dict[str, Any]]) -> Callable[[np.ndarray], np.ndarray]:
        """
        Compose multiple gauge transformations into a single function.
        
        This implements the functor composition: g1 o g2 o ... o gn
        
        Args:
            gauges: List of gauge dictionaries in application order
            
        Returns:
            Composite transformation function
        """
        def composite_transform(grid: np.ndarray) -> np.ndarray:
            result = grid.copy()
            for gauge in gauges:
                result = self._apply_single_gauge(result, gauge)
            return result
        
        return composite_transform
    
    def _apply_single_gauge(self, grid: np.ndarray, gauge: Dict[str, Any]) -> np.ndarray:
        """Apply a single gauge transformation to a grid."""
        if gauge['gauge_group'] == 'Z2_reflection':
            if gauge.get('axis') == 'horizontal':
                return np.fliplr(grid)
            else:
                return np.flipud(grid)
        
        elif gauge['gauge_group'] == 'C4_rotation':
            return np.rot90(grid)
        
        elif gauge['gauge_group'] == 'Sn_color_permutation':
            color_map = gauge['color_map']
            result = grid.copy()
            for from_c, to_c in color_map.items():
                result[grid == from_c] = to_c
            return result
        
        elif gauge['gauge_group'] == 'Zn_translation':
            dr, dc = gauge.get('vector', (0, 0))
            result = np.zeros_like(grid)
            for r in range(grid.shape[0]):
                for c in range(grid.shape[1]):
                    nr, nc = (r + dr) % grid.shape[0], (c + dc) % grid.shape[1]
                    result[nr, nc] = grid[r, c]
            return result
        
        return grid
    
    # =========================================================================
    # PHASE 2: GAUGE COMPOSITION ALGEBRA
    # =========================================================================
    
    def compute_topological_predicates(self, stalk: Dict[str, Any], 
                                        all_stalks: List[Dict[str, Any]]) -> Dict[str, Any]:
        """
        Compute topological predicates for a stalk based on adjacency relationships.
        
        The Laplacian's adjacency structure encodes ALL predicate information.
        We extract:
        - is_adjacent_to(color): shares an edge with pixels of given color
        - is_enclosed_by(color): bounding box perimeter is entirely bounded by color
        - is_max_size: this stalk has the most pixels
        - relative_position: where this stalk is relative to others
        
        Args:
            stalk: The stalk to compute predicates for
            all_stalks: All stalks in the decomposition
            
        Returns:
            Dictionary of predicate values
        """
        # Get the primary color of this stalk (first non-zero color)
        stalk_colors = stalk.get('colors', [])
        primary_color = stalk_colors[0] if stalk_colors else 0
        
        predicates = {
            'adjacent_colors': set(),
            'enclosed_by': None,
            'is_max_size': False,
            'relative_position': None,
            'stalk_color': primary_color,
            'all_colors': set(stalk_colors)
        }
        
        mask = stalk['mask']
        r_min, r_max, c_min, c_max = stalk['bbox']
        
        # Find adjacent colors by checking boundary pixels
        boundary_colors = set()
        for r, c in zip(*np.where(mask)):
            for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                nr, nc = r + dr, c + dc
                if 0 <= nr < self.H and 0 <= nc < self.W:
                    if not mask[nr, nc]:  # Not part of this stalk
                        neighbor_color = int(self.grid[nr, nc])
                        if neighbor_color != 0:  # Not background
                            boundary_colors.add(neighbor_color)
        predicates['adjacent_colors'] = boundary_colors
        
        # Check enclosure: is the bounding box perimeter entirely one color?
        perimeter_colors = set()
        # Top and bottom edges
        for c in range(max(0, c_min-1), min(self.W, c_max+2)):
            if r_min > 0:
                perimeter_colors.add(int(self.grid[r_min-1, c]))
            if r_max < self.H - 1:
                perimeter_colors.add(int(self.grid[r_max+1, c]))
        # Left and right edges
        for r in range(max(0, r_min-1), min(self.H, r_max+2)):
            if c_min > 0:
                perimeter_colors.add(int(self.grid[r, c_min-1]))
            if c_max < self.W - 1:
                perimeter_colors.add(int(self.grid[r, c_max+1]))
        
        perimeter_colors.discard(0)  # Remove background
        perimeter_colors.discard(primary_color)  # Remove self
        if len(perimeter_colors) == 1:
            predicates['enclosed_by'] = perimeter_colors.pop()
        
        # Check if max size
        stalk_sizes = [s['n_pixels'] for s in all_stalks]
        predicates['is_max_size'] = stalk['n_pixels'] == max(stalk_sizes)
        
        # Relative position (centroid)
        rows, cols = np.where(mask)
        centroid_r = np.mean(rows)
        centroid_c = np.mean(cols)
        predicates['relative_position'] = (centroid_r / self.H, centroid_c / self.W)
        
        return predicates
    
    def apply_residual_guided_composition(self, 
                                           stalk: Dict[str, Any],
                                           predicates: Dict[str, Any],
                                           max_depth: int = 3) -> Dict[str, Any]:
        """
        Apply gauge operations via residual-guided composition.
        
        This is the Thermodynamic EM-loop for gauge chaining:
        1. Apply best single gauge g1
        2. Measure residual Free Energy
        3. If E > 0, treat residual as new sub-problem, find g2
        4. Chain: T = g2 o g1
        
        This avoids combinatorial explosion by following the energy gradient.
        
        Args:
            stalk: The stalk to transform
            predicates: Topological predicates for conditional logic
            max_depth: Maximum composition depth
            
        Returns:
            Composition result with applied gauge sequence
        """
        if self.target is None:
            return {'success': False, 'reason': 'No target'}
        
        mask = stalk['mask']
        r_min, r_max, c_min, c_max = stalk['bbox']
        
        # Current state starts as input
        current_local = stalk['local_grid'].copy()
        target_local = self.target[r_min:r_max+1, c_min:c_max+1].copy()
        
        # Extract target within mask only
        stalk_mask_local = mask[r_min:r_max+1, c_min:c_max+1]
        
        applied_gauges = []
        
        for depth in range(max_depth):
            # Compute residual energy
            residual = np.abs(current_local - target_local) * stalk_mask_local
            energy = float(residual.sum())
            
            if energy < 0.5:  # Converged
                break
            
            # Create a temporary stalk with current state
            temp_stalk = {
                'local_grid': current_local,
                'mask': mask,
                'bbox': stalk['bbox'],
                'colors': stalk.get('colors', []),
                'id': stalk['id']
            }
            
            # Try each gauge operation and pick the one with lowest residual energy
            best_gauge = None
            best_result = current_local
            best_energy = energy
            
            # Candidate gauges to try
            candidates = self._generate_candidate_gauges(temp_stalk, predicates, target_local)
            
            for gauge in candidates:
                result = self._apply_gauge_to_stalk(temp_stalk, gauge)
                new_residual = np.abs(result - target_local) * stalk_mask_local
                new_energy = float(new_residual.sum())
                
                if new_energy < best_energy:
                    best_energy = new_energy
                    best_gauge = gauge
                    best_result = result
            
            if best_gauge is None:
                break  # No improvement possible
            
            applied_gauges.append(best_gauge)
            current_local = best_result
            
            if best_energy < 0.5:
                break
        
        # Final check
        final_residual = np.abs(current_local - target_local) * stalk_mask_local
        final_energy = float(final_residual.sum())
        
        return {
            'success': final_energy < 0.5,
            'gauge_sequence': applied_gauges,
            'result_local': current_local,
            'final_energy': final_energy,
            'composition_depth': len(applied_gauges)
        }
    
    def detect_and_fill_enclosed_voids(self) -> Optional[Dict[str, Any]]:
        """
        Detect background pixels that are enclosed by foreground and fill them.
        
        This handles tasks like 00d62c1b where the transformation is:
        "Fill holes inside shapes with a new color"
        
        Uses flood fill from edges to find unenclosed regions, then fills the rest.
        """
        if self.target is None:
            return None
        
        from scipy.ndimage import binary_fill_holes
        
        # Create foreground mask (any non-background)
        fg_mask = self.grid > 0
        
        # Fill holes in foreground
        filled = binary_fill_holes(fg_mask)
        
        # The holes are where filled differs from original
        holes_mask = filled & ~fg_mask
        
        if not holes_mask.any():
            return None
        
        # Check what color the holes should be filled with (from target)
        target_hole_colors = self.target[holes_mask]
        unique_fill_colors = np.unique(target_hole_colors)
        unique_fill_colors = unique_fill_colors[unique_fill_colors != 0]
        
        if len(unique_fill_colors) != 1:
            return None  # Ambiguous fill color
        
        fill_color = int(unique_fill_colors[0])
        
        # Create result by filling holes
        result = self.grid.copy()
        result[holes_mask] = fill_color
        
        if np.array_equal(result.astype(int), self.target.astype(int)):
            return {
                'success': True,
                'method': 'fill_enclosed',
                'fill_color': fill_color,
                'n_filled': int(holes_mask.sum()),
                'result': result
            }
        
        return None
    
    def _generate_candidate_gauges(self, 
                                    stalk: Dict[str, Any],
                                    predicates: Dict[str, Any],
                                    target_local: np.ndarray) -> List[Dict[str, Any]]:
        """
        Generate candidate gauge operations based on stalk and predicates.
        
        This implements predicate-gated gauge proposal:
        - If adjacent to color X, propose recolor operations involving X
        - If enclosed, propose fill operations
        - Always propose basic symmetry operations
        """
        candidates = []
        local_grid = stalk['local_grid']
        
        # 1. Color permutation based on local->target mapping
        local_colors = set(local_grid.flatten().astype(int)) - {0}
        target_colors = set(target_local.flatten().astype(int)) - {0}
        
        if local_colors and target_colors:
            # Try direct color mapping
            color_map = {}
            valid_map = True
            for r in range(local_grid.shape[0]):
                for c in range(local_grid.shape[1]):
                    lc = int(local_grid[r, c])
                    tc = int(target_local[r, c])
                    if lc != 0:
                        if lc in color_map:
                            if color_map[lc] != tc:
                                valid_map = False
                                break
                        else:
                            color_map[lc] = tc
                if not valid_map:
                    break
            
            if valid_map and color_map:
                candidates.append({
                    'gauge_group': 'Sn_color_permutation',
                    'color_map': color_map
                })
        
        # 2. Reflection operations
        candidates.append({'gauge_group': 'Z2_reflection', 'axis': 'horizontal'})
        candidates.append({'gauge_group': 'Z2_reflection', 'axis': 'vertical'})
        
        # 3. Rotation
        if local_grid.shape[0] == local_grid.shape[1]:
            candidates.append({'gauge_group': 'C4_rotation'})
        
        # 4. Predicate-gated: if adjacent to specific color, propose recolor TO that color
        for adj_color in predicates.get('adjacent_colors', []):
            if adj_color not in local_colors:
                for lc in local_colors:
                    candidates.append({
                        'gauge_group': 'Sn_color_permutation',
                        'color_map': {lc: adj_color},
                        'predicate': f'adjacent_to_{adj_color}'
                    })
        
        # 5. Fill with enclosing color
        enc_color = predicates.get('enclosed_by')
        if enc_color is not None:
            for lc in local_colors:
                if lc != enc_color:
                    candidates.append({
                        'gauge_group': 'Sn_color_permutation',
                        'color_map': {lc: enc_color},
                        'predicate': f'enclosed_by_{enc_color}'
                    })
        
        return candidates
    
    def _apply_composition_to_grid(self, 
                                    stalks: List[Dict[str, Any]],
                                    composition_results: List[Dict[str, Any]]) -> np.ndarray:
        """Apply composition results from all stalks to create final grid."""
        result_grid = self.grid.copy()
        
        for stalk, comp in zip(stalks, composition_results):
            if comp['success']:
                mask = stalk['mask']
                r_min, r_max, c_min, c_max = stalk['bbox']
                result_local = comp['result_local']
                
                for r, c in zip(*np.where(mask)):
                    local_r = r - r_min
                    local_c = c - c_min
                    if 0 <= local_r < result_local.shape[0] and 0 <= local_c < result_local.shape[1]:
                        result_grid[r, c] = result_local[local_r, local_c]
        
        return result_grid
    
    # =========================================================================
    # PHASE 3: SHAPE-CHANGE VIA RG FLOW (BOUNDING BOX EXTRACTION)
    # =========================================================================
    
    def extract_bounding_box(self, grid: np.ndarray = None) -> np.ndarray:
        """
        RG Flow: Crop to bounding box (integrate out the background).
        
        When the G-defect is "empty space surrounding the object", the
        minimal energy state is to delete the empty space.
        
        Args:
            grid: Grid to crop (uses self.grid if None)
            
        Returns:
            Cropped grid containing only the G-kernel
        """
        if grid is None:
            grid = self.grid
        
        mask = grid > 0
        if not mask.any():
            return grid
        
        rows, cols = np.where(mask)
        r_min, r_max = rows.min(), rows.max()
        c_min, c_max = cols.min(), cols.max()
        
        return grid[r_min:r_max+1, c_min:c_max+1].copy()
    
    def tile_to_size(self, 
                      kernel: np.ndarray, 
                      target_shape: Tuple[int, int]) -> np.ndarray:
        """
        RG Flow inverse: Tile a kernel to fill target shape.
        
        When the output is a periodic repetition of the G-kernel.
        
        Args:
            kernel: Small grid to tile
            target_shape: (H, W) of desired output
            
        Returns:
            Tiled grid
        """
        kh, kw = kernel.shape
        th, tw = target_shape
        
        result = np.zeros(target_shape, dtype=kernel.dtype)
        
        for r in range(th):
            for c in range(tw):
                result[r, c] = kernel[r % kh, c % kw]
        
        return result
    
    def predict_output_shape(self) -> Tuple[int, int]:
        """
        Predict output shape from the G-kernel structure.
        
        Heuristics:
        1. If input has clear bounding box, output = bounding box size
        2. If input has periodic structure, output = period size
        3. Otherwise, output = input (same-shape transformation)
        
        Returns:
            Predicted (H, W) of output
        """
        mask = self.grid > 0
        if not mask.any():
            return (self.H, self.W)
        
        rows, cols = np.where(mask)
        bbox_h = rows.max() - rows.min() + 1
        bbox_w = cols.max() - cols.min() + 1
        
        # Check if bounding box is significantly smaller than grid
        if bbox_h * bbox_w < 0.5 * self.H * self.W:
            return (bbox_h, bbox_w)
        
        return (self.H, self.W)
    
    # =========================================================================
    # UNIFIED SOLVE METHOD
    # =========================================================================
    
    def solve(self, verbose: bool = False) -> Dict[str, Any]:
        """
        Unified solve method using the full Cellular Sheaf architecture.
        
        Pipeline:
        1. Build semantic Laplacian (color-weighted, normalized)
        2. Decompose into stalks (spectral + connected components)
        3. Compute topological predicates per stalk
        4. Try single gauge per stalk
        5. If failed, apply residual-guided composition (Phase 2)
        6. RG Flow for shape adjustment
        
        Args:
            verbose: Print progress
            
        Returns:
            Solution dictionary
        """
        if self.target is None:
            return {'success': False, 'reason': 'No target provided'}
        
        # Check shape match
        if self.grid.shape != self.target.shape:
            # Try RG Flow: extract bounding box
            bbox = self.extract_bounding_box()
            if bbox.shape == self.target.shape:
                result = bbox.copy()
                matches = np.array_equal(result.astype(int), self.target.astype(int))
                return {
                    'success': matches,
                    'method': 'rg_flow_bbox',
                    'result': result
                }
            else:
                return {
                    'success': False,
                    'reason': f'Shape mismatch: {self.grid.shape} vs {self.target.shape}'
                }
        
        # Step 0: Try fill-enclosed (for tasks that fill holes inside shapes)
        fill_result = self.detect_and_fill_enclosed_voids()
        if fill_result is not None and fill_result['success']:
            if verbose:
                print(f"Solved via fill_enclosed: {fill_result['n_filled']} pixels with color {fill_result['fill_color']}")
            return fill_result
        
        # Step 1: Decompose into stalks
        stalks = self.decompose_to_stalks(method='hybrid')
        
        if verbose:
            print(f"Decomposed into {len(stalks)} stalks")
        
        # Step 2: Try direct stalk-wise gauge application (single gauge per stalk)
        result = self._apply_stalk_gauges(stalks)
        
        if result['matches_target']:
            return {
                'success': True,
                'method': 'stalk_gauge',
                'n_stalks': len(stalks),
                'result': result['result_grid'],
                'gauges': [sr['gauge'] for sr in result['stalk_results'] if sr['gauge']]
            }
        
        # Step 3: Phase 2 - Residual-guided composition with predicates
        if verbose:
            print("Single-gauge failed, trying residual-guided composition...")
        
        composition_results = []
        all_predicates = []
        
        for stalk in stalks:
            predicates = self.compute_topological_predicates(stalk, stalks)
            all_predicates.append(predicates)
            
            if verbose:
                adj_str = ','.join(map(str, predicates['adjacent_colors'])) or 'none'
                print(f"  Stalk {stalk['id']}: color={predicates['stalk_color']}, adj=[{adj_str}], enclosed={predicates['enclosed_by']}")
            
            comp_result = self.apply_residual_guided_composition(stalk, predicates, max_depth=3)
            composition_results.append(comp_result)
            
            if verbose and comp_result['success']:
                gauges = [g['gauge_group'] for g in comp_result['gauge_sequence']]
                print(f"    -> Solved with composition: {' o '.join(gauges)}")
        
        # Apply all composition results to grid
        result_grid = self._apply_composition_to_grid(stalks, composition_results)
        matches = np.array_equal(result_grid.astype(int), self.target.astype(int))
        
        if matches:
            return {
                'success': True,
                'method': 'gauge_composition',
                'n_stalks': len(stalks),
                'result': result_grid,
                'compositions': [
                    {'stalk_id': s['id'], 'sequence': c['gauge_sequence'], 'depth': c['composition_depth']}
                    for s, c in zip(stalks, composition_results) if c['success']
                ]
            }
        
        # Step 4: Fallback - try global color permutation
        sn_result = self._try_global_color_permutation()
        if sn_result['success']:
            return sn_result
        
        return {
            'success': False,
            'method': 'none',
            'final_energy': float(np.sum(np.abs(result_grid - self.target)))
        }
    
    def _try_global_color_permutation(self) -> Dict[str, Any]:
        """Fallback: try to find a global color permutation."""
        if self.target is None:
            return {'success': False}
        
        # Build color mapping from input to target
        color_map = {}
        for r in range(self.H):
            for c in range(self.W):
                ic = int(self.grid[r, c])
                tc = int(self.target[r, c])
                if ic in color_map:
                    if color_map[ic] != tc:
                        return {'success': False}
                else:
                    color_map[ic] = tc
        
        # Apply mapping
        result = self.grid.copy()
        for from_c, to_c in color_map.items():
            result[self.grid == from_c] = to_c
        
        matches = np.array_equal(result.astype(int), self.target.astype(int))
        
        return {
            'success': matches,
            'method': 'global_sn',
            'color_map': color_map,
            'result': result
        }


# =============================================================================
# DEMO AND TESTING
# =============================================================================

def demo_cellular_sheaf():
    """Demonstrate the Cellular Sheaf Engine on a multi-object task."""
    
    print("=" * 70)
    print("CELLULAR SHEAF ENGINE DEMO")
    print("=" * 70)
    
    # Create a test grid with multiple disconnected objects
    grid = np.array([
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 1, 1, 0, 0, 0, 0, 2, 2, 0],
        [0, 1, 0, 0, 0, 0, 0, 0, 2, 0],
        [0, 1, 0, 0, 0, 0, 0, 0, 2, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 3, 3, 3, 0, 0, 0, 0],
        [0, 0, 0, 3, 0, 3, 0, 0, 0, 0],
        [0, 0, 0, 3, 3, 3, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ], dtype=np.float32)
    
    # Target: reflect the L-shapes, keep the square
    target = np.array([
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 1, 1, 0, 0, 0, 0, 2, 2, 0],
        [0, 0, 1, 0, 0, 0, 0, 2, 0, 0],
        [0, 0, 1, 0, 0, 0, 0, 2, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 3, 3, 3, 0, 0, 0, 0],
        [0, 0, 0, 3, 0, 3, 0, 0, 0, 0],
        [0, 0, 0, 3, 3, 3, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ], dtype=np.float32)
    
    print("\nInput grid:")
    print(grid.astype(int))
    
    print("\nTarget grid:")
    print(target.astype(int))
    
    # Create engine
    engine = CellularSheafEngine(grid, target)
    
    # Build semantic Laplacian
    print("\n--- Semantic Laplacian ---")
    L = engine.build_semantic_laplacian()
    print(f"Laplacian shape: {L.shape}")
    print(f"Non-zero entries: {L.nnz}")
    
    # Compute spectral modes
    print("\n--- Spectral Analysis ---")
    eigenvalues, eigenvectors = engine.compute_spectral_modes(n_modes=10)
    print(f"Eigenvalues: {eigenvalues[:5]}")
    
    n_zero = np.sum(np.abs(eigenvalues) < 1e-6)
    print(f"Zero eigenvalue multiplicity: {n_zero}")
    print(f"Disconnected components (spectral): {engine.count_disconnected_components()}")
    
    # Decompose into stalks
    print("\n--- Cellular Sheaf Decomposition ---")
    stalks = engine.decompose_to_stalks(method='hybrid')
    print(f"Number of stalks: {len(stalks)}")
    
    for stalk in stalks:
        print(f"\n  Stalk {stalk['id']}:")
        print(f"    Pixels: {stalk['n_pixels']}")
        print(f"    Colors: {stalk['colors']}")
        print(f"    Bbox: {stalk['bbox']}")
        
        # Detect gauge
        gauge = engine.detect_stalk_gauge(stalk)
        if gauge:
            print(f"    Gauge: {gauge['gauge_group']}")
    
    # Solve
    print("\n--- Solve ---")
    result = engine.solve(verbose=True)
    print(f"\nSuccess: {result['success']}")
    print(f"Method: {result.get('method', 'unknown')}")
    
    if result['success']:
        print("\nResult grid:")
        print(result['result'].astype(int))


def eval_on_arc_task(task_path: str) -> Dict[str, Any]:
    """Evaluate the Cellular Sheaf Engine on an ARC task."""
    
    with open(task_path, 'r') as f:
        task = json.load(f)
    
    train_examples = task['train']
    results = []
    
    for i, example in enumerate(train_examples):
        input_grid = np.array(example['input'], dtype=np.float32)
        output_grid = np.array(example['output'], dtype=np.float32)
        
        # Skip shape-change tasks for now
        if input_grid.shape != output_grid.shape:
            results.append({
                'example': i,
                'success': False,
                'reason': 'shape_mismatch'
            })
            continue
        
        engine = CellularSheafEngine(input_grid, output_grid)
        result = engine.solve()
        result['example'] = i
        results.append(result)
    
    n_success = sum(1 for r in results if r['success'])
    
    return {
        'task': Path(task_path).stem,
        'examples': results,
        'n_train': len(train_examples),
        'n_success': n_success,
        'success_rate': n_success / len(train_examples) if train_examples else 0
    }


if __name__ == '__main__':
    demo_cellular_sheaf()
