"""
Emergent Sheaf Engine v6: Vectorized Instructive Signals

This module implements the EMERGENT intelligence paradigm for ARC solving.
Instead of hardcoded heuristics, all operations are generalized matrix 
operations on the Graph Laplacian that the system DISCOVERS through
thermodynamic relaxation.

Core Principle:
- NO hardcoded ARC-specific rules (no fill_enclosed, no hand-crafted predicates)
- ALL operations are matrix multiplications: X' = T @ X
- The system DISCOVERS which T minimizes Free Energy

Mathematical Foundation (v6 - Vectorized Instructive Signals):
1. Heat Kernel: H_t = exp(-t * L) - Diffusion operator (emergent filling)
2. Permutation Matrix: P - Derived from Fiedler vector (emergent reflection)
3. Color Transition: C - Learned from input/target color distributions
4. Boundary Operator: δ - For collision detection between stalks
5. Geodesic Ray: Shortest path on semantic manifold (connect-the-dots)
6. Relative Color: Gauge interactions (paint A like B)
7. Composition: Chain operators T_n ∘ ... ∘ T_1
8. Defect Gradient Analyzer: Vectorized signals from D = Target - State

v6 Key Innovation (Francioni et al., 2026):
- Instead of random search over 89 operators, analyze the Defect Matrix D
- Extract vectorized instructive signals: spatial shifts, color maps, morphology
- O(1) inference instead of O(n) combinatorial search

The EM Loop explores the continuous space of these operators and saves
successful operator sequences to the SheafAtlas for future reuse.
"""

import numpy as np
from scipy import sparse
from scipy.sparse.linalg import eigsh, expm_multiply
from scipy.linalg import expm
from scipy.ndimage import label as connected_components
from typing import Dict, Any, List, Tuple, Optional
import copy
import json
from pathlib import Path


class EmergentSheafEngine:
    """
    Hierarchical Emergent Sheaf Engine v6: Vectorized Instructive Signals.
    
    Key insight: The Free Energy gradient IS the instruction vector.
    Instead of random search, we analyze D = Target - State to extract
    exact operator parameters in O(1) time.
    
    Architecture:
    1. Decompose grid into stalks (connected components)
    2. Compute LOCAL spectral signatures per stalk
    3. Index Atlas by stalk geometry (position-invariant)
    4. Analyze Defect Matrix for vectorized signals (v6)
    5. Apply instructed operators or fall back to thermodynamic search
    6. Consolidate successful operators to SheafAtlas
    
    v6 Features (Vectorized Instructive Signals):
    - Defect Gradient Analyzer: Extract (dx, dy), color maps, morphology from D
    - Spatial Gradients: Stalk centroid shift -> translation matrix
    - Color Gradients: Pixel-wise color diff -> transition matrix
    - Morphological Gradients: Boundary intersection -> dilation/erosion
    - Geodesic Gradients: 1D path in D -> geodesic ray operator
    - O(1) inference replaces O(n) combinatorial search
    """
    
    def __init__(self,
                 grid: np.ndarray,
                 target: Optional[np.ndarray] = None,
                 signature_dims: int = 16):
        """
        Initialize the Emergent Sheaf Engine.
        
        Args:
            grid: Input ARC grid (H x W integer array, 0=background)
            target: Optional target output grid for supervised learning
        """
        self.grid = grid.astype(np.float32)
        self.target = target.astype(np.float32) if target is not None else None
        self.H, self.W = grid.shape
        self.N = self.H * self.W
        self.signature_dims = signature_dims
        
        # Spectral decomposition
        self._laplacian = None
        self._eigenvalues = None
        self._eigenvectors = None
        self._adjacency = None
        self._degree = None
        
        # Full eigendecomposition cache (for heat kernel operations)
        self._full_eigenvalues = None
        self._full_eigenvectors = None
        self._full_laplacian = None
        
        # Discovered operators (learned, not hardcoded)
        self._discovered_operators: List[Dict[str, Any]] = []
        
        # Background color
        self.background_color = 0
        
        # Stalk decomposition cache (v4)
        self._stalks: Optional[List[Dict[str, Any]]] = None

    def _clone_operator_sequence(self, operators: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """Deep-copy operators so Atlas storage/retrieval cannot mutate source state."""
        cloned: List[Dict[str, Any]] = []
        for op in operators:
            op_clone: Dict[str, Any] = {}
            for key, value in op.items():
                if isinstance(value, np.ndarray):
                    op_clone[key] = value.copy()
                else:
                    op_clone[key] = copy.deepcopy(value)
            cloned.append(op_clone)
        return cloned
        
    # =========================================================================
    # PHASE 1: BUILD THE SEMANTIC MANIFOLD
    # =========================================================================
    
    def build_laplacian(self, epsilon: float = 0.01) -> Tuple[np.ndarray, np.ndarray]:
        """
        Build the Graph Laplacian and Adjacency matrix.
        
        The Laplacian encodes ALL topological information:
        - Connectivity (which pixels are neighbors)
        - Color boundaries (weak coupling across colors)
        - Enclosure (random walk escape probability)
        
        Returns:
            (Laplacian L, Adjacency A) as dense matrices for small grids
        """
        if self._laplacian is not None:
            return self._laplacian, self._adjacency
        
        # Build adjacency matrix
        A = np.zeros((self.N, self.N), dtype=np.float32)
        
        for r in range(self.H):
            for c in range(self.W):
                i = r * self.W + c
                color_i = self.grid[r, c]
                
                # Skip background (topological void)
                if color_i == self.background_color:
                    continue
                
                # 4-connected neighbors
                for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                    nr, nc = r + dr, c + dc
                    if 0 <= nr < self.H and 0 <= nc < self.W:
                        j = nr * self.W + nc
                        color_j = self.grid[nr, nc]
                        
                        if color_j == self.background_color:
                            continue
                        
                        # Same color = strong connection, different = weak
                        if color_i == color_j:
                            A[i, j] = 1.0
                        else:
                            A[i, j] = epsilon
        
        # Degree matrix
        D = np.diag(A.sum(axis=1))
        
        # Laplacian: L = D - A
        L = D - A
        
        self._laplacian = L
        self._adjacency = A
        self._degree = D
        
        return L, A
    
    def compute_spectral_decomposition(self, n_modes: int = 10) -> Tuple[np.ndarray, np.ndarray]:
        """
        Compute eigendecomposition of the Laplacian.
        
        The eigenvectors encode:
        - Zero eigenvectors: Connected components
        - Fiedler vector (2nd smallest): Natural partition axis
        - Higher modes: Harmonic structure
        
        Returns:
            (eigenvalues, eigenvectors)
        """
        if self._eigenvalues is not None:
            return self._eigenvalues, self._eigenvectors
        
        L, _ = self.build_laplacian()
        
        # For small grids, use full eigendecomposition
        if self.N <= 100:
            eigenvalues, eigenvectors = np.linalg.eigh(L)
        else:
            # For larger grids, use sparse methods
            L_sparse = sparse.csr_matrix(L)
            k = min(n_modes, self.N - 2)
            eigenvalues, eigenvectors = eigsh(L_sparse, k=k, which='SM')
        
        # Sort by eigenvalue
        idx = np.argsort(eigenvalues)
        self._eigenvalues = eigenvalues[idx]
        self._eigenvectors = eigenvectors[:, idx]
        
        return self._eigenvalues, self._eigenvectors

    def compute_full_eigendecomposition(self) -> Tuple[np.ndarray, np.ndarray]:
        """
        Compute and cache FULL eigendecomposition of the grid Laplacian.
        
        This is expensive O(N³) but cached for reuse across all heat kernel
        and diffusion operations within the same engine instance.
        
        Returns:
            (eigenvalues, eigenvectors) - full N×N decomposition
        """
        if self._full_eigenvalues is not None:
            return self._full_eigenvalues, self._full_eigenvectors
        
        # Build full-grid Laplacian
        if self._full_laplacian is None:
            A_full = np.zeros((self.N, self.N), dtype=np.float32)
            for r in range(self.H):
                for c in range(self.W):
                    i = r * self.W + c
                    for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                        nr, nc = r + dr, c + dc
                        if 0 <= nr < self.H and 0 <= nc < self.W:
                            j = nr * self.W + nc
                            A_full[i, j] = 1.0
            
            D_full = np.diag(A_full.sum(axis=1))
            self._full_laplacian = D_full - A_full
        
        # Full eigendecomposition (cached)
        self._full_eigenvalues, self._full_eigenvectors = np.linalg.eigh(self._full_laplacian)
        
        return self._full_eigenvalues, self._full_eigenvectors
    
    def compute_cached_heat_kernel(self, t: float) -> np.ndarray:
        """
        Compute heat kernel using cached eigendecomposition.
        
        H_t = V @ diag(exp(-t * λ)) @ V^T
        
        This avoids recomputing the O(N³) eigendecomposition for each operator.
        """
        eigenvalues, eigenvectors = self.compute_full_eigendecomposition()
        exp_eigenvalues = np.exp(-t * eigenvalues)
        H_t = eigenvectors @ np.diag(exp_eigenvalues) @ eigenvectors.T
        return H_t

    def compute_spectral_signature(self, n_eigs: Optional[int] = None) -> np.ndarray:
        """
        Spectral key used by SheafAtlas memory.

        Key = first N eigenvalues of the semantic Laplacian (curvature signature).
        """
        if n_eigs is None:
            n_eigs = self.signature_dims

        eigenvalues, _ = self.compute_spectral_decomposition(n_modes=max(n_eigs, 10))
        sig = np.asarray(eigenvalues[:n_eigs], dtype=np.float32)

        if sig.shape[0] < n_eigs:
            padded = np.zeros((n_eigs,), dtype=np.float32)
            padded[:sig.shape[0]] = sig
            sig = padded

        return sig

    # =========================================================================
    # PHASE 1B: HIERARCHICAL STALK DECOMPOSITION (v4)
    # =========================================================================
    
    def decompose_to_stalks(self) -> List[Dict[str, Any]]:
        """
        Decompose the grid into Cellular Sheaf stalks.
        
        Each stalk is a connected component of same-color pixels.
        This is the correct topological decomposition: physics happens
        locally on stalks, not globally on the base space.
        
        Returns:
            List of stalk dictionaries with local_grid, bbox, spectral_signature
        """
        if self._stalks is not None:
            return self._stalks
        
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
                    masks.append((mask, int(color)))
        
        stalks = []
        for i, (mask, color) in enumerate(masks):
            # Compute bounding box
            rows, cols = np.where(mask)
            if len(rows) == 0:
                continue
            r_min, r_max = rows.min(), rows.max()
            c_min, c_max = cols.min(), cols.max()
            
            # Extract local grid (cropped to bounding box)
            local_h = r_max - r_min + 1
            local_w = c_max - c_min + 1
            local_grid = np.zeros((local_h, local_w), dtype=np.float32)
            for r, c in zip(rows, cols):
                local_grid[r - r_min, c - c_min] = self.grid[r, c]
            
            # Compute LOCAL spectral signature (position-invariant)
            local_signature = self._compute_local_stalk_signature(local_grid)
            
            stalks.append({
                'id': i,
                'mask': mask,
                'local_grid': local_grid,
                'bbox': (r_min, r_max, c_min, c_max),
                'position': (r_min, c_min),  # For translation detection
                'n_pixels': int(mask.sum()),
                'color': color,
                'spectral_signature': local_signature
            })
        
        self._stalks = stalks
        return stalks
    
    def _decompose_grid_to_stalks(self, grid: np.ndarray) -> List[Dict[str, Any]]:
        """
        Decompose an arbitrary grid into stalks (connected components).
        
        This is a stateless helper for analyzing grids other than self.grid
        (e.g., the target grid for Stalk-to-Stalk isomorphism detection).
        
        Returns:
            List of stalk dictionaries with mask, local_grid, bbox, color, etc.
        """
        stalks = []
        masks = []
        
        unique_colors = np.unique(grid)
        unique_colors = unique_colors[unique_colors != self.background_color]
        
        for color in unique_colors:
            color_mask = (grid == color).astype(int)
            labeled, n_components = connected_components(color_mask)
            
            for c in range(1, n_components + 1):
                mask = labeled == c
                if mask.any():
                    masks.append((mask, int(color)))
        
        for i, (mask, color) in enumerate(masks):
            rows, cols = np.where(mask)
            if len(rows) == 0:
                continue
            r_min, r_max = rows.min(), rows.max()
            c_min, c_max = cols.min(), cols.max()
            
            # Extract local boolean shape (color-agnostic)
            local_h = r_max - r_min + 1
            local_w = c_max - c_min + 1
            local_shape = np.zeros((local_h, local_w), dtype=bool)
            for r, c in zip(rows, cols):
                local_shape[r - r_min, c - c_min] = True
            
            # Centroid
            centroid = (rows.mean(), cols.mean())
            
            stalks.append({
                'id': i,
                'mask': mask,
                'local_shape': local_shape,  # Boolean shape (topological invariant)
                'bbox': (r_min, r_max, c_min, c_max),
                'centroid': centroid,
                'n_pixels': int(mask.sum()),
                'color': color,
            })
        
        return stalks
    
    def _compute_local_stalk_signature(self, local_grid: np.ndarray, n_eigs: int = 16) -> np.ndarray:
        """
        Compute spectral signature of a LOCAL stalk (position-invariant).
        
        This is the key to cross-task transfer: a 3x3 hollow square has
        the same eigenvalues regardless of where it sits on the global grid.
        
        Args:
            local_grid: Cropped local grid of the stalk
            n_eigs: Number of eigenvalues in signature
            
        Returns:
            Position-invariant spectral signature
        """
        h, w = local_grid.shape
        n = h * w
        
        if n < 2:
            # Trivial stalk - return zero signature
            return np.zeros(n_eigs, dtype=np.float32)
        
        # Build local Laplacian for this stalk
        A = np.zeros((n, n), dtype=np.float32)
        
        for r in range(h):
            for c in range(w):
                i = r * w + c
                color_i = local_grid[r, c]
                
                if color_i == self.background_color:
                    continue
                
                # 4-connected neighbors
                for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                    nr, nc = r + dr, c + dc
                    if 0 <= nr < h and 0 <= nc < w:
                        j = nr * w + nc
                        color_j = local_grid[nr, nc]
                        
                        if color_j == self.background_color:
                            continue
                        
                        if color_i == color_j:
                            A[i, j] = 1.0
                        else:
                            A[i, j] = 0.01
        
        # Laplacian: L = D - A
        D = np.diag(A.sum(axis=1))
        L = D - A
        
        # Eigendecomposition
        try:
            eigenvalues, _ = np.linalg.eigh(L)
            eigenvalues = np.sort(eigenvalues)
        except:
            return np.zeros(n_eigs, dtype=np.float32)
        
        # Take first n_eigs eigenvalues as signature
        sig = eigenvalues[:n_eigs] if len(eigenvalues) >= n_eigs else eigenvalues
        
        # Pad to fixed dimension
        if len(sig) < n_eigs:
            padded = np.zeros(n_eigs, dtype=np.float32)
            padded[:len(sig)] = sig
            sig = padded
        
        return sig.astype(np.float32)
    
    def compute_hierarchical_signature(self) -> np.ndarray:
        """
        Compute hierarchical signature: aggregate of local stalk signatures.
        
        This enables cross-task transfer by being position-invariant:
        - Concatenate sorted local stalk signatures
        - Pad/truncate to fixed dimension
        
        Returns:
            Hierarchical spectral signature
        """
        stalks = self.decompose_to_stalks()
        
        if not stalks:
            return np.zeros(self.signature_dims, dtype=np.float32)
        
        # Collect all local signatures, sorted by size (largest first)
        sorted_stalks = sorted(stalks, key=lambda s: s['n_pixels'], reverse=True)
        
        # Concatenate top stalk signatures
        all_sigs = []
        for stalk in sorted_stalks[:4]:  # Top 4 stalks
            all_sigs.extend(stalk['spectral_signature'][:4])  # First 4 eigenvalues each
        
        # Pad/truncate to signature_dims
        sig = np.zeros(self.signature_dims, dtype=np.float32)
        sig[:min(len(all_sigs), self.signature_dims)] = all_sigs[:self.signature_dims]
        
        return sig
    
    # =========================================================================
    # PHASE 2: EMERGENT OPERATORS (No Hardcoded Rules)
    # =========================================================================
    
    def compute_heat_kernel(self, t: float) -> np.ndarray:
        """
        Compute the Heat Kernel: H_t = exp(-t * L)
        
        This is the UNIVERSAL diffusion operator:
        - When applied to a grid vector, color "flows" along edges
        - Enclosed voids naturally get filled by surrounding color
        - t controls diffusion time (small t = local, large t = global)
        
        The system DISCOVERS that applying H_t to enclosed voids
        minimizes Free Energy - this is emergent "fill" behavior.
        
        Args:
            t: Diffusion time parameter
            
        Returns:
            Heat kernel matrix H_t
        """
        L, _ = self.build_laplacian()
        
        # H_t = exp(-t * L)
        # For numerical stability, use eigendecomposition
        eigenvalues, eigenvectors = self.compute_spectral_decomposition()
        
        # H_t = V @ diag(exp(-t * lambda)) @ V^T
        exp_eigenvalues = np.exp(-t * eigenvalues)
        H_t = eigenvectors @ np.diag(exp_eigenvalues) @ eigenvectors.T
        
        return H_t
    
    def compute_fiedler_permutation(self) -> np.ndarray:
        """
        Derive a permutation matrix from the Fiedler vector.
        
        The Fiedler vector (2nd eigenvector) defines a natural axis.
        Zero-crossings of the Fiedler vector partition the graph.
        Reflection across this axis = permutation matrix.
        
        This is EMERGENT reflection - derived from spectral properties,
        not hardcoded symmetry detection.
        
        Returns:
            Permutation matrix P for reflection
        """
        eigenvalues, eigenvectors = self.compute_spectral_decomposition()
        
        # Fiedler vector is 2nd eigenvector (skip constant first)
        fiedler_idx = 1 if eigenvalues[0] < 1e-10 else 0
        fiedler = eigenvectors[:, fiedler_idx]
        
        # Reshape to grid
        fiedler_grid = fiedler.reshape(self.H, self.W)
        
        # Find axis: column where Fiedler changes sign most
        sign_changes = np.abs(np.diff(np.sign(fiedler_grid), axis=1)).sum(axis=0)
        if sign_changes.max() > 0:
            axis_col = np.argmax(sign_changes)
        else:
            axis_col = self.W // 2
        
        # Build permutation matrix for horizontal reflection around axis
        P = np.zeros((self.N, self.N), dtype=np.float32)
        for r in range(self.H):
            for c in range(self.W):
                i = r * self.W + c
                # Mirror column around axis
                mirror_c = int(2 * axis_col - c)
                if 0 <= mirror_c < self.W:
                    j = r * self.W + mirror_c
                    P[i, j] = 1.0
                else:
                    P[i, i] = 1.0  # Can't mirror, stay in place
        
        return P
    
    def compute_rotation_permutation(self, k: int = 1) -> Optional[np.ndarray]:
        """
        Compute permutation matrix for k*90 degree rotation.
        
        Only valid for square grids.
        
        Args:
            k: Number of 90-degree rotations (1, 2, or 3)
            
        Returns:
            Permutation matrix P for rotation, or None if not square
        """
        if self.H != self.W:
            return None
        
        P = np.zeros((self.N, self.N), dtype=np.float32)
        
        for r in range(self.H):
            for c in range(self.W):
                i = r * self.W + c
                
                # Apply k rotations
                nr, nc = r, c
                for _ in range(k % 4):
                    nr, nc = nc, self.H - 1 - nr
                
                j = nr * self.W + nc
                P[i, j] = 1.0
        
        return P
    
    def discover_color_transition(self) -> Optional[np.ndarray]:
        """
        Discover color transition matrix from input/target relationship.
        
        If the transformation is a color permutation, this matrix encodes it.
        C[i, j] = probability that color i maps to color j.
        
        This is LEARNED from the data, not hardcoded.
        
        Returns:
            Color transition matrix or None
        """
        if self.target is None:
            return None
        
        # Find unique colors
        input_colors = np.unique(self.grid)
        target_colors = np.unique(self.target)
        max_color = max(input_colors.max(), target_colors.max()) + 1
        
        # Build transition counts
        C = np.zeros((int(max_color), int(max_color)), dtype=np.float32)
        
        for r in range(self.H):
            for c in range(self.W):
                ic = int(self.grid[r, c])
                tc = int(self.target[r, c])
                C[ic, tc] += 1
        
        # Normalize rows to get transition probabilities
        row_sums = C.sum(axis=1, keepdims=True)
        row_sums[row_sums == 0] = 1  # Avoid division by zero
        C = C / row_sums
        
        # Check if it's a valid permutation (each row has single 1)
        is_permutation = np.allclose(C.max(axis=1), 1.0) and np.allclose(C.sum(axis=1), 1.0)
        
        if is_permutation:
            # Make it exact
            C = (C == C.max(axis=1, keepdims=True)).astype(np.float32)
            return C
        
        return None
    
    # =========================================================================
    # PHASE 2B: SPECTRAL MORPHOLOGY (v4 - Continuous Operations)
    # =========================================================================
    
    def compute_spectral_dilation(self, t: float = 1.0, threshold: float = 0.1) -> np.ndarray:
        """
        Spectral Dilation: Grow objects via Heat Kernel diffusion.
        
        Apply H_t (Heat Kernel) and threshold: any pixel with heat > ε 
        becomes part of the object. This is the continuous equivalent
        of morphological dilation.
        
        Boundary condition: Neumann (heat reflects at boundary = growth)
        
        Args:
            t: Diffusion time (larger = more dilation)
            threshold: Heat threshold for inclusion
            
        Returns:
            Dilated grid
        """
        # Use cached heat kernel (avoids repeated O(N³) eigendecomposition)
        H_t = self.compute_cached_heat_kernel(t)
        
        # For each color, diffuse and threshold
        result = self.grid.copy()
        unique_colors = np.unique(self.grid)
        unique_colors = unique_colors[unique_colors != self.background_color]
        
        for color in unique_colors:
            color_mask = (self.grid == color).astype(float).flatten()
            if color_mask.sum() == 0:
                continue
            
            # Diffuse
            diffused = H_t @ color_mask
            diffused_grid = diffused.reshape(self.H, self.W)
            
            # Threshold: pixels with heat > threshold join the object
            # Only expand into background
            expansion = (diffused_grid > threshold) & (self.grid == 0)
            result[expansion] = color
        
        return result
    
    def compute_spectral_erosion(self, t: float = 1.0, threshold: float = 0.5) -> np.ndarray:
        """
        Spectral Erosion: Shrink objects via inverse heat flow.
        
        Apply negative heat flow (or equivalently, threshold at high heat):
        only pixels that are strongly connected to the core remain.
        
        Boundary condition: Dirichlet (heat escapes at boundary = shrinkage)
        
        Args:
            t: Erosion strength (larger = more erosion)
            threshold: Threshold for core membership (higher = more erosion)
            
        Returns:
            Eroded grid
        """
        # Use cached heat kernel (avoids repeated O(N³) eigendecomposition)
        H_t = self.compute_cached_heat_kernel(t)
        
        # For each color, diffuse and apply inverse threshold
        result = self.grid.copy()
        unique_colors = np.unique(self.grid)
        unique_colors = unique_colors[unique_colors != self.background_color]
        
        for color in unique_colors:
            color_mask = (self.grid == color).astype(float).flatten()
            if color_mask.sum() == 0:
                continue
            
            # Diffuse
            diffused = H_t @ color_mask
            diffused_grid = diffused.reshape(self.H, self.W)
            
            # Normalize by original value
            original_mask = self.grid == color
            if original_mask.any():
                max_heat = diffused_grid[original_mask].max()
                if max_heat > 0:
                    normalized = diffused_grid / max_heat
                    
                    # Erosion: remove pixels below threshold
                    eroded = (normalized < threshold) & original_mask
                    result[eroded] = 0
        
        return result
    
    def compute_translation_matrix(self, dx: int, dy: int) -> np.ndarray:
        """
        Compute translation (shift) matrix.
        
        This allows the thermodynamic loop to discover spatial translations
        as a learnable operation, not hardcoded.
        
        Args:
            dx: Horizontal shift (positive = right)
            dy: Vertical shift (positive = down)
            
        Returns:
            Translation permutation matrix S_{dx,dy}
        """
        S = np.zeros((self.N, self.N), dtype=np.float32)
        
        for r in range(self.H):
            for c in range(self.W):
                i = r * self.W + c
                
                # Source position (where this pixel came from)
                src_r = r - dy
                src_c = c - dx
                
                if 0 <= src_r < self.H and 0 <= src_c < self.W:
                    j = src_r * self.W + src_c
                    S[i, j] = 1.0
                # Pixels shifted out get background (handled by leaving S[i,:] = 0)
        
        return S
    
    def apply_color_transition(self, grid: np.ndarray, C: np.ndarray) -> np.ndarray:
        """Apply color transition matrix to grid."""
        result = np.zeros_like(grid)
        for r in range(grid.shape[0]):
            for c in range(grid.shape[1]):
                old_color = int(grid[r, c])
                if old_color < C.shape[0]:
                    new_color = np.argmax(C[old_color])
                    result[r, c] = new_color
                else:
                    result[r, c] = old_color
        return result
    
    # =========================================================================
    # PHASE 2C: INTER-STALK PHYSICS (v5 - Boundary Operators & Interactions)
    # =========================================================================
    
    def compute_stalk_boundary(self, stalk_mask: np.ndarray) -> np.ndarray:
        """
        Compute the Boundary Operator δ(stalk): pixels adjacent to background.
        
        In Sheaf Theory, the boundary is the interface where restriction maps
        connect local stalks. In physics, this is where interactions happen.
        
        Args:
            stalk_mask: Boolean mask of the stalk (H x W)
            
        Returns:
            Boolean mask of boundary pixels
        """
        boundary = np.zeros_like(stalk_mask, dtype=bool)
        
        for r in range(self.H):
            for c in range(self.W):
                if not stalk_mask[r, c]:
                    continue
                
                # Check if adjacent to background or grid edge
                is_boundary = False
                for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                    nr, nc = r + dr, c + dc
                    if nr < 0 or nr >= self.H or nc < 0 or nc >= self.W:
                        is_boundary = True
                        break
                    if self.grid[nr, nc] == 0 or not stalk_mask[nr, nc]:
                        is_boundary = True
                        break
                
                boundary[r, c] = is_boundary
        
        return boundary
    
    def compute_stalk_centroid(self, stalk_mask: np.ndarray) -> Tuple[float, float]:
        """Compute centroid (center of mass) of a stalk."""
        rows, cols = np.where(stalk_mask)
        if len(rows) == 0:
            return (self.H / 2, self.W / 2)
        return (float(rows.mean()), float(cols.mean()))
    
    def translate_until_collision(self, 
                                   source_stalk_id: int,
                                   target_stalk_id: int,
                                   direction: Tuple[int, int]) -> np.ndarray:
        """
        Translate Stalk A in direction (dx, dy) until δ(A) intersects δ(B).
        
        This implements "move object until it hits the wall/other object".
        
        Args:
            source_stalk_id: ID of stalk to move
            target_stalk_id: ID of stalk to collide with (or -1 for grid edge)
            direction: (dx, dy) unit direction
            
        Returns:
            Translated grid
        """
        stalks = self.decompose_to_stalks()
        
        if source_stalk_id >= len(stalks):
            return self.grid.copy()
        
        source_stalk = stalks[source_stalk_id]
        source_mask = source_stalk['mask']
        source_color = source_stalk['color']
        
        # Target boundary (or grid edge)
        if target_stalk_id >= 0 and target_stalk_id < len(stalks):
            target_mask = stalks[target_stalk_id]['mask']
            target_boundary = self.compute_stalk_boundary(target_mask)
        else:
            # Collide with grid edge or any other object
            target_boundary = None
        
        dx, dy = direction
        result = self.grid.copy()
        
        # Remove source from result
        result[source_mask] = 0
        
        # Translate until collision
        max_steps = max(self.H, self.W)
        best_offset = (0, 0)
        
        for step in range(1, max_steps):
            offset_r = step * dy
            offset_c = step * dx
            
            # Check if translated mask would collide
            collision = False
            valid = True
            
            rows, cols = np.where(source_mask)
            for r, c in zip(rows, cols):
                new_r = r + offset_r
                new_c = c + offset_c
                
                # Check grid bounds
                if new_r < 0 or new_r >= self.H or new_c < 0 or new_c >= self.W:
                    collision = True
                    break
                
                # Check collision with target boundary
                if target_boundary is not None and target_boundary[new_r, new_c]:
                    collision = True
                    break
                
                # Check collision with any non-source object
                if result[new_r, new_c] != 0:
                    collision = True
                    break
            
            if collision:
                break
            
            best_offset = (offset_r, offset_c)
        
        # Apply best offset
        rows, cols = np.where(source_mask)
        for r, c in zip(rows, cols):
            new_r = r + best_offset[0]
            new_c = c + best_offset[1]
            if 0 <= new_r < self.H and 0 <= new_c < self.W:
                result[new_r, new_c] = source_color
        
        return result
    
    def compute_geodesic_path(self, 
                               start: Tuple[int, int], 
                               end: Tuple[int, int]) -> List[Tuple[int, int]]:
        """
        Compute shortest path (geodesic) between two points on the grid.
        
        Uses BFS on the unweighted grid adjacency. This is the discrete
        analog of a geodesic on the semantic manifold.
        
        Args:
            start: (row, col) start position
            end: (row, col) end position
            
        Returns:
            List of (row, col) positions along the path
        """
        from collections import deque
        
        if start == end:
            return [start]
        
        visited = set()
        parent = {}
        queue = deque([start])
        visited.add(start)
        
        while queue:
            r, c = queue.popleft()
            
            if (r, c) == end:
                # Reconstruct path
                path = []
                current = end
                while current != start:
                    path.append(current)
                    current = parent[current]
                path.append(start)
                return path[::-1]
            
            for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                nr, nc = r + dr, c + dc
                if 0 <= nr < self.H and 0 <= nc < self.W:
                    if (nr, nc) not in visited:
                        visited.add((nr, nc))
                        parent[(nr, nc)] = (r, c)
                        queue.append((nr, nc))
        
        # No path found - return direct line
        return [start, end]
    
    def draw_geodesic_ray(self,
                          source_stalk_id: int,
                          target_stalk_id: int,
                          ray_color: int) -> np.ndarray:
        """
        Draw a geodesic ray (shortest path) between two stalk centroids.
        
        This implements "draw a line from A to B" as a matrix operation.
        
        Args:
            source_stalk_id: ID of source stalk
            target_stalk_id: ID of target stalk
            ray_color: Color to draw the ray
            
        Returns:
            Grid with geodesic ray drawn
        """
        stalks = self.decompose_to_stalks()
        
        if source_stalk_id >= len(stalks) or target_stalk_id >= len(stalks):
            return self.grid.copy()
        
        source_centroid = self.compute_stalk_centroid(stalks[source_stalk_id]['mask'])
        target_centroid = self.compute_stalk_centroid(stalks[target_stalk_id]['mask'])
        
        start = (int(round(source_centroid[0])), int(round(source_centroid[1])))
        end = (int(round(target_centroid[0])), int(round(target_centroid[1])))
        
        path = self.compute_geodesic_path(start, end)
        
        result = self.grid.copy()
        for r, c in path:
            if result[r, c] == 0:  # Only draw on background
                result[r, c] = ray_color
        
        return result
    
    def compute_stalk_adjacency_matrix(self) -> np.ndarray:
        """
        Compute adjacency matrix between stalks.
        
        A[i,j] = 1 if stalk i and stalk j are adjacent (share boundary pixels).
        This encodes the restriction maps in the cellular sheaf.
        
        Returns:
            (n_stalks x n_stalks) adjacency matrix
        """
        stalks = self.decompose_to_stalks()
        n = len(stalks)
        A = np.zeros((n, n), dtype=np.float32)
        
        for i, stalk_i in enumerate(stalks):
            boundary_i = self.compute_stalk_boundary(stalk_i['mask'])
            
            for j, stalk_j in enumerate(stalks):
                if i == j:
                    continue
                
                boundary_j = self.compute_stalk_boundary(stalk_j['mask'])
                
                # Check if boundaries are adjacent (within 1 pixel)
                rows_i, cols_i = np.where(boundary_i)
                rows_j, cols_j = np.where(boundary_j)
                
                for ri, ci in zip(rows_i, cols_i):
                    for rj, cj in zip(rows_j, cols_j):
                        if abs(ri - rj) <= 1 and abs(ci - cj) <= 1:
                            A[i, j] = 1.0
                            break
                    if A[i, j] > 0:
                        break
        
        return A
    
    def apply_relative_color(self,
                              source_stalk_id: int,
                              relation: str = 'adjacent') -> np.ndarray:
        """
        Paint Stalk A the color of a related Stalk B (gauge interaction).
        
        Relations:
        - 'adjacent': Color of most adjacent stalk
        - 'enclosing': Color of stalk that encloses this one
        - 'largest': Color of largest nearby stalk
        
        Args:
            source_stalk_id: ID of stalk to recolor
            relation: Type of relation to use
            
        Returns:
            Grid with recolored stalk
        """
        stalks = self.decompose_to_stalks()
        
        if source_stalk_id >= len(stalks):
            return self.grid.copy()
        
        source_stalk = stalks[source_stalk_id]
        source_mask = source_stalk['mask']
        
        # Find related stalk
        target_color = None
        
        if relation == 'adjacent':
            # Find most adjacent stalk by shared boundary
            A = self.compute_stalk_adjacency_matrix()
            adj_row = A[source_stalk_id]
            if adj_row.max() > 0:
                most_adjacent_id = int(np.argmax(adj_row))
                target_color = stalks[most_adjacent_id]['color']
        
        elif relation == 'enclosing':
            # Find stalk whose boundary surrounds this one
            source_boundary = self.compute_stalk_boundary(source_mask)
            rows, cols = np.where(source_boundary)
            
            best_encloser = None
            best_enclosure_score = 0
            
            for j, stalk_j in enumerate(stalks):
                if j == source_stalk_id:
                    continue
                
                # Count how many boundary pixels of source are adjacent to j
                enclosure_count = 0
                for r, c in zip(rows, cols):
                    for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                        nr, nc = r + dr, c + dc
                        if 0 <= nr < self.H and 0 <= nc < self.W:
                            if stalk_j['mask'][nr, nc]:
                                enclosure_count += 1
                                break
                
                if enclosure_count > best_enclosure_score:
                    best_enclosure_score = enclosure_count
                    best_encloser = j
            
            if best_encloser is not None:
                target_color = stalks[best_encloser]['color']
        
        elif relation == 'largest':
            # Find largest adjacent stalk
            A = self.compute_stalk_adjacency_matrix()
            adj_row = A[source_stalk_id]
            
            best_size = 0
            for j in range(len(stalks)):
                if adj_row[j] > 0 and stalks[j]['n_pixels'] > best_size:
                    best_size = stalks[j]['n_pixels']
                    target_color = stalks[j]['color']
        
        if target_color is None:
            return self.grid.copy()
        
        result = self.grid.copy()
        result[source_mask] = target_color
        return result
    
    # =========================================================================
    # PHASE 3: THERMODYNAMIC DISCOVERY LOOP
    # =========================================================================
    
    def compute_free_energy(self, state: np.ndarray) -> float:
        """
        Compute Free Energy = deviation from target.
        
        This is the quantity we minimize through thermodynamic relaxation.
        """
        if self.target is None:
            return float('inf')
        
        # Ensure shapes match
        if state.shape != self.target.shape:
            return float('inf')
        
        return float(np.sum(np.abs(state - self.target)))
    
    # =========================================================================
    # v6: DEFECT GRADIENT ANALYZER (Vectorized Instructive Signals)
    # =========================================================================
    
    def analyze_free_energy_gradient(self, 
                                      current_state: np.ndarray) -> List[Dict[str, Any]]:
        """
        Analyze the Defect Matrix D = Target - State to extract vectorized signals.
        
        Instead of random search over 89 operators, this method computes the
        exact operator parameters directly from the defect structure.
        
        Returns a list of instructed operators in priority order.
        """
        if self.target is None:
            return []
        
        if current_state.shape != self.target.shape:
            return []
        
        instructed_ops = []
        
        # Compute defect matrix (where they differ)
        D = (self.target != current_state).astype(np.int32)
        defect_positions = np.argwhere(D > 0)
        
        if len(defect_positions) == 0:
            return []  # Already solved
        
        # Get stalks from current state and target state
        stalks = self.decompose_to_stalks()
        n_stalks = len(stalks)
        target_stalks = self._decompose_grid_to_stalks(self.target)
        
        # =====================================================================
        # 1. STALK-TO-STALK ISOMORPHISM: Detect translations + color changes
        # =====================================================================
        # For each current stalk, find shape-isomorphic target stalks
        # This decouples Shape (topological invariant) from Color/Position (gauge)
        
        for stalk_id, stalk in enumerate(stalks):
            stalk_mask = stalk['mask']
            stalk_color = stalk['color']
            stalk_positions = np.argwhere(stalk_mask)
            
            if len(stalk_positions) == 0:
                continue
            
            # Compute current stalk centroid and local boolean shape
            curr_centroid = stalk_positions.mean(axis=0)
            r_min, r_max = stalk_positions[:, 0].min(), stalk_positions[:, 0].max()
            c_min, c_max = stalk_positions[:, 1].min(), stalk_positions[:, 1].max()
            local_h, local_w = r_max - r_min + 1, c_max - c_min + 1
            curr_local_shape = np.zeros((local_h, local_w), dtype=bool)
            for r, c in stalk_positions:
                curr_local_shape[r - r_min, c - c_min] = True
            
            # Search for isomorphic target stalks (exact shape match, any color)
            best_match = None
            best_iou = 0.0
            
            for tgt_stalk in target_stalks:
                tgt_shape = tgt_stalk['local_shape']
                
                # Quick dimension check
                if tgt_shape.shape != curr_local_shape.shape:
                    continue
                
                # Exact boolean shape match (topological isomorphism)
                if np.array_equal(tgt_shape, curr_local_shape):
                    # Perfect shape match! Extract morphism vectors
                    tgt_centroid = tgt_stalk['centroid']
                    tgt_color = tgt_stalk['color']
                    
                    # Spatial vector: f(X) -> Y
                    dy = int(round(tgt_centroid[0] - curr_centroid[0]))
                    dx = int(round(tgt_centroid[1] - curr_centroid[1]))
                    
                    # Gauge vector: color transition
                    color_changed = (tgt_color != stalk_color)
                    
                    # Prioritize by pixel count (larger matches are more confident)
                    iou = tgt_stalk['n_pixels']
                    if iou > best_iou:
                        best_iou = iou
                        best_match = {
                            'dx': dx, 'dy': dy,
                            'src_color': stalk_color,
                            'tgt_color': tgt_color,
                            'color_changed': color_changed,
                            'n_pixels': tgt_stalk['n_pixels']
                        }
            
            if best_match is not None:
                dx, dy = best_match['dx'], best_match['dy']
                src_color = best_match['src_color']
                tgt_color = best_match['tgt_color']
                color_changed = best_match['color_changed']
                n_pixels = best_match['n_pixels']
                
                translated = (dx != 0 or dy != 0)
                
                if translated and color_changed:
                    # COMPOSITE MORPHISM: Translation + Color Gauge
                    # Build the composed operator
                    C = np.eye(10)
                    C[src_color, src_color] = 0
                    C[src_color, tgt_color] = 1
                    
                    instructed_ops.append({
                        'type': 'composition',
                        'operators': [
                            {'type': 'translation', 'dx': dx, 'dy': dy},
                            {'type': 'color_transition', 'matrix': C}
                        ],
                        'name': f'gradient_compose_t{dx},{dy}_c{src_color}to{tgt_color}',
                        'confidence': 1.0,
                        'source': 'stalk_isomorphism'
                    })
                elif translated:
                    # Pure translation
                    instructed_ops.append({
                        'type': 'translation',
                        'dx': dx,
                        'dy': dy,
                        'name': f'gradient_translate_dx{dx}_dy{dy}',
                        'confidence': 1.0,
                        'source': 'stalk_isomorphism'
                    })
                elif color_changed:
                    # Pure color change (detected via isomorphism, not pixel diff)
                    C = np.eye(10)
                    C[src_color, src_color] = 0
                    C[src_color, tgt_color] = 1
                    
                    instructed_ops.append({
                        'type': 'color_transition',
                        'matrix': C,
                        'name': f'gradient_color_{src_color}_to_{tgt_color}',
                        'confidence': 1.0,
                        'source': 'stalk_isomorphism'
                    })
        
        # =====================================================================
        # 2. COLOR GRADIENTS: Detect exact color mappings
        # =====================================================================
        # If the defect is purely a color change (same positions, different colors)
        
        # Build pixel-wise color transition from state to target
        color_map = {}
        for r in range(current_state.shape[0]):
            for c in range(current_state.shape[1]):
                curr_c = int(current_state[r, c])
                tgt_c = int(self.target[r, c])
                if curr_c != tgt_c and curr_c > 0:  # Non-bg pixel that needs change
                    if curr_c not in color_map:
                        color_map[curr_c] = {}
                    if tgt_c not in color_map[curr_c]:
                        color_map[curr_c][tgt_c] = 0
                    color_map[curr_c][tgt_c] += 1
        
        # Find dominant color transitions
        for src_color, targets in color_map.items():
            if targets:
                dominant_target = max(targets.keys(), key=lambda k: targets[k])
                count = targets[dominant_target]
                
                # Build transition matrix
                C = np.eye(10)
                C[src_color, src_color] = 0
                C[src_color, dominant_target] = 1
                
                instructed_ops.append({
                    'type': 'color_transition',
                    'matrix': C,
                    'name': f'gradient_color_{src_color}_to_{dominant_target}',
                    'confidence': float(count) / max(len(defect_positions), 1),
                    'source': 'defect_gradient'
                })
        
        # =====================================================================
        # 3. MORPHOLOGICAL GRADIENTS: Detect dilation/erosion patterns
        # =====================================================================
        
        for stalk_id, stalk in enumerate(stalks):
            stalk_mask = stalk['mask']
            stalk_color = stalk['color']
            
            # Compute boundary of this stalk (pass mask, not id)
            boundary = self.compute_stalk_boundary(stalk_mask)
            boundary_positions = set(map(tuple, np.argwhere(boundary)))
            
            # Find defect positions
            defect_set = set(map(tuple, defect_positions))
            
            # Check if defect is adjacent to boundary (dilation signal)
            adjacent_to_boundary = 0
            for r, c in defect_set:
                for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                    if (r + dr, c + dc) in boundary_positions:
                        adjacent_to_boundary += 1
                        break
            
            if adjacent_to_boundary > 0:
                # Check if it's growth (target has more) or shrinkage (target has less)
                target_fg = (self.target > 0).sum()
                current_fg = (current_state > 0).sum()
                
                if target_fg > current_fg:
                    # Needs dilation
                    instructed_ops.append({
                        'type': 'spectral_dilation',
                        't': 1.0,
                        'threshold': 0.1,
                        'name': f'gradient_dilation_s{stalk_id}',
                        'confidence': adjacent_to_boundary / max(len(defect_positions), 1),
                        'source': 'defect_gradient'
                    })
                elif target_fg < current_fg:
                    # Needs erosion
                    instructed_ops.append({
                        'type': 'spectral_erosion',
                        't': 1.0,
                        'threshold': 0.5,
                        'name': f'gradient_erosion_s{stalk_id}',
                        'confidence': adjacent_to_boundary / max(len(defect_positions), 1),
                        'source': 'defect_gradient'
                    })
        
        # =====================================================================
        # 4. GEODESIC GRADIENTS: Detect 1D path patterns between stalks
        # =====================================================================
        
        if n_stalks >= 2:
            # Check if defect forms a line between two stalks
            defect_rows = defect_positions[:, 0]
            defect_cols = defect_positions[:, 1]
            
            # Check for horizontal or vertical alignment (1D path signature)
            row_variance = np.var(defect_rows) if len(defect_rows) > 1 else 0
            col_variance = np.var(defect_cols) if len(defect_cols) > 1 else 0
            
            is_line = (row_variance < 1.0 or col_variance < 1.0) and len(defect_positions) > 2
            
            if is_line:
                # Find which stalks this line connects
                defect_centroid = defect_positions.mean(axis=0)
                
                # Find two closest stalks to defect centroid
                stalk_distances = []
                for i, s in enumerate(stalks):
                    # Compute centroid from mask
                    s_positions = np.argwhere(s['mask'])
                    if len(s_positions) == 0:
                        continue
                    s_centroid = s_positions.mean(axis=0)
                    dist = np.sqrt((s_centroid[0] - defect_centroid[0])**2 + 
                                   (s_centroid[1] - defect_centroid[1])**2)
                    stalk_distances.append((i, dist))
                
                stalk_distances.sort(key=lambda x: x[1])
                
                if len(stalk_distances) >= 2:
                    source_id = stalk_distances[0][0]
                    target_id = stalk_distances[1][0]
                    
                    # Infer ray color from defect
                    defect_colors = self.target[defect_positions[:, 0], defect_positions[:, 1]]
                    ray_color = int(np.bincount(defect_colors.astype(int)).argmax())
                    
                    instructed_ops.append({
                        'type': 'geodesic_ray',
                        'source_stalk_id': source_id,
                        'target_stalk_id': target_id,
                        'ray_color': ray_color,
                        'name': f'gradient_ray_s{source_id}_t{target_id}',
                        'confidence': 0.8,
                        'source': 'defect_gradient'
                    })
        
        # Sort by confidence (highest first)
        instructed_ops.sort(key=lambda x: x.get('confidence', 0), reverse=True)
        
        return instructed_ops
    
    def apply_operator_to_grid(self, 
                                grid: np.ndarray, 
                                operator: Dict[str, Any]) -> np.ndarray:
        """
        Apply a discovered operator to the grid.
        
        Operators are matrix operations:
        - 'heat_kernel': Diffusion via H_t
        - 'permutation': Reflection/rotation via P
        - 'color_transition': Color mapping via C
        - 'diffusion_fill': Fill enclosed voids via diffusion
        """
        op_type = operator['type']
        
        if op_type == 'heat_kernel':
            t = operator['t']
            H_t = self.compute_heat_kernel(t)
            
            # Apply per color channel with voting
            color_scores = np.zeros((grid.shape[0], grid.shape[1], 10))
            
            for color in range(1, 10):  # ARC colors 1-9
                color_mask = (grid == color).astype(float).flatten()
                if color_mask.sum() > 0:
                    diffused = H_t @ color_mask
                    color_scores[:, :, color] = diffused.reshape(grid.shape)
            
            # Winner-take-all for each pixel
            result = np.argmax(color_scores, axis=2).astype(float)
            
            # Preserve original non-background pixels
            result[grid > 0] = grid[grid > 0]
            
            return result
        
        elif op_type == 'diffusion_fill':
            # Emergent fill via FULL-GRID Laplacian (including background)
            # This allows heat to diffuse into void regions
            t = operator.get('t', 1.0)
            fill_color = operator.get('fill_color', 1)
            
            # Use cached heat kernel (avoids repeated O(N³) eigendecomposition)
            H_t = self.compute_cached_heat_kernel(t)
            
            # Diffuse foreground indicator on full graph
            fg_mask = (grid > 0).astype(float).flatten()
            diffused = H_t @ fg_mask
            diffused_grid = diffused.reshape(grid.shape)
            
            # Fill where diffusion accumulated but original was empty
            # Key insight: enclosed voids receive diffusion from ALL sides
            # Use adaptive threshold based on local maxima
            bg_diffusion = diffused_grid[grid == 0]
            fg_diffusion = diffused_grid[grid > 0]
            thresh_mode = operator.get('thresh_mode', 'adaptive')
            
            if len(bg_diffusion) > 0 and len(fg_diffusion) > 0:
                bg_max = bg_diffusion.max()
                bg_median = np.median(bg_diffusion)
                bg_mean = bg_diffusion.mean()
                
                if thresh_mode == 'adaptive':
                    # Adaptive: threshold at high percentile
                    threshold = np.percentile(bg_diffusion, 75) if len(bg_diffusion) > 3 else bg_max * 0.7
                elif thresh_mode == 'high':
                    # High threshold: only fill very enclosed regions
                    threshold = bg_max * 0.9
                elif thresh_mode == 'low':
                    # Low threshold: fill more aggressively
                    threshold = bg_mean + (bg_max - bg_mean) * 0.3
                else:
                    threshold = (bg_median + bg_max) / 2
            else:
                threshold = 0.3
            
            result = grid.copy()
            fill_mask = (diffused_grid > threshold) & (grid == 0)
            result[fill_mask] = fill_color
            
            return result
            
        elif op_type == 'permutation':
            P = operator['matrix']
            grid_vec = grid.flatten()
            result_vec = np.zeros_like(grid_vec)
            
            # Permute pixel positions
            for i in range(self.N):
                j = np.argmax(P[i])
                result_vec[i] = grid_vec[j]
            
            return result_vec.reshape(grid.shape)
            
        elif op_type == 'color_transition':
            C = operator['matrix']
            return self.apply_color_transition(grid, C)
        
        elif op_type == 'spectral_dilation':
            # v4: Morphological dilation via heat diffusion
            t = operator.get('t', 1.0)
            threshold = operator.get('threshold', 0.1)
            return self.compute_spectral_dilation(t=t, threshold=threshold)
        
        elif op_type == 'spectral_erosion':
            # v4: Morphological erosion via inverse heat flow
            t = operator.get('t', 1.0)
            threshold = operator.get('threshold', 0.5)
            return self.compute_spectral_erosion(t=t, threshold=threshold)
        
        elif op_type == 'translation':
            # v4: Spatial translation via shift matrix
            dx = operator.get('dx', 0)
            dy = operator.get('dy', 0)
            S = self.compute_translation_matrix(dx, dy)
            grid_vec = grid.flatten()
            result_vec = np.zeros_like(grid_vec)
            
            for i in range(self.N):
                row = S[i]
                if row.sum() > 0:
                    j = np.argmax(row)
                    result_vec[i] = grid_vec[j]
                # else: stays 0 (background)
            
            return result_vec.reshape(grid.shape)
        
        # =====================================================================
        # v5: INTER-STALK PHYSICS OPERATORS
        # =====================================================================
        
        elif op_type == 'translate_until_collision':
            # v5: Move stalk until it hits another object or grid edge
            source_id = operator.get('source_stalk_id', 0)
            target_id = operator.get('target_stalk_id', -1)
            direction = operator.get('direction', (1, 0))
            return self.translate_until_collision(source_id, target_id, direction)
        
        elif op_type == 'geodesic_ray':
            # v5: Draw shortest path between stalk centroids
            source_id = operator.get('source_stalk_id', 0)
            target_id = operator.get('target_stalk_id', 1)
            ray_color = operator.get('ray_color', 1)
            return self.draw_geodesic_ray(source_id, target_id, ray_color)
        
        elif op_type == 'relative_color':
            # v5: Paint stalk the color of a related stalk (gauge interaction)
            source_id = operator.get('source_stalk_id', 0)
            relation = operator.get('relation', 'adjacent')
            return self.apply_relative_color(source_id, relation)
        
        elif op_type == 'composed' or op_type == 'composition':
            # v5/v6: Composition of multiple operators (bundle morphism)
            sub_operators = operator.get('operators', [])
            result = grid.copy()
            for sub_op in sub_operators:
                result = self.apply_operator_to_grid(result, sub_op)
            return result
        
        return grid

    def apply_operator_sequence(self,
                                grid: np.ndarray,
                                operators: List[Dict[str, Any]]) -> np.ndarray:
        """Apply a sequence of operators in order: X' = T_n ... T_2 T_1 X."""
        state = grid.copy()
        for op in operators:
            state = self.apply_operator_to_grid(state, op)
        return state

    def _try_warm_start(self,
                        atlas: "EmergentSheafAtlas",
                        signature: np.ndarray,
                        top_k: int = 3,
                        verbose: bool = False) -> Dict[str, Any]:
        """
        Fast loop: retrieve top-k similar signatures and test their operator sequences.
        """
        matches = atlas.find_top_k_charts(signature, k=top_k, min_similarity=0.0)
        if not matches:
            return {
                'success': False,
                'reason': 'atlas_empty',
                'method': 'atlas_warm_start',
                'warm_candidates': 0
            }

        best_energy = float('inf')
        best_state = None
        best_match = None

        for match in matches:
            chart_id = match['id']
            similarity = match['similarity']
            operators = atlas.get_operators(chart_id)
            if not operators:
                continue

            try:
                candidate = self.apply_operator_sequence(self.grid, operators)
                energy = self.compute_free_energy(candidate)
            except Exception:
                continue

            if energy < best_energy:
                best_energy = energy
                best_state = candidate
                best_match = match

            if energy < 0.5:
                if verbose:
                    print(f"  Warm-start hit: chart={chart_id}, sim={similarity:.3f}, E={energy:.3f}")
                return {
                    'success': True,
                    'method': 'atlas_warm_start',
                    'result': candidate,
                    'operators': operators,
                    'final_energy': energy,
                    'chart_id': chart_id,
                    'similarity': similarity,
                    'warm_candidates': len(matches)
                }

        return {
            'success': False,
            'method': 'atlas_warm_start',
            'reason': 'warm_start_miss',
            'final_energy': best_energy,
            'best_state': best_state,
            'best_match': best_match,
            'warm_candidates': len(matches)
        }
    
    def thermodynamic_discovery(self, 
                                 max_iterations: int = 50,
                                 temperature_schedule: str = 'exponential',
                                 verbose: bool = False) -> Dict[str, Any]:
        """
        v6: Vectorized Instructive Signal Discovery.
        
        Two-step process (Francioni et al., 2026):
        1. INSTRUCTED PROPOSAL: Analyze D = Target - State for vectorized signals
           - If gradient analyzer returns exact instruction, apply immediately
           - O(1) inference instead of O(n) search
        2. RANDOM BABBLING (Fallback): Only if no clear signal, search operators
        
        NO hardcoded rules - gradient analysis is pure matrix math on defects.
        """
        if self.target is None:
            return {'success': False, 'reason': 'No target'}
        
        # Shape check
        if self.grid.shape != self.target.shape:
            return {'success': False, 'reason': 'Shape mismatch'}
        
        # Adaptive iteration limit based on grid size (prevent O(N³) blowup)
        # Small grids: full iterations, Large grids: fewer iterations
        if self.N > 200:  # >14x14 grid
            max_iterations = min(max_iterations, 10)
        if self.N > 400:  # >20x20 grid
            max_iterations = min(max_iterations, 5)
        
        # Hard time limit per solve attempt (prevents getting stuck)
        import time as _time
        start_time = _time.time()
        max_solve_time = 30.0 if self.N > 200 else 60.0  # seconds
        
        current_state = self.grid.copy()
        current_energy = self.compute_free_energy(current_state)
        
        best_state = current_state.copy()
        best_energy = current_energy
        accepted_operators = []
        
        # Track vectorized vs random proposals
        vectorized_accepts = 0
        random_accepts = 0
        
        # Temperature for simulated annealing (fallback only)
        T = 10.0
        T_min = 0.01
        
        for iteration in range(max_iterations):
            # Check time limit
            if _time.time() - start_time > max_solve_time:
                break
            
            # =================================================================
            # STEP 1: VECTORIZED INSTRUCTED PROPOSAL (v6)
            # =================================================================
            instructed_ops = self.analyze_free_energy_gradient(current_state)
            
            found_instruction = False
            if instructed_ops:
                # Try instructed operators in confidence order
                for op in instructed_ops[:5]:  # Top 5 by confidence
                    try:
                        new_state = self.apply_operator_to_grid(current_state, op)
                        new_energy = self.compute_free_energy(new_state)
                        
                        if new_energy < current_energy:
                            current_state = new_state
                            current_energy = new_energy
                            accepted_operators.append(op)
                            vectorized_accepts += 1
                            found_instruction = True
                            
                            if verbose:
                                op_name = op.get('name', op['type'])
                                conf = op.get('confidence', 0)
                                print(f"  Iter {iteration}: VECTORIZED {op_name} (conf={conf:.2f}), E={current_energy:.1f}")
                            
                            if current_energy < best_energy:
                                best_state = current_state.copy()
                                best_energy = current_energy
                            
                            # Found solution?
                            if current_energy < 0.5:
                                return {
                                    'success': True,
                                    'method': 'vectorized_discovery',
                                    'result': best_state,
                                    'operators': accepted_operators,
                                    'iterations': iteration + 1,
                                    'final_energy': best_energy,
                                    'vectorized_accepts': vectorized_accepts,
                                    'random_accepts': random_accepts
                                }
                            break  # Move to next iteration after accepting
                    except Exception:
                        continue
            
            # =================================================================
            # STEP 2: RANDOM BABBLING FALLBACK (only if no instruction worked)
            # =================================================================
            if not found_instruction:
                candidates = self._generate_candidate_operators()
                
                # Try ALL candidates and find the BEST one (greedy)
                best_candidate = None
                best_candidate_state = None
                best_candidate_energy = current_energy
                
                for op in candidates:
                    try:
                        new_state = self.apply_operator_to_grid(current_state, op)
                        new_energy = self.compute_free_energy(new_state)
                        
                        if new_energy < best_candidate_energy:
                            best_candidate = op
                            best_candidate_state = new_state
                            best_candidate_energy = new_energy
                    except Exception:
                        continue
                
                if best_candidate is not None and best_candidate_energy < current_energy:
                    current_state = best_candidate_state
                    current_energy = best_candidate_energy
                    accepted_operators.append(best_candidate)
                    random_accepts += 1
                    
                    if verbose:
                        op_name = best_candidate.get('name', best_candidate['type'])
                        print(f"  Iter {iteration}: RANDOM {op_name}, E={current_energy:.1f}")
                    
                    if current_energy < best_energy:
                        best_state = current_state.copy()
                        best_energy = current_energy
                    
                    if current_energy < 0.5:
                        return {
                            'success': True,
                            'method': 'thermodynamic_discovery',
                            'result': best_state,
                            'operators': accepted_operators,
                            'iterations': iteration + 1,
                            'final_energy': best_energy,
                            'vectorized_accepts': vectorized_accepts,
                            'random_accepts': random_accepts
                        }
                else:
                    # No improvement - try Boltzmann escape
                    if len(candidates) > 0 and T > T_min:
                        op = candidates[np.random.randint(len(candidates))]
                        try:
                            new_state = self.apply_operator_to_grid(current_state, op)
                            new_energy = self.compute_free_energy(new_state)
                            delta_E = new_energy - current_energy
                            
                            if np.random.random() < np.exp(-delta_E / max(T, 1e-10)):
                                current_state = new_state
                                current_energy = new_energy
                        except:
                            pass
            
            # Cool down
            if temperature_schedule == 'exponential':
                T *= 0.9
            else:
                T = max(T - 0.5, T_min)
        
        return {
            'success': best_energy < 0.5,
            'method': 'thermodynamic_discovery',
            'result': best_state,
            'operators': accepted_operators,
            'iterations': max_iterations,
            'final_energy': best_energy,
            'vectorized_accepts': vectorized_accepts,
            'random_accepts': random_accepts
        }
    
    def _generate_candidate_operators(self) -> List[Dict[str, Any]]:
        """
        Generate candidate operators from the continuous operator space.
        
        This explores:
        1. Heat kernels with different t values (diffusion)
        2. Diffusion fill (emergent hole-filling)
        3. Permutation matrices (reflection, rotation)
        4. Color transitions (learned from data)
        
        NO hardcoded ARC rules - just mathematical operators.
        
        For large grids (>200 pixels), generates fewer candidates to prevent slowdown.
        """
        candidates = []
        
        # Adaptive candidate generation based on grid size
        is_large_grid = self.N > 200
        
        # 1. Heat kernels with various diffusion times
        heat_t_values = [0.5, 1.0, 2.0] if is_large_grid else [0.1, 0.5, 1.0, 2.0, 5.0]
        for t in heat_t_values:
            candidates.append({
                'type': 'heat_kernel',
                't': t
            })
        
        # 2. Diffusion fill - emergent void filling with multi-scale search
        # Learn fill color from target if available
        if self.target is not None:
            # Find colors in target that aren't in input
            input_colors = set(np.unique(self.grid).astype(int)) - {0}
            target_colors = set(np.unique(self.target).astype(int)) - {0}
            new_colors = target_colors - input_colors
            
            # Scale t by grid size for adaptive diffusion
            scale = (self.H + self.W) / 10.0
            
            # Reduce candidates for large grids
            t_bases = [0.5, 1.0] if is_large_grid else [0.3, 0.5, 1.0, 2.0, 3.0]
            thresh_modes = ['adaptive'] if is_large_grid else ['adaptive', 'high', 'low']
            
            for fill_color in new_colors:
                for t_base in t_bases:
                    t = t_base * scale
                    for thresh_mode in thresh_modes:
                        candidates.append({
                            'type': 'diffusion_fill',
                            't': t,
                            'fill_color': int(fill_color),
                            'thresh_mode': thresh_mode
                        })
        
        # 2. Fiedler-derived reflection
        try:
            P_reflect = self.compute_fiedler_permutation()
            candidates.append({
                'type': 'permutation',
                'matrix': P_reflect,
                'name': 'fiedler_reflection'
            })
        except:
            pass
        
        # 3. Rotation permutations (if square)
        for k in [1, 2, 3]:
            P_rot = self.compute_rotation_permutation(k)
            if P_rot is not None:
                candidates.append({
                    'type': 'permutation',
                    'matrix': P_rot,
                    'name': f'rotation_{k*90}'
                })
        
        # 4. Color transition (learned from target)
        C = self.discover_color_transition()
        if C is not None:
            candidates.append({
                'type': 'color_transition',
                'matrix': C,
                'name': 'learned_color_map'
            })
        
        # =====================================================================
        # v4: SPECTRAL MORPHOLOGY OPERATORS
        # =====================================================================
        
        # Skip expensive spectral morphology for large grids
        if not is_large_grid:
            # 5. Spectral Dilation (grow objects via heat diffusion)
            for t in [0.5, 1.0, 2.0]:
                for threshold in [0.05, 0.1, 0.2]:
                    candidates.append({
                        'type': 'spectral_dilation',
                        't': t,
                        'threshold': threshold,
                        'name': f'dilation_t{t}_th{threshold}'
                    })
            
            # 6. Spectral Erosion (shrink objects via inverse heat)
            for t in [0.5, 1.0, 2.0]:
                for threshold in [0.3, 0.5, 0.7]:
                    candidates.append({
                        'type': 'spectral_erosion',
                        't': t,
                        'threshold': threshold,
                        'name': f'erosion_t{t}_th{threshold}'
                    })
        
        # 7. Translation operators (spatial shifts)
        # Discover translation by comparing stalk positions input vs target
        if self.target is not None:
            # Infer likely translations from stalk movement
            candidate_shifts = self._infer_translation_candidates()
            for dx, dy in candidate_shifts:
                candidates.append({
                    'type': 'translation',
                    'dx': dx,
                    'dy': dy,
                    'name': f'translate_dx{dx}_dy{dy}'
                })
        
        # =====================================================================
        # v5: INTER-STALK PHYSICS OPERATORS
        # =====================================================================
        
        stalks = self.decompose_to_stalks()
        n_stalks = len(stalks)
        
        if n_stalks >= 1:
            # 8. Translate-until-collision (move stalk until it hits something)
            directions = [(1, 0), (-1, 0), (0, 1), (0, -1)]  # R, L, D, U
            for source_id in range(min(n_stalks, 3)):  # Top 3 stalks
                for direction in directions:
                    # Collide with grid edge
                    candidates.append({
                        'type': 'translate_until_collision',
                        'source_stalk_id': source_id,
                        'target_stalk_id': -1,  # Grid edge
                        'direction': direction,
                        'name': f'collision_s{source_id}_d{direction}'
                    })
                    # Collide with other stalks
                    for target_id in range(min(n_stalks, 3)):
                        if target_id != source_id:
                            candidates.append({
                                'type': 'translate_until_collision',
                                'source_stalk_id': source_id,
                                'target_stalk_id': target_id,
                                'direction': direction,
                                'name': f'collision_s{source_id}_t{target_id}_d{direction}'
                            })
        
        if n_stalks >= 2:
            # 9. Geodesic rays (draw lines between stalks)
            # Infer ray color from target
            if self.target is not None:
                target_colors = set(np.unique(self.target).astype(int)) - {0}
                input_colors = set(np.unique(self.grid).astype(int)) - {0}
                new_colors = target_colors - input_colors
                ray_colors = list(new_colors) if new_colors else list(target_colors)[:1]
            else:
                ray_colors = [1]
            
            for source_id in range(min(n_stalks, 3)):
                for target_id in range(min(n_stalks, 3)):
                    if source_id < target_id:
                        for ray_color in ray_colors[:2]:
                            candidates.append({
                                'type': 'geodesic_ray',
                                'source_stalk_id': source_id,
                                'target_stalk_id': target_id,
                                'ray_color': int(ray_color),
                                'name': f'ray_s{source_id}_t{target_id}_c{ray_color}'
                            })
            
            # 10. Relative color operators (gauge interactions)
            for source_id in range(min(n_stalks, 4)):
                for relation in ['adjacent', 'enclosing', 'largest']:
                    candidates.append({
                        'type': 'relative_color',
                        'source_stalk_id': source_id,
                        'relation': relation,
                        'name': f'recolor_s{source_id}_{relation}'
                    })
        
        # 11. Composed operators (chains of 2 operators)
        # Only generate a few strategic compositions to avoid combinatorial explosion
        if n_stalks >= 1 and self.target is not None:
            # Translation + Color change
            for source_id in range(min(n_stalks, 2)):
                for direction in [(1, 0), (0, 1)]:
                    candidates.append({
                        'type': 'composed',
                        'operators': [
                            {'type': 'translate_until_collision', 
                             'source_stalk_id': source_id, 
                             'target_stalk_id': -1, 
                             'direction': direction},
                            {'type': 'relative_color', 
                             'source_stalk_id': source_id, 
                             'relation': 'adjacent'}
                        ],
                        'name': f'translate_then_recolor_s{source_id}'
                    })
        
        return candidates
    
    def _infer_translation_candidates(self) -> List[Tuple[int, int]]:
        """
        Infer likely translation offsets by comparing input/target stalk positions.
        
        Returns list of (dx, dy) candidate shifts.
        """
        candidates = set()
        
        # Always include small shifts
        for d in [-2, -1, 0, 1, 2]:
            candidates.add((d, 0))
            candidates.add((0, d))
        
        # Compare input vs target centroids
        input_stalks = self.decompose_to_stalks()
        
        if not input_stalks:
            return list(candidates)
        
        # Create target engine temporarily
        target_engine = EmergentSheafEngine(self.target, signature_dims=self.signature_dims)
        target_stalks = target_engine.decompose_to_stalks()
        
        # Match stalks by spectral similarity and infer shifts
        for inp_stalk in input_stalks[:3]:  # Top 3 stalks
            inp_sig = inp_stalk['spectral_signature']
            inp_pos = inp_stalk['position']
            
            best_match = None
            best_sim = -1
            
            for tgt_stalk in target_stalks:
                tgt_sig = tgt_stalk['spectral_signature']
                sim = float(np.dot(inp_sig, tgt_sig) / (np.linalg.norm(inp_sig) * np.linalg.norm(tgt_sig) + 1e-10))
                
                if sim > best_sim:
                    best_sim = sim
                    best_match = tgt_stalk
            
            if best_match is not None and best_sim > 0.8:
                tgt_pos = best_match['position']
                dx = tgt_pos[1] - inp_pos[1]
                dy = tgt_pos[0] - inp_pos[0]
                candidates.add((dx, dy))
        
        return list(candidates)
    
    # =========================================================================
    # UNIFIED SOLVE METHOD
    # =========================================================================
    
    def solve(self,
              verbose: bool = False,
              atlas: Optional["EmergentSheafAtlas"] = None,
              warm_top_k: int = 3,
              use_hierarchical: bool = True) -> Dict[str, Any]:
        """
        Solve with perception-action hierarchy (v4: local stalk signatures).
        
        1) Compute HIERARCHICAL spectral signature (local stalk geometry)
        2) Atlas warm start with position-invariant matching
        3) Slow thermodynamic discovery fallback
        
        v4 Key insight: Index by LOCAL stalk geometry, not global grid.
        A 3x3 hollow square has the same eigenvalues regardless of position.
        """
        if self.target is None:
            return {'success': False, 'reason': 'No target'}
        
        # Shape check - handle bounding box extraction
        if self.grid.shape != self.target.shape:
            bbox = self._extract_bounding_box()
            if bbox.shape == self.target.shape:
                matches = np.array_equal(bbox.astype(int), self.target.astype(int))
                if matches:
                    return {
                        'success': True,
                        'method': 'bounding_box',
                        'result': bbox
                    }
            return {'success': False, 'reason': 'Shape mismatch'}
        
        # v4: Use HIERARCHICAL signature (local stalk geometry) for position-invariance
        if use_hierarchical:
            signature = self.compute_hierarchical_signature()
        else:
            signature = self.compute_spectral_signature(self.signature_dims)

        # Fast loop: warm start from memory
        warm_result = None
        if atlas is not None:
            warm_result = self._try_warm_start(
                atlas=atlas,
                signature=signature,
                top_k=warm_top_k,
                verbose=verbose,
            )
            if warm_result.get('success', False):
                chart_id = atlas.add_chart(
                    signature=signature,
                    operators=self._clone_operator_sequence(warm_result.get('operators', [])),
                    metadata={
                        'source': 'atlas_warm_start',
                        'final_energy': float(warm_result.get('final_energy', float('inf'))),
                        'grid_shape': tuple(int(v) for v in self.grid.shape),
                    },
                    dedup_threshold=0.995,
                )
                warm_result['atlas_chart_id'] = chart_id
                warm_result['atlas_size'] = atlas.size()
                return warm_result

        # Slow loop: thermodynamic discovery
        result = self.thermodynamic_discovery(verbose=verbose)

        # Consolidation: successful discoveries become Atlas memory
        if atlas is not None:
            result['warm_start_attempted'] = warm_result is not None
            result['warm_start_candidates'] = (
                warm_result.get('warm_candidates', 0) if warm_result else 0
            )

            if result.get('success', False) and result.get('operators'):
                chart_id = atlas.add_chart(
                    signature=signature,
                    operators=self._clone_operator_sequence(result['operators']),
                    metadata={
                        'source': 'thermodynamic_discovery',
                        'final_energy': float(result.get('final_energy', float('inf'))),
                        'grid_shape': tuple(int(v) for v in self.grid.shape),
                    },
                    dedup_threshold=0.995,
                )
                result['atlas_learned'] = True
                result['atlas_chart_id'] = chart_id
                result['atlas_size'] = atlas.size()
            else:
                result['atlas_learned'] = False
                result['atlas_size'] = atlas.size()

        return result
    
    def _extract_bounding_box(self) -> np.ndarray:
        """Extract bounding box of non-background pixels."""
        mask = self.grid > 0
        if not mask.any():
            return self.grid
        
        rows, cols = np.where(mask)
        r_min, r_max = rows.min(), rows.max()
        c_min, c_max = cols.min(), cols.max()
        
        return self.grid[r_min:r_max+1, c_min:c_max+1].copy()


# =============================================================================
# SHEAF ATLAS: Learned Operator Memory
# =============================================================================

class EmergentSheafAtlas:
    """
    The SheafAtlas stores DISCOVERED operators, not hardcoded rules.
    
    When an operator sequence successfully solves a task:
    1. Compute the spectral signature of the input
    2. Save the operator sequence indexed by that signature
    3. On future tasks, retrieve operators with similar signatures
    """
    
    def __init__(self, signature_dims: int = 16):
        self.charts: List[Dict[str, Any]] = []
        self.usage_counts: Dict[int, int] = {}
        self.signature_dims = signature_dims
        
        # Universal Morphism Layer: Index operators by TYPE (verb), not just signature (noun)
        # This enables retrieval of "translate_until_collision" regardless of stalk geometry
        self._morphism_index: Dict[str, List[Dict[str, Any]]] = {}

    def _prepare_signature(self, signature: np.ndarray) -> np.ndarray:
        sig = np.asarray(signature, dtype=np.float32).flatten()
        if sig.shape[0] >= self.signature_dims:
            return sig[:self.signature_dims]
        padded = np.zeros((self.signature_dims,), dtype=np.float32)
        padded[:sig.shape[0]] = sig
        return padded

    @staticmethod
    def _cosine_similarity(a: np.ndarray, b: np.ndarray) -> float:
        denom = (np.linalg.norm(a) * np.linalg.norm(b)) + 1e-10
        return float(np.dot(a, b) / denom)
    
    def add_chart(self,
                  signature: np.ndarray,
                  operators: List[Dict[str, Any]],
                  metadata: Optional[Dict[str, Any]] = None,
                  dedup_threshold: float = 0.995) -> int:
        """Add a discovered operator sequence to the Atlas (with near-duplicate dedup)."""
        prepared_signature = self._prepare_signature(signature)
        nearest = self.find_top_k_charts(prepared_signature, k=1, min_similarity=dedup_threshold)
        if nearest:
            chart_id = nearest[0]['id']
            existing_meta = self.charts[chart_id].setdefault('metadata', {})
            existing_meta['reinforced'] = int(existing_meta.get('reinforced', 0)) + 1
            if metadata:
                existing_meta.update(metadata)
            return chart_id

        chart_id = len(self.charts)
        self.charts.append({
            'id': chart_id,
            'signature': prepared_signature,
            'operators': copy.deepcopy(operators),
            'metadata': metadata or {}
        })
        self.usage_counts[chart_id] = 0
        
        # Index operators by type (verb) for Universal Morphism retrieval
        self._index_operators_by_type(operators)
        
        return chart_id
    
    def _index_operators_by_type(self, operators: List[Dict[str, Any]]) -> None:
        """Index operators by their type (verb) for universal morphism retrieval."""
        for op in operators:
            op_type = op.get('type', 'unknown')
            if op_type not in self._morphism_index:
                self._morphism_index[op_type] = []
            
            # Store a parameterized template (strip task-specific details)
            template = self._create_operator_template(op)
            
            # Avoid exact duplicates
            if not any(self._templates_equal(template, existing) 
                      for existing in self._morphism_index[op_type]):
                self._morphism_index[op_type].append(template)
    
    def _create_operator_template(self, op: Dict[str, Any]) -> Dict[str, Any]:
        """Create a parameterized template from an operator, preserving the verb."""
        template = {'type': op.get('type', 'unknown')}
        
        # Copy relevant parameters based on type
        op_type = op.get('type', '')
        
        if op_type == 'translate_until_collision':
            template['direction'] = op.get('direction')
            template['target_relation'] = op.get('target_relation', 'adjacent')
        elif op_type == 'relative_color':
            template['relation'] = op.get('relation', 'adjacent')
        elif op_type == 'fill_interior':
            pass  # No parameters needed - verb is self-describing
        elif op_type == 'complete_symmetry':
            template['axis'] = op.get('axis', 'horizontal')
        elif op_type == 'extend_to_edge':
            template['direction'] = op.get('direction')
        elif op_type == 'translation':
            # Keep direction but parameterize magnitude
            dr, dc = op.get('dr', 0), op.get('dc', 0)
            template['dr_sign'] = 1 if dr > 0 else (-1 if dr < 0 else 0)
            template['dc_sign'] = 1 if dc > 0 else (-1 if dc < 0 else 0)
        elif op_type == 'reflection':
            template['axis'] = op.get('axis', 'horizontal')
        elif op_type == 'color_map':
            # Keep as template - color mappings are universal
            template['from_color'] = op.get('from_color')
            template['to_color'] = op.get('to_color')
        elif op_type == 'crystallized_laplacian':
            # GEOMETRIC LOGIC CIRCUIT: Store the crystallized Laplacian matrix
            # This IS the Universal Morphism - pure physics, no Python functions
            template['edge_weights'] = op.get('edge_weights', [])
            template['structural_complexity'] = op.get('structural_complexity', 1.0)
            template['grokked'] = op.get('grokked', False)
        elif op_type == 'matrix_operator':
            # Pure math operator: P (permutation), C (color), v (translation)
            template['permutation_matrix'] = op.get('permutation_matrix')
            template['color_transition'] = op.get('color_transition')
            template['translation_vector'] = op.get('translation_vector')
        else:
            # Copy all parameters for unknown types
            template.update({k: v for k, v in op.items() if k != 'type'})
        
        return template
    
    def _templates_equal(self, t1: Dict[str, Any], t2: Dict[str, Any]) -> bool:
        """Check if two operator templates are equal."""
        if t1.get('type') != t2.get('type'):
            return False
        # Compare all keys
        keys = set(t1.keys()) | set(t2.keys())
        for k in keys:
            if t1.get(k) != t2.get(k):
                return False
        return True
    
    def _ensure_morphism_index(self) -> None:
        """Ensure _morphism_index exists (backwards compatibility for pickled atlases)."""
        if not hasattr(self, '_morphism_index') or self._morphism_index is None:
            self._morphism_index = {}
            # Rebuild index from existing charts
            for chart in self.charts:
                operators = chart.get('operators', [])
                self._index_operators_by_type(operators)
    
    def get_universal_morphisms(self) -> List[Dict[str, Any]]:
        """
        Return all unique relational operators (verbs) learned across all tasks.
        
        This is the Universal Morphism Layer - operators stripped of their
        specific stalk signatures, ready to be tested on any new stalk.
        
        Returns:
            List of operator templates, one per unique verb type
        """
        self._ensure_morphism_index()
        all_morphisms = []
        for op_type, templates in self._morphism_index.items():
            all_morphisms.extend(templates)
        return all_morphisms
    
    def get_morphisms_by_type(self, op_type: str) -> List[Dict[str, Any]]:
        """Get all templates for a specific operator type."""
        self._ensure_morphism_index()
        return copy.deepcopy(self._morphism_index.get(op_type, []))
    
    def get_morphism_types(self) -> List[str]:
        """Get all unique operator types in the Atlas."""
        self._ensure_morphism_index()
        return list(self._morphism_index.keys())

    def find_top_k_charts(self,
                          signature: np.ndarray,
                          k: int = 3,
                          min_similarity: float = 0.0) -> List[Dict[str, Any]]:
        """Return top-k charts by cosine similarity to spectral signature."""
        if not self.charts:
            return []

        query = self._prepare_signature(signature)
        scored: List[Dict[str, Any]] = []

        for chart in self.charts:
            sim = self._cosine_similarity(chart['signature'], query)
            if sim >= min_similarity:
                scored.append({
                    'id': chart['id'],
                    'similarity': sim,
                    'metadata': chart.get('metadata', {}),
                })

        scored.sort(key=lambda x: x['similarity'], reverse=True)
        return scored[:max(0, int(k))]
    
    def find_matching_chart(self, 
                            signature: np.ndarray, 
                            threshold: float = 0.9) -> Optional[int]:
        """Find a chart with similar spectral signature."""
        top = self.find_top_k_charts(signature, k=1, min_similarity=threshold)
        if not top:
            return None
        return top[0]['id']
    
    def get_operators(self, chart_id: int) -> List[Dict[str, Any]]:
        """Retrieve operators from a chart."""
        if 0 <= chart_id < len(self.charts):
            self.usage_counts[chart_id] += 1
            return copy.deepcopy(self.charts[chart_id]['operators'])
        return []

    def size(self) -> int:
        return len(self.charts)
    
    def clear(self) -> None:
        """
        Clear all charts and reset the Atlas for a new task.
        
        NOTE: In the new continuous learning paradigm, we should RARELY
        call clear(). The Atlas is a lifelong generative model.
        Only clear for completely fresh starts.
        """
        self.charts = []
        self.usage_counts = {}
        self._morphism_index = {}
        if hasattr(self, '_shape_mappings'):
            self._shape_mappings = []
    
    # =========================================================================
    # EQUATION OF STATE: Shape Prediction (Extensive Variables)
    # =========================================================================
    # 
    # In thermodynamics, extensive variables (volume, shape) must be predicted
    # BEFORE intensive variables (color transformations) can be applied.
    # This separates the topological base space from the fiber transformations.
    
    def learn_shape_mapping(self, input_shape: Tuple[int, int], 
                            output_shape: Tuple[int, int],
                            n_stalks: int = 0) -> None:
        """
        Learn the input→output shape relationship (Equation of State).
        
        Args:
            input_shape: (H_in, W_in) of input grid
            output_shape: (H_out, W_out) of output grid  
            n_stalks: Number of objects in the input (for scaling rules)
        """
        if not hasattr(self, '_shape_mappings'):
            self._shape_mappings = []
        
        self._shape_mappings.append({
            'input_shape': input_shape,
            'output_shape': output_shape,
            'n_stalks': n_stalks,
            'h_ratio': output_shape[0] / max(input_shape[0], 1),
            'w_ratio': output_shape[1] / max(input_shape[1], 1),
        })
    
    def predict_output_shape(self, input_shape: Tuple[int, int],
                             n_stalks: int = 0) -> Tuple[int, int]:
        """
        Predict output shape using learned Equation of State.
        
        Strategy (in order of priority):
        1. If exact input shape seen before, use that output shape
        2. Check for FIXED output size pattern (all outputs same size)
        3. Check for SCALING pattern (output = input * constant factor)
        4. Apply most common ratio
        5. Fall back to identity
        
        Returns:
            Predicted (H_out, W_out)
        """
        if not hasattr(self, '_shape_mappings') or not self._shape_mappings:
            return input_shape  # Identity fallback
        
        from collections import Counter
        
        # Strategy 1: Exact match
        for mapping in self._shape_mappings:
            if mapping['input_shape'] == input_shape:
                return mapping['output_shape']
        
        # Strategy 2: Check for FIXED output size pattern
        # If all outputs have the same shape, use that shape
        output_shapes = [m['output_shape'] for m in self._shape_mappings]
        output_shape_counts = Counter(output_shapes)
        if len(output_shape_counts) == 1:
            # All outputs have same shape - use it!
            return output_shapes[0]
        
        # Check if most common output shape appears in >50% of examples
        most_common_output, count = output_shape_counts.most_common(1)[0]
        if count > len(self._shape_mappings) * 0.5:
            return most_common_output
        
        # Strategy 3: Check for INTEGER SCALING pattern
        # (e.g., output is always 3x input)
        h_ratios = [round(m['h_ratio'], 1) for m in self._shape_mappings]
        w_ratios = [round(m['w_ratio'], 1) for m in self._shape_mappings]
        
        h_ratio_counts = Counter(h_ratios)
        w_ratio_counts = Counter(w_ratios)
        
        # If there's a dominant integer ratio, use it
        most_common_h = h_ratio_counts.most_common(1)[0][0]
        most_common_w = w_ratio_counts.most_common(1)[0][0]
        
        # Check if it's a clean integer scaling (1, 2, 3, etc.)
        if most_common_h == int(most_common_h) and most_common_w == int(most_common_w):
            predicted_h = max(1, int(input_shape[0] * most_common_h))
            predicted_w = max(1, int(input_shape[1] * most_common_w))
            return (predicted_h, predicted_w)
        
        # Strategy 4: Apply most common ratio (general case)
        ratio_counts = Counter()
        for m in self._shape_mappings:
            key = (round(m['h_ratio'], 2), round(m['w_ratio'], 2))
            ratio_counts[key] += 1
        
        if ratio_counts:
            most_common_ratio = ratio_counts.most_common(1)[0][0]
            h_ratio, w_ratio = most_common_ratio
            
            predicted_h = max(1, int(round(input_shape[0] * h_ratio)))
            predicted_w = max(1, int(round(input_shape[1] * w_ratio)))
            return (predicted_h, predicted_w)
        
        return input_shape  # Identity fallback
    
    def get_shape_confidence(self, input_shape: Tuple[int, int]) -> float:
        """
        Return confidence in shape prediction (0.0 to 1.0).
        Higher if we've seen this exact shape or consistent ratios.
        """
        if not hasattr(self, '_shape_mappings') or not self._shape_mappings:
            return 0.0
        
        # Exact match = high confidence
        for mapping in self._shape_mappings:
            if mapping['input_shape'] == input_shape:
                return 1.0
        
        # Check ratio consistency
        from collections import Counter
        ratio_counts = Counter()
        for m in self._shape_mappings:
            key = (round(m['h_ratio'], 2), round(m['w_ratio'], 2))
            ratio_counts[key] += 1
        
        if ratio_counts:
            most_common_count = ratio_counts.most_common(1)[0][1]
            total = sum(ratio_counts.values())
            return most_common_count / total
        
        return 0.0
