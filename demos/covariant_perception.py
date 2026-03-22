"""
Covariant Perception: Theory-Derived Universal Induction

From SGC/UPAT Theory:
- The rule is NOT searched for; it is the topological defect that remains after diffusion
- Construct Covariant Graph Laplacian: L_A = -Δ_A + V(x)
- V(x) encodes the covariance structure of the isolated object
- Hermite-Gaussian basis adapted to object structure reveals defect modes
- The rule is the operation that annihilates the defect (minimizes Free Energy)

Key insight: You do not compare input/output to guess the rule.
The input's own spectral decomposition tells you where symmetry is broken.
"""

import numpy as np
from scipy import linalg
from scipy.special import hermite
from typing import Tuple, Dict, Any, List, Optional
import json
from pathlib import Path


class ObjectAdaptedBasis:
    """
    Hermite-Gaussian basis adapted to an object's covariance structure.
    
    The eigenvectors of the covariance matrix define the natural axes.
    The quadratic potential V(x) = x^T Σ^{-1} x defines the "well" shape.
    """
    
    def __init__(self, positions: np.ndarray):
        """
        Initialize basis from object positions.
        
        Args:
            positions: Nx2 array of (row, col) coordinates
        """
        self.positions = positions
        self.n_points = len(positions)
        
        # Compute centroid (center of the potential well)
        self.centroid = positions.mean(axis=0)
        
        # Compute covariance matrix
        centered = positions - self.centroid
        self.covariance = centered.T @ centered / self.n_points
        
        # Eigendecomposition gives principal axes
        eigenvalues, eigenvectors = linalg.eigh(self.covariance)
        
        # Sort by eigenvalue (largest first = major axis)
        idx = np.argsort(eigenvalues)[::-1]
        self.eigenvalues = eigenvalues[idx]
        self.axes = eigenvectors[:, idx]  # Columns are principal axes
        
        # The inverse covariance defines the quadratic potential
        # V(x) = (1/2) x^T Σ^{-1} x
        # Regularize to avoid singularity
        reg_eigenvalues = np.maximum(self.eigenvalues, 0.1)
        self.precision = self.axes @ np.diag(1.0 / reg_eigenvalues) @ self.axes.T
        
    def project_to_principal(self, points: np.ndarray) -> np.ndarray:
        """Project points to principal coordinate system."""
        centered = points - self.centroid
        return centered @ self.axes
    
    def hermite_gaussian_1d(self, x: np.ndarray, n: int, sigma: float) -> np.ndarray:
        """
        1D Hermite-Gaussian function H_n(x/σ) * exp(-x²/2σ²)
        
        These are eigenfunctions of the 1D quantum harmonic oscillator.
        """
        H_n = hermite(n)
        scaled_x = x / sigma
        normalization = 1.0 / np.sqrt(2**n * np.math.factorial(n) * np.sqrt(np.pi) * sigma)
        return normalization * H_n(scaled_x) * np.exp(-scaled_x**2 / 2)
    
    def evaluate_basis(self, points: np.ndarray, max_order: int = 4) -> np.ndarray:
        """
        Evaluate Hermite-Gaussian basis functions at given points.
        
        Returns coefficients for each point in the 2D tensor product basis:
        ψ_{nm}(x,y) = H_n(x'/σ_x) * H_m(y'/σ_y) * exp(-x'²/2σ_x² - y'²/2σ_y²)
        
        where (x', y') are principal coordinates and σ_x, σ_y are the
        standard deviations along principal axes.
        """
        # Project to principal coordinates
        principal = self.project_to_principal(points)
        
        # Standard deviations along principal axes
        sigma = np.sqrt(self.eigenvalues)
        sigma = np.maximum(sigma, 0.5)  # Regularize
        
        # Build 2D tensor product basis
        n_basis = (max_order + 1) ** 2
        basis = np.zeros((len(points), n_basis))
        
        idx = 0
        for n in range(max_order + 1):
            for m in range(max_order + 1):
                # ψ_{nm} = H_n(x'/σ_x) * H_m(y'/σ_y)
                psi_n = self.hermite_gaussian_1d(principal[:, 0], n, sigma[0])
                psi_m = self.hermite_gaussian_1d(principal[:, 1], m, sigma[1])
                basis[:, idx] = psi_n * psi_m
                idx += 1
        
        return basis
    
    def decompose(self, values: np.ndarray, max_order: int = 4) -> np.ndarray:
        """
        Decompose a function defined on the object into Hermite-Gaussian coefficients.
        
        Args:
            values: Value at each position (length n_points)
            max_order: Maximum Hermite order to use
            
        Returns:
            Coefficients in the Hermite-Gaussian basis
        """
        basis = self.evaluate_basis(self.positions, max_order)
        
        # Least squares fit: find coefficients c such that basis @ c ≈ values
        coefficients, residuals, rank, s = linalg.lstsq(basis, values)
        
        return coefficients
    
    def get_symmetry_axis(self) -> Tuple[np.ndarray, str]:
        """
        Return the Fiedler axis (structural zero-crossing).
        
        For reflection symmetry, this is the axis perpendicular to the
        direction of maximum asymmetry.
        """
        # The minor axis (smaller eigenvalue) is where the object is "narrow"
        # For reflection tasks, this is typically the symmetry axis
        minor_axis = self.axes[:, 1]
        major_axis = self.axes[:, 0]
        
        # Determine if the axis is more vertical or horizontal
        if abs(major_axis[0]) > abs(major_axis[1]):
            axis_type = 'vertical'  # Major axis points vertically
        else:
            axis_type = 'horizontal'
            
        return self.centroid, minor_axis, axis_type


class CovariantLaplacian:
    """
    Covariant Graph Laplacian with object-adapted quadratic potential.
    
    L_A = -Δ_A + V(x)
    
    where V(x) = (1/2) x^T Σ^{-1} x encodes the covariance structure.
    """
    
    def __init__(self, positions: np.ndarray, adjacency: np.ndarray):
        """
        Initialize the covariant Laplacian.
        
        Args:
            positions: Nx2 array of coordinates
            adjacency: NxN adjacency matrix
        """
        self.positions = positions
        self.adjacency = adjacency
        self.n = len(positions)
        
        # Standard graph Laplacian
        degree = adjacency.sum(axis=1)
        degree[degree == 0] = 1
        D_inv_sqrt = np.diag(1.0 / np.sqrt(degree))
        self.graph_laplacian = np.eye(self.n) - D_inv_sqrt @ adjacency @ D_inv_sqrt
        
        # Object-adapted basis
        self.basis = ObjectAdaptedBasis(positions)
        
        # Quadratic potential V(x) = (1/2) x^T Σ^{-1} x
        # Evaluated at each node
        centered = positions - self.basis.centroid
        self.potential = np.array([
            0.5 * c @ self.basis.precision @ c for c in centered
        ])
        
        # Covariant Laplacian: L_A = graph_laplacian + diag(V)
        self.L_A = self.graph_laplacian + np.diag(self.potential)
    
    def eigenfunctions(self, k: int = 10) -> Tuple[np.ndarray, np.ndarray]:
        """
        Compute eigenfunctions of the covariant Laplacian.
        
        These are the object-adapted "Hermite-Gaussian-like" modes.
        
        Returns:
            eigenvalues: k smallest eigenvalues
            eigenvectors: corresponding eigenvectors
        """
        eigenvalues, eigenvectors = linalg.eigh(self.L_A)
        
        # Return k smallest
        return eigenvalues[:k], eigenvectors[:, :k]


def build_graph(grid: np.ndarray, color: int = 1) -> Tuple[np.ndarray, np.ndarray]:
    """Build adjacency matrix and positions from grid."""
    mask = (grid == color)
    positions = np.array(list(zip(*np.where(mask))))
    n = len(positions)
    
    if n == 0:
        return np.array([]), np.array([[]])
    
    pos_to_idx = {tuple(p): i for i, p in enumerate(positions)}
    
    adjacency = np.zeros((n, n))
    for i, (r, c) in enumerate(positions):
        for dr in [-1, 0, 1]:
            for dc in [-1, 0, 1]:
                if dr == 0 and dc == 0:
                    continue
                neighbor = (r + dr, c + dc)
                if neighbor in pos_to_idx:
                    adjacency[i, pos_to_idx[neighbor]] = 1
    
    return positions, adjacency


def identify_defect_modes(laplacian: CovariantLaplacian, 
                          threshold: float = 0.5) -> Dict[str, Any]:
    """
    Identify defect modes: high-frequency components that break symmetry.
    
    From theory:
    - Ground state (H_0) = symmetric, low energy
    - Defect modes = high-frequency, asymmetric
    - The defect is where free energy is concentrated
    """
    eigenvalues, eigenvectors = laplacian.eigenfunctions(k=min(10, laplacian.n))
    
    # The Fiedler vector (second eigenvector) encodes primary structure
    fiedler_value = eigenvalues[1] if len(eigenvalues) > 1 else 0
    fiedler_vector = eigenvectors[:, 1] if eigenvectors.shape[1] > 1 else np.zeros(laplacian.n)
    
    # Defect: nodes with extreme Fiedler values (asymmetric positions)
    fiedler_std = np.std(fiedler_vector)
    fiedler_mean = np.mean(fiedler_vector)
    
    # Positive defect: nodes that break symmetry on one side
    positive_defect_mask = fiedler_vector > fiedler_mean + threshold * fiedler_std
    negative_defect_mask = fiedler_vector < fiedler_mean - threshold * fiedler_std
    
    # The defect is on the side with fewer nodes (the "protrusion")
    positive_count = positive_defect_mask.sum()
    negative_count = negative_defect_mask.sum()
    
    if positive_count < negative_count:
        defect_mask = positive_defect_mask
        defect_side = 'positive'
    else:
        defect_mask = negative_defect_mask
        defect_side = 'negative'
    
    return {
        'eigenvalues': eigenvalues,
        'fiedler_vector': fiedler_vector,
        'fiedler_value': fiedler_value,
        'defect_mask': defect_mask,
        'defect_side': defect_side,
        'defect_positions': laplacian.positions[defect_mask]
    }


def compute_symmetry_completion(grid: np.ndarray, color: int = 1) -> Dict[str, Any]:
    """
    Compute symmetry completion using covariant perception.
    
    Theory-derived algorithm:
    1. Build covariant Laplacian with object-adapted potential
    2. Identify defect modes (where symmetry is broken)
    3. Apply reflection to annihilate defect (extend section to global)
    """
    positions, adjacency = build_graph(grid, color)
    n = len(positions)
    
    if n < 3:
        return {'success': False, 'reason': 'Too few nodes'}
    
    # Build covariant Laplacian
    laplacian = CovariantLaplacian(positions, adjacency)
    
    # Get the object-adapted basis and symmetry axis
    centroid, minor_axis, axis_type = laplacian.basis.get_symmetry_axis()
    
    # Identify defect modes
    defect_info = identify_defect_modes(laplacian)
    
    # The reflection axis passes through centroid, perpendicular to minor axis
    # For 2D reflection: reflect across the line through centroid with direction minor_axis
    
    # Compute reflection of defect positions
    defect_positions = defect_info['defect_positions']
    
    if len(defect_positions) == 0:
        return {
            'success': True,
            'message': 'No defect detected - object is already symmetric',
            'additions': []
        }
    
    # Reflection formula: x' = x - 2 * ((x - c) · n) * n
    # where c is centroid and n is the normal to the reflection axis
    # The normal is the MAJOR axis (perpendicular to the symmetry line)
    normal = laplacian.basis.axes[:, 0]  # Major axis
    
    reflected_positions = []
    for pos in defect_positions:
        vec = pos - centroid
        proj = np.dot(vec, normal)
        reflected = pos - 2 * proj * normal
        reflected_positions.append(reflected)
    
    reflected_positions = np.array(reflected_positions)
    
    # Round to grid positions and filter valid
    additions = []
    for pos in reflected_positions:
        r, c = int(round(pos[0])), int(round(pos[1]))
        if 0 <= r < grid.shape[0] and 0 <= c < grid.shape[1]:
            if grid[r, c] == 0:
                additions.append((r, c))
    
    return {
        'success': True,
        'centroid': centroid,
        'axis_type': axis_type,
        'normal': normal,
        'defect_positions': defect_positions,
        'reflected_positions': reflected_positions,
        'additions': additions,
        'defect_info': defect_info,
        'basis': laplacian.basis
    }


def predict_output(input_grid: np.ndarray, result: Dict[str, Any], 
                   input_color: int = 1, output_color: int = 2) -> np.ndarray:
    """Generate predicted output grid from symmetry completion result."""
    output = input_grid.copy()
    
    if not result.get('success', False):
        return output
    
    for r, c in result.get('additions', []):
        output[r, c] = output_color
    
    return output


def analyze_task(input_grid: np.ndarray, output_grid: np.ndarray,
                 verbose: bool = True) -> Dict[str, Any]:
    """
    Analyze a task using covariant perception.
    
    This implements the theory-derived algorithm:
    1. The input's spectral decomposition reveals where symmetry is broken
    2. The rule is the operation that annihilates the defect
    3. No comparison with output needed to FIND the rule
    """
    result = compute_symmetry_completion(input_grid)
    
    if verbose:
        print(f"Grid shape: {input_grid.shape}")
        if result['success']:
            print(f"Centroid: ({result['centroid'][0]:.2f}, {result['centroid'][1]:.2f})")
            print(f"Axis type: {result['axis_type']}")
            print(f"Reflection normal: {result['normal']}")
            print(f"Defect positions: {len(result['defect_positions'])}")
            print(f"Predicted additions: {len(result['additions'])}")
        else:
            print(f"Failed: {result.get('reason', 'unknown')}")
    
    # Generate prediction
    predicted = predict_output(input_grid, result)
    
    # Compare to actual
    actual_add = (output_grid == 2) & (input_grid == 0)
    predicted_add = (predicted == 2) & (input_grid == 0)
    
    overlap = (actual_add & predicted_add).sum()
    union = (actual_add | predicted_add).sum()
    iou = overlap / max(union, 1)
    
    if verbose:
        print(f"Actual additions: {actual_add.sum()}")
        print(f"IoU: {iou:.2%}")
    
    return {
        'result': result,
        'predicted': predicted,
        'iou': iou,
        'actual_additions': actual_add.sum(),
        'predicted_additions': predicted_add.sum()
    }


if __name__ == "__main__":
    arc_dir = Path(__file__).parent.parent / "data" / "arc" / "training"
    
    print("=" * 70)
    print("COVARIANT PERCEPTION: Theory-Derived Universal Induction")
    print("=" * 70)
    print()
    print("From SGC/UPAT Theory:")
    print("- L_A = -Delta_A + V(x) with object-adapted quadratic potential")
    print("- Hermite-Gaussian basis reveals defect modes")
    print("- The rule annihilates the defect (minimizes Free Energy)")
    print()
    
    # Test on task 1b60fb0c
    task_file = arc_dir / "1b60fb0c.json"
    with open(task_file) as f:
        task = json.load(f)
    
    print("=" * 70)
    print("Task 1b60fb0c: Reflection Symmetry Completion")
    print("=" * 70)
    
    total_iou = 0
    for i, ex in enumerate(task['train']):
        print(f"\n--- Example {i+1} ---")
        inp = np.array(ex['input'])
        out = np.array(ex['output'])
        
        analysis = analyze_task(inp, out, verbose=True)
        total_iou += analysis['iou']
    
    avg_iou = total_iou / len(task['train'])
    print(f"\n{'=' * 70}")
    print(f"Average IoU: {avg_iou:.2%}")
    print("=" * 70)
