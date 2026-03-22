"""
Spectral Perception: Theory-Derived Universal Induction

From SGC theory:
- The rule IS the ground state of the diffusion operator
- Hermite-Gaussian wavelets diagonalize diffusion
- The Fiedler vector encodes the primary structural axis
- Symmetry = eigenvector structure of the graph Laplacian

This is NOT empirical pattern matching. We derive perception
directly from the spectral geometry of the input.
"""

import numpy as np
from scipy import sparse
from scipy.sparse.linalg import eigsh
from typing import Tuple, Dict, Any, List, Optional
import json
from pathlib import Path


def grid_to_graph(grid: np.ndarray, color: int = None) -> Tuple[np.ndarray, List[Tuple[int, int]]]:
    """
    Convert a grid to a graph representation.
    
    Returns:
        adjacency: NxN adjacency matrix
        positions: List of (row, col) positions for each node
    """
    if color is not None:
        mask = (grid == color)
    else:
        mask = (grid != 0)
    
    positions = list(zip(*np.where(mask)))
    n = len(positions)
    
    if n == 0:
        return np.array([[]]), []
    
    pos_to_idx = {pos: i for i, pos in enumerate(positions)}
    
    # Build adjacency matrix (8-connected)
    adjacency = np.zeros((n, n))
    for i, (r, c) in enumerate(positions):
        for dr in [-1, 0, 1]:
            for dc in [-1, 0, 1]:
                if dr == 0 and dc == 0:
                    continue
                neighbor = (r + dr, c + dc)
                if neighbor in pos_to_idx:
                    j = pos_to_idx[neighbor]
                    adjacency[i, j] = 1
    
    return adjacency, positions


def compute_laplacian(adjacency: np.ndarray) -> np.ndarray:
    """
    Compute the normalized graph Laplacian.
    
    L = I - D^{-1/2} A D^{-1/2}
    
    This is the natural diffusion operator on the graph.
    """
    n = adjacency.shape[0]
    if n == 0:
        return np.array([[]])
    
    degree = adjacency.sum(axis=1)
    # Avoid division by zero
    degree[degree == 0] = 1
    
    D_inv_sqrt = np.diag(1.0 / np.sqrt(degree))
    L = np.eye(n) - D_inv_sqrt @ adjacency @ D_inv_sqrt
    
    return L


def compute_fiedler_vector(laplacian: np.ndarray) -> Tuple[np.ndarray, float]:
    """
    Compute the Fiedler vector (second smallest eigenvector).
    
    The Fiedler vector encodes the primary structural axis of the graph.
    It partitions the graph into two parts that are "maximally different"
    in terms of connectivity.
    
    For a symmetric shape, the Fiedler vector's zero-crossing IS the
    symmetry axis.
    """
    n = laplacian.shape[0]
    if n < 3:
        return np.zeros(n), 0.0
    
    # Compute smallest eigenvectors
    # λ₀ = 0 (constant), λ₁ = Fiedler value
    try:
        eigenvalues, eigenvectors = eigsh(laplacian, k=min(3, n-1), which='SM')
        
        # Sort by eigenvalue
        idx = np.argsort(eigenvalues)
        eigenvalues = eigenvalues[idx]
        eigenvectors = eigenvectors[:, idx]
        
        # Fiedler vector is the second (index 1)
        fiedler_value = eigenvalues[1] if len(eigenvalues) > 1 else 0
        fiedler_vector = eigenvectors[:, 1] if eigenvectors.shape[1] > 1 else np.zeros(n)
        
        return fiedler_vector, fiedler_value
    except Exception as e:
        return np.zeros(n), 0.0


def find_symmetry_axis_spectral(grid: np.ndarray, color: int = 1) -> Dict[str, Any]:
    """
    Find the symmetry axis using spectral analysis.
    
    From SGC theory:
    - Build graph from shape
    - Compute Laplacian (diffusion operator)
    - Fiedler vector encodes primary axis
    - Zero-crossing of Fiedler = symmetry axis
    - Extreme values of Fiedler = protrusions
    """
    adjacency, positions = grid_to_graph(grid, color)
    n = len(positions)
    
    if n < 3:
        return {'success': False, 'reason': 'Too few nodes'}
    
    laplacian = compute_laplacian(adjacency)
    fiedler, fiedler_value = compute_fiedler_vector(laplacian)
    
    # Map Fiedler values back to grid positions
    fiedler_map = {}
    for i, pos in enumerate(positions):
        fiedler_map[pos] = fiedler[i]
    
    # Find the axis: where Fiedler vector crosses zero
    # This partitions the shape into two halves
    positive_nodes = [pos for pos, val in fiedler_map.items() if val > 0]
    negative_nodes = [pos for pos, val in fiedler_map.items() if val < 0]
    
    # The axis is between positive and negative regions
    # Compute centroids
    if positive_nodes and negative_nodes:
        pos_centroid = np.mean(positive_nodes, axis=0)
        neg_centroid = np.mean(negative_nodes, axis=0)
        
        # Axis direction is perpendicular to line connecting centroids
        axis_direction = neg_centroid - pos_centroid
        axis_center = (pos_centroid + neg_centroid) / 2
        
        # Determine if axis is more vertical or horizontal
        if abs(axis_direction[1]) > abs(axis_direction[0]):
            axis_type = 'vertical'
            axis_position = axis_center[1]
        else:
            axis_type = 'horizontal'
            axis_position = axis_center[0]
    else:
        axis_type = 'unknown'
        axis_position = None
    
    # Find protrusions: nodes with extreme Fiedler values
    fiedler_std = np.std(fiedler)
    fiedler_mean = np.mean(fiedler)
    
    protrusion_threshold = 1.5  # 1.5 standard deviations
    protrusions = {
        'positive': [pos for pos, val in fiedler_map.items() 
                     if val > fiedler_mean + protrusion_threshold * fiedler_std],
        'negative': [pos for pos, val in fiedler_map.items() 
                     if val < fiedler_mean - protrusion_threshold * fiedler_std]
    }
    
    return {
        'success': True,
        'fiedler_value': fiedler_value,
        'fiedler_map': fiedler_map,
        'axis_type': axis_type,
        'axis_position': axis_position,
        'positive_partition': positive_nodes,
        'negative_partition': negative_nodes,
        'protrusions': protrusions,
        'n_nodes': n
    }


def predict_completion_spectral(input_grid: np.ndarray, color: int = 1) -> np.ndarray:
    """
    Predict the symmetry completion using spectral analysis.
    
    From theory:
    1. Find the Fiedler-derived symmetry axis
    2. Identify protrusions (extreme Fiedler values)
    3. Mirror protrusions across the axis
    """
    result = find_symmetry_axis_spectral(input_grid, color)
    
    if not result['success']:
        return input_grid.copy()
    
    output = input_grid.copy()
    
    # The protrusions on the positive side should be mirrored to negative
    # and vice versa (depending on which side has more)
    pos_prot = result['protrusions']['positive']
    neg_prot = result['protrusions']['negative']
    
    axis_pos = result['axis_position']
    axis_type = result['axis_type']
    
    if axis_pos is None:
        return output
    
    # Determine which side has the "missing" content
    # The side with fewer protrusions needs completion
    if len(pos_prot) > len(neg_prot):
        # Mirror positive protrusions to negative side
        to_mirror = pos_prot
    else:
        # Mirror negative protrusions to positive side
        to_mirror = neg_prot
    
    # Add mirrored pixels
    new_color = 2  # Convention: added pixels use color 2
    
    for pos in to_mirror:
        r, c = pos
        if axis_type == 'vertical':
            mirror_c = int(2 * axis_pos - c)
            mirror_pos = (r, mirror_c)
        else:  # horizontal
            mirror_r = int(2 * axis_pos - r)
            mirror_pos = (mirror_r, c)
        
        if (0 <= mirror_pos[0] < output.shape[0] and 
            0 <= mirror_pos[1] < output.shape[1] and
            output[mirror_pos] == 0):
            output[mirror_pos] = new_color
    
    return output


def analyze_task_spectral(input_grid: np.ndarray, output_grid: np.ndarray,
                          verbose: bool = True) -> Dict[str, Any]:
    """
    Analyze a task using spectral perception.
    
    This is the theory-derived analysis:
    1. Compute spectral structure of input
    2. Compute spectral structure of output
    3. Identify the transformation in spectral terms
    """
    input_analysis = find_symmetry_axis_spectral(input_grid, color=1)
    
    if verbose:
        print(f"Input shape: {input_grid.shape}")
        print(f"Input nodes: {input_analysis.get('n_nodes', 0)}")
        print(f"Fiedler value: {input_analysis.get('fiedler_value', 0):.4f}")
        print(f"Axis type: {input_analysis.get('axis_type')}")
        print(f"Axis position: {input_analysis.get('axis_position')}")
        print(f"Positive protrusions: {len(input_analysis.get('protrusions', {}).get('positive', []))}")
        print(f"Negative protrusions: {len(input_analysis.get('protrusions', {}).get('negative', []))}")
    
    # Predict completion
    predicted = predict_completion_spectral(input_grid, color=1)
    
    # Compare to actual output
    actual_add = (output_grid == 2) & (input_grid == 0)
    predicted_add = (predicted == 2) & (input_grid == 0)
    
    overlap = (actual_add & predicted_add).sum()
    union = (actual_add | predicted_add).sum()
    iou = overlap / max(union, 1)
    
    if verbose:
        print(f"\nPrediction accuracy:")
        print(f"  Actual additions: {actual_add.sum()}")
        print(f"  Predicted additions: {predicted_add.sum()}")
        print(f"  IoU: {iou:.2%}")
    
    return {
        'input_analysis': input_analysis,
        'predicted': predicted,
        'iou': iou,
        'actual_additions': actual_add.sum(),
        'predicted_additions': predicted_add.sum()
    }


if __name__ == "__main__":
    arc_dir = Path(__file__).parent.parent / "data" / "arc" / "training"
    
    print("=" * 60)
    print("SPECTRAL PERCEPTION: Theory-Derived Analysis")
    print("=" * 60)
    print()
    print("From SGC theory:")
    print("- Fiedler vector encodes primary structural axis")
    print("- Zero-crossing = symmetry axis")
    print("- Extreme values = protrusions")
    print()
    
    # Test on task 1b60fb0c
    task_file = arc_dir / "1b60fb0c.json"
    with open(task_file) as f:
        task = json.load(f)
    
    print("=" * 60)
    print("Task 1b60fb0c: Spectral Analysis")
    print("=" * 60)
    
    total_iou = 0
    for i, ex in enumerate(task['train']):
        print(f"\n--- Example {i+1} ---")
        inp = np.array(ex['input'])
        out = np.array(ex['output'])
        
        result = analyze_task_spectral(inp, out, verbose=True)
        total_iou += result['iou']
    
    avg_iou = total_iou / len(task['train'])
    print(f"\n{'=' * 60}")
    print(f"Average IoU: {avg_iou:.2%}")
    print("=" * 60)
