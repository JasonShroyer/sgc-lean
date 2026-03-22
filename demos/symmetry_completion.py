"""
Symmetry Completion: Theory-Derived Implementation

From SGC theory, symmetry completion is SECTION EXTENSION:
- Input is a partial section with G-defects
- Output is the minimal G-symmetric extension
- The G-defect = ker(I - g·I) = "protrusions"
- The G-kernel = where input is already G-invariant = "body"

This is NOT empirical pattern matching. We derive the algorithm
directly from the definition of G-equivariant section extension.
"""

import numpy as np
from typing import Tuple, Optional, Dict, Any, List, Callable
from dataclasses import dataclass
from abc import ABC, abstractmethod


class SymmetryGroup(ABC):
    """Abstract base class for symmetry groups acting on grids."""
    
    @abstractmethod
    def action(self, grid: np.ndarray) -> np.ndarray:
        """Apply the group generator to the grid."""
        pass
    
    @abstractmethod
    def inverse_action(self, grid: np.ndarray) -> np.ndarray:
        """Apply the inverse of the group generator."""
        pass
    
    @abstractmethod
    def orbit_size(self) -> int:
        """Size of the orbit under the group action."""
        pass
    
    def is_symmetric(self, grid: np.ndarray, tolerance: float = 0.95) -> bool:
        """Check if grid is G-symmetric."""
        transformed = self.action(grid)
        match = (grid == transformed).mean()
        return match >= tolerance


class VerticalReflection(SymmetryGroup):
    """Z_2 symmetry: reflection across vertical axis."""
    
    def __init__(self, axis: Optional[float] = None):
        self.axis = axis  # None means center
    
    def action(self, grid: np.ndarray) -> np.ndarray:
        return np.fliplr(grid)
    
    def inverse_action(self, grid: np.ndarray) -> np.ndarray:
        return np.fliplr(grid)  # Self-inverse
    
    def orbit_size(self) -> int:
        return 2


class HorizontalReflection(SymmetryGroup):
    """Z_2 symmetry: reflection across horizontal axis."""
    
    def action(self, grid: np.ndarray) -> np.ndarray:
        return np.flipud(grid)
    
    def inverse_action(self, grid: np.ndarray) -> np.ndarray:
        return np.flipud(grid)
    
    def orbit_size(self) -> int:
        return 2


class Rotation90(SymmetryGroup):
    """C_4 symmetry: 90-degree rotation."""
    
    def action(self, grid: np.ndarray) -> np.ndarray:
        return np.rot90(grid, k=1)
    
    def inverse_action(self, grid: np.ndarray) -> np.ndarray:
        return np.rot90(grid, k=-1)
    
    def orbit_size(self) -> int:
        return 4


class Rotation180(SymmetryGroup):
    """C_2 symmetry: 180-degree rotation."""
    
    def action(self, grid: np.ndarray) -> np.ndarray:
        return np.rot90(grid, k=2)
    
    def inverse_action(self, grid: np.ndarray) -> np.ndarray:
        return np.rot90(grid, k=2)  # Self-inverse
    
    def orbit_size(self) -> int:
        return 2


class Translation(SymmetryGroup):
    """Z_p × Z_q symmetry: periodic translation."""
    
    def __init__(self, period_x: int, period_y: int):
        self.period_x = period_x
        self.period_y = period_y
    
    def action(self, grid: np.ndarray) -> np.ndarray:
        return np.roll(np.roll(grid, self.period_y, axis=0), self.period_x, axis=1)
    
    def inverse_action(self, grid: np.ndarray) -> np.ndarray:
        return np.roll(np.roll(grid, -self.period_y, axis=0), -self.period_x, axis=1)
    
    def orbit_size(self) -> int:
        # For a grid of size (h, w), the orbit size is (h/period_y) * (w/period_x)
        return -1  # Variable


@dataclass
class GDecomposition:
    """
    The G-kernel/G-defect decomposition of a grid.
    
    From theory:
    - kernel: pixels where input is G-invariant (or both are zero)
    - defect: pixels that break G-symmetry (have no symmetric partner)
    """
    kernel_mask: np.ndarray  # Boolean mask of G-invariant pixels
    defect_mask: np.ndarray  # Boolean mask of G-defect pixels
    symmetry_group: SymmetryGroup


def compute_g_decomposition(grid: np.ndarray, G: SymmetryGroup) -> GDecomposition:
    """
    Compute the G-kernel and G-defect of a grid.
    
    From theory:
    - G-kernel K = {x : grid[x] = grid[g·x] for all g ∈ G, or both zero}
    - G-defect D = {x : grid[x] ≠ 0 and grid[g·x] = 0}
    """
    transformed = G.action(grid)
    
    # Kernel: where grid equals its transform (including both zero)
    kernel_mask = (grid == transformed) | ((grid == 0) & (transformed == 0))
    
    # Defect: non-zero pixels whose transform location is zero
    defect_mask = (grid != 0) & (transformed == 0)
    
    return GDecomposition(
        kernel_mask=kernel_mask,
        defect_mask=defect_mask,
        symmetry_group=G
    )


def compute_g_extension(grid: np.ndarray, G: SymmetryGroup, 
                        color_map: Optional[Dict[int, int]] = None) -> np.ndarray:
    """
    Compute the minimal G-symmetric extension of the grid.
    
    From theory (for Abelian G):
    - Extension E = grid ∪ G·(defect)
    - For each defect pixel, add its image under all g ∈ G
    - Color map handles cases like 1→2 in reflection tasks
    """
    decomp = compute_g_decomposition(grid, G)
    result = grid.copy()
    
    # Apply group action to defect pixels
    transformed = G.action(grid)
    
    for i in range(grid.shape[0]):
        for j in range(grid.shape[1]):
            if decomp.defect_mask[i, j]:
                # This pixel needs a symmetric partner
                # Find where it maps to under g^{-1}
                pass
    
    # For Z_2 groups, we can use the transform directly
    # The defect at position (i,j) should create a pixel at g·(i,j)
    
    # Create the extension: where defect exists, fill in the transform location
    defect_values = grid.copy()
    if color_map:
        for src, tgt in color_map.items():
            defect_values = np.where(defect_values == src, tgt, defect_values)
    
    # The transform of defect_values gives us what to add
    extension = G.action(defect_values)
    
    # Add extension where result is zero and extension is non-zero
    result = np.where((result == 0) & (extension != 0), extension, result)
    
    return result


def detect_target_symmetry(output: np.ndarray, 
                           candidates: List[SymmetryGroup] = None) -> Optional[Tuple[SymmetryGroup, Dict[int, int]]]:
    """
    Detect which symmetry group G the OUTPUT has.
    
    From theory: G acts on BOTH position AND color. So we check for
    symmetry up to a color permutation.
    
    Returns (G, color_perm) where color_perm[c] = c' means color c at position x
    maps to color c' at position g·x.
    """
    if candidates is None:
        candidates = [
            VerticalReflection(),
            HorizontalReflection(),
            Rotation180(),
            Rotation90()
        ]
    
    best_G = None
    best_match = 0
    best_color_perm = {}
    
    for G in candidates:
        transformed = G.action(output)
        
        # Find color correspondence: for each color c in output,
        # what color c' appears at the transformed position?
        colors = set(output[output != 0])
        color_perm = {}
        
        for c in colors:
            c_mask = (output == c)
            # What colors appear at transformed positions of c?
            transformed_colors = transformed[c_mask]
            if len(transformed_colors) > 0:
                # Most common color at transformed positions
                unique, counts = np.unique(transformed_colors, return_counts=True)
                color_perm[c] = unique[counts.argmax()]
        
        # Now check symmetry with color permutation
        # output[x] should map to color_perm[output[x]] at g·x
        match_count = 0
        total_count = 0
        
        for i in range(output.shape[0]):
            for j in range(output.shape[1]):
                if output[i, j] != 0:
                    expected = color_perm.get(output[i, j], output[i, j])
                    actual = transformed[i, j]
                    if actual == expected:
                        match_count += 1
                    total_count += 1
        
        if total_count > 0:
            match = match_count / total_count
            if match > best_match:
                best_match = match
                best_G = G
                best_color_perm = color_perm
    
    if best_match > 0.8:
        return (best_G, best_color_perm)
    return None


def verify_g_completion(input_grid: np.ndarray, output_grid: np.ndarray,
                        G: SymmetryGroup) -> Dict[str, Any]:
    """
    Verify that output = G-completion of input.
    
    From theory:
    1. Output should be G-symmetric
    2. Output should contain input (on the kernel)
    3. Output \ input should equal G·(defect of input)
    """
    # Check output is G-symmetric
    output_symmetric = G.is_symmetric(output_grid, tolerance=0.9)
    
    # Compute decomposition
    decomp = compute_g_decomposition(input_grid, G)
    
    # Check that output contains input on kernel
    kernel_preserved = (input_grid[decomp.kernel_mask] == 
                       output_grid[decomp.kernel_mask]).all()
    
    # Compute what was added
    added_mask = (output_grid != 0) & (input_grid == 0)
    
    # Compute expected addition (G-orbit of defect)
    expected_add = G.action(input_grid)
    expected_add_mask = (expected_add != 0) & (input_grid == 0)
    
    # Check overlap
    if expected_add_mask.any():
        add_match = (added_mask & expected_add_mask).sum() / added_mask.sum() if added_mask.any() else 0
    else:
        add_match = 0
    
    return {
        'output_symmetric': output_symmetric,
        'kernel_preserved': kernel_preserved,
        'addition_match': add_match,
        'is_g_completion': output_symmetric and kernel_preserved and add_match > 0.5,
        'decomposition': decomp
    }


def infer_color_map(input_grid: np.ndarray, output_grid: np.ndarray,
                    G: SymmetryGroup) -> Dict[int, int]:
    """
    Infer the color mapping used in the G-completion.
    
    E.g., in 1b60fb0c, color 1 in input becomes color 2 in the reflected addition.
    """
    # Find what colors were added
    added_mask = (output_grid != 0) & (input_grid == 0)
    if not added_mask.any():
        return {}
    
    added_colors = set(output_grid[added_mask])
    source_colors = set(input_grid[input_grid != 0])
    
    # The added colors should map from source colors via the transformation
    # For reflection: source pixels at (i,j) with color c become (i, 2a-j) with color c'
    color_map = {}
    
    for src_color in source_colors:
        src_mask = (input_grid == src_color)
        transformed_src = G.action(src_mask.astype(int))
        
        # Where transformed source overlaps with added region
        overlap = transformed_src & added_mask
        if overlap.any():
            # What color was added there?
            tgt_color = output_grid[overlap][0]
            color_map[int(src_color)] = int(tgt_color)
    
    return color_map


def analyze_task_from_theory(input_grid: np.ndarray, output_grid: np.ndarray,
                             verbose: bool = True) -> Dict[str, Any]:
    """
    Theory-driven task analysis.
    
    1. Detect G_target from OUTPUT (with color permutation)
    2. Verify input → output is G-completion
    3. Extract the G-decomposition and color map
    
    From SGC theory: The gauge group G acts on the TOTAL space (position × color).
    Symmetry means: output[g·x] = π(g) · output[x] where π is a color representation.
    """
    # Step 1: What symmetry does the OUTPUT have?
    result = detect_target_symmetry(output_grid)
    
    if result is None:
        if verbose:
            print("No target symmetry detected in output")
        return {'type': 'unknown', 'symmetry': None}
    
    G_target, color_perm = result
    
    if verbose:
        print(f"Detected target symmetry: {G_target.__class__.__name__}")
        print(f"Color permutation under G: {color_perm}")
    
    # Step 2: Verify this is a G-completion task
    verification = verify_g_completion(input_grid, output_grid, G_target)
    
    if verbose:
        print(f"Output is G-symmetric: {verification['output_symmetric']}")
        print(f"Kernel preserved: {verification['kernel_preserved']}")
        print(f"Addition match: {verification['addition_match']:.2%}")
        print(f"Is G-completion: {verification['is_g_completion']}")
    
    if not verification['is_g_completion']:
        return {'type': 'not_g_completion', 'symmetry': G_target, 'verification': verification}
    
    # Step 3: Infer color map
    color_map = infer_color_map(input_grid, output_grid, G_target)
    
    if verbose and color_map:
        print(f"Color map: {color_map}")
    
    # Step 4: Verify by reconstruction
    reconstructed = compute_g_extension(input_grid, G_target, color_map)
    reconstruction_match = (reconstructed == output_grid).mean()
    
    if verbose:
        print(f"Reconstruction accuracy: {reconstruction_match:.2%}")
    
    return {
        'type': 'g_completion',
        'symmetry': G_target,
        'color_map': color_map,
        'decomposition': verification['decomposition'],
        'reconstruction_match': reconstruction_match
    }


if __name__ == "__main__":
    import json
    from pathlib import Path
    
    arc_dir = Path(__file__).parent.parent / "data" / "arc" / "training"
    
    # Test on task 1b60fb0c
    task_file = arc_dir / "1b60fb0c.json"
    with open(task_file) as f:
        task = json.load(f)
    
    print("=" * 60)
    print("THEORY-DRIVEN ANALYSIS: Task 1b60fb0c")
    print("=" * 60)
    
    for i, ex in enumerate(task['train']):
        print(f"\n--- Example {i+1} ---")
        inp = np.array(ex['input'])
        out = np.array(ex['output'])
        
        result = analyze_task_from_theory(inp, out, verbose=True)
        print(f"Result type: {result['type']}")
