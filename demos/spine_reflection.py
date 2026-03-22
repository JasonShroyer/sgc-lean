"""
Spine-Based Reflection: Theory-Derived Symmetry Completion

From SGC/UPAT Theory:
- The G-kernel is the SPINE (vertically consistent structure)
- The G-defect is the PROTRUSION (horizontal extension)
- The rule mirrors the defect across the spine boundary
- The spine is where Fiedler values are LOW (central, well-connected)

Key insight: The spine is the "body" that would be symmetric.
The protrusion breaks symmetry. Mirroring restores ground state.
"""

import numpy as np
from typing import Tuple, Dict, Any, List, Optional
import json
from pathlib import Path


def find_symmetry_axis(grid: np.ndarray, color: int = 1) -> Tuple[Optional[float], Optional[int]]:
    """
    Find the symmetry axis by analyzing the shape's structure.
    
    From SGC theory: The axis is at the CENTER of the G-kernel (body).
    The body is the symmetric core. Protrusions extend asymmetrically.
    
    The axis = (body_left + body_right) / 2
    
    Returns: (axis_position, body_center_column)
    """
    mask = (grid == color)
    positions = np.array(list(zip(*np.where(mask))))
    
    if len(positions) == 0:
        return None, None
    
    # For each column, count how many rows have a pixel
    col_presence = mask.sum(axis=0)
    
    # Find the column range
    min_col = int(positions[:, 1].min())
    max_col = int(positions[:, 1].max())
    
    # Find rows that have content
    active_rows = np.where(mask.any(axis=1))[0]
    n_active_rows = len(active_rows)
    
    # The body consists of columns with HIGH vertical presence
    # These form the symmetric core; protrusions have lower presence
    threshold = 0.6 * n_active_rows  # At least 60% of active rows
    body_cols = [c for c in range(grid.shape[1]) if col_presence[c] >= threshold]
    
    if not body_cols:
        # Fallback: all columns with content
        body_cols = list(range(min_col, max_col + 1))
    
    # The body extent
    body_left = min(body_cols)
    body_right = max(body_cols)
    
    # The axis is at the CENTER of the body
    axis = (body_left + body_right) / 2.0
    
    # Determine protrusion direction
    left_protrusion = body_left - min_col
    right_protrusion = max_col - body_right
    
    return axis, int(round(axis))


def find_spine_column_spectral(grid: np.ndarray, color: int = 1) -> Optional[int]:
    """
    Find the spine using spectral analysis.
    
    The spine is where the shape is "most connected" vertically.
    We look for the column with maximum vertical connectivity.
    """
    mask = (grid == color)
    
    # Build per-column connectivity score
    # A column is part of the spine if:
    # 1. It has pixels in many rows
    # 2. Those pixels are vertically connected (consecutive rows)
    
    best_col = None
    best_score = 0
    
    for col in range(grid.shape[1]):
        col_rows = np.where(mask[:, col])[0]
        if len(col_rows) == 0:
            continue
        
        # Connectivity: how consecutive are the rows?
        if len(col_rows) > 1:
            gaps = np.diff(col_rows)
            connectivity = np.sum(gaps == 1) / (len(col_rows) - 1)
        else:
            connectivity = 1.0
        
        # Score = presence * connectivity
        score = len(col_rows) * connectivity
        
        if score > best_score:
            best_score = score
            best_col = col
    
    return best_col


def compute_reflection_completion(grid: np.ndarray, color: int = 1) -> Dict[str, Any]:
    """
    Compute symmetry completion by mirroring protrusions across the body center.
    
    Theory-derived algorithm (from SGC):
    1. Find the symmetry axis = center of G-kernel (body)
    2. Identify protrusions beyond the body (G-defect)
    3. Mirror protrusions to complete symmetry
    
    The body is the symmetric core with high vertical presence.
    Protrusions extend asymmetrically from the body.
    """
    mask = (grid == color)
    positions = np.array(list(zip(*np.where(mask))))
    
    if len(positions) == 0:
        return {'success': False, 'reason': 'No pixels found'}
    
    # Find the symmetry axis (center of body)
    axis, body_center = find_symmetry_axis(grid, color)
    
    if axis is None:
        return {'success': False, 'reason': 'Could not find axis'}
    
    # Get body columns (same logic as find_symmetry_axis)
    col_presence = mask.sum(axis=0)
    active_rows = np.where(mask.any(axis=1))[0]
    n_active_rows = len(active_rows)
    threshold = 0.6 * n_active_rows  # Match find_symmetry_axis
    body_cols = [c for c in range(grid.shape[1]) if col_presence[c] >= threshold]
    
    if not body_cols:
        min_col = int(positions[:, 1].min())
        max_col = int(positions[:, 1].max())
        body_cols = list(range(min_col, max_col + 1))
    
    body_left = min(body_cols)
    body_right = max(body_cols)
    
    # Protrusions are pixels OUTSIDE the body columns
    min_col = int(positions[:, 1].min())
    max_col = int(positions[:, 1].max())
    
    left_protrusion = body_left - min_col
    right_protrusion = max_col - body_right
    
    if right_protrusion > left_protrusion:
        # Protrusion on RIGHT (beyond body_right), mirror to LEFT
        protrusions = positions[positions[:, 1] > body_right]
    else:
        # Protrusion on LEFT, mirror to RIGHT
        protrusions = positions[positions[:, 1] < body_left]
    
    # Mirror protrusions across the axis
    additions = []
    for pos in protrusions:
        r, c = int(pos[0]), int(pos[1])
        # Mirror formula: new_c = 2 * axis - c
        mirror_c = int(round(2 * axis - c))
        
        if 0 <= mirror_c < grid.shape[1]:
            if grid[r, mirror_c] == 0:
                additions.append((r, mirror_c))
    
    return {
        'success': True,
        'body_cols': (body_left, body_right),
        'axis': axis,
        'n_protrusions': len(protrusions),
        'additions': additions
    }


def predict_output(input_grid: np.ndarray, result: Dict[str, Any],
                   output_color: int = 2) -> np.ndarray:
    """Generate predicted output from completion result."""
    output = input_grid.copy()
    
    if not result.get('success', False):
        return output
    
    for r, c in result.get('additions', []):
        output[r, c] = output_color
    
    return output


def analyze_task(input_grid: np.ndarray, output_grid: np.ndarray,
                 verbose: bool = True) -> Dict[str, Any]:
    """
    Analyze task using spine-based reflection.
    """
    result = compute_reflection_completion(input_grid)
    
    if verbose:
        if result['success']:
            print(f"Body columns: {result['body_cols']}")
            print(f"Reflection axis: {result['axis']}")
            print(f"Protrusions: {result['n_protrusions']}")
            print(f"Predicted additions: {len(result['additions'])}")
        else:
            print(f"Failed: {result.get('reason')}")
    
    predicted = predict_output(input_grid, result)
    
    actual_add = (output_grid == 2) & (input_grid == 0)
    predicted_add = (predicted == 2) & (input_grid == 0)
    
    overlap = (actual_add & predicted_add).sum()
    union = (actual_add | predicted_add).sum()
    iou = overlap / max(union, 1)
    
    if verbose:
        print(f"Actual additions: {actual_add.sum()}")
        print(f"IoU: {iou:.2%}")
        
        if iou < 1.0 and predicted_add.sum() > 0:
            pred_set = set(zip(*np.where(predicted_add)))
            actual_set = set(zip(*np.where(actual_add)))
            missing = actual_set - pred_set
            extra = pred_set - actual_set
            if missing:
                print(f"Missing: {sorted(list(missing))[:5]}")
            if extra:
                print(f"Extra: {sorted(list(extra))[:5]}")
    
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
    print("SPINE-BASED REFLECTION: Theory-Derived Symmetry Completion")
    print("=" * 70)
    print()
    print("From Theory:")
    print("- G-kernel = Spine (vertically consistent structure)")
    print("- G-defect = Protrusions (horizontal extensions)")
    print("- Rule = Mirror defect across spine boundary")
    print()
    
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
