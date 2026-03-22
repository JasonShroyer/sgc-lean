"""
Unit Test: Demonstrating True Gauge Transport (g != e)

This test creates controlled synthetic grids to prove that:
1. Directional predicates (spin-1 vectors) break D4 symmetry
2. Identity gauge fails when orientation is mismatched
3. Non-identity gauge (r90, flip_h, etc.) rescues the transfer

This is the definitive proof that the Sheaf Atlas resolves the Holonomy Obstruction.
"""

import numpy as np
import sys
sys.path.insert(0, '.')

from sheaf_atlas import SheafAtlas, GaugeElement, D4_GROUP

# =============================================================================
# DIRECTIONAL PREDICATE: Detects RIGHT edges only
# =============================================================================

def directional_edge_right(grid: np.ndarray) -> np.ndarray:
    """
    Detects pixels on the RIGHT edge of non-zero regions.
    
    This is a VECTOR (spin-1) predicate that breaks D4 symmetry.
    - On a grid with vertical stripes, it detects right edges of each stripe
    - On a grid with horizontal stripes, it detects nothing useful
    """
    mask = (grid > 0).astype(np.float32)
    h, w = mask.shape
    
    # Shift left by 1 (what's to the right of each pixel)
    shifted = np.zeros_like(mask)
    if w > 1:
        shifted[:, :-1] = mask[:, 1:]  # shifted[i,j] = mask[i,j+1]
    
    # Right edge = pixel is in mask, but pixel to right is not
    right_edge = np.clip(mask - shifted, 0, 1)
    return right_edge


def directional_edge_bottom(grid: np.ndarray) -> np.ndarray:
    """
    Detects pixels on the BOTTOM edge of non-zero regions.
    This is what directional_edge_right becomes under r90 rotation.
    """
    mask = (grid > 0).astype(np.float32)
    h, w = mask.shape
    
    # Shift up by 1 (what's below each pixel)
    shifted = np.zeros_like(mask)
    if h > 1:
        shifted[:-1, :] = mask[1:, :]  # shifted[i,j] = mask[i+1,j]
    
    # Bottom edge = pixel is in mask, but pixel below is not
    bottom_edge = np.clip(mask - shifted, 0, 1)
    return bottom_edge


# =============================================================================
# TEST GRIDS
# =============================================================================

# Grid A: VERTICAL stripes (right edges exist)
grid_vertical = np.array([
    [0, 1, 1, 0, 1, 1, 0],
    [0, 1, 1, 0, 1, 1, 0],
    [0, 1, 1, 0, 1, 1, 0],
    [0, 1, 1, 0, 1, 1, 0],
    [0, 1, 1, 0, 1, 1, 0],
])

# Grid B: HORIZONTAL stripes (bottom edges exist, right edges minimal)
grid_horizontal = np.array([
    [0, 0, 0, 0, 0, 0, 0],
    [1, 1, 1, 1, 1, 1, 1],
    [1, 1, 1, 1, 1, 1, 1],
    [0, 0, 0, 0, 0, 0, 0],
    [1, 1, 1, 1, 1, 1, 1],
])

# Target: We want to identify pixels that need to change
# For demo purposes, let's say we want to highlight edges
target_vertical = np.array([
    [0, 0, 1, 0, 0, 1, 0],  # Right edges of vertical stripes
    [0, 0, 1, 0, 0, 1, 0],
    [0, 0, 1, 0, 0, 1, 0],
    [0, 0, 1, 0, 0, 1, 0],
    [0, 0, 1, 0, 0, 1, 0],
])

target_horizontal = np.array([
    [0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0],
    [1, 1, 1, 1, 1, 1, 1],  # Bottom edge of first stripe
    [0, 0, 0, 0, 0, 0, 0],
    [1, 1, 1, 1, 1, 1, 1],  # Bottom edge of second stripe
])


def compute_overlap(pred_mask: np.ndarray, target: np.ndarray) -> float:
    """Compute how well the predicate mask matches the target."""
    pred_bool = pred_mask > 0.5
    target_bool = target > 0
    
    intersection = np.sum(pred_bool & target_bool)
    union = np.sum(pred_bool | target_bool)
    
    if union == 0:
        return 0.0
    return float(intersection) / float(union)  # IoU


# =============================================================================
# MAIN TEST
# =============================================================================

def run_test():
    print("="*70)
    print("GAUGE TRANSPORT UNIT TEST")
    print("Demonstrating Holonomy Resolution via D4 Transformations")
    print("="*70)
    
    # Show the grids
    print("\nGrid A (VERTICAL stripes):")
    print(grid_vertical)
    print("\nGrid B (HORIZONTAL stripes):")
    print(grid_horizontal)
    
    # Test directional_edge_right on both grids
    print("\n" + "-"*70)
    print("TEST 1: directional_edge_right predicate")
    print("-"*70)
    
    mask_a = directional_edge_right(grid_vertical)
    mask_b = directional_edge_right(grid_horizontal)
    
    print("\nOn Grid A (vertical stripes) - should detect right edges:")
    print(mask_a.astype(int))
    print(f"IoU with target: {compute_overlap(mask_a, target_vertical):.3f}")
    
    print("\nOn Grid B (horizontal stripes) - should detect very little:")
    print(mask_b.astype(int))
    print(f"IoU with target: {compute_overlap(mask_b, target_horizontal):.3f}")
    
    # Now test gauge transport
    print("\n" + "-"*70)
    print("TEST 2: GAUGE TRANSPORT")
    print("-"*70)
    
    print("\nProblem: We have a directional_edge_right predicate from Task A.")
    print("We want to apply it to Task B, which needs BOTTOM edges.")
    print("Identity gauge (g=e) will FAIL. We need gauge transport!")
    
    # Find the right gauge element
    print("\nTrying all D4 gauge elements:")
    
    best_gauge = None
    best_iou = 0.0
    
    for g in D4_GROUP:
        # Apply gauge transport: P_g(X) = g^{-1}(P(g(X)))
        transported_mask = g.transport_predicate(directional_edge_right, grid_horizontal)
        iou = compute_overlap(transported_mask, target_horizontal)
        
        status = ""
        if g.name == "e":
            status = " <-- IDENTITY"
        if iou > best_iou:
            best_iou = iou
            best_gauge = g
            status += " <-- BEST SO FAR"
        
        print(f"  {g.name:10s}: IoU = {iou:.3f}{status}")
    
    print(f"\nBest gauge: {best_gauge.name} with IoU = {best_iou:.3f}")
    
    if best_gauge.name != "e":
        print("\n" + "="*70)
        print("SUCCESS: Non-identity gauge (g != e) provides better transfer!")
        print("="*70)
        print(f"\nThe predicate directional_edge_right from Task A")
        print(f"was successfully transported to Task B via gauge '{best_gauge.name}'")
        print(f"\nThis demonstrates HOLONOMY RESOLUTION:")
        print(f"  - Identity gauge IoU: {compute_overlap(directional_edge_right(grid_horizontal), target_horizontal):.3f}")
        print(f"  - {best_gauge.name} gauge IoU: {best_iou:.3f}")
        print(f"\nThe gauge transformation rotated the semantic frame!")
    else:
        print("\nIdentity happened to work best (grids have similar orientation)")
    
    # Show the winning transported mask
    print("\n" + "-"*70)
    print(f"WINNING MASK (via {best_gauge.name}):")
    print("-"*70)
    winning_mask = best_gauge.transport_predicate(directional_edge_right, grid_horizontal)
    print(winning_mask.astype(int))
    
    # Compare with target
    print("\nTarget (what we want):")
    print(target_horizontal)
    
    # Final verification
    print("\n" + "="*70)
    print("VERIFICATION: Gauge Transport Mechanism")
    print("="*70)
    
    print("\nStep 1: Apply gauge g to input grid")
    g_grid = best_gauge.apply(grid_horizontal)
    print(f"g({best_gauge.name})(grid_horizontal) =")
    print(g_grid)
    
    print("\nStep 2: Apply predicate P to transformed grid")
    p_g_grid = directional_edge_right(g_grid)
    print(f"P(g(grid)) = directional_edge_right(...) =")
    print(p_g_grid.astype(int))
    
    print("\nStep 3: Apply inverse g^{-1} to transport mask back")
    final_mask = best_gauge.apply_inverse(p_g_grid)
    print(f"g^{{-1}}(P(g(grid))) =")
    print(final_mask.astype(int))
    
    print("\nThis is the PULLBACK definition of gauge transport:")
    print("P_g(X) = g^{-1}(P(g(X)))")
    
    return best_gauge.name != "e"


if __name__ == "__main__":
    success = run_test()
    print("\n" + "="*70)
    if success:
        print("GAUGE TRANSPORT PROVEN: Non-identity gauge required for transfer!")
    else:
        print("Note: Identity worked best for this specific grid pair.")
    print("="*70)
