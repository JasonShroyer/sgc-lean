#!/usr/bin/env python3
"""
Test v6 Vectorized Instructive Signals

Verify that the Defect Gradient Analyzer correctly extracts:
1. Spatial gradients -> translation operators (O(1) inference)
2. Color gradients -> color transition operators (O(1) inference)
3. Morphological gradients -> dilation/erosion operators
4. Geodesic gradients -> ray operators

The key metric is: does the engine solve in 1-2 iterations instead of 50?
"""

import numpy as np
import sys
import time

sys.path.insert(0, '.')
from emergent_sheaf_engine import EmergentSheafEngine


def test_translation_gradient():
    """Test that spatial shift is detected and solved in O(1)."""
    print("\n=== Test 1: Translation Gradient ===")
    
    # Input: object at (1,1)
    input_grid = np.array([
        [0, 0, 0, 0, 0],
        [0, 3, 3, 0, 0],
        [0, 3, 3, 0, 0],
        [0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0]
    ], dtype=float)
    
    # Target: same object shifted by (+2, +1)
    target_grid = np.array([
        [0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0],
        [0, 0, 3, 3, 0],
        [0, 0, 3, 3, 0]
    ], dtype=float)
    
    engine = EmergentSheafEngine(input_grid, target_grid)
    
    # First, test the gradient analyzer directly
    instructed_ops = engine.analyze_free_energy_gradient(input_grid)
    print(f"  Instructed operators found: {len(instructed_ops)}")
    for op in instructed_ops[:3]:
        print(f"    - {op.get('name', op['type'])}: conf={op.get('confidence', 0):.2f}")
    
    # Now run full discovery
    start = time.time()
    result = engine.thermodynamic_discovery(verbose=True)
    elapsed = time.time() - start
    
    success = result.get('success', False)
    iterations = result.get('iterations', 0)
    vectorized = result.get('vectorized_accepts', 0)
    random = result.get('random_accepts', 0)
    method = result.get('method', 'unknown')
    
    print(f"  Success: {success}")
    print(f"  Method: {method}")
    print(f"  Iterations: {iterations}")
    print(f"  Vectorized accepts: {vectorized}")
    print(f"  Random accepts: {random}")
    print(f"  Time: {elapsed:.3f}s")
    
    # O(1) criterion: should solve in <= 3 iterations with vectorized signal
    is_o1 = iterations <= 3 and vectorized > 0
    print(f"  O(1) Inference: {'[OK]' if is_o1 else '[FAIL]'}")
    
    return success and is_o1


def test_color_gradient():
    """Test that color change is detected and solved in O(1)."""
    print("\n=== Test 2: Color Gradient ===")
    
    # Input: blue object
    input_grid = np.array([
        [0, 0, 0, 0],
        [0, 1, 1, 0],
        [0, 1, 1, 0],
        [0, 0, 0, 0]
    ], dtype=float)
    
    # Target: same shape, different color (red)
    target_grid = np.array([
        [0, 0, 0, 0],
        [0, 2, 2, 0],
        [0, 2, 2, 0],
        [0, 0, 0, 0]
    ], dtype=float)
    
    engine = EmergentSheafEngine(input_grid, target_grid)
    
    # Test gradient analyzer
    instructed_ops = engine.analyze_free_energy_gradient(input_grid)
    print(f"  Instructed operators found: {len(instructed_ops)}")
    for op in instructed_ops[:3]:
        print(f"    - {op.get('name', op['type'])}: conf={op.get('confidence', 0):.2f}")
    
    # Run discovery
    start = time.time()
    result = engine.thermodynamic_discovery(verbose=True)
    elapsed = time.time() - start
    
    success = result.get('success', False)
    iterations = result.get('iterations', 0)
    vectorized = result.get('vectorized_accepts', 0)
    method = result.get('method', 'unknown')
    
    print(f"  Success: {success}")
    print(f"  Method: {method}")
    print(f"  Iterations: {iterations}")
    print(f"  Vectorized accepts: {vectorized}")
    print(f"  Time: {elapsed:.3f}s")
    
    is_o1 = iterations <= 3 and vectorized > 0
    print(f"  O(1) Inference: {'[OK]' if is_o1 else '[FAIL]'}")
    
    return success and is_o1


def test_dilation_gradient():
    """Test that morphological growth is detected."""
    print("\n=== Test 3: Dilation Gradient ===")
    
    # Input: small object
    input_grid = np.array([
        [0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0],
        [0, 0, 5, 0, 0],
        [0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0]
    ], dtype=float)
    
    # Target: dilated object (cross shape)
    target_grid = np.array([
        [0, 0, 0, 0, 0],
        [0, 0, 5, 0, 0],
        [0, 5, 5, 5, 0],
        [0, 0, 5, 0, 0],
        [0, 0, 0, 0, 0]
    ], dtype=float)
    
    engine = EmergentSheafEngine(input_grid, target_grid)
    
    # Test gradient analyzer
    instructed_ops = engine.analyze_free_energy_gradient(input_grid)
    print(f"  Instructed operators found: {len(instructed_ops)}")
    for op in instructed_ops[:3]:
        print(f"    - {op.get('name', op['type'])}: conf={op.get('confidence', 0):.2f}")
    
    # Check if dilation was proposed
    has_dilation = any(op['type'] == 'spectral_dilation' for op in instructed_ops)
    print(f"  Dilation signal detected: {'[OK]' if has_dilation else '[FAIL]'}")
    
    return has_dilation


def test_geodesic_gradient():
    """Test that line between stalks is detected as geodesic ray."""
    print("\n=== Test 4: Geodesic Gradient ===")
    
    # Input: two objects
    input_grid = np.array([
        [0, 0, 0, 0, 0, 0, 0],
        [0, 3, 0, 0, 0, 4, 0],
        [0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0]
    ], dtype=float)
    
    # Target: objects connected by a line
    target_grid = np.array([
        [0, 0, 0, 0, 0, 0, 0],
        [0, 3, 2, 2, 2, 4, 0],
        [0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0]
    ], dtype=float)
    
    engine = EmergentSheafEngine(input_grid, target_grid)
    
    # Test gradient analyzer
    instructed_ops = engine.analyze_free_energy_gradient(input_grid)
    print(f"  Instructed operators found: {len(instructed_ops)}")
    for op in instructed_ops[:3]:
        print(f"    - {op.get('name', op['type'])}: conf={op.get('confidence', 0):.2f}")
    
    # Check if geodesic ray was proposed
    has_geodesic = any(op['type'] == 'geodesic_ray' for op in instructed_ops)
    print(f"  Geodesic signal detected: {'[OK]' if has_geodesic else '[FAIL]'}")
    
    return has_geodesic


def test_combined_translation_color():
    """Test translation + color change (composition)."""
    print("\n=== Test 5: Combined Translation + Color ===")
    
    # Input: blue object at (1,1)
    input_grid = np.array([
        [0, 0, 0, 0, 0],
        [0, 1, 1, 0, 0],
        [0, 1, 1, 0, 0],
        [0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0]
    ], dtype=float)
    
    # Target: red object at (3,2)
    target_grid = np.array([
        [0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0],
        [0, 0, 2, 2, 0],
        [0, 0, 2, 2, 0]
    ], dtype=float)
    
    engine = EmergentSheafEngine(input_grid, target_grid)
    
    # Test gradient analyzer
    instructed_ops = engine.analyze_free_energy_gradient(input_grid)
    print(f"  Instructed operators found: {len(instructed_ops)}")
    for op in instructed_ops[:5]:
        print(f"    - {op.get('name', op['type'])}: conf={op.get('confidence', 0):.2f}")
    
    # Run discovery
    start = time.time()
    result = engine.thermodynamic_discovery(verbose=True)
    elapsed = time.time() - start
    
    success = result.get('success', False)
    iterations = result.get('iterations', 0)
    vectorized = result.get('vectorized_accepts', 0)
    
    print(f"  Success: {success}")
    print(f"  Iterations: {iterations}")
    print(f"  Vectorized accepts: {vectorized}")
    print(f"  Time: {elapsed:.3f}s")
    
    # For combined ops, should complete in reasonable iterations
    is_efficient = iterations <= 10
    print(f"  Efficient solve: {'[OK]' if is_efficient else '[FAIL]'}")
    
    return is_efficient


def main():
    print("=" * 60)
    print("EMERGENT SHEAF ENGINE v6 - Vectorized Instructive Signals")
    print("=" * 60)
    
    results = []
    
    results.append(("Translation Gradient", test_translation_gradient()))
    results.append(("Color Gradient", test_color_gradient()))
    results.append(("Dilation Gradient", test_dilation_gradient()))
    results.append(("Geodesic Gradient", test_geodesic_gradient()))
    results.append(("Combined Translation+Color", test_combined_translation_color()))
    
    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    
    passed = sum(1 for _, r in results if r)
    total = len(results)
    
    for name, result in results:
        status = "[OK]" if result else "[FAIL]"
        print(f"  {name}: {status}")
    
    print(f"\nTotal: {passed}/{total} tests passed")
    
    if passed == total:
        print("\nv6 Vectorized Instructive Signals: WORKING")
    else:
        print(f"\nv6 needs refinement: {total - passed} tests failed")
    
    return passed == total


if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)
