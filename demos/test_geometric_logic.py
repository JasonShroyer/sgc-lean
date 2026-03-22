#!/usr/bin/env python3
"""Test Geometric Boolean Logic via Sheaf Laplacian."""

import numpy as np
from spiking_sheaf_engine import SpikingSheafEngine

# Create a simple test grid with two stalks
grid = np.array([
    [0, 0, 1, 1, 0],
    [0, 0, 1, 1, 0],
    [0, 0, 0, 0, 0],
    [2, 2, 0, 0, 0],
    [2, 2, 0, 0, 0]
], dtype=np.float32)

print("=" * 60)
print("TESTING GEOMETRIC BOOLEAN LOGIC VIA SHEAF LAPLACIAN")
print("=" * 60)

# Initialize engine
engine = SpikingSheafEngine(grid)

# Decompose into stalks
stalks = engine.decompose_to_stalks(grid)
print(f"\nStalks found: {len(stalks)}")
for i, s in enumerate(stalks):
    print(f"  Stalk {i}: color={s['color']}, pixels={s['n_pixels']}")

# Test Logical Laplacian building
print("\n--- Testing Logical Laplacian Building ---")
L_and = engine.build_logical_laplacian(stalks, logic_type='and')
print(f"AND Laplacian shape: {L_and.shape}")

L_or = engine.build_logical_laplacian(stalks, logic_type='or')
print(f"OR Laplacian shape: {L_or.shape}")

L_not = engine.build_logical_laplacian(stalks, logic_type='not')
print(f"NOT Laplacian shape: {L_not.shape}")

# Test Geometric OR
print("\n--- Testing Geometric OR ---")
result_or = engine.compute_geometric_or(stalks)
print(f"OR result:\n{result_or}")

# Test Geometric NOT (phase inversion)
print("\n--- Testing Geometric NOT ---")
if stalks:
    result_not = engine.compute_geometric_not(stalks[0])
    print(f"NOT result (inverted stalk 0):\n{result_not}")

# Test Sparse Neuromorphic Substrate
print("\n--- Testing Sparse Neuromorphic Substrate ---")
L = engine.build_graph_laplacian()
X = grid.copy()
sparse_result = engine.compute_sparse_laplacian_product(L, X)
print(f"Sparse Laplacian product computed (non-zero elements: {np.count_nonzero(sparse_result)})")

# Test Grokking Phase Transition
print("\n--- Testing Grokking Phase Transition ---")
target = grid.copy()  # Same as input for this test
result = engine.crystallize_logical_laplacian(
    stalks, 
    target,
    max_iterations=20,
    initial_temperature=1.0,
    sparsity_lambda=0.1
)
print(f"Grokking result:")
print(f"  Grokked: {result['grokked']}")
print(f"  Final Accuracy: {result['final_accuracy']:.4f}")
print(f"  Structural Complexity: {result['structural_complexity']:.4f}")
print(f"  Edge Weights: {result['edge_weights']}")

print("\n" + "=" * 60)
print("GEOMETRIC LOGIC TEST COMPLETE")
print("=" * 60)
