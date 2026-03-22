"""Diagnostic test for v4 hierarchical signatures."""
import numpy as np
from emergent_sheaf_engine import EmergentSheafEngine, EmergentSheafAtlas

print("=== Test 1: Position-Invariance of Hierarchical Signatures ===")
# L-shape at top-left
g1 = np.array([
    [1, 0, 0, 0, 0],
    [1, 0, 0, 0, 0],
    [1, 1, 0, 0, 0],
    [0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0]
], dtype=float)

# Same L-shape at bottom-right
g2 = np.array([
    [0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0],
    [0, 0, 0, 1, 0],
    [0, 0, 0, 1, 1]
], dtype=float)

e1 = EmergentSheafEngine(g1)
e2 = EmergentSheafEngine(g2)

# Hierarchical (local stalk) signatures
sig1 = e1.compute_hierarchical_signature()
sig2 = e2.compute_hierarchical_signature()

cos_sim = np.dot(sig1, sig2) / (np.linalg.norm(sig1) * np.linalg.norm(sig2) + 1e-10)
print(f"Hierarchical signatures cosine similarity: {cos_sim:.4f}")
print(f"  sig1[:4] = {sig1[:4]}")
print(f"  sig2[:4] = {sig2[:4]}")

# Global signatures for comparison
global_sig1 = e1.compute_spectral_signature(16)
global_sig2 = e2.compute_spectral_signature(16)
global_cos = np.dot(global_sig1, global_sig2) / (np.linalg.norm(global_sig1) * np.linalg.norm(global_sig2) + 1e-10)
print(f"Global signatures cosine similarity: {global_cos:.4f}")
print(f"Improvement (hierarchical - global): {cos_sim - global_cos:.4f}")

print("\n=== Test 2: Atlas Storage and Retrieval ===")
atlas = EmergentSheafAtlas(signature_dims=16)
atlas.add_chart(sig1, [{"type": "test_op", "name": "fill_L"}], {"task": "test1"})
print(f"Atlas size after adding: {atlas.size()}")

# Lookup with sig2 (the shifted version)
matches = atlas.find_top_k_charts(sig2, k=1, min_similarity=0.0)
if matches:
    print(f"Found match with similarity = {matches[0]['similarity']:.4f}")
else:
    print("No match found")

print("\n=== Test 3: Stalk Decomposition ===")
stalks1 = e1.decompose_to_stalks()
stalks2 = e2.decompose_to_stalks()
print(f"Grid 1 stalks: {len(stalks1)}")
print(f"Grid 2 stalks: {len(stalks2)}")
for i, s in enumerate(stalks1):
    print(f"  Stalk {i}: pixels={s['n_pixels']}, pos={s['position']}, sig[:3]={s['spectral_signature'][:3]}")

print("\n=== Summary ===")
if cos_sim > 0.95:
    print("SUCCESS: Hierarchical signatures are position-invariant!")
elif cos_sim > global_cos:
    print(f"PARTIAL: Hierarchical better than global ({cos_sim:.3f} vs {global_cos:.3f})")
else:
    print("ISSUE: Hierarchical signatures not achieving position-invariance")
