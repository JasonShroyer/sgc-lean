"""
Phase 11b Diagnostic Ablation

Measures three scalars to identify dominant failure mode:
1. Median neighbor degree under cross-task similarity graph
2. Sheaf energy distribution for TL vs morph predicates  
3. Acceptance failures categorized by gate clause
"""
import os, sys
sys.path.insert(0, '.')

import numpy as np
from collections import defaultdict
from arc_sgc_phase8_3 import load_arc_tasks
from arc_sgc_residual_solver import (
    RecursiveResidualSolver, _morph_residual_refine, _tensor_residual_refine,
    DiscreteGradient, cluster_by_transformation_signature, HAS_MORPH_ALGEBRA
)

print(f"HAS_MORPH_ALGEBRA: {HAS_MORPH_ALGEBRA}")

tasks = load_arc_tasks('C:/Lean4 Projects/data/arc/training')
N = min(int(os.getenv('SGFE_TASK_LIMIT', '20')), len(tasks))
print(f"Running diagnostic on {N} tasks\n")

# Collectors
neighbor_degrees = []
sheaf_energies_morph = []
sheaf_energies_tl = []
rejection_reasons = defaultdict(int)
signature_vectors = []

class IdentityOp:
    name = 'identity'
    def apply(self, grid):
        return grid.copy()

for i, task in enumerate(tasks[:N]):
    print(f"[{i+1:3d}/{N}] {task.task_id}", end=" ", flush=True)
    
    # 1. Compute transformation signature for this task
    predictions = [ex.input_grid.data.numpy() for ex in task.train_examples]
    targets = [ex.output_grid.data.numpy() for ex in task.train_examples]
    
    # Filter same-shape examples
    valid = [(p, t) for p, t in zip(predictions, targets) if p.shape == t.shape]
    if not valid:
        print("(shape mismatch)")
        continue
    
    predictions, targets = zip(*valid)
    gradients = [DiscreteGradient.compute(p, t) for p, t in zip(predictions, targets)]
    
    # Build signature vector (same as cross-task validator)
    for grad in gradients:
        pos_frac = grad.positive_mask.sum() / max(grad.grid_size, 1)
        neg_frac = grad.negative_mask.sum() / max(grad.grid_size, 1)
        recolor_frac = grad.recolor_mask.sum() / max(grad.grid_size, 1)
        pure_recolor = 1.0 if grad.is_pure_recolor or grad.total_diff == 0 else 0.0
        sig = (pos_frac, neg_frac, recolor_frac, pure_recolor)
        signature_vectors.append(sig)
    
    # 2. Run morphological predicate synthesis and collect sheaf energies
    morph_result = _morph_residual_refine(
        task, IdentityOp(), list(range(len(task.train_examples))), verbose=False)
    
    for op, log in morph_result:
        if 'sheaf_energy' in log:
            sheaf_energies_morph.append(log['sheaf_energy'])
    
    # 3. Run TL predicate synthesis and collect sheaf energies + rejection reasons
    try:
        tl_result = _tensor_residual_refine(
            task, IdentityOp(), list(range(len(task.train_examples))),
            seed=hash(task.task_id) & 0x7FFFFFFF, verbose=False)
        
        for op, log in tl_result:
            if 'sheaf_energy' in log:
                sheaf_energies_tl.append(log['sheaf_energy'])
            if 'rejection_reason' in log:
                rejection_reasons[log['rejection_reason']] += 1
    except Exception as e:
        print(f"(TL error: {e})")
        continue
    
    print(f"morph={len(morph_result)} tl={len(tl_result)}")

# Compute neighbor degrees using transformation signature similarity
print("\n" + "="*60)
print("DIAGNOSTIC RESULTS")
print("="*60)

# 1. Neighbor degree analysis
print("\n### 1. Neighbor Degree Distribution ###")
if len(signature_vectors) >= 2:
    sig_array = np.array(signature_vectors)
    
    # Compute pairwise distances
    from scipy.spatial.distance import pdist, squareform
    distances = squareform(pdist(sig_array, metric='euclidean'))
    
    # Count neighbors at different thresholds
    for threshold in [0.3, 0.5, 0.6, 0.8]:
        neighbor_counts = (distances < threshold).sum(axis=1) - 1  # Exclude self
        print(f"  threshold={threshold}: min={neighbor_counts.min()} median={np.median(neighbor_counts):.1f} "
              f"mean={neighbor_counts.mean():.2f} max={neighbor_counts.max()}")
        if threshold == 0.6:
            neighbor_degrees = list(neighbor_counts)

# 2. Sheaf energy distribution
print("\n### 2. Sheaf Energy Distribution ###")
print(f"  Morphological predicates: n={len(sheaf_energies_morph)}")
if sheaf_energies_morph:
    print(f"    min={min(sheaf_energies_morph):.4f} median={np.median(sheaf_energies_morph):.4f} "
          f"mean={np.mean(sheaf_energies_morph):.4f} max={max(sheaf_energies_morph):.4f}")
    print(f"    sheaf_energy <= 0.3: {sum(1 for e in sheaf_energies_morph if e <= 0.3)}/{len(sheaf_energies_morph)}")

print(f"  TL predicates: n={len(sheaf_energies_tl)}")
if sheaf_energies_tl:
    print(f"    min={min(sheaf_energies_tl):.4f} median={np.median(sheaf_energies_tl):.4f} "
          f"mean={np.mean(sheaf_energies_tl):.4f} max={max(sheaf_energies_tl):.4f}")
    print(f"    sheaf_energy <= 0.3: {sum(1 for e in sheaf_energies_tl if e <= 0.3)}/{len(sheaf_energies_tl)}")
    print(f"    sheaf_energy <= 0.6: {sum(1 for e in sheaf_energies_tl if e <= 0.6)}/{len(sheaf_energies_tl)}")

# 3. Rejection reasons
print("\n### 3. Acceptance Failure Categories ###")
if rejection_reasons:
    for reason, count in sorted(rejection_reasons.items(), key=lambda x: -x[1]):
        print(f"  {reason}: {count}")
else:
    print("  (No rejection reasons logged - check if TL is accepting or not triggering)")

# 4. Signature analysis
print("\n### 4. Transformation Signature Analysis ###")
print(f"  Total signature vectors: {len(signature_vectors)}")
print(f"  Signature dimensionality: 4D (pos_frac, neg_frac, recolor_frac, pure_recolor)")
if signature_vectors:
    sig_array = np.array(signature_vectors)
    print(f"  Component ranges:")
    for i, name in enumerate(['pos_frac', 'neg_frac', 'recolor_frac', 'pure_recolor']):
        print(f"    {name}: [{sig_array[:,i].min():.3f}, {sig_array[:,i].max():.3f}]")
    
    # Check discretization potential
    unique_pure_recolor = len(set(sig_array[:,3]))
    print(f"  pure_recolor unique values: {unique_pure_recolor} (ideal: 2 for binary)")

print("\n" + "="*60)
print("DIAGNOSIS SUMMARY")
print("="*60)

# Diagnose dominant failure mode
if len(neighbor_degrees) > 0 and np.median(neighbor_degrees) == 0:
    print("DOMINANT FAILURE: Signature granularity mismatch")
    print("  → Median neighbor degree = 0 indicates singleton clusters")
    print("  → Fix: Coarsen signature (reduce k, discretize components)")
elif len(sheaf_energies_tl) > 0 and np.median(sheaf_energies_tl) > 0.6:
    print("DOMINANT FAILURE: Distance function mismatch")
    print("  → TL predicates have high sheaf energy (position leakage)")
    print("  → Fix: Remove coordinate gauge from TL features")
elif len(rejection_reasons) > 0:
    top_reason = max(rejection_reasons.items(), key=lambda x: x[1])
    print(f"DOMINANT FAILURE: Validation policy mismatch")
    print(f"  → Top rejection reason: {top_reason[0]} ({top_reason[1]} occurrences)")
    print("  → Fix: Align acceptance with renormalization (skip peer validation for low-sheaf)")
else:
    print("INCONCLUSIVE: Need more data or check logging")
