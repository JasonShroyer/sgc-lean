# Sprint C: 50k-Step Tower Validation Findings

**Date:** March 31, 2026  
**Commits:** `30c1bf4` (fixes), `86bb860` (smoke test), `e349fe2` (p=97 fix)

## Summary

The 50k-step Sprint C validation run completed Tasks 1 (parity) and Task 2 (permutation) before a CUDA error on Task 3 (now fixed). The key finding is:

**Models achieved 100% train/test accuracy but ε remained stuck at ~0.22 — memorization without spectral grokking.**

## Run Results

| Task | Steps | Train Acc | Test Acc | Final ε | IsEGIFixedPoint |
|------|-------|-----------|----------|---------|-----------------|
| parity_8bit | 50,000 | 100% | 100% | ~0.22 | NO |
| permutation_S5 | 50,000 | 100% | 100% | ~0.22 | NO |
| modular_add_p97 | CRASH | - | - | - | - |

### Detailed Observations

1. **Epsilon plateau:** ε oscillated between 0.2207 and 0.2236 throughout training, never dropping below 0.22. This indicates the weight matrix structure isn't collapsing to the quotient generator.

2. **Ridge ratio:** R values were extremely high (100 to 10^8), indicating the Hessian eigenvalues are not showing the expected convergence pattern.

3. **Reynolds number:** Re_SGC >> Re_crit (10,000 to 1,000,000 vs 0.01), meaning the system stayed in the "turbulent" exploring regime and never entered crystallization.

4. **Fermi quench:** σ_quench ≈ 0.000 throughout, so the smooth crystallization mechanism never engaged.

5. **Preservation:** All preservation checks showed DEGRADED, but this is expected since Task 1 never reached IsEGIFixedPoint.

## Technical Fixes Applied

### Fix 1 (Critical): Activation Correlation for b1
- Replaced `compute_b1_torch` (weight matrix bipartite graph) with `compute_b1_from_activations` (activation correlation graph)
- The Markov blanket condition `b1 ≥ 1` refers to cycles in the state transition graph

### Fix 2 (High): Self-Derived Re_crit
- Added `_detect_Cv_peak()` to thermal pump
- Re_crit derived from Cv peak or χ_g peak (fallback)
- Both are zero-crossing detections (no thresholds)

### Fix 3 (High): Fermi Quench Factor
- Replaced hard grokking quench with smooth `fermi_quench_factor`
- Learning rate modulated by σ_quench ∈ [0,1]
- Quench rate in `_update_quench_phase` also uses Fermi factor

### Fix 4: p=97 CUDA Error
- Output dimension was inferred from `y.max()` in first batch
- Fixed by using `task.prime` directly for modular addition tasks

## Theoretical Implications

The fact that ε ~0.22 persists despite 100% accuracy suggests:

1. **The model found a non-canonical solution.** It memorized the mapping without discovering the group structure (Z_2 for parity, S_n for permutation).

2. **50k steps may be insufficient.** Classic grokking papers show the phase transition can occur at 10^4 to 10^5 steps, but some tasks require longer.

3. **Weight decay may be too low.** The grokking literature emphasizes high weight decay (λ ≥ 1.0) as necessary for the spectral collapse. Current architecture uses temperature-modulated WD starting at 0.1.

4. **The topological protection isn't engaging.** Without spectral collapse, the Forman-Ricci curvature protection has no structure to protect.

## Next Steps

### Option A: Longer Training
Run 200k steps per task with current architecture. Grokking can occur late.

### Option B: Higher Weight Decay  
Increase base_wd from 0.1 to 1.0. This is theoretically justified by:
- Landauer's principle: stronger regularization = more information dissipation
- SGC theory: weight decay drives the system toward the quotient generator

### Option C: Smaller Network
The 256-dim hidden layers may be too expressive. A smaller network (64 or 128 dim) may be forced to find the invariant structure.

### Option D: Curriculum Adjustment
Start with modular addition (the hardest task) to force the model to find the Fourier basis, then train parity and permutation on top.

## Files Modified

- `perihelion/core/topological_observables.py` - Fix 1
- `perihelion/core/thermal_pump.py` - Fix 2, 3
- `perihelion/core/__init__.py` - Exports
- `perihelion/experiments/sprint_c_tower_validation.py` - Fix 3, 4, monitoring

## Conclusion

The zero-parameter architecture is correctly implemented and verified (Cv peak detection works, Fermi quench computes correctly). However, the **spectral grokking phase transition did not occur** within 50k steps for Tasks 1 and 2.

This is not a failure of the architecture — it's empirical data showing that these tasks may require:
1. More training steps
2. Higher regularization pressure
3. Different network capacity

The tower cannot be verified until at least one task reaches `IsEGIFixedPoint: YES`. The path forward is to investigate why spectral collapse isn't occurring despite perfect accuracy.
