# SGC Phase-1c Implementation Summary

**Date:** February 1, 2026  
**Status:** COMPLETE  
**Goal:** Make SGC metrics scale-invariant (Fisher-Rao geometry)

---

## Key Changes

### 1. Python: Scale-Free Stiffness Criterion

**Before (Absolute Threshold):**
```python
stiff_mask = eigenvalues > tau_stiff  # Breaks at high confidence
```

**After (Relative Threshold - Phase-1c):**
```python
stiff_threshold = tau_rel * max_eig  # Scale-invariant
stiff_mask = eigenvalues > stiff_threshold
```

**File:** `demos/sgc_grokking_phase1.py`
- Parameter renamed: `tau_stiff` → `tau_rel`
- Default: `tau_rel = 0.1` (top 10% of spectrum)

### 2. Python: Normalized Spectrum Logging

New metrics in `SGCMetrics` dataclass:
- `fisher_rigidity_normalized`: Rigidity / Tr(F) (scale-invariant)
- `trace_fisher`: Σλᵢ (total Fisher mass)
- `spectral_gap`: λₖ / λₖ₊₁ (structure indicator)
- `normalized_eigenvalues`: (λᵢ/λ_max) for top eigenvalues
- `fisher_estimator`: Explicit identification of estimation method

New TensorBoard scalars:
- `ScaleFree/RigidityNormalized`
- `ScaleFree/TraceFisher`
- `ScaleFree/SpectralGap`
- `Spectrum/NormEig_{1-5}`

### 3. Lean: FisherSpectralCriterionRel

**New Definition (lines 359-361):**
```lean
def FisherSpectralCriterionRel (F : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (tau_rel : ℝ) : Prop :=
  v ≠ 0 ∧ FisherRayleighQuotient F v > tau_rel * FisherOperatorNorm F
```

**Supporting Axioms:**
- `FisherOperatorNorm`: λ_max(F) proxy
- `FisherOperatorNorm_nonneg`: Non-negativity for PSD matrices
- `FisherSpectralCriterionRel_scale_invariant`: Key invariance theorem

### 4. Lean: DefectGatedConsolidationCriterionRel

**New Definition (lines 561-563):**
```lean
def DefectGatedConsolidationCriterionRel (F : Matrix (Fin n) (Fin n) ℝ)
    (v g : Fin n → ℝ) (tau_rel eps_stable : ℝ) : Prop :=
  FisherSpectralCriterionRel F v tau_rel ∧ GradientStability v g eps_stable
```

---

## Mathematical Foundation

### Chentsov's Theorem (Invariance Principle)
The Fisher-Rao metric is unique (up to scale) among Riemannian metrics that are invariant under sufficient-statistic coarse-grainings. Therefore:

> **SGC criteria should be scale-free to be intrinsic geometry.**

### Why Absolute Thresholds Fail
At high softmax confidence:
- ALL Fisher eigenvalues shrink (this is mathematically correct)
- Absolute threshold τ_stiff → all eigenvalues < τ → k = 0
- "Structure dissolution" is actually a measurement artifact

### Why Relative Thresholds Work
- `λᵢ > τ_rel × λ_max` is invariant under F → αF
- Preserves relative geometry (gaps, spectrum shape)
- Defines stiffness as "top fraction of spectrum"

---

## Files Modified

| File | Changes |
|------|---------|
| `demos/sgc_grokking_phase1.py` | Scale-free metrics, tau_rel, normalized logging |
| `src/SGC/InformationGeometry/RenormalizationDynamics.lean` | FisherSpectralCriterionRel, DefectGatedConsolidationCriterionRel |

---

## New Experiment Protocol

### Parameters
```bash
python demos/sgc_grokking_phase1.py \
  --tau_rel 0.1 \      # Relative threshold (10% of max eigenvalue)
  --eps_rel 0.1 \      # Cosine stability threshold
  --epochs 15000 \
  --sgc_interval 100
```

### Success Criteria (Phase-1c)
1. **Normalized spectrum becomes structured** (gap emerges)
2. **ConflictRatio drops** when S is defined spectrally
3. **k remains non-trivial** (not forced to 0 by scaling)
4. **RigidityNormalized** shows meaningful transition

---

## Verification

- [x] Python syntax check: PASSED
- [x] Lean build: PASSED (2276 jobs, 0 errors)
- [x] Scale-invariance: Documented in axiom

---

## Next Steps

1. **Run Experiment:** Execute grokking experiment with Phase-1c metrics
2. **Analyze Results:** Look for scale-free phase transition signatures
3. **Theory Validation:** Confirm normalized spectrum gaps align with grokking
4. **Document Findings:** Update investigation report with new results

---

*Phase-1c: Making SGC geometry intrinsic (Fisher-Rao invariant)*
