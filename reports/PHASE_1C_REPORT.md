# Phase-1c Validation Report: Scale-Invariant Stiffness Criterion

**Date:** 2026-02-01  
**Commit:** `243433610a8ccc0fcd9aea0bd3175bfada8681d1`  
**Branch:** `wip-quantum-bridge`

---

## 1. Objective

Validate that the relative stiffness threshold (`tau_rel * lambda_max`) prevents the consolidated dimension `k` from collapsing to zero when the absolute Fisher trace `Tr(F)` shrinks at high model confidence.

**Precise claim under test:**
> The criterion `lambda_i > tau_rel * ||F||` is invariant under positive scaling `F -> alpha*F` (scale-invariance), ensuring `k` remains interpretable even when `Tr(F) -> 0`.

**Note:** This is **scale-invariance** (invariance to global rescaling of F), **not** full Fisher-Rao invariance (which would require invariance under arbitrary reparameterizations/Markov morphisms per Chentsov's theorem).

---

## 2. Experimental Configuration

### 2.1 CLI Command
```bash
python -u demos/sgc_grokking_phase1.py \
    --tau_rel 0.01 \
    --epochs 15000 \
    --sgc_interval 100 \
    --log_dir logs/grokking/phase1c_tau001
```

### 2.2 Full Parameters
| Parameter | Value |
|-----------|-------|
| `p` (prime) | 97 |
| `hidden_dim` | 128 |
| `epochs` | 15000 |
| `lr` | 0.001 |
| `weight_decay` | 1.0 |
| `train_fraction` | 0.3 |
| `batch_size` | 512 |
| `sgc_interval` | 100 |
| `tau_rel` | 0.01 |
| `eps_rel` | 0.1 |
| `num_svd_samples` | 200 |
| `lambda_cost` | 0.01 |
| `seed` | 42 |
| `device` | cuda (RTX 5070) |

### 2.3 Log Directory
```
logs/grokking/phase1c_tau001/run_20260201_141002/
```

---

## 3. Results Summary

### 3.1 Training Outcome
- **Grokking achieved:** Epoch 11671
- **Final test accuracy:** 98.9%
- **Train accuracy:** 100% (from epoch ~500)

### 3.2 Key Metric Trajectories

| Epoch | Tr(F) | k | R_norm | Test Acc |
|-------|-------|---|--------|----------|
| 1 | 1.51 | 86 | 0.758 | 0.9% |
| 100 | 170.3 | 72 | 0.641 | 0.0% |
| 500 | 140.3 | 80 | 0.728 | 0.1% |
| 1000 | 69.5 | 74 | 0.667 | 0.2% |
| 5000 | ~0.05 | ~76 | ~0.70 | ~8% |
| 8000 | ~0.0002 | 75 | 0.650 | 78.5% |
| 9000 | 0.0000 | 78 | 0.597 | 89.8% |
| 10000 | 0.0000 | 81 | 0.784 | 94.0% |
| 11000 | 0.0000 | 77 | 0.681 | 98.4% |
| 11600 | 0.0000 | 76 | 0.596 | 98.9% |

---

## 4. Primary Finding

### 4.1 What Was Validated

**The Phase-1c prediction held:**
> "Even when `Tr(F)` shrinks to machine precision, `k` and normalized spectral metrics remain interpretable."

**Observed:**
- `Tr(F)` declined from 170.3 (peak) to 0.0000 (below float32 precision)
- `k` remained in the range **72-86 throughout** (never collapsed to 0)
- `R_norm` (normalized rigidity) stayed in range 0.55-0.78

### 4.2 What This Falsifies

The earlier "structure dissolution" observation (where `k -> 0` at high confidence) was **not** evidence that SGC structure dissolves during grokking. It was an artifact of using an **absolute** stiffness threshold (`lambda_i > tau_stiff`) which became impossible to satisfy when all eigenvalues shrank proportionally.

### 4.3 What This Does NOT Prove

- This single run does not establish that the result is robust across seeds/hyperparameters (robustness suite pending)
- This does not prove full Fisher-Rao invariance (Chentsov-style); only scale-invariance under `F -> alpha*F`
- This does not prove any universal claim about "intelligence" or "emergence" beyond the specific modular addition grokking task

---

## 5. Implementation Details

### 5.1 Python (demos/sgc_grokking_phase1.py)

**Stiffness criterion:**
```python
# Line 527
stiff_threshold = tau_rel * max_eig if max_eig > 1e-10 else 0.0
stiff_mask = eigenvalues > stiff_threshold
```

**Spectral gap (fixed):**
```python
# Lines 601-611
if num_stiff > 0 and num_stiff < k_max:
    lambda_k = eigenvalues[num_stiff - 1].item()
    lambda_k_plus_1 = eigenvalues[num_stiff].item()
    spectral_gap = lambda_k / lambda_k_plus_1 if lambda_k_plus_1 > 1e-10 else 1000.0
else:
    spectral_gap = 1.0
```

### 5.2 Lean (src/SGC/InformationGeometry/RenormalizationDynamics.lean)

**Scale-invariance axiom:**
```lean
axiom FisherOperatorNorm_smul (F : Matrix (Fin n) (Fin n) R) (alpha : R) (h_alpha : 0 < alpha) :
    FisherOperatorNorm (alpha . F) = alpha * FisherOperatorNorm F
```

**Relative criterion:**
```lean
def FisherSpectralCriterionRel (F : Matrix (Fin n) (Fin n) R) (v : Fin n -> R)
    (tau_rel : R) : Prop :=
  v != 0 && FisherRayleighQuotient F v > tau_rel * FisherOperatorNorm F
```

---

## 6. Reproducibility Checklist

- [x] Commit SHA recorded: `243433610a8ccc0fcd9aea0bd3175bfada8681d1`
- [x] Full CLI command documented
- [x] Random seed fixed: 42
- [x] TensorBoard logs preserved in `logs/grokking/phase1c_tau001/`
- [x] Python syntax verified: `python -m py_compile demos/sgc_grokking_phase1.py`
- [x] Lean build verified: `lake build SGC.InformationGeometry.RenormalizationDynamics`

---

## 7. Pending Work

### 7.1 Robustness Suite (Immediate)
| Run | tau_rel | seed | Status |
|-----|---------|------|--------|
| baseline | 0.01 | 42 | DONE |
| sweep-1 | 0.001 | 42 | PENDING |
| sweep-2 | 0.003 | 42 | PENDING |
| sweep-3 | 0.03 | 42 | PENDING |
| seed-1 | 0.01 | 123 | PENDING |
| seed-2 | 0.01 | 456 | PENDING |
| seed-3 | 0.01 | 789 | PENDING |

### 7.2 Phase-1d (Optional)
Add second Fisher proxy (Gauss-Newton / Jacobian-based) to verify that normalized spectra agree qualitatively across estimation methods.

---

## 8. Conclusion

Phase-1c validation **passed**: the scale-invariant stiffness criterion (`tau_rel * ||F||`) keeps the consolidated dimension `k` interpretable across the full training trajectory, including the high-confidence regime where `Tr(F) -> 0`.

This resolves the "structure dissolution" puzzle from earlier experiments and confirms that SGC metrics should use **relative geometry** (spectrum shape, normalized eigenvalues) rather than absolute Fisher magnitude.

**Next step:** Run robustness suite to strengthen the claim before broader dissemination.
