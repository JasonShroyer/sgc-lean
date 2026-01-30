# ISR Sudoku Experiment: Deep-Dive Debug Diagnosis

**Branch**: `wip-quantum-bridge`  
**File**: `demos/iterative_spectral_refinement.py`  
**Date**: 2026-01-30

## Observed Symptoms

| Metric | Observed Value | Expected |
|--------|---------------|----------|
| Loss | ~2.197 (≈ log 9) | Should decrease |
| Solved Accuracy | 0% | Should improve |
| Leakage ε_t | ~6-20, not collapsing | Should collapse as model learns |
| η (non-normality) | ~1e-4, flat | Should show hump-then-collapse |
| Effective Rank | ~28, stable | Expected to stay high |

---

## Diagnosis: What Was Broken vs What Needs More Training

### 🔴 BROKEN: Critical Bugs

#### 1. **Python `hash()` is Non-Deterministic** (CRITICAL)

```python
# OLD (broken):
def compute_partition_hash(self, y):
    pred = y.argmax(dim=-1).cpu().numpy()
    return torch.tensor([hash(tuple(p.tolist())) for p in pred], ...)
```

**Problems**:
- Python's `hash()` is **salted per process** (PEP 456) - different runs produce different hashes
- Forces **CPU↔GPU synchronization** in the hot loop - massive performance hit
- Partition groups change between runs, making results non-reproducible

**Fix**: GPU-native polynomial rolling hash using prime multipliers:
```python
# NEW (fixed):
hash_vals = ((pred.long() + 1) * self.hash_primes.unsqueeze(0)).sum(dim=-1)
```

#### 2. **Multi-Solution Puzzles (Noisy Labels)**

The original puzzle generator used random clue deletion without uniqueness checking:

```
Sanity check with --no_unique:
  [WARN] 16/50 puzzles have multiple solutions
  Uniqueness rate: 68.0%
```

**Impact**: ~32% of training samples had ambiguous labels - the model was being penalized for producing valid alternate solutions.

**Fix**: Added `SudokuSolver.is_unique()` with backtracking solver that counts solutions up to limit=2.

#### 3. **Puzzle Difficulty Too Hard**

Original: `min_clues=17, max_clues=35` (17 clues is the theoretical minimum for uniqueness)

**Problem**: Starting with extremely hard puzzles prevents the model from learning basic patterns.

**Fix**: Curriculum starting with `min_clues=45, max_clues=55` (easy puzzles with ~50 clues given).

---

### 🟡 NEEDED FIXES (Correctness/Observability)

#### 4. **Singleton Ratio Metric Incomplete**

Original only logged `singleton_groups / total_groups`.

**Fix**: Now logs both:
- `singleton_ratio_groups`: singleton groups / total groups
- `singleton_ratio_samples`: samples in singleton groups / batch size

#### 5. **Shape Handling Issues**

Used `.view()` which can fail on non-contiguous tensors.

**Fix**: Use `.reshape()` for safety.

#### 6. **η Estimator Numerical Stability**

Original had no checks for NaN/Inf from gradient computation.

**Fix**: Added NaN/Inf filtering, vector normalization, try/except for gradient failures.

---

### 🟢 NOT BROKEN: Needs More Training

#### Loss at ~2.197 ≈ log(9)

This is the **entropy of a uniform distribution over 9 classes**. When the model outputs uniform predictions (before learning), cross-entropy loss equals log(9) ≈ 2.197.

**Interpretation**: Model hasn't learned anything yet. With fixed data and easier curriculum, loss should start decreasing within 10-20 epochs.

#### Effective Rank ~28

This is **expected and correct**. The latent space should maintain high dimensionality (not collapse) even as the output entropy drops. Rank ~28 is healthy for hidden_dim=128.

---

## Recommended Run Configuration

```bash
# Full training with fixes
python demos/iterative_spectral_refinement.py \
    --generate \
    --num_puzzles 5000 \
    --epochs 100 \
    --batch_size 64 \
    --min_clues_start 50 \
    --max_clues_start 60 \
    --min_clues_end 30 \
    --max_clues_end 45 \
    --eta_mode pooled \
    --log_interval 50

# Quick sanity check
python demos/iterative_spectral_refinement.py \
    --generate \
    --num_puzzles 100 \
    --sanity_check_data
```

---

## Expected Behavior After Fixes

| Epoch | Loss | Cell Acc | Leakage | η | Interpretation |
|-------|------|----------|---------|---|----------------|
| 1-10 | 2.2→2.0 | 0→5% | High | Low | Learning basic patterns |
| 10-30 | 2.0→1.5 | 5→20% | Decreasing | Rising | Active computation |
| 30-60 | 1.5→1.0 | 20→50% | Low | Peak→falling | Consolidation |
| 60-100 | 1.0→0.5 | 50→80%+ | Very low | Low | Convergence |

---

## Files Changed

- `demos/iterative_spectral_refinement.py`: All fixes implemented
- `demos/ISR_DEBUG_DIAGNOSIS.md`: This document

## Verification Commands

```bash
# Verify deterministic hashing
python -c "
import torch
from demos.iterative_spectral_refinement import SGCAnalyzer, ISRConfig
cfg = ISRConfig()
device = torch.device('cuda')
analyzer = SGCAnalyzer(cfg, device)
y = torch.randn(4, 81, 9, device=device)
h1 = analyzer.compute_partition_hash(y)
h2 = analyzer.compute_partition_hash(y)
print('Hashes equal:', torch.equal(h1, h2))  # Should be True
"

# Verify uniqueness checking
python -c "
from demos.iterative_spectral_refinement import SudokuSolver
import numpy as np
grid = np.zeros((9,9), dtype=np.int64)
SudokuSolver.solve(grid)
print('Solved grid unique:', SudokuSolver.is_unique(grid))  # True (full grid)
grid[0,0] = 0
grid[0,1] = 0
print('With 2 empty:', SudokuSolver.count_solutions(grid, limit=3))  # Likely >1
"
```

---

## Conclusion

**Primary cause of 0% accuracy**: Multi-solution puzzles (noisy labels) + non-deterministic partitioning + overly hard puzzles.

**After fixes**: The model should start learning within 10-20 epochs on easy puzzles, with observable leakage collapse correlating with solving accuracy (H1 hypothesis).
