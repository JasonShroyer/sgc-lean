# SGC TensorBoard Metrics Guide

## Overview

This document explains each metric tracked in TensorBoard for the SGC Grokking experiment and describes the expected **Signature of Emergence** (grokking phase transition).

---

## Metric Categories

### 1. Performance Metrics

| Metric | TensorBoard Path | Formula | Interpretation |
|--------|------------------|---------|----------------|
| **Train Accuracy** | `Performance/TrainAcc` | % correct on training set | Memorization progress |
| **Test Accuracy** | `Performance/TestAcc` | % correct on held-out test set | **Generalization** - the key outcome |
| **Train Loss** | `Performance/TrainLoss` | Cross-entropy loss | Optimization progress |
| **Generalization Gap** | `Performance/GeneralizationGap` | `TrainAcc - TestAcc` | Overfitting measure; should **collapse** at grokking |

---

### 2. SGC Core Metrics (Theory-Testing)

These are the primary metrics aligned with the Lean formalization in `RenormalizationDynamics.lean`.

#### ConflictRatio
**TensorBoard:** `SGC/ConflictRatio`

**Formula:**
$$C(S, g) = \frac{\|P_S g\|^2}{\|g\|^2}$$

**Lean Definition:**
```lean
noncomputable def ConflictRatio (S : ConsolidatedSubspace n k) (g : Fin n → ℝ) : ℝ :=
  let proj_sq := ∑ i : Fin k, (S.SubspaceMatrix.mulVec g i)^2
  let g_sq := ∑ i : Fin n, (g i)^2
  if g_sq = 0 then 0 else proj_sq / g_sq
```

**Interpretation:**
- Measures how much the current gradient **conflicts** with the consolidated subspace
- **High C**: Gradient is trying to update directions already "locked in" → instability
- **Low C**: Gradient is orthogonal to learned structure → stable learning
- **At grokking**: Should **DROP sharply** as the network finds a generalizing solution

---

#### FisherRigidity
**TensorBoard:** `SGC/FisherRigidity`

**Formula:**
$$R(S) = \text{Tr}(P_S \cdot F \cdot P_S) = \sum_{i \in S} \lambda_i$$

**Lean Definition:**
```lean
noncomputable def FisherRigidity (state : ComputationalState n k) : ℝ :=
  let S_mat := SubspaceMatrix state.S
  let F_proj := S_mat.transpose.mul (state.F.mul S_mat)
  Matrix.trace F_proj
```

**Interpretation:**
- Total **information content** of the consolidated subspace
- Sum of Fisher eigenvalues for directions in S
- **High R**: Consolidated subspace captures important parameter sensitivities
- **At grokking**: Should **RISE** as the network consolidates meaningful structure

---

#### ConsolidatedDim (k)
**TensorBoard:** `SGC/ConsolidatedDim`

**Formula:**
$$k = \dim(S) = |\{v : \text{Stiff}(v) \land \text{Stable}(v)\}|$$

**Interpretation:**
- Number of directions passing the **DefectGatedConsolidationCriterion**
- Represents the "effective dimension" of learned structure
- **At grokking**: Should **CHANGE** (often reorganize) at the phase transition

---

#### VariationalObjective
**TensorBoard:** `SGC/VariationalObjective`

**Formula:**
$$V = R(S) - \lambda \cdot k$$

**Interpretation:**
- Rigidity minus complexity penalty
- The theoretical objective that should be **maximized** by good solutions
- Balances information content against model complexity
- **At grokking**: Should **INCREASE** as the network finds efficient representations

---

### 3. Defect-Gated Consolidation Diagnostics

These metrics break down the consolidation criterion.

#### NumStiff
**TensorBoard:** `Consolidation/NumStiff`

**Formula:**
$$\text{NumStiff} = |\{v : \lambda_v > \tau_{\text{stiff}}\}|$$

**Interpretation:**
- Directions with high Fisher eigenvalue (high curvature/information)
- These directions are "important" to the model's predictions
- High NumStiff + Low NumConsolidated → many directions are still being updated

---

#### NumStable
**TensorBoard:** `Consolidation/NumStable`

**Formula (Cosine Stability):**
$$\text{NumStable} = \left|\left\{v : \frac{|v \cdot g|}{\|v\|\|g\|} < \epsilon_{\text{rel}}\right\}\right|$$

**Interpretation:**
- Directions where the gradient is nearly orthogonal (not being updated)
- High stability = the network has "settled" in that direction
- Low stability = active learning/updating in that direction

---

#### StiffAndStable (= ConsolidatedDim)
**TensorBoard:** `Consolidation/StiffAndStable`

**Interpretation:**
- The **intersection**: directions that are both important AND settled
- This is the core of DefectGatedConsolidationCriterion
- Prevents "hallucination lock-in" by only consolidating stable knowledge

---

### 4. Spectral Diagnostics

#### MaxEigenvalue
**TensorBoard:** `Spectral/MaxEigenvalue`

**Interpretation:**
- Largest Fisher eigenvalue (λ₁)
- Indicates the "sharpest" direction in parameter space
- Useful for calibrating `tau_stiff` threshold

---

#### GradientNorm
**TensorBoard:** `Spectral/GradientNorm`

**Formula:** $\|g\|$

**Interpretation:**
- Magnitude of mean gradient
- Tracks overall learning signal strength
- Should decrease as training converges

---

### 5. Derived Metrics (Phase Transition Detection)

#### RigidityPerDim
**TensorBoard:** `Derived/RigidityPerDim`

**Formula:**
$$\text{RigidityPerDim} = \frac{R}{k} = \frac{\text{FisherRigidity}}{\text{ConsolidatedDim}}$$

**Interpretation:**
- Average information per consolidated direction
- **At grokking**: Should **SPIKE** as the network finds high-quality directions

---

#### ConflictRigidityRatio
**TensorBoard:** `Derived/ConflictRigidityRatio`

**Formula:**
$$\text{CRR} = \frac{C}{R} = \frac{\text{ConflictRatio}}{\text{FisherRigidity}}$$

**Interpretation:**
- Ratio of "conflict" to "rigidity"
- **Before grokking**: High (lots of conflict relative to structure)
- **At grokking**: Should **INVERT/DROP** dramatically

---

## The Signature of Emergence (Grokking)

### What to Look For in TensorBoard

The SGC theory predicts a **Triple Crossing Signature** at the grokking phase transition:

```
                    MEMORIZATION           |    GROKKING      |    GENERALIZATION
                         PHASE             |   TRANSITION     |        PHASE
                                           |                  |
Test Accuracy     ________________________|_______/‾‾‾‾‾‾‾‾‾‾|‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
                         ~0%               |     JUMP         |       ~100%
                                           |                  |
Conflict Ratio    ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾|\_________________|________________
                       HIGH                |     DROP         |        LOW
                                           |                  |
Fisher Rigidity   ________________________|_____/‾‾‾‾‾‾‾‾‾‾‾‾|‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
                       LOW                 |     RISE         |        HIGH
                                           |                  |
Consolidated Dim  ~~~~~~~~~~~~~~~~~~~~~~~~|~~~~~/\/\/\~~~~~~~|~~~~~~~~~~~~~~~~
                     FLUCTUATING           |   REORGANIZE     |      STABLE
```

### Detailed Predictions

| Phase | Test Acc | Conflict (C) | Rigidity (R) | Dim (k) | Interpretation |
|-------|----------|--------------|--------------|---------|----------------|
| **Memorization** | ~0-5% | HIGH (0.1-0.5) | LOW | Variable | Model memorizing, no structure |
| **Transition** | JUMP | DROP | RISE | CHANGE | Phase transition / emergence |
| **Generalization** | ~100% | LOW (<0.05) | HIGH | Stable | Structured solution found |

### Key Signatures to Watch

1. **Generalization Gap Collapse**
   - `Performance/GeneralizationGap` drops from ~100% to ~0%
   - This IS grokking

2. **Conflict-Rigidity Inversion**
   - `SGC/ConflictRatio` drops while `SGC/FisherRigidity` rises
   - The "crossing" of these curves marks the transition

3. **RigidityPerDim Spike**
   - `Derived/RigidityPerDim` should spike at transition
   - Indicates discovery of high-quality representations

4. **Consolidation Reorganization**
   - `SGC/ConsolidatedDim` may fluctuate then stabilize
   - Or show a discrete jump at transition

---

## TensorBoard Layout Recommendation

For optimal monitoring, create a custom TensorBoard layout with these groupings:

### Panel 1: Performance (Watch for grokking)
- `Performance/TestAcc` (primary indicator)
- `Performance/TrainAcc`
- `Performance/GeneralizationGap`

### Panel 2: SGC Core (Theory validation)
- `SGC/ConflictRatio`
- `SGC/FisherRigidity`
- `SGC/ConsolidatedDim`

### Panel 3: Phase Transition Indicators
- `Derived/RigidityPerDim`
- `Derived/ConflictRigidityRatio`
- `SGC/VariationalObjective`

### Panel 4: Diagnostics
- `Spectral/MaxEigenvalue`
- `Spectral/GradientNorm`
- `Consolidation/NumStiff`
- `Consolidation/NumStable`

---

## Falsification Criteria

The SGC theory would be **falsified** if:

1. **Grokking occurs WITHOUT Conflict drop** - Theory predicts C must decrease
2. **Grokking occurs WITHOUT Rigidity rise** - Theory predicts R must increase
3. **Conflict and Rigidity move in the same direction** at transition
4. **ConsolidatedDim is constant** through the entire process (no reorganization)

---

## Running the Experiment

```bash
# Recommended settings for observing grokking
python demos/sgc_grokking_phase1.py \
  --epochs 15000 \
  --lr 3e-4 \
  --train_fraction 0.3 \
  --sgc_interval 50 \
  --tau_stiff 0.001 \
  --p 97

# Launch TensorBoard
tensorboard --logdir logs/grokking --port 6006
```

---

*Document generated for SGC Phase 1 Grokking Experiment*
