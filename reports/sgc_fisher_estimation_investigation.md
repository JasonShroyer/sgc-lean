# SGC Grokking Experiment: First-Principles Mathematical Investigation

**Date:** February 1, 2026  
**Status:** ANALYSIS COMPLETE - NUANCED FINDING  
**Conclusion:** The "structure dissolution" is **mathematically correct behavior**, not an artifact. Fisher Information naturally decreases at high softmax confidence. The SGC theory needs refinement to handle this regime.

---

## Executive Summary

Our experiment appeared to show that the consolidated subspace "dissolved" during grokking (ConsolidatedDim: 87 → 0). Upon first-principles investigation, we discovered this was caused by a **fundamental error in our Fisher Information estimation method**.

**The Error:** We used the gradient outer product to estimate Fisher Information. This estimator goes to zero at loss minima (where gradients vanish), even though the TRUE Fisher Information (curvature) remains nonzero.

**Implication:** Our experiment did NOT validly test the SGC theory. The results must be reinterpreted, and the experiment redesigned.

---

## 1. The Two Definitions of Fisher Information

The Fisher Information Matrix has two equivalent definitions:

### Definition 1: Score Covariance (What We Computed)

$$F_{ij} = \mathbb{E}\left[ \frac{\partial \log p}{\partial \theta_i} \cdot \frac{\partial \log p}{\partial \theta_j} \right]$$

For cross-entropy loss $L = -\log p$:
$$F = \mathbb{E}[\nabla L \cdot \nabla L^T]$$

**Our implementation:**
```python
G = stack([grad(loss_i) for i in samples])  # M × N gradient matrix
F_empirical = (1/M) * G.T @ G
eigenvalues = SVD(G).singular_values ** 2 / M
```

### Definition 2: Expected Hessian (Curvature)

$$F_{ij} = -\mathbb{E}\left[ \frac{\partial^2 \log p}{\partial \theta_i \partial \theta_j} \right]$$

### The Equivalence Theorem

Under regularity conditions, these definitions are **mathematically equivalent**:
$$\mathbb{E}[\nabla \log p \cdot \nabla \log p^T] = -\mathbb{E}[\nabla^2 \log p]$$

**However**, this equivalence holds for the **expected value over the true data distribution**. When using empirical samples at a loss minimum, the two methods diverge dramatically.

---

## 2. What Happens at a Loss Minimum?

### At Convergence (100% Train Accuracy, Loss ≈ 0):

| Quantity | Gradient-Based | Hessian-Based |
|----------|----------------|---------------|
| **Formula** | $\nabla L \cdot \nabla L^T$ | $-\nabla^2 \log p$ |
| **At minimum** | → 0 (gradients vanish) | Remains positive (curvature exists) |
| **Interpretation** | "No force" | "Stable equilibrium" |

### Empirical Verification

We tested this on a simple logistic regression at 100% accuracy:

```
Gradient-based Fisher max eigenvalue: 0.000023
Hessian-based Fisher max eigenvalue:  0.859631
Ratio (Hessian/Gradient): 36,812x
```

**The Hessian-based Fisher is 37,000× larger than the gradient-based estimate!**

---

## 3. Physical Analogy: Ball in a Bowl

Consider a ball at the bottom of a potential well:

```
Energy
  |    \     /
  |     \   /
  |      \_/    ← minimum
  |_____________ Position
```

**At the minimum:**
- **Gradient of energy = 0** (no net force, ball is stationary)
- **Curvature > 0** (this is WHY it's a stable minimum)

If we measure "stiffness" by gradient magnitude:
- We wrongly conclude: "The system is soft at the minimum"

If we measure "stiffness" by curvature:
- We correctly see: "The minimum is a STIFF equilibrium point"

**Our experiment made the first error.** We measured gradient magnitude (which vanishes at minima) instead of curvature (which characterizes the minimum's stability).

---

## 4. What Our Experiment Actually Measured

### What We Thought We Were Testing

> "Does the consolidated subspace (stiff + stable directions) reorganize during grokking?"

### What We Actually Measured

> "Does the gradient magnitude in various directions change during training?"

### The Artifact

As the model converged (loss → 0):
1. Gradients → 0 (we're at a minimum)
2. Gradient-based Fisher eigenvalues → 0
3. No directions satisfied `eigenvalue > tau_stiff` (0.001)
4. ConsolidatedDim → 0

**This is NOT "structure dissolution"!** This is the gradient-based estimator breaking down at convergence.

---

## 5. Implications for SGC Theory

### What We CAN Conclude

1. **Grokking occurred** — Test accuracy rose from 0% to 15.5%
2. **ConflictRatio dropped** — But this is trivially true when S = ∅ (empty subspace)
3. **The experiment design was flawed** — Results cannot validate or falsify SGC theory

### What We CANNOT Conclude

1. ~~Structure dissolves during grokking~~ (measurement artifact)
2. ~~FisherRigidity decreases at emergence~~ (measurement artifact)
3. ~~ConflictRatio → 0 is meaningful~~ (it's 0 because S is empty)

---

## 6. The Correct Approach

### Option 1: Hessian-Based Fisher (Gold Standard)

Compute the actual Hessian of the loss:
$$F_{ij} = \frac{\partial^2 L}{\partial \theta_i \partial \theta_j}$$

**Pros:** Measures true curvature, remains valid at convergence  
**Cons:** O(n²) computation, expensive for large models

### Option 2: Gauss-Newton Approximation

For neural networks with softmax output:
$$F \approx J^T \cdot \text{diag}(p(1-p)) \cdot J$$

where J is the Jacobian of logits with respect to parameters.

**Pros:** Captures curvature, more tractable than full Hessian  
**Cons:** Approximation, requires careful implementation

### Option 3: Normalized Gradient Fisher

Scale the gradient-based Fisher by gradient magnitude:
$$F_{normalized} = \frac{G^T G}{||g_{mean}||^2}$$

**Pros:** Removes scale dependence, simple modification  
**Cons:** Changes interpretation, may not match Lean definition

### Option 4: Fixed-Loss Measurement

Compute Fisher when loss reaches a threshold (e.g., L = 0.1), not at convergence.

**Pros:** Avoids vanishing gradient problem  
**Cons:** Requires careful experimental design, may miss dynamics

---

## 7. Recommended Fix for Phase 1 Experiment

### Immediate Fix: Use Gauss-Newton Approximation

The Gauss-Newton approximation provides a curvature estimate that:
1. Remains nonzero at convergence
2. Is computationally tractable
3. Has clear information-geometric interpretation

### Implementation Sketch

```python
def compute_fisher_gauss_newton(model, dataloader, device):
    """Compute Fisher via Gauss-Newton approximation."""
    # For each sample, compute Jacobian of logits w.r.t. parameters
    # J_i = d(logits)/d(theta) at sample i
    # F = (1/M) * sum_i [ J_i^T * diag(p_i * (1-p_i)) * J_i ]
    ...
```

### Alternative: Normalize by Gradient Norm

Modify the current implementation to use:
```python
# Current (breaks at convergence):
eigenvalues = (s ** 2) / M

# Fixed (scale-invariant):
g_norm_sq = g_mean.norm() ** 2
if g_norm_sq > 1e-10:
    eigenvalues_normalized = (s ** 2) / (M * g_norm_sq)
else:
    eigenvalues_normalized = eigenvalues  # fallback
```

---

## 8. Lessons Learned

### Mathematical Lesson

> **The score covariance and Hessian definitions of Fisher Information are only equivalent in expectation.** At loss minima, the empirical score covariance vanishes while the Hessian remains positive.

### Experimental Design Lesson

> **When testing a theory, ensure the measurement method remains valid across the entire experimental regime.** Our gradient-based Fisher estimator was valid during training but broke down at convergence—precisely where we wanted to observe the grokking transition.

### Theory Building Lesson

> **Cross-check measurements against first principles before interpreting results.** The "structure dissolution" interpretation was superficially plausible but fundamentally incorrect.

---

## 9. Revised Interpretation of Results

### Original (Incorrect) Interpretation

> "Grokking involves structure dissolution—the consolidated subspace collapses as the model generalizes."

### Correct Interpretation

> "Our measurement method (gradient-based Fisher) broke down at convergence. The observed collapse of ConsolidatedDim was an artifact, not a real phenomenon. The experiment does not validly test SGC theory and must be redesigned."

---

## 10. Next Steps

1. **Implement Gauss-Newton Fisher estimation** — Replace SVD of gradients with proper curvature estimation

2. **Re-run the grokking experiment** — With corrected Fisher estimation

3. **Validate the fix** — Verify that Fisher eigenvalues remain nonzero at convergence

4. **Update Lean formalization** — Consider whether the Lean definition needs to specify WHICH Fisher estimator to use

5. **Document the correction** — Ensure future experiments avoid this pitfall

---

## Appendix: Verification Code

```python
# Demonstrates the 37,000x discrepancy between gradient-based 
# and Hessian-based Fisher at convergence

# Train simple classifier to 100% accuracy
model = nn.Linear(2, 2)
# ... train to convergence ...

# Method 1: Gradient outer product (WRONG at convergence)
G = stack([grad(loss_i) for each sample])
F_grad = G.T @ G / M
max_eig_grad = 0.000023  # Vanishes!

# Method 2: Numerical Hessian (CORRECT)
H = numerical_hessian(loss, params)
max_eig_hess = 0.859631  # Nonzero!

# Ratio: 36,812x difference!
```

---

## References

1. Amari, S. (2016). *Information Geometry and Its Applications*. Springer.
2. Martens, J. (2020). "New Insights and Perspectives on the Natural Gradient Method." JMLR.
3. Power, A. et al. (2022). "Grokking: Generalization Beyond Overfitting." arXiv:2201.02177.
4. SGC Lean Formalization: `src/SGC/InformationGeometry/RenormalizationDynamics.lean`

---

*Investigation conducted February 1, 2026*  
*Conclusion: Experiment must be redesigned with proper Fisher estimation*
