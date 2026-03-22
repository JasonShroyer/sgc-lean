# Sudoku SGC Iteration Summary: v3 → v5

## Executive Summary

Starting from v2's 62.7% plateau, we explored three architectural variations guided by first-principles reasoning from the SGC formalization. The breakthrough came from shifting from "solve all at once" (NP-hard spin glass) to "iterative collapse" (renormalization), achieving **85.0% accuracy** — a **+22.3% improvement**.

---

## Version Progression

| Version | Key Change | Best Accuracy | Outcome |
|---------|-----------|---------------|---------|
| v2 (baseline) | Reactive repulsion | 62.7% | Plateau (glassy state) |
| v3 | Hard Sphere + Langevin | 55-58% | **Worse** (Void Trap) |
| v4 | Entropy Stabilizer | 38% | **Worse** (Attraction lock) |
| **v5** | **Iterative Collapse** | **85.0%** | **+22.3% improvement** |

---

## Key Discoveries

### 1. The "Void Trap" (v3)

**Change:** Replaced reactive repulsion with unconditional "Hard Sphere" repulsion.

**Theory:** Push stalks apart regardless of overlap to escape glassy state.

**Result:** Accuracy dropped to 55-58%.

**Diagnosis:** Hard Sphere pushed stalks into the **orthogonal complement** of the Code Subspace — the "Void" where stalks are "maximally different from neighbor" but not valid digits. From `SGC.Bridge.Quantum`: we implemented H_interaction but omitted H_stabilizer.

### 2. The "Entropy-Polarity Paradox" (v4)

**Change:** Added entropy stabilizer to pull stalks toward valid digits (simplex vertices).

**Theory:** H = H_interaction + H_stabilizer. Entropy penalty creates "gravity" around valid digits.

**Result:** Accuracy dropped to 38%, polarity went to g ≈ 0.97 (attraction instead of repulsion).

**Diagnosis:** The entropy stabilizer operated **independently** of constraints. It forced all cells to sharpen to the **same** digit (easiest path to low entropy = consensus). This created a "False Vacuum" at the Consensus State.

**Key Insight:** 
- ∂E_total/∂g = E_attr - E_repl
- When cells predict same digit: E_attr ≈ 0, E_repl ≈ 1 → gradient negative → g increases
- Positive feedback loop locked in attraction

### 3. The Renormalization Breakthrough (v5)

**Change:** Iterative collapse (Wavefunction Collapse) — solve one cell at a time.

**Theory:** From `SGC.Renormalization.Approximate`:
- "Solve all at once" = NP-hard spin glass problem
- "Iterative collapse" = renormalization (integrate out degrees of freedom)
- Each collapse: state space 9^N → 9^(N-1)

**Algorithm:**
1. Run diffusion to relax the field
2. Find cell with **lowest entropy** (highest confidence)
3. **Collapse** (write in pen — becomes hard clue)
4. Propagate constraints via diffusion
5. Repeat until solved or stuck

**Result:** 85.0% accuracy, 43.5 collapses per puzzle (out of ~46 unknowns).

**Why it works:**
- **Symmetry breaking:** First collapse breaks the hardest symmetry
- **Avalanche effect:** One collapse triggers chain of obvious moves
- **Sequential commitment:** Navigate solution tree, not optimize globally

---

## Theoretical Lessons

### 1. Let the System Discover, Don't Impose

Every "improvement" that imposed external knowledge (Hard Sphere, Entropy Stabilizer, Polarity Regularizer) made things worse. The system should discover constraints through interaction with the environment.

v2's reactive repulsion worked because it let the system **feel** constraint violations naturally.

### 2. The Order of Emergence Matters

```
WRONG:  Sharpen predictions → Then differentiate
RIGHT:  Differentiate (repulsion) → Then sharpen (collapse)
```

The entropy stabilizer violated the causal order. The system must first resolve conflicts, then commit.

### 3. Renormalization > Global Optimization

For constraint satisfaction problems:
- Global optimization fights against exponential state space
- Sequential commitment (renormalization) reduces complexity at each step
- This is how humans solve Sudoku

### 4. The Missing Piece from SGC Theory

The breakthrough came from recognizing that `SGC.Renormalization.Approximate` directly applies:
- Coarse-graining = collapsing cells
- Defect operator = constraint propagation
- Spectral gap increases (problem gets easier) with each collapse

---

## Current Plateau Analysis (85%)

The remaining ~15% errors likely come from:

1. **Early Mistake Propagation:** A wrong collapse locks in an error with no backtracking
2. **Confidence Miscalibration:** Collapsing on cells that aren't truly certain
3. **No Hypothesis Branching:** Single-path search can't recover from errors

---

## Files Created

- `demos/adaptive_polarity_v3.py` — Langevin + Hard Sphere (Void Trap)
- `demos/adaptive_polarity_v4.py` — Entropy Stabilizer (Attraction Lock)
- `demos/adaptive_polarity_v5.py` — **Iterative Collapse** (Breakthrough)

---

## Next Steps (Theory-Driven)

1. **Constraint Checking:** Verify collapse doesn't create immediate contradiction
2. **Uncertainty Quantification:** Better calibration of when to collapse
3. **Backtracking / Hypotheses:** Tree search with rollback on contradiction
4. **Connect to Lean Formalization:** Formalize the collapse-as-renormalization correspondence

---

*Generated: 2026-02-07*
