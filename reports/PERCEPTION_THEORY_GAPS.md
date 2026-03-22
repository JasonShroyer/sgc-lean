# Perception Theory: What We Know and What's Missing

## Established Theory

### 1. Translation Symmetry (WORKS)
- **Detection**: FFT autocorrelation finds tile periods
- **Theory**: The gauge group is Z_p × Z_q (discrete translations)
- **Result**: 100% accuracy on task 0dfd9992

### 2. Gauge Obstruction (UNDERSTOOD)
From GAUGE_OBSTRUCTION_DIAGNOSTIC.md:
- The task manifold has non-trivial holonomy (c₁ ≠ 0)
- No global predicate library can exist
- Must use local charts with transition functions

### 3. Chart Structure (PARTIAL)
- Tasks cluster by transformation signature
- Within a chart, operations transfer
- Different charts have different gauge structures

## Missing Theory

### 1. Object Decomposition
**Question**: How do we decompose a shape into "body" and "protrusions"?

**Candidate theories**:
- Scale-space (Gaussian pyramid): protrusions = high-frequency components
- Persistent homology: protrusions = features with short persistence
- Medial axis: protrusions = branches from the skeleton
- Information theory: protrusions = high-surprise regions

**Gap**: No principled way to choose between these or derive from SGC.

### 2. Level Selection
**Question**: At what level of abstraction does the gauge structure become simple?

For task 0dfd9992: Pixel level works (translation is simple at pixel level)
For task 1b60fb0c: Need object level (reflection of "protrusions")

**Candidate theory**: Renormalization group flow
- Coarse-grain until dynamics simplifies
- The "right" level is where the effective action has few terms

**Gap**: No algorithm to find this level automatically.

### 3. Gauge Group Identification
**Question**: Given input and output, what is the gauge group G?

**Known**: G is the largest subgroup where σ(g·x) = g·σ(x)

**Gap**: This definition requires checking all g ∈ Aut(fiber), which is exponential.

## Path Forward

### Option A: Lean Formalization
Formalize the perception layer in Lean 4:
- Define what "protrusion" means mathematically
- Prove properties (uniqueness, computability)
- Derive algorithm from proof

### Option B: Physics Analogy
Find physics systems with analogous structure:
- Spontaneous symmetry breaking (restoration)
- Defect dynamics in crystals
- Phase transitions and order parameters

### Option C: Learn the Geometry
As suggested in GAUGE_OBSTRUCTION_DIAGNOSTIC.md:
- Learn transition functions from task pairs
- Learn the connection A from cross-task correspondences
- Use learned geometry to guide perception

## Honest Assessment

For task 1b60fb0c specifically, I cannot derive the solution from pure theory.
The transformation involves object-level structure that I don't know how to
characterize without empirical analysis.

The theory tells me WHAT to look for (the level where gauge structure is simple)
but not HOW to find it automatically.
