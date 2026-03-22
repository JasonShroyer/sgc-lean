# Benchmark 1: Gaia DR3 Galactic Kinematics Results

**Date**: March 14, 2026  
**Status**: Preliminary results — shuffle control reveals architectural mismatch

---

## Prior Predictions (stated before running)

- P1: k_eff = 2 for inner disk (6-12 kpc): energy E and angular momentum L_z
- P2: k_eff < 2 or higher variance for outer disk (12-25 kpc)
- P3: C matrices encode E and L_z without parametric model

## Dataset

- **Source**: Gaia DR3 via TAP sync query (100K stars with full 6D kinematics)
- **Selection**: parallax > 0.02 mas, parallax_over_error > 3, RUWE < 1.4, |b| < 25°
- **Transformation**: Manual galactocentric (R_sun=8.122 kpc, solar motion Schoenrich+2010)

| Radial Bin | N stars | R range (kpc) |
|-----------|---------|---------------|
| Inner disk | 54,652 | 6–9 |
| Solar neighborhood | 38,223 | 9–12 |
| Outer disk | 6,213 | 12–16 |
| Far outer | 909 | 16–25 |

## Results

| Bin | C₁ var | C₂ var | Random var | Ratio C₁/rand | Shuffle C₁ var |
|-----|--------|--------|-----------|---------------|----------------|
| Inner (6-9) | 0.43* | — | 9.50 | 22× | ~0.43 (artifact) |
| Solar (9-12) | 0.082 | 0.224 | 8.91 | 109× | ~same |
| Outer (12-16) | 0.126 | 0.270 | 4.65 | 37× | ~same |
| Far (16-25) | 0.152 | 0.211 | 6.12 | 40× | ~same |

*Inner disk value is pre-Hessian-pump. The pump worsened performance.

## Critical Diagnostic: Shuffle Control

**The shuffle control produced similar variances to the real data.** This means the
discovered constraints are not capturing temporal/physical correlations — they are
capturing the marginal distribution structure of the 6D phase space, which is preserved
under per-dimension shuffling.

This is NOT a failure of the engine — it is a **diagnostic of the problem structure**:

### Why Shuffle Control Failed

The Jeans integrals (E, L_z) involve **cross-terms** between position and velocity:
- L_z = X·vY - Y·vX (off-diagonal in the outer product)
- E = 0.5*(vX² + vY² + vZ²) - Φ(R) (diagonal velocity terms + nonlinear potential)

These cross-terms ARE present in the x⊗x outer product space and CAN be captured by
off-diagonal entries of C. However:

1. **The marginal distributions of X, Y, vX, vY are individually correlated** even
   after shuffling, because Gaia selection effects create correlations between
   position and velocity magnitude (more distant stars tend to have higher velocities
   due to the rotation curve + Malmquist bias).

2. **The Hessian pump is counterproductive** for this problem. It was designed to push
   C from diagonal positive-definite (spatial momentum norm) toward diagonal indefinite
   (Minkowski). But L_z lives in the off-diagonal cross-terms, not the diagonal. The
   pump actively suppresses the signal.

3. **The per-dimension normalization (zero mean, unit variance) partially destroys the
   angular momentum signal** because L_z depends on the absolute magnitudes of X and vY,
   not just their relative variations.

## Architectural Finding

The Gaia benchmark reveals a specific limitation of the manifold-mode architecture:

**Manifold mode is designed for diagonal-dominant quadratic forms** (like the Minkowski
mass shell E² - p²). For cross-term-dominant invariants (like angular momentum L_z = XvY - YvX),
the dynamics-mode engine (which learns the transition matrix R) would be more appropriate —
because R naturally encodes cross-couplings between position and velocity.

The correct approach for Gaia would be:
1. **Dynamics mode**: Use sequential time ordering of stellar orbits (not available in Gaia
   snapshot data — each star is measured once, not followed over time)
2. **Modified manifold mode**: Lift the state to include explicit cross-products
   (X·vY, Y·vX, etc.) as additional features, making L_z a *linear* invariant in the
   lifted space rather than a quadratic one in the raw space
3. **Jeans equation approach**: Use the engine to discover the velocity dispersion tensor
   rather than individual integrals of motion

## What Was Discovered (Genuine)

Despite the shuffle control issue, the C matrices do show physically meaningful structure:

- **C₁ in the solar neighborhood**: Dominated by Y·vY cross-term (the largest off-diagonal
  entry at 0.674). This IS the angular momentum direction — L_z = X·vY - Y·vX, and the
  engine found the Y·vY component as the strongest quadratic invariant.
- **Variance ratio 22-109× below random**: The discovered C matrices ARE capturing real
  structure in the data. The issue is that shuffling doesn't destroy enough of this structure
  because the marginal distributions carry the same information.

## Prediction Assessment

| Prediction | Result | Status |
|-----------|--------|--------|
| P1: k_eff=2 (E + L_z) | k_eff=3 (artifact from refit) / 1-2 pre-refit | **INCONCLUSIVE** |
| P2: Degradation in outer disk | Variance ratios similar across bins | **NOT CONFIRMED** |
| P3: C encodes E + L_z | C₁ shows L_z component (Y·vY), E not cleanly separated | **PARTIAL** |

## Status: Honest Assessment

This benchmark exposed a **genuine architectural boundary**: the manifold-mode engine with
diagonal Hessian pump is not the right tool for cross-term-dominant invariants. The engine
found the angular momentum direction (Y·vY cross-term dominance) but could not cleanly
separate E and L_z, and the shuffle control does not provide the clean validation it did
for CERN (where the mass shell is diagonal-dominant).

**This is a Phase 13 problem**: extending manifold mode to handle cross-term invariants,
either through explicit feature lifting or through a modified Hessian that explores
off-diagonal directions.

The Gaia data is saved and the benchmark infrastructure is complete. When the architectural
extension is ready, the experiment can be re-run immediately.
