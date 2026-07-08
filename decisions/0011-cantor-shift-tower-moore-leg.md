# 0011 — The Cantor Shift Tower: closing the Moore leg of the fluid-computation triangle

**Date**: 2026-07-07 · **Status**: kernel-verified, committed on `cantor-layer-wip`
**Module**: `src/SGC/Bridge/CantorShiftTower.lean` (audit §13)

## Decision

Formalize the symbolic-dynamics leg (Moore 1990/91) of the Miranda-program
fluid-computation triangle as a finite, axiom-free SGC renormalization tower,
rather than attempting continuum Reeb/Euler embeddings.

## What was proved (all `[propext, Classical.choice, Quot.sound]` or less)

| Theorem | Content |
|---|---|
| `tail_shiftIn` | tower projection ∘ machine step = machine step ∘ tower projection |
| `shiftKernel_row_sum` | the depth-n machine step is row-stochastic |
| `shiftTower_stronglyLumpable` | cylinder truncation depth n+1 → n is an EXACT coarse-graining |
| `shiftTower_quotient_realizes` | **renormalization = shift**: the quotient machine IS the machine one level down |
| `shiftTower_defect_zero` | lumpability defect ε = 0 at every depth |
| `shiftGenerator_stronglyLumpable` | generator form (K − I), conservative |
| `truncate_pathShift` | truncation semiconjugates the true `PathSpace` shift to the tower (**zero axioms** — definitional) |

## The triangle now formalized

- **Miranda/fluid leg** (`DiscreteFluidDynamics`, 2026-06): currents, h-principle
  flexibility/rigidity, viscous budget `τ∞ = 1/ν`, damped budget `1/(νε)`.
- **Cantor leg** (`PadicPathSpace`): `PathSpace (Fin p) ≃ₜ ℤ_[p]` — the substrate
  on which CMPP (PNAS 2021) encode machine states.
- **Moore leg** (this module): the shift dynamics itself, with the SGC statement
  that it is renormalization-transparent: ε = 0 ⇒ validity horizon `T* = 1/ε = ∞`.

**Insight worth remembering**: for shift systems, the RG map and the time map
coincide (`shiftTower_quotient_realizes` + `truncate_pathShift`). Symbolic
computation is the ε = 0 pole of the damped validity budget `1/(νε)` — the
"sealed crystal" phase. This is *why* Turing-completeness can survive embedding
into a flow: the symbolic layer adds no coarse-graining leakage on top of the
viscous budget; only dissipation truncates computation.

## Same-sprint context (2026-07-05, commits `565aa98`, `3188327`)

Seven axioms retired: `HeatKernel_opNorm_bound`, `Duhamel_integral_bound`,
`Horizontal_Duhamel_integral_bound` deleted (theorems with explicit constants in
`DefectHorizonBridge`); `PropagatorDiff_eq_proj_trajectory_diff`,
`HeatKernel_semigroup`, `all_ones_norm_sq_pos`, `inner_pi_orthogonal_decomp`
proved. Flagship trajectory theorems kernel-clean; `spectral_stability_reversible`
reduced to exactly `Weyl_inequality_pi`; `NCD_uniform_error_bound` to the NCD pair.

## Epistemic boundary (unchanged)

The continuum column (Reeb fields, Poincaré sections, Euler flows) is a research
dictionary, NOT formalized. No claim of Turing-completeness is made in Lean —
only the exact-lumpability structure that the continuum constructions rely on.
