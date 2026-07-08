# 0012 — Exotic Pairs: the coarse face does not determine the fine invariant

**Date**: 2026-07-07 · **Status**: kernel-verified, committed on `cantor-layer-wip` (2b96545)
**Module**: `src/SGC/Bridge/ExoticPairs.lean` (audit §14)

## Decision

Formalize the *discrete shadow* of the exotic-ℝ⁴ phenomenon at the finite
Markov-generator layer — pairs of generators that are **coarse-isomorphic but
fine-inequivalent** — rather than attempting smooth 4-manifold topology, gauge
theory, or supersymmetric QFT in Lean (Mathlib has none of these; any direct
attempt would be vapor-ware signatures).

## What was proved (all `[propext, Classical.choice, Quot.sound]`, zero SGC axioms)

For EVERY coarse model `M` reversible w.r.t. a positive `πW`, the two fine
completions on `W × ZMod 3`:

  `L₁ = uniformLift M`   and   `L₂ = exoticLift M w₀ δ = L₁ + fiberCycle w₀ δ`   (δ > 0)

| Theorem | Content |
|---|---|
| `stronglyLumpable_add_blockNeutral` | surgery lemma: block-neutral perturbations preserve strong lumpability |
| `quotientGenerator_add_blockNeutral` | coarse blindness: block-neutral surgery leaves the quotient literally unchanged |
| `exoticLift_same_quotient` | (a) L₁, L₂ have the SAME quotient generator |
| `exoticLift_stronglyLumpable` | (b) L₂ is strongly lumpable (exact coarse-graining, ε = 0 lumpability) |
| `exoticLift_quotient_realizes` | (c) L₂ realizes the SAME coarse model `M` |
| `killingDefect_uniformLift_zero` | Sasakian leg: `KillingDefect L₁ = 0` (Chern–Hamilton criticality) |
| `killingDefect_exoticLift_pos` | **HEADLINE** Anosov/NESS leg: `KillingDefect L₂ > 0` |
| `exoticLift_coarse_current_zero` | (d) invisibility: the coarse probability current of L₂ vanishes identically |

## The dictionary (analogy, NOT formalized)

| Smooth 4D topology / QFT | Discrete (this module) |
|---|---|
| homeomorphism type (Freedman) | `QuotientGeneratorSimple` (coarse face) |
| smooth structure | the fine generator itself |
| exotic pair (std ℝ⁴, exotic ℝ⁴) | (`uniformLift M`, `exoticLift M w₀ δ`) |
| curvature invariant (Donaldson/SW) | `KillingDefect` = discrete Chern–Hamilton energy |
| exoticness invisible to topology | `exoticLift_coarse_current_zero` |

**Insight worth remembering**: the separation is *strictly one-way*. Fine NESS
(K > 0) can hide under coarse equilibrium — but by
`reversible_quotient_of_reversible` (equilibrium is hereditary downward), coarse
NESS never admits a reversible fine completion. The `KillingDefect` is strictly
finer-than-coarse data, exactly as smooth structure is strictly finer than
homeomorphism type in d = 4. And the witness is *cheap*: a single δ-weighted
3-cycle in one fiber (`fiberCycle`), the minimal "handle" — irreversibility
needs a cycle, and `ZMod 3` is the smallest fiber carrying one with all
diagonal compensation intra-block.

## Consequence for the 5090 annealing experiment (design constraint)

An annealer free to modify all rates while preserving only the coarse face CAN
always reach K = 0 — take the `uniformLift` member. So "the exotic lattice
cannot be annealed" is FALSE without a conservation law. Topological protection
of K > 0 requires a conserved fine-scale class datum; the natural candidate is
the **cycle affinity** (Kolmogorov holonomy of the log-rate connection, the
discrete Wilson loop `∑_cycle log(L_xy/L_yx)`). The experiment must therefore
anneal within a fixed affinity class, not merely a fixed coarse face.

## Queued follow-ups

1. Affinity classes (Kolmogorov holonomy) + the protection theorem: annealing
   preserving affinity classes cannot kill the defect.
2. Shared stationarity (`fiberCycle_stationary`) and the explicit
   positive-current cycle via `killingDefect_pos_iff_positive_current_cycle`.
3. The 5090 discrete exotic-annealing experiment, now correctly scoped by the
   protection constraint above.

## Epistemic honesty

No claim that SGC defects ARE smooth-structure invariants of actual
4-manifolds. The theorem is about finite Markov generators: coarse data
underdetermines fine irreversibility, with an explicit, fully constructive
witness pair. Chern–Hamilton anchor: arXiv:2311.15833 as in
`DiscreteFluidDynamics` §7.
