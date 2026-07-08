# 0013 — Affinity Protection: the conserved charge sealing the exotic phase

**Date**: 2026-07-07 · **Status**: kernel-verified, committed on `cantor-layer-wip` (06d7490)
**Module**: `src/SGC/Bridge/AffinityProtection.lean` (audit §15)
**Predecessor**: 0012 (Exotic Pairs) — closes its queued follow-up #1.

## Decision

Formalize the conservation law that protects the exotic member of an exotic
pair, as a *division-free, log-free* invariant: the **affinity charge**
`Q(L, c) := ∏ L(cᵢ, cᵢ₊₁) − ∏ L(cᵢ₊₁, cᵢ)` on ℕ-indexed closed walks (the cycle
vocabulary already used by `DiscreteFluidDynamics` §3). On positive rates,
`Q ≠ 0 ⟺` the Schnakenberg cycle affinity `∑ log(L₊/L₋) ≠ 0` — the holonomy of
the log-rate connection, a discrete Wilson loop. `Q` needs no positivity, no
logs, no measure — it is data of the generator alone.

## What was proved (all `[propext, Classical.choice, Quot.sound]`, zero SGC axioms)

| Theorem | Content |
|---|---|
| `cycle_measure_prod_shift` | telescoping: the measure product shifts around a closed cycle |
| `cycleProd_balance_of_detailedBalance` | **Kolmogorov obstruction**: detailed balance w.r.t. any positive π ⇒ forward = backward products on every cycle (reversibility = flat connection) |
| `affinityCharge_eq_zero_of_detailedBalance` | equilibrium is affinity-trivial |
| `killingDefect_pos_of_affinityCharge_ne_zero` | **protection kernel**: ONE charged cycle ⇒ `KillingDefect L π > 0` for EVERY positive π — positivity of the defect is measure-independent, intrinsic to the generator |
| `annealing_protection` | **conserved charge ⇒ eternal NESS**: along any generator path conserving the charge of a charged cycle, the defect stays > 0 at every time, for every positive measure |
| `exoticLift_handle_fwd` / `_bwd` | the handle's rates: `a + δ` forward, `a` backward (`a = M w₀ w₀ / 3`) |
| `exoticLift_affinityCharge_pos` | **the handle is charged for EVERY base model**: `Q = (a+δ)³ − a³ > 0` (no hypotheses on `M` — the charge is created by the surgery, not inherited) |
| `killingDefect_exoticLift_pos_universal` | **HEADLINE**: the exotic lift has `K > 0` w.r.t. every positive measure — upgrades 0012's fixed-measure statement to full measure-independence |
| `uniformLift_affinityCharge_zero` | the uniform member of the pair is affinity-trivial on every cycle |
| `affinity_separates_pair` | the exotic pair lies in **different affinity classes** |

## Why this matters

1. **It fixes the falsifiability gap of 0012.** There we proved an annealer
   preserving only the coarse face CAN always kill the defect. Now: an annealer
   preserving the affinity charge NEVER can. "Exotic-annealing" is a theorem,
   not a hope, once moves are charge-conserving. The 5090 experiment is now
   correctly scoped: anneal within a fixed affinity class.
2. **Measure-independence completes the exotic-ℝ⁴ analogy.** Smooth-structure
   invariants do not depend on a choice of Riemannian metric; our defect
   positivity now does not depend on a choice of stationary measure. The charge
   is the conserved class datum behind "homeomorphic but never diffeomorphic".
3. **The physics dictionary** (framing, in docstrings only): charge = discrete
   Wilson loop / holonomy; Kolmogorov criterion = flatness; protection =
   Noether-style conservation sealing the NESS phase. Any Langlands-flavored
   reading (holonomy classes as "automorphic" data of a correspondence) is
   explicitly labeled a north star, NOT a claim.

## Proof-engineering notes

- The charge is a *difference of products*, not a log-ratio: no positivity
  hypotheses anywhere in §1–§3, so the theorems apply to algebraic lifts
  (e.g. `uniformLift`, whose intra-fiber entries can be negative).
- The telescoping lemma is two lines: `Finset.prod_range_succ` vs
  `prod_range_succ'` + `mul_right_cancel₀`.
- The handle computation reduces to `∏ const = const³` (`Finset.prod_const`),
  and `(a+δ)³ − a³ = δ·(¾(2a+δ)² + ¼δ²) > 0` via `nlinarith`.
- `ZMod 3` arithmetic side conditions (`1 ≠ 0`, `x + 1 ≠ x`) discharge by
  `decide` / `congrArg (· − x)` + `simp`.

## Queued follow-ups

1. `fiberCycle_stationary` + explicit positive-current cycle via
   `killingDefect_pos_iff_positive_current_cycle` (0012 follow-up #2, still open).
2. Converse direction: which charge configurations are *realizable* — a discrete
   Schnakenberg affinity basis (cycle space dimension = |E| − |V| + 1).
3. The 5090 experiment: charge-conserving annealing moves on `W × ZMod 3`.
