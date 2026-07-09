# 0014 — Schnakenberg Basis: realizability of affinity charges

**Date**: 2026-07-08 · **Status**: kernel-verified, committed on `cantor-layer-wip` (9bf60ae)
**Module**: `src/SGC/Bridge/SchnakenbergBasis.lean` (audit §16)
**Predecessors**: 0012 (Exotic Pairs), 0013 (Affinity Protection) — this is the converse of 0013.

## Decision

Prove the **realizability converse** of Phase E: the affinity charge data is not
just a conserved obstruction but a *free parameter* — every antisymmetric charge
assignment on the fundamental cycles of a star tree is realized by an explicit,
honest CTMC generator. Phases E + F together classify: **affinity data is
conserved (E) and free (F) — the exact parameter space of the NESS landscape.**

## The linearization insight (the "Ah-Ha")

Artemis's blueprint proposed handle-style surgeries per chord. That works for
log-affinities but our Phase E charge `Q = ∏L₊ − ∏L₋` is *polynomial* —
surgeries generically give CUBIC charge equations (`(a+δ)³ − a³`).

**Resolution**: pin every star-tree edge to symmetric rate `1`. The fundamental
triangle `v₀ → x → y → v₀` then has charge

```
Q = 1·L(x,y)·1 − 1·L(y,x)·1 = q x y − q y x
```

— **exactly linear in the chord rates**. Each triangle contains exactly one
chord, so the equations decouple completely: the chord matrix IS the charge
data. Gauge-theoretic reading (framing, not formalized): the star gauge
trivializes the tree-part of the connection; the polynomial Wilson loop
abelianizes — the discrete shadow of conjugating into a maximal torus. This is
the Polettini–Esposito gauge picture of stochastic thermodynamics made
type-theoretically effective.

## What was proved (all `[propext, Classical.choice, Quot.sound]`, zero SGC axioms)

| Theorem | Content |
|---|---|
| `divergenceHom`, `antisymmetricSubmodule`, `cycleSpace` | the cycle space as a genuine `Submodule ℝ (V → V → ℝ)` = antisymmetric ⊓ ker(divergence) |
| `mem_cycleSpace_iff` | submodule membership ⟺ Prop-level `InCycleSpace` of `DiscreteFluidDynamics` — the vocabularies agree |
| `edgeCurrent`, `divergence_edgeCurrent` | elementary edge currents: source `+1`, target `−1` |
| `triCurrent_mem_cycleSpace` | triangle currents are 1-cycles (divergences telescope) |
| `chordGenerator_row_sum_zero` | the chord generator is conservative |
| `chordGenerator_offdiag_nonneg` | honest CTMC rates when the chord data is nonnegative |
| `chordGenerator_affinityCharge` | **the linearization**: fundamental-cycle charge = `q x y − q y x` |
| `schnakenberg_realizability` | **HEADLINE**: every antisymmetric `A` is realized exactly, with nonnegative rates, via positive-part chords `q = max(A, 0)` (case split gives `A⁺xy − A⁺yx = A x y` exactly) |
| `killingDefect_pos_of_chord_asym` | one asymmetric chord ⇒ `K > 0` for every positive measure (Phase E kernel applied) |

## Honest scoping

- **Claimed**: cycle-space submodule structure, triangle currents as 1-cycles,
  exact realizability with honest rates, protection corollary.
- **Deferred to F2, NOT claimed**: linear independence of the triangle currents
  and the dimension count `dim = (n−1)(n−2)/2` (graph genus / first Betti
  number of the complete graph). Independence needs an unordered-pair index
  (ordered pairs give `triCurrent v₀ x y = −triCurrent v₀ y x`); spanning is
  the heavy half (rank-nullity over submodules of function spaces).
- **Framing only, in docstrings**: Polettini–Esposito gauge dictionary;
  hypertoric Hitchin fibration / Kirchhoff-polynomial fiber volumes
  (Hausel–Proudfoot, Groechenig–McBreen) as the north-star for C2
  (Langlands–Schnakenberg duality). No such claim is formalized.

## Queued follow-ups

1. **F2**: independence + dimension of `cycleSpace` (needs `[LinearOrder V]` or
   `Sym2` indexing for one-triangle-per-unordered-pair).
2. `fiberCycle_stationary` + explicit positive-current cycle (0012 follow-up, open).
3. 5090 experiment: charge-conserving annealing; `chordGenerator` now provides
   the natural move set — vary `q` symmetrically (charge-preserving) vs
   antisymmetrically (charge-changing) and watch `KillingDefect`.
