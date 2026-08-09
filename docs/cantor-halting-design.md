# CantorHalting bridge — design note (2026-08-09)

Goal: the three-register correspondence — **halting fuel = cylinder depth =
curvature-defect location** — as kernel theorems, composing the three modules
published today/this summer: `HaltingCompiler` (marker), `PadicPathSpace`
(truncation), `CurvatureUndecidability` (Γ₂ stencil). Timeboxed composition
sprint per external review 2026-08-09; hard stop at three theorems + one
corollary.

## Index convention (explicit, per guardrail 1)

`multistep (step M) (init w) n` is the configuration after `n` successful
steps; fuel `0` is the initial configuration, always live.
`haltMarkerNat M w T = true` iff the run is live at fuel `T` and the `none`
transition occurs between fuel `T` and `T+1` — i.e. the machine completes
exactly `T` steps. `haltNow` halts at `T = 0`.

Consequently "halts at exactly `T`" is decided by coordinate `T` of the
marker path, hence by `truncate (T+1)` and no shallower truncation:
coordinate `T` exists in `Fin (T+1)` and not in `Fin n` for `n ≤ T`.

## Non-halting case (per guardrail 2)

No total horizon object is introduced. All three-register statements are
conditional on the explicit hypothesis `HaltsAt M w T`
(`:= haltMarkerNat M w T = true`). The never-halting comparison object is
`neverHaltPath := const 0`; the concrete never-halting machine `spinRight`
realizes it (`markerPath_spinRight`). If a total horizon is ever wanted it
will be `Option ℕ`-valued — deferred, out of scope here.

## Deliverable (hard stop)

1. `markerPath M w : PathSpace (Fin 2)` — the halting history as a Cantor
   point (`1` at coordinate `n` iff the machine halts at exactly `n`), plus
   `haltsAt_iff_truncate`: `HaltsAt M w T ↔`
   `truncate (Fin 2) (T+1) (markerPath M w) ⟨T, _⟩ = 1`. The event is a
   depth-`(T+1)` cylinder observable, with the exact bound in the statement.
2. `truncate_markerPath_eq_of_le` (resolution blindness): if `HaltsAt M w T`
   and `n ≤ T` then `truncate n (markerPath M w) = truncate n neverHaltPath`;
   and `truncate_markerPath_ne_at_horizon`: at depth `T+1` they separate.
   So `T+1` is the *exact* separation depth.
3. `gam2_local_eq` / `gam2_nonneg_of_unit_stencil` (localized flatness): the
   discrete Bochner identity at `x` **derived from the stencil**: `Γ₂(f)(x)`
   inspects exactly the four edge rates `q(x−2), q(x−1), q(x), q(x+1)` (same
   support as the proved `gam2_heavy_eq`); if those four are `1`, `Γ₂(f)(x)`
   is the sum of three squares, hence `≥ 0`. No "2-ball" prose — the exact
   inspected edges appear as hypotheses.

Corollary `resolution_horizon` (the only place the registers meet, under the
explicit halting hypothesis): if `HaltsAt M w T` then (i) the event is read
off coordinate `T` at depth `T+1`; (ii) truncations at depth `≤ T` equal the
never-halt truncations; (iii) `Γ₂ ≥ 0` pointwise for the compiled generator
at every site `x` with `{x−2, x−1, x, x+1} ∌ (T : ℤ)` — the defect support is
exactly the stencil of the single heavy edge `{T, T+1}`.

## Explicitly NOT claimed (recorded as open, not scoped)

- **ε(n) activation law**: "the lumpability defect of a halting-decorated
  shift kernel transitions 0 → ε > 0 at n = T". Requires constructing the
  decorated kernel and computing its defect; conjectural design project.
- **Strain-projection slogan**: "finite-generator strain is the geometric
  projection of high-dimensional symbolic drift". North star, supplies no
  lemmas; `SGC.Geometry.OperatorStrain` must not cite this module as a
  mathematical dependency.
- Emergence/grokking interpretation: vault material (`insights/`), not Lean.

## Audit standard

All theorems close over exactly `[propext, Classical.choice, Quot.sound]`;
headliners join `scripts/AxiomAudit.lean` on success.
