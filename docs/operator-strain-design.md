# OperatorStrain (discrete) — design note (2026-08-09)

NS Table of Targets, goal 1, discrete-first: the exact discrete analogue of
the operator-strain bridge `Ric_BE(νΔ + u·∇) = νRic − S_u` (flat space:
`= −S_u`). Derived by computer algebra BEFORE formalization (scripts
`scripts/derivations/derive_operator_strain.py`, `verify_strain_identity.py`,
`confirm_linear_witness.py`); every Lean theorem below formalizes a
CAS-verified identity (residual 0), so the proofs are `ring`-level.

## The derived identity (the discrete Bochner-with-strain formula)

For the weighted line (`SGC.Bridge.CurvatureUndecidability` conventions,
symmetric edge weights `q`, edge `{x, x+1}` has rate `q x`), with
`D(y) = f(y−1) − 2f(y) + f(y+1)`:

```
Γ₂(f)(x) = q(x−1)q(x−2)/4 · D(x−1)²        ← discrete ν²‖Hess f‖²
         + q(x−1)q(x)/2   · D(x)²
         + q(x)q(x+1)/4   · D(x+1)²
         + q(x−1)/4 · strainL(x) · (f(x)−f(x−1))²   ← discrete −S_u(∇f,∇f)
         + q(x)/4   · strainR(x) · (f(x+1)−f(x))²
strainL(x) = 4q(x−1) − 3q(x) − q(x−2)
strainR(x) = 4q(x) − 3q(x−1) − q(x+1)
```

Unconditional (no hypotheses on `q`). The strain coefficients are the
deviation of the rate field from local flatness; constant `q` ⇒ both vanish
⇒ pure sum of squares ⇒ `CD(0,∞)` (recovers `cd0_unitW` at `q ≡ 1`).

## The drift half (uniform drift is strain-free)

For the asymmetric constant-rate generator
`(Lf)(x) = P(f(x+1)−f(x)) + M(f(x−1)−f(x))` (drift `b = P − M`, viscosity
`ν = (P+M)/2`), CAS gives the pure sum of squares
`Γ₂ = M²/4·D(x−1)² + MP/2·D(x)² + P²/4·D(x+1)²`: the discrete "constant
vector field on flat space has `S_u = 0`". `CD(0,∞)` for every uniformly
drifted line, any `P, M ≥ 0`.

## The discovery: the linear witness and the strain dipole

For the single strained edge `q(T) = 1 + s`, all else `1`:

* `Γ₂(id)(T−1) = −s/4 < 0` for **every** `s > 0` — the identity function
  `f(x) = x` is a universal witness; any strain, however small, breaks
  `CD(0,∞)`. (The rate-4 gadget of `CurvatureUndecidability` is the `s = 3`
  point of this family; its margin was never needed.)
* Total strain `σ(x) := q(x−1)strainL(x) + q(x)strainR(x) = 4·Γ₂(id)(x)`
  forms a dipole: `σ = (−s, s(4s+1), s(4s+1), −s)` at `x = T−1, T, T+1, T+2`,
  zero elsewhere; `Σσ = 8s² = 4Σ_edges(∇q)² ≥ 0`. Compression at the flanks,
  extension at the core, net stretching positive — the discrete precursor of
  "incompressible strain is trace-free, so nonzero strain forces a negative
  direction somewhere", which is exactly the continuum reviewer's point that
  negative operator curvature is *generic* in smooth flows (the cold-water
  guardrail, now visible discretely).

## Deliverable

Module `SGC.Geometry.OperatorStrain`:
1. `gam2_strain_eq` — the identity (unconditional, `ring`).
2. `gam2_nonneg_of_zero_strain`, `cd0_const` — zero strain ⇒ flat.
3. `gamOp/gam2Op` generic Γ-calculus + `driftline_bochner`, `cd0_driftline` —
   uniform drift is strain-free.
4. `gam2_linear_eq_totalStrain`, `not_cd0_heavyW` (any `s > 0`),
   `heavyW_dipole_sum` — the linear witness and the dipole sum rule.

## NOT claimed

* No continuum statement; the `Ric_BE = −S_u` correspondence is prose.
* No dependency on `CantorHalting` (algebraically independent, per review).
* Variable-drift (`p(x), m(x)` both varying) strain identity: deferred —
  the CAS pipeline is in place, but the decomposition convention needs a
  design pass (the symmetric-`q` and constant-`P,M` cases scoped here are
  canonical; the mixed case has gauge freedom).
* The continuum cold-water theorem (decaying shear) remains a continuum
  target; the dipole result is its discrete precursor only.
