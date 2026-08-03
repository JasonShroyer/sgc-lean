---
method: Local-Invariant Undecidability (global Bakry-Émery bound is Π⁰₁-complete)
status: VALIDATED
domain: spectral
replaces: []
replaced_by: []
evidence:
  - src/SGC/Bridge/CurvatureUndecidability.lean
  - "vault: insights/bakry-emery-halting-synthesis.md"
  - "vault: experiments/be_curvature/*.py"
  - "vault: inbox/20260802_191957-deep-research-computability-and-undecidability-of-bakry-emery-curvature-fo.md"
date: 2026-08-02
---
## Verdict

Deciding a **global** Bakry-Émery curvature bound `inf_x κ(x) ≥ 0` for a computable
locally finite reversible Markov generator is **Π⁰₁-complete** — equivalent to the
complement of the halting problem — and this is *elementary*: it needs only that κ is
a **local** invariant, that uniform rates give `κ ≥ 0`, and that one rational rate
pattern gives `κ < 0`. Do **not** route this through Turing-complete fluid flows, and do
**not** expect a Lichnerowicz-type equivalence with spectral-gap undecidability.

## When to use / When NOT to use

**Use** this pattern whenever asked whether some *local* geometric invariant of a
computable infinite generator is decidable: the answer is almost certainly "Π⁰₁-complete,
and cheaply so". The recipe is: (1) find a homogeneous background where the invariant is
non-negative; (2) find one finite local pattern where it is negative; (3) place that
pattern at the halting step of a deterministic machine, where "halts in exactly `i`
steps" is a *total decidable* predicate.

**Do NOT** use the fluid/Euler/Beltrami route for hardness. It adds an unproved uniform
lower bound on `Ric + Hess φ − ½𝓛_X g` along the computational channels of a Beltrami
field, and buys nothing. **Do NOT** use "the computation stops" as the curvature gadget:
the endpoint of a ray has `κ = +3/2 > 0`. **Do NOT** claim geometric depth for this
result — see Why.

## Why (SGC)

`κ(x)` depends only on the 2-ball around `x` (`Γ` and `Γ₂` in
`SGC.Bridge.GeometricClosure` are 1- and 2-local respectively). An infimum of a local
quantity over a computable state space is therefore Π⁰₁ *by construction*, and Π⁰₁-hard
as soon as a single local certificate exists. A **spectral gap is not local**, which is
exactly why Cubitt–Perez-Garcia–Wolf needed elaborate tiling/clock gadgetry for the
quantum spectral gap while this proof is a page of algebra.

Consequence for H2 (the hoped-for Lichnerowicz transfer): it **fails**. Lichnerowicz runs
one way only (`κ ≥ K > 0 ⇒ gap ≥ K`), and in our construction *both* branches have
spectral gap 0 — the bi-infinite path has purely continuous spectrum reaching 0 and one
altered edge rate does not open a gap. So the generator's gap carries no information
about halting while its curvature carries all of it; the reduction cannot transfer.

The exact discrete Bochner identity found here is the reusable asset:

    Γ₂(f)(x) = ¼(Δ²f)(x−1)² + ½(Δ²f)(x)² + ¼(Δ²f)(x+1)²,   (Δ²f)(y) = f(y−1) − 2f(y) + f(y+1)

on the flat line — a sum of squares with **no Ricci term**, the discrete shadow of
`Γ₂ = |Hess f|² + Ric(∇f,∇f)`. It makes `Γ₂` on chain-like state spaces a sum of squares
of second differences, and lumpability acts on second differences linearly — so this is
the natural tool for the still-open question of whether `CD(0,∞)` survives
`SGC.Renormalization.QuotientGenerator`.

## Evidence

- Six theorems, all `[propext, Classical.choice, Quot.sound]` (pure kernel base, zero SGC
  axioms, zero `sorry`), root build green at 3279 jobs —
  `src/SGC/Bridge/CurvatureUndecidability.lean`, audit via
  `scratch/CurvUndecAxioms.lean`.
- Calculator validated against **seven** published anchors, including the sharp one:
  Cushing–Liu–Münch–Peyerimhoff–Stagg (*Exp. Math.* 2019, Thm 1.1) classify cubic
  `CD(0,∞)` graphs as exactly prisms and Möbius ladders — computed: prisms/ladders all
  `≥ 0`, **Petersen `= −1` exactly**. Also `K_n = n/2+1`, `Q_d = 2`, `C_{n≥5} = 0`,
  `C_4 = 2`, `ℤ = 0`.
- "the endpoint of a ray: κ = +1.500000" — `experiments/be_curvature/be_curvature.py`
  output (the naive gadget is positively curved; recorded so we never reach for it).
- "κ(leaf) = 2 − n/2" exactly, tail-independent for tails 3…40, certified by the integer
  witness `f = 2·1_leaf + 1·1_join` — `experiments/be_curvature/gadget_witness.py`.
- "most negative kappa(centre) found: −7.800663" for a rate window on a *fixed* line —
  `experiments/be_curvature/bulk_and_weights.py` (rates alone suffice; geometry need not
  change).
- Bulk certificate is published, contrary to the SDR run's "not found": *"It is well
  known that all abelian Cayley graphs satisfy the CD(0,∞) condition"* — Cushing–Liu–Münch
  §10 (doi:10.4153/cjm-2018-015-4), after Klartag–Kozma–Ralli–Tetali
  (doi:10.4153/cjm-2015-046-8). `ℤ` is the Cayley graph of `ℤ` with generators `±1`.
- Independent-source adjudication: the Gemini Deep Research PDF's reduction decides an
  **orbit-restricted** infimum from a marked point on an *input-independent* generator, so
  its `inf_x κ(x)` is negative in both branches — a different object from the target, and
  its κ can be replaced by any indicator of the halting region. Recorded in
  `insights/bakry-emery-halting-synthesis.md` §2.

## Canonical implementation

- `src/SGC/Bridge/CurvatureUndecidability.lean` — the theorem (`cd0_haltW_iff`)
- `experiments/be_curvature/be_curvature.py` — validated curvature calculator (vault)
- `experiments/be_curvature/birth_death_reduction.py` — the reduction in exact rationals
- `insights/bakry-emery-halting-synthesis.md` — full synthesis, scope limits, open questions
