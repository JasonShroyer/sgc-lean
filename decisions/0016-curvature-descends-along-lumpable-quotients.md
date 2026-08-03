---
method: Curvature Descent under Exact Lumpability (CD(rho,inf) is inherited fine -> coarse)
status: VALIDATED
domain: spectral
replaces: []
replaced_by: []
evidence:
  - src/SGC/Renormalization/CurvatureQuotient.lean
  - src/SGC/Renormalization/Lumpability.lean
  - "vault: experiments/be_curvature/lumpability_curvature.py"
  - "vault: insights/bakry-emery-halting-synthesis.md (section 11)"
date: 2026-08-02
---
## Verdict

Bakry-Émery curvature bounds **descend along exactly lumpable quotients**: if `L` is
strongly lumpable w.r.t. `P` and satisfies `CD(rho, inf)`, then `QuotientGeneratorSimple
L P` satisfies `CD(rho, inf)` with the **same** rho. The whole Gamma-calculus intertwines,
because lifting is multiplicative (`lift f * lift g = lift (f*g)`, by `rfl`) on top of the
generator intertwining `L_lift_eq` already in the repo. The implication is **one-way**:
renormalization can only ever *improve* curvature.

## When to use / When NOT to use

**Use** when you need a curvature bound on a coarse-grained model and you already have
one upstairs — it is free, no defect terms, same constant. Also use the contrapositive
`not_RicciCurvatureBound_of_quotient` as a **sound one-sided certificate for curvature
violation**: if the coarse model fails `CD(rho,inf)`, the fine model failed it too. That
is cheap to check because the quotient is small.

**Do NOT** use it in the direction usually wanted: a curvature bound on the quotient says
**nothing** about the fine chain. Coarse-graining is useless for curvature *verification*.

**Do NOT** assume this covers approximate lumpability. `IsRowSumApproxLumpable` with
`eps > 0` is NOT covered — the Gamma-calculus picks up defect terms there and it is open.
That is the physically relevant "wobbly chair" case and the natural next target.

## Why (SGC)

`Gamma` and `Gamma2` are built from nothing but the generator and *pointwise products* of
observables. Lifting `f |-> f o quot_map` is a ring homomorphism on observables and, under
strong lumpability, intertwines the generators. Hence

    Gamma_L(lift f, lift g)  = lift(Gamma_M(f,g))
    Gamma2_L(lift f, lift g) = lift(Gamma2_M(f,g))

Every observable downstairs is a lift and every coarse state is `[x]` for some `x`, so
testing the fine `CD` condition against lifted observables yields the coarse one verbatim.

This settles the item the Solaris Deep Research foraging run isolated as *Contested* and
load-bearing: *"whether discrete Bakry-Émery [...] curvature bounds are preserved under
lumpability or quotient operations [...] remains an unresolved, open research question."*
For the exact case it is not open, and the proof was already 95% present in
`Lumpability.lean`.

Read together with `Bridge/CurvatureUndecidability.lean` (deciding a global bound is
Pi-0-1-complete), this is the transfer that the commission's H2 wanted, arriving by a
different route than proposed: hardness lives downstairs and *lifts*, rather than
curvature and spectral gaps being interchangeable (they are not — see decision 0015).

It is also the second instance of a pattern, not an isolated fact: the same one-way
asymmetry is already proved for `KillingDefect` in `Bridge/ExoticPairs.lean` (fine
irreversibility can hide beneath a coarse equilibrium, never the reverse).

## Evidence

- 8 theorems, all `[propext, Classical.choice, Quot.sound]` — pure kernel base, zero SGC
  axioms, zero `sorry`, and notably **not** depending on `BakryEmery_implies_stability`
  (the one axiom in `GeometricClosure`). Root build green at **3280 jobs**. Audit:
  `scratch/CurvQuotientAxioms.lean`.
- Verified numerically BEFORE it was proved, which is why it was trusted:
  *"max |Gamma_L(lift f)(x) - Gamma_M(f)([x])| = 1.421e-14"* and
  *"max |Gamma_2L(lift f)(x) - Gamma_2M(f)([x])| = 8.527e-14"* over 5600 comparisons —
  `experiments/be_curvature/lumpability_curvature.py`.
- *"18 exactly lumpable pairs tested, 0 violations of 'min kappa is non-decreasing under
  lumping'"* — same script. Includes `Q_d -> Ehrenfest` holding `+2` for d = 2..5,
  `K_6 -> 2 blocks` going `+4 -> +6`, `C_8 -> C_8/rot2` going `0 -> +4`,
  `prism C_5xK_2 -> C_5` holding `0`, `P_9 -> folded` holding `0`.
- Converse NOT established: for the 6-leaf broom, collapsing the leaf orbit leaves
  `min kappa = -2.432730` unchanged (the negatively curved vertex is a singleton block),
  so no "hiding" example was found. Status of the converse: OPEN.

## Canonical implementation

- `src/SGC/Renormalization/CurvatureQuotient.lean` — `RicciCurvatureBound_quotient`
  (headline), `Gamma_lift_eq`, `Gamma2_lift_eq`, `not_RicciCurvatureBound_of_quotient`
- `experiments/be_curvature/lumpability_curvature.py` — the numerical check (vault)
