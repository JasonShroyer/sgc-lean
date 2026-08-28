---
name: axiom-preflight
description: MANDATORY checklist before committing or trusting any `axiom` declaration in this repo — definition/range/convention/degeneracy audits, numerical witness, consumer trace, joint model. Invoke whenever adding, modifying, or relying on an axiom.
---

# Axiom Pre-Flight

Read and execute `docs/axiom-preflight.md` (the seven checks) BEFORE any
`axiom` lands in `src/`. Record the evidence in
`docs/axiom-discharge-campaign.md` first; an axiom without a pre-flight
ledger entry is a defect.

Quick form of the seven checks:
1. Definitions it references validated independently (unit/small cases).
2. Exact parameter ranges named; boundary + one outside point tested.
3. Conventions (row/column, action vs hypothesis) conserve mass/normalization.
4. Degenerate instantiations (zero measure/generator, empty/singleton type)
   are neither false nor silently vacuous.
5. Numerical witness: random + adversarial instances tested (Python, 5 min).
6. Proof-term consumer trace; certified cores stay out of its blast radius.
7. A joint model with the axiom's whole family exists (satisfiability).

History that motivates this (all caught in-repo): adjoint_pi_spec (False
derived), Bakry–Émery family (jointly unsatisfiable), Tsallis V1/V2
(definition error; range over-extension), TsallisDPI (convention
transposition, numerically falsified).
