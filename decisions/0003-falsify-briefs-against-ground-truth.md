---
method: falsify-design-briefs-against-ground-truth
status: VALIDATED
domain: research-methodology
evidence:
  - "sgc-second-brain git 2b68652 (CORE x SGC Phase 1)"
  - "ThermodynamicNeuron / theta*=(3 lambda sigma^2)^(1/4): 0 hits across 92 src/*.lean + vault"
  - "src/SGC/Evolution/Conservation.lean:163 (safe_surgery_preserves_blanket, verified)"
  - "reports/AXIOM_SORRY_LANDSCAPE_2026-05-25.md (real audit; 'v0.6.0 audit' = 0 hits)"
date: 2026-06-01
---

# Falsify every design-brief claim against the Lean/code ground truth before integrating it

## Verdict
VALIDATED. When an external brief (human or LLM) proposes a construct, theorem, or
formula, grep the actual `src/` tree and the compiled vault for it *before* building on
it. Admit only what survives. This is the single highest-value behaviour the second-brain
enables, and it caught real fabrications twice.

## When to use vs NOT
- USE before adopting any named theorem, axiom, formula, experiment, or capability claim
  from a brief, paper summary, or assistant.
- NOT a blocking gate on routine work; it is a fast verification reflex, not sign-off.

## Why (SGC)
This *is* the CORE admission gate applied to claims. The brief is a candidate rollout
`tau-`; the verified library is the successful prior `tau+`; a claim is admitted only if
it provably matches ground truth (`a_hat > b_q`). Mapped to
`safe_surgery_preserves_blanket` (`Evolution/Conservation.lean:163`): admitting an
unverified claim is *unsafe surgery* on the institutional memory's Markov blanket -- it
lets a fabrication leak in and corrupt downstream work.

## Evidence
- **Brief A (CORE design):** claimed a `ThermodynamicNeuron` with admission threshold
  `theta* = (3 lambda sigma^2)^(1/4)`. Grep across 92 `src/SGC/**/*.lean` + the vault =>
  **0 hits**. REJECTED and excluded. The *verified* mapping (the `epsilon < 0.15` closure
  gate via `trajectory_closure_bound` + `safe_surgery_preserves_blanket`) was admitted and
  is strictly stronger. Shipped as `sgc-second-brain` git `2b68652`.
- **Brief B (Phase 2):** claimed a "Lean v0.6.0 audit" (**0 hits**; the real artifact is
  `reports/AXIOM_SORRY_LANDSCAPE_2026-05-25.md`) and "Phase 6 grokking experiments" (no
  such labelled phase). BUT its three named axioms were verified **real**:
  `Duhamel_integral_bound`, `Weyl_inequality_pi`, `HeatKernel_opNorm_bound` are genuine
  `axiom` decls in `Renormalization/Approximate.lean`. Mixed brief: corrected, not discarded.

## Canonical implementation
`Get-ChildItem src -Recurse -Filter *.lean | Select-String -SimpleMatch '<Name>'` (+ check
the vault). Treat the brief as `tau-`, the library as `tau+`. If 0 hits: reject or
downgrade to OPEN; never carry the claim forward as fact.
