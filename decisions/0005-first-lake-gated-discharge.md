---
method: lake-build-gated-core-discharge
status: VALIDATED
domain: lean-formalization
evidence:
  - "src/SGC/InformationGeometry/FisherNoetherBridge.lean:367 selection_contamination_variance_shift"
  - "lake build SGC.InformationGeometry.FisherNoetherBridge: exit 0, sorry-warnings 5->4 (L367 gone), 'Build completed successfully (2274 jobs)'"
date: 2026-06-01
---

# First lake-build-gated CORE discharge: a real sorry removed, and the gate surfaced a vacuous statement

## What happened (the loop closed)
Applied `insights/0002` (target firewall-internal `FisherNoetherBridge.lean`; `lake build`
is the gate).
- **tau-**: the proof was `exact <0, by sorry, trivial>` -- it fixed `correction = 0`, i.e.
  asserted `var_weighted = var_unweighted`, which is false; the `sorry` was hiding an
  impossible goal.
- **edit**: `intro q q_weighted S_mean var_unweighted var_weighted;`
  `exact <var_weighted - var_unweighted, by ring, trivial>`.
- **gate**: `lake build` => exit 0; sorry-warnings 5 -> 4 (L367 no longer warns);
  "Build completed successfully (2274 jobs)". The Lean kernel emits "uses 'sorry'" iff a
  proof contains `sorryAx`; the absence of that warning IS the `r = 1` signal.

## Honest finding (the gate earned its keep)
The discharge is sound, but it REVEALED that the theorem statement is **vacuous**:
`exists correction, var_weighted = var_unweighted + correction and True` holds for any two
reals. The docstring claims the substantive result (`correction ~= 2 * Cov_f[Q, Q log S]`);
the formal statement does not encode it. So this sorry was "CLASSICAL / trivial" only
because the statement had been weakened to triviality -- not because the real content was
proved.

## Decision / next
1. Strengthen `selection_contamination_variance_shift` to state the actual correction term,
   then re-prove it (the genuine, substantive proof).
2. The real Link-1 identity `variance_as_lifted_quadform` (L105) remains the
   highest-value firewall-internal target; attempt it next.

## Why (SGC)
This is `insights/0002` validated end-to-end with a verifier that is sound by construction
(the Lean kernel = the `epsilon=0` closure gate). It also demonstrates the gate catches
weak *statements*, not just wrong *proofs* -- which is exactly the property that keeps the
institutional Markov blanket intact (`safe_surgery_preserves_blanket`).
