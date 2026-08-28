# The Axiom Pre-Flight Checklist

**Run BEFORE any `axiom` is committed or trusted — not after a stress-test
forces it.** Distilled from five caught failures: adjoint_pi_spec
(False derived), Bakry–Émery energy family (jointly unsatisfiable),
Tsallis V1 (identity on a wrong definition), Tsallis V2 (binary-case
identity over-generalized), TsallisDPI (transposed convention, numerically
falsified). The taxonomy: **definition error → range over-extension →
convention error → degenerate-parameter vacuity/falsity.**

## The seven checks

1. **DEFINITION AUDIT.** Every definition the axiom references: validate it
   independently at unit values and one hand-checkable case before trusting
   any identity built on it. *(Tsallis V1: the extropy definition itself
   was wrong.)*
2. **RANGE AUDIT.** For every parameter, name the exact domain on which the
   claim is provable; check the boundary AND one point outside it. Claim
   only the proven range — never "all n"/"all q" by syntactic reachability.
   *(Tsallis V2: true at n = 2, false at n = 3. f_q convex iff q < 2; the
   q ≈ 2.5 regime is outside — correctly.)*
3. **CONVENTION AUDIT.** Row vs column, action vs hypothesis, orientation,
   transposes: verify a conservation law (mass, normalization, symmetry)
   actually survives the stated action under the stated hypothesis.
   *(TsallisDPI: row sums hypothesized, column action taken — mass leaked.)*
4. **DEGENERACY AUDIT.** Instantiate every quantified parameter at its
   degenerate values (zero measure, zero generator, empty/singleton type,
   n = 1): does the axiom become vacuous (satisfiable but empty) or false?
   *(adjoint_pi_spec at π = (1,0): False derivable. CD(ρ,∞) at L = 0:
   vacuously true for all ρ, poisoning downstream implications.)*
5. **NUMERICAL WITNESS.** For any inequality or identity: five minutes of
   Python on random + adversarial instances before axiomatizing. This is
   the cheapest check with the highest catch rate (caught TsallisDPI).
6. **CONSUMER TRACE.** Grep proof-term consumers (not docstrings). Falsity
   of an axiom with consumers can poison certified theorems; per-theorem
   `#print axioms` certificates bound the blast radius — verify the
   candidate stays OUT of the certified core's dependency cones.
7. **JOINT MODEL.** Exhibit (at least on paper, in the ledger entry) one
   nontrivial model satisfying the new axiom TOGETHER with its family —
   axioms are trusted jointly, and pairwise-plausible families can be
   jointly unsatisfiable *(Bakry–Émery + vacuous CD at L = 0)*.

## Process

- The ledger entry (docs/axiom-discharge-campaign.md) records the evidence
  for each check BEFORE the axiom lands; an axiom without a pre-flight
  entry is a defect.
- Repairs preserve the old statement verbatim in the ledger
  (archive-not-delete applies to statements).
- Counterexamples are kept as tombstones or numerical scripts.
- The checklist itself is versioned here; new failure modes extend it.

*Meta-note: this checklist is a product of the research, not overhead on
it. The method — agentic exploration disciplined by an incorruptible
kernel, with satisfiability-first trust management — is itself one of the
project's principal artifacts.*
