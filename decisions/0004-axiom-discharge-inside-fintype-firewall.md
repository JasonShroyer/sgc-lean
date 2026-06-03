---
method: lean-axiom-discharge-inside-fintype-firewall
status: VALIDATED
domain: lean-formalization
evidence:
  - "reports/AXIOM_SORRY_LANDSCAPE_2026-05-25.md (233 axioms / 64 sorries; cluster analysis)"
  - "DISCHARGED: src/SGC/Thermodynamics/FluxDecomposition.lean:505,611,664 (now theorems)"
  - "OPEN: src/SGC/Thermodynamics/EntropyProduction.lean:677 (gaspard_path_space_identity, still axiom)"
  - "OPEN: src/SGC/Symbiosis.lean:396 (mitosis_reduces_structural_free_energy, still axiom)"
date: 2026-06-01
---

# Discharge SGC axioms that reduce to finite-dimensional L2(pi) linear algebra; defer those needing continuum / path-space infrastructure

## Verdict
VALIDATED (NUANCED). An SGC axiom is tractably dischargeable when its statement lives
inside the `[Fintype V]` firewall -- i.e. it reduces to a finite-dimensional fact about
operators on `(V -> R)` under the `L2(pi)` inner product. It stays a long-lived axiom when
it requires infrastructure the library does not yet have (path-space measures, continuum
limits, Lifshitz critical-dimension formalism).

## When to use vs NOT
- USE to triage the axiom/sorry backlog: attempt firewall-internal targets first; they are
  the steep part of the curve (cheap, high-yield, sound verifier).
- NOT for continuum-pass axioms yet -- the audit predicts proof-theoretic strength jumps
  (WKL0 -> ATR0) once `[Fintype V]` is removed; those are research-front, not backlog.

## Why (SGC)
The verifier here is the Lean kernel: a target is "admitted" iff `lake build` succeeds with
no new `axiom`/`sorry`. This is the CORE admission gate made **sound by construction** --
no LLM judge, no permissive-gate failure mode. It is the cleanest instantiation of the
`epsilon < 0.15` closure gate: a discharged proof has *zero* defect.

## Evidence
- **Discharged (tau+):** `normal_of_self_adjoint` (`FluxDecomposition.lean:611`),
  `pi_adjoint_inner` (`:505`), `sector_condition_companion` (`:664`) -- all now `theorem`,
  closed in Sprint 1 per the landscape report. Each is a self-adjointness / inner-product
  identity on `(V -> R)` with `[Fintype V]`: firewall-internal.
- **Still axiom (tau-/open):** `gaspard_path_space_identity` (`EntropyProduction.lean:677`,
  needs path-space measure infrastructure, multi-sprint) and
  `mitosis_reduces_structural_free_energy` (`Symbiosis.lean:396`, needs Lifshitz
  critical-dimension formalism). Both are firewall-external.
- **Backlog shape:** 233 axioms / 64 sorries; densest *tractable* sorry cluster is
  `InformationGeometry/FisherNoetherBridge.lean` (12) -- the audit's recommended Priority 2.

## Canonical implementation
Pick a firewall-internal target (start with the `FisherNoetherBridge.lean` sorries or a
finite-dim spectral fact). Attempt the proof; `lake build` is the gate. On success => `tau+`
EDL entry; on failure => `tau-` entry naming the missing lemma. Either way the attempt is
high-quality rollout memory for CORE reflection.
