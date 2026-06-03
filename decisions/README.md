# Decisions — Experimental Method Ledger (EDL)

This directory is the SGC project's **living memory of what works and what doesn't**.
It exists so that writing a new accelerated-grokking script for a fresh domain becomes
an act of *remembering*, not rediscovering — and so we never backslide into methods our
own experiments already ruled out, nor wrongly abandon methods that actually win.

## Philosophy: recall, not veto

These records are **retrievable expertise**, not gates. They do not block work or
require sign-off. They make the right approach obvious from context: each validated
recipe and its SGC-grounded justification becomes part of the knowledge graph, so the
correct method surfaces naturally and the wrong one simply never gets reached for.

> The second-brain doesn't say "don't do X." It says "here is the full recipe that
> works, and the theoretical reason why."

## The one hard rule: ground every claim

Every verdict MUST cite and quote the actual experimental record — a file in
`reports/`, `RESEARCH_JOURNAL.md`, or a named experiment script. **No invented
conclusions.**

This rule exists because of a real near-miss. An external assistant confidently
recommended recording *"L1 regularization → REJECTED, destroys spectral closure."*
But this repo's own record says the opposite:

- `reports/BENCHMARKS_456.md`: *"L1 (symmetric) wins: MDL = -1.64 (best)."*
- `reports/continual_learning_protected_crystal_report.md`: *"Grokking Requires
  Weight Decay + Exploration"* and *"Weight decay is critical (drives compression)."*

A hallucinated verdict would have steered us away from a method our data shows can win
— the exact backsliding this ledger is meant to prevent. **If evidence is ambiguous,
status = OPEN and say so.**

## Entry format

Filename: `NNNN-method-slug.md` (zero-padded, increasing).

```text
---
method:                 # canonical name -> becomes the graph entity
status: OPEN            # VALIDATED | REJECTED | NUANCED | OPEN
domain:                 # grokking | continual-learning | spectral | general | ...
replaces: []            # optional cross-links
replaced_by: []
evidence: []            # source files quoted in the body
date: 2026-05-31
---
## Verdict
One sentence.

## When to use / When NOT to use

## Why (SGC)
The theoretical reason, tied to the formal theory in `src/SGC/`.

## Evidence
- "<direct quote>" — `reports/FILE.md`

## Canonical implementation
- `path/to/reference_script.py`
```

## The living loop (capture + recall)

1. **Capture** — when an experiment concludes, write or refresh the relevant entry.
   The `.windsurf/workflows/edl-capture.md` workflow walks through this.
2. **Compile** — `swarmvault ingest decisions && swarmvault compile` turns each method
   into a high-confidence node linked to the theory and prior experiments.
3. **Recall** — before implementing a method, the validated recipe is already in
   context; `swarmvault query "<method> <domain>"` when unsure.
4. **Refine** — new results reinforce or update the entry. The formal theory stays the
   anchor, so entries remain grounded in SGC rather than empirical folklore.

## Candidates still to document (ranked by presence in the record)

- `sgc_grokking_phase1_report.md`, `SGC_GROKKING_RESEARCH_REPORT.md` — the grokking recipe
- `continual_learning_protected_crystal_report.md` — protection vs. plasticity
- `LIFSHITZ_EXPERIMENT_ANALYSIS.md` — Lifshitz-transition diagnostics
- `ADAPTIVE_POLARITY_BREAKTHROUGH.md` — adaptive polarity (the v2→v10 lineage)
- `THRML_002_EXPERIMENTAL_REPORT.md` — thermodynamic bridge validation
