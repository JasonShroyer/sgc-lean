---
trigger: always_on
---

# SGC Second-Brain: Recall & Capture (this is a recall system, NOT a gate)

The SGC second-brain (compiled vault at `c:\Users\Jason\sgc-second-brain`) is a living
memory of which methods work, which fail, and the SGC-grounded reason why. Treat it as
internalized expertise, like a senior researcher who has run all these experiments —
not as a checkpoint that pauses work.

## Recall (default behavior)
When designing or modifying experiments, training loops, optimizers, regularizers, or
when porting a method to a new domain: draw on the validated methods already captured
in `decisions/` and `reports/`. Reach for the validated recipe by default. The reason a
failed method does not reappear is that the working pattern is already complete and
well-justified — **never pause to ask permission or gate the work on this.**

## Ground every claim
Trust a recipe because of its cited evidence, not vibes. Do NOT assert that a method is
good or bad without the experimental record behind it. (A past external assistant
wrongly claimed "L1 regularization is rejected"; this repo's `reports/BENCHMARKS_456.md`
shows L1 can win, and `continual_learning_protected_crystal_report.md` shows weight
decay is *required* for grokking. Hallucinated verdicts cause backsliding.)

## Capture (keep the memory alive)
When an experiment concludes, record the outcome as a `decisions/NNNN-method-slug.md`
entry following `decisions/README.md`, grounded in the run's actual results and quotes.
Do this as part of wrapping up the experiment, not as a separate approval step.
