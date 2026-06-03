---
method: weight-decay
status: NUANCED
domain: grokking
evidence:
  - reports/continual_learning_protected_crystal_report.md
  - reports/BENCHMARKS_456.md
date: 2026-05-31
---

# Weight Decay Drives Grokking

## Verdict

Weight decay is **required** for grokking â€” it drives the compression phase â€” but
*how* and *where* it is applied is decisive. Do **not** blanket-reject L1/L2
regularization; the record shows it can win.

## When to use / When NOT to use

- **USE:** weight decay on a task's *own* parameters to induce the grokking /
  compression transition.
- **DO NOT:** mix weight decay into a *projected* gradient (it overloads the loss
  term ~30x), or apply it inside a *protected null space* (it destroys the preserved
  weights of an earlier task).

## Why (SGC)

Grokking is a compression process: weight decay supplies the compressive pressure that
moves a model from memorization to the generalizing solution. Misapplied â€” in the null
space, or mixed into projection â€” it corrupts the geometry it is supposed to refine.
This is a concrete instance of the meta-principle in `0001`: the pressure must act
*with* the intrinsic dynamics, not as an externally bolted-on override.

## Evidence

- "Grokking Requires Weight Decay + Exploration" â€” `reports/continual_learning_protected_crystal_report.md` (Â§5.2)
- "Weight decay is **critical** (drives compression)" â€” same report
- "Weight decay must NOT be mixed into gradient (overloads)" â€” same report (v3b experiment)
- "**Weight decay in null space** destroys Task A's weights that happen to lie there" â€” same report
- "**L1 (symmetric) wins**: MDL = -1.64 (best)" â€” `reports/BENCHMARKS_456.md`
  (direct counter-example to any blanket "regularization is harmful" claim)

## Canonical implementation

- `reports/continual_learning_protected_crystal_report.md` â€” see the v3b (mixed,
  failed) vs. v4b (null-space weight decay, alpha=0.001) configurations.
