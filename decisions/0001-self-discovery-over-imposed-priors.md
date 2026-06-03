---
method: self-discovery-over-imposed-priors
status: VALIDATED
domain: general
replaces: [hard-sphere-penalty, entropy-stabilizer, hand-tuned-polarity-regularizer]
evidence:
  - reports/ITERATION_SUMMARY_V3_V5.md
date: 2026-05-31
---

# Self-Discovery Over Imposed Priors

## Verdict

Let the system discover structure intrinsically. Hand-imposed external priors and
regularizers have *consistently* degraded SGC dynamics across the v3â€“v5 iterations.

## When to use / When NOT to use

- **USE:** intrinsic objectives that let the geometry/spectrum emerge from the
  dynamics (the SGC default).
- **AVOID:** bolting on external "knowledge" constraints to force a behavior â€”
  hard-sphere penalties, entropy stabilizers, hand-tuned polarity regularizers.

## Why (SGC)

SGC posits that the relevant structure (spectral / geometric closure) is an *emergent*
property of the dynamics. Externally imposed constraints optimize the wrong geometry
and suppress the very emergence the theory depends on. This is a meta-principle: it
predicts *why* specific imposed regularizers (see `0002`) fail when misapplied.

## Evidence

- "Every 'improvement' that imposed external knowledge (Hard Sphere, Entropy
  Stabilizer, Polarity Regularizer) made things worse. The system should discover
  [structure itself]." â€” `reports/ITERATION_SUMMARY_V3_V5.md`

## Canonical implementation

- Lineage: `demos/adaptive_polarity_v2.py` â€¦ `demos/adaptive_polarity_v10_hybrid_bootstrap.py`
- Conclusion writeup: `reports/ADAPTIVE_POLARITY_BREAKTHROUGH.md`
