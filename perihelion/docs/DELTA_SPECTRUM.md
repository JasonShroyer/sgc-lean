# The Four-Region δ Spectrum

**Date:** March 29, 2026  
**Status:** Theoretical clarification from Sprint 6 results

---

## The Core Insight

Sprint 6 revealed that "deterministic" does not imply δ≈0. What implies δ≈0 is **definitional transitivity** — where the transitive closure is guaranteed by the logical structure of the relation itself, independent of any empirical observation.

The simple pendulum PRECEDES relation (1-step successor) returned δ=0.18, not δ=0.05. This is correct: the relation is empirically causal, not logically mathematical. You cannot skip intermediate steps in a periodic orbit, so many valid (A,B,C) chains have no observed (A,C) direct transition.

---

## The Four Regions

| Region | δ Range | Defining Property | Inference Horizon |
|--------|---------|-------------------|-------------------|
| **Mathematical** | 0.000 exact | Transitivity by definition | Unlimited |
| **Physical Law** | 0.01–0.10 | Transitivity by physical law | Very long (100+ steps) |
| **Causal** | 0.15–0.35 | Transitivity in principle, exceptions in practice | 3–8 steps |
| **Social** | 0.40–0.70 | Weak transitivity, cycles common | 1–2 steps |

---

## Mathematical (δ = 0.000)

**Criterion:** Transitivity is guaranteed by the definition of the relation, independent of what the world does.

**Examples:**
- Logical implication: if A⇒B and B⇒C, then A⇒C by modus ponens
- Set containment: if A⊂B and B⊂C, then A⊂C by definition
- Theorem dependency: if A is used in proof of B, and B in proof of C, then A is transitively required for C
- Mathematical inequality: if A<B and B<C, then A<C

**Key property:** No data can falsify transitivity. The relation is closed under composition by construction.

**Measured:** δ = 0.0000 exact (Sprint 6C, theorem dependency)

---

## Physical Law (δ ≈ 0.01–0.10)

**Criterion:** Transitivity is guaranteed by a physical law that holds without exception in the domain under study.

**Examples:**
- Energy conservation in an ideal system: E(t₁)=E(t₂) and E(t₂)=E(t₃) implies E(t₁)=E(t₃)
- Full state-to-state map in deterministic ODE (not 1-step PRECEDES, but the complete state)
- Relativistic causality: if A is in B's past light cone, and B in C's, then A is in C's

**Why not exactly 0:** Measurement noise, discretization, or numerical approximation introduces rare violations. The underlying law is exact, but the measurement is not.

**Expected:** δ ∈ [0.01, 0.10] depending on measurement precision

---

## Causal (δ ≈ 0.15–0.35)

**Criterion:** The relation is transitive in principle but admits exceptions due to noise, multiple causation, context-dependence, or narrow relation definitions.

**Examples:**
- PRECEDES (1-step successor): Transitivity requires skipping steps, which may not be observed
- CAUSES in natural language: "Smoking causes cancer, cancer causes death" — but smoking doesn't always cause death
- ENABLES: A enables B enables C — but A may not directly enable C without B

**Why higher δ:** The relation definition excludes some valid transitive completions, or the world genuinely has exceptions to the transitive rule.

**Measured:** δ = 0.18 (Sprint 6B, simple pendulum PRECEDES)  
**Prior benchmark:** δ = 0.20 (hand-curated causal triplets)

---

## Social (δ ≈ 0.40–0.70)

**Criterion:** The relation is weakly transitive or actively anti-transitive (cycles are common).

**Examples:**
- PREDICTS in chaos: Long-range prediction fails by Lyapunov instability
- FRIENDS: A is friends with B, B with C — but A and C may be strangers or enemies
- PREFERS: Rock-paper-scissors structure, A>B>C>A
- AGREES_WITH in opinion networks: Echo chambers and polarization break global transitivity

**Why high δ:** The world genuinely contains cycles and anti-transitive structure. These are not measurement artifacts.

**Measured:** δ = 0.56 (Sprint 6A, double pendulum chaos)  
**Prior benchmark:** δ = 0.51 (hand-curated social triplets)

---

## The Inference Horizon

The δ value directly predicts how far transitive inference can reliably propagate:

- **Mathematical (δ=0):** Unlimited inference depth. A⇒B⇒C⇒...⇒Z implies A⇒Z with certainty.
- **Physical law (δ≈0.05):** ~20 steps before error compounds significantly (0.95²⁰ ≈ 0.36)
- **Causal (δ≈0.25):** ~3-4 steps before majority of chains fail (0.75⁴ ≈ 0.32)
- **Social (δ≈0.50):** ~1-2 steps only (0.50² = 0.25)

This is the **inference horizon** of the relation type. SGC theory predicts that reasoning systems should not attempt transitive inference beyond this horizon without additional evidence.

---

## Implications for SGC Architecture

1. **Relation classification determines inference strategy.** Before applying transitive closure, classify the relation and check δ.

2. **Mixed corpora require per-relation δ estimation.** A corpus containing both mathematical proofs and social opinions has internal δ variation.

3. **The critical phase (δ≈0.17) is where inference becomes unreliable.** This is the boundary between causal and social — the point where transitive inference transitions from "usually works" to "often fails."

4. **Automatic extraction must preserve relation type.** If extraction conflates mathematical and social relations, the measured δ will be meaningless.

---

## Validated Results

| Relation | Domain | Measured δ | Classification |
|----------|--------|------------|----------------|
| IMPLIES (theorem) | Formal math | 0.0000 | Mathematical |
| PRECEDES (phase) | Physics ODE | 0.1818 | Causal |
| PREDICTS (chaos) | Physics chaos | 0.5625 | Social |
| Logical implication | Semantic | 0.0000 | Mathematical |
| Causes/enables | Semantic | 0.2000 | Causal |
| Friends/prefers | Semantic | 0.5100 | Social |

The ordering **mathematical < causal < social** holds across all tested domains.
