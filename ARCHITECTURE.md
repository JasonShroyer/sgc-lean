# SGC Architecture & Design Decisions

This document explains the architectural choices in the SGC library, particularly those
that may appear unconventional to experienced Lean/Mathlib developers.

## Executive Summary

SGC is a **verified physics paper**, not a general-purpose mathematics library. Design
decisions prioritize:

1. **Verifiability** of specific theorems from the physics literature
2. **Readability** for physicists reviewing the proofs
3. **Flexibility** for operations that transform the measure (coarse-graining)

---

## The Explicit Weight Pattern

### What It Is

Throughout SGC, geometry is parameterized by an explicit weight function `pi_dist : V → ℝ`
rather than using Mathlib's `InnerProductSpace` typeclass:

```lean
def inner_pi (pi_dist : V → ℝ) (u v : V → ℝ) : ℝ :=
  ∑ x, pi_dist x * u x * v x
```

### Why Not Use `InnerProductSpace`?

**The weight changes.** In renormalization theory, coarse-graining transforms the stationary
distribution from `π` to `π̄`. A typical proof in `Lumpability.lean` needs:

```lean
-- Original space with weight π
inner_pi pi_dist (lift_fun P f) (lift_fun P g)
-- Coarse-grained space with weight π̄  
inner_pi (pi_bar P pi_dist) f g
```

Using typeclasses would require:
1. Wrapper types `WeightedSpace π` and `WeightedSpace π̄`
2. Coercion machinery between them
3. Localized instances for each weight

The explicit pattern avoids this complexity while remaining mathematically rigorous.

### Connection to Mathlib

We **do** establish the connection to Mathlib's infrastructure. See `SGC.Axioms.Geometry`:

```lean
-- Isometry to standard Euclidean space
def iso_L2_to_std (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) : 
    (V → ℝ) ≃ₗ[ℝ] (V → ℝ)

-- The key isometry lemma
lemma norm_pi_eq_euclidean_norm (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) (f : V → ℝ) :
    norm_pi pi_dist f = ‖(WithLp.equiv 2 (V → ℝ)).symm (iso_L2_to_std pi_dist h_pos f)‖
```

This proves that our explicit `norm_pi` is isometric to Mathlib's `EuclideanSpace` norm.
The operator norm bounds use Mathlib's `ContinuousLinearMap.le_opNorm` via this isometry.

### Trade-off Acknowledged

Yes, we re-prove `cauchy_schwarz_pi` and bilinearity lemmas. This is approximately 100 lines
of straightforward algebra. In exchange, we gain:

- Direct control over weight transformations
- Proofs that mirror physics paper notation
- No typeclass resolution overhead in complex theorems

---

## Proof Structure Philosophy

### "Monolithic" Proofs

The main theorem `spectral_stability_bound` is ~370 lines. This is intentional:

1. **Physics Paper Structure**: The proof mirrors how the result appears in publications,
   with clearly labeled steps (Step 1-8) and section headers.

2. **Logical Flow**: Breaking into many small lemmas fragments the narrative. A reviewer
   can follow the proof top-to-bottom as they would a paper appendix.

3. **Named Intermediates**: Key results are bound to descriptive names:
   ```lean
   have h_sector := sector_envelope_bound_canonical ...
   have h_diag_bound := sum_abs_diag_le_card_opNorm ...
   have h_LK_opNorm : opNorm_pi ... ≤ L_opNorm * Real.exp ... := by ...
   ```

### Lemmatization Strategy

Reusable building blocks **are** extracted:
- `HeatKernel_preserves_one` (stationarity)
- `sector_envelope_bound_canonical` (spectral decay)
- `sum_abs_diag_le_card_opNorm` (diagonal bound)

Domain-specific assembly logic stays inline for readability.

---

## Naming Conventions

### `constant_vec_one` vs `fun _ => 1`

Both appear in the codebase. `constant_vec_one` is used in theorem statements for clarity:

```lean
-- Clear physics meaning: "L kills constants"
(hL1 : L *ᵥ constant_vec_one = 0)
```

Inside proofs, `fun _ => 1` is used when it arises from computation.

**Note**: These are definitionally equal: `constant_vec_one = fun _ => 1`.

### Variable Naming

- `pi_dist` — Stationary distribution (physics: π)
- `hπ` — Positivity hypothesis
- `h_sum` — Normalization hypothesis (∑ π = 1)
- `L`, `H` — Generator and its symmetric part

We avoid single-letter Greek (`μ`, `π`) to prevent Unicode issues and maintain grep-ability.

---

## Scope Decisions

### Finite State Spaces (`[Fintype V]`)

SGC restricts to finite state spaces. This is deliberate:

1. **Avoids Measure Theory**: Continuous state spaces require Lebesgue integration,
   conditional expectations via Radon-Nikodym, etc. This adds 1000+ lines of boilerplate
   that obscures the physics.

2. **Computational Content**: Finite sums are computable. The library can (in principle)
   be extracted to executable code.

3. **Sufficient for the Paper**: The physics results being verified concern finite
   Markov chains and their coarse-grainings.

### Extension Path

The `Bridge.Discretization` module defines an axiomatic interface for continuum limits.
This allows the finite-state theorems to be *instantiated* for continuous systems once
the convergence axioms are discharged.

---

## Two-Tier Architecture

See `VERIFIED_CORE_MANIFEST.md` for details. In brief:

| Layer | Status | Content |
|-------|--------|---------|
| **Verified Core** | ✅ Zero sorries | Spectral gaps, Doob-Meyer, Lumpability, variational principles |
| **Axiomatic Bridge** | ⚠️ Axiomatized | `manifold_hypothesis`, `spectral_convergence_axiom` |

The axioms represent deep analytic results (Belkin-Niyogi convergence) that would require
substantial measure-theoretic infrastructure to prove. They are clearly documented with
literature references and proof sketches.

---

## Summary for Reviewers

If you're coming from Mathlib development:

1. **The explicit weights are intentional** — not ignorance of typeclasses
2. **The proof structure follows physics conventions** — not poor factoring
3. **The finite restriction is a feature** — not a limitation
4. **The axioms are honest** — not hidden sorries

The goal is a **verified physics paper**, readable by physicists, checkable by machines.

---

*Last updated: January 2026*
