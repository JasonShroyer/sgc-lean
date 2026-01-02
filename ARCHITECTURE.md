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

**Note**: `constant_vec_one` is defined as `abbrev`, ensuring definitional equality with 
`fun _ => 1` is immediate for the elaborator without unfolding.

### Variable Naming

- `pi_dist` — Stationary distribution (physics: π)
- `hπ` — Positivity hypothesis
- `h_sum` — Normalization hypothesis (∑ π = 1)
- `L`, `H` — Generator and its symmetric part

**Why `pi_dist` instead of `π`?**

A reviewer suggested using Unicode `π` directly since Lean 4 supports it well. We deliberately 
chose ASCII names for:

1. **Grep-ability**: `grep -r "pi_dist"` works reliably across all terminals and editors.
   Greek letters can have encoding issues in some toolchains.

2. **Cross-platform consistency**: Windows PowerShell, Linux terminals, and macOS may render
   Unicode differently. ASCII names are universally stable.

3. **IDE compatibility**: Some older VSCode versions or alternative editors may not handle
   Greek variable names in autocomplete/refactoring as smoothly.

For a verified paper intended to be audited by diverse reviewers with varying toolchains,
ASCII robustness outweighs the aesthetic benefit of matching paper notation.

### Namespace Opens

Several modules use `open Matrix Real Finset` globally. This is acceptable for a terminal
artifact (verified paper) but would be problematic for a library meant to be imported.
If SGC is ever refactored into a general-purpose library, these opens should be scoped.

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

**Why bake `[Fintype V]` into variable declarations?**

A reviewer noted that having `[Fintype V]` in file-level variable declarations makes
generalization to infinite dimensions harder. This is intentional:

- **Infinite dimensions are explicitly out of scope.** The goal is a verified paper for
  discrete stochastic systems, not a general functional analysis library.
- **Generalization would require different proof strategies** (measure theory, 
  operator semigroups, etc.), not just removing the constraint.
- **Clear scope prevents scope creep.** Future contributors know exactly what the
  library covers without digging through proofs.

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

## Future Improvements

### Proof Transport for Foundational Lemmas

The current `cauchy_schwarz_pi` is proven from first principles using the polynomial 
discriminant method (~50 lines). A reviewer suggested using the isometry `iso_L2_to_std` 
to transport Mathlib's `abs_real_inner_le_norm` instead.

This is a valid improvement that would:
- Demonstrate tighter Mathlib integration
- Reduce maintenance burden as Mathlib evolves

**Status:** Deferred. The current proof is correct and educational. Proof transport 
requires careful handling of Mathlib's `EuclideanSpace` inner product API. This is a 
good first issue for contributors familiar with Mathlib's inner product infrastructure.

### Computability & SciLean Integration

The codebase is marked `noncomputable section` due to use of `Real`. However, the 
*structure* is entirely computable:

- `∑` over `Fintype` is just a loop
- `Matrix` operations are nested loops
- No non-constructive axioms in the core logic

**Path to Executability:**

1. **Scalar Abstraction:** Generalize from `ℝ` to a type `R` with `[Field R]`, then
   instantiate with `Float` for computation.

2. **Partition Refinement:** The `Setoid`-based `Partition` in `Lumpability.lean` is
   elegant for proofs but `Quotient` types are not VM-computable. A "computable
   refinement" using `Array Nat` for block assignments would enable execution.

3. **SciLean Integration:** The explicit weight pattern aligns well with SciLean's
   approach to scientific computing. Future work could provide a transpilation path.

**Status:** Out of scope for verified paper. Documented for future contributors 
interested in executable extraction.

### ProbabilityMeasure Structure

A reviewer suggested bundling `(pi_dist, h_pos, h_sum)` into a structure. This is now
available as `ProbabilityMeasure V` in `SGC.Axioms.Geometry`:

```lean
structure ProbabilityMeasure (V : Type*) [Fintype V] where
  mass : V → ℝ
  pos : ∀ v, 0 < mass v
  sum_one : ∑ v, mass v = 1
```

**Usage:** New code should prefer `μ : ProbabilityMeasure V`. Existing code retains
the unbundled form for compatibility. Gradual migration is encouraged.

---

## Research Directions (AGI/Robotics Applications)

The following extensions would bridge the "verified physics paper" to practical 
Object-Centered AI and robotics applications:

### Approximate Lumpability ("Wobbly Chair" Theorem)

**Status:** ✅ Implemented (`IsApproximatelyLumpable`, `approximate_gap_leakage_bound`)

Real-world symmetries are never exact. A "chair" has scratches; atoms vibrate.
`IsApproximatelyLumpable L P ε` captures that coarse-graining works even when 
partition symmetries hold only up to tolerance ε.

The axiomatized leakage bound (`SpectralGap_bar ≥ SpectralGap - C * ε`) validates
that macroscopic models remain stable under sensor noise. Full proof requires
Rayleigh quotient perturbation theory (Stewart & Sun, Kato).

### Dynamic State Spaces ("Cat Injection")

**Status:** 🔬 Research Direction

The current Doob-Meyer decomposition assumes static `[Fintype V]`. In robotics,
an agent encounters novelty—the state space expands from V to V ∪ {cat}.

**Challenge:** Formalizing thermodynamic extension when the domain changes:
- How does the martingale increment M_n behave under domain expansion?
- Formalize the "surprise shock": S(new_state) = -log(π(new_state)) where π → 0

This is the mathematical foundation for "Phone a Friend" triggers in active inference.

### Compositionality (Systems Engineering)

**Status:** 🔬 Research Direction

Current library analyzes monolithic matrices L. Real systems are composed:
"I know how an airfoil works, I know how a jet engine works... I can invent an airplane."

**Goal:** Tensor product or disjoint union for spectral objects:
- Define composite generator L_{A⊗B} from subsystems
- Prove **Spectral Additivity**: `SpectralGap(A ⊗ B) ≥ min(Gap(A), Gap(B)) - ||Interaction||`

This is the bedrock of compositional verification: build safe complex systems 
by composing verified simple systems.

---

*Last updated: January 2026*
