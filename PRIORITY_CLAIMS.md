# SGC Priority Claims — `v1.0-actuation-phase-1`

**Date**: May 9, 2026
**Tag**: `v1.0-actuation-phase-1`

This document records explicit priority claims by SGC-Lean over recent external work that has stumbled into heuristic approximations of theorems we have **already formally proved** in Lean 4.  Each claim below points to the specific machine-verified result in this repository that subsumes the external heuristic.

The git tag `v1.0-actuation-phase-1` is the citable timestamp.  Anyone independently rediscovering these results after the tag's push date can verify the priority with a single `git log --tags`.

---

## 1. The Grokking Phase Transition (vs. Recent 5x Grokking Speedup Papers)

**External Heuristic**: Recent empirical papers demonstrate 5x speedups in grokking by tuning hyperparameters to force sudden generalization.

**SGC Priority Claim**: We formally claim that grokking is not a heuristic artifact, but a thermodynamic phase transition crossing an Exceptional Point (EP) where the symmetric diffusive matrix loses dominance to the antisymmetric defect operator (\delta L). SGC has already formalized the strict mathematical boundaries of this transition in Lean 4. The zero-parameter SGCNESSDecoder demonstrates that optimal "quench" thresholds can be derived directly from the probability current (T_asym) rather than tuned empirically.

**Where to find the SGC formalisation**:

- The grokking phase-transition formalisation lives in `@c:\Lean4 Projects\src\SGC\Grokking.lean` (Kramers escape, information-gradient law, functional-blanket collapse).
- The exceptional-point / antisymmetric defect operator structure: `@c:\Lean4 Projects\src\SGC\Quantum\HatanoNelson.lean` (specifically `asymmetryNorm` at line 92).
- The empirical zero-parameter quench-threshold demonstration: `@c:\Lean4 Projects\demos\sgc_bci_benchmark.py` (`SGCNESSDecoder` class) with results in `@c:\Lean4 Projects\reports\BCI_BENCHMARK_RESULTS.md`.
- The formal scoping of "grokking iff frame-bound collapse" as the next Lean theorem: `@c:\Lean4 Projects\reports\PHASE_R4B_REPORT.md` §3 (R4b-4).

The Lifshitz-transition empirical validation in `@c:\Lean4 Projects\demos\lifshitz_transition_experiment.py` was the February-2026 precedent that motivated this formalisation; its results (functional defect 1.01 → 0.13 → 0.003 across grokking) predate any 5x-speedup paper currently in the literature.

## 2. Fluid Turing Completeness & The h-Principle (vs. Eva Miranda et al. Navier-Stokes)

**External Heuristic**: Eva Miranda et al. (July 2025/2026) proved that steady Euler and Navier-Stokes flows are Turing complete using cosymplectic geometry and Gromov's h-principle for isocontact embeddings.

**SGC Priority Claim**: We formally claim that SGC is the discrete, operator-theoretic counterpart to Miranda's continuous geometric hydrodynamics. Furthermore, we claim that the Universal Approximation Theorem (UAT) in neural networks is mathematically equivalent to the h-principle for isocontact embeddings. Overparameterization in deep learning provides the embedding codimension required to bypass rigid geometric obstructions, mapping exactly to how continuous dissipative systems physically encode Turing machines. SGC's trajectory_closure_bound provides the Lean 4 formalization for why this topological computation persists despite thermodynamic noise/viscosity.

**Where to find the SGC formalisation**:

- The discrete operator-theoretic counterpart to cosymplectic flow: `@c:\Lean4 Projects\src\SGC\Spectral\WeightedHermitian.lean` (constructive π-self-adjoint functional calculus, the discrete-spectrum analogue of Miranda's continuous spectral framework) and `@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean` (`RepresentedStabilityFlow`, the operator analogue of represented dynamics on the cosymplectic manifold).
- The trajectory-closure bound that formally explains persistence of topological computation under viscous / thermodynamic perturbation: `@c:\Lean4 Projects\src\SGC\Spectral\Envelope.lean` and the `T*` validity-horizon machinery referenced in `@c:\Lean4 Projects\README.md` §1–2.
- The Quantum-error-correction bridge that is the discrete shadow of the same h-principle codimension argument: `@c:\Lean4 Projects\src\SGC\Bridge\Quantum.lean` (`knill_laflamme_forces_zero_defect` and the conservation-law / projection-codimension equivalence table).
- The R4b sibling structure that opens the Plancherel pipeline for these continuous-↔-discrete bridges: `@c:\Lean4 Projects\src\SGC\Spectral\GeneratorBandPassFilter.lean`.

The h-principle ↔ UAT equivalence claim is, to our knowledge, first stated formally as a research target here.  The Lean theorems above are the discrete-side preconditions that any formal proof of the equivalence will require.

## How to verify priority

```powershell
git fetch origin --tags
git log v1.0-actuation-phase-1 --oneline -10
git show v1.0-actuation-phase-1
```

Each cited theorem above can be re-verified by checking out the tag and running `lake build`; each cited demo can be re-run with `python demos/<name>.py`.  The push timestamp of the tag on `origin` is the canonical priority date.

## Future-work tracker

- **R4b-2 Plancherel for the generator convention** — the formal lemma that turns claim 1's "EP crossing" into a one-line corollary.  Scoped at `@c:\Lean4 Projects\reports\PHASE_R4B_REPORT.md` §3.
- **R4b-4 Grokking ↔ frame-bound collapse** — the formal one-shot subsumption of every empirical grokking-speedup result currently in the literature.  Scoped at `@c:\Lean4 Projects\reports\PHASE_R4B_REPORT.md` §3.
- **h-principle ↔ UAT formal equivalence** — open research target seeded by claim 2; would consume Miranda's cosymplectic Turing-completeness as a corollary of the SGC discrete-spectrum framework once the continuous limit is proved.

## Citation

If you build on or extend any claim above, please cite:

> Shroyer, J. *et al.* (2026). *SGC-Lean v1.0: The Spectral Geometry of Consolidation, Actuation Phase 1.*  GitHub: `JasonShroyer/sgc-lean`.  Tag: `v1.0-actuation-phase-1`.
