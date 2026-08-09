# SGC — The Spectral Geometry of Consolidation (Formalization Archive)

Lean 4 formalization of structural persistence in stochastic systems: the
Γ-calculus of finite Markov generators, exact and approximate lumpability,
discrete Bakry-Émery curvature, symbolic (p-adic) path spaces, and bridges to
computability and hydrodynamics.

This branch is a **formalization-only archive**. It contains the Lean sources,
build configuration, and CI audit — nothing else. It is updated as the
formalization progresses.

## Build

Requires [elan](https://github.com/leanprover/elan). Toolchain and Mathlib are
pinned (`lean-toolchain`, `lake-manifest.json`; currently Lean 4.25.2).

```
lake exe cache get   # fetch Mathlib build cache
lake build           # full library
lake env lean scripts/AxiomAudit.lean   # headline axiom audit (hard gate)
```

## Epistemic tiers

The library is explicitly stratified; the CI enforces the boundary.

1. **Verified core.** Kernel-checked theorems whose dependency closure contains
   exactly Lean's classical trio `[propext, Classical.choice, Quot.sound]` —
   no project axioms, no `sorry`. The headline theorems below are gated by
   `scripts/AxiomAudit.lean`: if anything else enters their closure, CI fails.
2. **Firewalled modeling interfaces.** Some modules declare explicit `axiom`s
   documenting continuum/analytic assumptions (e.g. manifold convergence,
   Duhamel/Weyl bounds). These are deliberate, visible interfaces — never
   imported by the verified core. CI reports their count and locations.
3. **Work in progress.** A small number of modules contain `sorry`-marked
   statements under active development. CI reports them; they are not part of
   any headline claim.

## Headline theorems (verified core)

| Theorem | Module | Statement |
|---|---|---|
| `pathSpace_homeo_padicInt` | `SGC.Topology.PadicPathSpace` | `PathSpace (Fin p) ≃ₜ ℤ_[p]` for prime `p`, via an explicit digit-tower comparison map |
| `pi_pathSpace_homeo_pi_padicInt` | `SGC.Topology.PadicPathSpace` | d-fold product version: `(Fin d → PathSpace (Fin p)) ≃ₜ (Fin d → ℤ_[p])` |
| `killingDefect_quantitative` | `SGC.Bridge.AffinityProtectionQuantitative` | Measure-independent lower bound on the Killing defect in terms of the affinity charge of a cycle |
| `killingDefect_exoticLift_quantitative` | `SGC.Bridge.AffinityProtectionQuantitative` | Instantiation at the m = 3 exotic-lift handle cycle |
| `cd0_haltW_iff` | `SGC.Bridge.CurvatureUndecidability` | On the bi-infinite path with rates in {1,4}: `CD(0,∞)` holds iff the (at-most-once) marker never fires — the hardness gadget for deciding a global Bakry-Émery bound |
| `not_cd0_haltW_of_halts` | `SGC.Bridge.CurvatureUndecidability` | Contrapositive: a fired marker is witnessed by strictly negative Γ₂ |
| `cd0_compiled_iff` | `SGC.Bridge.HaltingCompiler` | The compiled reduction: `CD0 (haltW (haltMarker M w)) ↔ ¬ (TM0.eval M w).Dom` — deciding the global curvature bound on the compiled generator family is deciding non-halting for Mathlib's `Turing.TM0` machines |
| `not_cd0_compiled_iff` | `SGC.Bridge.HaltingCompiler` | Contrapositive: a curvature violation in the compiled generator is exactly a halting certificate (both poles inhabited: `not_cd0_haltNow`, `cd0_spinRight`) |
| `RicciCurvatureBound_quotient` | `SGC.Renormalization.CurvatureQuotient` | `CD(ρ,∞)` descends along exactly lumpable quotients (Γ-calculus intertwining) |
| `StarExample.curvature_hiding` | `SGC.Renormalization.CurvatureQuotient` | Strictness witness: the star `K_{1,6}` violates `CD(0,∞)` while its two-state orbit quotient satisfies `CD(9/2,∞)` |

## Scope and prior art

- The mathematical content of the quotient-descent theorem is due to
  **Pedrotti–Salez**, *A new cutoff criterion for non-negatively curved
  chains*, [arXiv:2501.13079](https://arxiv.org/abs/2501.13079), §2.2
  (Markovian projections). To our knowledge — pending a dedicated cross-prover
  prior-art search — this development contributes a Lean formalization of the
  projection/intertwining curvature argument for finite discrete Markov
  generators, together with the formally verified strict-improvement witness.
- Per-vertex Bakry-Émery curvature as an eigenvalue problem:
  **Cushing–Kamtue–Liu–Peyerimhoff**,
  [arXiv:2102.08687](https://arxiv.org/abs/2102.08687).
- The discrete fluid dictionary (`SGC.Bridge.DiscreteFluidDynamics`) is a
  research dictionary against the fluid-computation program of
  **Cardona–Miranda–Peralta-Salas** (PNAS 118, 2021) and successors; the
  continuum statements are *not* formalized here and no equivalence is
  claimed. The curvature-undecidability module is self-contained and does not
  use fluid dynamics.
- `cd0_haltW_iff` is stated for an abstract at-most-once Boolean marker; the
  computable compiler `(M, w) ↦ haltMarker M w` closing this gap is provided
  by `SGC.Bridge.HaltingCompiler` (`cd0_compiled_iff`), over Mathlib's own
  `Turing.TM0` model and halting predicate `(TM0.eval M w).Dom`. The
  undecidability of `TM0` halting itself and Π⁰₁ *membership* of the global
  bound are not re-proved there; the reduction is the formalized content.

## License

Apache 2.0 — see [LICENSE](LICENSE).

## Citation

> Shroyer, J. *et al.* (2026). *SGC: The Spectral Geometry of Consolidation —
> Lean 4 formalization.* GitHub: `JasonShroyer/sgc-lean`, branch
> `formalization`.
