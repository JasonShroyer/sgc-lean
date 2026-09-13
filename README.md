# SGC - Two Horizons

**Kernel-checked Lean 4 theorems on coarse-graining defects, fluid computation, and
regularity budgets.**

This repository is the curated formalization behind the position paper
[*Two Horizons: Coarse-Graining Defects, Fluid Computation, and Regularity Budgets*](docs/two-horizons.md).
It contains exactly the Lean modules that paper cites, their transitive import
closure, the axiom ledger, and the machine-generated audit receipts. Nothing else.

## What is proved here

Let `L` be a finite-state Markov generator, `P` a partition into macrostates, `Pi` the
conditional-expectation projector, `D = (I - Pi) L Pi` the **lumpability defect**.

| Theorem | Declaration | Statement (informal) |
|---|---|---|
| Kernel Horizon | `SGC.Renormalization.KernelHorizon.kernel_closure_error_le` | closure error after `n` steps `<= n * ||C_T||`; validity horizon is inverse in the defect |
| Defect-Horizon bound | `SGC.Bridge.DefectHorizonBridge.defect_horizon_bound` | `||e^{tL} f0 - e^{t L-bar} f0||_pi <= t ||D||_pi e^{t(...)} ||f0||_pi`, explicit constants |
| Curvature descends | `SGC.Renormalization.CurvatureQuotient.RicciCurvatureBound_quotient` | Bakry-Emery `CD(rho, inf)` is preserved by exactly lumpable quotients; strict witness `curvature_hiding` |
| Curvature bound is Pi^0_1-hard | `SGC.Bridge.HaltingCompiler.cd0_compiled_iff` | global `CD(0, inf)` on a compiled generator family `<->` non-halting of Mathlib `TM0` machines |
| Moore's shift is renormalization-transparent | `SGC.Bridge.CantorShiftTower.shiftTower_defect_zero` | cylinder truncations of the shift form an exact (`epsilon = 0`) strongly lumpable tower |
| Discrete fluid dictionary | `SGC.Bridge.DiscreteFluidDynamics.*` | finite-state continuity / equilibrium / cycle / lift facts; `int_0^inf e^{-nu t} = 1/nu` |
| Abstract BKM (L0) | `SGC.Bridge.AbstractBKM.norm_le_exp_budget` | `||x'|| <= W ||x||  =>  ||x t|| <= exp(int_0^t W) ||x 0||`; finite budget => bounded; excursion => budget spent |

All of these have kernel closure `{propext, Classical.choice, Quot.sound}`. See
[`AXIOMS.md`](AXIOMS.md) for the complete ledger, including the two non-headline
theorems in `TrajectoryClosure` that still consume declared axioms.

## What is not claimed

- No result about the Clay Navier-Stokes alternatives (A)/(B).
- The continuum dictionary in `DiscreteFluidDynamics` (steady Euler, contact geometry)
  is a research framing stated as such in the file, not a theorem.
- `AbstractBKM` proves an abstract budget theorem in a normed space; it does not
  instantiate Euler or Navier-Stokes. Levels L1-L3 of the ladder are open.
- The mathematics of `RicciCurvatureBound_quotient` is due to Pedrotti-Salez
  (arXiv:2501.13079); the kernel-checked formalization and the strict-improvement
  witness are this project's.

## Build

```
elan toolchain install leanprover/lean4:v4.25.2   # pinned in lean-toolchain
lake exe cache get
lake build
```

Mathlib is pinned by `lake-manifest.json`. The build has been replayed from a clean
checkout of this branch (3138 jobs, no errors).

## Audit

Receipts under [`docs/receipts/`](docs/receipts/) were produced by
[`lean-triage`](https://github.com/JasonShroyer/sgc-second-brain/tree/main/lean-triage)
(v0.2.1): per-theorem kernel axiom closure with origin, verbatim kernel-printed statement
with SHA-256, unused-hypothesis check, definition cone, budgeted vacuity / triviality
witnesses, repo-wide axiom inventory with consumer counts. `REPORT.md` in each receipt
directory is rendered only from the sealed `receipt.json`.

## Layout

```
src/SGC.lean                    curated root (headline modules listed first)
src/SGC/Bridge/                 the bridges: horizons, curvature undecidability, shift tower,
                                discrete fluids, AbstractBKM
src/SGC/Renormalization/        lumpability, defect, Kernel Horizon, curvature quotient
src/SGC/{Axioms,Spectral,Geometry,Thermodynamics,Topology}/   supporting closure
docs/two-horizons.md            the position paper (claims labelled KERNEL / EXTERNAL /
                                FRAMING / CONJECTURE, with a claim map)
docs/bkm-ladder.md              the L0-L3 design note
docs/receipts/                  lean-triage receipts
AXIOMS.md                       axiom ledger
```

## Citation

See [`CITATION.cff`](CITATION.cff).

## License

Apache 2.0. See [`LICENSE`](LICENSE).
