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
| Bernoulli shift tower is exactly lumpable | `SGC.Bridge.CantorShiftTower.shiftTower_defect_zero` | uniform fresh-symbol shift kernels form an exact (`epsilon = 0`) strongly lumpable tower under deletion of the oldest symbol (identification with Moore's generalized shifts is framing, not theorem) |
| Discrete fluid dictionary | `SGC.Bridge.DiscreteFluidDynamics.*` | finite-state continuity / equilibrium / cycle / lift facts; `int_0^inf e^{-nu t} = 1/nu` |
| Residual Horizon | `SGC.Bridge.ResidualHorizon.residual_horizon` | projected fine trajectory vs exact coarse trajectory: `dist <= eps (e^{Kt} - 1) / K` where `eps` bounds the residual (closure term); zero residual => exact tracking |
| Statistical Horizon | `SGC.Bridge.StatisticalHorizon.statistical_forecast_horizon` | Koopman-type `U` (`||U|| <= 1`), projection `P`, `A = P U P`, `delta = ||(1-P) U P||`: `||P U^m P - A^m P|| <= m delta`; regression test `fourCycle_K2_ne_K1_sq` |
| Detailed balance is involution | `SGC.Bridge.DeterministicKernels.detailedBalance_iff_involutive` | deterministic `f` with positive invariant `pi`: detailed balance `<->` `f (f x) = x`; orbit of length `> 2` `=>` positive-current cycle; bare two-level handoff toy is compatible |
| Terminal decoding certificate | `SGC.Bridge.TerminalDecoding.kernel_terminal_reliability` | `tv(rho T^m J, rho J Q^m) <= min 1 (m c/2)`; a fixed decoder's per-class error transfers within that budget; `D_obs` sandwiched between `D_ref - 2 eps` and an explicit full-state contraction bound; `no_terminal_decoder_of_contraction`; Dobrushin mixing budgets |
| Block renormalization is exact | `SGC.Bridge.BlockRenormalization.detKernel_pow`, `multistep_mul`, `evalDom_iff_block_halts` | `(T_f)^b = T_{f^[b]}`; `h` blocks of `b` TM steps `=` `b*h` steps; the block tower halts iff the machine halts (Mathlib `Turing.eval`) |
| Deterministic lumpability is a factor map | `SGC.Bridge.DeterministicLumpability.detKernel_stronglyLumpable_iff`, `coarseGenerator_detKernel_eq` | `IsStronglyLumpable (T_f) P <-> f descends to P.Quot`; then the `pi`-weighted coarse kernel equals `T_{f-bar}` for every positive `pi`; eternal closure; blocking commutes with quotienting |
| Abstract BKM (L0) | `SGC.Bridge.AbstractBKM.norm_le_exp_budget` | `||x'|| <= W ||x||  =>  ||x t|| <= exp(int_0^t W) ||x 0||`; finite budget => bounded; excursion => budget spent |

All of these have kernel closure contained in `{propext, Classical.choice, Quot.sound}`
(183 of 185 theorems in the headline modules; 166 equal to all three). See
[`AXIOMS.md`](AXIOMS.md) for the complete ledger, including the two non-headline
theorems in `TrajectoryClosure` that still consume declared axioms.

## What is not claimed

- No result about the Clay Navier-Stokes alternatives (A)/(B).
- The continuum dictionary in `DiscreteFluidDynamics` (steady Euler, contact geometry)
  is a research framing stated as such in the file, not a theorem.
- `CantorShiftTower` proves exact lumpability of a *Bernoulli* shift tower; it does not
  formalize Moore's generalized shifts or a Turing simulation (external review,
  2026-09-12; docstring re-scoped).
- `ResidualHorizon` and `StatisticalHorizon` are Gronwall / telescoping statements in
  abstract settings; residual-controlled a posteriori error control for Galerkin
  Navier-Stokes is prior art (Morosi-Pizzocchero; Chernyshenko-Constantin-Robinson-Titi)
  and is not claimed as new.
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
checkout of this branch (3141 jobs, no errors).

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
