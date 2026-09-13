/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/

-- Foundations and weighted spaces
import SGC.Axioms.WeightedSpace
import SGC.Axioms.Geometry
import SGC.Axioms.GeometryGeneral
import SGC.Spectral.Core.Assumptions
import SGC.Spectral.Core.Projector
import SGC.Spectral.Envelope

-- Renormalization: lumpability, defect, horizons, curvature
import SGC.Renormalization.Lumpability
import SGC.Renormalization.Approximate
import SGC.Renormalization.MeasureReentry
import SGC.Renormalization.KernelHorizon
import SGC.Renormalization.CurvatureQuotient

-- Geometry and thermodynamics used by the bridges
import SGC.Geometry.DiscreteCurvature
import SGC.Geometry.CurvatureBridge
import SGC.Thermodynamics.LogSum
import SGC.Thermodynamics.EntropyProduction
import SGC.Thermodynamics.FluxDecomposition
import SGC.Topology.PadicPathSpace

-- Bridges
import SGC.Bridge.ValidityHorizon
import SGC.Bridge.DefectHorizonBridge
import SGC.Bridge.TrajectoryClosure
import SGC.Bridge.Consolidation
import SGC.Bridge.CoherenceObstruction
import SGC.Bridge.GeometricClosure
import SGC.Bridge.PhaseClassifier
import SGC.Bridge.Quantum
import SGC.Bridge.Recovery
import SGC.Bridge.CurvatureUndecidability
import SGC.Bridge.HaltingCompiler
import SGC.Bridge.CantorShiftTower
import SGC.Bridge.DiscreteFluidDynamics
import SGC.Bridge.AbstractBKM
import SGC.Bridge.ResidualHorizon

/-!
# SGC - Two Horizons

Curated root for the *Two Horizons* program: coarse-graining defects, fluid
computation (Miranda-Moore), and regularity budgets (Beale-Kato-Majda).

Every module below is kernel-checked. The headline declarations and their exact
axiom closures are recorded in `AXIOMS.md` and in the `lean-triage` receipts under
`docs/receipts/`. The position paper is `docs/two-horizons.md`.

## Headline modules

* `SGC.Renormalization.KernelHorizon` - the Kernel Horizon theorem:
  finite-time closure error `<= n * ||C_T||`; validity horizon inverse in the defect.
* `SGC.Bridge.DefectHorizonBridge` - continuous-time defect-horizon bound with
  explicit constants; the abstract leakage `epsilon` equals the concrete defect.
* `SGC.Bridge.TrajectoryClosure` - trajectory closure bounds, axiom-free restatement.
* `SGC.Bridge.ValidityHorizon` - semigroup perturbation bound in a Banach algebra.
* `SGC.Renormalization.CurvatureQuotient` - Bakry-Emery `CD(rho, inf)` descends along
  exactly lumpable quotients (mathematics: Pedrotti-Salez; formalization + strict
  witness: this project).
* `SGC.Bridge.CurvatureUndecidability`, `SGC.Bridge.HaltingCompiler` - a global
  curvature bound on a compiled generator family is equivalent to non-halting of
  Mathlib's `Turing.TM0` machines.
* `SGC.Bridge.CantorShiftTower` - Moore's shift is an exact (`epsilon = 0`) strongly
  lumpable renormalization tower.
* `SGC.Bridge.DiscreteFluidDynamics` - finite-state current / cycle / lift facts and
  the viscous time budget; the continuum dictionary is framing, stated as such.
* `SGC.Bridge.AbstractBKM` - L0 of the BKM ladder: time-dependent Gronwall budget
  theorem in a normed space; finite budget implies bounded evolution.
* `SGC.Bridge.ResidualHorizon` - the nonlinear Kernel Horizon: coarse-law error is
  controlled by the accumulated residual (re-entry / closure term); zero residual
  forces exact tracking.

## Supporting modules

Everything else in `src/SGC/` is the transitive import closure needed to build the
headline modules. Some supporting modules declare axioms that the headline theorems
do NOT consume; see `AXIOMS.md`.
-/
