# Axiom ledger

Trust in a Lean theorem is decided by the **kernel closure of that theorem**, not by
the import graph of the file it lives in. This ledger records both, so that a reader
can see exactly which declared assumptions exist in this tree and which theorems, if
any, consume them.

Source of the numbers: `lean-triage` receipt `docs/receipts/opus-closure/receipt.json`
(kernel `collectAxioms` per theorem; repo-wide inventory with consumer counts over the
loaded closure), taken at `sgc-lean` commit `0012a5a` on toolchain
`leanprover/lean4:v4.25.2`.

## Headline theorems: closure is the standard three axioms

All 170 theorems in the ten headline modules named in `README.md` have kernel closure
contained in `{propext, Classical.choice, Quot.sound}`, **with two exceptions**, both in
`SGC.Bridge.TrajectoryClosure` and both documented in that file as belonging to
separate, unfinished retirement campaigns:

| Theorem | Declared axioms consumed |
|---|---|
| `SGC.Approximate.NCD_uniform_error_bound` | `NCD_defect_split`, `NCD_integral_bound` |
| `SGC.Approximate.spectral_stability_reversible` | `Weyl_inequality_pi` |

Neither is cited by the position paper, neither is a headline result, and nothing
else in the tree depends on them. They are kept so that the module is identical to
the main development; they will be discharged or removed before any wider release.

## Declared axioms in the shipped closure (38)

These live in *supporting* modules pulled in by the import graph (chiefly
`CurvatureQuotient -> GeometricClosure -> Consolidation/Recovery/Quantum/CurvatureBridge`
and `ValidityHorizon -> PhaseClassifier`). "Consumers" counts declarations in the
loaded closure whose type or value mentions the axiom. A consumer count of 0 means
the axiom is dead weight here.

| Axiom | Module | Consumers | Unconstrained numeric params |
|---|---|---|---|
| `SGC.Axioms.GeometryGeneral.fidelity_pi` | `SGC.Axioms.GeometryGeneral` | 0 | - |
| `SGC.Axioms.GeometryGeneral.traceNorm_pi` | `SGC.Axioms.GeometryGeneral` | 8 | - |
| `SGC.Axioms.GeometryGeneral.traceNorm_pi_add` | `SGC.Axioms.GeometryGeneral` | 1 | - |
| `SGC.Axioms.GeometryGeneral.traceNorm_pi_neg` | `SGC.Axioms.GeometryGeneral` | 1 | - |
| `SGC.Axioms.GeometryGeneral.traceNorm_pi_nonneg` | `SGC.Axioms.GeometryGeneral` | 1 | - |
| `SGC.Bridge.Coherence.HeatKernel_preserves_nonneg` | `SGC.Bridge.CoherenceObstruction` | 1 | - |
| `SGC.Bridge.Coherence.HeatKernel_preserves_sum` | `SGC.Bridge.CoherenceObstruction` | 1 | - |
| `SGC.Bridge.Coherence.norm_zero_forces_alpha_zero` | `SGC.Bridge.CoherenceObstruction` | 1 | - |
| `SGC.Bridge.Coherence.partition_membership_sum_one` | `SGC.Bridge.CoherenceObstruction` | 1 | - |
| `SGC.Bridge.GeometricClosure.BakryEmery_implies_stability` | `SGC.Bridge.GeometricClosure` | 1 | - |
| `SGC.Bridge.GeometricClosure.EnergyDerivative` | `SGC.Bridge.GeometricClosure` | 8 | - |
| `SGC.Bridge.GeometricClosure.EnergySecondDerivative` | `SGC.Bridge.GeometricClosure` | 7 | - |
| `SGC.Bridge.GeometricClosure.Poincare_from_integrated_curvature` | `SGC.Bridge.GeometricClosure` | 1 | - |
| `SGC.Bridge.GeometricClosure.Ricci_tensor_min` | `SGC.Bridge.GeometricClosure` | 2 | - |
| `SGC.Bridge.GeometricClosure.exponential_decay_from_convexity` | `SGC.Bridge.GeometricClosure` | 1 | - |
| `SGC.Bridge.Quantum.KL_coefficient_real` | `SGC.Bridge.Quantum` | 1 | - |
| `SGC.Bridge.Quantum.complexifyDefect_zero_iff` | `SGC.Bridge.Quantum` | 2 | - |
| `SGC.Bridge.Quantum.partitionToCodeSubspace` | `SGC.Bridge.Quantum` | 24 | - |
| `SGC.Bridge.Quantum.partitionToCodeSubspace_proj_eq` | `SGC.Bridge.Quantum` | 1 | - |
| `SGC.Bridge.Recovery.DataProcessingInequality` | `SGC.Bridge.Recovery` | 3 | - |
| `SGC.Bridge.Recovery.LandauerPrinciple` | `SGC.Bridge.Recovery` | 1 | - |
| `SGC.Bridge.Recovery.PetzRecoveryTheorem` | `SGC.Bridge.Recovery` | 2 | - |
| `SGC.Bridge.OllivierRicciCurvature` | `SGC.Geometry.CurvatureBridge` | 1 | - |
| `SGC.Bridge.curvature_defect_correspondence` | `SGC.Geometry.CurvatureBridge` | 0 | - |
| `SGC.Bridge.energy_entropy_rate_correspondence` | `SGC.Geometry.CurvatureBridge` | 0 | - |
| `SGC.Bridge.error_gradient_is_curvature` | `SGC.Geometry.CurvatureBridge` | 0 | - |
| `SGC.Bridge.yamabe_bounds_hidden_entropy` | `SGC.Geometry.CurvatureBridge` | 0 | - |
| `SGC.Geometry.KAT_existence` | `SGC.Geometry.DiscreteCurvature` | 1 | - |
| `SGC.Geometry.discrete_gauss_bonnet` | `SGC.Geometry.DiscreteCurvature` | 0 | - |
| `SGC.Geometry.totalSolidAngle` | `SGC.Geometry.DiscreteCurvature` | 1 | - |
| `SGC.Geometry.yamabe_flow_convergence` | `SGC.Geometry.DiscreteCurvature` | 0 | - |
| `SGC.Approximate.NCD_defect_split` | `SGC.Renormalization.Approximate` | 1 | - |
| `SGC.Approximate.NCD_integral_bound` | `SGC.Renormalization.Approximate` | 1 | - |
| `SGC.Approximate.Weyl_inequality_pi` | `SGC.Renormalization.Approximate` | 1 | - |
| `SGC.Approximate.rowsum_to_opNorm_bound` | `SGC.Renormalization.Approximate` | 1 | - |
| `SGC.Thermodynamics.gaspard_path_space_identity` | `SGC.Thermodynamics.EntropyProduction` | 2 | - |
| `SGC.Thermodynamics.hidden_entropy_bound_from_trajectory` | `SGC.Thermodynamics.EntropyProduction` | 1 | - |
| `SGC.Thermodynamics.non_normality_from_flux` | `SGC.Thermodynamics.FluxDecomposition` | 0 | - |

## Cleanup obligations before public release

1. Move the Gamma-calculus definitions (`RicciCurvatureBound`, `Gamma`, `Gamma2`) out of
   `GeometricClosure` into an axiom-free module so that `CurvatureQuotient`'s import
   closure carries no declared axioms *by construction*, not only by kernel check.
2. Discharge or delete `NCD_defect_split`, `NCD_integral_bound`, `Weyl_inequality_pi`
   (Weyl's inequality for the pi-weighted inner product is provable from Mathlib's
   Courant-Fischer material; the NCD pair needs a model or removal).
3. Delete the 8 zero-consumer axioms or move their modules out of the closure.
4. Re-run `lean-triage` and replace this ledger from the new receipt.

## Method

Every number here is machine-derived from the elaborated environment (`Lean.collectAxioms`,
`Expr.getUsedConstants`), never from source text. The receipt also records the verbatim
kernel-printed statement of each headline theorem with a SHA-256, unused hypotheses,
and the project-local definition cone of each statement.
