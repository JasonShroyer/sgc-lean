# lean-triage report: FINDINGS

- receipt: `lean-triage-71ef010b1b24-20260913T011932Z`  (hash_self `866a7700560fd5c9...`)
- tool: lean-triage 0.2.1 (source `7e7d28e056e9`, probe `b070c71d2773`)
- repo: https://github.com/JasonShroyer/sgc-lean.git
- commit: 0012a5a5b16f7e4e26465e84c3772627a17a5fd0  dirty=False
- toolchain: leanprover/lean4:v4.25.2
- source tree sha256: `71ef010b1b248ecf127c2efd5a11a4cedae21fda2fad56bd285c26f4b97c5703`
- modules: SGC.Bridge.AbstractBKM, SGC.Bridge.DiscreteFluidDynamics, SGC.Bridge.CantorShiftTower, SGC.Bridge.HaltingCompiler, SGC.Bridge.CurvatureUndecidability, SGC.Renormalization.CurvatureQuotient, SGC.Renormalization.KernelHorizon, SGC.Bridge.DefectHorizonBridge, SGC.Bridge.TrajectoryClosure, SGC.Bridge.ValidityHorizon

## Verdict

**FINDINGS** - 3 fail, 29 warn, 367 info.

NO_BLOCKING_EVIDENCE = no configured blocking evidence found by the checks that ran. REVIEW = warn-level items need a human. FINDINGS = evidence the claim is not established as stated. None of these means 'correct' or 'important'.

## Execution context

- execution_mode: trusted_local  network_policy: unknown  credential_mounts: unknown (self-declared by operator)
- checks that did NOT run: lake build (skipped by request), kernel replay from fresh environment (lean4checker not available or build unverified), comparator / external checker (never run automatically), human claim-map attestation (none supplied)

## Findings

basis: kernel = read from the kernel/elaborated environment; witness = a reproducible object (closing tactic) was produced; heuristic = pattern that needs a human; attestation = human-signed or unsigned claim; process = provenance/toolchain/process fact.

| sev | basis | id | code | theorem | detail |
|---|---|---|---|---|---|
| fail | kernel | F03 | AXIOM_BEYOND_TRUSTED_BASE | SGC.Approximate.NCD_uniform_error_bound | closure depends on axiom SGC.Approximate.NCD_defect_split (project, module SGC.Renormalization.Approximate) |
| fail | kernel | F03 | AXIOM_BEYOND_TRUSTED_BASE | SGC.Approximate.NCD_uniform_error_bound | closure depends on axiom SGC.Approximate.NCD_integral_bound (project, module SGC.Renormalization.Approximate) |
| fail | kernel | F03 | AXIOM_BEYOND_TRUSTED_BASE | SGC.Approximate.spectral_stability_reversible | closure depends on axiom SGC.Approximate.Weyl_inequality_pi (project, module SGC.Renormalization.Approximate) |
| warn | heuristic | F10 | CITED_DECLARATION_MISSING | SGC.DiscreteFluidDynamics | cited in reports/CELEGANS_FLOQUET_TSALLIS_BRIDGE.md but no such declaration exists in the loaded environment or in project sources |
| warn | heuristic | F10 | CITED_DECLARATION_MISSING | SGC.Measurement.Interfaces.TightnessAudit | cited in demos/README.md but no such declaration exists in the loaded environment or in project sources |
| warn | heuristic | F10 | CITED_DECLARATION_MISSING | SGC.Measurement.Interfaces.tightness_ratio_nonneg | cited in demos/README.md but no such declaration exists in the loaded environment or in project sources |
| warn | heuristic | F10 | CITED_DECLARATION_MISSING | SGC.Measurement.Wavelets | cited in demos/README.md but no such declaration exists in the loaded environment or in project sources |
| warn | heuristic | F10 | CITED_DECLARATION_MISSING | SGC.Measurement.Wavelets.DiffusionWavelet | cited in demos/README.md but no such declaration exists in the loaded environment or in project sources |
| warn | heuristic | F10 | CITED_DECLARATION_MISSING | SGC.Stochastic.KramersEscape | cited in reports/BROWNIAN_MOTION_LEAN_EXPLORATION.md but no such declaration exists in the loaded environment or in project sources |
| warn | heuristic | F08 | DEFINITION_REVIEW_CANDIDATE_IGNORED_ARGS | - | definition SGC.Approximate.CoarseProjectorMatrix ignores explicit argument(s) hπ |
| warn | heuristic | F08 | DEFINITION_REVIEW_CANDIDATE_IGNORED_ARGS | - | definition SGC.Bridge.CurvatureUndecidability.unitW ignores explicit argument(s) x._@.SGC.Bridge.CurvatureUndecidability.3800758693._hygCtx._hyg.5 |
| warn | heuristic | F08 | DEFINITION_REVIEW_CANDIDATE_IGNORED_ARGS | - | definition SGC.Bridge.DefectHorizonBridge.PiMat ignores explicit argument(s) pi_dist, _hπ |
| warn | heuristic | F08 | DEFINITION_REVIEW_CANDIDATE_IGNORED_ARGS | - | definition SGC.Bridge.DefectHorizonBridge.instAlgebraRealPiMat ignores explicit argument(s) pi_dist, hπ |
| warn | heuristic | F08 | DEFINITION_REVIEW_CANDIDATE_IGNORED_ARGS | - | definition SGC.Bridge.DefectHorizonBridge.instRingPiMat ignores explicit argument(s) pi_dist, hπ |
| warn | heuristic | F08 | DEFINITION_REVIEW_CANDIDATE_IGNORED_ARGS | - | definition SGC.Bridge.DefectHorizonBridge.ofMat ignores explicit argument(s) pi_dist, hπ |
| warn | heuristic | F08 | DEFINITION_REVIEW_CANDIDATE_IGNORED_ARGS | - | definition SGC.Bridge.DefectHorizonBridge.toMat ignores explicit argument(s) pi_dist, hπ |
| warn | heuristic | F08 | DEFINITION_REVIEW_CANDIDATE_IGNORED_ARGS | - | definition SGC.Bridge.HaltingCompiler.haltNow ignores explicit argument(s) x._@.SGC.Bridge.HaltingCompiler.3717856741._hygCtx._hyg.16, x._@.SGC.Bridge.HaltingCompiler.3717856741._hygCtx._hyg.18 |
| warn | heuristic | F08 | DEFINITION_REVIEW_CANDIDATE_IGNORED_ARGS | - | definition SGC.Bridge.HaltingCompiler.spinRight ignores explicit argument(s) x._@.SGC.Bridge.HaltingCompiler.1318617077._hygCtx._hyg.17 |
| warn | heuristic | F08 | DEFINITION_REVIEW_CANDIDATE_IGNORED_ARGS | - | definition SGC.Q_map ignores explicit argument(s) _hπ |
| warn | heuristic | F08 | DEFINITION_REVIEW_CANDIDATE_IGNORED_ARGS | - | definition SGC.constant_vec_one ignores explicit argument(s) x._@.SGC.Axioms.Geometry.221746778._hygCtx._hyg.16 |
| warn | heuristic | F08 | DEFINITION_REVIEW_CANDIDATE_IGNORED_ARGS | - | definition SGC.opNorm_set ignores explicit argument(s) _h_pos |
| warn | heuristic | F10 | NARRATIVE_CLAIM_NEEDS_HUMAN_MAP | - | strong-claim vocabulary 'Millennium' appears 2x (THEORY.md:175, docs/bkm-formalization-design.md:46); a human must map the formal statements to it |
| warn | heuristic | F10 | NARRATIVE_CLAIM_NEEDS_HUMAN_MAP | - | strong-claim vocabulary 'Navier-Stokes' appears 5x (PRIORITY_CLAIMS.md:93, PRIORITY_CLAIMS.md:95, PRIORITY_CLAIMS.md:99, ...); a human must map the formal statements to it |
| warn | heuristic | F10 | NARRATIVE_CLAIM_NEEDS_HUMAN_MAP | - | strong-claim vocabulary 'Riemann' appears 26x (CHANGELOG.md:164, RESEARCH_JOURNAL.md:90, VERIFIED_CORE_MANIFEST.md:381, ...); a human must map the formal statements to it |
| warn | heuristic | F10 | NARRATIVE_CLAIM_NEEDS_HUMAN_MAP | - | strong-claim vocabulary 'fully verified' appears 5x (README.md:37, VERIFIED_CORE_MANIFEST.md:52, VERIFIED_CORE_MANIFEST.md:117, ...); a human must map the formal statements to it |
| warn | heuristic | F10 | NARRATIVE_CLAIM_NEEDS_HUMAN_MAP | - | strong-claim vocabulary 'settles' appears 3x (decisions/0016-curvature-descends-along-lumpable-quotients.md:50, reports/PHASE_4A_CANONICAL_WAVELET_FISHER_RAO_INTEGRATION.md:249, theory_context/SGC UPAT Methods Deep Dive.md:211); a human must map the formal statements to it |
| warn | heuristic | F10 | NARRATIVE_CLAIM_NEEDS_HUMAN_MAP | - | strong-claim vocabulary 'unconditional' appears 10x (RESEARCH_JOURNAL.md:285, RESEARCH_JOURNAL.md:567, RESEARCH_JOURNAL.md:816, ...); a human must map the formal statements to it |
| warn | process | F13 | TOOLCHAIN_ADVISORY | - | toolchain leanprover/lean4:v4.25.2 is below 4.32.2: Kernel soundness bug (nested inductive types with phantom parameters) allowed an axiom-free proof of False; #print axioms reported nothing. Fixed in Lean 4.32.2. |
| warn | process | F13 | TOOLCHAIN_ADVISORY | - | toolchain leanprover/lean4:v4.25.2 is below 4.32.2: Runtime reference-count overflow path that could corrupt memory and yield False (reported in the 2026 soundness-bug hunt). |
| warn | kernel | F09 | UNUSED_HYPOTHESIS | SGC.Approximate.trajectory_closure_bound | hypothesis `hε` never occurs in the proof term; the statement may be over-constrained or mis-stated |
| warn | kernel | F09 | UNUSED_HYPOTHESIS | SGC.Approximate.vertical_error_bound | hypothesis `hε` never occurs in the proof term; the statement may be over-constrained or mis-stated |
| warn | kernel | F09 | UNUSED_HYPOTHESIS | SGC.Bridge.DefectHorizonBridge.instFiniteDimensionalRealPiMat | hypothesis `hπ` never occurs in the proof term; the statement may be over-constrained or mis-stated |
| info | witness | F07 | AUTOMATION_CLOSES_TARGET_UNDER_POLICY | SGC.Bridge.AbstractBKM.budget_zero | the configured automation policy closes the statement (`simp`); legitimate, but weigh against any strong narrative |
| info | witness | F07 | AUTOMATION_CLOSES_TARGET_UNDER_POLICY | SGC.Bridge.CantorShiftTower.truncate_pathShift | the configured automation policy closes the statement (`rfl`); legitimate, but weigh against any strong narrative |
| info | witness | F07 | AUTOMATION_CLOSES_TARGET_UNDER_POLICY | SGC.Bridge.CurvatureUndecidability.wit_add_one | the configured automation policy closes the statement (`simp`); legitimate, but weigh against any strong narrative |
| info | witness | F07 | AUTOMATION_CLOSES_TARGET_UNDER_POLICY | SGC.Bridge.CurvatureUndecidability.wit_add_two | the configured automation policy closes the statement (`simp`); legitimate, but weigh against any strong narrative |
| info | witness | F07 | AUTOMATION_CLOSES_TARGET_UNDER_POLICY | SGC.Bridge.CurvatureUndecidability.wit_self | the configured automation policy closes the statement (`simp`); legitimate, but weigh against any strong narrative |
| info | witness | F07 | AUTOMATION_CLOSES_TARGET_UNDER_POLICY | SGC.Bridge.CurvatureUndecidability.wit_sub_one | the configured automation policy closes the statement (`simp`); legitimate, but weigh against any strong narrative |
| info | witness | F07 | AUTOMATION_CLOSES_TARGET_UNDER_POLICY | SGC.Bridge.CurvatureUndecidability.wit_sub_two | the configured automation policy closes the statement (`simp`); legitimate, but weigh against any strong narrative |
| info | witness | F07 | AUTOMATION_CLOSES_TARGET_UNDER_POLICY | SGC.Bridge.DefectHorizonBridge.pmNorm_def | the configured automation policy closes the statement (`rfl`); legitimate, but weigh against any strong narrative |
| info | witness | F07 | AUTOMATION_CLOSES_TARGET_UNDER_POLICY | SGC.Bridge.HaltingCompiler.multistep_succ | the configured automation policy closes the statement (`rfl`); legitimate, but weigh against any strong narrative |
| info | witness | F07 | AUTOMATION_CLOSES_TARGET_UNDER_POLICY | SGC.Bridge.HaltingCompiler.multistep_zero | the configured automation policy closes the statement (`rfl`); legitimate, but weigh against any strong narrative |
| info | witness | F07 | AUTOMATION_CLOSES_TARGET_UNDER_POLICY | SGC.Bridge.HaltingCompiler.step_haltNow | the configured automation policy closes the statement (`rfl`); legitimate, but weigh against any strong narrative |
| info | witness | F07 | AUTOMATION_CLOSES_TARGET_UNDER_POLICY | SGC.Bridge.HaltingCompiler.step_spinRight | the configured automation policy closes the statement (`rfl`); legitimate, but weigh against any strong narrative |
| info | witness | F07 | AUTOMATION_CLOSES_TARGET_UNDER_POLICY | SGC.Renormalization.CurvatureQuotient.lift_fun_mul | the configured automation policy closes the statement (`rfl`); legitimate, but weigh against any strong narrative |
| info | kernel | F16 | AXIOM_UNREFERENCED | - | axiom SGC.Axioms.GeometryGeneral.fidelity_pi has no consumer in the loaded project modules; trust-surface bloat |
| info | kernel | F16 | AXIOM_UNREFERENCED | - | axiom SGC.Bridge.curvature_defect_correspondence has no consumer in the loaded project modules; trust-surface bloat |
| info | kernel | F16 | AXIOM_UNREFERENCED | - | axiom SGC.Bridge.energy_entropy_rate_correspondence has no consumer in the loaded project modules; trust-surface bloat |
| info | kernel | F16 | AXIOM_UNREFERENCED | - | axiom SGC.Bridge.error_gradient_is_curvature has no consumer in the loaded project modules; trust-surface bloat |
| info | kernel | F16 | AXIOM_UNREFERENCED | - | axiom SGC.Bridge.yamabe_bounds_hidden_entropy has no consumer in the loaded project modules; trust-surface bloat |
| info | kernel | F16 | AXIOM_UNREFERENCED | - | axiom SGC.Geometry.discrete_gauss_bonnet has no consumer in the loaded project modules; trust-surface bloat |
| info | kernel | F16 | AXIOM_UNREFERENCED | - | axiom SGC.Geometry.yamabe_flow_convergence has no consumer in the loaded project modules; trust-surface bloat |
| info | kernel | F16 | AXIOM_UNREFERENCED | - | axiom SGC.Thermodynamics.non_normality_from_flux has no consumer in the loaded project modules; trust-surface bloat |
| info | process | F12 | BUILD_SKIPPED | - | build skipped by request; the probe ran against existing .olean files whose provenance is not established here |
| info | heuristic | F10 | CITED_DECLARATION_UNLOADED | SGC.Bridge.CelegansFloquetTsallis.celegans_anomalous_diffusion_value | cited in reports/CELEGANS_FLOQUET_TSALLIS_BRIDGE.md; a declaration with this final name exists in project sources but not in the audited modules |
| info | heuristic | F10 | CITED_DECLARATION_UNLOADED | SGC.Bridge.CelegansFloquetTsallis.celegans_scaling_lt_UGM | cited in reports/CELEGANS_FLOQUET_TSALLIS_BRIDGE.md; a declaration with this final name exists in project sources but not in the audited modules |
| info | heuristic | F10 | CITED_DECLARATION_UNLOADED | SGC.Bridge.CelegansFloquetTsallis.predicted_alpha_eq_r_half | cited in reports/CELEGANS_FLOQUET_TSALLIS_BRIDGE.md; a declaration with this final name exists in project sources but not in the audited modules |
| info | heuristic | F10 | CITED_DECLARATION_UNLOADED | SGC.ComplexityRelativity.complexity_is_relational | cited in reports/SECOND_LAW_FORMALIZATION_2026-05-25.md; a declaration with this final name exists in project sources but not in the audited modules |
| info | heuristic | F10 | CITED_DECLARATION_UNLOADED | SGC.Evolution.Dynamics.EvolutionStep | cited in demos/README.md; a declaration with this final name exists in project sources but not in the audited modules |
| info | heuristic | F10 | CITED_DECLARATION_UNLOADED | SGC.Markov.StationaryDistribution.lean | cited in reports/PHASE_R2_R4_OPEN_DISCOVERY_FINDINGS.md; a declaration with this final name exists in project sources but not in the audited modules |
| info | heuristic | F10 | CITED_DECLARATION_UNLOADED | SGC.Quantum.KnillLaflamme.lean | cited in reports/PHASE_R2_R4_OPEN_DISCOVERY_FINDINGS.md; a declaration with this final name exists in project sources but not in the audited modules |
| info | heuristic | F10 | CITED_DECLARATION_UNLOADED | SGC.Spectral.Floquet.PeriodicGeneratorFamily | cited in reports/SPINGLASS_GAUGE_AUDIT.md; a declaration with this final name exists in project sources but not in the audited modules |
| info | heuristic | F10 | CITED_DECLARATION_UNLOADED | SGC.Stochastic.conjecture_C2_hard_half | cited in reports/CELEGANS_FLOQUET_TSALLIS_BRIDGE.md; a declaration with this final name exists in project sources but not in the audited modules |
| info | heuristic | F10 | CITED_DECLARATION_UNLOADED | SGC.Thermodynamics.Evolution.CanEvolve | cited in demos/README.md; a declaration with this final name exists in project sources but not in the audited modules |
| info | heuristic | F10 | CITED_DECLARATION_UNLOADED | SGC.Thermodynamics.Evolution.SatisfiesEvolutionInequality | cited in demos/README.md; a declaration with this final name exists in project sources but not in the audited modules |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Approximate.CoarseGeneratorMatrix.congr_simp | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Approximate.NCD_uniform_error_bound | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Approximate.PropagatorDiff_eq_proj_trajectory_diff | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Approximate.coarseGen_mul_proj | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Approximate.proj_commutes_heatKernel_coarseGen | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Approximate.proj_swap_heatKernelMap_coarseGen | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Approximate.propagator_approximation_bound | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Approximate.spectral_stability_reversible | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Approximate.trajectory_closure_bound | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Approximate.trajectory_norm_bound_uniform | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Approximate.vertical_error_bound | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.AbstractBKM.bounded_of_budget_le | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.AbstractBKM.budget_zero | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.AbstractBKM.exists_budget_gt_of_norm_gt | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.AbstractBKM.hasDerivAt_budget | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.AbstractBKM.norm_le_barrier_of_budget_control | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.AbstractBKM.norm_le_exp_budget | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.CantorShiftTower.row_sum_block_one | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.CantorShiftTower.row_sum_block_sub | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.CantorShiftTower.shiftGenerator_row_sum_zero | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.CantorShiftTower.shiftGenerator_stronglyLumpable | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.CantorShiftTower.shiftKernel_nonneg | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.CantorShiftTower.shiftKernel_row_sum | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.CantorShiftTower.shiftKernel_row_sum_block | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.CantorShiftTower.shiftTower_defect_zero | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.CantorShiftTower.shiftTower_eternal_closure | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.CantorShiftTower.shiftTower_quotient_realizes | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.CantorShiftTower.shiftTower_stronglyLumpable | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.CantorShiftTower.tailPartition_quot_map_eq_iff | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.CantorShiftTower.tail_shiftIn | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.CantorShiftTower.truncate_pathShift | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.CurvatureUndecidability.cd0_haltW_iff | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.CurvatureUndecidability.cd0_unitW | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.CurvatureUndecidability.gam2_heavy_eq | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.CurvatureUndecidability.gam2_unitW_eq | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.CurvatureUndecidability.haltW_eq_four | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.CurvatureUndecidability.haltW_eq_one | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.CurvatureUndecidability.haltW_eq_unitW | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.CurvatureUndecidability.not_cd0_haltW_of_halts | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.CurvatureUndecidability.not_cd0_of_heavy_edge | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.CurvatureUndecidability.wit_add_one | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.CurvatureUndecidability.wit_add_two | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.CurvatureUndecidability.wit_self | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.CurvatureUndecidability.wit_sub_one | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.CurvatureUndecidability.wit_sub_two | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.HeatKernel_opNorm_bound_proved | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.coarseGeneratorMatrix_mul_proj | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.coarseProj_fixes_coarse_heatKernel | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.defectComplement_mul_proj | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.defectComplement_mul_proj_eq_coarse | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.defectComplement_pow_mul_proj | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.defectMatrix_mulVec | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.defectMatrix_toLin | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.defect_eq_validity_leakage | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.defect_horizon_bound | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.exp_defectComplement_apply | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.exp_defectComplement_mul_proj | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.exp_piMat_eq | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.heatKernel_opNorm_explicit | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.instCompleteSpacePiMat | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.instFiniteDimensionalRealPiMat | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.instNormOneClassPiMatOfNonempty | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.mulProjLin_continuous | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.norm_exp_le | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.norm_pi_neg | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.norm_pi_nonneg' | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.norm_sq_pi_proj_pythagorean | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.opNorm_exp_eq_pmNorm | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.pmNorm_add_le | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.pmNorm_def | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.pmNorm_eq_zero | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.pmNorm_mulVec_le | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.pmNorm_mul_le | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.pmNorm_neg | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.pmNorm_nonneg | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.pmNorm_smul_le | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.pmNorm_zero | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.proj_mul_coarseGen | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.smul_defectComplement_pow_mul_proj | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.toMatLin_continuous | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.total_error_pythagorean | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.trajectory_closure_bound_explicit | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.vertical_closure_bound_explicit | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DefectHorizonBridge.vertical_defect_horizon_bound | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DiscreteFluidDynamics.coarse_current_eq_sum_fine | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DiscreteFluidDynamics.current_zero_iff_reversible | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DiscreteFluidDynamics.cycle_of_pos_cycleSpace_field | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DiscreteFluidDynamics.damped_validity_budget | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DiscreteFluidDynamics.divergence_current_eq_neg_residual | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DiscreteFluidDynamics.edgeInner_gradient_eq | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DiscreteFluidDynamics.fiberPartition_quot_map_eq_iff | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DiscreteFluidDynamics.killingDefect_eq_edgeInner_self | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DiscreteFluidDynamics.killingDefect_eq_four_antisym | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DiscreteFluidDynamics.killingDefect_eq_zero_iff_reversible | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DiscreteFluidDynamics.killingDefect_nonneg | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DiscreteFluidDynamics.killingDefect_pos_iff_positive_current_cycle | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DiscreteFluidDynamics.ness_has_current_cycle | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DiscreteFluidDynamics.ness_quotient_forces_ness_fine | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DiscreteFluidDynamics.orthogonal_gradients_iff_divergence_free | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DiscreteFluidDynamics.pibar_mul_coarseGenerator | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DiscreteFluidDynamics.reversible_iff_no_positive_current_cycle | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DiscreteFluidDynamics.reversible_quotient_of_reversible | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DiscreteFluidDynamics.stationary_current_in_cycle_space | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DiscreteFluidDynamics.stationary_current_orthogonal_gradients | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DiscreteFluidDynamics.stationary_iff_current_divergence_free | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DiscreteFluidDynamics.uniformLift_current_scales | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DiscreteFluidDynamics.uniformLift_quotient_realizes | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DiscreteFluidDynamics.uniformLift_row_sum_block | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DiscreteFluidDynamics.uniformLift_row_sum_zero | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DiscreteFluidDynamics.uniformLift_stationary | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DiscreteFluidDynamics.uniformLift_stronglyLumpable | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DiscreteFluidDynamics.viscous_time_budget | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.HaltingCompiler.cd0_compiled_iff | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.HaltingCompiler.cd0_spinRight | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.HaltingCompiler.evalDom_iff_multistep | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.HaltingCompiler.haltMarkerNat_all_false_iff | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.HaltingCompiler.haltMarkerNat_at_most_once | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.HaltingCompiler.haltMarkerNat_eq_false_of_lt | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.HaltingCompiler.haltMarker_all_false_iff | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.HaltingCompiler.haltMarker_at_most_once | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.HaltingCompiler.halted_of_multistep_none | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.HaltingCompiler.multistep_none_mono | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.HaltingCompiler.multistep_none_succ | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.HaltingCompiler.multistep_of_reaches | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.HaltingCompiler.multistep_succ | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.HaltingCompiler.multistep_zero | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.HaltingCompiler.not_cd0_compiled_iff | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.HaltingCompiler.not_cd0_compiled_of_halts | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.HaltingCompiler.not_cd0_haltNow | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.HaltingCompiler.reaches_of_multistep | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.HaltingCompiler.step_haltNow | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.HaltingCompiler.step_spinRight | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.ValidityHorizon.current_driven_crystal | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.ValidityHorizon.drive_injects_vorticity | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.ValidityHorizon.exp_perturbation_bound | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.ValidityHorizon.killingDefect_driven_crystal | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.ValidityHorizon.no_spontaneous_universality | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.ValidityHorizon.probabilityCurrent_add | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.ValidityHorizon.substrate_alone_is_crystal | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.ValidityHorizon.validity_horizon | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.ValidityHorizon.validity_horizon_inverse_leakage | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Renormalization.CurvatureQuotient.Gamma2Sq_lift_eq | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Renormalization.CurvatureQuotient.Gamma2_lift_eq | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Renormalization.CurvatureQuotient.GammaSq_lift_eq | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Renormalization.CurvatureQuotient.Gamma_lift_eq | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Renormalization.CurvatureQuotient.HasPositiveRicci_quotient | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Renormalization.CurvatureQuotient.RicciCurvatureBound_quotient | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Renormalization.CurvatureQuotient.StarExample.curvature_hiding | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Renormalization.CurvatureQuotient.StarExample.lift_two_valued | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Renormalization.CurvatureQuotient.StarExample.starGen_lumpable | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Renormalization.CurvatureQuotient.StarExample.starGen_not_cd0 | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Renormalization.CurvatureQuotient.StarExample.starP_mk_eq_mk | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Renormalization.CurvatureQuotient.StarExample.starQuotient_cd | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Renormalization.CurvatureQuotient.instNonemptyQuot | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Renormalization.CurvatureQuotient.lift_fun_mul | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Renormalization.CurvatureQuotient.not_RicciCurvatureBound_of_quotient | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Renormalization.KernelHorizon.IsStochastic.nonneg | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Renormalization.KernelHorizon.IsStochastic.row_sum_one | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Renormalization.KernelHorizon.coarseKernel_isStochastic | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Renormalization.KernelHorizon.commutator_columns_centered | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Renormalization.KernelHorizon.eternal_closure_of_zero_commutator | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Renormalization.KernelHorizon.kernel_closure_error_le | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Renormalization.KernelHorizon.kernel_closure_error_le_geom | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Renormalization.KernelHorizon.kernel_closure_error_le_uniform | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Renormalization.KernelHorizon.lift_matrix_linfty_le_one | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Renormalization.KernelHorizon.linfty_opNorm_le_one_of_rows | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Renormalization.KernelHorizon.linfty_opNorm_le_one_of_stochastic | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Renormalization.KernelHorizon.stochastic_pow_norm_le_one | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Renormalization.KernelHorizon.sum_row_sum_block | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Renormalization.KernelHorizon.within_tolerance_of_defect_small | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Approximate.CoarseGeneratorMatrix.congr_simp | 9 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Approximate.NCD_uniform_error_bound | 17 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Approximate.PropagatorDiff_eq_proj_trajectory_diff | 18 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Approximate.coarseGen_mul_proj | 9 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Approximate.proj_commutes_heatKernel_coarseGen | 10 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Approximate.proj_swap_heatKernelMap_coarseGen | 15 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Approximate.propagator_approximation_bound | 24 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Approximate.spectral_stability_reversible | 24 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Approximate.trajectory_closure_bound | 22 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Approximate.trajectory_norm_bound_uniform | 6 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Approximate.vertical_error_bound | 20 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.AbstractBKM.bounded_of_budget_le | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.AbstractBKM.budget_zero | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.AbstractBKM.exists_budget_gt_of_norm_gt | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.AbstractBKM.hasDerivAt_budget | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.AbstractBKM.norm_le_barrier_of_budget_control | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.AbstractBKM.norm_le_exp_budget | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.CantorShiftTower.row_sum_block_one | 7 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.CantorShiftTower.row_sum_block_sub | 7 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.CantorShiftTower.shiftGenerator_row_sum_zero | 4 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.CantorShiftTower.shiftGenerator_stronglyLumpable | 14 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.CantorShiftTower.shiftKernel_nonneg | 3 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.CantorShiftTower.shiftKernel_row_sum | 3 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.CantorShiftTower.shiftKernel_row_sum_block | 13 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.CantorShiftTower.shiftTower_defect_zero | 13 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.CantorShiftTower.shiftTower_eternal_closure | 16 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.CantorShiftTower.shiftTower_quotient_realizes | 14 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.CantorShiftTower.shiftTower_stronglyLumpable | 13 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.CantorShiftTower.tailPartition_quot_map_eq_iff | 8 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.CantorShiftTower.tail_shiftIn | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.CantorShiftTower.truncate_pathShift | 4 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.CurvatureUndecidability.cd0_haltW_iff | 6 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.CurvatureUndecidability.cd0_unitW | 6 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.CurvatureUndecidability.gam2_heavy_eq | 5 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.CurvatureUndecidability.gam2_unitW_eq | 5 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.CurvatureUndecidability.haltW_eq_four | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.CurvatureUndecidability.haltW_eq_one | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.CurvatureUndecidability.haltW_eq_unitW | 3 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.CurvatureUndecidability.not_cd0_haltW_of_halts | 6 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.CurvatureUndecidability.not_cd0_of_heavy_edge | 5 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.CurvatureUndecidability.wit_add_one | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.CurvatureUndecidability.wit_add_two | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.CurvatureUndecidability.wit_self | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.CurvatureUndecidability.wit_sub_one | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.CurvatureUndecidability.wit_sub_two | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.HeatKernel_opNorm_bound_proved | 7 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.coarseGeneratorMatrix_mul_proj | 9 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.coarseProj_fixes_coarse_heatKernel | 15 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.defectComplement_mul_proj | 9 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.defectComplement_mul_proj_eq_coarse | 10 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.defectComplement_pow_mul_proj | 10 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.defectMatrix_mulVec | 14 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.defectMatrix_toLin | 14 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.defect_eq_validity_leakage | 62 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.defect_horizon_bound | 22 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.exp_defectComplement_apply | 16 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.exp_defectComplement_mul_proj | 10 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.exp_piMat_eq | 50 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.heatKernel_opNorm_explicit | 7 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.instCompleteSpacePiMat | 48 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.instFiniteDimensionalRealPiMat | 3 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.instNormOneClassPiMatOfNonempty | 48 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.mulProjLin_continuous | 59 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.norm_pi_neg | 3 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.norm_pi_nonneg' | 3 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.norm_sq_pi_proj_pythagorean | 12 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.opNorm_exp_eq_pmNorm | 50 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.pmNorm_add_le | 10 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.pmNorm_def | 45 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.pmNorm_eq_zero | 10 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.pmNorm_mulVec_le | 9 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.pmNorm_mul_le | 10 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.pmNorm_neg | 10 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.pmNorm_nonneg | 9 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.pmNorm_smul_le | 11 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.pmNorm_zero | 10 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.proj_mul_coarseGen | 9 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.smul_defectComplement_pow_mul_proj | 10 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.toMatLin_continuous | 51 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.total_error_pythagorean | 17 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.trajectory_closure_bound_explicit | 23 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.vertical_closure_bound_explicit | 22 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DefectHorizonBridge.vertical_defect_horizon_bound | 21 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DiscreteFluidDynamics.coarse_current_eq_sum_fine | 10 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DiscreteFluidDynamics.current_zero_iff_reversible | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DiscreteFluidDynamics.cycle_of_pos_cycleSpace_field | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DiscreteFluidDynamics.divergence_current_eq_neg_residual | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DiscreteFluidDynamics.edgeInner_gradient_eq | 3 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DiscreteFluidDynamics.fiberPartition_quot_map_eq_iff | 6 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DiscreteFluidDynamics.killingDefect_eq_edgeInner_self | 3 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DiscreteFluidDynamics.killingDefect_eq_four_antisym | 3 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DiscreteFluidDynamics.killingDefect_eq_zero_iff_reversible | 3 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DiscreteFluidDynamics.killingDefect_nonneg | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DiscreteFluidDynamics.killingDefect_pos_iff_positive_current_cycle | 3 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DiscreteFluidDynamics.ness_has_current_cycle | 3 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DiscreteFluidDynamics.ness_quotient_forces_ness_fine | 10 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DiscreteFluidDynamics.orthogonal_gradients_iff_divergence_free | 3 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DiscreteFluidDynamics.pibar_mul_coarseGenerator | 9 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DiscreteFluidDynamics.reversible_iff_no_positive_current_cycle | 3 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DiscreteFluidDynamics.reversible_quotient_of_reversible | 10 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DiscreteFluidDynamics.stationary_current_in_cycle_space | 4 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DiscreteFluidDynamics.stationary_current_orthogonal_gradients | 4 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DiscreteFluidDynamics.stationary_iff_current_divergence_free | 3 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DiscreteFluidDynamics.uniformLift_current_scales | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DiscreteFluidDynamics.uniformLift_quotient_realizes | 11 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DiscreteFluidDynamics.uniformLift_row_sum_block | 10 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DiscreteFluidDynamics.uniformLift_row_sum_zero | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DiscreteFluidDynamics.uniformLift_stationary | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DiscreteFluidDynamics.uniformLift_stronglyLumpable | 10 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.HaltingCompiler.cd0_compiled_iff | 10 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.HaltingCompiler.cd0_spinRight | 11 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.HaltingCompiler.evalDom_iff_multistep | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.HaltingCompiler.haltMarkerNat_all_false_iff | 3 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.HaltingCompiler.haltMarkerNat_at_most_once | 3 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.HaltingCompiler.haltMarkerNat_eq_false_of_lt | 3 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.HaltingCompiler.haltMarker_all_false_iff | 4 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.HaltingCompiler.haltMarker_at_most_once | 4 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.HaltingCompiler.halted_of_multistep_none | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.HaltingCompiler.multistep_none_mono | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.HaltingCompiler.multistep_none_succ | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.HaltingCompiler.multistep_of_reaches | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.HaltingCompiler.multistep_succ | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.HaltingCompiler.multistep_zero | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.HaltingCompiler.not_cd0_compiled_iff | 10 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.HaltingCompiler.not_cd0_compiled_of_halts | 10 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.HaltingCompiler.not_cd0_haltNow | 11 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.HaltingCompiler.reaches_of_multistep | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.HaltingCompiler.step_haltNow | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.HaltingCompiler.step_spinRight | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.ValidityHorizon.current_driven_crystal | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.ValidityHorizon.drive_injects_vorticity | 4 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.ValidityHorizon.killingDefect_driven_crystal | 3 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.ValidityHorizon.no_spontaneous_universality | 20 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.ValidityHorizon.probabilityCurrent_add | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.ValidityHorizon.substrate_alone_is_crystal | 4 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Renormalization.CurvatureQuotient.Gamma2Sq_lift_eq | 14 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Renormalization.CurvatureQuotient.Gamma2_lift_eq | 13 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Renormalization.CurvatureQuotient.GammaSq_lift_eq | 13 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Renormalization.CurvatureQuotient.Gamma_lift_eq | 12 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Renormalization.CurvatureQuotient.HasPositiveRicci_quotient | 12 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Renormalization.CurvatureQuotient.RicciCurvatureBound_quotient | 11 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Renormalization.CurvatureQuotient.StarExample.curvature_hiding | 15 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Renormalization.CurvatureQuotient.StarExample.lift_two_valued | 8 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Renormalization.CurvatureQuotient.StarExample.starGen_lumpable | 11 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Renormalization.CurvatureQuotient.StarExample.starGen_not_cd0 | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Renormalization.CurvatureQuotient.StarExample.starP_mk_eq_mk | 5 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Renormalization.CurvatureQuotient.StarExample.starQuotient_cd | 14 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Renormalization.CurvatureQuotient.instNonemptyQuot | 3 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Renormalization.CurvatureQuotient.lift_fun_mul | 5 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Renormalization.CurvatureQuotient.not_RicciCurvatureBound_of_quotient | 11 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Renormalization.KernelHorizon.IsStochastic.nonneg | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Renormalization.KernelHorizon.IsStochastic.row_sum_one | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Renormalization.KernelHorizon.coarseKernel_isStochastic | 11 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Renormalization.KernelHorizon.commutator_columns_centered | 12 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Renormalization.KernelHorizon.eternal_closure_of_zero_commutator | 12 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Renormalization.KernelHorizon.kernel_closure_error_le | 13 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Renormalization.KernelHorizon.kernel_closure_error_le_geom | 13 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Renormalization.KernelHorizon.kernel_closure_error_le_uniform | 13 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Renormalization.KernelHorizon.lift_matrix_linfty_le_one | 8 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Renormalization.KernelHorizon.linfty_opNorm_le_one_of_stochastic | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Renormalization.KernelHorizon.stochastic_pow_norm_le_one | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Renormalization.KernelHorizon.sum_row_sum_block | 8 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Renormalization.KernelHorizon.within_tolerance_of_defect_small | 13 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F09 | UNUSED_HYPOTHESIS | SGC.Bridge.DiscreteFluidDynamics.damped_validity_budget | hypothesis `_hε` never occurs in the proof term; the statement may be over-constrained or mis-stated |

## Per-theorem receipt

### `SGC.Approximate.CoarseGeneratorMatrix.congr_simp`

- statement (kernel-elaborated, sha256 `d8e2488c0fa463ac`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L L_1 : Matrix V V ℝ), L = L_1 → ∀ (P P_1 : SGC.Partition V), P = P_1 → ∀ (pi_dist pi_dist_1 : V → ℝ) (e_pi_dist : pi_dist = pi_dist_1) (_hπ : ∀ (v : V), 0 < pi_dist v) (a a_1 : V), a = a_1 → ∀ (a_2 a_3 : V), a_2 = a_3 → SGC.Approximate.CoarseGeneratorMatrix L P pi_dist _hπ a a_2 = SGC.Approximate.CoarseGeneratorMatrix L_1 P_1 pi_dist_1 ⋯ a_1 a_3

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Approximate.CoarseGeneratorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.Approximate.CoarseProjectorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`  [ignores hπ]
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Approximate.NCD_uniform_error_bound`

- statement (kernel-elaborated, sha256 `5b27d6af009e3803`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] [Nonempty V] (L L_fast L_slow : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (ε γ : ℝ), SGC.Approximate.IsNCD L L_fast L_slow P pi_dist hπ ε γ → ∀ (t : ℝ), 0 ≤ t → ∀ (f₀ : V → ℝ), f₀ = (SGC.Approximate.CoarseProjector P pi_dist hπ) f₀ → ∃ C ≥ 0, SGC.norm_pi pi_dist ((SGC.Approximate.HeatKernelMap L t) f₀ - (SGC.Approximate.CoarseProjector P pi_dist hπ) ((SGC.Approximate.HeatKernelMap L t) f₀)) ≤ ε / γ * C * SGC.norm_pi pi_dist f₀

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], SGC.Approximate.NCD_defect_split [project], SGC.Approximate.NCD_integral_bound [project], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Approximate.IsNCD` (inductive, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → Matrix V V ℝ → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ℝ → ℝ → Prop`
    - `SGC.Approximate.CoarseProjector` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.norm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Approximate.HeatKernelMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.lift_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → (P.Quot → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Q_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] P.Quot → ℝ`  [ignores _hπ]
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.HeatKernel` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → Matrix V V ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Approximate.PropagatorDiff_eq_proj_trajectory_diff`

- statement (kernel-elaborated, sha256 `cc875fc5c99942f3`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] [Nonempty V] (L : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (t : ℝ) (f : V → ℝ), (SGC.Approximate.PropagatorDiff L P pi_dist hπ t) f = (SGC.Approximate.CoarseProjector P pi_dist hπ) ((SGC.Approximate.HeatKernelMap L t) ((SGC.Approximate.CoarseProjector P pi_dist hπ) f) - (SGC.Approximate.HeatKernelMap (SGC.Approximate.CoarseGeneratorMatrix L P pi_dist hπ) t) ((SGC.Approximate.CoarseProjector P pi_dist hπ) f))

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Approximate.PropagatorDiff` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.CoarseProjector` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.HeatKernelMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.CoarseGeneratorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.Approximate.EffectivePropagator` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.CoarsePropagatorLifted` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.lift_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → (P.Quot → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Q_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] P.Quot → ℝ`  [ignores _hπ]
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.HeatKernel` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → Matrix V V ℝ`
    - `SGC.Approximate.CoarseProjectorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`  [ignores hπ]
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Approximate.coarseGen_mul_proj`

- statement (kernel-elaborated, sha256 `e087bbc59e9215a8`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] [Nonempty V] (L : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v), SGC.Approximate.CoarseGeneratorMatrix L P pi_dist hπ * SGC.Approximate.CoarseProjectorMatrix P pi_dist hπ = SGC.Approximate.CoarseGeneratorMatrix L P pi_dist hπ

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Approximate.CoarseGeneratorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.Approximate.CoarseProjectorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`  [ignores hπ]
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Approximate.proj_commutes_heatKernel_coarseGen`

- statement (kernel-elaborated, sha256 `ea366575e4a63894`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] [Nonempty V] (L : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (t : ℝ), SGC.Approximate.CoarseProjectorMatrix P pi_dist hπ * SGC.Approximate.HeatKernel (SGC.Approximate.CoarseGeneratorMatrix L P pi_dist hπ) t = SGC.Approximate.HeatKernel (SGC.Approximate.CoarseGeneratorMatrix L P pi_dist hπ) t * SGC.Approximate.CoarseProjectorMatrix P pi_dist hπ

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Approximate.CoarseProjectorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`  [ignores hπ]
    - `SGC.Approximate.HeatKernel` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → Matrix V V ℝ`
    - `SGC.Approximate.CoarseGeneratorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Approximate.proj_swap_heatKernelMap_coarseGen`

- statement (kernel-elaborated, sha256 `a72fc1f4bc861010`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] [Nonempty V] (L : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (t : ℝ) (g : V → ℝ), (SGC.Approximate.CoarseProjector P pi_dist hπ) ((SGC.Approximate.HeatKernelMap (SGC.Approximate.CoarseGeneratorMatrix L P pi_dist hπ) t) g) = (SGC.Approximate.HeatKernelMap (SGC.Approximate.CoarseGeneratorMatrix L P pi_dist hπ) t) ((SGC.Approximate.CoarseProjector P pi_dist hπ) g)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Approximate.CoarseProjector` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.HeatKernelMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.CoarseGeneratorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.lift_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → (P.Quot → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Q_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] P.Quot → ℝ`  [ignores _hπ]
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.HeatKernel` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → Matrix V V ℝ`
    - `SGC.Approximate.CoarseProjectorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`  [ignores hπ]
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Approximate.propagator_approximation_bound`

- statement (kernel-elaborated, sha256 `eaeb857e0917bfc5`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] [Nonempty V] (L : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (ε : ℝ), 0 ≤ ε → SGC.Approximate.IsApproxLumpable L P pi_dist hπ ε → ∀ (t : ℝ), 0 ≤ t → ∃ C ≥ 0, SGC.opNorm_pi pi_dist hπ (SGC.Approximate.PropagatorDiff L P pi_dist hπ t) ≤ ε * t * C

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Approximate.IsApproxLumpable` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ℝ → Prop`
    - `SGC.opNorm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → ℝ`
    - `SGC.Approximate.PropagatorDiff` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.DefectOperator` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.opNorm_set` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → Set ℝ`  [ignores _h_pos]
    - `SGC.Approximate.EffectivePropagator` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.CoarsePropagatorLifted` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.CoarseProjector` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.norm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Approximate.HeatKernel` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → Matrix V V ℝ`
    - `SGC.Approximate.CoarseGeneratorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.lift_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → (P.Quot → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Q_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] P.Quot → ℝ`  [ignores _hπ]
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Approximate.CoarseProjectorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`  [ignores hπ]
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Approximate.spectral_stability_reversible`

- statement (kernel-elaborated, sha256 `0f61121c1f32ea28`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] [Nonempty V] (L : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (ε : ℝ), 0 ≤ ε → SGC.Approximate.IsApproxLumpable L P pi_dist hπ ε → ∀ (t : ℝ), 0 ≤ t → ∀ (k : ℕ), SGC.Approximate.IsSelfAdjoint_pi (SGC.Approximate.EffectivePropagator L P pi_dist hπ t) pi_dist → SGC.Approximate.IsSelfAdjoint_pi (SGC.Approximate.CoarsePropagatorLifted L P pi_dist hπ t) pi_dist → ∃ C eigenvalue_k, C ≥ 0 ∧ |eigenvalue_k (SGC.Approximate.EffectivePropagator L P pi_dist hπ t) - eigenvalue_k (SGC.Approximate.CoarsePropagatorLifted L P pi_dist hπ t)| ≤ ε * t * C

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], SGC.Approximate.Weyl_inequality_pi [project], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Approximate.IsApproxLumpable` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ℝ → Prop`
    - `SGC.Approximate.IsSelfAdjoint_pi` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → ((V → ℝ) →ₗ[ℝ] V → ℝ) → (V → ℝ) → Prop`
    - `SGC.Approximate.EffectivePropagator` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.CoarsePropagatorLifted` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.opNorm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → ℝ`
    - `SGC.Approximate.DefectOperator` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Approximate.CoarseProjector` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.HeatKernel` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → Matrix V V ℝ`
    - `SGC.Approximate.CoarseGeneratorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.opNorm_set` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → Set ℝ`  [ignores _h_pos]
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.lift_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → (P.Quot → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Q_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] P.Quot → ℝ`  [ignores _hπ]
    - `SGC.Approximate.CoarseProjectorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`  [ignores hπ]
    - `SGC.norm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Approximate.trajectory_closure_bound`

- statement (kernel-elaborated, sha256 `aa327073456754f3`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] [Nonempty V] (L : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (ε : ℝ), 0 ≤ ε → SGC.Approximate.IsApproxLumpable L P pi_dist hπ ε → ∀ (t : ℝ), 0 ≤ t → ∃ C ≥ 0, ∀ (f₀ : V → ℝ), f₀ = (SGC.Approximate.CoarseProjector P pi_dist hπ) f₀ → SGC.norm_pi pi_dist ((SGC.Approximate.HeatKernelMap L t) f₀ - (SGC.Approximate.HeatKernelMap (SGC.Approximate.CoarseGeneratorMatrix L P pi_dist hπ) t) f₀) ≤ ε * t * C * SGC.norm_pi pi_dist f₀

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: hε
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Approximate.IsApproxLumpable` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ℝ → Prop`
    - `SGC.Approximate.CoarseProjector` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.norm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Approximate.HeatKernelMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.CoarseGeneratorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.opNorm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → ℝ`
    - `SGC.Approximate.DefectOperator` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.lift_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → (P.Quot → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Q_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] P.Quot → ℝ`  [ignores _hπ]
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.HeatKernel` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → Matrix V V ℝ`
    - `SGC.Approximate.CoarseProjectorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`  [ignores hπ]
    - `SGC.opNorm_set` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → Set ℝ`  [ignores _h_pos]
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Approximate.trajectory_norm_bound_uniform`

- statement (kernel-elaborated, sha256 `72676cf8e00e6f01`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] [Nonempty V] (L : Matrix V V ℝ) (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f₀ : V → ℝ) (T : ℝ), 0 ≤ T → ∃ B ≥ 1, ∀ (s : ℝ), 0 ≤ s → s ≤ T → SGC.norm_pi pi_dist ((SGC.Approximate.HeatKernelMap L s) f₀) ≤ B * SGC.norm_pi pi_dist f₀

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.norm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Approximate.HeatKernelMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.HeatKernel` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → Matrix V V ℝ`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`

### `SGC.Approximate.vertical_error_bound`

- statement (kernel-elaborated, sha256 `d4e530f90648a1fa`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] [Nonempty V] (L : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (ε : ℝ), 0 ≤ ε → SGC.Approximate.IsApproxLumpable L P pi_dist hπ ε → ∀ (t : ℝ), 0 ≤ t → ∀ (f₀ : V → ℝ), f₀ = (SGC.Approximate.CoarseProjector P pi_dist hπ) f₀ → ∃ C ≥ 0, SGC.norm_pi pi_dist ((SGC.Approximate.HeatKernelMap L t) f₀ - (SGC.Approximate.CoarseProjector P pi_dist hπ) ((SGC.Approximate.HeatKernelMap L t) f₀)) ≤ ε * t * C * SGC.norm_pi pi_dist f₀

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: hε
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Approximate.IsApproxLumpable` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ℝ → Prop`
    - `SGC.Approximate.CoarseProjector` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.norm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Approximate.HeatKernelMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.opNorm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → ℝ`
    - `SGC.Approximate.DefectOperator` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.lift_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → (P.Quot → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Q_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] P.Quot → ℝ`  [ignores _hπ]
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.HeatKernel` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → Matrix V V ℝ`
    - `SGC.opNorm_set` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → Set ℝ`  [ignores _h_pos]
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.AbstractBKM.bounded_of_budget_le`

- statement (kernel-elaborated, sha256 `700aa96445b3b2cc`):

      ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {x x' : ℝ → E} {W : ℝ → ℝ} {T M : ℝ}, Continuous W → ContinuousOn x (Set.Icc 0 T) → (∀ t ∈ Set.Ico 0 T, HasDerivWithinAt x (x' t) (Set.Ici t) t) → (∀ t ∈ Set.Ico 0 T, ‖x' t‖ ≤ W t * ‖x t‖) → (∀ t ∈ Set.Icc 0 T, SGC.Bridge.AbstractBKM.budget W t ≤ M) → ∀ t ∈ Set.Icc 0 T, ‖x t‖ ≤ Real.exp M * ‖x 0‖

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.AbstractBKM.budget` (def, SGC.Bridge.AbstractBKM): `(ℝ → ℝ) → ℝ → ℝ`

### `SGC.Bridge.AbstractBKM.budget_zero`

- statement (kernel-elaborated, sha256 `c2af994425cb26f7`):

      ∀ (W : ℝ → ℝ), SGC.Bridge.AbstractBKM.budget W 0 = 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=simp vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.AbstractBKM.budget` (def, SGC.Bridge.AbstractBKM): `(ℝ → ℝ) → ℝ → ℝ`

### `SGC.Bridge.AbstractBKM.exists_budget_gt_of_norm_gt`

- statement (kernel-elaborated, sha256 `3e80fe2f31f6a05f`):

      ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {x x' : ℝ → E} {W : ℝ → ℝ} {T M : ℝ}, Continuous W → ContinuousOn x (Set.Icc 0 T) → (∀ t ∈ Set.Ico 0 T, HasDerivWithinAt x (x' t) (Set.Ici t) t) → (∀ t ∈ Set.Ico 0 T, ‖x' t‖ ≤ W t * ‖x t‖) → (∃ t ∈ Set.Icc 0 T, Real.exp M * ‖x 0‖ < ‖x t‖) → ∃ t ∈ Set.Icc 0 T, M < SGC.Bridge.AbstractBKM.budget W t

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.AbstractBKM.budget` (def, SGC.Bridge.AbstractBKM): `(ℝ → ℝ) → ℝ → ℝ`

### `SGC.Bridge.AbstractBKM.hasDerivAt_budget`

- statement (kernel-elaborated, sha256 `1ec22d1b0313e60a`):

      ∀ {W : ℝ → ℝ}, Continuous W → ∀ (t : ℝ), HasDerivAt (SGC.Bridge.AbstractBKM.budget W) (W t) t

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.AbstractBKM.budget` (def, SGC.Bridge.AbstractBKM): `(ℝ → ℝ) → ℝ → ℝ`

### `SGC.Bridge.AbstractBKM.norm_le_barrier_of_budget_control`

- statement (kernel-elaborated, sha256 `b566ea5137155ed5`):

      ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {x x' : ℝ → E} {W : ℝ → ℝ} {T : ℝ}, Continuous W → ContinuousOn x (Set.Icc 0 T) → (∀ t ∈ Set.Ico 0 T, HasDerivWithinAt x (x' t) (Set.Ici t) t) → (∀ t ∈ Set.Ico 0 T, ‖x' t‖ ≤ W t * ‖x t‖) → ∀ {ε : ℝ}, 0 < ε → ∀ t ∈ Set.Icc 0 T, ‖x t‖ ≤ Real.exp (SGC.Bridge.AbstractBKM.budget W t) * (‖x 0‖ + ε * Real.exp t)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.AbstractBKM.budget` (def, SGC.Bridge.AbstractBKM): `(ℝ → ℝ) → ℝ → ℝ`

### `SGC.Bridge.AbstractBKM.norm_le_exp_budget`

- statement (kernel-elaborated, sha256 `740a38effe89ce4c`):

      ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {x x' : ℝ → E} {W : ℝ → ℝ} {T : ℝ}, Continuous W → ContinuousOn x (Set.Icc 0 T) → (∀ t ∈ Set.Ico 0 T, HasDerivWithinAt x (x' t) (Set.Ici t) t) → (∀ t ∈ Set.Ico 0 T, ‖x' t‖ ≤ W t * ‖x t‖) → ∀ t ∈ Set.Icc 0 T, ‖x t‖ ≤ Real.exp (SGC.Bridge.AbstractBKM.budget W t) * ‖x 0‖

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.AbstractBKM.budget` (def, SGC.Bridge.AbstractBKM): `(ℝ → ℝ) → ℝ → ℝ`

### `SGC.Bridge.CantorShiftTower.row_sum_block_one`

- statement (kernel-elaborated, sha256 `e55fed5273438fd5`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (P : SGC.Partition V) (i : V) (Bq : P.Quot), SGC.row_sum_block 1 P i Bq = if P.quot_map i = Bq then 1 else 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.row_sum_block` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → V → P.Quot → ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.CantorShiftTower.row_sum_block_sub`

- statement (kernel-elaborated, sha256 `e5b4546805d8b98d`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (A B : Matrix V V ℝ) (P : SGC.Partition V) (i : V) (Bq : P.Quot), SGC.row_sum_block (A - B) P i Bq = SGC.row_sum_block A P i Bq - SGC.row_sum_block B P i Bq

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.row_sum_block` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → V → P.Quot → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.CantorShiftTower.shiftGenerator_row_sum_zero`

- statement (kernel-elaborated, sha256 `ca18854db1af6ce0`):

      ∀ (p n : ℕ) [NeZero p] (w : SGC.Bridge.CantorShiftTower.Word p n), ∑ w', SGC.Bridge.CantorShiftTower.shiftGenerator p n w w' = 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.CantorShiftTower.Word` (def, SGC.Bridge.CantorShiftTower): `ℕ → ℕ → Type`
    - `SGC.Bridge.CantorShiftTower.shiftGenerator` (def, SGC.Bridge.CantorShiftTower): `(p n : ℕ) → Matrix (SGC.Bridge.CantorShiftTower.Word p n) (SGC.Bridge.CantorShiftTower.Word p n) ℝ`
    - `SGC.Bridge.CantorShiftTower.shiftKernel` (def, SGC.Bridge.CantorShiftTower): `(p n : ℕ) → Matrix (SGC.Bridge.CantorShiftTower.Word p n) (SGC.Bridge.CantorShiftTower.Word p n) ℝ`
    - `SGC.Bridge.CantorShiftTower.shiftIn` (def, SGC.Bridge.CantorShiftTower): `{A : Type u_1} → {n : ℕ} → (Fin n → A) → A → Fin n → A`

### `SGC.Bridge.CantorShiftTower.shiftGenerator_stronglyLumpable`

- statement (kernel-elaborated, sha256 `0839ee9fc035e8ca`):

      ∀ (p n : ℕ), SGC.IsStronglyLumpable (SGC.Bridge.CantorShiftTower.shiftGenerator p n.succ) (SGC.Bridge.CantorShiftTower.tailPartition p n)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.IsStronglyLumpable` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → Prop`
    - `SGC.Bridge.CantorShiftTower.Word` (def, SGC.Bridge.CantorShiftTower): `ℕ → ℕ → Type`
    - `SGC.Bridge.CantorShiftTower.shiftGenerator` (def, SGC.Bridge.CantorShiftTower): `(p n : ℕ) → Matrix (SGC.Bridge.CantorShiftTower.Word p n) (SGC.Bridge.CantorShiftTower.Word p n) ℝ`
    - `SGC.Bridge.CantorShiftTower.tailPartition` (def, SGC.Bridge.CantorShiftTower): `(p n : ℕ) → SGC.Partition (SGC.Bridge.CantorShiftTower.Word p (n + 1))`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Bridge.CantorShiftTower.shiftKernel` (def, SGC.Bridge.CantorShiftTower): `(p n : ℕ) → Matrix (SGC.Bridge.CantorShiftTower.Word p n) (SGC.Bridge.CantorShiftTower.Word p n) ℝ`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Bridge.CantorShiftTower.tail` (def, SGC.Bridge.CantorShiftTower): `{A : Type u_1} → {n : ℕ} → (Fin (n + 1) → A) → Fin n → A`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Bridge.CantorShiftTower.shiftIn` (def, SGC.Bridge.CantorShiftTower): `{A : Type u_1} → {n : ℕ} → (Fin n → A) → A → Fin n → A`

### `SGC.Bridge.CantorShiftTower.shiftKernel_nonneg`

- statement (kernel-elaborated, sha256 `72c8d3dadd6c3f07`):

      ∀ (p n : ℕ) (w w' : SGC.Bridge.CantorShiftTower.Word p n), 0 ≤ SGC.Bridge.CantorShiftTower.shiftKernel p n w w'

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.CantorShiftTower.Word` (def, SGC.Bridge.CantorShiftTower): `ℕ → ℕ → Type`
    - `SGC.Bridge.CantorShiftTower.shiftKernel` (def, SGC.Bridge.CantorShiftTower): `(p n : ℕ) → Matrix (SGC.Bridge.CantorShiftTower.Word p n) (SGC.Bridge.CantorShiftTower.Word p n) ℝ`
    - `SGC.Bridge.CantorShiftTower.shiftIn` (def, SGC.Bridge.CantorShiftTower): `{A : Type u_1} → {n : ℕ} → (Fin n → A) → A → Fin n → A`

### `SGC.Bridge.CantorShiftTower.shiftKernel_row_sum`

- statement (kernel-elaborated, sha256 `bcc41c6443dd1411`):

      ∀ (p n : ℕ) [NeZero p] (w : SGC.Bridge.CantorShiftTower.Word p n), ∑ w', SGC.Bridge.CantorShiftTower.shiftKernel p n w w' = 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.CantorShiftTower.Word` (def, SGC.Bridge.CantorShiftTower): `ℕ → ℕ → Type`
    - `SGC.Bridge.CantorShiftTower.shiftKernel` (def, SGC.Bridge.CantorShiftTower): `(p n : ℕ) → Matrix (SGC.Bridge.CantorShiftTower.Word p n) (SGC.Bridge.CantorShiftTower.Word p n) ℝ`
    - `SGC.Bridge.CantorShiftTower.shiftIn` (def, SGC.Bridge.CantorShiftTower): `{A : Type u_1} → {n : ℕ} → (Fin n → A) → A → Fin n → A`

### `SGC.Bridge.CantorShiftTower.shiftKernel_row_sum_block`

- statement (kernel-elaborated, sha256 `6919dc4ccc5b3393`):

      ∀ (p n : ℕ) (u : SGC.Bridge.CantorShiftTower.Word p (n + 1)) (B : (SGC.Bridge.CantorShiftTower.tailPartition p n).Quot), SGC.row_sum_block (SGC.Bridge.CantorShiftTower.shiftKernel p (n + 1)) (SGC.Bridge.CantorShiftTower.tailPartition p n) u B = SGC.Bridge.CantorShiftTower.shiftKernel p n (SGC.Bridge.CantorShiftTower.tail u) (SGC.Bridge.CantorShiftTower.tail (Quotient.out B))

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.CantorShiftTower.Word` (def, SGC.Bridge.CantorShiftTower): `ℕ → ℕ → Type`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.CantorShiftTower.tailPartition` (def, SGC.Bridge.CantorShiftTower): `(p n : ℕ) → SGC.Partition (SGC.Bridge.CantorShiftTower.Word p (n + 1))`
    - `SGC.row_sum_block` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → V → P.Quot → ℝ`
    - `SGC.Bridge.CantorShiftTower.shiftKernel` (def, SGC.Bridge.CantorShiftTower): `(p n : ℕ) → Matrix (SGC.Bridge.CantorShiftTower.Word p n) (SGC.Bridge.CantorShiftTower.Word p n) ℝ`
    - `SGC.Bridge.CantorShiftTower.tail` (def, SGC.Bridge.CantorShiftTower): `{A : Type u_1} → {n : ℕ} → (Fin (n + 1) → A) → Fin n → A`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Bridge.CantorShiftTower.shiftIn` (def, SGC.Bridge.CantorShiftTower): `{A : Type u_1} → {n : ℕ} → (Fin n → A) → A → Fin n → A`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.CantorShiftTower.shiftTower_defect_zero`

- statement (kernel-elaborated, sha256 `5d7109561670714d`):

      ∀ (p n : ℕ), SGC.IsRowSumApproxLumpable (SGC.Bridge.CantorShiftTower.shiftKernel p (n + 1)) (SGC.Bridge.CantorShiftTower.tailPartition p n) 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.IsRowSumApproxLumpable` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → ℝ → Prop`
    - `SGC.Bridge.CantorShiftTower.Word` (def, SGC.Bridge.CantorShiftTower): `ℕ → ℕ → Type`
    - `SGC.Bridge.CantorShiftTower.shiftKernel` (def, SGC.Bridge.CantorShiftTower): `(p n : ℕ) → Matrix (SGC.Bridge.CantorShiftTower.Word p n) (SGC.Bridge.CantorShiftTower.Word p n) ℝ`
    - `SGC.Bridge.CantorShiftTower.tailPartition` (def, SGC.Bridge.CantorShiftTower): `(p n : ℕ) → SGC.Partition (SGC.Bridge.CantorShiftTower.Word p (n + 1))`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Bridge.CantorShiftTower.shiftIn` (def, SGC.Bridge.CantorShiftTower): `{A : Type u_1} → {n : ℕ} → (Fin n → A) → A → Fin n → A`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Bridge.CantorShiftTower.tail` (def, SGC.Bridge.CantorShiftTower): `{A : Type u_1} → {n : ℕ} → (Fin (n + 1) → A) → Fin n → A`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.CantorShiftTower.shiftTower_eternal_closure`

- statement (kernel-elaborated, sha256 `fbe4240d1768870e`):

      ∀ (p n m : ℕ), SGC.Bridge.CantorShiftTower.shiftKernel p (n + 1) ^ m * SGC.lift_matrix (SGC.Bridge.CantorShiftTower.tailPartition p n) = SGC.lift_matrix (SGC.Bridge.CantorShiftTower.tailPartition p n) * SGC.QuotientGeneratorSimple (SGC.Bridge.CantorShiftTower.shiftKernel p (n + 1)) (SGC.Bridge.CantorShiftTower.tailPartition p n) ^ m

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.CantorShiftTower.Word` (def, SGC.Bridge.CantorShiftTower): `ℕ → ℕ → Type`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.CantorShiftTower.tailPartition` (def, SGC.Bridge.CantorShiftTower): `(p n : ℕ) → SGC.Partition (SGC.Bridge.CantorShiftTower.Word p (n + 1))`
    - `SGC.Bridge.CantorShiftTower.shiftKernel` (def, SGC.Bridge.CantorShiftTower): `(p n : ℕ) → Matrix (SGC.Bridge.CantorShiftTower.Word p n) (SGC.Bridge.CantorShiftTower.Word p n) ℝ`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.QuotientGeneratorSimple` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Bridge.CantorShiftTower.tail` (def, SGC.Bridge.CantorShiftTower): `{A : Type u_1} → {n : ℕ} → (Fin (n + 1) → A) → Fin n → A`
    - `SGC.Bridge.CantorShiftTower.shiftIn` (def, SGC.Bridge.CantorShiftTower): `{A : Type u_1} → {n : ℕ} → (Fin n → A) → A → Fin n → A`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.row_sum_block` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → V → P.Quot → ℝ`

### `SGC.Bridge.CantorShiftTower.shiftTower_quotient_realizes`

- statement (kernel-elaborated, sha256 `d1ed638f4cbe42ce`):

      ∀ (p n : ℕ) (u u' : SGC.Bridge.CantorShiftTower.Word p (n + 1)), SGC.QuotientGeneratorSimple (SGC.Bridge.CantorShiftTower.shiftKernel p (n + 1)) (SGC.Bridge.CantorShiftTower.tailPartition p n) ((SGC.Bridge.CantorShiftTower.tailPartition p n).quot_map u) ((SGC.Bridge.CantorShiftTower.tailPartition p n).quot_map u') = SGC.Bridge.CantorShiftTower.shiftKernel p n (SGC.Bridge.CantorShiftTower.tail u) (SGC.Bridge.CantorShiftTower.tail u')

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.CantorShiftTower.Word` (def, SGC.Bridge.CantorShiftTower): `ℕ → ℕ → Type`
    - `SGC.QuotientGeneratorSimple` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Bridge.CantorShiftTower.shiftKernel` (def, SGC.Bridge.CantorShiftTower): `(p n : ℕ) → Matrix (SGC.Bridge.CantorShiftTower.Word p n) (SGC.Bridge.CantorShiftTower.Word p n) ℝ`
    - `SGC.Bridge.CantorShiftTower.tailPartition` (def, SGC.Bridge.CantorShiftTower): `(p n : ℕ) → SGC.Partition (SGC.Bridge.CantorShiftTower.Word p (n + 1))`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Bridge.CantorShiftTower.tail` (def, SGC.Bridge.CantorShiftTower): `{A : Type u_1} → {n : ℕ} → (Fin (n + 1) → A) → Fin n → A`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.row_sum_block` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → V → P.Quot → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Bridge.CantorShiftTower.shiftIn` (def, SGC.Bridge.CantorShiftTower): `{A : Type u_1} → {n : ℕ} → (Fin n → A) → A → Fin n → A`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.CantorShiftTower.shiftTower_stronglyLumpable`

- statement (kernel-elaborated, sha256 `4a6fdc4e9e9962ce`):

      ∀ (p n : ℕ), SGC.IsStronglyLumpable (SGC.Bridge.CantorShiftTower.shiftKernel p (n + 1)) (SGC.Bridge.CantorShiftTower.tailPartition p n)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.IsStronglyLumpable` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → Prop`
    - `SGC.Bridge.CantorShiftTower.Word` (def, SGC.Bridge.CantorShiftTower): `ℕ → ℕ → Type`
    - `SGC.Bridge.CantorShiftTower.shiftKernel` (def, SGC.Bridge.CantorShiftTower): `(p n : ℕ) → Matrix (SGC.Bridge.CantorShiftTower.Word p n) (SGC.Bridge.CantorShiftTower.Word p n) ℝ`
    - `SGC.Bridge.CantorShiftTower.tailPartition` (def, SGC.Bridge.CantorShiftTower): `(p n : ℕ) → SGC.Partition (SGC.Bridge.CantorShiftTower.Word p (n + 1))`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Bridge.CantorShiftTower.shiftIn` (def, SGC.Bridge.CantorShiftTower): `{A : Type u_1} → {n : ℕ} → (Fin n → A) → A → Fin n → A`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Bridge.CantorShiftTower.tail` (def, SGC.Bridge.CantorShiftTower): `{A : Type u_1} → {n : ℕ} → (Fin (n + 1) → A) → Fin n → A`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.CantorShiftTower.tailPartition_quot_map_eq_iff`

- statement (kernel-elaborated, sha256 `9f2bf4213f4a3a42`):

      ∀ {p n : ℕ} (u : SGC.Bridge.CantorShiftTower.Word p (n + 1)) (B : (SGC.Bridge.CantorShiftTower.tailPartition p n).Quot), (SGC.Bridge.CantorShiftTower.tailPartition p n).quot_map u = B ↔ SGC.Bridge.CantorShiftTower.tail u = SGC.Bridge.CantorShiftTower.tail (Quotient.out B)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.CantorShiftTower.Word` (def, SGC.Bridge.CantorShiftTower): `ℕ → ℕ → Type`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.CantorShiftTower.tailPartition` (def, SGC.Bridge.CantorShiftTower): `(p n : ℕ) → SGC.Partition (SGC.Bridge.CantorShiftTower.Word p (n + 1))`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Bridge.CantorShiftTower.tail` (def, SGC.Bridge.CantorShiftTower): `{A : Type u_1} → {n : ℕ} → (Fin (n + 1) → A) → Fin n → A`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`

### `SGC.Bridge.CantorShiftTower.tail_shiftIn`

- statement (kernel-elaborated, sha256 `8a84e4897b4703fb`):

      ∀ {A : Type u_1} {n : ℕ} (u : Fin (n + 1) → A) (b : A), SGC.Bridge.CantorShiftTower.tail (SGC.Bridge.CantorShiftTower.shiftIn u b) = SGC.Bridge.CantorShiftTower.shiftIn (SGC.Bridge.CantorShiftTower.tail u) b

- axioms: Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.CantorShiftTower.tail` (def, SGC.Bridge.CantorShiftTower): `{A : Type u_1} → {n : ℕ} → (Fin (n + 1) → A) → Fin n → A`
    - `SGC.Bridge.CantorShiftTower.shiftIn` (def, SGC.Bridge.CantorShiftTower): `{A : Type u_1} → {n : ℕ} → (Fin n → A) → A → Fin n → A`

### `SGC.Bridge.CantorShiftTower.truncate_pathShift`

- statement (kernel-elaborated, sha256 `77602e6562b4fc06`):

      ∀ (A : Type u_1) (n : ℕ) (x : SGC.Topology.PadicPathSpace.PathSpace A), SGC.Topology.PadicPathSpace.truncate A n (SGC.Bridge.CantorShiftTower.pathShift A x) = SGC.Bridge.CantorShiftTower.tail (SGC.Topology.PadicPathSpace.truncate A (n + 1) x)

- axioms: none
- unused hypotheses: none
- automation: trivial_by=rfl vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Topology.PadicPathSpace.PathSpace` (def, SGC.Topology.PadicPathSpace): `Type u_1 → Type u_1`
    - `SGC.Topology.PadicPathSpace.truncate` (def, SGC.Topology.PadicPathSpace): `(A : Type u_1) → (n : ℕ) → SGC.Topology.PadicPathSpace.PathSpace A → Fin n → A`
    - `SGC.Bridge.CantorShiftTower.pathShift` (def, SGC.Bridge.CantorShiftTower): `(A : Type u_1) → SGC.Topology.PadicPathSpace.PathSpace A → SGC.Topology.PadicPathSpace.PathSpace A`
    - `SGC.Bridge.CantorShiftTower.tail` (def, SGC.Bridge.CantorShiftTower): `{A : Type u_1} → {n : ℕ} → (Fin (n + 1) → A) → Fin n → A`

### `SGC.Bridge.CurvatureUndecidability.cd0_haltW_iff`

- statement (kernel-elaborated, sha256 `42a936c10b7ec732`):

      ∀ (H : ℤ → Bool), (∀ (i j : ℤ), H i = true → H j = true → i = j) → (SGC.Bridge.CurvatureUndecidability.CD0 (SGC.Bridge.CurvatureUndecidability.haltW H) ↔ ∀ (i : ℤ), H i = false)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.CurvatureUndecidability.CD0` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → Prop`
    - `SGC.Bridge.CurvatureUndecidability.haltW` (def, SGC.Bridge.CurvatureUndecidability): `(ℤ → Bool) → SGC.Bridge.CurvatureUndecidability.Weights`
    - `SGC.Bridge.CurvatureUndecidability.Weights` (def, SGC.Bridge.CurvatureUndecidability): `Type`
    - `SGC.Bridge.CurvatureUndecidability.gam2` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → (ℤ → ℝ) → ℤ → ℝ`
    - `SGC.Bridge.CurvatureUndecidability.lineGen` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → ℤ → ℝ`
    - `SGC.Bridge.CurvatureUndecidability.gam` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → (ℤ → ℝ) → ℤ → ℝ`

### `SGC.Bridge.CurvatureUndecidability.cd0_unitW`

- statement (kernel-elaborated, sha256 `2974bc530e4321c6`):

      SGC.Bridge.CurvatureUndecidability.CD0 SGC.Bridge.CurvatureUndecidability.unitW

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.CurvatureUndecidability.CD0` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → Prop`
    - `SGC.Bridge.CurvatureUndecidability.unitW` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights`  [ignores x._@.SGC.Bridge.CurvatureUndecidability.3800758693._hygCtx._hyg.5]
    - `SGC.Bridge.CurvatureUndecidability.Weights` (def, SGC.Bridge.CurvatureUndecidability): `Type`
    - `SGC.Bridge.CurvatureUndecidability.gam2` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → (ℤ → ℝ) → ℤ → ℝ`
    - `SGC.Bridge.CurvatureUndecidability.lineGen` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → ℤ → ℝ`
    - `SGC.Bridge.CurvatureUndecidability.gam` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → (ℤ → ℝ) → ℤ → ℝ`

### `SGC.Bridge.CurvatureUndecidability.gam2_heavy_eq`

- statement (kernel-elaborated, sha256 `78ac4e3410b24c64`):

      ∀ (q : SGC.Bridge.CurvatureUndecidability.Weights) (T : ℤ), q (T - 2) = 1 → q (T - 1) = 1 → q T = 4 → q (T + 1) = 1 → SGC.Bridge.CurvatureUndecidability.gam2 q (SGC.Bridge.CurvatureUndecidability.wit T) (SGC.Bridge.CurvatureUndecidability.wit T) T = -(1 / 4)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.CurvatureUndecidability.Weights` (def, SGC.Bridge.CurvatureUndecidability): `Type`
    - `SGC.Bridge.CurvatureUndecidability.gam2` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → (ℤ → ℝ) → ℤ → ℝ`
    - `SGC.Bridge.CurvatureUndecidability.wit` (def, SGC.Bridge.CurvatureUndecidability): `ℤ → ℤ → ℝ`
    - `SGC.Bridge.CurvatureUndecidability.lineGen` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → ℤ → ℝ`
    - `SGC.Bridge.CurvatureUndecidability.gam` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → (ℤ → ℝ) → ℤ → ℝ`

### `SGC.Bridge.CurvatureUndecidability.gam2_unitW_eq`

- statement (kernel-elaborated, sha256 `867a666ca0d09fa3`):

      ∀ (f : ℤ → ℝ) (x : ℤ), SGC.Bridge.CurvatureUndecidability.gam2 SGC.Bridge.CurvatureUndecidability.unitW f f x = 1 / 4 * (f (x - 2) - 2 * f (x - 1) + f x) ^ 2 + 1 / 2 * (f (x - 1) - 2 * f x + f (x + 1)) ^ 2 + 1 / 4 * (f x - 2 * f (x + 1) + f (x + 2)) ^ 2

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.CurvatureUndecidability.gam2` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → (ℤ → ℝ) → ℤ → ℝ`
    - `SGC.Bridge.CurvatureUndecidability.unitW` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights`  [ignores x._@.SGC.Bridge.CurvatureUndecidability.3800758693._hygCtx._hyg.5]
    - `SGC.Bridge.CurvatureUndecidability.Weights` (def, SGC.Bridge.CurvatureUndecidability): `Type`
    - `SGC.Bridge.CurvatureUndecidability.lineGen` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → ℤ → ℝ`
    - `SGC.Bridge.CurvatureUndecidability.gam` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → (ℤ → ℝ) → ℤ → ℝ`

### `SGC.Bridge.CurvatureUndecidability.haltW_eq_four`

- statement (kernel-elaborated, sha256 `57714a7d8ee91802`):

      ∀ {H : ℤ → Bool} {i : ℤ}, H i = true → SGC.Bridge.CurvatureUndecidability.haltW H i = 4

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.CurvatureUndecidability.haltW` (def, SGC.Bridge.CurvatureUndecidability): `(ℤ → Bool) → SGC.Bridge.CurvatureUndecidability.Weights`
    - `SGC.Bridge.CurvatureUndecidability.Weights` (def, SGC.Bridge.CurvatureUndecidability): `Type`

### `SGC.Bridge.CurvatureUndecidability.haltW_eq_one`

- statement (kernel-elaborated, sha256 `099f8701ff185a15`):

      ∀ {H : ℤ → Bool} {i : ℤ}, H i = false → SGC.Bridge.CurvatureUndecidability.haltW H i = 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.CurvatureUndecidability.haltW` (def, SGC.Bridge.CurvatureUndecidability): `(ℤ → Bool) → SGC.Bridge.CurvatureUndecidability.Weights`
    - `SGC.Bridge.CurvatureUndecidability.Weights` (def, SGC.Bridge.CurvatureUndecidability): `Type`

### `SGC.Bridge.CurvatureUndecidability.haltW_eq_unitW`

- statement (kernel-elaborated, sha256 `3fe6b85d6d33817b`):

      ∀ {H : ℤ → Bool}, (∀ (i : ℤ), H i = false) → SGC.Bridge.CurvatureUndecidability.haltW H = SGC.Bridge.CurvatureUndecidability.unitW

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.CurvatureUndecidability.Weights` (def, SGC.Bridge.CurvatureUndecidability): `Type`
    - `SGC.Bridge.CurvatureUndecidability.haltW` (def, SGC.Bridge.CurvatureUndecidability): `(ℤ → Bool) → SGC.Bridge.CurvatureUndecidability.Weights`
    - `SGC.Bridge.CurvatureUndecidability.unitW` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights`  [ignores x._@.SGC.Bridge.CurvatureUndecidability.3800758693._hygCtx._hyg.5]

### `SGC.Bridge.CurvatureUndecidability.not_cd0_haltW_of_halts`

- statement (kernel-elaborated, sha256 `32b3da38fbe372b6`):

      ∀ (H : ℤ → Bool) (T : ℤ), (∀ (i j : ℤ), H i = true → H j = true → i = j) → H T = true → ¬SGC.Bridge.CurvatureUndecidability.CD0 (SGC.Bridge.CurvatureUndecidability.haltW H)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.CurvatureUndecidability.CD0` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → Prop`
    - `SGC.Bridge.CurvatureUndecidability.haltW` (def, SGC.Bridge.CurvatureUndecidability): `(ℤ → Bool) → SGC.Bridge.CurvatureUndecidability.Weights`
    - `SGC.Bridge.CurvatureUndecidability.Weights` (def, SGC.Bridge.CurvatureUndecidability): `Type`
    - `SGC.Bridge.CurvatureUndecidability.gam2` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → (ℤ → ℝ) → ℤ → ℝ`
    - `SGC.Bridge.CurvatureUndecidability.lineGen` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → ℤ → ℝ`
    - `SGC.Bridge.CurvatureUndecidability.gam` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → (ℤ → ℝ) → ℤ → ℝ`

### `SGC.Bridge.CurvatureUndecidability.not_cd0_of_heavy_edge`

- statement (kernel-elaborated, sha256 `36ac82c77effa3f8`):

      ∀ (q : SGC.Bridge.CurvatureUndecidability.Weights) (T : ℤ), q (T - 2) = 1 → q (T - 1) = 1 → q T = 4 → q (T + 1) = 1 → ¬SGC.Bridge.CurvatureUndecidability.CD0 q

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.CurvatureUndecidability.Weights` (def, SGC.Bridge.CurvatureUndecidability): `Type`
    - `SGC.Bridge.CurvatureUndecidability.CD0` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → Prop`
    - `SGC.Bridge.CurvatureUndecidability.gam2` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → (ℤ → ℝ) → ℤ → ℝ`
    - `SGC.Bridge.CurvatureUndecidability.lineGen` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → ℤ → ℝ`
    - `SGC.Bridge.CurvatureUndecidability.gam` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → (ℤ → ℝ) → ℤ → ℝ`

### `SGC.Bridge.CurvatureUndecidability.wit_add_one`

- statement (kernel-elaborated, sha256 `0aa89317863cf3c1`):

      ∀ (T : ℤ), SGC.Bridge.CurvatureUndecidability.wit T (T + 1) = 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=simp vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.CurvatureUndecidability.wit` (def, SGC.Bridge.CurvatureUndecidability): `ℤ → ℤ → ℝ`

### `SGC.Bridge.CurvatureUndecidability.wit_add_two`

- statement (kernel-elaborated, sha256 `2a59b0b5c0d46951`):

      ∀ (T : ℤ), SGC.Bridge.CurvatureUndecidability.wit T (T + 2) = 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=simp vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.CurvatureUndecidability.wit` (def, SGC.Bridge.CurvatureUndecidability): `ℤ → ℤ → ℝ`

### `SGC.Bridge.CurvatureUndecidability.wit_self`

- statement (kernel-elaborated, sha256 `be30b858822a54ab`):

      ∀ (T : ℤ), SGC.Bridge.CurvatureUndecidability.wit T T = 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=simp vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.CurvatureUndecidability.wit` (def, SGC.Bridge.CurvatureUndecidability): `ℤ → ℤ → ℝ`

### `SGC.Bridge.CurvatureUndecidability.wit_sub_one`

- statement (kernel-elaborated, sha256 `7831fe28b461df37`):

      ∀ (T : ℤ), SGC.Bridge.CurvatureUndecidability.wit T (T - 1) = 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=simp vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.CurvatureUndecidability.wit` (def, SGC.Bridge.CurvatureUndecidability): `ℤ → ℤ → ℝ`

### `SGC.Bridge.CurvatureUndecidability.wit_sub_two`

- statement (kernel-elaborated, sha256 `438602a80eeb699b`):

      ∀ (T : ℤ), SGC.Bridge.CurvatureUndecidability.wit T (T - 2) = -1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=simp vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.CurvatureUndecidability.wit` (def, SGC.Bridge.CurvatureUndecidability): `ℤ → ℤ → ℝ`

### `SGC.Bridge.DefectHorizonBridge.HeatKernel_opNorm_bound_proved`

- statement (kernel-elaborated, sha256 `eecfbb2ea2ae459c`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) [Nonempty V] (L : Matrix V V ℝ) (T : ℝ), 0 ≤ T → ∃ B ≥ 1, ∀ (s : ℝ), 0 ≤ s → s ≤ T → SGC.opNorm_pi pi_dist hπ (SGC.Approximate.matrixToLinearMap (SGC.Approximate.HeatKernel L s)) ≤ B

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.opNorm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → ℝ`
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.HeatKernel` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → Matrix V V ℝ`
    - `SGC.opNorm_set` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → Set ℝ`  [ignores _h_pos]
    - `SGC.norm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`

### `SGC.Bridge.DefectHorizonBridge.coarseGeneratorMatrix_mul_proj`

- statement (kernel-elaborated, sha256 `388214b9e174ca72`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (L : Matrix V V ℝ) (P : SGC.Partition V), SGC.Approximate.CoarseGeneratorMatrix L P pi_dist hπ * SGC.Approximate.CoarseProjectorMatrix P pi_dist hπ = SGC.Approximate.CoarseGeneratorMatrix L P pi_dist hπ

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Approximate.CoarseGeneratorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.Approximate.CoarseProjectorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`  [ignores hπ]
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.DefectHorizonBridge.coarseProj_fixes_coarse_heatKernel`

- statement (kernel-elaborated, sha256 `306f068bf1a0dc5a`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) [Nonempty V] (L : Matrix V V ℝ) (P : SGC.Partition V) (t : ℝ) (f₀ : V → ℝ), f₀ = (SGC.Approximate.CoarseProjector P pi_dist hπ) f₀ → (SGC.Approximate.CoarseProjector P pi_dist hπ) ((SGC.Approximate.HeatKernelMap (SGC.Approximate.CoarseGeneratorMatrix L P pi_dist hπ) t) f₀) = (SGC.Approximate.HeatKernelMap (SGC.Approximate.CoarseGeneratorMatrix L P pi_dist hπ) t) f₀

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Approximate.CoarseProjector` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.HeatKernelMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.CoarseGeneratorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.lift_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → (P.Quot → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Q_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] P.Quot → ℝ`  [ignores _hπ]
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.HeatKernel` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → Matrix V V ℝ`
    - `SGC.Approximate.CoarseProjectorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`  [ignores hπ]
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.DefectHorizonBridge.defectComplement_mul_proj`

- statement (kernel-elaborated, sha256 `cb987a50067f7241`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (L : Matrix V V ℝ) (P : SGC.Partition V), (L - SGC.Bridge.DefectHorizonBridge.DefectMatrix L P pi_dist hπ) * SGC.Approximate.CoarseProjectorMatrix P pi_dist hπ = SGC.Approximate.CoarseProjectorMatrix P pi_dist hπ * L * SGC.Approximate.CoarseProjectorMatrix P pi_dist hπ

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.DefectHorizonBridge.DefectMatrix` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.Approximate.CoarseProjectorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`  [ignores hπ]
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.DefectHorizonBridge.defectComplement_mul_proj_eq_coarse`

- statement (kernel-elaborated, sha256 `a479d6e8cd3a80da`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (L : Matrix V V ℝ) (P : SGC.Partition V), (L - SGC.Bridge.DefectHorizonBridge.DefectMatrix L P pi_dist hπ) * SGC.Approximate.CoarseProjectorMatrix P pi_dist hπ = SGC.Approximate.CoarseGeneratorMatrix L P pi_dist hπ

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.DefectHorizonBridge.DefectMatrix` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.Approximate.CoarseProjectorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`  [ignores hπ]
    - `SGC.Approximate.CoarseGeneratorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.DefectHorizonBridge.defectComplement_pow_mul_proj`

- statement (kernel-elaborated, sha256 `2546481cae2de1c4`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (L : Matrix V V ℝ) (P : SGC.Partition V) (n : ℕ), (L - SGC.Bridge.DefectHorizonBridge.DefectMatrix L P pi_dist hπ) ^ n * SGC.Approximate.CoarseProjectorMatrix P pi_dist hπ = SGC.Approximate.CoarseGeneratorMatrix L P pi_dist hπ ^ n * SGC.Approximate.CoarseProjectorMatrix P pi_dist hπ

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.DefectHorizonBridge.DefectMatrix` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.Approximate.CoarseProjectorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`  [ignores hπ]
    - `SGC.Approximate.CoarseGeneratorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.DefectHorizonBridge.defectMatrix_mulVec`

- statement (kernel-elaborated, sha256 `61e0ef23603d6a37`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (f : V → ℝ), (SGC.Bridge.DefectHorizonBridge.DefectMatrix L P pi_dist hπ).mulVec f = (SGC.Approximate.DefectOperator L P pi_dist hπ) f

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.DefectHorizonBridge.DefectMatrix` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.Approximate.DefectOperator` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.CoarseProjectorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`  [ignores hπ]
    - `SGC.Approximate.CoarseProjector` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.lift_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → (P.Quot → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Q_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] P.Quot → ℝ`  [ignores _hπ]
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.DefectHorizonBridge.defectMatrix_toLin`

- statement (kernel-elaborated, sha256 `a7238c6e1bd3c749`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v), SGC.Approximate.matrixToLinearMap (SGC.Bridge.DefectHorizonBridge.DefectMatrix L P pi_dist hπ) = SGC.Approximate.DefectOperator L P pi_dist hπ

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.DefectMatrix` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.Approximate.DefectOperator` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.CoarseProjectorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`  [ignores hπ]
    - `SGC.Approximate.CoarseProjector` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.lift_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → (P.Quot → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Q_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] P.Quot → ℝ`  [ignores _hπ]
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.DefectHorizonBridge.defect_eq_validity_leakage`

- statement (kernel-elaborated, sha256 `544318617ef91aea`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (L : Matrix V V ℝ) (P : SGC.Partition V), ‖SGC.Bridge.DefectHorizonBridge.ofMat pi_dist hπ (SGC.Bridge.DefectHorizonBridge.DefectMatrix L P pi_dist hπ)‖ = SGC.opNorm_pi pi_dist hπ (SGC.Approximate.DefectOperator L P pi_dist hπ)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.DefectHorizonBridge.PiMat` (def, SGC.Bridge.DefectHorizonBridge): `(V : Type u_2) → [Fintype V] → [DecidableEq V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Type u_2`  [ignores pi_dist,_hπ]
    - `SGC.Bridge.DefectHorizonBridge.instNormedRingPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → NormedRing (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`
    - `SGC.Bridge.DefectHorizonBridge.ofMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ`  [ignores pi_dist,hπ]
    - `SGC.Bridge.DefectHorizonBridge.DefectMatrix` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.opNorm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → ℝ`
    - `SGC.Approximate.DefectOperator` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.instNormedAddCommGroupPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → NormedAddCommGroup (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`
    - `SGC.Bridge.DefectHorizonBridge.instRingPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → Ring (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`  [ignores pi_dist,hπ]
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_mul_le` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M N : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ (M * N) ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M * SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ N`
    - `SGC.Approximate.CoarseProjectorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`  [ignores hπ]
    - `SGC.opNorm_set` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → Set ℝ`  [ignores _h_pos]
    - `SGC.Approximate.CoarseProjector` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_zero` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ 0 = 0`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_add_le` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M N : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ (M + N) ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M + SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ N`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_neg` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ (-M) = SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_eq_zero` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) {M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ}, SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M = 0 → M = 0`
    - `SGC.Bridge.DefectHorizonBridge.toMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → Matrix V V ℝ`  [ignores pi_dist,hπ]
    - `SGC.opNorm_pi_comp` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A B : (V → ℝ) →ₗ[ℝ] V → ℝ), SGC.opNorm_pi pi_dist h_pos (A ∘ₗ B) ≤ SGC.opNorm_pi pi_dist h_pos A * SGC.opNorm_pi pi_dist h_pos B`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.norm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.lift_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → (P.Quot → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Q_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] P.Quot → ℝ`  [ignores _hπ]
    - `SGC.opNorm_pi_le_of_bound` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ) (c : ℝ), 0 ≤ c → (∀ (f : V → ℝ), SGC.norm_pi pi_dist (A f) ≤ c * SGC.norm_pi pi_dist f) → SGC.opNorm_pi pi_dist h_pos A ≤ c`
    - `SGC.norm_pi_eq_zero_iff` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f : V → ℝ), SGC.norm_pi pi_dist f = 0 ↔ f = 0`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_nonneg` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), 0 ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M`
    - `SGC.Approximate.norm_pi_add_le` (theorem, SGC.Renormalization.Approximate): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f g : V → ℝ), SGC.norm_pi pi_dist (f + g) ≤ SGC.norm_pi pi_dist f + SGC.norm_pi pi_dist g`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_mulVec_le` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ) (f : V → ℝ), SGC.norm_pi pi_dist ((SGC.Bridge.DefectHorizonBridge.toMat pi_dist hπ M).mulVec f) ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M * SGC.norm_pi pi_dist f`
    - `SGC.Bridge.DefectHorizonBridge.norm_pi_neg` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist f : V → ℝ), SGC.norm_pi pi_dist (-f) = SGC.norm_pi pi_dist f`
    - `SGC.Bridge.DefectHorizonBridge.norm_pi_nonneg'` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist f : V → ℝ), 0 ≤ SGC.norm_pi pi_dist f`
    - `SGC.opNorm_set_bddBelow` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ), BddBelow (SGC.opNorm_set pi_dist h_pos A)`
    - `SGC.opNorm_pi_bound` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ) (f : V → ℝ), SGC.norm_pi pi_dist (A f) ≤ SGC.opNorm_pi pi_dist h_pos A * SGC.norm_pi pi_dist f`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.norm_sq_pi_nonneg` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (h : V → ℝ), 0 ≤ SGC.norm_sq_pi pi_dist h`
    - `SGC.norm_sq_pi_eq_zero_iff` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (h : V → ℝ), SGC.norm_sq_pi pi_dist h = 0 ↔ ∀ (v : V), h v = 0`
    - `SGC.opNorm_pi_nonneg` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ), 0 ≤ SGC.opNorm_pi pi_dist h_pos A`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.inner_pi_add_left` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (u v w : V → ℝ), SGC.inner_pi pi_dist (u + v) w = SGC.inner_pi pi_dist u w + SGC.inner_pi pi_dist v w`
    - `SGC.inner_pi_add_right` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (u v w : V → ℝ), SGC.inner_pi pi_dist u (v + w) = SGC.inner_pi pi_dist u v + SGC.inner_pi pi_dist u w`
    - `SGC.inner_pi_comm` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (u v : V → ℝ), SGC.inner_pi pi_dist u v = SGC.inner_pi pi_dist v u`
    - `SGC.cauchy_schwarz_pi` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f g : V → ℝ), |SGC.inner_pi pi_dist f g| ≤ SGC.norm_pi pi_dist f * SGC.norm_pi pi_dist g`
    - `SGC.norm_pi_smul_abs` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (c : ℝ) (f : V → ℝ), SGC.norm_pi pi_dist (c • f) = |c| * SGC.norm_pi pi_dist f`
    - `SGC.norm_pi_pos_of_ne_zero` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f : V → ℝ), f ≠ 0 → 0 < SGC.norm_pi pi_dist f`
    - `SGC.opNorm_set_nonempty` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ), (SGC.opNorm_set pi_dist h_pos A).Nonempty`
    - `SGC.norm_sq_pi_eq_sum` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist h : V → ℝ), SGC.norm_sq_pi pi_dist h = ∑ v, pi_dist v * h v ^ 2`
    - `SGC.sum_quad` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist f g : V → ℝ) (t : ℝ), ∑ v, pi_dist v * (f v + t * g v) ^ 2 = ∑ v, pi_dist v * f v ^ 2 + 2 * t * ∑ v, pi_dist v * (f v * g v) + t ^ 2 * ∑ v, pi_dist v * g v ^ 2`
    - `SGC.sqrt_ineq_of_sq_le` (theorem, SGC.Axioms.Geometry): `∀ (a b c : ℝ), 0 ≤ a → 0 ≤ c → b ^ 2 ≤ a * c → |b| ≤ √a * √c`
    - `SGC.norm_sq_pi_smul` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (c : ℝ) (f : V → ℝ), SGC.norm_sq_pi pi_dist (c • f) = c ^ 2 * SGC.norm_sq_pi pi_dist f`
    - `SGC.iso_L2_to_std` (def, SGC.Axioms.Geometry): `{V : Type u_1} → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) ≃ₗ[ℝ] V → ℝ`
    - `SGC.norm_pi_eq_euclidean_norm` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (f : V → ℝ), SGC.norm_pi pi_dist f = ‖(WithLp.equiv 2 (V → ℝ)).symm ((SGC.iso_L2_to_std pi_dist h_pos) f)‖`
    - `SGC.pointwise_quad` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [Fintype V] [DecidableEq V] (f g : V → ℝ) (t : ℝ) (v : V), (f v + t * g v) ^ 2 = f v ^ 2 + 2 * t * (f v * g v) + t ^ 2 * g v ^ 2`
    - `SGC.inner_pi_smul_left` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (c : ℝ) (u v : V → ℝ), SGC.inner_pi pi_dist (c • u) v = c * SGC.inner_pi pi_dist u v`
    - `SGC.inner_pi_smul_right` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (c : ℝ) (u v : V → ℝ), SGC.inner_pi pi_dist u (c • v) = c * SGC.inner_pi pi_dist u v`
    - `SGC.norm_pi_eq_sqrt_sum_sq` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (f : V → ℝ), SGC.norm_pi pi_dist f = √(∑ v, (SGC.iso_L2_to_std pi_dist h_pos) f v ^ 2)`
    - `SGC.norm_sq_pi_eq_euclidean` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (f : V → ℝ), SGC.norm_sq_pi pi_dist f = ∑ v, (SGC.iso_L2_to_std pi_dist h_pos) f v ^ 2`

### `SGC.Bridge.DefectHorizonBridge.defect_horizon_bound`

- statement (kernel-elaborated, sha256 `83d672d91f1c2429`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) [Nonempty V] (L : Matrix V V ℝ) (P : SGC.Partition V) (t : ℝ), 0 ≤ t → ∀ (f₀ : V → ℝ), f₀ = (SGC.Approximate.CoarseProjector P pi_dist hπ) f₀ → SGC.norm_pi pi_dist ((SGC.Approximate.HeatKernelMap L t) f₀ - (SGC.Approximate.HeatKernelMap (SGC.Approximate.CoarseGeneratorMatrix L P pi_dist hπ) t) f₀) ≤ t * SGC.opNorm_pi pi_dist hπ (SGC.Approximate.DefectOperator L P pi_dist hπ) * Real.exp (t * (SGC.opNorm_pi pi_dist hπ (SGC.Approximate.matrixToLinearMap (L - SGC.Bridge.DefectHorizonBridge.DefectMatrix L P pi_dist hπ)) + SGC.opNorm_pi pi_dist hπ (SGC.Approximate.DefectOperator L P pi_dist hπ))) * SGC.norm_pi pi_dist f₀

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Approximate.CoarseProjector` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.norm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Approximate.HeatKernelMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.CoarseGeneratorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.opNorm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → ℝ`
    - `SGC.Approximate.DefectOperator` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.DefectMatrix` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.lift_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → (P.Quot → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Q_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] P.Quot → ℝ`  [ignores _hπ]
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Approximate.HeatKernel` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → Matrix V V ℝ`
    - `SGC.Approximate.CoarseProjectorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`  [ignores hπ]
    - `SGC.opNorm_set` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → Set ℝ`  [ignores _h_pos]
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.DefectHorizonBridge.exp_defectComplement_apply`

- statement (kernel-elaborated, sha256 `afd98e68ee5d60db`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) [Nonempty V] (L : Matrix V V ℝ) (P : SGC.Partition V) (t : ℝ) (f₀ : V → ℝ), f₀ = (SGC.Approximate.CoarseProjector P pi_dist hπ) f₀ → (NormedSpace.exp ℝ (t • (L - SGC.Bridge.DefectHorizonBridge.DefectMatrix L P pi_dist hπ))).mulVec f₀ = (SGC.Approximate.HeatKernelMap (SGC.Approximate.CoarseGeneratorMatrix L P pi_dist hπ) t) f₀

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Approximate.CoarseProjector` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.DefectMatrix` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.Approximate.HeatKernelMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.CoarseGeneratorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.lift_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → (P.Quot → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Q_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] P.Quot → ℝ`  [ignores _hπ]
    - `SGC.Approximate.CoarseProjectorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`  [ignores hπ]
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.HeatKernel` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → Matrix V V ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.DefectHorizonBridge.exp_defectComplement_mul_proj`

- statement (kernel-elaborated, sha256 `c2941eafed744654`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (L : Matrix V V ℝ) (P : SGC.Partition V) (t : ℝ), NormedSpace.exp ℝ (t • (L - SGC.Bridge.DefectHorizonBridge.DefectMatrix L P pi_dist hπ)) * SGC.Approximate.CoarseProjectorMatrix P pi_dist hπ = NormedSpace.exp ℝ (t • SGC.Approximate.CoarseGeneratorMatrix L P pi_dist hπ) * SGC.Approximate.CoarseProjectorMatrix P pi_dist hπ

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.DefectHorizonBridge.DefectMatrix` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.Approximate.CoarseProjectorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`  [ignores hπ]
    - `SGC.Approximate.CoarseGeneratorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.DefectHorizonBridge.exp_piMat_eq`

- statement (kernel-elaborated, sha256 `900e46aed457bef9`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M : Matrix V V ℝ), SGC.Bridge.DefectHorizonBridge.toMat pi_dist hπ (NormedSpace.exp ℝ (SGC.Bridge.DefectHorizonBridge.ofMat pi_dist hπ M)) = NormedSpace.exp ℝ M

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DefectHorizonBridge.toMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → Matrix V V ℝ`  [ignores pi_dist,hπ]
    - `SGC.Bridge.DefectHorizonBridge.PiMat` (def, SGC.Bridge.DefectHorizonBridge): `(V : Type u_2) → [Fintype V] → [DecidableEq V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Type u_2`  [ignores pi_dist,_hπ]
    - `SGC.Bridge.DefectHorizonBridge.instRingPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → Ring (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`  [ignores pi_dist,hπ]
    - `SGC.Bridge.DefectHorizonBridge.instAlgebraRealPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → Algebra ℝ (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`  [ignores pi_dist,hπ]
    - `SGC.Bridge.DefectHorizonBridge.instNormedRingPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → NormedRing (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`
    - `SGC.Bridge.DefectHorizonBridge.ofMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ`  [ignores pi_dist,hπ]
    - `SGC.Bridge.DefectHorizonBridge.instNormedAddCommGroupPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → NormedAddCommGroup (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_mul_le` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M N : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ (M * N) ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M * SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ N`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_zero` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ 0 = 0`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_add_le` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M N : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ (M + N) ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M + SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ N`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_neg` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ (-M) = SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_eq_zero` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) {M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ}, SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M = 0 → M = 0`
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.opNorm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → ℝ`
    - `SGC.opNorm_pi_comp` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A B : (V → ℝ) →ₗ[ℝ] V → ℝ), SGC.opNorm_pi pi_dist h_pos (A ∘ₗ B) ≤ SGC.opNorm_pi pi_dist h_pos A * SGC.opNorm_pi pi_dist h_pos B`
    - `SGC.opNorm_pi_le_of_bound` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ) (c : ℝ), 0 ≤ c → (∀ (f : V → ℝ), SGC.norm_pi pi_dist (A f) ≤ c * SGC.norm_pi pi_dist f) → SGC.opNorm_pi pi_dist h_pos A ≤ c`
    - `SGC.norm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.norm_pi_eq_zero_iff` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f : V → ℝ), SGC.norm_pi pi_dist f = 0 ↔ f = 0`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_nonneg` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), 0 ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M`
    - `SGC.Approximate.norm_pi_add_le` (theorem, SGC.Renormalization.Approximate): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f g : V → ℝ), SGC.norm_pi pi_dist (f + g) ≤ SGC.norm_pi pi_dist f + SGC.norm_pi pi_dist g`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_mulVec_le` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ) (f : V → ℝ), SGC.norm_pi pi_dist ((SGC.Bridge.DefectHorizonBridge.toMat pi_dist hπ M).mulVec f) ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M * SGC.norm_pi pi_dist f`
    - `SGC.Bridge.DefectHorizonBridge.norm_pi_neg` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist f : V → ℝ), SGC.norm_pi pi_dist (-f) = SGC.norm_pi pi_dist f`
    - `SGC.Bridge.DefectHorizonBridge.norm_pi_nonneg'` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist f : V → ℝ), 0 ≤ SGC.norm_pi pi_dist f`
    - `SGC.opNorm_set` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → Set ℝ`  [ignores _h_pos]
    - `SGC.opNorm_set_bddBelow` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ), BddBelow (SGC.opNorm_set pi_dist h_pos A)`
    - `SGC.opNorm_pi_bound` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ) (f : V → ℝ), SGC.norm_pi pi_dist (A f) ≤ SGC.opNorm_pi pi_dist h_pos A * SGC.norm_pi pi_dist f`
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.norm_sq_pi_nonneg` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (h : V → ℝ), 0 ≤ SGC.norm_sq_pi pi_dist h`
    - `SGC.norm_sq_pi_eq_zero_iff` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (h : V → ℝ), SGC.norm_sq_pi pi_dist h = 0 ↔ ∀ (v : V), h v = 0`
    - `SGC.opNorm_pi_nonneg` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ), 0 ≤ SGC.opNorm_pi pi_dist h_pos A`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.inner_pi_add_left` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (u v w : V → ℝ), SGC.inner_pi pi_dist (u + v) w = SGC.inner_pi pi_dist u w + SGC.inner_pi pi_dist v w`
    - `SGC.inner_pi_add_right` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (u v w : V → ℝ), SGC.inner_pi pi_dist u (v + w) = SGC.inner_pi pi_dist u v + SGC.inner_pi pi_dist u w`
    - `SGC.inner_pi_comm` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (u v : V → ℝ), SGC.inner_pi pi_dist u v = SGC.inner_pi pi_dist v u`
    - `SGC.cauchy_schwarz_pi` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f g : V → ℝ), |SGC.inner_pi pi_dist f g| ≤ SGC.norm_pi pi_dist f * SGC.norm_pi pi_dist g`
    - `SGC.norm_pi_smul_abs` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (c : ℝ) (f : V → ℝ), SGC.norm_pi pi_dist (c • f) = |c| * SGC.norm_pi pi_dist f`
    - `SGC.norm_pi_pos_of_ne_zero` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f : V → ℝ), f ≠ 0 → 0 < SGC.norm_pi pi_dist f`
    - `SGC.opNorm_set_nonempty` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ), (SGC.opNorm_set pi_dist h_pos A).Nonempty`
    - `SGC.norm_sq_pi_eq_sum` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist h : V → ℝ), SGC.norm_sq_pi pi_dist h = ∑ v, pi_dist v * h v ^ 2`
    - `SGC.sum_quad` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist f g : V → ℝ) (t : ℝ), ∑ v, pi_dist v * (f v + t * g v) ^ 2 = ∑ v, pi_dist v * f v ^ 2 + 2 * t * ∑ v, pi_dist v * (f v * g v) + t ^ 2 * ∑ v, pi_dist v * g v ^ 2`
    - `SGC.sqrt_ineq_of_sq_le` (theorem, SGC.Axioms.Geometry): `∀ (a b c : ℝ), 0 ≤ a → 0 ≤ c → b ^ 2 ≤ a * c → |b| ≤ √a * √c`
    - `SGC.norm_sq_pi_smul` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (c : ℝ) (f : V → ℝ), SGC.norm_sq_pi pi_dist (c • f) = c ^ 2 * SGC.norm_sq_pi pi_dist f`
    - `SGC.iso_L2_to_std` (def, SGC.Axioms.Geometry): `{V : Type u_1} → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) ≃ₗ[ℝ] V → ℝ`
    - `SGC.norm_pi_eq_euclidean_norm` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (f : V → ℝ), SGC.norm_pi pi_dist f = ‖(WithLp.equiv 2 (V → ℝ)).symm ((SGC.iso_L2_to_std pi_dist h_pos) f)‖`
    - `SGC.pointwise_quad` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [Fintype V] [DecidableEq V] (f g : V → ℝ) (t : ℝ) (v : V), (f v + t * g v) ^ 2 = f v ^ 2 + 2 * t * (f v * g v) + t ^ 2 * g v ^ 2`
    - `SGC.inner_pi_smul_left` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (c : ℝ) (u v : V → ℝ), SGC.inner_pi pi_dist (c • u) v = c * SGC.inner_pi pi_dist u v`
    - `SGC.inner_pi_smul_right` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (c : ℝ) (u v : V → ℝ), SGC.inner_pi pi_dist u (c • v) = c * SGC.inner_pi pi_dist u v`
    - `SGC.norm_pi_eq_sqrt_sum_sq` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (f : V → ℝ), SGC.norm_pi pi_dist f = √(∑ v, (SGC.iso_L2_to_std pi_dist h_pos) f v ^ 2)`
    - `SGC.norm_sq_pi_eq_euclidean` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (f : V → ℝ), SGC.norm_sq_pi pi_dist f = ∑ v, (SGC.iso_L2_to_std pi_dist h_pos) f v ^ 2`

### `SGC.Bridge.DefectHorizonBridge.heatKernel_opNorm_explicit`

- statement (kernel-elaborated, sha256 `3938a5a493a875d1`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) [Nonempty V] (L : Matrix V V ℝ) (s : ℝ), 0 ≤ s → SGC.opNorm_pi pi_dist hπ (SGC.Approximate.matrixToLinearMap (SGC.Approximate.HeatKernel L s)) ≤ Real.exp (s * SGC.opNorm_pi pi_dist hπ (SGC.Approximate.matrixToLinearMap L))

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.opNorm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → ℝ`
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.HeatKernel` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → Matrix V V ℝ`
    - `SGC.opNorm_set` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → Set ℝ`  [ignores _h_pos]
    - `SGC.norm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`

### `SGC.Bridge.DefectHorizonBridge.instCompleteSpacePiMat`

- statement (kernel-elaborated, sha256 `f8465f900ef84a37`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v), CompleteSpace (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DefectHorizonBridge.PiMat` (def, SGC.Bridge.DefectHorizonBridge): `(V : Type u_2) → [Fintype V] → [DecidableEq V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Type u_2`  [ignores pi_dist,_hπ]
    - `SGC.Bridge.DefectHorizonBridge.instNormedRingPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → NormedRing (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`
    - `SGC.Bridge.DefectHorizonBridge.instNormedAddCommGroupPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → NormedAddCommGroup (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`
    - `SGC.Bridge.DefectHorizonBridge.instRingPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → Ring (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`  [ignores pi_dist,hπ]
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_mul_le` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M N : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ (M * N) ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M * SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ N`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_zero` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ 0 = 0`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_add_le` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M N : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ (M + N) ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M + SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ N`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_neg` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ (-M) = SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_eq_zero` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) {M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ}, SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M = 0 → M = 0`
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.toMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → Matrix V V ℝ`  [ignores pi_dist,hπ]
    - `SGC.opNorm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → ℝ`
    - `SGC.opNorm_pi_comp` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A B : (V → ℝ) →ₗ[ℝ] V → ℝ), SGC.opNorm_pi pi_dist h_pos (A ∘ₗ B) ≤ SGC.opNorm_pi pi_dist h_pos A * SGC.opNorm_pi pi_dist h_pos B`
    - `SGC.opNorm_pi_le_of_bound` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ) (c : ℝ), 0 ≤ c → (∀ (f : V → ℝ), SGC.norm_pi pi_dist (A f) ≤ c * SGC.norm_pi pi_dist f) → SGC.opNorm_pi pi_dist h_pos A ≤ c`
    - `SGC.norm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.norm_pi_eq_zero_iff` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f : V → ℝ), SGC.norm_pi pi_dist f = 0 ↔ f = 0`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_nonneg` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), 0 ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M`
    - `SGC.Approximate.norm_pi_add_le` (theorem, SGC.Renormalization.Approximate): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f g : V → ℝ), SGC.norm_pi pi_dist (f + g) ≤ SGC.norm_pi pi_dist f + SGC.norm_pi pi_dist g`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_mulVec_le` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ) (f : V → ℝ), SGC.norm_pi pi_dist ((SGC.Bridge.DefectHorizonBridge.toMat pi_dist hπ M).mulVec f) ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M * SGC.norm_pi pi_dist f`
    - `SGC.Bridge.DefectHorizonBridge.norm_pi_neg` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist f : V → ℝ), SGC.norm_pi pi_dist (-f) = SGC.norm_pi pi_dist f`
    - `SGC.Bridge.DefectHorizonBridge.norm_pi_nonneg'` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist f : V → ℝ), 0 ≤ SGC.norm_pi pi_dist f`
    - `SGC.opNorm_set` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → Set ℝ`  [ignores _h_pos]
    - `SGC.opNorm_set_bddBelow` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ), BddBelow (SGC.opNorm_set pi_dist h_pos A)`
    - `SGC.opNorm_pi_bound` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ) (f : V → ℝ), SGC.norm_pi pi_dist (A f) ≤ SGC.opNorm_pi pi_dist h_pos A * SGC.norm_pi pi_dist f`
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.norm_sq_pi_nonneg` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (h : V → ℝ), 0 ≤ SGC.norm_sq_pi pi_dist h`
    - `SGC.norm_sq_pi_eq_zero_iff` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (h : V → ℝ), SGC.norm_sq_pi pi_dist h = 0 ↔ ∀ (v : V), h v = 0`
    - `SGC.opNorm_pi_nonneg` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ), 0 ≤ SGC.opNorm_pi pi_dist h_pos A`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.inner_pi_add_left` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (u v w : V → ℝ), SGC.inner_pi pi_dist (u + v) w = SGC.inner_pi pi_dist u w + SGC.inner_pi pi_dist v w`
    - `SGC.inner_pi_add_right` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (u v w : V → ℝ), SGC.inner_pi pi_dist u (v + w) = SGC.inner_pi pi_dist u v + SGC.inner_pi pi_dist u w`
    - `SGC.inner_pi_comm` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (u v : V → ℝ), SGC.inner_pi pi_dist u v = SGC.inner_pi pi_dist v u`
    - `SGC.cauchy_schwarz_pi` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f g : V → ℝ), |SGC.inner_pi pi_dist f g| ≤ SGC.norm_pi pi_dist f * SGC.norm_pi pi_dist g`
    - `SGC.norm_pi_smul_abs` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (c : ℝ) (f : V → ℝ), SGC.norm_pi pi_dist (c • f) = |c| * SGC.norm_pi pi_dist f`
    - `SGC.norm_pi_pos_of_ne_zero` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f : V → ℝ), f ≠ 0 → 0 < SGC.norm_pi pi_dist f`
    - `SGC.opNorm_set_nonempty` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ), (SGC.opNorm_set pi_dist h_pos A).Nonempty`
    - `SGC.norm_sq_pi_eq_sum` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist h : V → ℝ), SGC.norm_sq_pi pi_dist h = ∑ v, pi_dist v * h v ^ 2`
    - `SGC.sum_quad` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist f g : V → ℝ) (t : ℝ), ∑ v, pi_dist v * (f v + t * g v) ^ 2 = ∑ v, pi_dist v * f v ^ 2 + 2 * t * ∑ v, pi_dist v * (f v * g v) + t ^ 2 * ∑ v, pi_dist v * g v ^ 2`
    - `SGC.sqrt_ineq_of_sq_le` (theorem, SGC.Axioms.Geometry): `∀ (a b c : ℝ), 0 ≤ a → 0 ≤ c → b ^ 2 ≤ a * c → |b| ≤ √a * √c`
    - `SGC.norm_sq_pi_smul` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (c : ℝ) (f : V → ℝ), SGC.norm_sq_pi pi_dist (c • f) = c ^ 2 * SGC.norm_sq_pi pi_dist f`
    - `SGC.iso_L2_to_std` (def, SGC.Axioms.Geometry): `{V : Type u_1} → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) ≃ₗ[ℝ] V → ℝ`
    - `SGC.norm_pi_eq_euclidean_norm` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (f : V → ℝ), SGC.norm_pi pi_dist f = ‖(WithLp.equiv 2 (V → ℝ)).symm ((SGC.iso_L2_to_std pi_dist h_pos) f)‖`
    - `SGC.pointwise_quad` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [Fintype V] [DecidableEq V] (f g : V → ℝ) (t : ℝ) (v : V), (f v + t * g v) ^ 2 = f v ^ 2 + 2 * t * (f v * g v) + t ^ 2 * g v ^ 2`
    - `SGC.inner_pi_smul_left` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (c : ℝ) (u v : V → ℝ), SGC.inner_pi pi_dist (c • u) v = c * SGC.inner_pi pi_dist u v`
    - `SGC.inner_pi_smul_right` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (c : ℝ) (u v : V → ℝ), SGC.inner_pi pi_dist u (c • v) = c * SGC.inner_pi pi_dist u v`
    - `SGC.norm_pi_eq_sqrt_sum_sq` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (f : V → ℝ), SGC.norm_pi pi_dist f = √(∑ v, (SGC.iso_L2_to_std pi_dist h_pos) f v ^ 2)`
    - `SGC.norm_sq_pi_eq_euclidean` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (f : V → ℝ), SGC.norm_sq_pi pi_dist f = ∑ v, (SGC.iso_L2_to_std pi_dist h_pos) f v ^ 2`

### `SGC.Bridge.DefectHorizonBridge.instFiniteDimensionalRealPiMat`

- statement (kernel-elaborated, sha256 `7dff5db7a84e1ad5`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v), FiniteDimensional ℝ (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: hπ
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DefectHorizonBridge.PiMat` (def, SGC.Bridge.DefectHorizonBridge): `(V : Type u_2) → [Fintype V] → [DecidableEq V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Type u_2`  [ignores pi_dist,_hπ]
    - `SGC.Bridge.DefectHorizonBridge.instRingPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → Ring (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`  [ignores pi_dist,hπ]
    - `SGC.Bridge.DefectHorizonBridge.instAlgebraRealPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → Algebra ℝ (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`  [ignores pi_dist,hπ]

### `SGC.Bridge.DefectHorizonBridge.instNormOneClassPiMatOfNonempty`

- statement (kernel-elaborated, sha256 `b6a73185e7f77318`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) [Nonempty V], NormOneClass (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DefectHorizonBridge.PiMat` (def, SGC.Bridge.DefectHorizonBridge): `(V : Type u_2) → [Fintype V] → [DecidableEq V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Type u_2`  [ignores pi_dist,_hπ]
    - `SGC.Bridge.DefectHorizonBridge.instNormedRingPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → NormedRing (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`
    - `SGC.Bridge.DefectHorizonBridge.instRingPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → Ring (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`  [ignores pi_dist,hπ]
    - `SGC.Bridge.DefectHorizonBridge.instNormedAddCommGroupPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → NormedAddCommGroup (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_mul_le` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M N : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ (M * N) ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M * SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ N`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_zero` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ 0 = 0`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_add_le` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M N : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ (M + N) ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M + SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ N`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_neg` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ (-M) = SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_eq_zero` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) {M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ}, SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M = 0 → M = 0`
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.toMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → Matrix V V ℝ`  [ignores pi_dist,hπ]
    - `SGC.opNorm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → ℝ`
    - `SGC.opNorm_pi_comp` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A B : (V → ℝ) →ₗ[ℝ] V → ℝ), SGC.opNorm_pi pi_dist h_pos (A ∘ₗ B) ≤ SGC.opNorm_pi pi_dist h_pos A * SGC.opNorm_pi pi_dist h_pos B`
    - `SGC.opNorm_pi_le_of_bound` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ) (c : ℝ), 0 ≤ c → (∀ (f : V → ℝ), SGC.norm_pi pi_dist (A f) ≤ c * SGC.norm_pi pi_dist f) → SGC.opNorm_pi pi_dist h_pos A ≤ c`
    - `SGC.norm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.norm_pi_eq_zero_iff` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f : V → ℝ), SGC.norm_pi pi_dist f = 0 ↔ f = 0`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_nonneg` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), 0 ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M`
    - `SGC.Approximate.norm_pi_add_le` (theorem, SGC.Renormalization.Approximate): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f g : V → ℝ), SGC.norm_pi pi_dist (f + g) ≤ SGC.norm_pi pi_dist f + SGC.norm_pi pi_dist g`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_mulVec_le` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ) (f : V → ℝ), SGC.norm_pi pi_dist ((SGC.Bridge.DefectHorizonBridge.toMat pi_dist hπ M).mulVec f) ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M * SGC.norm_pi pi_dist f`
    - `SGC.Bridge.DefectHorizonBridge.norm_pi_neg` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist f : V → ℝ), SGC.norm_pi pi_dist (-f) = SGC.norm_pi pi_dist f`
    - `SGC.Bridge.DefectHorizonBridge.norm_pi_nonneg'` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist f : V → ℝ), 0 ≤ SGC.norm_pi pi_dist f`
    - `SGC.opNorm_set` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → Set ℝ`  [ignores _h_pos]
    - `SGC.opNorm_set_bddBelow` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ), BddBelow (SGC.opNorm_set pi_dist h_pos A)`
    - `SGC.opNorm_pi_bound` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ) (f : V → ℝ), SGC.norm_pi pi_dist (A f) ≤ SGC.opNorm_pi pi_dist h_pos A * SGC.norm_pi pi_dist f`
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.norm_sq_pi_nonneg` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (h : V → ℝ), 0 ≤ SGC.norm_sq_pi pi_dist h`
    - `SGC.norm_sq_pi_eq_zero_iff` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (h : V → ℝ), SGC.norm_sq_pi pi_dist h = 0 ↔ ∀ (v : V), h v = 0`
    - `SGC.opNorm_pi_nonneg` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ), 0 ≤ SGC.opNorm_pi pi_dist h_pos A`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.inner_pi_add_left` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (u v w : V → ℝ), SGC.inner_pi pi_dist (u + v) w = SGC.inner_pi pi_dist u w + SGC.inner_pi pi_dist v w`
    - `SGC.inner_pi_add_right` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (u v w : V → ℝ), SGC.inner_pi pi_dist u (v + w) = SGC.inner_pi pi_dist u v + SGC.inner_pi pi_dist u w`
    - `SGC.inner_pi_comm` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (u v : V → ℝ), SGC.inner_pi pi_dist u v = SGC.inner_pi pi_dist v u`
    - `SGC.cauchy_schwarz_pi` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f g : V → ℝ), |SGC.inner_pi pi_dist f g| ≤ SGC.norm_pi pi_dist f * SGC.norm_pi pi_dist g`
    - `SGC.norm_pi_smul_abs` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (c : ℝ) (f : V → ℝ), SGC.norm_pi pi_dist (c • f) = |c| * SGC.norm_pi pi_dist f`
    - `SGC.norm_pi_pos_of_ne_zero` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f : V → ℝ), f ≠ 0 → 0 < SGC.norm_pi pi_dist f`
    - `SGC.opNorm_set_nonempty` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ), (SGC.opNorm_set pi_dist h_pos A).Nonempty`
    - `SGC.norm_sq_pi_eq_sum` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist h : V → ℝ), SGC.norm_sq_pi pi_dist h = ∑ v, pi_dist v * h v ^ 2`
    - `SGC.sum_quad` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist f g : V → ℝ) (t : ℝ), ∑ v, pi_dist v * (f v + t * g v) ^ 2 = ∑ v, pi_dist v * f v ^ 2 + 2 * t * ∑ v, pi_dist v * (f v * g v) + t ^ 2 * ∑ v, pi_dist v * g v ^ 2`
    - `SGC.sqrt_ineq_of_sq_le` (theorem, SGC.Axioms.Geometry): `∀ (a b c : ℝ), 0 ≤ a → 0 ≤ c → b ^ 2 ≤ a * c → |b| ≤ √a * √c`
    - `SGC.norm_sq_pi_smul` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (c : ℝ) (f : V → ℝ), SGC.norm_sq_pi pi_dist (c • f) = c ^ 2 * SGC.norm_sq_pi pi_dist f`
    - `SGC.iso_L2_to_std` (def, SGC.Axioms.Geometry): `{V : Type u_1} → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) ≃ₗ[ℝ] V → ℝ`
    - `SGC.norm_pi_eq_euclidean_norm` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (f : V → ℝ), SGC.norm_pi pi_dist f = ‖(WithLp.equiv 2 (V → ℝ)).symm ((SGC.iso_L2_to_std pi_dist h_pos) f)‖`
    - `SGC.pointwise_quad` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [Fintype V] [DecidableEq V] (f g : V → ℝ) (t : ℝ) (v : V), (f v + t * g v) ^ 2 = f v ^ 2 + 2 * t * (f v * g v) + t ^ 2 * g v ^ 2`
    - `SGC.inner_pi_smul_left` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (c : ℝ) (u v : V → ℝ), SGC.inner_pi pi_dist (c • u) v = c * SGC.inner_pi pi_dist u v`
    - `SGC.inner_pi_smul_right` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (c : ℝ) (u v : V → ℝ), SGC.inner_pi pi_dist u (c • v) = c * SGC.inner_pi pi_dist u v`
    - `SGC.norm_pi_eq_sqrt_sum_sq` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (f : V → ℝ), SGC.norm_pi pi_dist f = √(∑ v, (SGC.iso_L2_to_std pi_dist h_pos) f v ^ 2)`
    - `SGC.norm_sq_pi_eq_euclidean` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (f : V → ℝ), SGC.norm_sq_pi pi_dist f = ∑ v, (SGC.iso_L2_to_std pi_dist h_pos) f v ^ 2`

### `SGC.Bridge.DefectHorizonBridge.mulProjLin_continuous`

- statement (kernel-elaborated, sha256 `8656ab3c347730f1`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (P : SGC.Partition V), Continuous ⇑(SGC.Bridge.DefectHorizonBridge.mulProjLin pi_dist hπ P)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.DefectHorizonBridge.PiMat` (def, SGC.Bridge.DefectHorizonBridge): `(V : Type u_2) → [Fintype V] → [DecidableEq V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Type u_2`  [ignores pi_dist,_hπ]
    - `SGC.Bridge.DefectHorizonBridge.instNormedRingPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → NormedRing (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`
    - `SGC.Bridge.DefectHorizonBridge.instNormedAddCommGroupPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → NormedAddCommGroup (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`
    - `SGC.Bridge.DefectHorizonBridge.instNormedAlgebraRealPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → NormedAlgebra ℝ (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`
    - `SGC.Bridge.DefectHorizonBridge.mulProjLin` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Partition V → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ →ₗ[ℝ] Matrix V V ℝ`
    - `SGC.Bridge.DefectHorizonBridge.instRingPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → Ring (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`  [ignores pi_dist,hπ]
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_mul_le` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M N : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ (M * N) ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M * SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ N`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_zero` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ 0 = 0`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_add_le` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M N : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ (M + N) ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M + SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ N`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_neg` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ (-M) = SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_eq_zero` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) {M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ}, SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M = 0 → M = 0`
    - `SGC.Bridge.DefectHorizonBridge.instAlgebraRealPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → Algebra ℝ (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`  [ignores pi_dist,hπ]
    - `SGC.Bridge.DefectHorizonBridge.toMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → Matrix V V ℝ`  [ignores pi_dist,hπ]
    - `SGC.Approximate.CoarseProjectorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`  [ignores hπ]
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.opNorm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → ℝ`
    - `SGC.opNorm_pi_comp` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A B : (V → ℝ) →ₗ[ℝ] V → ℝ), SGC.opNorm_pi pi_dist h_pos (A ∘ₗ B) ≤ SGC.opNorm_pi pi_dist h_pos A * SGC.opNorm_pi pi_dist h_pos B`
    - `SGC.opNorm_pi_le_of_bound` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ) (c : ℝ), 0 ≤ c → (∀ (f : V → ℝ), SGC.norm_pi pi_dist (A f) ≤ c * SGC.norm_pi pi_dist f) → SGC.opNorm_pi pi_dist h_pos A ≤ c`
    - `SGC.norm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.norm_pi_eq_zero_iff` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f : V → ℝ), SGC.norm_pi pi_dist f = 0 ↔ f = 0`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_nonneg` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), 0 ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M`
    - `SGC.Approximate.norm_pi_add_le` (theorem, SGC.Renormalization.Approximate): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f g : V → ℝ), SGC.norm_pi pi_dist (f + g) ≤ SGC.norm_pi pi_dist f + SGC.norm_pi pi_dist g`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_mulVec_le` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ) (f : V → ℝ), SGC.norm_pi pi_dist ((SGC.Bridge.DefectHorizonBridge.toMat pi_dist hπ M).mulVec f) ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M * SGC.norm_pi pi_dist f`
    - `SGC.Bridge.DefectHorizonBridge.norm_pi_neg` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist f : V → ℝ), SGC.norm_pi pi_dist (-f) = SGC.norm_pi pi_dist f`
    - `SGC.Bridge.DefectHorizonBridge.norm_pi_nonneg'` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist f : V → ℝ), 0 ≤ SGC.norm_pi pi_dist f`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.opNorm_set` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → Set ℝ`  [ignores _h_pos]
    - `SGC.opNorm_set_bddBelow` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ), BddBelow (SGC.opNorm_set pi_dist h_pos A)`
    - `SGC.opNorm_pi_bound` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ) (f : V → ℝ), SGC.norm_pi pi_dist (A f) ≤ SGC.opNorm_pi pi_dist h_pos A * SGC.norm_pi pi_dist f`
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.norm_sq_pi_nonneg` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (h : V → ℝ), 0 ≤ SGC.norm_sq_pi pi_dist h`
    - `SGC.norm_sq_pi_eq_zero_iff` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (h : V → ℝ), SGC.norm_sq_pi pi_dist h = 0 ↔ ∀ (v : V), h v = 0`
    - `SGC.opNorm_pi_nonneg` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ), 0 ≤ SGC.opNorm_pi pi_dist h_pos A`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.inner_pi_add_left` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (u v w : V → ℝ), SGC.inner_pi pi_dist (u + v) w = SGC.inner_pi pi_dist u w + SGC.inner_pi pi_dist v w`
    - `SGC.inner_pi_add_right` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (u v w : V → ℝ), SGC.inner_pi pi_dist u (v + w) = SGC.inner_pi pi_dist u v + SGC.inner_pi pi_dist u w`
    - `SGC.inner_pi_comm` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (u v : V → ℝ), SGC.inner_pi pi_dist u v = SGC.inner_pi pi_dist v u`
    - `SGC.cauchy_schwarz_pi` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f g : V → ℝ), |SGC.inner_pi pi_dist f g| ≤ SGC.norm_pi pi_dist f * SGC.norm_pi pi_dist g`
    - `SGC.norm_pi_smul_abs` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (c : ℝ) (f : V → ℝ), SGC.norm_pi pi_dist (c • f) = |c| * SGC.norm_pi pi_dist f`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.norm_pi_pos_of_ne_zero` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f : V → ℝ), f ≠ 0 → 0 < SGC.norm_pi pi_dist f`
    - `SGC.opNorm_set_nonempty` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ), (SGC.opNorm_set pi_dist h_pos A).Nonempty`
    - `SGC.norm_sq_pi_eq_sum` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist h : V → ℝ), SGC.norm_sq_pi pi_dist h = ∑ v, pi_dist v * h v ^ 2`
    - `SGC.sum_quad` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist f g : V → ℝ) (t : ℝ), ∑ v, pi_dist v * (f v + t * g v) ^ 2 = ∑ v, pi_dist v * f v ^ 2 + 2 * t * ∑ v, pi_dist v * (f v * g v) + t ^ 2 * ∑ v, pi_dist v * g v ^ 2`
    - `SGC.sqrt_ineq_of_sq_le` (theorem, SGC.Axioms.Geometry): `∀ (a b c : ℝ), 0 ≤ a → 0 ≤ c → b ^ 2 ≤ a * c → |b| ≤ √a * √c`
    - `SGC.norm_sq_pi_smul` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (c : ℝ) (f : V → ℝ), SGC.norm_sq_pi pi_dist (c • f) = c ^ 2 * SGC.norm_sq_pi pi_dist f`
    - `SGC.iso_L2_to_std` (def, SGC.Axioms.Geometry): `{V : Type u_1} → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) ≃ₗ[ℝ] V → ℝ`
    - `SGC.norm_pi_eq_euclidean_norm` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (f : V → ℝ), SGC.norm_pi pi_dist f = ‖(WithLp.equiv 2 (V → ℝ)).symm ((SGC.iso_L2_to_std pi_dist h_pos) f)‖`
    - `SGC.pointwise_quad` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [Fintype V] [DecidableEq V] (f g : V → ℝ) (t : ℝ) (v : V), (f v + t * g v) ^ 2 = f v ^ 2 + 2 * t * (f v * g v) + t ^ 2 * g v ^ 2`
    - `SGC.inner_pi_smul_left` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (c : ℝ) (u v : V → ℝ), SGC.inner_pi pi_dist (c • u) v = c * SGC.inner_pi pi_dist u v`
    - `SGC.inner_pi_smul_right` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (c : ℝ) (u v : V → ℝ), SGC.inner_pi pi_dist u (c • v) = c * SGC.inner_pi pi_dist u v`
    - `SGC.norm_pi_eq_sqrt_sum_sq` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (f : V → ℝ), SGC.norm_pi pi_dist f = √(∑ v, (SGC.iso_L2_to_std pi_dist h_pos) f v ^ 2)`
    - `SGC.norm_sq_pi_eq_euclidean` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (f : V → ℝ), SGC.norm_sq_pi pi_dist f = ∑ v, (SGC.iso_L2_to_std pi_dist h_pos) f v ^ 2`

### `SGC.Bridge.DefectHorizonBridge.norm_exp_le`

- statement (kernel-elaborated, sha256 `f6379bc8ad9567b0`):

      ∀ {𝔸 : Type u_2} [inst : NormedRing 𝔸] [NormOneClass 𝔸] [inst_2 : NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (x : 𝔸), ‖NormedSpace.exp ℝ x‖ ≤ Real.exp ‖x‖

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

### `SGC.Bridge.DefectHorizonBridge.norm_pi_neg`

- statement (kernel-elaborated, sha256 `2d7dd41768b0bf1e`):

      ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist f : V → ℝ), SGC.norm_pi pi_dist (-f) = SGC.norm_pi pi_dist f

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.norm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`

### `SGC.Bridge.DefectHorizonBridge.norm_pi_nonneg'`

- statement (kernel-elaborated, sha256 `d10093ff57d79004`):

      ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist f : V → ℝ), 0 ≤ SGC.norm_pi pi_dist f

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.norm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`

### `SGC.Bridge.DefectHorizonBridge.norm_sq_pi_proj_pythagorean`

- statement (kernel-elaborated, sha256 `17bf00fe13324938`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) [Nonempty V] (P : SGC.Partition V) (w : V → ℝ), SGC.norm_sq_pi pi_dist w = SGC.norm_sq_pi pi_dist ((SGC.Approximate.CoarseProjector P pi_dist hπ) w) + SGC.norm_sq_pi pi_dist (w - (SGC.Approximate.CoarseProjector P pi_dist hπ) w)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Approximate.CoarseProjector` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.lift_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → (P.Quot → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Q_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] P.Quot → ℝ`  [ignores _hπ]
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.DefectHorizonBridge.opNorm_exp_eq_pmNorm`

- statement (kernel-elaborated, sha256 `f07e3a2a64ebdf18`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) [Nonempty V] (M : Matrix V V ℝ), SGC.opNorm_pi pi_dist hπ (SGC.Approximate.matrixToLinearMap (NormedSpace.exp ℝ M)) = ‖NormedSpace.exp ℝ (SGC.Bridge.DefectHorizonBridge.ofMat pi_dist hπ M)‖

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.opNorm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → ℝ`
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.PiMat` (def, SGC.Bridge.DefectHorizonBridge): `(V : Type u_2) → [Fintype V] → [DecidableEq V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Type u_2`  [ignores pi_dist,_hπ]
    - `SGC.Bridge.DefectHorizonBridge.instNormedRingPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → NormedRing (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`
    - `SGC.Bridge.DefectHorizonBridge.instRingPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → Ring (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`  [ignores pi_dist,hπ]
    - `SGC.Bridge.DefectHorizonBridge.instAlgebraRealPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → Algebra ℝ (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`  [ignores pi_dist,hπ]
    - `SGC.Bridge.DefectHorizonBridge.ofMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ`  [ignores pi_dist,hπ]
    - `SGC.opNorm_set` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → Set ℝ`  [ignores _h_pos]
    - `SGC.Bridge.DefectHorizonBridge.instNormedAddCommGroupPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → NormedAddCommGroup (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_mul_le` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M N : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ (M * N) ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M * SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ N`
    - `SGC.norm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_zero` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ 0 = 0`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_add_le` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M N : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ (M + N) ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M + SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ N`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_neg` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ (-M) = SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_eq_zero` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) {M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ}, SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M = 0 → M = 0`
    - `SGC.Bridge.DefectHorizonBridge.toMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → Matrix V V ℝ`  [ignores pi_dist,hπ]
    - `SGC.opNorm_pi_comp` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A B : (V → ℝ) →ₗ[ℝ] V → ℝ), SGC.opNorm_pi pi_dist h_pos (A ∘ₗ B) ≤ SGC.opNorm_pi pi_dist h_pos A * SGC.opNorm_pi pi_dist h_pos B`
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.opNorm_pi_le_of_bound` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ) (c : ℝ), 0 ≤ c → (∀ (f : V → ℝ), SGC.norm_pi pi_dist (A f) ≤ c * SGC.norm_pi pi_dist f) → SGC.opNorm_pi pi_dist h_pos A ≤ c`
    - `SGC.norm_pi_eq_zero_iff` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f : V → ℝ), SGC.norm_pi pi_dist f = 0 ↔ f = 0`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_nonneg` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), 0 ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M`
    - `SGC.Approximate.norm_pi_add_le` (theorem, SGC.Renormalization.Approximate): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f g : V → ℝ), SGC.norm_pi pi_dist (f + g) ≤ SGC.norm_pi pi_dist f + SGC.norm_pi pi_dist g`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_mulVec_le` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ) (f : V → ℝ), SGC.norm_pi pi_dist ((SGC.Bridge.DefectHorizonBridge.toMat pi_dist hπ M).mulVec f) ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M * SGC.norm_pi pi_dist f`
    - `SGC.Bridge.DefectHorizonBridge.norm_pi_neg` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist f : V → ℝ), SGC.norm_pi pi_dist (-f) = SGC.norm_pi pi_dist f`
    - `SGC.Bridge.DefectHorizonBridge.norm_pi_nonneg'` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist f : V → ℝ), 0 ≤ SGC.norm_pi pi_dist f`
    - `SGC.opNorm_set_bddBelow` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ), BddBelow (SGC.opNorm_set pi_dist h_pos A)`
    - `SGC.opNorm_pi_bound` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ) (f : V → ℝ), SGC.norm_pi pi_dist (A f) ≤ SGC.opNorm_pi pi_dist h_pos A * SGC.norm_pi pi_dist f`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.norm_sq_pi_nonneg` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (h : V → ℝ), 0 ≤ SGC.norm_sq_pi pi_dist h`
    - `SGC.norm_sq_pi_eq_zero_iff` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (h : V → ℝ), SGC.norm_sq_pi pi_dist h = 0 ↔ ∀ (v : V), h v = 0`
    - `SGC.opNorm_pi_nonneg` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ), 0 ≤ SGC.opNorm_pi pi_dist h_pos A`
    - `SGC.inner_pi_add_left` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (u v w : V → ℝ), SGC.inner_pi pi_dist (u + v) w = SGC.inner_pi pi_dist u w + SGC.inner_pi pi_dist v w`
    - `SGC.inner_pi_add_right` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (u v w : V → ℝ), SGC.inner_pi pi_dist u (v + w) = SGC.inner_pi pi_dist u v + SGC.inner_pi pi_dist u w`
    - `SGC.inner_pi_comm` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (u v : V → ℝ), SGC.inner_pi pi_dist u v = SGC.inner_pi pi_dist v u`
    - `SGC.cauchy_schwarz_pi` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f g : V → ℝ), |SGC.inner_pi pi_dist f g| ≤ SGC.norm_pi pi_dist f * SGC.norm_pi pi_dist g`
    - `SGC.norm_pi_smul_abs` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (c : ℝ) (f : V → ℝ), SGC.norm_pi pi_dist (c • f) = |c| * SGC.norm_pi pi_dist f`
    - `SGC.norm_pi_pos_of_ne_zero` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f : V → ℝ), f ≠ 0 → 0 < SGC.norm_pi pi_dist f`
    - `SGC.opNorm_set_nonempty` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ), (SGC.opNorm_set pi_dist h_pos A).Nonempty`
    - `SGC.norm_sq_pi_eq_sum` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist h : V → ℝ), SGC.norm_sq_pi pi_dist h = ∑ v, pi_dist v * h v ^ 2`
    - `SGC.sum_quad` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist f g : V → ℝ) (t : ℝ), ∑ v, pi_dist v * (f v + t * g v) ^ 2 = ∑ v, pi_dist v * f v ^ 2 + 2 * t * ∑ v, pi_dist v * (f v * g v) + t ^ 2 * ∑ v, pi_dist v * g v ^ 2`
    - `SGC.sqrt_ineq_of_sq_le` (theorem, SGC.Axioms.Geometry): `∀ (a b c : ℝ), 0 ≤ a → 0 ≤ c → b ^ 2 ≤ a * c → |b| ≤ √a * √c`
    - `SGC.norm_sq_pi_smul` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (c : ℝ) (f : V → ℝ), SGC.norm_sq_pi pi_dist (c • f) = c ^ 2 * SGC.norm_sq_pi pi_dist f`
    - `SGC.iso_L2_to_std` (def, SGC.Axioms.Geometry): `{V : Type u_1} → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) ≃ₗ[ℝ] V → ℝ`
    - `SGC.norm_pi_eq_euclidean_norm` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (f : V → ℝ), SGC.norm_pi pi_dist f = ‖(WithLp.equiv 2 (V → ℝ)).symm ((SGC.iso_L2_to_std pi_dist h_pos) f)‖`
    - `SGC.pointwise_quad` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [Fintype V] [DecidableEq V] (f g : V → ℝ) (t : ℝ) (v : V), (f v + t * g v) ^ 2 = f v ^ 2 + 2 * t * (f v * g v) + t ^ 2 * g v ^ 2`
    - `SGC.inner_pi_smul_left` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (c : ℝ) (u v : V → ℝ), SGC.inner_pi pi_dist (c • u) v = c * SGC.inner_pi pi_dist u v`
    - `SGC.inner_pi_smul_right` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (c : ℝ) (u v : V → ℝ), SGC.inner_pi pi_dist u (c • v) = c * SGC.inner_pi pi_dist u v`
    - `SGC.norm_pi_eq_sqrt_sum_sq` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (f : V → ℝ), SGC.norm_pi pi_dist f = √(∑ v, (SGC.iso_L2_to_std pi_dist h_pos) f v ^ 2)`
    - `SGC.norm_sq_pi_eq_euclidean` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (f : V → ℝ), SGC.norm_sq_pi pi_dist f = ∑ v, (SGC.iso_L2_to_std pi_dist h_pos) f v ^ 2`

### `SGC.Bridge.DefectHorizonBridge.pmNorm_add_le`

- statement (kernel-elaborated, sha256 `2a0d96b73e6fe981`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M N : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ (M + N) ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M + SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ N

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DefectHorizonBridge.PiMat` (def, SGC.Bridge.DefectHorizonBridge): `(V : Type u_2) → [Fintype V] → [DecidableEq V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Type u_2`  [ignores pi_dist,_hπ]
    - `SGC.Bridge.DefectHorizonBridge.pmNorm` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.instRingPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → Ring (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`  [ignores pi_dist,hπ]
    - `SGC.opNorm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → ℝ`
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.toMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → Matrix V V ℝ`  [ignores pi_dist,hπ]
    - `SGC.opNorm_set` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → Set ℝ`  [ignores _h_pos]
    - `SGC.norm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`

### `SGC.Bridge.DefectHorizonBridge.pmNorm_def`

- statement (kernel-elaborated, sha256 `018dba08f40cac62`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), ‖M‖ = SGC.opNorm_pi pi_dist hπ (SGC.Approximate.matrixToLinearMap (SGC.Bridge.DefectHorizonBridge.toMat pi_dist hπ M))

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=rfl vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DefectHorizonBridge.PiMat` (def, SGC.Bridge.DefectHorizonBridge): `(V : Type u_2) → [Fintype V] → [DecidableEq V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Type u_2`  [ignores pi_dist,_hπ]
    - `SGC.Bridge.DefectHorizonBridge.instNormedAddCommGroupPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → NormedAddCommGroup (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`
    - `SGC.opNorm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → ℝ`
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.toMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → Matrix V V ℝ`  [ignores pi_dist,hπ]
    - `SGC.Bridge.DefectHorizonBridge.instRingPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → Ring (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`  [ignores pi_dist,hπ]
    - `SGC.Bridge.DefectHorizonBridge.pmNorm` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_zero` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ 0 = 0`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_add_le` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M N : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ (M + N) ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M + SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ N`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_neg` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ (-M) = SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_eq_zero` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) {M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ}, SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M = 0 → M = 0`
    - `SGC.opNorm_set` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → Set ℝ`  [ignores _h_pos]
    - `SGC.opNorm_pi_le_of_bound` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ) (c : ℝ), 0 ≤ c → (∀ (f : V → ℝ), SGC.norm_pi pi_dist (A f) ≤ c * SGC.norm_pi pi_dist f) → SGC.opNorm_pi pi_dist h_pos A ≤ c`
    - `SGC.norm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.norm_pi_eq_zero_iff` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f : V → ℝ), SGC.norm_pi pi_dist f = 0 ↔ f = 0`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_nonneg` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), 0 ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M`
    - `SGC.Approximate.norm_pi_add_le` (theorem, SGC.Renormalization.Approximate): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f g : V → ℝ), SGC.norm_pi pi_dist (f + g) ≤ SGC.norm_pi pi_dist f + SGC.norm_pi pi_dist g`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_mulVec_le` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ) (f : V → ℝ), SGC.norm_pi pi_dist ((SGC.Bridge.DefectHorizonBridge.toMat pi_dist hπ M).mulVec f) ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M * SGC.norm_pi pi_dist f`
    - `SGC.Bridge.DefectHorizonBridge.norm_pi_neg` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist f : V → ℝ), SGC.norm_pi pi_dist (-f) = SGC.norm_pi pi_dist f`
    - `SGC.Bridge.DefectHorizonBridge.norm_pi_nonneg'` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist f : V → ℝ), 0 ≤ SGC.norm_pi pi_dist f`
    - `SGC.opNorm_set_bddBelow` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ), BddBelow (SGC.opNorm_set pi_dist h_pos A)`
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.norm_sq_pi_nonneg` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (h : V → ℝ), 0 ≤ SGC.norm_sq_pi pi_dist h`
    - `SGC.norm_sq_pi_eq_zero_iff` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (h : V → ℝ), SGC.norm_sq_pi pi_dist h = 0 ↔ ∀ (v : V), h v = 0`
    - `SGC.opNorm_pi_nonneg` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ), 0 ≤ SGC.opNorm_pi pi_dist h_pos A`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.inner_pi_add_left` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (u v w : V → ℝ), SGC.inner_pi pi_dist (u + v) w = SGC.inner_pi pi_dist u w + SGC.inner_pi pi_dist v w`
    - `SGC.inner_pi_add_right` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (u v w : V → ℝ), SGC.inner_pi pi_dist u (v + w) = SGC.inner_pi pi_dist u v + SGC.inner_pi pi_dist u w`
    - `SGC.inner_pi_comm` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (u v : V → ℝ), SGC.inner_pi pi_dist u v = SGC.inner_pi pi_dist v u`
    - `SGC.cauchy_schwarz_pi` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f g : V → ℝ), |SGC.inner_pi pi_dist f g| ≤ SGC.norm_pi pi_dist f * SGC.norm_pi pi_dist g`
    - `SGC.opNorm_pi_bound` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ) (f : V → ℝ), SGC.norm_pi pi_dist (A f) ≤ SGC.opNorm_pi pi_dist h_pos A * SGC.norm_pi pi_dist f`
    - `SGC.norm_pi_smul_abs` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (c : ℝ) (f : V → ℝ), SGC.norm_pi pi_dist (c • f) = |c| * SGC.norm_pi pi_dist f`
    - `SGC.norm_sq_pi_eq_sum` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist h : V → ℝ), SGC.norm_sq_pi pi_dist h = ∑ v, pi_dist v * h v ^ 2`
    - `SGC.sum_quad` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist f g : V → ℝ) (t : ℝ), ∑ v, pi_dist v * (f v + t * g v) ^ 2 = ∑ v, pi_dist v * f v ^ 2 + 2 * t * ∑ v, pi_dist v * (f v * g v) + t ^ 2 * ∑ v, pi_dist v * g v ^ 2`
    - `SGC.sqrt_ineq_of_sq_le` (theorem, SGC.Axioms.Geometry): `∀ (a b c : ℝ), 0 ≤ a → 0 ≤ c → b ^ 2 ≤ a * c → |b| ≤ √a * √c`
    - `SGC.norm_pi_pos_of_ne_zero` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f : V → ℝ), f ≠ 0 → 0 < SGC.norm_pi pi_dist f`
    - `SGC.opNorm_set_nonempty` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ), (SGC.opNorm_set pi_dist h_pos A).Nonempty`
    - `SGC.norm_sq_pi_smul` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (c : ℝ) (f : V → ℝ), SGC.norm_sq_pi pi_dist (c • f) = c ^ 2 * SGC.norm_sq_pi pi_dist f`
    - `SGC.pointwise_quad` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [Fintype V] [DecidableEq V] (f g : V → ℝ) (t : ℝ) (v : V), (f v + t * g v) ^ 2 = f v ^ 2 + 2 * t * (f v * g v) + t ^ 2 * g v ^ 2`
    - `SGC.iso_L2_to_std` (def, SGC.Axioms.Geometry): `{V : Type u_1} → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) ≃ₗ[ℝ] V → ℝ`
    - `SGC.norm_pi_eq_euclidean_norm` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (f : V → ℝ), SGC.norm_pi pi_dist f = ‖(WithLp.equiv 2 (V → ℝ)).symm ((SGC.iso_L2_to_std pi_dist h_pos) f)‖`
    - `SGC.inner_pi_smul_left` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (c : ℝ) (u v : V → ℝ), SGC.inner_pi pi_dist (c • u) v = c * SGC.inner_pi pi_dist u v`
    - `SGC.inner_pi_smul_right` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (c : ℝ) (u v : V → ℝ), SGC.inner_pi pi_dist u (c • v) = c * SGC.inner_pi pi_dist u v`
    - `SGC.norm_pi_eq_sqrt_sum_sq` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (f : V → ℝ), SGC.norm_pi pi_dist f = √(∑ v, (SGC.iso_L2_to_std pi_dist h_pos) f v ^ 2)`
    - `SGC.norm_sq_pi_eq_euclidean` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (f : V → ℝ), SGC.norm_sq_pi pi_dist f = ∑ v, (SGC.iso_L2_to_std pi_dist h_pos) f v ^ 2`

### `SGC.Bridge.DefectHorizonBridge.pmNorm_eq_zero`

- statement (kernel-elaborated, sha256 `00b4b6657765ac3d`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) {M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ}, SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M = 0 → M = 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DefectHorizonBridge.PiMat` (def, SGC.Bridge.DefectHorizonBridge): `(V : Type u_2) → [Fintype V] → [DecidableEq V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Type u_2`  [ignores pi_dist,_hπ]
    - `SGC.Bridge.DefectHorizonBridge.pmNorm` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.instRingPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → Ring (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`  [ignores pi_dist,hπ]
    - `SGC.opNorm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → ℝ`
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.toMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → Matrix V V ℝ`  [ignores pi_dist,hπ]
    - `SGC.opNorm_set` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → Set ℝ`  [ignores _h_pos]
    - `SGC.norm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`

### `SGC.Bridge.DefectHorizonBridge.pmNorm_mulVec_le`

- statement (kernel-elaborated, sha256 `da634f0cc5990370`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ) (f : V → ℝ), SGC.norm_pi pi_dist ((SGC.Bridge.DefectHorizonBridge.toMat pi_dist hπ M).mulVec f) ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M * SGC.norm_pi pi_dist f

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DefectHorizonBridge.PiMat` (def, SGC.Bridge.DefectHorizonBridge): `(V : Type u_2) → [Fintype V] → [DecidableEq V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Type u_2`  [ignores pi_dist,_hπ]
    - `SGC.norm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.toMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → Matrix V V ℝ`  [ignores pi_dist,hπ]
    - `SGC.Bridge.DefectHorizonBridge.pmNorm` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → ℝ`
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.opNorm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → ℝ`
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.opNorm_set` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → Set ℝ`  [ignores _h_pos]

### `SGC.Bridge.DefectHorizonBridge.pmNorm_mul_le`

- statement (kernel-elaborated, sha256 `734a43f33cf9d1ff`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M N : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ (M * N) ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M * SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ N

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DefectHorizonBridge.PiMat` (def, SGC.Bridge.DefectHorizonBridge): `(V : Type u_2) → [Fintype V] → [DecidableEq V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Type u_2`  [ignores pi_dist,_hπ]
    - `SGC.Bridge.DefectHorizonBridge.pmNorm` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.instRingPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → Ring (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`  [ignores pi_dist,hπ]
    - `SGC.opNorm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → ℝ`
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.toMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → Matrix V V ℝ`  [ignores pi_dist,hπ]
    - `SGC.opNorm_set` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → Set ℝ`  [ignores _h_pos]
    - `SGC.norm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`

### `SGC.Bridge.DefectHorizonBridge.pmNorm_neg`

- statement (kernel-elaborated, sha256 `58a9177ba087822e`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ (-M) = SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DefectHorizonBridge.PiMat` (def, SGC.Bridge.DefectHorizonBridge): `(V : Type u_2) → [Fintype V] → [DecidableEq V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Type u_2`  [ignores pi_dist,_hπ]
    - `SGC.Bridge.DefectHorizonBridge.pmNorm` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.instRingPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → Ring (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`  [ignores pi_dist,hπ]
    - `SGC.opNorm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → ℝ`
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.toMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → Matrix V V ℝ`  [ignores pi_dist,hπ]
    - `SGC.opNorm_set` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → Set ℝ`  [ignores _h_pos]
    - `SGC.norm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`

### `SGC.Bridge.DefectHorizonBridge.pmNorm_nonneg`

- statement (kernel-elaborated, sha256 `b662492b37c20f77`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), 0 ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DefectHorizonBridge.PiMat` (def, SGC.Bridge.DefectHorizonBridge): `(V : Type u_2) → [Fintype V] → [DecidableEq V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Type u_2`  [ignores pi_dist,_hπ]
    - `SGC.Bridge.DefectHorizonBridge.pmNorm` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → ℝ`
    - `SGC.opNorm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → ℝ`
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.toMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → Matrix V V ℝ`  [ignores pi_dist,hπ]
    - `SGC.opNorm_set` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → Set ℝ`  [ignores _h_pos]
    - `SGC.norm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`

### `SGC.Bridge.DefectHorizonBridge.pmNorm_smul_le`

- statement (kernel-elaborated, sha256 `f2072f73ad9b0d4a`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (c : ℝ) (M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ (c • M) ≤ |c| * SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DefectHorizonBridge.PiMat` (def, SGC.Bridge.DefectHorizonBridge): `(V : Type u_2) → [Fintype V] → [DecidableEq V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Type u_2`  [ignores pi_dist,_hπ]
    - `SGC.Bridge.DefectHorizonBridge.pmNorm` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.instRingPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → Ring (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`  [ignores pi_dist,hπ]
    - `SGC.Bridge.DefectHorizonBridge.instAlgebraRealPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → Algebra ℝ (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`  [ignores pi_dist,hπ]
    - `SGC.opNorm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → ℝ`
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.toMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → Matrix V V ℝ`  [ignores pi_dist,hπ]
    - `SGC.opNorm_set` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → Set ℝ`  [ignores _h_pos]
    - `SGC.norm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`

### `SGC.Bridge.DefectHorizonBridge.pmNorm_zero`

- statement (kernel-elaborated, sha256 `d8498cc44202705c`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ 0 = 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DefectHorizonBridge.pmNorm` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.PiMat` (def, SGC.Bridge.DefectHorizonBridge): `(V : Type u_2) → [Fintype V] → [DecidableEq V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Type u_2`  [ignores pi_dist,_hπ]
    - `SGC.Bridge.DefectHorizonBridge.instRingPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → Ring (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`  [ignores pi_dist,hπ]
    - `SGC.opNorm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → ℝ`
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.toMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → Matrix V V ℝ`  [ignores pi_dist,hπ]
    - `SGC.opNorm_set` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → Set ℝ`  [ignores _h_pos]
    - `SGC.norm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`

### `SGC.Bridge.DefectHorizonBridge.proj_mul_coarseGen`

- statement (kernel-elaborated, sha256 `705c1aa630352e13`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) [Nonempty V] (L : Matrix V V ℝ) (P : SGC.Partition V), SGC.Approximate.CoarseProjectorMatrix P pi_dist hπ * SGC.Approximate.CoarseGeneratorMatrix L P pi_dist hπ = SGC.Approximate.CoarseGeneratorMatrix L P pi_dist hπ

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Approximate.CoarseProjectorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`  [ignores hπ]
    - `SGC.Approximate.CoarseGeneratorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.DefectHorizonBridge.smul_defectComplement_pow_mul_proj`

- statement (kernel-elaborated, sha256 `59baca325899dd51`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (L : Matrix V V ℝ) (P : SGC.Partition V) (t : ℝ) (n : ℕ), (t • (L - SGC.Bridge.DefectHorizonBridge.DefectMatrix L P pi_dist hπ)) ^ n * SGC.Approximate.CoarseProjectorMatrix P pi_dist hπ = (t • SGC.Approximate.CoarseGeneratorMatrix L P pi_dist hπ) ^ n * SGC.Approximate.CoarseProjectorMatrix P pi_dist hπ

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.DefectHorizonBridge.DefectMatrix` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.Approximate.CoarseProjectorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`  [ignores hπ]
    - `SGC.Approximate.CoarseGeneratorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.DefectHorizonBridge.toMatLin_continuous`

- statement (kernel-elaborated, sha256 `51b723b090336918`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v), Continuous ⇑(SGC.Bridge.DefectHorizonBridge.toMatLin pi_dist hπ)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DefectHorizonBridge.PiMat` (def, SGC.Bridge.DefectHorizonBridge): `(V : Type u_2) → [Fintype V] → [DecidableEq V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Type u_2`  [ignores pi_dist,_hπ]
    - `SGC.Bridge.DefectHorizonBridge.instNormedRingPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → NormedRing (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`
    - `SGC.Bridge.DefectHorizonBridge.instNormedAddCommGroupPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → NormedAddCommGroup (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`
    - `SGC.Bridge.DefectHorizonBridge.instNormedAlgebraRealPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → NormedAlgebra ℝ (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`
    - `SGC.Bridge.DefectHorizonBridge.toMatLin` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ →ₗ[ℝ] Matrix V V ℝ`
    - `SGC.Bridge.DefectHorizonBridge.instRingPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → Ring (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`  [ignores pi_dist,hπ]
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_mul_le` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M N : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ (M * N) ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M * SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ N`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_zero` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ 0 = 0`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_add_le` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M N : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ (M + N) ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M + SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ N`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_neg` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ (-M) = SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_eq_zero` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) {M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ}, SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M = 0 → M = 0`
    - `SGC.Bridge.DefectHorizonBridge.instAlgebraRealPiMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → Algebra ℝ (SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ)`  [ignores pi_dist,hπ]
    - `SGC.Bridge.DefectHorizonBridge.toMat` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → (hπ : ∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ → Matrix V V ℝ`  [ignores pi_dist,hπ]
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.opNorm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → ℝ`
    - `SGC.opNorm_pi_comp` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A B : (V → ℝ) →ₗ[ℝ] V → ℝ), SGC.opNorm_pi pi_dist h_pos (A ∘ₗ B) ≤ SGC.opNorm_pi pi_dist h_pos A * SGC.opNorm_pi pi_dist h_pos B`
    - `SGC.opNorm_pi_le_of_bound` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ) (c : ℝ), 0 ≤ c → (∀ (f : V → ℝ), SGC.norm_pi pi_dist (A f) ≤ c * SGC.norm_pi pi_dist f) → SGC.opNorm_pi pi_dist h_pos A ≤ c`
    - `SGC.norm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.norm_pi_eq_zero_iff` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f : V → ℝ), SGC.norm_pi pi_dist f = 0 ↔ f = 0`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_nonneg` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ), 0 ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M`
    - `SGC.Approximate.norm_pi_add_le` (theorem, SGC.Renormalization.Approximate): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f g : V → ℝ), SGC.norm_pi pi_dist (f + g) ≤ SGC.norm_pi pi_dist f + SGC.norm_pi pi_dist g`
    - `SGC.Bridge.DefectHorizonBridge.pmNorm_mulVec_le` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (M : SGC.Bridge.DefectHorizonBridge.PiMat V pi_dist hπ) (f : V → ℝ), SGC.norm_pi pi_dist ((SGC.Bridge.DefectHorizonBridge.toMat pi_dist hπ M).mulVec f) ≤ SGC.Bridge.DefectHorizonBridge.pmNorm pi_dist hπ M * SGC.norm_pi pi_dist f`
    - `SGC.Bridge.DefectHorizonBridge.norm_pi_neg` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist f : V → ℝ), SGC.norm_pi pi_dist (-f) = SGC.norm_pi pi_dist f`
    - `SGC.Bridge.DefectHorizonBridge.norm_pi_nonneg'` (theorem, SGC.Bridge.DefectHorizonBridge): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist f : V → ℝ), 0 ≤ SGC.norm_pi pi_dist f`
    - `SGC.opNorm_set` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → Set ℝ`  [ignores _h_pos]
    - `SGC.opNorm_set_bddBelow` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ), BddBelow (SGC.opNorm_set pi_dist h_pos A)`
    - `SGC.opNorm_pi_bound` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ) (f : V → ℝ), SGC.norm_pi pi_dist (A f) ≤ SGC.opNorm_pi pi_dist h_pos A * SGC.norm_pi pi_dist f`
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.norm_sq_pi_nonneg` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (h : V → ℝ), 0 ≤ SGC.norm_sq_pi pi_dist h`
    - `SGC.norm_sq_pi_eq_zero_iff` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (h : V → ℝ), SGC.norm_sq_pi pi_dist h = 0 ↔ ∀ (v : V), h v = 0`
    - `SGC.opNorm_pi_nonneg` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ), 0 ≤ SGC.opNorm_pi pi_dist h_pos A`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.inner_pi_add_left` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (u v w : V → ℝ), SGC.inner_pi pi_dist (u + v) w = SGC.inner_pi pi_dist u w + SGC.inner_pi pi_dist v w`
    - `SGC.inner_pi_add_right` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (u v w : V → ℝ), SGC.inner_pi pi_dist u (v + w) = SGC.inner_pi pi_dist u v + SGC.inner_pi pi_dist u w`
    - `SGC.inner_pi_comm` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (u v : V → ℝ), SGC.inner_pi pi_dist u v = SGC.inner_pi pi_dist v u`
    - `SGC.cauchy_schwarz_pi` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f g : V → ℝ), |SGC.inner_pi pi_dist f g| ≤ SGC.norm_pi pi_dist f * SGC.norm_pi pi_dist g`
    - `SGC.norm_pi_smul_abs` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (c : ℝ) (f : V → ℝ), SGC.norm_pi pi_dist (c • f) = |c| * SGC.norm_pi pi_dist f`
    - `SGC.norm_pi_pos_of_ne_zero` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (f : V → ℝ), f ≠ 0 → 0 < SGC.norm_pi pi_dist f`
    - `SGC.opNorm_set_nonempty` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] V → ℝ), (SGC.opNorm_set pi_dist h_pos A).Nonempty`
    - `SGC.norm_sq_pi_eq_sum` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist h : V → ℝ), SGC.norm_sq_pi pi_dist h = ∑ v, pi_dist v * h v ^ 2`
    - `SGC.sum_quad` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist f g : V → ℝ) (t : ℝ), ∑ v, pi_dist v * (f v + t * g v) ^ 2 = ∑ v, pi_dist v * f v ^ 2 + 2 * t * ∑ v, pi_dist v * (f v * g v) + t ^ 2 * ∑ v, pi_dist v * g v ^ 2`
    - `SGC.sqrt_ineq_of_sq_le` (theorem, SGC.Axioms.Geometry): `∀ (a b c : ℝ), 0 ≤ a → 0 ≤ c → b ^ 2 ≤ a * c → |b| ≤ √a * √c`
    - `SGC.norm_sq_pi_smul` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (c : ℝ) (f : V → ℝ), SGC.norm_sq_pi pi_dist (c • f) = c ^ 2 * SGC.norm_sq_pi pi_dist f`
    - `SGC.iso_L2_to_std` (def, SGC.Axioms.Geometry): `{V : Type u_1} → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) ≃ₗ[ℝ] V → ℝ`
    - `SGC.norm_pi_eq_euclidean_norm` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (f : V → ℝ), SGC.norm_pi pi_dist f = ‖(WithLp.equiv 2 (V → ℝ)).symm ((SGC.iso_L2_to_std pi_dist h_pos) f)‖`
    - `SGC.pointwise_quad` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [Fintype V] [DecidableEq V] (f g : V → ℝ) (t : ℝ) (v : V), (f v + t * g v) ^ 2 = f v ^ 2 + 2 * t * (f v * g v) + t ^ 2 * g v ^ 2`
    - `SGC.inner_pi_smul_left` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (c : ℝ) (u v : V → ℝ), SGC.inner_pi pi_dist (c • u) v = c * SGC.inner_pi pi_dist u v`
    - `SGC.inner_pi_smul_right` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {pi_dist : V → ℝ} (c : ℝ) (u v : V → ℝ), SGC.inner_pi pi_dist u (c • v) = c * SGC.inner_pi pi_dist u v`
    - `SGC.norm_pi_eq_sqrt_sum_sq` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (f : V → ℝ), SGC.norm_pi pi_dist f = √(∑ v, (SGC.iso_L2_to_std pi_dist h_pos) f v ^ 2)`
    - `SGC.norm_sq_pi_eq_euclidean` (theorem, SGC.Axioms.Geometry): `∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (pi_dist : V → ℝ) (h_pos : ∀ (v : V), 0 < pi_dist v) (f : V → ℝ), SGC.norm_sq_pi pi_dist f = ∑ v, (SGC.iso_L2_to_std pi_dist h_pos) f v ^ 2`

### `SGC.Bridge.DefectHorizonBridge.total_error_pythagorean`

- statement (kernel-elaborated, sha256 `1acce55fe361538e`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) [Nonempty V] (L : Matrix V V ℝ) (P : SGC.Partition V) (t : ℝ) (f₀ : V → ℝ), f₀ = (SGC.Approximate.CoarseProjector P pi_dist hπ) f₀ → SGC.norm_sq_pi pi_dist ((SGC.Approximate.HeatKernelMap L t) f₀ - (SGC.Approximate.HeatKernelMap (SGC.Approximate.CoarseGeneratorMatrix L P pi_dist hπ) t) f₀) = SGC.norm_sq_pi pi_dist ((SGC.Approximate.CoarseProjector P pi_dist hπ) ((SGC.Approximate.HeatKernelMap L t) f₀) - (SGC.Approximate.HeatKernelMap (SGC.Approximate.CoarseGeneratorMatrix L P pi_dist hπ) t) f₀) + SGC.norm_sq_pi pi_dist ((SGC.Approximate.HeatKernelMap L t) f₀ - (SGC.Approximate.CoarseProjector P pi_dist hπ) ((SGC.Approximate.HeatKernelMap L t) f₀))

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Approximate.CoarseProjector` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Approximate.HeatKernelMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.CoarseGeneratorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.lift_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → (P.Quot → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Q_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] P.Quot → ℝ`  [ignores _hπ]
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.HeatKernel` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → Matrix V V ℝ`
    - `SGC.Approximate.CoarseProjectorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`  [ignores hπ]
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.DefectHorizonBridge.trajectory_closure_bound_explicit`

- statement (kernel-elaborated, sha256 `567b4fb53671f919`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) [Nonempty V] (L : Matrix V V ℝ) (P : SGC.Partition V) (ε : ℝ), SGC.Approximate.IsApproxLumpable L P pi_dist hπ ε → ∀ (t : ℝ), 0 ≤ t → ∀ (f₀ : V → ℝ), f₀ = (SGC.Approximate.CoarseProjector P pi_dist hπ) f₀ → SGC.norm_pi pi_dist ((SGC.Approximate.HeatKernelMap L t) f₀ - (SGC.Approximate.HeatKernelMap (SGC.Approximate.CoarseGeneratorMatrix L P pi_dist hπ) t) f₀) ≤ t * ε * Real.exp (t * (SGC.opNorm_pi pi_dist hπ (SGC.Approximate.matrixToLinearMap (L - SGC.Bridge.DefectHorizonBridge.DefectMatrix L P pi_dist hπ)) + ε)) * SGC.norm_pi pi_dist f₀

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Approximate.IsApproxLumpable` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ℝ → Prop`
    - `SGC.Approximate.CoarseProjector` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.norm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Approximate.HeatKernelMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.CoarseGeneratorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.opNorm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → ℝ`
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.DefectMatrix` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.Approximate.DefectOperator` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.lift_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → (P.Quot → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Q_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] P.Quot → ℝ`  [ignores _hπ]
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Approximate.HeatKernel` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → Matrix V V ℝ`
    - `SGC.Approximate.CoarseProjectorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`  [ignores hπ]
    - `SGC.opNorm_set` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → Set ℝ`  [ignores _h_pos]
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.DefectHorizonBridge.vertical_closure_bound_explicit`

- statement (kernel-elaborated, sha256 `b4bb4738b9d29d2c`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) [Nonempty V] (L : Matrix V V ℝ) (P : SGC.Partition V) (ε : ℝ), SGC.Approximate.IsApproxLumpable L P pi_dist hπ ε → ∀ (t : ℝ), 0 ≤ t → ∀ (f₀ : V → ℝ), f₀ = (SGC.Approximate.CoarseProjector P pi_dist hπ) f₀ → SGC.norm_pi pi_dist ((SGC.Approximate.HeatKernelMap L t) f₀ - (SGC.Approximate.CoarseProjector P pi_dist hπ) ((SGC.Approximate.HeatKernelMap L t) f₀)) ≤ t * ε * Real.exp (t * (SGC.opNorm_pi pi_dist hπ (SGC.Approximate.matrixToLinearMap (L - SGC.Bridge.DefectHorizonBridge.DefectMatrix L P pi_dist hπ)) + ε)) * SGC.norm_pi pi_dist f₀

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Approximate.IsApproxLumpable` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ℝ → Prop`
    - `SGC.Approximate.CoarseProjector` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.norm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Approximate.HeatKernelMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.opNorm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → ℝ`
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.DefectMatrix` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.Approximate.DefectOperator` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.lift_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → (P.Quot → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Q_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] P.Quot → ℝ`  [ignores _hπ]
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Approximate.HeatKernel` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → Matrix V V ℝ`
    - `SGC.opNorm_set` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → Set ℝ`  [ignores _h_pos]
    - `SGC.Approximate.CoarseProjectorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`  [ignores hπ]
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.DefectHorizonBridge.vertical_defect_horizon_bound`

- statement (kernel-elaborated, sha256 `a5eb4036c7d17ef0`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) [Nonempty V] (L : Matrix V V ℝ) (P : SGC.Partition V) (t : ℝ), 0 ≤ t → ∀ (f₀ : V → ℝ), f₀ = (SGC.Approximate.CoarseProjector P pi_dist hπ) f₀ → SGC.norm_pi pi_dist ((SGC.Approximate.HeatKernelMap L t) f₀ - (SGC.Approximate.CoarseProjector P pi_dist hπ) ((SGC.Approximate.HeatKernelMap L t) f₀)) ≤ t * SGC.opNorm_pi pi_dist hπ (SGC.Approximate.DefectOperator L P pi_dist hπ) * Real.exp (t * (SGC.opNorm_pi pi_dist hπ (SGC.Approximate.matrixToLinearMap (L - SGC.Bridge.DefectHorizonBridge.DefectMatrix L P pi_dist hπ)) + SGC.opNorm_pi pi_dist hπ (SGC.Approximate.DefectOperator L P pi_dist hπ))) * SGC.norm_pi pi_dist f₀

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Approximate.CoarseProjector` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.norm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Approximate.HeatKernelMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.opNorm_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → ℝ`
    - `SGC.Approximate.DefectOperator` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Approximate.matrixToLinearMap` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Bridge.DefectHorizonBridge.DefectMatrix` (def, SGC.Bridge.DefectHorizonBridge): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.lift_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → (P.Quot → ℝ) →ₗ[ℝ] V → ℝ`
    - `SGC.Q_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → (V → ℝ) →ₗ[ℝ] P.Quot → ℝ`  [ignores _hπ]
    - `SGC.norm_sq_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Approximate.HeatKernel` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [DecidableEq V] → Matrix V V ℝ → ℝ → Matrix V V ℝ`
    - `SGC.opNorm_set` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → ((V → ℝ) →ₗ[ℝ] V → ℝ) → Set ℝ`  [ignores _h_pos]
    - `SGC.Approximate.CoarseProjectorMatrix` (def, SGC.Renormalization.Approximate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → SGC.Partition V → (pi_dist : V → ℝ) → (∀ (v : V), 0 < pi_dist v) → Matrix V V ℝ`  [ignores hπ]
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.DiscreteFluidDynamics.coarse_current_eq_sum_fine`

- statement (kernel-elaborated, sha256 `03b9a7d0ab1a6f42`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (A B : P.Quot), SGC.Thermodynamics.ProbabilityCurrent (SGC.Thermodynamics.CoarseGenerator L P pi_dist) (SGC.pi_bar P pi_dist) A B = ∑ x, ∑ y, if P.quot_map x = A ∧ P.quot_map y = B then SGC.Thermodynamics.ProbabilityCurrent L pi_dist x y else 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Thermodynamics.ProbabilityCurrent` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → V → V → ℝ`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.DiscreteFluidDynamics.current_zero_iff_reversible`

- statement (kernel-elaborated, sha256 `1456ce1955b310ec`):

      ∀ {V : Type u_1} [Fintype V] [DecidableEq V] (L : Matrix V V ℝ) (pi_dist : V → ℝ), (∀ (x y : V), SGC.Thermodynamics.ProbabilityCurrent L pi_dist x y = 0) ↔ SGC.Thermodynamics.DetailedBalance L pi_dist

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Thermodynamics.ProbabilityCurrent` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → V → V → ℝ`
    - `SGC.Thermodynamics.DetailedBalance` (def, SGC.Thermodynamics.FluxDecomposition): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → Prop`

### `SGC.Bridge.DiscreteFluidDynamics.cycle_of_pos_cycleSpace_field`

- statement (kernel-elaborated, sha256 `a956541ea31cf022`):

      ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {J : V → V → ℝ}, SGC.Bridge.DiscreteFluidDynamics.InCycleSpace J → ∀ {x₀ y₀ : V}, 0 < J x₀ y₀ → ∃ len c, 0 < len ∧ c 0 = c len ∧ ∀ m < len, 0 < J (c m) (c (m + 1))

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DiscreteFluidDynamics.InCycleSpace` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → [Fintype V] → (V → V → ℝ) → Prop`
    - `SGC.Bridge.DiscreteFluidDynamics.divergence` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → [Fintype V] → (V → V → ℝ) → V → ℝ`

### `SGC.Bridge.DiscreteFluidDynamics.damped_validity_budget`

- statement (kernel-elaborated, sha256 `0223293350281f2a`):

      ∀ {ν ε : ℝ}, 0 < ν → 0 < ε → (∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(ν * t))) * (1 / ε) = 1 / (ν * ε)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: _hε
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

### `SGC.Bridge.DiscreteFluidDynamics.divergence_current_eq_neg_residual`

- statement (kernel-elaborated, sha256 `b947b82904febd42`):

      ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (L : Matrix V V ℝ) (pi_dist : V → ℝ), (∀ (x : V), ∑ y, L x y = 0) → ∀ (x : V), SGC.Bridge.DiscreteFluidDynamics.divergence (SGC.Thermodynamics.ProbabilityCurrent L pi_dist) x = -∑ z, pi_dist z * L z x

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DiscreteFluidDynamics.divergence` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → [Fintype V] → (V → V → ℝ) → V → ℝ`
    - `SGC.Thermodynamics.ProbabilityCurrent` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → V → V → ℝ`

### `SGC.Bridge.DiscreteFluidDynamics.edgeInner_gradient_eq`

- statement (kernel-elaborated, sha256 `1ea036ab09a5b088`):

      ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (ω : V → V → ℝ), (∀ (x y : V), ω x y = -ω y x) → ∀ (f : V → ℝ), SGC.Bridge.DiscreteFluidDynamics.edgeInner ω (SGC.Bridge.DiscreteFluidDynamics.gradientField f) = -2 * ∑ x, f x * SGC.Bridge.DiscreteFluidDynamics.divergence ω x

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DiscreteFluidDynamics.edgeInner` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → [Fintype V] → (V → V → ℝ) → (V → V → ℝ) → ℝ`
    - `SGC.Bridge.DiscreteFluidDynamics.gradientField` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → (V → ℝ) → V → V → ℝ`
    - `SGC.Bridge.DiscreteFluidDynamics.divergence` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → [Fintype V] → (V → V → ℝ) → V → ℝ`

### `SGC.Bridge.DiscreteFluidDynamics.fiberPartition_quot_map_eq_iff`

- statement (kernel-elaborated, sha256 `b9098f47e7d0a1b1`):

      ∀ (W : Type u_2) [Fintype W] [inst : DecidableEq W] (F : Type u_3) [Fintype F] [inst_2 : DecidableEq F] (p : W × F) (B : (SGC.Bridge.DiscreteFluidDynamics.fiberPartition W F).Quot), (SGC.Bridge.DiscreteFluidDynamics.fiberPartition W F).quot_map p = B ↔ p.1 = (Quotient.out B).1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.DiscreteFluidDynamics.fiberPartition` (def, SGC.Bridge.DiscreteFluidDynamics): `(W : Type u_2) → [inst : DecidableEq W] → (F : Type u_3) → [inst_1 : DecidableEq F] → SGC.Partition (W × F)`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`

### `SGC.Bridge.DiscreteFluidDynamics.killingDefect_eq_edgeInner_self`

- statement (kernel-elaborated, sha256 `623802db0e4a09cb`):

      ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (L : Matrix V V ℝ) (pi_dist : V → ℝ), SGC.Bridge.DiscreteFluidDynamics.KillingDefect L pi_dist = SGC.Bridge.DiscreteFluidDynamics.edgeInner (SGC.Thermodynamics.ProbabilityCurrent L pi_dist) (SGC.Thermodynamics.ProbabilityCurrent L pi_dist)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DiscreteFluidDynamics.KillingDefect` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → ℝ`
    - `SGC.Bridge.DiscreteFluidDynamics.edgeInner` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → [Fintype V] → (V → V → ℝ) → (V → V → ℝ) → ℝ`
    - `SGC.Thermodynamics.ProbabilityCurrent` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → V → V → ℝ`

### `SGC.Bridge.DiscreteFluidDynamics.killingDefect_eq_four_antisym`

- statement (kernel-elaborated, sha256 `236d2a72907a1dc5`):

      ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (L : Matrix V V ℝ) (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → SGC.Bridge.DiscreteFluidDynamics.KillingDefect L pi_dist = 4 * ∑ x, ∑ y, (pi_dist x * SGC.Thermodynamics.AntisymmetricPart L pi_dist x y) ^ 2

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DiscreteFluidDynamics.KillingDefect` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → ℝ`
    - `SGC.Thermodynamics.AntisymmetricPart` (def, SGC.Thermodynamics.FluxDecomposition): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → Matrix V V ℝ`
    - `SGC.Thermodynamics.ProbabilityCurrent` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → V → V → ℝ`

### `SGC.Bridge.DiscreteFluidDynamics.killingDefect_eq_zero_iff_reversible`

- statement (kernel-elaborated, sha256 `91a608729e4c9ab6`):

      ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (L : Matrix V V ℝ) (pi_dist : V → ℝ), SGC.Bridge.DiscreteFluidDynamics.KillingDefect L pi_dist = 0 ↔ SGC.Thermodynamics.DetailedBalance L pi_dist

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DiscreteFluidDynamics.KillingDefect` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → ℝ`
    - `SGC.Thermodynamics.DetailedBalance` (def, SGC.Thermodynamics.FluxDecomposition): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → Prop`
    - `SGC.Thermodynamics.ProbabilityCurrent` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → V → V → ℝ`

### `SGC.Bridge.DiscreteFluidDynamics.killingDefect_nonneg`

- statement (kernel-elaborated, sha256 `718716337f2e2288`):

      ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (L : Matrix V V ℝ) (pi_dist : V → ℝ), 0 ≤ SGC.Bridge.DiscreteFluidDynamics.KillingDefect L pi_dist

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DiscreteFluidDynamics.KillingDefect` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → ℝ`
    - `SGC.Thermodynamics.ProbabilityCurrent` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → V → V → ℝ`

### `SGC.Bridge.DiscreteFluidDynamics.killingDefect_pos_iff_positive_current_cycle`

- statement (kernel-elaborated, sha256 `e9c700487d43f340`):

      ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (L : Matrix V V ℝ) (pi_dist : V → ℝ), (∀ (x : V), ∑ y, L x y = 0) → SGC.Bridge.DiscreteFluidDynamics.IsStationary L pi_dist → (0 < SGC.Bridge.DiscreteFluidDynamics.KillingDefect L pi_dist ↔ ∃ len c, 0 < len ∧ c 0 = c len ∧ ∀ m < len, 0 < SGC.Thermodynamics.ProbabilityCurrent L pi_dist (c m) (c (m + 1)))

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DiscreteFluidDynamics.IsStationary` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → Prop`
    - `SGC.Bridge.DiscreteFluidDynamics.KillingDefect` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → ℝ`
    - `SGC.Thermodynamics.ProbabilityCurrent` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → V → V → ℝ`

### `SGC.Bridge.DiscreteFluidDynamics.ness_has_current_cycle`

- statement (kernel-elaborated, sha256 `2e3ea371cd7e244c`):

      ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (L : Matrix V V ℝ) (pi_dist : V → ℝ), (∀ (x : V), ∑ y, L x y = 0) → SGC.Bridge.DiscreteFluidDynamics.IsStationary L pi_dist → ¬SGC.Thermodynamics.DetailedBalance L pi_dist → ∃ len c, 0 < len ∧ c 0 = c len ∧ ∀ m < len, 0 < SGC.Thermodynamics.ProbabilityCurrent L pi_dist (c m) (c (m + 1))

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DiscreteFluidDynamics.IsStationary` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → Prop`
    - `SGC.Thermodynamics.DetailedBalance` (def, SGC.Thermodynamics.FluxDecomposition): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → Prop`
    - `SGC.Thermodynamics.ProbabilityCurrent` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → V → V → ℝ`

### `SGC.Bridge.DiscreteFluidDynamics.ness_quotient_forces_ness_fine`

- statement (kernel-elaborated, sha256 `4149e51a2b69e075`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ¬SGC.Thermodynamics.DetailedBalance (SGC.Thermodynamics.CoarseGenerator L P pi_dist) (SGC.pi_bar P pi_dist) → ¬SGC.Thermodynamics.DetailedBalance L pi_dist

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Thermodynamics.DetailedBalance` (def, SGC.Thermodynamics.FluxDecomposition): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → Prop`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.DiscreteFluidDynamics.orthogonal_gradients_iff_divergence_free`

- statement (kernel-elaborated, sha256 `057ebdea2332f11c`):

      ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (ω : V → V → ℝ), (∀ (x y : V), ω x y = -ω y x) → ((∀ (f : V → ℝ), SGC.Bridge.DiscreteFluidDynamics.edgeInner ω (SGC.Bridge.DiscreteFluidDynamics.gradientField f) = 0) ↔ ∀ (x : V), SGC.Bridge.DiscreteFluidDynamics.divergence ω x = 0)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DiscreteFluidDynamics.edgeInner` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → [Fintype V] → (V → V → ℝ) → (V → V → ℝ) → ℝ`
    - `SGC.Bridge.DiscreteFluidDynamics.gradientField` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → (V → ℝ) → V → V → ℝ`
    - `SGC.Bridge.DiscreteFluidDynamics.divergence` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → [Fintype V] → (V → V → ℝ) → V → ℝ`

### `SGC.Bridge.DiscreteFluidDynamics.pibar_mul_coarseGenerator`

- statement (kernel-elaborated, sha256 `9bedcd9822ca1c80`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (A B : P.Quot), SGC.pi_bar P pi_dist A * SGC.Thermodynamics.CoarseGenerator L P pi_dist A B = ∑ x, ∑ y, if P.quot_map x = A ∧ P.quot_map y = B then pi_dist x * L x y else 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.DiscreteFluidDynamics.reversible_iff_no_positive_current_cycle`

- statement (kernel-elaborated, sha256 `de434b69aa91e609`):

      ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (L : Matrix V V ℝ) (pi_dist : V → ℝ), (∀ (x : V), ∑ y, L x y = 0) → SGC.Bridge.DiscreteFluidDynamics.IsStationary L pi_dist → (SGC.Thermodynamics.DetailedBalance L pi_dist ↔ ¬∃ len c, 0 < len ∧ c 0 = c len ∧ ∀ m < len, 0 < SGC.Thermodynamics.ProbabilityCurrent L pi_dist (c m) (c (m + 1)))

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DiscreteFluidDynamics.IsStationary` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → Prop`
    - `SGC.Thermodynamics.DetailedBalance` (def, SGC.Thermodynamics.FluxDecomposition): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → Prop`
    - `SGC.Thermodynamics.ProbabilityCurrent` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → V → V → ℝ`

### `SGC.Bridge.DiscreteFluidDynamics.reversible_quotient_of_reversible`

- statement (kernel-elaborated, sha256 `282323a0a855e27c`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → SGC.Thermodynamics.DetailedBalance L pi_dist → SGC.Thermodynamics.DetailedBalance (SGC.Thermodynamics.CoarseGenerator L P pi_dist) (SGC.pi_bar P pi_dist)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Thermodynamics.DetailedBalance` (def, SGC.Thermodynamics.FluxDecomposition): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → Prop`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.DiscreteFluidDynamics.stationary_current_in_cycle_space`

- statement (kernel-elaborated, sha256 `fa2956a797a0ade9`):

      ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (L : Matrix V V ℝ) (pi_dist : V → ℝ), (∀ (x : V), ∑ y, L x y = 0) → SGC.Bridge.DiscreteFluidDynamics.IsStationary L pi_dist → SGC.Bridge.DiscreteFluidDynamics.InCycleSpace (SGC.Thermodynamics.ProbabilityCurrent L pi_dist)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DiscreteFluidDynamics.IsStationary` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → Prop`
    - `SGC.Bridge.DiscreteFluidDynamics.InCycleSpace` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → [Fintype V] → (V → V → ℝ) → Prop`
    - `SGC.Thermodynamics.ProbabilityCurrent` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → V → V → ℝ`
    - `SGC.Bridge.DiscreteFluidDynamics.divergence` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → [Fintype V] → (V → V → ℝ) → V → ℝ`

### `SGC.Bridge.DiscreteFluidDynamics.stationary_current_orthogonal_gradients`

- statement (kernel-elaborated, sha256 `5226adb0aed684d7`):

      ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (L : Matrix V V ℝ) (pi_dist : V → ℝ), (∀ (x : V), ∑ y, L x y = 0) → SGC.Bridge.DiscreteFluidDynamics.IsStationary L pi_dist → ∀ (f : V → ℝ), SGC.Bridge.DiscreteFluidDynamics.edgeInner (SGC.Thermodynamics.ProbabilityCurrent L pi_dist) (SGC.Bridge.DiscreteFluidDynamics.gradientField f) = 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DiscreteFluidDynamics.IsStationary` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → Prop`
    - `SGC.Bridge.DiscreteFluidDynamics.edgeInner` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → [Fintype V] → (V → V → ℝ) → (V → V → ℝ) → ℝ`
    - `SGC.Thermodynamics.ProbabilityCurrent` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → V → V → ℝ`
    - `SGC.Bridge.DiscreteFluidDynamics.gradientField` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → (V → ℝ) → V → V → ℝ`

### `SGC.Bridge.DiscreteFluidDynamics.stationary_iff_current_divergence_free`

- statement (kernel-elaborated, sha256 `1f20799d6d7f58c2`):

      ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (L : Matrix V V ℝ) (pi_dist : V → ℝ), (∀ (x : V), ∑ y, L x y = 0) → (SGC.Bridge.DiscreteFluidDynamics.IsStationary L pi_dist ↔ ∀ (x : V), SGC.Bridge.DiscreteFluidDynamics.divergence (SGC.Thermodynamics.ProbabilityCurrent L pi_dist) x = 0)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DiscreteFluidDynamics.IsStationary` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → Prop`
    - `SGC.Bridge.DiscreteFluidDynamics.divergence` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → [Fintype V] → (V → V → ℝ) → V → ℝ`
    - `SGC.Thermodynamics.ProbabilityCurrent` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → V → V → ℝ`

### `SGC.Bridge.DiscreteFluidDynamics.uniformLift_current_scales`

- statement (kernel-elaborated, sha256 `c3809ce597b2edcf`):

      ∀ (W : Type u_2) [Fintype W] [DecidableEq W] (F : Type u_3) [inst : Fintype F] [DecidableEq F] [Nonempty F] (M : Matrix W W ℝ) (piW : W → ℝ) (p q : W × F), SGC.Thermodynamics.ProbabilityCurrent (SGC.Bridge.DiscreteFluidDynamics.uniformLift W F M) (fun r => piW r.1 / ↑(Fintype.card F)) p q = SGC.Thermodynamics.ProbabilityCurrent M piW p.1 q.1 / ↑(Fintype.card F) ^ 2

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Thermodynamics.ProbabilityCurrent` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → V → V → ℝ`
    - `SGC.Bridge.DiscreteFluidDynamics.uniformLift` (def, SGC.Bridge.DiscreteFluidDynamics): `(W : Type u_2) → (F : Type u_3) → [Fintype F] → Matrix W W ℝ → Matrix (W × F) (W × F) ℝ`

### `SGC.Bridge.DiscreteFluidDynamics.uniformLift_quotient_realizes`

- statement (kernel-elaborated, sha256 `6d53098da10d354d`):

      ∀ (W : Type u_2) [inst : Fintype W] [inst_1 : DecidableEq W] (F : Type u_3) [inst_2 : Fintype F] [inst_3 : DecidableEq F] [Nonempty F] (M : Matrix W W ℝ) (w w' : W) (f f' : F), SGC.QuotientGeneratorSimple (SGC.Bridge.DiscreteFluidDynamics.uniformLift W F M) (SGC.Bridge.DiscreteFluidDynamics.fiberPartition W F) ((SGC.Bridge.DiscreteFluidDynamics.fiberPartition W F).quot_map (w, f)) ((SGC.Bridge.DiscreteFluidDynamics.fiberPartition W F).quot_map (w', f')) = M w w'

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.QuotientGeneratorSimple` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Bridge.DiscreteFluidDynamics.uniformLift` (def, SGC.Bridge.DiscreteFluidDynamics): `(W : Type u_2) → (F : Type u_3) → [Fintype F] → Matrix W W ℝ → Matrix (W × F) (W × F) ℝ`
    - `SGC.Bridge.DiscreteFluidDynamics.fiberPartition` (def, SGC.Bridge.DiscreteFluidDynamics): `(W : Type u_2) → [inst : DecidableEq W] → (F : Type u_3) → [inst_1 : DecidableEq F] → SGC.Partition (W × F)`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.row_sum_block` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → V → P.Quot → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.DiscreteFluidDynamics.uniformLift_row_sum_block`

- statement (kernel-elaborated, sha256 `860d8e83c23f3b47`):

      ∀ (W : Type u_2) [inst : Fintype W] [inst_1 : DecidableEq W] (F : Type u_3) [inst_2 : Fintype F] [inst_3 : DecidableEq F] [Nonempty F] (M : Matrix W W ℝ) (p : W × F) (B : (SGC.Bridge.DiscreteFluidDynamics.fiberPartition W F).Quot), SGC.row_sum_block (SGC.Bridge.DiscreteFluidDynamics.uniformLift W F M) (SGC.Bridge.DiscreteFluidDynamics.fiberPartition W F) p B = M p.1 (Quotient.out B).1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.DiscreteFluidDynamics.fiberPartition` (def, SGC.Bridge.DiscreteFluidDynamics): `(W : Type u_2) → [inst : DecidableEq W] → (F : Type u_3) → [inst_1 : DecidableEq F] → SGC.Partition (W × F)`
    - `SGC.row_sum_block` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → V → P.Quot → ℝ`
    - `SGC.Bridge.DiscreteFluidDynamics.uniformLift` (def, SGC.Bridge.DiscreteFluidDynamics): `(W : Type u_2) → (F : Type u_3) → [Fintype F] → Matrix W W ℝ → Matrix (W × F) (W × F) ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.DiscreteFluidDynamics.uniformLift_row_sum_zero`

- statement (kernel-elaborated, sha256 `cd60006b1a39f658`):

      ∀ (W : Type u_2) [inst : Fintype W] [DecidableEq W] (F : Type u_3) [inst_2 : Fintype F] [DecidableEq F] [Nonempty F] (M : Matrix W W ℝ), (∀ (w : W), ∑ w', M w w' = 0) → ∀ (p : W × F), ∑ q, SGC.Bridge.DiscreteFluidDynamics.uniformLift W F M p q = 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DiscreteFluidDynamics.uniformLift` (def, SGC.Bridge.DiscreteFluidDynamics): `(W : Type u_2) → (F : Type u_3) → [Fintype F] → Matrix W W ℝ → Matrix (W × F) (W × F) ℝ`

### `SGC.Bridge.DiscreteFluidDynamics.uniformLift_stationary`

- statement (kernel-elaborated, sha256 `ac0fda74a5510336`):

      ∀ (W : Type u_2) [inst : Fintype W] [DecidableEq W] (F : Type u_3) [inst_2 : Fintype F] [DecidableEq F] [Nonempty F] (M : Matrix W W ℝ) (piW : W → ℝ), SGC.Bridge.DiscreteFluidDynamics.IsStationary M piW → SGC.Bridge.DiscreteFluidDynamics.IsStationary (SGC.Bridge.DiscreteFluidDynamics.uniformLift W F M) fun r => piW r.1 / ↑(Fintype.card F)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DiscreteFluidDynamics.IsStationary` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → Prop`
    - `SGC.Bridge.DiscreteFluidDynamics.uniformLift` (def, SGC.Bridge.DiscreteFluidDynamics): `(W : Type u_2) → (F : Type u_3) → [Fintype F] → Matrix W W ℝ → Matrix (W × F) (W × F) ℝ`

### `SGC.Bridge.DiscreteFluidDynamics.uniformLift_stronglyLumpable`

- statement (kernel-elaborated, sha256 `238aa850fc4a4e06`):

      ∀ (W : Type u_2) [inst : Fintype W] [inst_1 : DecidableEq W] (F : Type u_3) [inst_2 : Fintype F] [inst_3 : DecidableEq F] [Nonempty F] (M : Matrix W W ℝ), SGC.IsStronglyLumpable (SGC.Bridge.DiscreteFluidDynamics.uniformLift W F M) (SGC.Bridge.DiscreteFluidDynamics.fiberPartition W F)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.IsStronglyLumpable` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → Prop`
    - `SGC.Bridge.DiscreteFluidDynamics.uniformLift` (def, SGC.Bridge.DiscreteFluidDynamics): `(W : Type u_2) → (F : Type u_3) → [Fintype F] → Matrix W W ℝ → Matrix (W × F) (W × F) ℝ`
    - `SGC.Bridge.DiscreteFluidDynamics.fiberPartition` (def, SGC.Bridge.DiscreteFluidDynamics): `(W : Type u_2) → [inst : DecidableEq W] → (F : Type u_3) → [inst_1 : DecidableEq F] → SGC.Partition (W × F)`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.DiscreteFluidDynamics.viscous_time_budget`

- statement (kernel-elaborated, sha256 `d3838ca7d929e935`):

      ∀ {ν : ℝ}, 0 < ν → ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(ν * t)) = 1 / ν

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

### `SGC.Bridge.HaltingCompiler.cd0_compiled_iff`

- statement (kernel-elaborated, sha256 `b67c9df409c07c85`):

      ∀ {Γ : Type u_2} [inst : Inhabited Γ] {Λ : Type u_3} [inst_1 : Inhabited Λ] (M : Turing.TM0.Machine Γ Λ) (w : List Γ), SGC.Bridge.CurvatureUndecidability.CD0 (SGC.Bridge.CurvatureUndecidability.haltW (SGC.Bridge.HaltingCompiler.haltMarker M w)) ↔ ¬(Turing.TM0.eval M w).Dom

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.CurvatureUndecidability.CD0` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → Prop`
    - `SGC.Bridge.CurvatureUndecidability.haltW` (def, SGC.Bridge.CurvatureUndecidability): `(ℤ → Bool) → SGC.Bridge.CurvatureUndecidability.Weights`
    - `SGC.Bridge.HaltingCompiler.haltMarker` (def, SGC.Bridge.HaltingCompiler): `{Γ : Type u_2} → [Inhabited Γ] → {Λ : Type u_3} → [inst : Inhabited Λ] → Turing.TM0.Machine Γ Λ → List Γ → ℤ → Bool`
    - `SGC.Bridge.CurvatureUndecidability.Weights` (def, SGC.Bridge.CurvatureUndecidability): `Type`
    - `SGC.Bridge.CurvatureUndecidability.gam2` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → (ℤ → ℝ) → ℤ → ℝ`
    - `SGC.Bridge.HaltingCompiler.haltMarkerNat` (def, SGC.Bridge.HaltingCompiler): `{Γ : Type u_2} → [Inhabited Γ] → {Λ : Type u_3} → [inst : Inhabited Λ] → Turing.TM0.Machine Γ Λ → List Γ → ℕ → Bool`
    - `SGC.Bridge.CurvatureUndecidability.lineGen` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → ℤ → ℝ`
    - `SGC.Bridge.CurvatureUndecidability.gam` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → (ℤ → ℝ) → ℤ → ℝ`
    - `SGC.Bridge.HaltingCompiler.multistep` (def, SGC.Bridge.HaltingCompiler): `{σ : Type u_1} → (σ → Option σ) → σ → ℕ → Option σ`
    - `SGC.Bridge.HaltingCompiler.multistep.match_1` (def, SGC.Bridge.HaltingCompiler): `(motive : ℕ → Sort u_1) → (x : ℕ) → (Unit → motive 0) → ((n : ℕ) → motive n.succ) → motive x`

### `SGC.Bridge.HaltingCompiler.cd0_spinRight`

- statement (kernel-elaborated, sha256 `5f64d3d1143059ec`):

      ∀ {Γ : Type u_2} [inst : Inhabited Γ] {Λ : Type u_3} [inst_1 : Inhabited Λ] (w : List Γ), SGC.Bridge.CurvatureUndecidability.CD0 (SGC.Bridge.CurvatureUndecidability.haltW (SGC.Bridge.HaltingCompiler.haltMarker SGC.Bridge.HaltingCompiler.spinRight w))

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.CurvatureUndecidability.CD0` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → Prop`
    - `SGC.Bridge.CurvatureUndecidability.haltW` (def, SGC.Bridge.CurvatureUndecidability): `(ℤ → Bool) → SGC.Bridge.CurvatureUndecidability.Weights`
    - `SGC.Bridge.HaltingCompiler.haltMarker` (def, SGC.Bridge.HaltingCompiler): `{Γ : Type u_2} → [Inhabited Γ] → {Λ : Type u_3} → [inst : Inhabited Λ] → Turing.TM0.Machine Γ Λ → List Γ → ℤ → Bool`
    - `SGC.Bridge.HaltingCompiler.spinRight` (def, SGC.Bridge.HaltingCompiler): `{Γ : Type u_2} → {Λ : Type u_3} → [inst : Inhabited Λ] → Turing.TM0.Machine Γ Λ`  [ignores x._@.SGC.Bridge.HaltingCompiler.1318617077._hygCtx._hyg.17]
    - `SGC.Bridge.CurvatureUndecidability.Weights` (def, SGC.Bridge.CurvatureUndecidability): `Type`
    - `SGC.Bridge.CurvatureUndecidability.gam2` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → (ℤ → ℝ) → ℤ → ℝ`
    - `SGC.Bridge.HaltingCompiler.haltMarkerNat` (def, SGC.Bridge.HaltingCompiler): `{Γ : Type u_2} → [Inhabited Γ] → {Λ : Type u_3} → [inst : Inhabited Λ] → Turing.TM0.Machine Γ Λ → List Γ → ℕ → Bool`
    - `SGC.Bridge.CurvatureUndecidability.lineGen` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → ℤ → ℝ`
    - `SGC.Bridge.CurvatureUndecidability.gam` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → (ℤ → ℝ) → ℤ → ℝ`
    - `SGC.Bridge.HaltingCompiler.multistep` (def, SGC.Bridge.HaltingCompiler): `{σ : Type u_1} → (σ → Option σ) → σ → ℕ → Option σ`
    - `SGC.Bridge.HaltingCompiler.multistep.match_1` (def, SGC.Bridge.HaltingCompiler): `(motive : ℕ → Sort u_1) → (x : ℕ) → (Unit → motive 0) → ((n : ℕ) → motive n.succ) → motive x`

### `SGC.Bridge.HaltingCompiler.evalDom_iff_multistep`

- statement (kernel-elaborated, sha256 `495765f50eb476be`):

      ∀ {σ : Type u_1} {f : σ → Option σ} {a : σ}, (Turing.eval f a).Dom ↔ ∃ n, SGC.Bridge.HaltingCompiler.multistep f a n = none

- axioms: Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.HaltingCompiler.multistep` (def, SGC.Bridge.HaltingCompiler): `{σ : Type u_1} → (σ → Option σ) → σ → ℕ → Option σ`
    - `SGC.Bridge.HaltingCompiler.multistep.match_1` (def, SGC.Bridge.HaltingCompiler): `(motive : ℕ → Sort u_1) → (x : ℕ) → (Unit → motive 0) → ((n : ℕ) → motive n.succ) → motive x`

### `SGC.Bridge.HaltingCompiler.haltMarkerNat_all_false_iff`

- statement (kernel-elaborated, sha256 `6539fa49d41b58eb`):

      ∀ {Γ : Type u_2} [inst : Inhabited Γ] {Λ : Type u_3} [inst_1 : Inhabited Λ] (M : Turing.TM0.Machine Γ Λ) (w : List Γ), (∀ (n : ℕ), SGC.Bridge.HaltingCompiler.haltMarkerNat M w n = false) ↔ ∀ (n : ℕ), (SGC.Bridge.HaltingCompiler.multistep (Turing.TM0.step M) (Turing.TM0.init w) n).isSome = true

- axioms: Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.HaltingCompiler.haltMarkerNat` (def, SGC.Bridge.HaltingCompiler): `{Γ : Type u_2} → [Inhabited Γ] → {Λ : Type u_3} → [inst : Inhabited Λ] → Turing.TM0.Machine Γ Λ → List Γ → ℕ → Bool`
    - `SGC.Bridge.HaltingCompiler.multistep` (def, SGC.Bridge.HaltingCompiler): `{σ : Type u_1} → (σ → Option σ) → σ → ℕ → Option σ`
    - `SGC.Bridge.HaltingCompiler.multistep.match_1` (def, SGC.Bridge.HaltingCompiler): `(motive : ℕ → Sort u_1) → (x : ℕ) → (Unit → motive 0) → ((n : ℕ) → motive n.succ) → motive x`

### `SGC.Bridge.HaltingCompiler.haltMarkerNat_at_most_once`

- statement (kernel-elaborated, sha256 `a8d13ce04ea11d98`):

      ∀ {Γ : Type u_2} [inst : Inhabited Γ] {Λ : Type u_3} [inst_1 : Inhabited Λ] (M : Turing.TM0.Machine Γ Λ) (w : List Γ) {m n : ℕ}, SGC.Bridge.HaltingCompiler.haltMarkerNat M w m = true → SGC.Bridge.HaltingCompiler.haltMarkerNat M w n = true → m = n

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.HaltingCompiler.haltMarkerNat` (def, SGC.Bridge.HaltingCompiler): `{Γ : Type u_2} → [Inhabited Γ] → {Λ : Type u_3} → [inst : Inhabited Λ] → Turing.TM0.Machine Γ Λ → List Γ → ℕ → Bool`
    - `SGC.Bridge.HaltingCompiler.multistep` (def, SGC.Bridge.HaltingCompiler): `{σ : Type u_1} → (σ → Option σ) → σ → ℕ → Option σ`
    - `SGC.Bridge.HaltingCompiler.multistep.match_1` (def, SGC.Bridge.HaltingCompiler): `(motive : ℕ → Sort u_1) → (x : ℕ) → (Unit → motive 0) → ((n : ℕ) → motive n.succ) → motive x`

### `SGC.Bridge.HaltingCompiler.haltMarkerNat_eq_false_of_lt`

- statement (kernel-elaborated, sha256 `a0f23d1935b5d063`):

      ∀ {Γ : Type u_2} [inst : Inhabited Γ] {Λ : Type u_3} [inst_1 : Inhabited Λ] {M : Turing.TM0.Machine Γ Λ} {w : List Γ} {m n : ℕ}, m < n → SGC.Bridge.HaltingCompiler.haltMarkerNat M w m = true → SGC.Bridge.HaltingCompiler.haltMarkerNat M w n = false

- axioms: Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.HaltingCompiler.haltMarkerNat` (def, SGC.Bridge.HaltingCompiler): `{Γ : Type u_2} → [Inhabited Γ] → {Λ : Type u_3} → [inst : Inhabited Λ] → Turing.TM0.Machine Γ Λ → List Γ → ℕ → Bool`
    - `SGC.Bridge.HaltingCompiler.multistep` (def, SGC.Bridge.HaltingCompiler): `{σ : Type u_1} → (σ → Option σ) → σ → ℕ → Option σ`
    - `SGC.Bridge.HaltingCompiler.multistep.match_1` (def, SGC.Bridge.HaltingCompiler): `(motive : ℕ → Sort u_1) → (x : ℕ) → (Unit → motive 0) → ((n : ℕ) → motive n.succ) → motive x`

### `SGC.Bridge.HaltingCompiler.haltMarker_all_false_iff`

- statement (kernel-elaborated, sha256 `61c3631d46b4fd30`):

      ∀ {Γ : Type u_2} [inst : Inhabited Γ] {Λ : Type u_3} [inst_1 : Inhabited Λ] (M : Turing.TM0.Machine Γ Λ) (w : List Γ), (∀ (i : ℤ), SGC.Bridge.HaltingCompiler.haltMarker M w i = false) ↔ ∀ (n : ℕ), SGC.Bridge.HaltingCompiler.haltMarkerNat M w n = false

- axioms: Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.HaltingCompiler.haltMarker` (def, SGC.Bridge.HaltingCompiler): `{Γ : Type u_2} → [Inhabited Γ] → {Λ : Type u_3} → [inst : Inhabited Λ] → Turing.TM0.Machine Γ Λ → List Γ → ℤ → Bool`
    - `SGC.Bridge.HaltingCompiler.haltMarkerNat` (def, SGC.Bridge.HaltingCompiler): `{Γ : Type u_2} → [Inhabited Γ] → {Λ : Type u_3} → [inst : Inhabited Λ] → Turing.TM0.Machine Γ Λ → List Γ → ℕ → Bool`
    - `SGC.Bridge.HaltingCompiler.multistep` (def, SGC.Bridge.HaltingCompiler): `{σ : Type u_1} → (σ → Option σ) → σ → ℕ → Option σ`
    - `SGC.Bridge.HaltingCompiler.multistep.match_1` (def, SGC.Bridge.HaltingCompiler): `(motive : ℕ → Sort u_1) → (x : ℕ) → (Unit → motive 0) → ((n : ℕ) → motive n.succ) → motive x`

### `SGC.Bridge.HaltingCompiler.haltMarker_at_most_once`

- statement (kernel-elaborated, sha256 `bfc5647a299ab40e`):

      ∀ {Γ : Type u_2} [inst : Inhabited Γ] {Λ : Type u_3} [inst_1 : Inhabited Λ] (M : Turing.TM0.Machine Γ Λ) (w : List Γ) (i j : ℤ), SGC.Bridge.HaltingCompiler.haltMarker M w i = true → SGC.Bridge.HaltingCompiler.haltMarker M w j = true → i = j

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.HaltingCompiler.haltMarker` (def, SGC.Bridge.HaltingCompiler): `{Γ : Type u_2} → [Inhabited Γ] → {Λ : Type u_3} → [inst : Inhabited Λ] → Turing.TM0.Machine Γ Λ → List Γ → ℤ → Bool`
    - `SGC.Bridge.HaltingCompiler.haltMarkerNat` (def, SGC.Bridge.HaltingCompiler): `{Γ : Type u_2} → [Inhabited Γ] → {Λ : Type u_3} → [inst : Inhabited Λ] → Turing.TM0.Machine Γ Λ → List Γ → ℕ → Bool`
    - `SGC.Bridge.HaltingCompiler.multistep` (def, SGC.Bridge.HaltingCompiler): `{σ : Type u_1} → (σ → Option σ) → σ → ℕ → Option σ`
    - `SGC.Bridge.HaltingCompiler.multistep.match_1` (def, SGC.Bridge.HaltingCompiler): `(motive : ℕ → Sort u_1) → (x : ℕ) → (Unit → motive 0) → ((n : ℕ) → motive n.succ) → motive x`

### `SGC.Bridge.HaltingCompiler.halted_of_multistep_none`

- statement (kernel-elaborated, sha256 `0f62b16e219b3de9`):

      ∀ {σ : Type u_1} {f : σ → Option σ} {a : σ} {n : ℕ}, SGC.Bridge.HaltingCompiler.multistep f a n = none → ∃ b, Turing.Reaches f a b ∧ f b = none

- axioms: propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.HaltingCompiler.multistep` (def, SGC.Bridge.HaltingCompiler): `{σ : Type u_1} → (σ → Option σ) → σ → ℕ → Option σ`
    - `SGC.Bridge.HaltingCompiler.multistep.match_1` (def, SGC.Bridge.HaltingCompiler): `(motive : ℕ → Sort u_1) → (x : ℕ) → (Unit → motive 0) → ((n : ℕ) → motive n.succ) → motive x`

### `SGC.Bridge.HaltingCompiler.multistep_none_mono`

- statement (kernel-elaborated, sha256 `506bfd7a7d3db903`):

      ∀ {σ : Type u_1} {f : σ → Option σ} {a : σ} {m n : ℕ}, m ≤ n → SGC.Bridge.HaltingCompiler.multistep f a m = none → SGC.Bridge.HaltingCompiler.multistep f a n = none

- axioms: none
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.HaltingCompiler.multistep` (def, SGC.Bridge.HaltingCompiler): `{σ : Type u_1} → (σ → Option σ) → σ → ℕ → Option σ`
    - `SGC.Bridge.HaltingCompiler.multistep.match_1` (def, SGC.Bridge.HaltingCompiler): `(motive : ℕ → Sort u_1) → (x : ℕ) → (Unit → motive 0) → ((n : ℕ) → motive n.succ) → motive x`

### `SGC.Bridge.HaltingCompiler.multistep_none_succ`

- statement (kernel-elaborated, sha256 `087e725c8748ddea`):

      ∀ {σ : Type u_1} {f : σ → Option σ} {a : σ} {n : ℕ}, SGC.Bridge.HaltingCompiler.multistep f a n = none → SGC.Bridge.HaltingCompiler.multistep f a (n + 1) = none

- axioms: none
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.HaltingCompiler.multistep` (def, SGC.Bridge.HaltingCompiler): `{σ : Type u_1} → (σ → Option σ) → σ → ℕ → Option σ`
    - `SGC.Bridge.HaltingCompiler.multistep.match_1` (def, SGC.Bridge.HaltingCompiler): `(motive : ℕ → Sort u_1) → (x : ℕ) → (Unit → motive 0) → ((n : ℕ) → motive n.succ) → motive x`

### `SGC.Bridge.HaltingCompiler.multistep_of_reaches`

- statement (kernel-elaborated, sha256 `67b09e27684bcb68`):

      ∀ {σ : Type u_1} {f : σ → Option σ} {a b : σ}, Turing.Reaches f a b → ∃ n, SGC.Bridge.HaltingCompiler.multistep f a n = some b

- axioms: none
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.HaltingCompiler.multistep` (def, SGC.Bridge.HaltingCompiler): `{σ : Type u_1} → (σ → Option σ) → σ → ℕ → Option σ`
    - `SGC.Bridge.HaltingCompiler.multistep.match_1` (def, SGC.Bridge.HaltingCompiler): `(motive : ℕ → Sort u_1) → (x : ℕ) → (Unit → motive 0) → ((n : ℕ) → motive n.succ) → motive x`

### `SGC.Bridge.HaltingCompiler.multistep_succ`

- statement (kernel-elaborated, sha256 `2c9f4d767f1a289e`):

      ∀ {σ : Type u_1} (f : σ → Option σ) (a : σ) (n : ℕ), SGC.Bridge.HaltingCompiler.multistep f a (n + 1) = (SGC.Bridge.HaltingCompiler.multistep f a n).bind f

- axioms: none
- unused hypotheses: none
- automation: trivial_by=rfl vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.HaltingCompiler.multistep` (def, SGC.Bridge.HaltingCompiler): `{σ : Type u_1} → (σ → Option σ) → σ → ℕ → Option σ`
    - `SGC.Bridge.HaltingCompiler.multistep.match_1` (def, SGC.Bridge.HaltingCompiler): `(motive : ℕ → Sort u_1) → (x : ℕ) → (Unit → motive 0) → ((n : ℕ) → motive n.succ) → motive x`

### `SGC.Bridge.HaltingCompiler.multistep_zero`

- statement (kernel-elaborated, sha256 `86aee356b18c5a11`):

      ∀ {σ : Type u_1} (f : σ → Option σ) (a : σ), SGC.Bridge.HaltingCompiler.multistep f a 0 = some a

- axioms: none
- unused hypotheses: none
- automation: trivial_by=rfl vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.HaltingCompiler.multistep` (def, SGC.Bridge.HaltingCompiler): `{σ : Type u_1} → (σ → Option σ) → σ → ℕ → Option σ`
    - `SGC.Bridge.HaltingCompiler.multistep.match_1` (def, SGC.Bridge.HaltingCompiler): `(motive : ℕ → Sort u_1) → (x : ℕ) → (Unit → motive 0) → ((n : ℕ) → motive n.succ) → motive x`

### `SGC.Bridge.HaltingCompiler.not_cd0_compiled_iff`

- statement (kernel-elaborated, sha256 `e11b25979852c9ef`):

      ∀ {Γ : Type u_2} [inst : Inhabited Γ] {Λ : Type u_3} [inst_1 : Inhabited Λ] (M : Turing.TM0.Machine Γ Λ) (w : List Γ), ¬SGC.Bridge.CurvatureUndecidability.CD0 (SGC.Bridge.CurvatureUndecidability.haltW (SGC.Bridge.HaltingCompiler.haltMarker M w)) ↔ (Turing.TM0.eval M w).Dom

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.CurvatureUndecidability.CD0` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → Prop`
    - `SGC.Bridge.CurvatureUndecidability.haltW` (def, SGC.Bridge.CurvatureUndecidability): `(ℤ → Bool) → SGC.Bridge.CurvatureUndecidability.Weights`
    - `SGC.Bridge.HaltingCompiler.haltMarker` (def, SGC.Bridge.HaltingCompiler): `{Γ : Type u_2} → [Inhabited Γ] → {Λ : Type u_3} → [inst : Inhabited Λ] → Turing.TM0.Machine Γ Λ → List Γ → ℤ → Bool`
    - `SGC.Bridge.CurvatureUndecidability.Weights` (def, SGC.Bridge.CurvatureUndecidability): `Type`
    - `SGC.Bridge.CurvatureUndecidability.gam2` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → (ℤ → ℝ) → ℤ → ℝ`
    - `SGC.Bridge.HaltingCompiler.haltMarkerNat` (def, SGC.Bridge.HaltingCompiler): `{Γ : Type u_2} → [Inhabited Γ] → {Λ : Type u_3} → [inst : Inhabited Λ] → Turing.TM0.Machine Γ Λ → List Γ → ℕ → Bool`
    - `SGC.Bridge.CurvatureUndecidability.lineGen` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → ℤ → ℝ`
    - `SGC.Bridge.CurvatureUndecidability.gam` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → (ℤ → ℝ) → ℤ → ℝ`
    - `SGC.Bridge.HaltingCompiler.multistep` (def, SGC.Bridge.HaltingCompiler): `{σ : Type u_1} → (σ → Option σ) → σ → ℕ → Option σ`
    - `SGC.Bridge.HaltingCompiler.multistep.match_1` (def, SGC.Bridge.HaltingCompiler): `(motive : ℕ → Sort u_1) → (x : ℕ) → (Unit → motive 0) → ((n : ℕ) → motive n.succ) → motive x`

### `SGC.Bridge.HaltingCompiler.not_cd0_compiled_of_halts`

- statement (kernel-elaborated, sha256 `f746ec24e8bfb3e1`):

      ∀ {Γ : Type u_2} [inst : Inhabited Γ] {Λ : Type u_3} [inst_1 : Inhabited Λ] (M : Turing.TM0.Machine Γ Λ) (w : List Γ), (Turing.TM0.eval M w).Dom → ¬SGC.Bridge.CurvatureUndecidability.CD0 (SGC.Bridge.CurvatureUndecidability.haltW (SGC.Bridge.HaltingCompiler.haltMarker M w))

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.CurvatureUndecidability.CD0` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → Prop`
    - `SGC.Bridge.CurvatureUndecidability.haltW` (def, SGC.Bridge.CurvatureUndecidability): `(ℤ → Bool) → SGC.Bridge.CurvatureUndecidability.Weights`
    - `SGC.Bridge.HaltingCompiler.haltMarker` (def, SGC.Bridge.HaltingCompiler): `{Γ : Type u_2} → [Inhabited Γ] → {Λ : Type u_3} → [inst : Inhabited Λ] → Turing.TM0.Machine Γ Λ → List Γ → ℤ → Bool`
    - `SGC.Bridge.CurvatureUndecidability.Weights` (def, SGC.Bridge.CurvatureUndecidability): `Type`
    - `SGC.Bridge.CurvatureUndecidability.gam2` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → (ℤ → ℝ) → ℤ → ℝ`
    - `SGC.Bridge.HaltingCompiler.haltMarkerNat` (def, SGC.Bridge.HaltingCompiler): `{Γ : Type u_2} → [Inhabited Γ] → {Λ : Type u_3} → [inst : Inhabited Λ] → Turing.TM0.Machine Γ Λ → List Γ → ℕ → Bool`
    - `SGC.Bridge.CurvatureUndecidability.lineGen` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → ℤ → ℝ`
    - `SGC.Bridge.CurvatureUndecidability.gam` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → (ℤ → ℝ) → ℤ → ℝ`
    - `SGC.Bridge.HaltingCompiler.multistep` (def, SGC.Bridge.HaltingCompiler): `{σ : Type u_1} → (σ → Option σ) → σ → ℕ → Option σ`
    - `SGC.Bridge.HaltingCompiler.multistep.match_1` (def, SGC.Bridge.HaltingCompiler): `(motive : ℕ → Sort u_1) → (x : ℕ) → (Unit → motive 0) → ((n : ℕ) → motive n.succ) → motive x`

### `SGC.Bridge.HaltingCompiler.not_cd0_haltNow`

- statement (kernel-elaborated, sha256 `a4cca0c93a97d367`):

      ∀ {Γ : Type u_2} [inst : Inhabited Γ] {Λ : Type u_3} [inst_1 : Inhabited Λ] (w : List Γ), ¬SGC.Bridge.CurvatureUndecidability.CD0 (SGC.Bridge.CurvatureUndecidability.haltW (SGC.Bridge.HaltingCompiler.haltMarker SGC.Bridge.HaltingCompiler.haltNow w))

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.CurvatureUndecidability.CD0` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → Prop`
    - `SGC.Bridge.CurvatureUndecidability.haltW` (def, SGC.Bridge.CurvatureUndecidability): `(ℤ → Bool) → SGC.Bridge.CurvatureUndecidability.Weights`
    - `SGC.Bridge.HaltingCompiler.haltMarker` (def, SGC.Bridge.HaltingCompiler): `{Γ : Type u_2} → [Inhabited Γ] → {Λ : Type u_3} → [inst : Inhabited Λ] → Turing.TM0.Machine Γ Λ → List Γ → ℤ → Bool`
    - `SGC.Bridge.HaltingCompiler.haltNow` (def, SGC.Bridge.HaltingCompiler): `{Γ : Type u_2} → {Λ : Type u_3} → [inst : Inhabited Λ] → Turing.TM0.Machine Γ Λ`  [ignores x._@.SGC.Bridge.HaltingCompiler.3717856741._hygCtx._hyg.16,x._@.SGC.Bridge.HaltingCompiler.3717856741._hygCtx._hyg.18]
    - `SGC.Bridge.CurvatureUndecidability.Weights` (def, SGC.Bridge.CurvatureUndecidability): `Type`
    - `SGC.Bridge.CurvatureUndecidability.gam2` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → (ℤ → ℝ) → ℤ → ℝ`
    - `SGC.Bridge.HaltingCompiler.haltMarkerNat` (def, SGC.Bridge.HaltingCompiler): `{Γ : Type u_2} → [Inhabited Γ] → {Λ : Type u_3} → [inst : Inhabited Λ] → Turing.TM0.Machine Γ Λ → List Γ → ℕ → Bool`
    - `SGC.Bridge.CurvatureUndecidability.lineGen` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → ℤ → ℝ`
    - `SGC.Bridge.CurvatureUndecidability.gam` (def, SGC.Bridge.CurvatureUndecidability): `SGC.Bridge.CurvatureUndecidability.Weights → (ℤ → ℝ) → (ℤ → ℝ) → ℤ → ℝ`
    - `SGC.Bridge.HaltingCompiler.multistep` (def, SGC.Bridge.HaltingCompiler): `{σ : Type u_1} → (σ → Option σ) → σ → ℕ → Option σ`
    - `SGC.Bridge.HaltingCompiler.multistep.match_1` (def, SGC.Bridge.HaltingCompiler): `(motive : ℕ → Sort u_1) → (x : ℕ) → (Unit → motive 0) → ((n : ℕ) → motive n.succ) → motive x`

### `SGC.Bridge.HaltingCompiler.reaches_of_multistep`

- statement (kernel-elaborated, sha256 `96725432429d40fa`):

      ∀ {σ : Type u_1} {f : σ → Option σ} {a : σ} {n : ℕ} {b : σ}, SGC.Bridge.HaltingCompiler.multistep f a n = some b → Turing.Reaches f a b

- axioms: propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.HaltingCompiler.multistep` (def, SGC.Bridge.HaltingCompiler): `{σ : Type u_1} → (σ → Option σ) → σ → ℕ → Option σ`
    - `SGC.Bridge.HaltingCompiler.multistep.match_1` (def, SGC.Bridge.HaltingCompiler): `(motive : ℕ → Sort u_1) → (x : ℕ) → (Unit → motive 0) → ((n : ℕ) → motive n.succ) → motive x`

### `SGC.Bridge.HaltingCompiler.step_haltNow`

- statement (kernel-elaborated, sha256 `aace8d6a4e0580b4`):

      ∀ {Γ : Type u_2} [inst : Inhabited Γ] {Λ : Type u_3} [inst_1 : Inhabited Λ] (c : Turing.TM0.Cfg Γ Λ), Turing.TM0.step SGC.Bridge.HaltingCompiler.haltNow c = none

- axioms: Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=rfl vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.HaltingCompiler.haltNow` (def, SGC.Bridge.HaltingCompiler): `{Γ : Type u_2} → {Λ : Type u_3} → [inst : Inhabited Λ] → Turing.TM0.Machine Γ Λ`  [ignores x._@.SGC.Bridge.HaltingCompiler.3717856741._hygCtx._hyg.16,x._@.SGC.Bridge.HaltingCompiler.3717856741._hygCtx._hyg.18]

### `SGC.Bridge.HaltingCompiler.step_spinRight`

- statement (kernel-elaborated, sha256 `f7f4732bab2b27ad`):

      ∀ {Γ : Type u_2} [inst : Inhabited Γ] {Λ : Type u_3} [inst_1 : Inhabited Λ] (c : Turing.TM0.Cfg Γ Λ), Turing.TM0.step SGC.Bridge.HaltingCompiler.spinRight c = some { q := c.q, Tape := Turing.Tape.move Turing.Dir.right c.Tape }

- axioms: Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=rfl vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.HaltingCompiler.spinRight` (def, SGC.Bridge.HaltingCompiler): `{Γ : Type u_2} → {Λ : Type u_3} → [inst : Inhabited Λ] → Turing.TM0.Machine Γ Λ`  [ignores x._@.SGC.Bridge.HaltingCompiler.1318617077._hygCtx._hyg.17]

### `SGC.Bridge.ValidityHorizon.current_driven_crystal`

- statement (kernel-elaborated, sha256 `1296508424551e82`):

      ∀ {V : Type u_1} [Fintype V] [DecidableEq V] (L D : Matrix V V ℝ) (pi_dist : V → ℝ), SGC.Thermodynamics.DetailedBalance L pi_dist → ∀ (x y : V), SGC.Thermodynamics.ProbabilityCurrent (L + D) pi_dist x y = SGC.Thermodynamics.ProbabilityCurrent D pi_dist x y

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Thermodynamics.DetailedBalance` (def, SGC.Thermodynamics.FluxDecomposition): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → Prop`
    - `SGC.Thermodynamics.ProbabilityCurrent` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → V → V → ℝ`

### `SGC.Bridge.ValidityHorizon.drive_injects_vorticity`

- statement (kernel-elaborated, sha256 `b0138b5b56e62b57`):

      ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (L D : Matrix V V ℝ) (pi_dist : V → ℝ), SGC.Thermodynamics.DetailedBalance L pi_dist → 0 < SGC.Bridge.DiscreteFluidDynamics.KillingDefect D pi_dist → ¬SGC.Bridge.PhaseClassifier.CrystalPhase (L + D) pi_dist

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Thermodynamics.DetailedBalance` (def, SGC.Thermodynamics.FluxDecomposition): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → Prop`
    - `SGC.Bridge.DiscreteFluidDynamics.KillingDefect` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → ℝ`
    - `SGC.Bridge.PhaseClassifier.CrystalPhase` (def, SGC.Bridge.PhaseClassifier): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → Prop`
    - `SGC.Thermodynamics.ProbabilityCurrent` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → V → V → ℝ`

### `SGC.Bridge.ValidityHorizon.exp_perturbation_bound`

- statement (kernel-elaborated, sha256 `a2f5cdbdc77e3ea6`):

      ∀ {𝔸 : Type u_2} [inst : NormedRing 𝔸] [NormOneClass 𝔸] [inst_2 : NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A B : 𝔸), ‖NormedSpace.exp ℝ (A + B) - NormedSpace.exp ℝ A‖ ≤ ‖B‖ * Real.exp (‖A‖ + ‖B‖)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

### `SGC.Bridge.ValidityHorizon.killingDefect_driven_crystal`

- statement (kernel-elaborated, sha256 `eefa6ea507eec52a`):

      ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (L D : Matrix V V ℝ) (pi_dist : V → ℝ), SGC.Thermodynamics.DetailedBalance L pi_dist → SGC.Bridge.DiscreteFluidDynamics.KillingDefect (L + D) pi_dist = SGC.Bridge.DiscreteFluidDynamics.KillingDefect D pi_dist

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Thermodynamics.DetailedBalance` (def, SGC.Thermodynamics.FluxDecomposition): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → Prop`
    - `SGC.Bridge.DiscreteFluidDynamics.KillingDefect` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → ℝ`
    - `SGC.Thermodynamics.ProbabilityCurrent` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → V → V → ℝ`

### `SGC.Bridge.ValidityHorizon.no_spontaneous_universality`

- statement (kernel-elaborated, sha256 `e08adb1e9b1cb4c0`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (γ : ℝ) (L : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → SGC.Bridge.PhaseClassifier.CrystalPhase L pi_dist → ¬SGC.Bridge.PhaseClassifier.UniversalPhase γ (SGC.Thermodynamics.CoarseGenerator L P pi_dist) (SGC.pi_bar P pi_dist)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.PhaseClassifier.CrystalPhase` (def, SGC.Bridge.PhaseClassifier): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → Prop`
    - `SGC.Bridge.PhaseClassifier.UniversalPhase` (def, SGC.Bridge.PhaseClassifier): `{V : Type u_1} → [Fintype V] → ℝ → Matrix V V ℝ → (V → ℝ) → Prop`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Bridge.DiscreteFluidDynamics.KillingDefect` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → ℝ`
    - `SGC.DirichletGap` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.ProbabilityCurrent` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → V → V → ℝ`
    - `SGC.RayleighSet` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → Set ℝ`
    - `SGC.inner_pi` (def, SGC.Axioms.Geometry): `{V : Type u_1} → [Fintype V] → (V → ℝ) → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.constant_vec_one` (def, SGC.Axioms.Geometry): `{V : Type u_1} → V → ℝ`  [ignores x._@.SGC.Axioms.Geometry.221746778._hygCtx._hyg.16]
    - `SGC.RayleighQuotient` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → (V → ℝ) → ℝ`
    - `SGC.DirichletForm` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → (V → ℝ) → ℝ`

### `SGC.Bridge.ValidityHorizon.probabilityCurrent_add`

- statement (kernel-elaborated, sha256 `9610458235a028ee`):

      ∀ {V : Type u_1} [Fintype V] [DecidableEq V] (L D : Matrix V V ℝ) (pi_dist : V → ℝ) (x y : V), SGC.Thermodynamics.ProbabilityCurrent (L + D) pi_dist x y = SGC.Thermodynamics.ProbabilityCurrent L pi_dist x y + SGC.Thermodynamics.ProbabilityCurrent D pi_dist x y

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Thermodynamics.ProbabilityCurrent` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → V → V → ℝ`

### `SGC.Bridge.ValidityHorizon.substrate_alone_is_crystal`

- statement (kernel-elaborated, sha256 `3806891c8a96df10`):

      ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (L : Matrix V V ℝ) (pi_dist : V → ℝ), SGC.Thermodynamics.DetailedBalance L pi_dist → SGC.Bridge.PhaseClassifier.CrystalPhase L pi_dist

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Thermodynamics.DetailedBalance` (def, SGC.Thermodynamics.FluxDecomposition): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → Prop`
    - `SGC.Bridge.PhaseClassifier.CrystalPhase` (def, SGC.Bridge.PhaseClassifier): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → Prop`
    - `SGC.Bridge.DiscreteFluidDynamics.KillingDefect` (def, SGC.Bridge.DiscreteFluidDynamics): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → ℝ`
    - `SGC.Thermodynamics.ProbabilityCurrent` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → V → V → ℝ`

### `SGC.Bridge.ValidityHorizon.validity_horizon`

- statement (kernel-elaborated, sha256 `36e2e864ba50a241`):

      ∀ {𝔸 : Type u_2} [inst : NormedRing 𝔸] [NormOneClass 𝔸] [inst_2 : NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A B : 𝔸) (t : ℝ), 0 ≤ t → ‖NormedSpace.exp ℝ (t • (A + B)) - NormedSpace.exp ℝ (t • A)‖ ≤ t * ‖B‖ * Real.exp (t * (‖A‖ + ‖B‖))

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

### `SGC.Bridge.ValidityHorizon.validity_horizon_inverse_leakage`

- statement (kernel-elaborated, sha256 `ed89c9b8f2b82f33`):

      ∀ {𝔸 : Type u_2} [inst : NormedRing 𝔸] [NormOneClass 𝔸] [inst_2 : NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A B : 𝔸), B ≠ 0 → ∀ (δ t : ℝ), 0 ≤ t → t * (‖A‖ + ‖B‖) ≤ 1 → t ≤ δ / (Real.exp 1 * ‖B‖) → ‖NormedSpace.exp ℝ (t • (A + B)) - NormedSpace.exp ℝ (t • A)‖ ≤ δ

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

### `SGC.Renormalization.CurvatureQuotient.Gamma2Sq_lift_eq`

- statement (kernel-elaborated, sha256 `e2ebe194b7032b9a`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L : Matrix V V ℝ) (P : SGC.Partition V), SGC.IsStronglyLumpable L P → ∀ (f : P.Quot → ℝ), SGC.Bridge.GeometricClosure.Gamma2Sq L (SGC.lift_fun P f) = SGC.lift_fun P (SGC.Bridge.GeometricClosure.Gamma2Sq (SGC.QuotientGeneratorSimple L P) f)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.IsStronglyLumpable` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → Prop`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.GeometricClosure.Gamma2Sq` (def, SGC.Bridge.GeometricClosure): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → V → ℝ`
    - `SGC.lift_fun` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → (P.Quot → ℝ) → V → ℝ`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.QuotientGeneratorSimple` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Bridge.GeometricClosure.Gamma2` (def, SGC.Bridge.GeometricClosure): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → (V → ℝ) → V → ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.row_sum_block` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → V → P.Quot → ℝ`
    - `SGC.Bridge.GeometricClosure.Gamma` (def, SGC.Bridge.GeometricClosure): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → (V → ℝ) → V → ℝ`

### `SGC.Renormalization.CurvatureQuotient.Gamma2_lift_eq`

- statement (kernel-elaborated, sha256 `205c696ac3ea510b`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L : Matrix V V ℝ) (P : SGC.Partition V), SGC.IsStronglyLumpable L P → ∀ (f g : P.Quot → ℝ), SGC.Bridge.GeometricClosure.Gamma2 L (SGC.lift_fun P f) (SGC.lift_fun P g) = SGC.lift_fun P (SGC.Bridge.GeometricClosure.Gamma2 (SGC.QuotientGeneratorSimple L P) f g)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.IsStronglyLumpable` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → Prop`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.GeometricClosure.Gamma2` (def, SGC.Bridge.GeometricClosure): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → (V → ℝ) → V → ℝ`
    - `SGC.lift_fun` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → (P.Quot → ℝ) → V → ℝ`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.QuotientGeneratorSimple` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Bridge.GeometricClosure.Gamma` (def, SGC.Bridge.GeometricClosure): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → (V → ℝ) → V → ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.row_sum_block` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → V → P.Quot → ℝ`

### `SGC.Renormalization.CurvatureQuotient.GammaSq_lift_eq`

- statement (kernel-elaborated, sha256 `2c6d467471de1e1f`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L : Matrix V V ℝ) (P : SGC.Partition V), SGC.IsStronglyLumpable L P → ∀ (f : P.Quot → ℝ), SGC.Bridge.GeometricClosure.GammaSq L (SGC.lift_fun P f) = SGC.lift_fun P (SGC.Bridge.GeometricClosure.GammaSq (SGC.QuotientGeneratorSimple L P) f)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.IsStronglyLumpable` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → Prop`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.GeometricClosure.GammaSq` (def, SGC.Bridge.GeometricClosure): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → V → ℝ`
    - `SGC.lift_fun` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → (P.Quot → ℝ) → V → ℝ`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.QuotientGeneratorSimple` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Bridge.GeometricClosure.Gamma` (def, SGC.Bridge.GeometricClosure): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → (V → ℝ) → V → ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.row_sum_block` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → V → P.Quot → ℝ`

### `SGC.Renormalization.CurvatureQuotient.Gamma_lift_eq`

- statement (kernel-elaborated, sha256 `cba3c5b8a862d730`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L : Matrix V V ℝ) (P : SGC.Partition V), SGC.IsStronglyLumpable L P → ∀ (f g : P.Quot → ℝ), SGC.Bridge.GeometricClosure.Gamma L (SGC.lift_fun P f) (SGC.lift_fun P g) = SGC.lift_fun P (SGC.Bridge.GeometricClosure.Gamma (SGC.QuotientGeneratorSimple L P) f g)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.IsStronglyLumpable` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → Prop`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.GeometricClosure.Gamma` (def, SGC.Bridge.GeometricClosure): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → (V → ℝ) → (V → ℝ) → V → ℝ`
    - `SGC.lift_fun` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → (P.Quot → ℝ) → V → ℝ`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.QuotientGeneratorSimple` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.row_sum_block` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → V → P.Quot → ℝ`

### `SGC.Renormalization.CurvatureQuotient.HasPositiveRicci_quotient`

- statement (kernel-elaborated, sha256 `6570a706c82c75fa`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L : Matrix V V ℝ) (P : SGC.Partition V), SGC.IsStronglyLumpable L P → SGC.Bridge.GeometricClosure.HasPositiveRicci L → SGC.Bridge.GeometricClosure.HasPositiveRicci (SGC.QuotientGeneratorSimple L P)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.IsStronglyLumpable` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → Prop`
    - `SGC.Bridge.GeometricClosure.HasPositiveRicci` (def, SGC.Bridge.GeometricClosure): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.QuotientGeneratorSimple` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Bridge.GeometricClosure.RicciCurvatureBound` (inductive, SGC.Bridge.GeometricClosure): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → ℝ → Prop`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.row_sum_block` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → V → P.Quot → ℝ`

### `SGC.Renormalization.CurvatureQuotient.RicciCurvatureBound_quotient`

- statement (kernel-elaborated, sha256 `a20a4ad022be861b`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L : Matrix V V ℝ) (P : SGC.Partition V), SGC.IsStronglyLumpable L P → ∀ (rho : ℝ), SGC.Bridge.GeometricClosure.RicciCurvatureBound L rho → SGC.Bridge.GeometricClosure.RicciCurvatureBound (SGC.QuotientGeneratorSimple L P) rho

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.IsStronglyLumpable` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → Prop`
    - `SGC.Bridge.GeometricClosure.RicciCurvatureBound` (inductive, SGC.Bridge.GeometricClosure): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → ℝ → Prop`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.QuotientGeneratorSimple` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.row_sum_block` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → V → P.Quot → ℝ`

### `SGC.Renormalization.CurvatureQuotient.StarExample.curvature_hiding`

- statement (kernel-elaborated, sha256 `9d0880fe65bc03ec`):

      SGC.IsStronglyLumpable SGC.Renormalization.CurvatureQuotient.StarExample.starGen SGC.Renormalization.CurvatureQuotient.StarExample.starP ∧ ¬SGC.Bridge.GeometricClosure.RicciCurvatureBound SGC.Renormalization.CurvatureQuotient.StarExample.starGen 0 ∧ SGC.Bridge.GeometricClosure.RicciCurvatureBound (SGC.QuotientGeneratorSimple SGC.Renormalization.CurvatureQuotient.StarExample.starGen SGC.Renormalization.CurvatureQuotient.StarExample.starP) (9 / 2)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.IsStronglyLumpable` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → Prop`
    - `SGC.Renormalization.CurvatureQuotient.StarExample.starGen` (def, SGC.Renormalization.CurvatureQuotient): `Matrix (Fin 7) (Fin 7) ℝ`
    - `SGC.Renormalization.CurvatureQuotient.StarExample.starP` (def, SGC.Renormalization.CurvatureQuotient): `SGC.Partition (Fin 7)`
    - `SGC.Bridge.GeometricClosure.RicciCurvatureBound` (inductive, SGC.Bridge.GeometricClosure): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → ℝ → Prop`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.QuotientGeneratorSimple` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Renormalization.CurvatureQuotient.StarExample.starSetoid` (def, SGC.Renormalization.CurvatureQuotient): `Setoid (Fin 7)`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.row_sum_block` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → V → P.Quot → ℝ`

### `SGC.Renormalization.CurvatureQuotient.StarExample.lift_two_valued`

- statement (kernel-elaborated, sha256 `f1f642622320e19f`):

      ∀ (f : SGC.Renormalization.CurvatureQuotient.StarExample.starP.Quot → ℝ), SGC.lift_fun SGC.Renormalization.CurvatureQuotient.StarExample.starP f = fun v => if v = 0 then f ⟦0⟧ else f ⟦1⟧

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Renormalization.CurvatureQuotient.StarExample.starP` (def, SGC.Renormalization.CurvatureQuotient): `SGC.Partition (Fin 7)`
    - `SGC.lift_fun` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → (P.Quot → ℝ) → V → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Renormalization.CurvatureQuotient.StarExample.starSetoid` (def, SGC.Renormalization.CurvatureQuotient): `Setoid (Fin 7)`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`

### `SGC.Renormalization.CurvatureQuotient.StarExample.starGen_lumpable`

- statement (kernel-elaborated, sha256 `229dfa9a0453b33c`):

      SGC.IsStronglyLumpable SGC.Renormalization.CurvatureQuotient.StarExample.starGen SGC.Renormalization.CurvatureQuotient.StarExample.starP

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.IsStronglyLumpable` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → Prop`
    - `SGC.Renormalization.CurvatureQuotient.StarExample.starGen` (def, SGC.Renormalization.CurvatureQuotient): `Matrix (Fin 7) (Fin 7) ℝ`
    - `SGC.Renormalization.CurvatureQuotient.StarExample.starP` (def, SGC.Renormalization.CurvatureQuotient): `SGC.Partition (Fin 7)`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Renormalization.CurvatureQuotient.StarExample.starSetoid` (def, SGC.Renormalization.CurvatureQuotient): `Setoid (Fin 7)`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Renormalization.CurvatureQuotient.StarExample.starGen_not_cd0`

- statement (kernel-elaborated, sha256 `fc383580279c66fb`):

      ¬SGC.Bridge.GeometricClosure.RicciCurvatureBound SGC.Renormalization.CurvatureQuotient.StarExample.starGen 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.GeometricClosure.RicciCurvatureBound` (inductive, SGC.Bridge.GeometricClosure): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → ℝ → Prop`
    - `SGC.Renormalization.CurvatureQuotient.StarExample.starGen` (def, SGC.Renormalization.CurvatureQuotient): `Matrix (Fin 7) (Fin 7) ℝ`

### `SGC.Renormalization.CurvatureQuotient.StarExample.starP_mk_eq_mk`

- statement (kernel-elaborated, sha256 `c8a61127fb1988bc`):

      ∀ {z w : Fin 7}, ⟦z⟧ = ⟦w⟧ ↔ (z = 0 ↔ w = 0)

- axioms: Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Renormalization.CurvatureQuotient.StarExample.starP` (def, SGC.Renormalization.CurvatureQuotient): `SGC.Partition (Fin 7)`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Renormalization.CurvatureQuotient.StarExample.starSetoid` (def, SGC.Renormalization.CurvatureQuotient): `Setoid (Fin 7)`

### `SGC.Renormalization.CurvatureQuotient.StarExample.starQuotient_cd`

- statement (kernel-elaborated, sha256 `4172c9a752dc1a9b`):

      SGC.Bridge.GeometricClosure.RicciCurvatureBound (SGC.QuotientGeneratorSimple SGC.Renormalization.CurvatureQuotient.StarExample.starGen SGC.Renormalization.CurvatureQuotient.StarExample.starP) (9 / 2)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.GeometricClosure.RicciCurvatureBound` (inductive, SGC.Bridge.GeometricClosure): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → ℝ → Prop`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Renormalization.CurvatureQuotient.StarExample.starP` (def, SGC.Renormalization.CurvatureQuotient): `SGC.Partition (Fin 7)`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.QuotientGeneratorSimple` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Renormalization.CurvatureQuotient.StarExample.starGen` (def, SGC.Renormalization.CurvatureQuotient): `Matrix (Fin 7) (Fin 7) ℝ`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Renormalization.CurvatureQuotient.StarExample.starSetoid` (def, SGC.Renormalization.CurvatureQuotient): `Setoid (Fin 7)`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.row_sum_block` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → V → P.Quot → ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`

### `SGC.Renormalization.CurvatureQuotient.instNonemptyQuot`

- statement (kernel-elaborated, sha256 `9fb778eb38c60c6c`):

      ∀ {V : Type u_1} [inst : DecidableEq V] [Nonempty V] (P : SGC.Partition V), Nonempty P.Quot

- axioms: Classical.choice [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`

### `SGC.Renormalization.CurvatureQuotient.lift_fun_mul`

- statement (kernel-elaborated, sha256 `193a582e79db5b63`):

      ∀ {V : Type u_1} [inst : DecidableEq V] (P : SGC.Partition V) (f g : P.Quot → ℝ), SGC.lift_fun P f * SGC.lift_fun P g = SGC.lift_fun P (f * g)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=rfl vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.lift_fun` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → (P.Quot → ℝ) → V → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`

### `SGC.Renormalization.CurvatureQuotient.not_RicciCurvatureBound_of_quotient`

- statement (kernel-elaborated, sha256 `21492a5f0b680330`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L : Matrix V V ℝ) (P : SGC.Partition V), SGC.IsStronglyLumpable L P → ∀ (rho : ℝ), ¬SGC.Bridge.GeometricClosure.RicciCurvatureBound (SGC.QuotientGeneratorSimple L P) rho → ¬SGC.Bridge.GeometricClosure.RicciCurvatureBound L rho

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.IsStronglyLumpable` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → Prop`
    - `SGC.Bridge.GeometricClosure.RicciCurvatureBound` (inductive, SGC.Bridge.GeometricClosure): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → ℝ → Prop`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.QuotientGeneratorSimple` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.row_sum_block` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → V → P.Quot → ℝ`

### `SGC.Renormalization.KernelHorizon.IsStochastic.nonneg`

- statement (kernel-elaborated, sha256 `0ed5043223a79e44`):

      ∀ {V : Type u_1} [inst : Fintype V] {T : Matrix V V ℝ}, SGC.Renormalization.KernelHorizon.IsStochastic T → ∀ (i j : V), 0 ≤ T i j

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`

### `SGC.Renormalization.KernelHorizon.IsStochastic.row_sum_one`

- statement (kernel-elaborated, sha256 `e4fccbffe801113f`):

      ∀ {V : Type u_1} [inst : Fintype V] {T : Matrix V V ℝ}, SGC.Renormalization.KernelHorizon.IsStochastic T → ∀ (i : V), ∑ j, T i j = 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`

### `SGC.Renormalization.KernelHorizon.coarseKernel_isStochastic`

- statement (kernel-elaborated, sha256 `506c921d99f2b523`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (T : Matrix V V ℝ) (P : SGC.Partition V) {pi_dist : V → ℝ}, (∀ (x : V), 0 < pi_dist x) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Renormalization.KernelHorizon.IsStochastic (SGC.Thermodynamics.CoarseGenerator T P pi_dist)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Renormalization.KernelHorizon.commutator_columns_centered`

- statement (kernel-elaborated, sha256 `a013bd15fa2ef0db`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (T : Matrix V V ℝ) (P : SGC.Partition V) {pi_dist : V → ℝ}, (∀ (x : V), 0 < pi_dist x) → ∀ (B : P.Quot), ∑ x, pi_dist x * SGC.Renormalization.MeasureReentry.closureCommutator T P pi_dist x B = 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Renormalization.KernelHorizon.eternal_closure_of_zero_commutator`

- statement (kernel-elaborated, sha256 `f4ab34161eb6c34c`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (T : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ), SGC.Renormalization.MeasureReentry.closureCommutator T P pi_dist = 0 → ∀ (n : ℕ), T ^ n * SGC.lift_matrix P = SGC.lift_matrix P * SGC.Thermodynamics.CoarseGenerator T P pi_dist ^ n

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Renormalization.KernelHorizon.kernel_closure_error_le`

- statement (kernel-elaborated, sha256 `3999a6a1e552dfc9`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (T : Matrix V V ℝ) (P : SGC.Partition V) {pi_dist : V → ℝ}, (∀ (x : V), 0 < pi_dist x) → SGC.Renormalization.KernelHorizon.IsStochastic T → ∀ (n : ℕ), ‖T ^ n * SGC.lift_matrix P - SGC.lift_matrix P * SGC.Thermodynamics.CoarseGenerator T P pi_dist ^ n‖ ≤ ↑n * ‖SGC.Renormalization.MeasureReentry.closureCommutator T P pi_dist‖

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Renormalization.KernelHorizon.kernel_closure_error_le_geom`

- statement (kernel-elaborated, sha256 `598e4c67009c36e2`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (T : Matrix V V ℝ) (P : SGC.Partition V) {pi_dist : V → ℝ}, (∀ (x : V), 0 < pi_dist x) → SGC.Renormalization.KernelHorizon.IsStochastic T → ∀ {α : ℝ}, (∀ (m : ℕ), ‖T ^ m * SGC.Renormalization.MeasureReentry.closureCommutator T P pi_dist‖ ≤ α ^ m * ‖SGC.Renormalization.MeasureReentry.closureCommutator T P pi_dist‖) → ∀ (n : ℕ), ‖T ^ n * SGC.lift_matrix P - SGC.lift_matrix P * SGC.Thermodynamics.CoarseGenerator T P pi_dist ^ n‖ ≤ (∑ k ∈ Finset.range n, α ^ k) * ‖SGC.Renormalization.MeasureReentry.closureCommutator T P pi_dist‖

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Renormalization.KernelHorizon.kernel_closure_error_le_uniform`

- statement (kernel-elaborated, sha256 `7387753346324fd1`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (T : Matrix V V ℝ) (P : SGC.Partition V) {pi_dist : V → ℝ}, (∀ (x : V), 0 < pi_dist x) → SGC.Renormalization.KernelHorizon.IsStochastic T → ∀ {α : ℝ}, 0 ≤ α → α < 1 → (∀ (m : ℕ), ‖T ^ m * SGC.Renormalization.MeasureReentry.closureCommutator T P pi_dist‖ ≤ α ^ m * ‖SGC.Renormalization.MeasureReentry.closureCommutator T P pi_dist‖) → ∀ (n : ℕ), ‖T ^ n * SGC.lift_matrix P - SGC.lift_matrix P * SGC.Thermodynamics.CoarseGenerator T P pi_dist ^ n‖ ≤ 1 / (1 - α) * ‖SGC.Renormalization.MeasureReentry.closureCommutator T P pi_dist‖

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Renormalization.KernelHorizon.lift_matrix_linfty_le_one`

- statement (kernel-elaborated, sha256 `ce0e2941ec33967f`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (P : SGC.Partition V), ‖SGC.lift_matrix P‖ ≤ 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`

### `SGC.Renormalization.KernelHorizon.linfty_opNorm_le_one_of_rows`

- statement (kernel-elaborated, sha256 `ba9cf46ab8c2b561`):

      ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (M : Matrix V V ℝ), (∀ (i j : V), 0 ≤ M i j) → (∀ (i : V), ∑ j, M i j ≤ 1) → ‖M‖ ≤ 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

### `SGC.Renormalization.KernelHorizon.linfty_opNorm_le_one_of_stochastic`

- statement (kernel-elaborated, sha256 `787c39adbd8b0307`):

      ∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] (T : Matrix V V ℝ), SGC.Renormalization.KernelHorizon.IsStochastic T → ‖T‖ ≤ 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`

### `SGC.Renormalization.KernelHorizon.stochastic_pow_norm_le_one`

- statement (kernel-elaborated, sha256 `4929e939abda1dd5`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (T : Matrix V V ℝ), SGC.Renormalization.KernelHorizon.IsStochastic T → ∀ (n : ℕ), ‖T ^ n‖ ≤ 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`

### `SGC.Renormalization.KernelHorizon.sum_row_sum_block`

- statement (kernel-elaborated, sha256 `a44b13ad5752f2e5`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (M : Matrix V V ℝ) (P : SGC.Partition V) (i : V), ∑ B, SGC.row_sum_block M P i B = ∑ j, M i j

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.row_sum_block` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → V → P.Quot → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`

### `SGC.Renormalization.KernelHorizon.within_tolerance_of_defect_small`

- statement (kernel-elaborated, sha256 `3b2bac3f8d586d7b`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (T : Matrix V V ℝ) (P : SGC.Partition V) {pi_dist : V → ℝ}, (∀ (x : V), 0 < pi_dist x) → SGC.Renormalization.KernelHorizon.IsStochastic T → ∀ {η : ℝ} (n : ℕ), ↑n * ‖SGC.Renormalization.MeasureReentry.closureCommutator T P pi_dist‖ ≤ η → ‖T ^ n * SGC.lift_matrix P - SGC.lift_matrix P * SGC.Thermodynamics.CoarseGenerator T P pi_dist ^ n‖ ≤ η

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

## Trust surface (project axioms)

| axiom | type | consumers | unconstrained numeric params |
|---|---|---|---|
| `SGC.Approximate.rowsum_to_opNorm_bound` | `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (ε : ℝ), 0 ≤ ε → SGC.IsRowSumApproxLumpable L P ε → SGC.opNorm_pi pi_dist hπ (SGC.Approximate.DefectOperator L P pi_dist hπ) ≤ ↑(Fintype.card V) * ε` | 1 | - |
| `SGC.Approximate.Weyl_inequality_pi` | `∀ {V : Type u_1} [inst : Fintype V] (A B : (V → ℝ) →ₗ[ℝ] V → ℝ) (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (k : ℕ), SGC.Approximate.IsSelfAdjoint_pi A pi_dist → SGC.Approximate.IsSelfAdjoint_pi B pi_dist → ∃ eigenvalue_k, |eigenvalue_k A - eigenvalue_k B| ≤ SGC.opNorm_pi pi_dist hπ (A - B)` | 1 | - |
| `SGC.Approximate.NCD_defect_split` | `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L L_fast L_slow : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (ε γ : ℝ), SGC.Approximate.IsNCD L L_fast L_slow P pi_dist hπ ε γ → SGC.Approximate.DefectOperator L P pi_dist hπ = ε • SGC.Approximate.DefectOperator L_slow P pi_dist hπ` | 1 | - |
| `SGC.Approximate.NCD_integral_bound` | `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L L_fast L_slow : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (ε γ : ℝ), SGC.Approximate.IsNCD L L_fast L_slow P pi_dist hπ ε γ → ∀ (t : ℝ), 0 ≤ t → ∀ (f₀ : V → ℝ), f₀ = (SGC.Approximate.CoarseProjector P pi_dist hπ) f₀ → ∀ (M : ℝ), 0 ≤ M → (∀ (s : ℝ), 0 ≤ s → s ≤ t → SGC.norm_pi pi_dist ((SGC.Approximate.DefectOperator L P pi_dist hπ) ((SGC.Approximate.CoarseProjector P pi_dist hπ) ((SGC.Approximate.HeatKernelMap L s) f₀))) ≤ M * SGC.norm_pi pi_dist f₀) → SGC.norm_pi pi_dist ((SGC.Approximate.HeatKernelMap L t) f₀ - (SGC.Approximate.CoarseProjector P pi_dist hπ) ((SGC.Approximate.HeatKernelMap L t) f₀)) ≤ M / γ * SGC.norm_pi pi_dist f₀` | 1 | - |
| `SGC.Thermodynamics.hidden_entropy_bound_from_trajectory` | `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ) (hπ : ∀ (x : V), 0 < pi_dist x) (ε : ℝ), 0 ≤ ε → SGC.Approximate.IsApproxLumpable L P pi_dist hπ ε → ∀ (C_traj : ℝ), 0 < C_traj → SGC.Thermodynamics.HiddenEntropyProduction L P pi_dist ≤ ↑(Fintype.card V) * C_traj ^ 2 * ε ^ 2` | 1 | - |
| `SGC.Thermodynamics.gaspard_path_space_identity` | `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ) (hπ : ∀ (x : V), 0 < pi_dist x), (∀ (x y : V), x ≠ y → 0 ≤ L x y) → (∀ (v : V), ∑ u, pi_dist u * L u v = 0) → ∀ γ > 0, γ ≤ SGC.DirichletGap L pi_dist → γ * SGC.opNorm_pi pi_dist hπ (SGC.Approximate.DefectOperator L P pi_dist hπ) ^ 2 ≤ SGC.Thermodynamics.HiddenEntropyProduction L P pi_dist` | 2 | - |
| `SGC.Thermodynamics.non_normality_from_flux` | `∀ {V : Type u_1} [inst : Fintype V] (L : Matrix V V ℝ) (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∃ C > 0, ∀ (x y : V), |SGC.Thermodynamics.NonNormalityCommutator L pi_dist x y| ≤ C * ∑ z, |SGC.Thermodynamics.AntisymmetricPart L pi_dist x z| * |SGC.Thermodynamics.AntisymmetricPart L pi_dist z y|` | 0 | - |
| `SGC.Axioms.GeometryGeneral.traceNorm_pi_neg` | `∀ {V : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] (pi_dist : V → ℝ) (A : (V → 𝕜) →ₗ[𝕜] V → 𝕜), SGC.Axioms.GeometryGeneral.traceNorm_pi pi_dist (-A) = SGC.Axioms.GeometryGeneral.traceNorm_pi pi_dist A` | 1 | - |
| `SGC.Axioms.GeometryGeneral.traceNorm_pi_nonneg` | `∀ {V : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] (pi_dist : V → ℝ) (A : (V → 𝕜) →ₗ[𝕜] V → 𝕜), 0 ≤ SGC.Axioms.GeometryGeneral.traceNorm_pi pi_dist A` | 1 | - |
| `SGC.Axioms.GeometryGeneral.fidelity_pi` | `{V : Type u_1} → {𝕜 : Type u_2} → [inst : RCLike 𝕜] → (V → ℝ) → ((V → 𝕜) →ₗ[𝕜] V → 𝕜) → ((V → 𝕜) →ₗ[𝕜] V → 𝕜) → ℝ` | 0 | - |
| `SGC.Axioms.GeometryGeneral.traceNorm_pi_add` | `∀ {V : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] (pi_dist : V → ℝ) (A B : (V → 𝕜) →ₗ[𝕜] V → 𝕜), SGC.Axioms.GeometryGeneral.traceNorm_pi pi_dist (A + B) ≤ SGC.Axioms.GeometryGeneral.traceNorm_pi pi_dist A + SGC.Axioms.GeometryGeneral.traceNorm_pi pi_dist B` | 1 | - |
| `SGC.Axioms.GeometryGeneral.traceNorm_pi` | `{V : Type u_1} → {𝕜 : Type u_2} → [inst : RCLike 𝕜] → (V → ℝ) → ((V → 𝕜) →ₗ[𝕜] V → 𝕜) → ℝ` | 8 | - |
| `SGC.Bridge.Quantum.partitionToCodeSubspace` | `{V : Type u_1} → [inst : Fintype V] → [inst_1 : DecidableEq V] → (pi_dist : V → ℝ) → SGC.Partition V → SGC.Bridge.Quantum.CodeSubspace V pi_dist` | 24 | - |
| `SGC.Bridge.Quantum.partitionToCodeSubspace_proj_eq` | `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (P : SGC.Partition V) (f : V → ℂ), (SGC.Bridge.Quantum.partitionToCodeSubspace pi_dist P).proj f = fun v => ↑((SGC.Approximate.CoarseProjector P pi_dist hπ) (fun w => RCLike.re (f w)) v) + Complex.I * ↑((SGC.Approximate.CoarseProjector P pi_dist hπ) (fun w => RCLike.im (f w)) v)` | 1 | - |
| `SGC.Bridge.Quantum.complexifyDefect_zero_iff` | `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (L : Matrix V V ℝ) (P : SGC.Partition V), SGC.Bridge.Quantum.complexifyDefect pi_dist hπ L P = 0 ↔ SGC.opNorm_pi pi_dist hπ (SGC.Approximate.DefectOperator L P pi_dist hπ) = 0` | 2 | - |
| `SGC.Bridge.Quantum.KL_coefficient_real` | `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (L : Matrix V V ℝ) (P : SGC.Partition V) (α : ℂ), SGC.Axioms.GeometryGeneral.IsSelfAdjoint_pi pi_dist (SGC.Axioms.GeometryGeneral.adjoint_pi pi_dist (SGC.Bridge.Quantum.complexifyDefect pi_dist hπ L P) ∘ₗ SGC.Bridge.Quantum.complexifyDefect pi_dist hπ L P) → (∀ (f : V → ℂ), (SGC.Bridge.Quantum.partitionToCodeSubspace pi_dist P).proj ((SGC.Axioms.GeometryGeneral.adjoint_pi pi_dist (SGC.Bridge.Quantum.complexifyDefect pi_dist hπ L P)) ((SGC.Bridge.Quantum.complexifyDefect pi_dist hπ L P) ((SGC.Bridge.Quantum.partitionToCodeSubspace pi_dist P).proj f))) = α • (SGC.Bridge.Quantum.partitionToCodeSubspace pi_dist P).proj f) → α.im = 0` | 1 | - |
| `SGC.Bridge.Coherence.HeatKernel_preserves_nonneg` | `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L : Matrix V V ℝ) (t : ℝ), 0 ≤ t → (∀ (v : V), L v v ≤ 0) → (∀ (v : V), ∑ w, L v w = 0) → (∀ (v w : V), v ≠ w → 0 ≤ L v w) → ∀ (p : V → ℝ), (∀ (v : V), 0 ≤ p v) → ∀ (v : V), 0 ≤ (SGC.Approximate.HeatKernelMap L t) p v` | 1 | - |
| `SGC.Bridge.Coherence.HeatKernel_preserves_sum` | `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L : Matrix V V ℝ) (t : ℝ), 0 ≤ t → (∀ (v : V), ∑ w, L v w = 0) → ∀ (p : V → ℝ), ∑ v, (SGC.Approximate.HeatKernelMap L t) p v = ∑ v, p v` | 1 | - |
| `SGC.Bridge.Coherence.partition_membership_sum_one` | `∀ {V : Type u_1} [inst : DecidableEq V] (P : SGC.Partition V) [inst_1 : Fintype P.Quot] (v : V), (∑ k, if ∃ q, (Fintype.equivFin P.Quot).symm k = q ∧ P.quot_map v = q then 1 else 0) = 1` | 1 | - |
| `SGC.Bridge.Coherence.norm_zero_forces_alpha_zero` | `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (L : Matrix V V ℝ) (P : SGC.Partition V) (α : ℝ), (∀ (ψ : V → ℂ), SGC.Axioms.GeometryGeneral.inner_pi pi_dist ((SGC.Bridge.Quantum.complexifyDefect pi_dist hπ L P) ψ) ((SGC.Bridge.Quantum.complexifyDefect pi_dist hπ L P) ψ) = 0) → α = 0` | 1 | - |
| `SGC.Bridge.Recovery.DataProcessingInequality` | `∀ {V : Type u_1} [inst : Fintype V] (M : Matrix V V ℝ) (p q : V → ℝ), (∀ (y : V), ∑ x, M y x = 1) → (∀ (y x : V), 0 ≤ M y x) → (∀ (x : V), 0 ≤ p x) → (∀ (x : V), 0 ≤ q x) → SGC.Bridge.Recovery.RelativeEntropy (SGC.Bridge.Recovery.applyChannel M p) (SGC.Bridge.Recovery.applyChannel M q) ≤ SGC.Bridge.Recovery.RelativeEntropy p q` | 3 | - |
| `SGC.Bridge.Recovery.PetzRecoveryTheorem` | `∀ {V : Type u_1} [inst : Fintype V] (M : Matrix V V ℝ) (p q : V → ℝ), (∀ (y : V), ∑ x, M y x = 1) → (∀ (y x : V), 0 ≤ M y x) → (∀ (x : V), 0 < p x) → (∀ (x : V), 0 < q x) → (SGC.Bridge.Recovery.RelativeEntropy (SGC.Bridge.Recovery.applyChannel M p) (SGC.Bridge.Recovery.applyChannel M q) = SGC.Bridge.Recovery.RelativeEntropy p q ↔ ∃ R, SGC.Bridge.Recovery.applyChannel R (SGC.Bridge.Recovery.applyChannel M p) = p)` | 2 | - |
| `SGC.Bridge.Recovery.LandauerPrinciple` | `∀ {V : Type u_1} [inst : Fintype V] (pi_dist : V → ℝ) (kT : ℝ), 0 < kT → ∀ (p_initial p_final : V → ℝ), (∀ (x : V), 0 < p_initial x) → (∀ (x : V), 0 < p_final x) → SGC.Bridge.Recovery.LandauerCost pi_dist kT p_initial p_final ≥ 0` | 1 | - |
| `SGC.Geometry.KAT_existence` | `∀ {V : Type u_1} [inst : DecidableEq V] [inst_1 : Fintype V] (K : SGC.Geometry.SimplicialComplex V), True → K.dim = 2 → ∃ _u, True` | 1 | - |
| `SGC.Geometry.yamabe_flow_convergence` | `∀ {V : Type u_1} [inst : DecidableEq V] [inst_1 : Fintype V] (K : SGC.Geometry.SimplicialComplex V) (g : SGC.Geometry.PLMetric V K), True → SGC.Geometry.DiscreteYamabeProblem K g` | 0 | - |
| `SGC.Geometry.totalSolidAngle` | `ℕ → ℝ` | 1 | - |
| `SGC.Geometry.discrete_gauss_bonnet` | `∀ {V : Type u_1} [inst : DecidableEq V] [Fintype V] (K : SGC.Geometry.SimplicialComplex V) (g : SGC.Geometry.PLMetric V K) (euler_char : ℤ) (vertices : Finset V) (curvature : V → ℝ), ∑ v ∈ vertices, curvature v = 2 * Real.pi * ↑euler_char` | 0 | - |
| `SGC.Bridge.energy_entropy_rate_correspondence` | `∀ {V : Type u_1} [inst : DecidableEq V] (curvature u : V → ℝ), (∀ (v : V), 0 < u v) → ∀ (L : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∃ C > 0, True` | 0 | - |
| `SGC.Bridge.curvature_defect_correspondence` | `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (K : SGC.Geometry.SimplicialComplex V) (g : SGC.Geometry.PLMetric V K) (L : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (curvature : V → ℝ), ∃ embedding, ∃ C > 0, ∀ (v : V), |curvature v - SGC.Geometry.averageCurvature curvature| ≤ C * |embedding v - ∑ w, pi_dist w * embedding w|` | 0 | - |
| `SGC.Bridge.error_gradient_is_curvature` | `∀ {V : Type u_1} [inst : DecidableEq V] (L : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∀ (u : V → ℝ), (∀ (v : V), 0 < u v) → ∃ C, C > 0` | 0 | - |
| `SGC.Bridge.yamabe_bounds_hidden_entropy` | `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (K : SGC.Geometry.SimplicialComplex V) (g : SGC.Geometry.PLMetric V K) (u : SGC.Geometry.ConformalFactor V) (L : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → Matrix.vecMul pi_dist L = 0 → ∀ (curvature : V → ℝ), ∃ c > 0, c * SGC.Thermodynamics.HiddenEntropyProduction L P pi_dist ≤ SGC.Bridge.AssemblyIndex curvature u.factor` | 0 | - |
| `SGC.Bridge.OllivierRicciCurvature` | `{V : Type u_1} → Matrix V V ℝ → V → V → ℝ` | 1 | - |
| `SGC.Bridge.GeometricClosure.Ricci_tensor_min` | `∀ {V : Type u_1} [inst : Fintype V] {W : Type u_2} [inst_1 : Fintype W] (L_A : Matrix V V ℝ) (L_B : Matrix W W ℝ) (rho_A rho_B : ℝ), SGC.Bridge.GeometricClosure.RicciCurvatureBound L_A rho_A → SGC.Bridge.GeometricClosure.RicciCurvatureBound L_B rho_B → SGC.Bridge.GeometricClosure.RicciCurvatureBoundProduct L_A L_B (min rho_A rho_B)` | 2 | - |
| `SGC.Bridge.GeometricClosure.EnergyDerivative` | `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → (V → ℝ) → ℝ → ℝ` | 8 | - |
| `SGC.Bridge.GeometricClosure.exponential_decay_from_convexity` | `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L : Matrix V V ℝ), ∀ rho > 0, ∀ (p₀ pi_stat : V → ℝ), (∀ (s : ℝ), HasDerivAt (fun τ => SGC.Bridge.GeometricClosure.EnergyFunctional L p₀ pi_stat τ) (SGC.Bridge.GeometricClosure.EnergyDerivative L p₀ pi_stat s) s) → (∀ (s : ℝ), 0 ≤ s → SGC.Bridge.GeometricClosure.EnergyDerivative L p₀ pi_stat s ≤ -(2 * rho) * SGC.Bridge.GeometricClosure.EnergyFunctional L p₀ pi_stat s) → ∀ t ≥ 0, SGC.Bridge.GeometricClosure.EnergyFunctional L p₀ pi_stat t ≤ SGC.Bridge.GeometricClosure.EnergyFunctional L p₀ pi_stat 0 * Real.exp (-2 * rho * t)` | 1 | - |
| `SGC.Bridge.GeometricClosure.Poincare_from_integrated_curvature` | `∀ {V : Type u_1} [inst : Fintype V] (L : Matrix V V ℝ) (pi_dist : V → ℝ), ∀ rho > 0, Matrix.vecMul pi_dist L = 0 → (∀ (v : V), 0 < pi_dist v) → (∀ (f : V → ℝ), SGC.Bridge.GeometricClosure.Gamma2_pi L pi_dist f ≥ rho * SGC.Bridge.GeometricClosure.Gamma_pi L pi_dist f) → ∀ (f : V → ℝ), SGC.DirichletForm L pi_dist f ≥ rho * SGC.Bridge.GeometricClosure.VarianceEnergy pi_dist f` | 1 | - |
| `SGC.Bridge.GeometricClosure.EnergySecondDerivative` | `{V : Type u_1} → Matrix V V ℝ → (V → ℝ) → (V → ℝ) → ℝ → ℝ` | 7 | - |
| `SGC.Bridge.GeometricClosure.BakryEmery_implies_stability` | `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L : Matrix V V ℝ) (rho : ℝ), SGC.Bridge.GeometricClosure.RicciCurvatureBound L rho → (∀ (i j : V), i ≠ j → 0 ≤ L i j) → (∀ (i : V), ∑ j, L i j = 0) → (∀ (p₀ pi_stat : V → ℝ) (s : ℝ), HasDerivAt (fun τ => SGC.Bridge.GeometricClosure.EnergyFunctional L p₀ pi_stat τ) (SGC.Bridge.GeometricClosure.EnergyDerivative L p₀ pi_stat s) s) → (∀ (p₀ pi_stat : V → ℝ) (s : ℝ), HasDerivAt (fun τ => SGC.Bridge.GeometricClosure.EnergyDerivative L p₀ pi_stat τ) (SGC.Bridge.GeometricClosure.EnergySecondDerivative L p₀ pi_stat s) s) → SGC.Bridge.GeometricClosure.IntrinsicStabilityInequality L rho` | 1 | - |

## Human steps remaining

1. Read each printed statement and decide whether it says what the prose claims; record the decision in a claim map.
2. Read every definition in the cone lists above.
3. For any project axiom: name the model in which it holds and check joint consistency and degenerate parameters.
4. If kernel replay did not run, run `lean4checker --fresh` on the modules; for kernel-level exploits run `comparator` with an external checker.

## What this receipt does not certify

- This receipt records evidence and witnesses. It does not certify importance, novelty, or that any formal statement matches an informal claim; claim_map is UNATTESTED unless a named human signed it.
- Automation probes (triviality, vacuity, emptiness) are budgeted searches: absence of a witness is not evidence of non-triviality or consistency.
- The definition cone is a reading list, not a verdict; only a human can judge whether a definition captures the intended concept.
- Kernel implementation bugs and environment hacking are only excluded by external checkers (lean4checker --fresh, comparator); this tool records whether they ran.
- Lean's kernel, elaborator, and dependencies are trusted; their axioms are the baseline, not audited here.
- Only the listed modules/targets are audited; nothing is implied about other declarations.
