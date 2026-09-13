# lean-triage report: REVIEW

- receipt: `lean-triage-5b6d6ef227ba-20260913T194727Z`  (hash_self `6b597ab9b5a9fc5b...`)
- tool: lean-triage 0.2.1 (source `25bc5fa54832`, probe `2010c645afc8`)
- repo: https://github.com/JasonShroyer/sgc-lean.git
- commit: 16c991218fedc5015e62956c69e3bc3474596b23  dirty=True
- toolchain: leanprover/lean4:v4.25.2
- source tree sha256: `5b6d6ef227baf69b4bd478bfd385ecf20eb751ece172f3af65a4eff3d9a136fc`
- modules: SGC.Bridge.TerminalDecoding

## Verdict

**REVIEW** - 0 fail, 16 warn, 229 info.

NO_BLOCKING_EVIDENCE = no configured blocking evidence found by the checks that ran. REVIEW = warn-level items need a human. FINDINGS = evidence the claim is not established as stated. None of these means 'correct' or 'important'.

## Execution context

- execution_mode: trusted_local  network_policy: unknown  credential_mounts: unknown (self-declared by operator)
- checks that did NOT run: lake build (skipped by request), kernel replay from fresh environment (lean4checker not available or build unverified), comparator / external checker (never run automatically), human claim-map attestation (none supplied)

## Findings

basis: kernel = read from the kernel/elaborated environment; witness = a reproducible object (closing tactic) was produced; heuristic = pattern that needs a human; attestation = human-signed or unsigned claim; process = provenance/toolchain/process fact.

| sev | basis | id | code | theorem | detail |
|---|---|---|---|---|---|
| warn | heuristic | F10 | CITED_DECLARATION_MISSING | SGC.DiscreteFluidDynamics | cited in reports/CELEGANS_FLOQUET_TSALLIS_BRIDGE.md but no such declaration exists in the loaded environment or in project sources |
| warn | heuristic | F10 | CITED_DECLARATION_MISSING | SGC.Measurement.Interfaces.TightnessAudit | cited in demos/README.md but no such declaration exists in the loaded environment or in project sources |
| warn | heuristic | F10 | CITED_DECLARATION_MISSING | SGC.Measurement.Interfaces.tightness_ratio_nonneg | cited in demos/README.md but no such declaration exists in the loaded environment or in project sources |
| warn | heuristic | F10 | CITED_DECLARATION_MISSING | SGC.Measurement.Wavelets | cited in demos/README.md but no such declaration exists in the loaded environment or in project sources |
| warn | heuristic | F10 | CITED_DECLARATION_MISSING | SGC.Measurement.Wavelets.DiffusionWavelet | cited in demos/README.md but no such declaration exists in the loaded environment or in project sources |
| warn | heuristic | F10 | CITED_DECLARATION_MISSING | SGC.Stochastic.KramersEscape | cited in reports/BROWNIAN_MOTION_LEAN_EXPLORATION.md but no such declaration exists in the loaded environment or in project sources |
| warn | heuristic | F08 | DEFINITION_REVIEW_CANDIDATE_IGNORED_ARGS | - | definition SGC.Bridge.TerminalDecoding.Regression.reset ignores explicit argument(s) x._@.SGC.Bridge.TerminalDecoding.738208583._hygCtx._hyg.28, x._@.SGC.Bridge.TerminalDecoding.738208583._hygCtx._hyg.30 |
| warn | process | F12 | DIRTY_TREE | - | working tree has uncommitted changes; audited bytes may differ from the recorded commit |
| warn | heuristic | F10 | NARRATIVE_CLAIM_NEEDS_HUMAN_MAP | - | strong-claim vocabulary 'Millennium' appears 2x (THEORY.md:175, docs/bkm-formalization-design.md:46); a human must map the formal statements to it |
| warn | heuristic | F10 | NARRATIVE_CLAIM_NEEDS_HUMAN_MAP | - | strong-claim vocabulary 'Navier-Stokes' appears 5x (PRIORITY_CLAIMS.md:93, PRIORITY_CLAIMS.md:95, PRIORITY_CLAIMS.md:99, ...); a human must map the formal statements to it |
| warn | heuristic | F10 | NARRATIVE_CLAIM_NEEDS_HUMAN_MAP | - | strong-claim vocabulary 'Riemann' appears 26x (CHANGELOG.md:164, RESEARCH_JOURNAL.md:90, VERIFIED_CORE_MANIFEST.md:381, ...); a human must map the formal statements to it |
| warn | heuristic | F10 | NARRATIVE_CLAIM_NEEDS_HUMAN_MAP | - | strong-claim vocabulary 'fully verified' appears 5x (README.md:37, VERIFIED_CORE_MANIFEST.md:52, VERIFIED_CORE_MANIFEST.md:117, ...); a human must map the formal statements to it |
| warn | heuristic | F10 | NARRATIVE_CLAIM_NEEDS_HUMAN_MAP | - | strong-claim vocabulary 'settles' appears 3x (decisions/0016-curvature-descends-along-lumpable-quotients.md:50, reports/PHASE_4A_CANONICAL_WAVELET_FISHER_RAO_INTEGRATION.md:249, theory_context/SGC UPAT Methods Deep Dive.md:211); a human must map the formal statements to it |
| warn | heuristic | F10 | NARRATIVE_CLAIM_NEEDS_HUMAN_MAP | - | strong-claim vocabulary 'unconditional' appears 10x (RESEARCH_JOURNAL.md:285, RESEARCH_JOURNAL.md:567, RESEARCH_JOURNAL.md:816, ...); a human must map the formal statements to it |
| warn | process | F13 | TOOLCHAIN_ADVISORY | - | toolchain leanprover/lean4:v4.25.2 is below 4.32.2: Kernel soundness bug (nested inductive types with phantom parameters) allowed an axiom-free proof of False; #print axioms reported nothing. Fixed in Lean 4.32.2. |
| warn | process | F13 | TOOLCHAIN_ADVISORY | - | toolchain leanprover/lean4:v4.25.2 is below 4.32.2: Runtime reference-count overflow path that could corrupt memory and yield False (reported in the 2026 soundness-bug hunt). |
| info | witness | F07 | AUTOMATION_CLOSES_TARGET_UNDER_POLICY | SGC.Bridge.TerminalDecoding.Regression.discrete_quot_eq | the configured automation policy closes the statement (`simp`); legitimate, but weigh against any strong narrative |
| info | witness | F07 | AUTOMATION_CLOSES_TARGET_UNDER_POLICY | SGC.Bridge.TerminalDecoding.terminalBudget_zero | the configured automation policy closes the statement (`simp`); legitimate, but weigh against any strong narrative |
| info | witness | F07 | AUTOMATION_CLOSES_TARGET_UNDER_POLICY | SGC.Bridge.TerminalDecoding.terminalError_zero | the configured automation policy closes the statement (`simp`); legitimate, but weigh against any strong narrative |
| info | witness | F07 | AUTOMATION_CLOSES_TARGET_UNDER_POLICY | SGC.Bridge.TerminalDecoding.tv_self | the configured automation policy closes the statement (`simp`); legitimate, but weigh against any strong narrative |
| info | kernel | F16 | AXIOM_UNREFERENCED | - | axiom SGC.Approximate.NCD_defect_split has no consumer in the loaded project modules; trust-surface bloat |
| info | kernel | F16 | AXIOM_UNREFERENCED | - | axiom SGC.Approximate.NCD_integral_bound has no consumer in the loaded project modules; trust-surface bloat |
| info | kernel | F16 | AXIOM_UNREFERENCED | - | axiom SGC.Approximate.Weyl_inequality_pi has no consumer in the loaded project modules; trust-surface bloat |
| info | process | F12 | BUILD_SKIPPED | - | build skipped by request; the probe ran against existing .olean files whose provenance is not established here |
| info | heuristic | F10 | CITED_DECLARATION_UNLOADED | SGC.Bridge.CelegansFloquetTsallis.celegans_anomalous_diffusion_value | cited in reports/CELEGANS_FLOQUET_TSALLIS_BRIDGE.md; a declaration with this final name exists in project sources but not in the audited modules |
| info | heuristic | F10 | CITED_DECLARATION_UNLOADED | SGC.Bridge.CelegansFloquetTsallis.celegans_scaling_lt_UGM | cited in reports/CELEGANS_FLOQUET_TSALLIS_BRIDGE.md; a declaration with this final name exists in project sources but not in the audited modules |
| info | heuristic | F10 | CITED_DECLARATION_UNLOADED | SGC.Bridge.CelegansFloquetTsallis.predicted_alpha_eq_r_half | cited in reports/CELEGANS_FLOQUET_TSALLIS_BRIDGE.md; a declaration with this final name exists in project sources but not in the audited modules |
| info | heuristic | F10 | CITED_DECLARATION_UNLOADED | SGC.Bridge.CurvatureUndecidability.cd0_haltW_iff | cited in docs/haltmarker-design.md; a declaration with this final name exists in project sources but not in the audited modules |
| info | heuristic | F10 | CITED_DECLARATION_UNLOADED | SGC.ComplexityRelativity.complexity_is_relational | cited in reports/SECOND_LAW_FORMALIZATION_2026-05-25.md; a declaration with this final name exists in project sources but not in the audited modules |
| info | heuristic | F10 | CITED_DECLARATION_UNLOADED | SGC.Evolution.Dynamics.EvolutionStep | cited in demos/README.md; a declaration with this final name exists in project sources but not in the audited modules |
| info | heuristic | F10 | CITED_DECLARATION_UNLOADED | SGC.Markov.StationaryDistribution.lean | cited in reports/PHASE_R2_R4_OPEN_DISCOVERY_FINDINGS.md; a declaration with this final name exists in project sources but not in the audited modules |
| info | heuristic | F10 | CITED_DECLARATION_UNLOADED | SGC.Quantum.KnillLaflamme.lean | cited in reports/PHASE_R2_R4_OPEN_DISCOVERY_FINDINGS.md; a declaration with this final name exists in project sources but not in the audited modules |
| info | heuristic | F10 | CITED_DECLARATION_UNLOADED | SGC.Spectral.Floquet.PeriodicGeneratorFamily | cited in reports/SPINGLASS_GAUGE_AUDIT.md; a declaration with this final name exists in project sources but not in the audited modules |
| info | heuristic | F10 | CITED_DECLARATION_UNLOADED | SGC.Stochastic.conjecture_C2_hard_half | cited in reports/CELEGANS_FLOQUET_TSALLIS_BRIDGE.md; a declaration with this final name exists in project sources but not in the audited modules |
| info | heuristic | F10 | CITED_DECLARATION_UNLOADED | SGC.Thermodynamics.Evolution.CanEvolve | cited in demos/README.md; a declaration with this final name exists in project sources but not in the audited modules |
| info | heuristic | F10 | CITED_DECLARATION_UNLOADED | SGC.Thermodynamics.Evolution.SatisfiesEvolutionInequality | cited in demos/README.md; a declaration with this final name exists in project sources but not in the audited modules |
| info | heuristic | F10 | CITED_DECLARATION_UNLOADED | SGC.Thermodynamics.antisymmetric_part_zero_iff_detailed_balance | cited in reports/BROWNIAN_MOTION_LEAN_EXPLORATION.md; a declaration with this final name exists in project sources but not in the audited modules |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Decoder.bounds | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Decoder.error_bounds | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Decoder.error_sum | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Decoder.loss_bounds | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.ProbabilityRow.ext | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.ProbabilityRow.ext_iff | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.ProbabilityRow.nonempty | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.ProbabilityRow.nonneg | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.ProbabilityRow.push_apply | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.ProbabilityRow.sum_one | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.asymmetric_deterministic_minimax_attained | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.asymmetric_deterministic_minimax_lower | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.asymmetric_equal_prior_attained | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.asymmetric_equal_prior_lower | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.asymmetric_errors | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.asymmetric_minimax_attained | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.asymmetric_minimax_lower | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.asymmetric_no_both_quarter | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.discrete_coarse_entry | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.discrete_commutator_zero | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.discrete_quot_eq | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.erase_coarse_eq_one | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.erase_lift_entry | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.erase_quot_subsingleton | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.erasing_actual_equal | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.erasing_budget_zero | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.erasing_closure_zero | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.erasing_exact_transfer | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.erasing_full_tv_one | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.erasing_no_both_below_half | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.erasing_observed_tv_zero | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.erasing_threshold_equality | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.identity_stochastic | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.nonstationary_reference_exact | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.point_half_tv | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.point_l1_normalization | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.point_tv_normalization | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.reset_dobrushin_zero | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.reset_forgets_both_inputs | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.reset_stochastic | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.swap_dobrushin_one | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.swap_stochastic | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.weights_not_normalized | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.weights_not_stationary | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.Regression.weights_positive | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.RowStochastic.mul | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.RowStochastic.nonneg | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.RowStochastic.of_existing | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.RowStochastic.one | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.RowStochastic.pow | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.RowStochastic.sum_one | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.abs_bounded_test_le_half_l1 | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.abs_interval_test_le | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.actualLaw_alignment | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.bounded_test_tv | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.class_terminal_budget_exact | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.closureCommutator_row_sum_zero | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.decoder_error_sum_lower | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.deterministic_error_eq | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.dobrushin_le_one | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.dobrushin_nonneg | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.exact_terminal_budget_le | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.fixed_decoder_error_transfer | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.iterated_tv_contraction | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.joint_terminal_certificate | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.kernel_error_dobrushin | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.kernel_fixed_decoder_error_transfer | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.kernel_horizon_tv | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.kernel_horizon_tv_mixing | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.kernel_horizon_tv_sharp | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.kernel_horizon_tv_uniform_mixing | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.kernel_horizon_tv_zero | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.kernel_joint_terminal_certificate | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.kernel_terminal_reliability | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.l1_nonneg | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.l1_vecMul_le | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.mixing_budget_le_terminal | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.no_terminal_decoder_of_contraction | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.observed_distinguishability_lower | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.observed_distinguishability_two_sided | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.prob_vecMul_row_l1_le | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.reference_contraction_compatibility | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.rowL1Norm_le | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.rowL1Norm_mul_dobrushin | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.rowL1Norm_mul_pow_dobrushin | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.rowStochastic_lift | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.row_l1_le_rowL1Norm | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.row_tv_le_dobrushin | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.semantic_contraction_compatibility | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.signed_l1_vecMul_dobrushin | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.stochastic_difference_rowL1Norm_le_two | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.sum_vecMul_stochastic | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.terminalBudget_zero | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.terminalError_zero | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.terminal_reliability_of_reference_bounds | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.tv_data_processing | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.tv_dobrushin_contraction | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.tv_le_one | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.tv_lower_of_individual_error_bounds | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.tv_nonneg | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.tv_self | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.tv_symm | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.tv_triangle | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.TerminalDecoding.tv_vecMul_le_half_row_l1 | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Decoder.bounds | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Decoder.error_bounds | 6 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Decoder.error_sum | 6 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Decoder.loss_bounds | 3 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.ProbabilityRow.ext | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.ProbabilityRow.ext_iff | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.ProbabilityRow.nonempty | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.ProbabilityRow.nonneg | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.ProbabilityRow.push_apply | 5 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.ProbabilityRow.sum_one | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.asymmetric_deterministic_minimax_attained | 11 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.asymmetric_deterministic_minimax_lower | 11 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.asymmetric_equal_prior_attained | 11 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.asymmetric_equal_prior_lower | 9 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.asymmetric_errors | 9 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.asymmetric_minimax_attained | 11 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.asymmetric_minimax_lower | 9 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.asymmetric_no_both_quarter | 9 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.discrete_coarse_entry | 12 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.discrete_commutator_zero | 15 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.discrete_quot_eq | 6 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.erase_coarse_eq_one | 13 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.erase_lift_entry | 9 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.erase_quot_subsingleton | 5 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.erasing_actual_equal | 23 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.erasing_budget_zero | 17 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.erasing_closure_zero | 15 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.erasing_exact_transfer | 33 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.erasing_full_tv_one | 6 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.erasing_no_both_below_half | 28 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.erasing_observed_tv_zero | 26 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.erasing_threshold_equality | 17 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.identity_stochastic | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.nonstationary_reference_exact | 28 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.point_half_tv | 7 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.point_l1_normalization | 5 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.point_tv_normalization | 6 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.reset_dobrushin_zero | 4 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.reset_forgets_both_inputs | 7 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.reset_stochastic | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.swap_dobrushin_one | 4 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.swap_stochastic | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.weights_not_normalized | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.weights_not_stationary | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.Regression.weights_positive | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.RowStochastic.mul | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.RowStochastic.nonneg | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.RowStochastic.of_existing | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.RowStochastic.one | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.RowStochastic.pow | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.RowStochastic.sum_one | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.abs_bounded_test_le_half_l1 | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.abs_interval_test_le | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.actualLaw_alignment | 25 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.bounded_test_tv | 4 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.class_terminal_budget_exact | 23 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.closureCommutator_row_sum_zero | 13 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.decoder_error_sum_lower | 8 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.deterministic_error_eq | 8 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.dobrushin_le_one | 4 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.dobrushin_nonneg | 3 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.exact_terminal_budget_le | 17 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.fixed_decoder_error_transfer | 8 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.iterated_tv_contraction | 7 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.joint_terminal_certificate | 7 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.kernel_error_dobrushin | 17 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.kernel_fixed_decoder_error_transfer | 26 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.kernel_horizon_tv | 24 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.kernel_horizon_tv_mixing | 26 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.kernel_horizon_tv_sharp | 24 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.kernel_horizon_tv_uniform_mixing | 25 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.kernel_horizon_tv_zero | 21 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.kernel_joint_terminal_certificate | 24 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.kernel_terminal_reliability | 26 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.l1_nonneg | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.l1_vecMul_le | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.mixing_budget_le_terminal | 18 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.no_terminal_decoder_of_contraction | 8 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.observed_distinguishability_lower | 4 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.observed_distinguishability_two_sided | 4 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.prob_vecMul_row_l1_le | 4 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.reference_contraction_compatibility | 4 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.rowL1Norm_le | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.rowL1Norm_mul_dobrushin | 3 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.rowL1Norm_mul_pow_dobrushin | 4 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.rowStochastic_lift | 9 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.row_l1_le_rowL1Norm | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.row_tv_le_dobrushin | 5 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.semantic_contraction_compatibility | 8 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.signed_l1_vecMul_dobrushin | 4 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.stochastic_difference_rowL1Norm_le_two | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.sum_vecMul_stochastic | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.terminalBudget_zero | 14 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.terminalError_zero | 12 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.terminal_reliability_of_reference_bounds | 8 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.tv_data_processing | 3 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.tv_dobrushin_contraction | 7 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.tv_le_one | 4 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.tv_lower_of_individual_error_bounds | 8 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.tv_nonneg | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.tv_self | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.tv_symm | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.tv_triangle | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.TerminalDecoding.tv_vecMul_le_half_row_l1 | 5 project-local definition(s) determine what this theorem is about; read them |

## Per-theorem receipt

### `SGC.Bridge.TerminalDecoding.Decoder.bounds`

- statement (kernel-elaborated, sha256 `0fd835295623d7b8`):

      ∀ {X : Type u_4} (self : SGC.Bridge.TerminalDecoding.Decoder X) (x : X), self.probOne x ∈ Set.Icc 0 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.Decoder` (inductive, SGC.Bridge.TerminalDecoding): `Type u_4 → Type u_4`
    - `SGC.Bridge.TerminalDecoding.Decoder.probOne` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → SGC.Bridge.TerminalDecoding.Decoder X → X → ℝ`

### `SGC.Bridge.TerminalDecoding.Decoder.error_bounds`

- statement (kernel-elaborated, sha256 `2f3f42fa912156dc`):

      ∀ {X : Type u_1} [inst : Fintype X] (d : SGC.Bridge.TerminalDecoding.Decoder X) (p : SGC.Bridge.TerminalDecoding.ProbabilityRow X) (b : Bool), d.error p b ∈ Set.Icc 0 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.Decoder` (inductive, SGC.Bridge.TerminalDecoding): `Type u_4 → Type u_4`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.Decoder.error` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.Decoder X → SGC.Bridge.TerminalDecoding.ProbabilityRow X → Bool → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.loss` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → SGC.Bridge.TerminalDecoding.Decoder X → Bool → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.probOne` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → SGC.Bridge.TerminalDecoding.Decoder X → X → ℝ`

### `SGC.Bridge.TerminalDecoding.Decoder.error_sum`

- statement (kernel-elaborated, sha256 `e8318d702d920b3e`):

      ∀ {X : Type u_1} [inst : Fintype X] (d : SGC.Bridge.TerminalDecoding.Decoder X) (p q : SGC.Bridge.TerminalDecoding.ProbabilityRow X), d.error p false + d.error q true = 1 - (∑ x, q.mass x * d.probOne x - ∑ x, p.mass x * d.probOne x)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.Decoder` (inductive, SGC.Bridge.TerminalDecoding): `Type u_4 → Type u_4`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.Decoder.error` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.Decoder X → SGC.Bridge.TerminalDecoding.ProbabilityRow X → Bool → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.probOne` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → SGC.Bridge.TerminalDecoding.Decoder X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.loss` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → SGC.Bridge.TerminalDecoding.Decoder X → Bool → X → ℝ`

### `SGC.Bridge.TerminalDecoding.Decoder.loss_bounds`

- statement (kernel-elaborated, sha256 `4972fa0a09bb075d`):

      ∀ {X : Type u_1} (d : SGC.Bridge.TerminalDecoding.Decoder X) (b : Bool) (x : X), d.loss b x ∈ Set.Icc 0 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.Decoder` (inductive, SGC.Bridge.TerminalDecoding): `Type u_4 → Type u_4`
    - `SGC.Bridge.TerminalDecoding.Decoder.loss` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → SGC.Bridge.TerminalDecoding.Decoder X → Bool → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.probOne` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → SGC.Bridge.TerminalDecoding.Decoder X → X → ℝ`

### `SGC.Bridge.TerminalDecoding.ProbabilityRow.ext`

- statement (kernel-elaborated, sha256 `4b0e888d677051ec`):

      ∀ {X : Type u_1} [inst : Fintype X] {p q : SGC.Bridge.TerminalDecoding.ProbabilityRow X}, (∀ (x : X), p.mass x = q.mass x) → p = q

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`

### `SGC.Bridge.TerminalDecoding.ProbabilityRow.ext_iff`

- statement (kernel-elaborated, sha256 `a42d0b48af977295`):

      ∀ {X : Type u_1} [inst : Fintype X] {p q : SGC.Bridge.TerminalDecoding.ProbabilityRow X}, p = q ↔ ∀ (x : X), p.mass x = q.mass x

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`

### `SGC.Bridge.TerminalDecoding.ProbabilityRow.nonempty`

- statement (kernel-elaborated, sha256 `fe95c873a78a39ac`):

      ∀ {X : Type u_1} [inst : Fintype X] (p : SGC.Bridge.TerminalDecoding.ProbabilityRow X), Nonempty X

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`

### `SGC.Bridge.TerminalDecoding.ProbabilityRow.nonneg`

- statement (kernel-elaborated, sha256 `c6d4854961ee081f`):

      ∀ {X : Type u_4} [inst : Fintype X] (self : SGC.Bridge.TerminalDecoding.ProbabilityRow X) (x : X), 0 ≤ self.mass x

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`

### `SGC.Bridge.TerminalDecoding.ProbabilityRow.push_apply`

- statement (kernel-elaborated, sha256 `30ebb70ce7048416`):

      ∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype X] [inst_1 : Fintype Y] (p : SGC.Bridge.TerminalDecoding.ProbabilityRow X) (M : Matrix X Y ℝ) (hM : SGC.Bridge.TerminalDecoding.RowStochastic M) (y : Y), (p.push M hM).mass y = ∑ x, p.mass x * M x y

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.push` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [inst : Fintype X] → [inst_1 : Fintype Y] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → (M : Matrix X Y ℝ) → SGC.Bridge.TerminalDecoding.RowStochastic M → SGC.Bridge.TerminalDecoding.ProbabilityRow Y`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`

### `SGC.Bridge.TerminalDecoding.ProbabilityRow.sum_one`

- statement (kernel-elaborated, sha256 `124a052d60bbac32`):

      ∀ {X : Type u_4} [inst : Fintype X] (self : SGC.Bridge.TerminalDecoding.ProbabilityRow X), ∑ x, self.mass x = 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`

### `SGC.Bridge.TerminalDecoding.Regression.asymmetric_deterministic_minimax_attained`

- statement (kernel-elaborated, sha256 `3f5db57cb2132ef9`):

      max ((SGC.Bridge.TerminalDecoding.deterministicDecoder fun x => x == 1).error (SGC.Bridge.TerminalDecoding.Regression.point 0) false) ((SGC.Bridge.TerminalDecoding.deterministicDecoder fun x => x == 1).error SGC.Bridge.TerminalDecoding.Regression.half true) = 1 / 2

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.Decoder.error` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.Decoder X → SGC.Bridge.TerminalDecoding.ProbabilityRow X → Bool → ℝ`
    - `SGC.Bridge.TerminalDecoding.deterministicDecoder` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → (X → Bool) → SGC.Bridge.TerminalDecoding.Decoder X`
    - `SGC.Bridge.TerminalDecoding.Regression.point` (def, SGC.Bridge.TerminalDecoding): `Fin 2 → SGC.Bridge.TerminalDecoding.ProbabilityRow (Fin 2)`
    - `SGC.Bridge.TerminalDecoding.Regression.half` (def, SGC.Bridge.TerminalDecoding): `SGC.Bridge.TerminalDecoding.ProbabilityRow (Fin 2)`
    - `SGC.Bridge.TerminalDecoding.Decoder` (inductive, SGC.Bridge.TerminalDecoding): `Type u_4 → Type u_4`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.loss` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → SGC.Bridge.TerminalDecoding.Decoder X → Bool → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → (probOne : X → ℝ) → (∀ (x : X), probOne x ∈ Set.Icc 0 1) → SGC.Bridge.TerminalDecoding.Decoder X`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.Bridge.TerminalDecoding.Decoder.probOne` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → SGC.Bridge.TerminalDecoding.Decoder X → X → ℝ`

### `SGC.Bridge.TerminalDecoding.Regression.asymmetric_deterministic_minimax_lower`

- statement (kernel-elaborated, sha256 `35eeed6b2b89d35e`):

      ∀ (d : Fin 2 → Bool), 1 / 2 ≤ max ((SGC.Bridge.TerminalDecoding.deterministicDecoder d).error (SGC.Bridge.TerminalDecoding.Regression.point 0) false) ((SGC.Bridge.TerminalDecoding.deterministicDecoder d).error SGC.Bridge.TerminalDecoding.Regression.half true)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.Decoder.error` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.Decoder X → SGC.Bridge.TerminalDecoding.ProbabilityRow X → Bool → ℝ`
    - `SGC.Bridge.TerminalDecoding.deterministicDecoder` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → (X → Bool) → SGC.Bridge.TerminalDecoding.Decoder X`
    - `SGC.Bridge.TerminalDecoding.Regression.point` (def, SGC.Bridge.TerminalDecoding): `Fin 2 → SGC.Bridge.TerminalDecoding.ProbabilityRow (Fin 2)`
    - `SGC.Bridge.TerminalDecoding.Regression.half` (def, SGC.Bridge.TerminalDecoding): `SGC.Bridge.TerminalDecoding.ProbabilityRow (Fin 2)`
    - `SGC.Bridge.TerminalDecoding.Decoder` (inductive, SGC.Bridge.TerminalDecoding): `Type u_4 → Type u_4`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.loss` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → SGC.Bridge.TerminalDecoding.Decoder X → Bool → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → (probOne : X → ℝ) → (∀ (x : X), probOne x ∈ Set.Icc 0 1) → SGC.Bridge.TerminalDecoding.Decoder X`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.Bridge.TerminalDecoding.Decoder.probOne` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → SGC.Bridge.TerminalDecoding.Decoder X → X → ℝ`

### `SGC.Bridge.TerminalDecoding.Regression.asymmetric_equal_prior_attained`

- statement (kernel-elaborated, sha256 `be3782beb71591d7`):

      (SGC.Bridge.TerminalDecoding.Regression.averageDecoder.error (SGC.Bridge.TerminalDecoding.Regression.point 0) false + SGC.Bridge.TerminalDecoding.Regression.averageDecoder.error SGC.Bridge.TerminalDecoding.Regression.half true) / 2 = 1 / 4

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.Decoder.error` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.Decoder X → SGC.Bridge.TerminalDecoding.ProbabilityRow X → Bool → ℝ`
    - `SGC.Bridge.TerminalDecoding.Regression.averageDecoder` (def, SGC.Bridge.TerminalDecoding): `SGC.Bridge.TerminalDecoding.Decoder (Fin 2)`
    - `SGC.Bridge.TerminalDecoding.Regression.point` (def, SGC.Bridge.TerminalDecoding): `Fin 2 → SGC.Bridge.TerminalDecoding.ProbabilityRow (Fin 2)`
    - `SGC.Bridge.TerminalDecoding.Regression.half` (def, SGC.Bridge.TerminalDecoding): `SGC.Bridge.TerminalDecoding.ProbabilityRow (Fin 2)`
    - `SGC.Bridge.TerminalDecoding.Decoder` (inductive, SGC.Bridge.TerminalDecoding): `Type u_4 → Type u_4`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.loss` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → SGC.Bridge.TerminalDecoding.Decoder X → Bool → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → (probOne : X → ℝ) → (∀ (x : X), probOne x ∈ Set.Icc 0 1) → SGC.Bridge.TerminalDecoding.Decoder X`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.Bridge.TerminalDecoding.Decoder.probOne` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → SGC.Bridge.TerminalDecoding.Decoder X → X → ℝ`

### `SGC.Bridge.TerminalDecoding.Regression.asymmetric_equal_prior_lower`

- statement (kernel-elaborated, sha256 `ab9536ec10f5e772`):

      ∀ (d : SGC.Bridge.TerminalDecoding.Decoder (Fin 2)), 1 / 4 ≤ (d.error (SGC.Bridge.TerminalDecoding.Regression.point 0) false + d.error SGC.Bridge.TerminalDecoding.Regression.half true) / 2

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.Decoder` (inductive, SGC.Bridge.TerminalDecoding): `Type u_4 → Type u_4`
    - `SGC.Bridge.TerminalDecoding.Decoder.error` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.Decoder X → SGC.Bridge.TerminalDecoding.ProbabilityRow X → Bool → ℝ`
    - `SGC.Bridge.TerminalDecoding.Regression.point` (def, SGC.Bridge.TerminalDecoding): `Fin 2 → SGC.Bridge.TerminalDecoding.ProbabilityRow (Fin 2)`
    - `SGC.Bridge.TerminalDecoding.Regression.half` (def, SGC.Bridge.TerminalDecoding): `SGC.Bridge.TerminalDecoding.ProbabilityRow (Fin 2)`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.loss` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → SGC.Bridge.TerminalDecoding.Decoder X → Bool → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.Bridge.TerminalDecoding.Decoder.probOne` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → SGC.Bridge.TerminalDecoding.Decoder X → X → ℝ`

### `SGC.Bridge.TerminalDecoding.Regression.asymmetric_errors`

- statement (kernel-elaborated, sha256 `fd2230695d54969d`):

      ∀ (d : SGC.Bridge.TerminalDecoding.Decoder (Fin 2)), d.error (SGC.Bridge.TerminalDecoding.Regression.point 0) false = d.probOne 0 ∧ d.error SGC.Bridge.TerminalDecoding.Regression.half true = 1 - (d.probOne 0 + d.probOne 1) / 2

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.Decoder` (inductive, SGC.Bridge.TerminalDecoding): `Type u_4 → Type u_4`
    - `SGC.Bridge.TerminalDecoding.Decoder.error` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.Decoder X → SGC.Bridge.TerminalDecoding.ProbabilityRow X → Bool → ℝ`
    - `SGC.Bridge.TerminalDecoding.Regression.point` (def, SGC.Bridge.TerminalDecoding): `Fin 2 → SGC.Bridge.TerminalDecoding.ProbabilityRow (Fin 2)`
    - `SGC.Bridge.TerminalDecoding.Decoder.probOne` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → SGC.Bridge.TerminalDecoding.Decoder X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Regression.half` (def, SGC.Bridge.TerminalDecoding): `SGC.Bridge.TerminalDecoding.ProbabilityRow (Fin 2)`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.loss` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → SGC.Bridge.TerminalDecoding.Decoder X → Bool → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`

### `SGC.Bridge.TerminalDecoding.Regression.asymmetric_minimax_attained`

- statement (kernel-elaborated, sha256 `6d8ec7c548abdc1e`):

      max (SGC.Bridge.TerminalDecoding.Regression.minimaxDecoder.error (SGC.Bridge.TerminalDecoding.Regression.point 0) false) (SGC.Bridge.TerminalDecoding.Regression.minimaxDecoder.error SGC.Bridge.TerminalDecoding.Regression.half true) = 1 / 3

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.Decoder.error` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.Decoder X → SGC.Bridge.TerminalDecoding.ProbabilityRow X → Bool → ℝ`
    - `SGC.Bridge.TerminalDecoding.Regression.minimaxDecoder` (def, SGC.Bridge.TerminalDecoding): `SGC.Bridge.TerminalDecoding.Decoder (Fin 2)`
    - `SGC.Bridge.TerminalDecoding.Regression.point` (def, SGC.Bridge.TerminalDecoding): `Fin 2 → SGC.Bridge.TerminalDecoding.ProbabilityRow (Fin 2)`
    - `SGC.Bridge.TerminalDecoding.Regression.half` (def, SGC.Bridge.TerminalDecoding): `SGC.Bridge.TerminalDecoding.ProbabilityRow (Fin 2)`
    - `SGC.Bridge.TerminalDecoding.Decoder` (inductive, SGC.Bridge.TerminalDecoding): `Type u_4 → Type u_4`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.loss` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → SGC.Bridge.TerminalDecoding.Decoder X → Bool → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → (probOne : X → ℝ) → (∀ (x : X), probOne x ∈ Set.Icc 0 1) → SGC.Bridge.TerminalDecoding.Decoder X`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.Bridge.TerminalDecoding.Decoder.probOne` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → SGC.Bridge.TerminalDecoding.Decoder X → X → ℝ`

### `SGC.Bridge.TerminalDecoding.Regression.asymmetric_minimax_lower`

- statement (kernel-elaborated, sha256 `c6d8d881d4c91065`):

      ∀ (d : SGC.Bridge.TerminalDecoding.Decoder (Fin 2)), 1 / 3 ≤ max (d.error (SGC.Bridge.TerminalDecoding.Regression.point 0) false) (d.error SGC.Bridge.TerminalDecoding.Regression.half true)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.Decoder` (inductive, SGC.Bridge.TerminalDecoding): `Type u_4 → Type u_4`
    - `SGC.Bridge.TerminalDecoding.Decoder.error` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.Decoder X → SGC.Bridge.TerminalDecoding.ProbabilityRow X → Bool → ℝ`
    - `SGC.Bridge.TerminalDecoding.Regression.point` (def, SGC.Bridge.TerminalDecoding): `Fin 2 → SGC.Bridge.TerminalDecoding.ProbabilityRow (Fin 2)`
    - `SGC.Bridge.TerminalDecoding.Regression.half` (def, SGC.Bridge.TerminalDecoding): `SGC.Bridge.TerminalDecoding.ProbabilityRow (Fin 2)`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.loss` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → SGC.Bridge.TerminalDecoding.Decoder X → Bool → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.Bridge.TerminalDecoding.Decoder.probOne` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → SGC.Bridge.TerminalDecoding.Decoder X → X → ℝ`

### `SGC.Bridge.TerminalDecoding.Regression.asymmetric_no_both_quarter`

- statement (kernel-elaborated, sha256 `3f214e7b9436a5cc`):

      ∀ (d : SGC.Bridge.TerminalDecoding.Decoder (Fin 2)), ¬(d.error (SGC.Bridge.TerminalDecoding.Regression.point 0) false ≤ 1 / 4 ∧ d.error SGC.Bridge.TerminalDecoding.Regression.half true ≤ 1 / 4)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.Decoder` (inductive, SGC.Bridge.TerminalDecoding): `Type u_4 → Type u_4`
    - `SGC.Bridge.TerminalDecoding.Decoder.error` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.Decoder X → SGC.Bridge.TerminalDecoding.ProbabilityRow X → Bool → ℝ`
    - `SGC.Bridge.TerminalDecoding.Regression.point` (def, SGC.Bridge.TerminalDecoding): `Fin 2 → SGC.Bridge.TerminalDecoding.ProbabilityRow (Fin 2)`
    - `SGC.Bridge.TerminalDecoding.Regression.half` (def, SGC.Bridge.TerminalDecoding): `SGC.Bridge.TerminalDecoding.ProbabilityRow (Fin 2)`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.loss` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → SGC.Bridge.TerminalDecoding.Decoder X → Bool → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.Bridge.TerminalDecoding.Decoder.probOne` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → SGC.Bridge.TerminalDecoding.Decoder X → X → ℝ`

### `SGC.Bridge.TerminalDecoding.Regression.discrete_coarse_entry`

- statement (kernel-elaborated, sha256 `2d72cb94cb921028`):

      ∀ (T : Matrix (Fin 2) (Fin 2) ℝ) (x y : Fin 2), SGC.Thermodynamics.CoarseGenerator T SGC.Bridge.TerminalDecoding.Regression.discretePartition SGC.Bridge.TerminalDecoding.Regression.weights (SGC.Bridge.TerminalDecoding.Regression.discretePartition.quot_map x) (SGC.Bridge.TerminalDecoding.Regression.discretePartition.quot_map y) = T x y

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.Regression.discretePartition` (def, SGC.Bridge.TerminalDecoding): `SGC.Partition (Fin 2)`
    - `SGC.Bridge.TerminalDecoding.Regression.weights` (def, SGC.Bridge.TerminalDecoding): `Fin 2 → ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.TerminalDecoding.Regression.discrete_commutator_zero`

- statement (kernel-elaborated, sha256 `b65a8311504690f4`):

      ∀ (T : Matrix (Fin 2) (Fin 2) ℝ), SGC.Renormalization.MeasureReentry.closureCommutator T SGC.Bridge.TerminalDecoding.Regression.discretePartition SGC.Bridge.TerminalDecoding.Regression.weights = 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.TerminalDecoding.Regression.discretePartition` (def, SGC.Bridge.TerminalDecoding): `SGC.Partition (Fin 2)`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.Regression.weights` (def, SGC.Bridge.TerminalDecoding): `Fin 2 → ℝ`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.TerminalDecoding.Regression.discrete_quot_eq`

- statement (kernel-elaborated, sha256 `3be43c90b20aa2b0`):

      ∀ (x y : Fin 2), SGC.Bridge.TerminalDecoding.Regression.discretePartition.quot_map x = SGC.Bridge.TerminalDecoding.Regression.discretePartition.quot_map y ↔ x = y

- axioms: Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=simp vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.TerminalDecoding.Regression.discretePartition` (def, SGC.Bridge.TerminalDecoding): `SGC.Partition (Fin 2)`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`

### `SGC.Bridge.TerminalDecoding.Regression.erase_coarse_eq_one`

- statement (kernel-elaborated, sha256 `959d21c2e79b0520`):

      ∀ (T : Matrix (Fin 2) (Fin 2) ℝ), SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Thermodynamics.CoarseGenerator T SGC.Bridge.TerminalDecoding.Regression.erasePartition SGC.Bridge.TerminalDecoding.Regression.weights = 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.TerminalDecoding.Regression.erasePartition` (def, SGC.Bridge.TerminalDecoding): `SGC.Partition (Fin 2)`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.Regression.weights` (def, SGC.Bridge.TerminalDecoding): `Fin 2 → ℝ`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.TerminalDecoding.Regression.erase_lift_entry`

- statement (kernel-elaborated, sha256 `f6915791781d1023`):

      ∀ (x : Fin 2) (y : SGC.Bridge.TerminalDecoding.Regression.erasePartition.Quot), SGC.lift_matrix SGC.Bridge.TerminalDecoding.Regression.erasePartition x y = 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.TerminalDecoding.Regression.erasePartition` (def, SGC.Bridge.TerminalDecoding): `SGC.Partition (Fin 2)`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.TerminalDecoding.Regression.erase_quot_subsingleton`

- statement (kernel-elaborated, sha256 `8d08c6fbfcc4dcad`):

      Subsingleton SGC.Bridge.TerminalDecoding.Regression.erasePartition.Quot

- axioms: Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.TerminalDecoding.Regression.erasePartition` (def, SGC.Bridge.TerminalDecoding): `SGC.Partition (Fin 2)`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`

### `SGC.Bridge.TerminalDecoding.Regression.erasing_actual_equal`

- statement (kernel-elaborated, sha256 `9ad74e90bdf181f5`):

      ∀ (p q : SGC.Bridge.TerminalDecoding.ProbabilityRow (Fin 2)) (m : ℕ), SGC.Bridge.TerminalDecoding.actualLaw 1 SGC.Bridge.TerminalDecoding.Regression.erasePartition SGC.Bridge.TerminalDecoding.Regression.identity_stochastic p m = SGC.Bridge.TerminalDecoding.actualLaw 1 SGC.Bridge.TerminalDecoding.Regression.erasePartition SGC.Bridge.TerminalDecoding.Regression.identity_stochastic q m

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.TerminalDecoding.Regression.erasePartition` (def, SGC.Bridge.TerminalDecoding): `SGC.Partition (Fin 2)`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Bridge.TerminalDecoding.actualLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.TerminalDecoding.Regression.identity_stochastic` (theorem, SGC.Bridge.TerminalDecoding): `SGC.Renormalization.KernelHorizon.IsStochastic 1`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.push` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [inst : Fintype X] → [inst_1 : Fintype Y] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → (M : Matrix X Y ℝ) → SGC.Bridge.TerminalDecoding.RowStochastic M → SGC.Bridge.TerminalDecoding.ProbabilityRow Y`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Renormalization.KernelHorizon.IsStochastic.mk` (ctor, SGC.Renormalization.KernelHorizon): `∀ {V : Type u_1} [inst : Fintype V] {T : Matrix V V ℝ}, (∀ (i j : V), 0 ≤ T i j) → (∀ (i : V), ∑ j, T i j = 1) → SGC.Renormalization.KernelHorizon.IsStochastic T`
    - `SGC.Bridge.TerminalDecoding.RowStochastic.nonneg` (theorem, SGC.Bridge.TerminalDecoding): `∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype Y] {M : Matrix X Y ℝ}, SGC.Bridge.TerminalDecoding.RowStochastic M → ∀ (x : X) (y : Y), 0 ≤ M x y`
    - `SGC.Bridge.TerminalDecoding.RowStochastic.one` (theorem, SGC.Bridge.TerminalDecoding): `∀ {X : Type u_1} [inst : Fintype X] [inst_1 : DecidableEq X], SGC.Bridge.TerminalDecoding.RowStochastic 1`
    - `SGC.Bridge.TerminalDecoding.RowStochastic.sum_one` (theorem, SGC.Bridge.TerminalDecoding): `∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype Y] {M : Matrix X Y ℝ}, SGC.Bridge.TerminalDecoding.RowStochastic M → ∀ (x : X), ∑ y, M x y = 1`
    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Bridge.TerminalDecoding.RowStochastic.mk` (ctor, SGC.Bridge.TerminalDecoding): `∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype Y] {M : Matrix X Y ℝ}, (∀ (x : X) (y : Y), 0 ≤ M x y) → (∀ (x : X), ∑ y, M x y = 1) → SGC.Bridge.TerminalDecoding.RowStochastic M`

### `SGC.Bridge.TerminalDecoding.Regression.erasing_budget_zero`

- statement (kernel-elaborated, sha256 `f16ea7b0159f65be`):

      ∀ (m : ℕ), SGC.Bridge.TerminalDecoding.terminalBudget 1 SGC.Bridge.TerminalDecoding.Regression.erasePartition SGC.Bridge.TerminalDecoding.Regression.weights m = 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.terminalBudget` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → [inst : DecidableEq X] → Matrix X X ℝ → SGC.Partition X → (X → ℝ) → ℕ → ℝ`
    - `SGC.Bridge.TerminalDecoding.Regression.erasePartition` (def, SGC.Bridge.TerminalDecoding): `SGC.Partition (Fin 2)`
    - `SGC.Bridge.TerminalDecoding.Regression.weights` (def, SGC.Bridge.TerminalDecoding): `Fin 2 → ℝ`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.TerminalDecoding.Regression.erasing_closure_zero`

- statement (kernel-elaborated, sha256 `48651362c4e08aab`):

      SGC.Renormalization.MeasureReentry.closureCommutator 1 SGC.Bridge.TerminalDecoding.Regression.erasePartition SGC.Bridge.TerminalDecoding.Regression.weights = 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.TerminalDecoding.Regression.erasePartition` (def, SGC.Bridge.TerminalDecoding): `SGC.Partition (Fin 2)`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.Regression.weights` (def, SGC.Bridge.TerminalDecoding): `Fin 2 → ℝ`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.TerminalDecoding.Regression.erasing_exact_transfer`

- statement (kernel-elaborated, sha256 `17f6b3a1e424032e`):

      ∀ (rho : SGC.Bridge.TerminalDecoding.ProbabilityRow (Fin 2)) (d : SGC.Bridge.TerminalDecoding.Decoder SGC.Bridge.TerminalDecoding.Regression.erasePartition.Quot) (b : Bool) (m : ℕ), d.error (SGC.Bridge.TerminalDecoding.actualLaw 1 SGC.Bridge.TerminalDecoding.Regression.erasePartition SGC.Bridge.TerminalDecoding.Regression.identity_stochastic rho m) b = d.error (SGC.Bridge.TerminalDecoding.referenceLaw 1 SGC.Bridge.TerminalDecoding.Regression.erasePartition SGC.Bridge.TerminalDecoding.Regression.weights_positive SGC.Bridge.TerminalDecoding.Regression.identity_stochastic rho m) b

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.Decoder` (inductive, SGC.Bridge.TerminalDecoding): `Type u_4 → Type u_4`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.TerminalDecoding.Regression.erasePartition` (def, SGC.Bridge.TerminalDecoding): `SGC.Partition (Fin 2)`
    - `SGC.Bridge.TerminalDecoding.Decoder.error` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.Decoder X → SGC.Bridge.TerminalDecoding.ProbabilityRow X → Bool → ℝ`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Bridge.TerminalDecoding.actualLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.TerminalDecoding.Regression.identity_stochastic` (theorem, SGC.Bridge.TerminalDecoding): `SGC.Renormalization.KernelHorizon.IsStochastic 1`
    - `SGC.Bridge.TerminalDecoding.referenceLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → {pi : X → ℝ} → (∀ (x : X), 0 < pi x) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.TerminalDecoding.Regression.weights` (def, SGC.Bridge.TerminalDecoding): `Fin 2 → ℝ`
    - `SGC.Bridge.TerminalDecoding.Regression.weights_positive` (theorem, SGC.Bridge.TerminalDecoding): `∀ (x : Fin 2), 0 < SGC.Bridge.TerminalDecoding.Regression.weights x`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.loss` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → SGC.Bridge.TerminalDecoding.Decoder X → Bool → X → ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.push` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [inst : Fintype X] → [inst_1 : Fintype Y] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → (M : Matrix X Y ℝ) → SGC.Bridge.TerminalDecoding.RowStochastic M → SGC.Bridge.TerminalDecoding.ProbabilityRow Y`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Renormalization.KernelHorizon.IsStochastic.mk` (ctor, SGC.Renormalization.KernelHorizon): `∀ {V : Type u_1} [inst : Fintype V] {T : Matrix V V ℝ}, (∀ (i j : V), 0 ≤ T i j) → (∀ (i : V), ∑ j, T i j = 1) → SGC.Renormalization.KernelHorizon.IsStochastic T`
    - `SGC.Bridge.TerminalDecoding.RowStochastic.nonneg` (theorem, SGC.Bridge.TerminalDecoding): `∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype Y] {M : Matrix X Y ℝ}, SGC.Bridge.TerminalDecoding.RowStochastic M → ∀ (x : X) (y : Y), 0 ≤ M x y`
    - `SGC.Bridge.TerminalDecoding.RowStochastic.one` (theorem, SGC.Bridge.TerminalDecoding): `∀ {X : Type u_1} [inst : Fintype X] [inst_1 : DecidableEq X], SGC.Bridge.TerminalDecoding.RowStochastic 1`
    - `SGC.Bridge.TerminalDecoding.RowStochastic.sum_one` (theorem, SGC.Bridge.TerminalDecoding): `∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype Y] {M : Matrix X Y ℝ}, SGC.Bridge.TerminalDecoding.RowStochastic M → ∀ (x : X), ∑ y, M x y = 1`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.probOne` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → SGC.Bridge.TerminalDecoding.Decoder X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Bridge.TerminalDecoding.RowStochastic.mk` (ctor, SGC.Bridge.TerminalDecoding): `∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype Y] {M : Matrix X Y ℝ}, (∀ (x : X) (y : Y), 0 ≤ M x y) → (∀ (x : X), ∑ y, M x y = 1) → SGC.Bridge.TerminalDecoding.RowStochastic M`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.TerminalDecoding.Regression.erasing_full_tv_one`

- statement (kernel-elaborated, sha256 `9ffb743d42882a8a`):

      ∀ (m : ℕ), SGC.Bridge.TerminalDecoding.tv (Matrix.vecMul (SGC.Bridge.TerminalDecoding.Regression.point 0).mass (1 ^ m)) (Matrix.vecMul (SGC.Bridge.TerminalDecoding.Regression.point 1).mass (1 ^ m)) = 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Regression.point` (def, SGC.Bridge.TerminalDecoding): `Fin 2 → SGC.Bridge.TerminalDecoding.ProbabilityRow (Fin 2)`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`

### `SGC.Bridge.TerminalDecoding.Regression.erasing_no_both_below_half`

- statement (kernel-elaborated, sha256 `625c00709852dd82`):

      ∀ (d : SGC.Bridge.TerminalDecoding.Decoder SGC.Bridge.TerminalDecoding.Regression.erasePartition.Quot) (m : ℕ), ¬(d.error (SGC.Bridge.TerminalDecoding.actualLaw 1 SGC.Bridge.TerminalDecoding.Regression.erasePartition SGC.Bridge.TerminalDecoding.Regression.identity_stochastic (SGC.Bridge.TerminalDecoding.Regression.point 0) m) false < 1 / 2 ∧ d.error (SGC.Bridge.TerminalDecoding.actualLaw 1 SGC.Bridge.TerminalDecoding.Regression.erasePartition SGC.Bridge.TerminalDecoding.Regression.identity_stochastic (SGC.Bridge.TerminalDecoding.Regression.point 1) m) true < 1 / 2)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.Decoder` (inductive, SGC.Bridge.TerminalDecoding): `Type u_4 → Type u_4`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.TerminalDecoding.Regression.erasePartition` (def, SGC.Bridge.TerminalDecoding): `SGC.Partition (Fin 2)`
    - `SGC.Bridge.TerminalDecoding.Decoder.error` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.Decoder X → SGC.Bridge.TerminalDecoding.ProbabilityRow X → Bool → ℝ`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Bridge.TerminalDecoding.actualLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.TerminalDecoding.Regression.identity_stochastic` (theorem, SGC.Bridge.TerminalDecoding): `SGC.Renormalization.KernelHorizon.IsStochastic 1`
    - `SGC.Bridge.TerminalDecoding.Regression.point` (def, SGC.Bridge.TerminalDecoding): `Fin 2 → SGC.Bridge.TerminalDecoding.ProbabilityRow (Fin 2)`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.loss` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → SGC.Bridge.TerminalDecoding.Decoder X → Bool → X → ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.push` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [inst : Fintype X] → [inst_1 : Fintype Y] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → (M : Matrix X Y ℝ) → SGC.Bridge.TerminalDecoding.RowStochastic M → SGC.Bridge.TerminalDecoding.ProbabilityRow Y`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Renormalization.KernelHorizon.IsStochastic.mk` (ctor, SGC.Renormalization.KernelHorizon): `∀ {V : Type u_1} [inst : Fintype V] {T : Matrix V V ℝ}, (∀ (i j : V), 0 ≤ T i j) → (∀ (i : V), ∑ j, T i j = 1) → SGC.Renormalization.KernelHorizon.IsStochastic T`
    - `SGC.Bridge.TerminalDecoding.RowStochastic.nonneg` (theorem, SGC.Bridge.TerminalDecoding): `∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype Y] {M : Matrix X Y ℝ}, SGC.Bridge.TerminalDecoding.RowStochastic M → ∀ (x : X) (y : Y), 0 ≤ M x y`
    - `SGC.Bridge.TerminalDecoding.RowStochastic.one` (theorem, SGC.Bridge.TerminalDecoding): `∀ {X : Type u_1} [inst : Fintype X] [inst_1 : DecidableEq X], SGC.Bridge.TerminalDecoding.RowStochastic 1`
    - `SGC.Bridge.TerminalDecoding.RowStochastic.sum_one` (theorem, SGC.Bridge.TerminalDecoding): `∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype Y] {M : Matrix X Y ℝ}, SGC.Bridge.TerminalDecoding.RowStochastic M → ∀ (x : X), ∑ y, M x y = 1`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.Bridge.TerminalDecoding.Decoder.probOne` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → SGC.Bridge.TerminalDecoding.Decoder X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Bridge.TerminalDecoding.RowStochastic.mk` (ctor, SGC.Bridge.TerminalDecoding): `∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype Y] {M : Matrix X Y ℝ}, (∀ (x : X) (y : Y), 0 ≤ M x y) → (∀ (x : X), ∑ y, M x y = 1) → SGC.Bridge.TerminalDecoding.RowStochastic M`

### `SGC.Bridge.TerminalDecoding.Regression.erasing_observed_tv_zero`

- statement (kernel-elaborated, sha256 `9429c95503ab8cc9`):

      ∀ (m : ℕ), SGC.Bridge.TerminalDecoding.tv (SGC.Bridge.TerminalDecoding.actualLaw 1 SGC.Bridge.TerminalDecoding.Regression.erasePartition SGC.Bridge.TerminalDecoding.Regression.identity_stochastic (SGC.Bridge.TerminalDecoding.Regression.point 0) m).mass (SGC.Bridge.TerminalDecoding.actualLaw 1 SGC.Bridge.TerminalDecoding.Regression.erasePartition SGC.Bridge.TerminalDecoding.Regression.identity_stochastic (SGC.Bridge.TerminalDecoding.Regression.point 1) m).mass = 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.TerminalDecoding.Regression.erasePartition` (def, SGC.Bridge.TerminalDecoding): `SGC.Partition (Fin 2)`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.actualLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.TerminalDecoding.Regression.identity_stochastic` (theorem, SGC.Bridge.TerminalDecoding): `SGC.Renormalization.KernelHorizon.IsStochastic 1`
    - `SGC.Bridge.TerminalDecoding.Regression.point` (def, SGC.Bridge.TerminalDecoding): `Fin 2 → SGC.Bridge.TerminalDecoding.ProbabilityRow (Fin 2)`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.push` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [inst : Fintype X] → [inst_1 : Fintype Y] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → (M : Matrix X Y ℝ) → SGC.Bridge.TerminalDecoding.RowStochastic M → SGC.Bridge.TerminalDecoding.ProbabilityRow Y`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Renormalization.KernelHorizon.IsStochastic.mk` (ctor, SGC.Renormalization.KernelHorizon): `∀ {V : Type u_1} [inst : Fintype V] {T : Matrix V V ℝ}, (∀ (i j : V), 0 ≤ T i j) → (∀ (i : V), ∑ j, T i j = 1) → SGC.Renormalization.KernelHorizon.IsStochastic T`
    - `SGC.Bridge.TerminalDecoding.RowStochastic.nonneg` (theorem, SGC.Bridge.TerminalDecoding): `∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype Y] {M : Matrix X Y ℝ}, SGC.Bridge.TerminalDecoding.RowStochastic M → ∀ (x : X) (y : Y), 0 ≤ M x y`
    - `SGC.Bridge.TerminalDecoding.RowStochastic.one` (theorem, SGC.Bridge.TerminalDecoding): `∀ {X : Type u_1} [inst : Fintype X] [inst_1 : DecidableEq X], SGC.Bridge.TerminalDecoding.RowStochastic 1`
    - `SGC.Bridge.TerminalDecoding.RowStochastic.sum_one` (theorem, SGC.Bridge.TerminalDecoding): `∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype Y] {M : Matrix X Y ℝ}, SGC.Bridge.TerminalDecoding.RowStochastic M → ∀ (x : X), ∑ y, M x y = 1`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Bridge.TerminalDecoding.RowStochastic.mk` (ctor, SGC.Bridge.TerminalDecoding): `∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype Y] {M : Matrix X Y ℝ}, (∀ (x : X) (y : Y), 0 ≤ M x y) → (∀ (x : X), ∑ y, M x y = 1) → SGC.Bridge.TerminalDecoding.RowStochastic M`

### `SGC.Bridge.TerminalDecoding.Regression.erasing_threshold_equality`

- statement (kernel-elaborated, sha256 `390332ee8fe6a8be`):

      ∀ (p : SGC.Bridge.TerminalDecoding.ProbabilityRow SGC.Bridge.TerminalDecoding.Regression.erasePartition.Quot), SGC.Bridge.TerminalDecoding.tv p.mass p.mass = 0 ∧ SGC.Bridge.TerminalDecoding.Regression.erasingCoin.error p false = 1 / 2 ∧ SGC.Bridge.TerminalDecoding.Regression.erasingCoin.error p true = 1 / 2

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.TerminalDecoding.Regression.erasePartition` (def, SGC.Bridge.TerminalDecoding): `SGC.Partition (Fin 2)`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.error` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.Decoder X → SGC.Bridge.TerminalDecoding.ProbabilityRow X → Bool → ℝ`
    - `SGC.Bridge.TerminalDecoding.Regression.erasingCoin` (def, SGC.Bridge.TerminalDecoding): `SGC.Bridge.TerminalDecoding.Decoder SGC.Bridge.TerminalDecoding.Regression.erasePartition.Quot`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder` (inductive, SGC.Bridge.TerminalDecoding): `Type u_4 → Type u_4`
    - `SGC.Bridge.TerminalDecoding.Decoder.loss` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → SGC.Bridge.TerminalDecoding.Decoder X → Bool → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → (probOne : X → ℝ) → (∀ (x : X), probOne x ∈ Set.Icc 0 1) → SGC.Bridge.TerminalDecoding.Decoder X`
    - `SGC.Bridge.TerminalDecoding.Decoder.probOne` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → SGC.Bridge.TerminalDecoding.Decoder X → X → ℝ`

### `SGC.Bridge.TerminalDecoding.Regression.identity_stochastic`

- statement (kernel-elaborated, sha256 `e92864d4e3beccb7`):

      SGC.Renormalization.KernelHorizon.IsStochastic 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`

### `SGC.Bridge.TerminalDecoding.Regression.nonstationary_reference_exact`

- statement (kernel-elaborated, sha256 `ab0987f66aa5b325`):

      ∀ (rho : SGC.Bridge.TerminalDecoding.ProbabilityRow (Fin 2)) (m : ℕ), SGC.Bridge.TerminalDecoding.tv (SGC.Bridge.TerminalDecoding.actualLaw SGC.Bridge.TerminalDecoding.Regression.swap SGC.Bridge.TerminalDecoding.Regression.discretePartition SGC.Bridge.TerminalDecoding.Regression.swap_stochastic rho m).mass (SGC.Bridge.TerminalDecoding.referenceLaw SGC.Bridge.TerminalDecoding.Regression.swap SGC.Bridge.TerminalDecoding.Regression.discretePartition SGC.Bridge.TerminalDecoding.Regression.weights_positive SGC.Bridge.TerminalDecoding.Regression.swap_stochastic rho m).mass = 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.TerminalDecoding.Regression.discretePartition` (def, SGC.Bridge.TerminalDecoding): `SGC.Partition (Fin 2)`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.actualLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.TerminalDecoding.Regression.swap` (def, SGC.Bridge.TerminalDecoding): `Matrix (Fin 2) (Fin 2) ℝ`
    - `SGC.Bridge.TerminalDecoding.Regression.swap_stochastic` (theorem, SGC.Bridge.TerminalDecoding): `SGC.Renormalization.KernelHorizon.IsStochastic SGC.Bridge.TerminalDecoding.Regression.swap`
    - `SGC.Bridge.TerminalDecoding.referenceLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → {pi : X → ℝ} → (∀ (x : X), 0 < pi x) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.TerminalDecoding.Regression.weights` (def, SGC.Bridge.TerminalDecoding): `Fin 2 → ℝ`
    - `SGC.Bridge.TerminalDecoding.Regression.weights_positive` (theorem, SGC.Bridge.TerminalDecoding): `∀ (x : Fin 2), 0 < SGC.Bridge.TerminalDecoding.Regression.weights x`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.push` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [inst : Fintype X] → [inst_1 : Fintype Y] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → (M : Matrix X Y ℝ) → SGC.Bridge.TerminalDecoding.RowStochastic M → SGC.Bridge.TerminalDecoding.ProbabilityRow Y`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Renormalization.KernelHorizon.IsStochastic.mk` (ctor, SGC.Renormalization.KernelHorizon): `∀ {V : Type u_1} [inst : Fintype V] {T : Matrix V V ℝ}, (∀ (i j : V), 0 ≤ T i j) → (∀ (i : V), ∑ j, T i j = 1) → SGC.Renormalization.KernelHorizon.IsStochastic T`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.TerminalDecoding.Regression.point_half_tv`

- statement (kernel-elaborated, sha256 `900ffc7b0c5dd63b`):

      SGC.Bridge.TerminalDecoding.tv (SGC.Bridge.TerminalDecoding.Regression.point 0).mass SGC.Bridge.TerminalDecoding.Regression.half.mass = 1 / 2

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Regression.point` (def, SGC.Bridge.TerminalDecoding): `Fin 2 → SGC.Bridge.TerminalDecoding.ProbabilityRow (Fin 2)`
    - `SGC.Bridge.TerminalDecoding.Regression.half` (def, SGC.Bridge.TerminalDecoding): `SGC.Bridge.TerminalDecoding.ProbabilityRow (Fin 2)`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`

### `SGC.Bridge.TerminalDecoding.Regression.point_l1_normalization`

- statement (kernel-elaborated, sha256 `66d3b446b79d9bf9`):

      SGC.Bridge.TerminalDecoding.l1 ((SGC.Bridge.TerminalDecoding.Regression.point 0).mass - (SGC.Bridge.TerminalDecoding.Regression.point 1).mass) = 2

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Regression.point` (def, SGC.Bridge.TerminalDecoding): `Fin 2 → SGC.Bridge.TerminalDecoding.ProbabilityRow (Fin 2)`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`

### `SGC.Bridge.TerminalDecoding.Regression.point_tv_normalization`

- statement (kernel-elaborated, sha256 `f0d999969d0085ab`):

      SGC.Bridge.TerminalDecoding.tv (SGC.Bridge.TerminalDecoding.Regression.point 0).mass (SGC.Bridge.TerminalDecoding.Regression.point 1).mass = 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Regression.point` (def, SGC.Bridge.TerminalDecoding): `Fin 2 → SGC.Bridge.TerminalDecoding.ProbabilityRow (Fin 2)`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`

### `SGC.Bridge.TerminalDecoding.Regression.reset_dobrushin_zero`

- statement (kernel-elaborated, sha256 `a881de1bad2e7332`):

      SGC.Bridge.TerminalDecoding.dobrushin SGC.Bridge.TerminalDecoding.Regression.reset = 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.dobrushin` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.Regression.reset` (def, SGC.Bridge.TerminalDecoding): `Matrix (Fin 2) (Fin 2) ℝ`  [ignores x._@.SGC.Bridge.TerminalDecoding.738208583._hygCtx._hyg.28,x._@.SGC.Bridge.TerminalDecoding.738208583._hygCtx._hyg.30]
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowDifferences` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → Matrix X Y ℝ → Matrix (X × X) Y ℝ`

### `SGC.Bridge.TerminalDecoding.Regression.reset_forgets_both_inputs`

- statement (kernel-elaborated, sha256 `f8762d4933038890`):

      SGC.Bridge.TerminalDecoding.tv (Matrix.vecMul (SGC.Bridge.TerminalDecoding.Regression.point 0).mass SGC.Bridge.TerminalDecoding.Regression.reset) (Matrix.vecMul (SGC.Bridge.TerminalDecoding.Regression.point 1).mass SGC.Bridge.TerminalDecoding.Regression.reset) = 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Regression.point` (def, SGC.Bridge.TerminalDecoding): `Fin 2 → SGC.Bridge.TerminalDecoding.ProbabilityRow (Fin 2)`
    - `SGC.Bridge.TerminalDecoding.Regression.reset` (def, SGC.Bridge.TerminalDecoding): `Matrix (Fin 2) (Fin 2) ℝ`  [ignores x._@.SGC.Bridge.TerminalDecoding.738208583._hygCtx._hyg.28,x._@.SGC.Bridge.TerminalDecoding.738208583._hygCtx._hyg.30]
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`

### `SGC.Bridge.TerminalDecoding.Regression.reset_stochastic`

- statement (kernel-elaborated, sha256 `93beba1b86046782`):

      SGC.Bridge.TerminalDecoding.RowStochastic SGC.Bridge.TerminalDecoding.Regression.reset

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.Regression.reset` (def, SGC.Bridge.TerminalDecoding): `Matrix (Fin 2) (Fin 2) ℝ`  [ignores x._@.SGC.Bridge.TerminalDecoding.738208583._hygCtx._hyg.28,x._@.SGC.Bridge.TerminalDecoding.738208583._hygCtx._hyg.30]

### `SGC.Bridge.TerminalDecoding.Regression.swap_dobrushin_one`

- statement (kernel-elaborated, sha256 `121d88acf41140fa`):

      SGC.Bridge.TerminalDecoding.dobrushin SGC.Bridge.TerminalDecoding.Regression.swap = 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.dobrushin` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.Regression.swap` (def, SGC.Bridge.TerminalDecoding): `Matrix (Fin 2) (Fin 2) ℝ`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowDifferences` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → Matrix X Y ℝ → Matrix (X × X) Y ℝ`

### `SGC.Bridge.TerminalDecoding.Regression.swap_stochastic`

- statement (kernel-elaborated, sha256 `14ede41e6dbffcf3`):

      SGC.Renormalization.KernelHorizon.IsStochastic SGC.Bridge.TerminalDecoding.Regression.swap

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.Regression.swap` (def, SGC.Bridge.TerminalDecoding): `Matrix (Fin 2) (Fin 2) ℝ`

### `SGC.Bridge.TerminalDecoding.Regression.weights_not_normalized`

- statement (kernel-elaborated, sha256 `3d163c9ebdeed5b2`):

      ∑ x, SGC.Bridge.TerminalDecoding.Regression.weights x ≠ 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.Regression.weights` (def, SGC.Bridge.TerminalDecoding): `Fin 2 → ℝ`

### `SGC.Bridge.TerminalDecoding.Regression.weights_not_stationary`

- statement (kernel-elaborated, sha256 `ddb4377c7dcca190`):

      Matrix.vecMul SGC.Bridge.TerminalDecoding.Regression.weights SGC.Bridge.TerminalDecoding.Regression.swap ≠ SGC.Bridge.TerminalDecoding.Regression.weights

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.Regression.weights` (def, SGC.Bridge.TerminalDecoding): `Fin 2 → ℝ`
    - `SGC.Bridge.TerminalDecoding.Regression.swap` (def, SGC.Bridge.TerminalDecoding): `Matrix (Fin 2) (Fin 2) ℝ`

### `SGC.Bridge.TerminalDecoding.Regression.weights_positive`

- statement (kernel-elaborated, sha256 `86cbd442380f353a`):

      ∀ (x : Fin 2), 0 < SGC.Bridge.TerminalDecoding.Regression.weights x

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.Regression.weights` (def, SGC.Bridge.TerminalDecoding): `Fin 2 → ℝ`

### `SGC.Bridge.TerminalDecoding.RowStochastic.mul`

- statement (kernel-elaborated, sha256 `581efd935454cce5`):

      ∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst : Fintype Y] [inst_1 : Fintype Z] {M : Matrix X Y ℝ} {N : Matrix Y Z ℝ}, SGC.Bridge.TerminalDecoding.RowStochastic M → SGC.Bridge.TerminalDecoding.RowStochastic N → SGC.Bridge.TerminalDecoding.RowStochastic (M * N)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`

### `SGC.Bridge.TerminalDecoding.RowStochastic.nonneg`

- statement (kernel-elaborated, sha256 `af984a739e00b693`):

      ∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype Y] {M : Matrix X Y ℝ}, SGC.Bridge.TerminalDecoding.RowStochastic M → ∀ (x : X) (y : Y), 0 ≤ M x y

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`

### `SGC.Bridge.TerminalDecoding.RowStochastic.of_existing`

- statement (kernel-elaborated, sha256 `9875d56dd6cbca17`):

      ∀ {X : Type u_1} [inst : Fintype X] {M : Matrix X X ℝ}, SGC.Renormalization.KernelHorizon.IsStochastic M → SGC.Bridge.TerminalDecoding.RowStochastic M

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`

### `SGC.Bridge.TerminalDecoding.RowStochastic.one`

- statement (kernel-elaborated, sha256 `027bf2ade889ad42`):

      ∀ {X : Type u_1} [inst : Fintype X] [inst_1 : DecidableEq X], SGC.Bridge.TerminalDecoding.RowStochastic 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`

### `SGC.Bridge.TerminalDecoding.RowStochastic.pow`

- statement (kernel-elaborated, sha256 `6a282e02d5c0113d`):

      ∀ {X : Type u_1} [inst : Fintype X] [inst_1 : DecidableEq X] {M : Matrix X X ℝ}, SGC.Bridge.TerminalDecoding.RowStochastic M → ∀ (m : ℕ), SGC.Bridge.TerminalDecoding.RowStochastic (M ^ m)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`

### `SGC.Bridge.TerminalDecoding.RowStochastic.sum_one`

- statement (kernel-elaborated, sha256 `297f4ae7c776f05f`):

      ∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype Y] {M : Matrix X Y ℝ}, SGC.Bridge.TerminalDecoding.RowStochastic M → ∀ (x : X), ∑ y, M x y = 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`

### `SGC.Bridge.TerminalDecoding.abs_bounded_test_le_half_l1`

- statement (kernel-elaborated, sha256 `0813003dd01604c6`):

      ∀ {X : Type u_1} [inst : Fintype X] {v f : X → ℝ}, ∑ x, v x = 0 → (∀ (x : X), f x ∈ Set.Icc 0 1) → |∑ x, v x * f x| ≤ SGC.Bridge.TerminalDecoding.l1 v / 2

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`

### `SGC.Bridge.TerminalDecoding.abs_interval_test_le`

- statement (kernel-elaborated, sha256 `98ef36d2e7818b5b`):

      ∀ {X : Type u_1} [inst : Fintype X] {v f : X → ℝ}, ∑ x, v x = 0 → ∀ {a b : ℝ}, (∀ (x : X), f x ∈ Set.Icc a b) → |∑ x, v x * f x| ≤ SGC.Bridge.TerminalDecoding.l1 v * ((b - a) / 2)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`

### `SGC.Bridge.TerminalDecoding.actualLaw_alignment`

- statement (kernel-elaborated, sha256 `119e982544d0956d`):

      ∀ {X : Type u_1} [inst : Fintype X] [inst_1 : DecidableEq X] (T : Matrix X X ℝ) (P : SGC.Partition X) (hT : SGC.Renormalization.KernelHorizon.IsStochastic T) (rho : SGC.Bridge.TerminalDecoding.ProbabilityRow X) (m : ℕ), (rho.push (T ^ m) ⋯).push (SGC.lift_matrix P) ⋯ = SGC.Bridge.TerminalDecoding.actualLaw T P hT rho m

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.push` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [inst : Fintype X] → [inst_1 : Fintype Y] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → (M : Matrix X Y ℝ) → SGC.Bridge.TerminalDecoding.RowStochastic M → SGC.Bridge.TerminalDecoding.ProbabilityRow Y`
    - `SGC.Bridge.TerminalDecoding.RowStochastic.pow` (theorem, SGC.Bridge.TerminalDecoding): `∀ {X : Type u_1} [inst : Fintype X] [inst_1 : DecidableEq X] {M : Matrix X X ℝ}, SGC.Bridge.TerminalDecoding.RowStochastic M → ∀ (m : ℕ), SGC.Bridge.TerminalDecoding.RowStochastic (M ^ m)`
    - `SGC.Bridge.TerminalDecoding.RowStochastic.of_existing` (theorem, SGC.Bridge.TerminalDecoding): `∀ {X : Type u_1} [inst : Fintype X] {M : Matrix X X ℝ}, SGC.Renormalization.KernelHorizon.IsStochastic M → SGC.Bridge.TerminalDecoding.RowStochastic M`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.rowStochastic_lift` (theorem, SGC.Bridge.TerminalDecoding): `∀ {X : Type u_1} [inst : Fintype X] [inst_1 : DecidableEq X] (P : SGC.Partition X), SGC.Bridge.TerminalDecoding.RowStochastic (SGC.lift_matrix P)`
    - `SGC.Bridge.TerminalDecoding.actualLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.RowStochastic.one` (theorem, SGC.Bridge.TerminalDecoding): `∀ {X : Type u_1} [inst : Fintype X] [inst_1 : DecidableEq X], SGC.Bridge.TerminalDecoding.RowStochastic 1`
    - `SGC.Bridge.TerminalDecoding.RowStochastic.mul` (theorem, SGC.Bridge.TerminalDecoding): `∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst : Fintype Y] [inst_1 : Fintype Z] {M : Matrix X Y ℝ} {N : Matrix Y Z ℝ}, SGC.Bridge.TerminalDecoding.RowStochastic M → SGC.Bridge.TerminalDecoding.RowStochastic N → SGC.Bridge.TerminalDecoding.RowStochastic (M * N)`
    - `SGC.Bridge.TerminalDecoding.RowStochastic.mk` (ctor, SGC.Bridge.TerminalDecoding): `∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype Y] {M : Matrix X Y ℝ}, (∀ (x : X) (y : Y), 0 ≤ M x y) → (∀ (x : X), ∑ y, M x y = 1) → SGC.Bridge.TerminalDecoding.RowStochastic M`
    - `SGC.Renormalization.KernelHorizon.IsStochastic.nonneg` (theorem, SGC.Renormalization.KernelHorizon): `∀ {V : Type u_1} [inst : Fintype V] {T : Matrix V V ℝ}, SGC.Renormalization.KernelHorizon.IsStochastic T → ∀ (i j : V), 0 ≤ T i j`
    - `SGC.Renormalization.KernelHorizon.IsStochastic.row_sum_one` (theorem, SGC.Renormalization.KernelHorizon): `∀ {V : Type u_1} [inst : Fintype V] {T : Matrix V V ℝ}, SGC.Renormalization.KernelHorizon.IsStochastic T → ∀ (i : V), ∑ j, T i j = 1`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Bridge.TerminalDecoding.RowStochastic.nonneg` (theorem, SGC.Bridge.TerminalDecoding): `∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype Y] {M : Matrix X Y ℝ}, SGC.Bridge.TerminalDecoding.RowStochastic M → ∀ (x : X) (y : Y), 0 ≤ M x y`
    - `SGC.Bridge.TerminalDecoding.RowStochastic.sum_one` (theorem, SGC.Bridge.TerminalDecoding): `∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype Y] {M : Matrix X Y ℝ}, SGC.Bridge.TerminalDecoding.RowStochastic M → ∀ (x : X), ∑ y, M x y = 1`

### `SGC.Bridge.TerminalDecoding.bounded_test_tv`

- statement (kernel-elaborated, sha256 `7455a34cc518fc17`):

      ∀ {X : Type u_1} [inst : Fintype X] (p q : SGC.Bridge.TerminalDecoding.ProbabilityRow X) {f : X → ℝ}, (∀ (x : X), f x ∈ Set.Icc 0 1) → |∑ x, p.mass x * f x - ∑ x, q.mass x * f x| ≤ SGC.Bridge.TerminalDecoding.tv p.mass q.mass

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`

### `SGC.Bridge.TerminalDecoding.class_terminal_budget_exact`

- statement (kernel-elaborated, sha256 `437728770f320cc9`):

      ∀ {X : Type u_1} [inst : Fintype X] [inst_1 : DecidableEq X] (T : Matrix X X ℝ) (P : SGC.Partition X) {pi : X → ℝ} (hpi : ∀ (x : X), 0 < pi x) (hT : SGC.Renormalization.KernelHorizon.IsStochastic T) (rho : SGC.Bridge.TerminalDecoding.ProbabilityRow X) (m : ℕ), SGC.Bridge.TerminalDecoding.tv (SGC.Bridge.TerminalDecoding.actualLaw T P hT rho m).mass (SGC.Bridge.TerminalDecoding.referenceLaw T P hpi hT rho m).mass = SGC.Bridge.TerminalDecoding.classTerminalBudget T P pi rho m

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.actualLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.TerminalDecoding.referenceLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → {pi : X → ℝ} → (∀ (x : X), 0 < pi x) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.TerminalDecoding.classTerminalBudget` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → Matrix X X ℝ → SGC.Partition X → (X → ℝ) → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → ℝ`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.push` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [inst : Fintype X] → [inst_1 : Fintype Y] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → (M : Matrix X Y ℝ) → SGC.Bridge.TerminalDecoding.RowStochastic M → SGC.Bridge.TerminalDecoding.ProbabilityRow Y`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.terminalError` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → [inst : DecidableEq X] → Matrix X X ℝ → (P : SGC.Partition X) → (X → ℝ) → ℕ → Matrix X P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.TerminalDecoding.closureCommutator_row_sum_zero`

- statement (kernel-elaborated, sha256 `93f29059413e7086`):

      ∀ {X : Type u_1} [inst : Fintype X] [inst_1 : DecidableEq X] (T : Matrix X X ℝ) (P : SGC.Partition X) {pi : X → ℝ}, (∀ (x : X), 0 < pi x) → SGC.Renormalization.KernelHorizon.IsStochastic T → ∀ (x : X), ∑ y, SGC.Renormalization.MeasureReentry.closureCommutator T P pi x y = 0

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
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.TerminalDecoding.decoder_error_sum_lower`

- statement (kernel-elaborated, sha256 `b92797bcca3e1439`):

      ∀ {X : Type u_1} [inst : Fintype X] (d : SGC.Bridge.TerminalDecoding.Decoder X) (p q : SGC.Bridge.TerminalDecoding.ProbabilityRow X), 1 - SGC.Bridge.TerminalDecoding.tv p.mass q.mass ≤ d.error p false + d.error q true

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.Decoder` (inductive, SGC.Bridge.TerminalDecoding): `Type u_4 → Type u_4`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.error` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.Decoder X → SGC.Bridge.TerminalDecoding.ProbabilityRow X → Bool → ℝ`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.loss` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → SGC.Bridge.TerminalDecoding.Decoder X → Bool → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.probOne` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → SGC.Bridge.TerminalDecoding.Decoder X → X → ℝ`

### `SGC.Bridge.TerminalDecoding.deterministic_error_eq`

- statement (kernel-elaborated, sha256 `3a4f935eaaf22e9b`):

      ∀ {X : Type u_1} [inst : Fintype X] (d : X → Bool) (p : SGC.Bridge.TerminalDecoding.ProbabilityRow X) (b : Bool), (SGC.Bridge.TerminalDecoding.deterministicDecoder d).error p b = ∑ x, if d x = b then 0 else p.mass x

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.Decoder.error` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.Decoder X → SGC.Bridge.TerminalDecoding.ProbabilityRow X → Bool → ℝ`
    - `SGC.Bridge.TerminalDecoding.deterministicDecoder` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → (X → Bool) → SGC.Bridge.TerminalDecoding.Decoder X`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder` (inductive, SGC.Bridge.TerminalDecoding): `Type u_4 → Type u_4`
    - `SGC.Bridge.TerminalDecoding.Decoder.loss` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → SGC.Bridge.TerminalDecoding.Decoder X → Bool → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → (probOne : X → ℝ) → (∀ (x : X), probOne x ∈ Set.Icc 0 1) → SGC.Bridge.TerminalDecoding.Decoder X`
    - `SGC.Bridge.TerminalDecoding.Decoder.probOne` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → SGC.Bridge.TerminalDecoding.Decoder X → X → ℝ`

### `SGC.Bridge.TerminalDecoding.dobrushin_le_one`

- statement (kernel-elaborated, sha256 `3895b7afe417b1c7`):

      ∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype X] [inst_1 : Fintype Y] {M : Matrix X Y ℝ}, SGC.Bridge.TerminalDecoding.RowStochastic M → SGC.Bridge.TerminalDecoding.dobrushin M ≤ 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.dobrushin` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowDifferences` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → Matrix X Y ℝ → Matrix (X × X) Y ℝ`

### `SGC.Bridge.TerminalDecoding.dobrushin_nonneg`

- statement (kernel-elaborated, sha256 `723faa79b6f462b7`):

      ∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype X] [inst_1 : Fintype Y] (M : Matrix X Y ℝ), 0 ≤ SGC.Bridge.TerminalDecoding.dobrushin M

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.dobrushin` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowDifferences` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → Matrix X Y ℝ → Matrix (X × X) Y ℝ`

### `SGC.Bridge.TerminalDecoding.exact_terminal_budget_le`

- statement (kernel-elaborated, sha256 `2179184a98e8a8e3`):

      ∀ {X : Type u_1} [inst : Fintype X] [inst_1 : DecidableEq X] (T : Matrix X X ℝ) (P : SGC.Partition X) {pi : X → ℝ}, (∀ (x : X), 0 < pi x) → SGC.Renormalization.KernelHorizon.IsStochastic T → ∀ (m : ℕ), SGC.Bridge.TerminalDecoding.exactTerminalBudget T P pi m ≤ SGC.Bridge.TerminalDecoding.terminalBudget T P pi m

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.exactTerminalBudget` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → [inst : DecidableEq X] → Matrix X X ℝ → SGC.Partition X → (X → ℝ) → ℕ → ℝ`
    - `SGC.Bridge.TerminalDecoding.terminalBudget` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → [inst : DecidableEq X] → Matrix X X ℝ → SGC.Partition X → (X → ℝ) → ℕ → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Bridge.TerminalDecoding.terminalError` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → [inst : DecidableEq X] → Matrix X X ℝ → (P : SGC.Partition X) → (X → ℝ) → ℕ → Matrix X P.Quot ℝ`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.TerminalDecoding.fixed_decoder_error_transfer`

- statement (kernel-elaborated, sha256 `c6caadf18ac17baf`):

      ∀ {X : Type u_1} [inst : Fintype X] (d : SGC.Bridge.TerminalDecoding.Decoder X) (a r : SGC.Bridge.TerminalDecoding.ProbabilityRow X) (b : Bool), |d.error a b - d.error r b| ≤ SGC.Bridge.TerminalDecoding.tv a.mass r.mass

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.Decoder` (inductive, SGC.Bridge.TerminalDecoding): `Type u_4 → Type u_4`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.Decoder.error` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.Decoder X → SGC.Bridge.TerminalDecoding.ProbabilityRow X → Bool → ℝ`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.loss` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → SGC.Bridge.TerminalDecoding.Decoder X → Bool → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.probOne` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → SGC.Bridge.TerminalDecoding.Decoder X → X → ℝ`

### `SGC.Bridge.TerminalDecoding.iterated_tv_contraction`

- statement (kernel-elaborated, sha256 `c61c98861abe4fdc`):

      ∀ {W : ℕ → Type u_4} [inst : (j : ℕ) → Fintype (W j)] (laws : (j : ℕ) → Bool → SGC.Bridge.TerminalDecoding.ProbabilityRow (W j)) (K : (j : ℕ) → Matrix (W j) (W (j + 1)) ℝ) (hK : ∀ (j : ℕ), SGC.Bridge.TerminalDecoding.RowStochastic (K j)), (∀ (j : ℕ) (b : Bool), (laws j b).push (K j) ⋯ = laws (j + 1) b) → ∀ (theta : ℕ → ↑(Set.Icc 0 1)), (∀ (j : ℕ), SGC.Bridge.TerminalDecoding.tv ((laws j false).push (K j) ⋯).mass ((laws j true).push (K j) ⋯).mass ≤ ↑(theta j) * SGC.Bridge.TerminalDecoding.tv (laws j false).mass (laws j true).mass) → ∀ (m : ℕ), SGC.Bridge.TerminalDecoding.tv (laws m false).mass (laws m true).mass ≤ SGC.Bridge.TerminalDecoding.tv (laws 0 false).mass (laws 0 true).mass * ∏ j ∈ Finset.range m, ↑(theta j)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.push` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [inst : Fintype X] → [inst_1 : Fintype Y] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → (M : Matrix X Y ℝ) → SGC.Bridge.TerminalDecoding.RowStochastic M → SGC.Bridge.TerminalDecoding.ProbabilityRow Y`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`

### `SGC.Bridge.TerminalDecoding.joint_terminal_certificate`

- statement (kernel-elaborated, sha256 `2435884112758cc6`):

      ∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype X] [inst_1 : Fintype Y] (a r : Bool → SGC.Bridge.TerminalDecoding.ProbabilityRow Y) (full : Bool → SGC.Bridge.TerminalDecoding.ProbabilityRow X) (O : Matrix X Y ℝ) (hO : SGC.Bridge.TerminalDecoding.RowStochastic O), (∀ (b : Bool), (full b).push O hO = a b) → ∀ (epsilon : Bool → ℝ), (∀ (b : Bool), SGC.Bridge.TerminalDecoding.tv (a b).mass (r b).mass ≤ epsilon b) → ∀ {U : ℝ}, SGC.Bridge.TerminalDecoding.tv (full false).mass (full true).mass ≤ U → max 0 (SGC.Bridge.TerminalDecoding.tv (r false).mass (r true).mass - (epsilon false + epsilon true)) ≤ SGC.Bridge.TerminalDecoding.tv (a false).mass (a true).mass ∧ SGC.Bridge.TerminalDecoding.tv (a false).mass (a true).mass ≤ min (SGC.Bridge.TerminalDecoding.tv (r false).mass (r true).mass + epsilon false + epsilon true) U ∧ SGC.Bridge.TerminalDecoding.tv (a false).mass (a true).mass ≤ SGC.Bridge.TerminalDecoding.tv (full false).mass (full true).mass ∧ SGC.Bridge.TerminalDecoding.tv (full false).mass (full true).mass ≤ U

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.push` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [inst : Fintype X] → [inst_1 : Fintype Y] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → (M : Matrix X Y ℝ) → SGC.Bridge.TerminalDecoding.RowStochastic M → SGC.Bridge.TerminalDecoding.ProbabilityRow Y`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`

### `SGC.Bridge.TerminalDecoding.kernel_error_dobrushin`

- statement (kernel-elaborated, sha256 `0549dd060dfbcec3`):

      ∀ {X : Type u_1} [inst : Fintype X] [inst_1 : DecidableEq X] (T : Matrix X X ℝ) (P : SGC.Partition X) {pi : X → ℝ}, (∀ (x : X), 0 < pi x) → SGC.Renormalization.KernelHorizon.IsStochastic T → ∀ (m : ℕ), SGC.Bridge.TerminalDecoding.rowL1Norm (SGC.Bridge.TerminalDecoding.terminalError T P pi m) ≤ (∑ j ∈ Finset.range m, SGC.Bridge.TerminalDecoding.dobrushin (SGC.Thermodynamics.CoarseGenerator T P pi) ^ j) * SGC.Bridge.TerminalDecoding.rowL1Norm (SGC.Renormalization.MeasureReentry.closureCommutator T P pi)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Bridge.TerminalDecoding.terminalError` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → [inst : DecidableEq X] → Matrix X X ℝ → (P : SGC.Partition X) → (X → ℝ) → ℕ → Matrix X P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.dobrushin` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Bridge.TerminalDecoding.rowDifferences` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → Matrix X Y ℝ → Matrix (X × X) Y ℝ`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.TerminalDecoding.kernel_fixed_decoder_error_transfer`

- statement (kernel-elaborated, sha256 `b3326a921dca7855`):

      ∀ {X : Type u_1} [inst : Fintype X] [inst_1 : DecidableEq X] (T : Matrix X X ℝ) (P : SGC.Partition X) {pi : X → ℝ} (hpi : ∀ (x : X), 0 < pi x) (hT : SGC.Renormalization.KernelHorizon.IsStochastic T) (rho : SGC.Bridge.TerminalDecoding.ProbabilityRow X) (d : SGC.Bridge.TerminalDecoding.Decoder P.Quot) (b : Bool) (m : ℕ), |d.error (SGC.Bridge.TerminalDecoding.actualLaw T P hT rho m) b - d.error (SGC.Bridge.TerminalDecoding.referenceLaw T P hpi hT rho m) b| ≤ SGC.Bridge.TerminalDecoding.terminalBudget T P pi m

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.Decoder` (inductive, SGC.Bridge.TerminalDecoding): `Type u_4 → Type u_4`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.TerminalDecoding.Decoder.error` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.Decoder X → SGC.Bridge.TerminalDecoding.ProbabilityRow X → Bool → ℝ`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Bridge.TerminalDecoding.actualLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.TerminalDecoding.referenceLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → {pi : X → ℝ} → (∀ (x : X), 0 < pi x) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.TerminalDecoding.terminalBudget` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → [inst : DecidableEq X] → Matrix X X ℝ → SGC.Partition X → (X → ℝ) → ℕ → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.loss` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → SGC.Bridge.TerminalDecoding.Decoder X → Bool → X → ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.push` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [inst : Fintype X] → [inst_1 : Fintype Y] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → (M : Matrix X Y ℝ) → SGC.Bridge.TerminalDecoding.RowStochastic M → SGC.Bridge.TerminalDecoding.ProbabilityRow Y`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.probOne` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → SGC.Bridge.TerminalDecoding.Decoder X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.TerminalDecoding.kernel_horizon_tv`

- statement (kernel-elaborated, sha256 `d4dc28bcf3d59a49`):

      ∀ {X : Type u_1} [inst : Fintype X] [inst_1 : DecidableEq X] (T : Matrix X X ℝ) (P : SGC.Partition X) {pi : X → ℝ} (hpi : ∀ (x : X), 0 < pi x) (hT : SGC.Renormalization.KernelHorizon.IsStochastic T) (rho : SGC.Bridge.TerminalDecoding.ProbabilityRow X) (m : ℕ), SGC.Bridge.TerminalDecoding.tv (SGC.Bridge.TerminalDecoding.actualLaw T P hT rho m).mass (SGC.Bridge.TerminalDecoding.referenceLaw T P hpi hT rho m).mass ≤ SGC.Bridge.TerminalDecoding.terminalBudget T P pi m

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.actualLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.TerminalDecoding.referenceLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → {pi : X → ℝ} → (∀ (x : X), 0 < pi x) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.TerminalDecoding.terminalBudget` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → [inst : DecidableEq X] → Matrix X X ℝ → SGC.Partition X → (X → ℝ) → ℕ → ℝ`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.push` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [inst : Fintype X] → [inst_1 : Fintype Y] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → (M : Matrix X Y ℝ) → SGC.Bridge.TerminalDecoding.RowStochastic M → SGC.Bridge.TerminalDecoding.ProbabilityRow Y`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.TerminalDecoding.kernel_horizon_tv_mixing`

- statement (kernel-elaborated, sha256 `2102ae627707137b`):

      ∀ {X : Type u_1} [inst : Fintype X] [inst_1 : DecidableEq X] (T : Matrix X X ℝ) (P : SGC.Partition X) {pi : X → ℝ} (hpi : ∀ (x : X), 0 < pi x) (hT : SGC.Renormalization.KernelHorizon.IsStochastic T) (rho : SGC.Bridge.TerminalDecoding.ProbabilityRow X) (m : ℕ), SGC.Bridge.TerminalDecoding.tv (SGC.Bridge.TerminalDecoding.actualLaw T P hT rho m).mass (SGC.Bridge.TerminalDecoding.referenceLaw T P hpi hT rho m).mass ≤ SGC.Bridge.TerminalDecoding.mixingBudget T P pi m

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.actualLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.TerminalDecoding.referenceLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → {pi : X → ℝ} → (∀ (x : X), 0 < pi x) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.TerminalDecoding.mixingBudget` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → [inst : DecidableEq X] → Matrix X X ℝ → SGC.Partition X → (X → ℝ) → ℕ → ℝ`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.push` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [inst : Fintype X] → [inst_1 : Fintype Y] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → (M : Matrix X Y ℝ) → SGC.Bridge.TerminalDecoding.RowStochastic M → SGC.Bridge.TerminalDecoding.ProbabilityRow Y`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.dobrushin` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowDifferences` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → Matrix X Y ℝ → Matrix (X × X) Y ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.TerminalDecoding.kernel_horizon_tv_sharp`

- statement (kernel-elaborated, sha256 `1db9271b5883b317`):

      ∀ {X : Type u_1} [inst : Fintype X] [inst_1 : DecidableEq X] (T : Matrix X X ℝ) (P : SGC.Partition X) {pi : X → ℝ} (hpi : ∀ (x : X), 0 < pi x) (hT : SGC.Renormalization.KernelHorizon.IsStochastic T) (rho : SGC.Bridge.TerminalDecoding.ProbabilityRow X) (m : ℕ), SGC.Bridge.TerminalDecoding.tv (SGC.Bridge.TerminalDecoding.actualLaw T P hT rho m).mass (SGC.Bridge.TerminalDecoding.referenceLaw T P hpi hT rho m).mass ≤ SGC.Bridge.TerminalDecoding.exactTerminalBudget T P pi m

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.actualLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.TerminalDecoding.referenceLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → {pi : X → ℝ} → (∀ (x : X), 0 < pi x) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.TerminalDecoding.exactTerminalBudget` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → [inst : DecidableEq X] → Matrix X X ℝ → SGC.Partition X → (X → ℝ) → ℕ → ℝ`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.push` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [inst : Fintype X] → [inst_1 : Fintype Y] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → (M : Matrix X Y ℝ) → SGC.Bridge.TerminalDecoding.RowStochastic M → SGC.Bridge.TerminalDecoding.ProbabilityRow Y`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.terminalError` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → [inst : DecidableEq X] → Matrix X X ℝ → (P : SGC.Partition X) → (X → ℝ) → ℕ → Matrix X P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.TerminalDecoding.kernel_horizon_tv_uniform_mixing`

- statement (kernel-elaborated, sha256 `be04d6fbeb45db9a`):

      ∀ {X : Type u_1} [inst : Fintype X] [inst_1 : DecidableEq X] (T : Matrix X X ℝ) (P : SGC.Partition X) {pi : X → ℝ} (hpi : ∀ (x : X), 0 < pi x) (hT : SGC.Renormalization.KernelHorizon.IsStochastic T) (rho : SGC.Bridge.TerminalDecoding.ProbabilityRow X), SGC.Bridge.TerminalDecoding.dobrushin (SGC.Thermodynamics.CoarseGenerator T P pi) < 1 → ∀ (m : ℕ), SGC.Bridge.TerminalDecoding.tv (SGC.Bridge.TerminalDecoding.actualLaw T P hT rho m).mass (SGC.Bridge.TerminalDecoding.referenceLaw T P hpi hT rho m).mass ≤ min 1 (SGC.Bridge.TerminalDecoding.rowL1Norm (SGC.Renormalization.MeasureReentry.closureCommutator T P pi) / (2 * (1 - SGC.Bridge.TerminalDecoding.dobrushin (SGC.Thermodynamics.CoarseGenerator T P pi))))

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.dobrushin` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.actualLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.TerminalDecoding.referenceLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → {pi : X → ℝ} → (∀ (x : X), 0 < pi x) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.rowDifferences` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → Matrix X Y ℝ → Matrix (X × X) Y ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.push` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [inst : Fintype X] → [inst_1 : Fintype Y] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → (M : Matrix X Y ℝ) → SGC.Bridge.TerminalDecoding.RowStochastic M → SGC.Bridge.TerminalDecoding.ProbabilityRow Y`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`

### `SGC.Bridge.TerminalDecoding.kernel_horizon_tv_zero`

- statement (kernel-elaborated, sha256 `a26fa557d89d49b5`):

      ∀ {X : Type u_1} [inst : Fintype X] [inst_1 : DecidableEq X] (T : Matrix X X ℝ) (P : SGC.Partition X) {pi : X → ℝ} (hpi : ∀ (x : X), 0 < pi x) (hT : SGC.Renormalization.KernelHorizon.IsStochastic T) (rho : SGC.Bridge.TerminalDecoding.ProbabilityRow X), SGC.Bridge.TerminalDecoding.tv (SGC.Bridge.TerminalDecoding.actualLaw T P hT rho 0).mass (SGC.Bridge.TerminalDecoding.referenceLaw T P hpi hT rho 0).mass = 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.actualLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.TerminalDecoding.referenceLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → {pi : X → ℝ} → (∀ (x : X), 0 < pi x) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.push` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [inst : Fintype X] → [inst_1 : Fintype Y] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → (M : Matrix X Y ℝ) → SGC.Bridge.TerminalDecoding.RowStochastic M → SGC.Bridge.TerminalDecoding.ProbabilityRow Y`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.TerminalDecoding.kernel_joint_terminal_certificate`

- statement (kernel-elaborated, sha256 `f76bda02aaebd0e3`):

      ∀ {X : Type u_1} [inst : Fintype X] [inst_1 : DecidableEq X] (T : Matrix X X ℝ) (P : SGC.Partition X) {pi : X → ℝ} (hpi : ∀ (x : X), 0 < pi x) (hT : SGC.Renormalization.KernelHorizon.IsStochastic T) (mu : Bool → SGC.Bridge.TerminalDecoding.ProbabilityRow X) (m : ℕ) (Gamma : ↑(Set.Icc 0 1)),   SGC.Bridge.TerminalDecoding.tv (Matrix.vecMul (mu false).mass (T ^ m)) (Matrix.vecMul (mu true).mass (T ^ m)) ≤ ↑Gamma * SGC.Bridge.TerminalDecoding.tv (mu false).mass (mu true).mass →     have a := fun b => SGC.Bridge.TerminalDecoding.actualLaw T P hT (mu b) m;     have r := fun b => SGC.Bridge.TerminalDecoding.referenceLaw T P hpi hT (mu b) m;     max 0 (SGC.Bridge.TerminalDecoding.tv (r false).mass (r true).mass - 2 * SGC.Bridge.TerminalDecoding.exactTerminalBudget T P pi m) ≤ SGC.Bridge.TerminalDecoding.tv (a false).mass (a true).mass ∧ SGC.Bridge.TerminalDecoding.tv (a false).mass (a true).mass ≤ SGC.Bridge.TerminalDecoding.tv (Matrix.vecMul (mu false).mass (T ^ m)) (Matrix.vecMul (mu true).mass (T ^ m)) ∧ SGC.Bridge.TerminalDecoding.tv (Matrix.vecMul (mu false).mass (T ^ m)) (Matrix.vecMul (mu true).mass (T ^ m)) ≤ ↑Gamma * SGC.Bridge.TerminalDecoding.tv (mu false).mass (mu true).mass

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Bridge.TerminalDecoding.actualLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.TerminalDecoding.referenceLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → {pi : X → ℝ} → (∀ (x : X), 0 < pi x) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.TerminalDecoding.exactTerminalBudget` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → [inst : DecidableEq X] → Matrix X X ℝ → SGC.Partition X → (X → ℝ) → ℕ → ℝ`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.push` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [inst : Fintype X] → [inst_1 : Fintype Y] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → (M : Matrix X Y ℝ) → SGC.Bridge.TerminalDecoding.RowStochastic M → SGC.Bridge.TerminalDecoding.ProbabilityRow Y`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.terminalError` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → [inst : DecidableEq X] → Matrix X X ℝ → (P : SGC.Partition X) → (X → ℝ) → ℕ → Matrix X P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.TerminalDecoding.kernel_terminal_reliability`

- statement (kernel-elaborated, sha256 `b20aba5a82424d4d`):

      ∀ {X : Type u_1} [inst : Fintype X] [inst_1 : DecidableEq X] (T : Matrix X X ℝ) (P : SGC.Partition X) {pi : X → ℝ} (hpi : ∀ (x : X), 0 < pi x) (hT : SGC.Renormalization.KernelHorizon.IsStochastic T) (mu : Bool → SGC.Bridge.TerminalDecoding.ProbabilityRow X) (d : SGC.Bridge.TerminalDecoding.Decoder P.Quot) (beta p : Bool → ↑(Set.Icc 0 1)) (m : ℕ), (∀ (b : Bool), d.error (SGC.Bridge.TerminalDecoding.referenceLaw T P hpi hT (mu b) m) b ≤ ↑(beta b)) → (∀ (b : Bool), ↑(beta b) + SGC.Bridge.TerminalDecoding.terminalBudget T P pi m ≤ ↑(p b)) → ∀ (b : Bool), d.error (SGC.Bridge.TerminalDecoding.actualLaw T P hT (mu b) m) b ≤ ↑(p b)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.Decoder` (inductive, SGC.Bridge.TerminalDecoding): `Type u_4 → Type u_4`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.TerminalDecoding.Decoder.error` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.Decoder X → SGC.Bridge.TerminalDecoding.ProbabilityRow X → Bool → ℝ`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Bridge.TerminalDecoding.referenceLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → {pi : X → ℝ} → (∀ (x : X), 0 < pi x) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.TerminalDecoding.terminalBudget` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → [inst : DecidableEq X] → Matrix X X ℝ → SGC.Partition X → (X → ℝ) → ℕ → ℝ`
    - `SGC.Bridge.TerminalDecoding.actualLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.loss` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → SGC.Bridge.TerminalDecoding.Decoder X → Bool → X → ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.push` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [inst : Fintype X] → [inst_1 : Fintype Y] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → (M : Matrix X Y ℝ) → SGC.Bridge.TerminalDecoding.RowStochastic M → SGC.Bridge.TerminalDecoding.ProbabilityRow Y`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.probOne` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → SGC.Bridge.TerminalDecoding.Decoder X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.TerminalDecoding.l1_nonneg`

- statement (kernel-elaborated, sha256 `9a77d41357fea64b`):

      ∀ {X : Type u_1} [inst : Fintype X] (v : X → ℝ), 0 ≤ SGC.Bridge.TerminalDecoding.l1 v

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`

### `SGC.Bridge.TerminalDecoding.l1_vecMul_le`

- statement (kernel-elaborated, sha256 `9e3de81450a0f147`):

      ∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype X] [inst_1 : Fintype Y] {M : Matrix X Y ℝ}, SGC.Bridge.TerminalDecoding.RowStochastic M → ∀ (v : X → ℝ), SGC.Bridge.TerminalDecoding.l1 (Matrix.vecMul v M) ≤ SGC.Bridge.TerminalDecoding.l1 v

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`

### `SGC.Bridge.TerminalDecoding.mixing_budget_le_terminal`

- statement (kernel-elaborated, sha256 `f486c2314e4f3c1a`):

      ∀ {X : Type u_1} [inst : Fintype X] [inst_1 : DecidableEq X] (T : Matrix X X ℝ) (P : SGC.Partition X) {pi : X → ℝ}, (∀ (x : X), 0 < pi x) → SGC.Renormalization.KernelHorizon.IsStochastic T → ∀ (m : ℕ), SGC.Bridge.TerminalDecoding.mixingBudget T P pi m ≤ SGC.Bridge.TerminalDecoding.terminalBudget T P pi m

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.mixingBudget` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → [inst : DecidableEq X] → Matrix X X ℝ → SGC.Partition X → (X → ℝ) → ℕ → ℝ`
    - `SGC.Bridge.TerminalDecoding.terminalBudget` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → [inst : DecidableEq X] → Matrix X X ℝ → SGC.Partition X → (X → ℝ) → ℕ → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.dobrushin` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.rowDifferences` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → Matrix X Y ℝ → Matrix (X × X) Y ℝ`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.TerminalDecoding.no_terminal_decoder_of_contraction`

- statement (kernel-elaborated, sha256 `730b92dd45f68f95`):

      ∀ {X : Type u_1} [inst : Fintype X] (full : Bool → SGC.Bridge.TerminalDecoding.ProbabilityRow X) (p : Bool → ↑(Set.Icc 0 1)) {U : ℝ}, SGC.Bridge.TerminalDecoding.tv (full false).mass (full true).mass ≤ U → U < 1 - ↑(p false) - ↑(p true) → ∀ (d : SGC.Bridge.TerminalDecoding.Decoder X), ↑(p false) < d.error (full false) false ∨ ↑(p true) < d.error (full true) true

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder` (inductive, SGC.Bridge.TerminalDecoding): `Type u_4 → Type u_4`
    - `SGC.Bridge.TerminalDecoding.Decoder.error` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.Decoder X → SGC.Bridge.TerminalDecoding.ProbabilityRow X → Bool → ℝ`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.loss` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → SGC.Bridge.TerminalDecoding.Decoder X → Bool → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.probOne` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → SGC.Bridge.TerminalDecoding.Decoder X → X → ℝ`

### `SGC.Bridge.TerminalDecoding.observed_distinguishability_lower`

- statement (kernel-elaborated, sha256 `cbe73ca1fa113220`):

      ∀ {X : Type u_1} [inst : Fintype X] (a r : Bool → SGC.Bridge.TerminalDecoding.ProbabilityRow X) (epsilon : Bool → ℝ), (∀ (b : Bool), SGC.Bridge.TerminalDecoding.tv (a b).mass (r b).mass ≤ epsilon b) → max 0 (SGC.Bridge.TerminalDecoding.tv (r false).mass (r true).mass - (epsilon false + epsilon true)) ≤ SGC.Bridge.TerminalDecoding.tv (a false).mass (a true).mass

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`

### `SGC.Bridge.TerminalDecoding.observed_distinguishability_two_sided`

- statement (kernel-elaborated, sha256 `fc646835622d6fd0`):

      ∀ {X : Type u_1} [inst : Fintype X] (a r : Bool → SGC.Bridge.TerminalDecoding.ProbabilityRow X) (epsilon : Bool → ℝ), (∀ (b : Bool), SGC.Bridge.TerminalDecoding.tv (a b).mass (r b).mass ≤ epsilon b) → |SGC.Bridge.TerminalDecoding.tv (a false).mass (a true).mass - SGC.Bridge.TerminalDecoding.tv (r false).mass (r true).mass| ≤ epsilon false + epsilon true

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`

### `SGC.Bridge.TerminalDecoding.prob_vecMul_row_l1_le`

- statement (kernel-elaborated, sha256 `c7c812e6600ac40f`):

      ∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype X] [inst_1 : Fintype Y] (p : SGC.Bridge.TerminalDecoding.ProbabilityRow X) (M : Matrix X Y ℝ), SGC.Bridge.TerminalDecoding.l1 (Matrix.vecMul p.mass M) ≤ SGC.Bridge.TerminalDecoding.rowL1Norm M

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`

### `SGC.Bridge.TerminalDecoding.reference_contraction_compatibility`

- statement (kernel-elaborated, sha256 `ee0e57f9e1a44410`):

      ∀ {X : Type u_1} [inst : Fintype X] (a r : Bool → SGC.Bridge.TerminalDecoding.ProbabilityRow X) (epsilon : Bool → ℝ), (∀ (b : Bool), SGC.Bridge.TerminalDecoding.tv (a b).mass (r b).mass ≤ epsilon b) → ∀ {U : ℝ}, SGC.Bridge.TerminalDecoding.tv (a false).mass (a true).mass ≤ U → SGC.Bridge.TerminalDecoding.tv (r false).mass (r true).mass ≤ U + epsilon false + epsilon true

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`

### `SGC.Bridge.TerminalDecoding.rowL1Norm_le`

- statement (kernel-elaborated, sha256 `8019558b83516319`):

      ∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype X] [inst_1 : Fintype Y] (M : Matrix X Y ℝ) {a : ℝ}, 0 ≤ a → (∀ (x : X), SGC.Bridge.TerminalDecoding.l1 (M x) ≤ a) → SGC.Bridge.TerminalDecoding.rowL1Norm M ≤ a

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`

### `SGC.Bridge.TerminalDecoding.rowL1Norm_mul_dobrushin`

- statement (kernel-elaborated, sha256 `7a30cfa9c38f00a8`):

      ∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst : Fintype X] [inst_1 : Fintype Y] [inst_2 : Fintype Z] (M : Matrix X Y ℝ) (Q : Matrix Y Z ℝ), (∀ (x : X), ∑ y, M x y = 0) → SGC.Bridge.TerminalDecoding.rowL1Norm (M * Q) ≤ SGC.Bridge.TerminalDecoding.dobrushin Q * SGC.Bridge.TerminalDecoding.rowL1Norm M

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.dobrushin` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowDifferences` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → Matrix X Y ℝ → Matrix (X × X) Y ℝ`

### `SGC.Bridge.TerminalDecoding.rowL1Norm_mul_pow_dobrushin`

- statement (kernel-elaborated, sha256 `a4d00596f81b0a7a`):

      ∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype X] [inst_1 : Fintype Y] [inst_2 : DecidableEq Y] (M : Matrix X Y ℝ) (Q : Matrix Y Y ℝ), SGC.Bridge.TerminalDecoding.RowStochastic Q → (∀ (x : X), ∑ y, M x y = 0) → ∀ (m : ℕ), SGC.Bridge.TerminalDecoding.rowL1Norm (M * Q ^ m) ≤ SGC.Bridge.TerminalDecoding.dobrushin Q ^ m * SGC.Bridge.TerminalDecoding.rowL1Norm M

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.dobrushin` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowDifferences` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → Matrix X Y ℝ → Matrix (X × X) Y ℝ`

### `SGC.Bridge.TerminalDecoding.rowStochastic_lift`

- statement (kernel-elaborated, sha256 `bf5237f26d6ad9a1`):

      ∀ {X : Type u_1} [inst : Fintype X] [inst_1 : DecidableEq X] (P : SGC.Partition X), SGC.Bridge.TerminalDecoding.RowStochastic (SGC.lift_matrix P)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`

### `SGC.Bridge.TerminalDecoding.row_l1_le_rowL1Norm`

- statement (kernel-elaborated, sha256 `a7a4488a45047a6a`):

      ∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype X] [inst_1 : Fintype Y] (M : Matrix X Y ℝ) (x : X), SGC.Bridge.TerminalDecoding.l1 (M x) ≤ SGC.Bridge.TerminalDecoding.rowL1Norm M

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`

### `SGC.Bridge.TerminalDecoding.row_tv_le_dobrushin`

- statement (kernel-elaborated, sha256 `784cedb2529f0891`):

      ∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype X] [inst_1 : Fintype Y] (M : Matrix X Y ℝ) (x x' : X), SGC.Bridge.TerminalDecoding.tv (M x) (M x') ≤ SGC.Bridge.TerminalDecoding.dobrushin M

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.dobrushin` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowDifferences` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → Matrix X Y ℝ → Matrix (X × X) Y ℝ`

### `SGC.Bridge.TerminalDecoding.semantic_contraction_compatibility`

- statement (kernel-elaborated, sha256 `f35af0b8f7d8fccb`):

      ∀ {X : Type u_1} [inst : Fintype X] (d : SGC.Bridge.TerminalDecoding.Decoder X) (a r : Bool → SGC.Bridge.TerminalDecoding.ProbabilityRow X) (epsilon : Bool → ℝ), (∀ (b : Bool), SGC.Bridge.TerminalDecoding.tv (a b).mass (r b).mass ≤ epsilon b) → ∀ {U : ℝ}, SGC.Bridge.TerminalDecoding.tv (a false).mass (a true).mass ≤ U → 1 - U ≤ d.error (r false) false + d.error (r true) true + epsilon false + epsilon true

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.Decoder` (inductive, SGC.Bridge.TerminalDecoding): `Type u_4 → Type u_4`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.error` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.Decoder X → SGC.Bridge.TerminalDecoding.ProbabilityRow X → Bool → ℝ`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.loss` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → SGC.Bridge.TerminalDecoding.Decoder X → Bool → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.probOne` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → SGC.Bridge.TerminalDecoding.Decoder X → X → ℝ`

### `SGC.Bridge.TerminalDecoding.signed_l1_vecMul_dobrushin`

- statement (kernel-elaborated, sha256 `061e327a00824899`):

      ∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype X] [inst_1 : Fintype Y] (M : Matrix X Y ℝ) (v : X → ℝ), ∑ x, v x = 0 → SGC.Bridge.TerminalDecoding.l1 (Matrix.vecMul v M) ≤ SGC.Bridge.TerminalDecoding.dobrushin M * SGC.Bridge.TerminalDecoding.l1 v

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.dobrushin` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowDifferences` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → Matrix X Y ℝ → Matrix (X × X) Y ℝ`

### `SGC.Bridge.TerminalDecoding.stochastic_difference_rowL1Norm_le_two`

- statement (kernel-elaborated, sha256 `9f8611e06a9faa49`):

      ∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype X] [inst_1 : Fintype Y] {M N : Matrix X Y ℝ}, SGC.Bridge.TerminalDecoding.RowStochastic M → SGC.Bridge.TerminalDecoding.RowStochastic N → SGC.Bridge.TerminalDecoding.rowL1Norm (M - N) ≤ 2

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`

### `SGC.Bridge.TerminalDecoding.sum_vecMul_stochastic`

- statement (kernel-elaborated, sha256 `3d45476691e239a1`):

      ∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype X] [inst_1 : Fintype Y] {M : Matrix X Y ℝ}, SGC.Bridge.TerminalDecoding.RowStochastic M → ∀ (v : X → ℝ), ∑ y, Matrix.vecMul v M y = ∑ x, v x

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`

### `SGC.Bridge.TerminalDecoding.terminalBudget_zero`

- statement (kernel-elaborated, sha256 `37988d2b22eb90cf`):

      ∀ {X : Type u_1} [inst : Fintype X] [inst_1 : DecidableEq X] (T : Matrix X X ℝ) (P : SGC.Partition X) (pi : X → ℝ), SGC.Bridge.TerminalDecoding.terminalBudget T P pi 0 = 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=simp vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.TerminalDecoding.terminalBudget` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → [inst : DecidableEq X] → Matrix X X ℝ → SGC.Partition X → (X → ℝ) → ℕ → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.TerminalDecoding.terminalError_zero`

- statement (kernel-elaborated, sha256 `1cd5f60fa036c4d2`):

      ∀ {X : Type u_1} [inst : Fintype X] [inst_1 : DecidableEq X] (T : Matrix X X ℝ) (P : SGC.Partition X) (pi : X → ℝ), SGC.Bridge.TerminalDecoding.terminalError T P pi 0 = 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=simp vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.TerminalDecoding.terminalError` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → [inst : DecidableEq X] → Matrix X X ℝ → (P : SGC.Partition X) → (X → ℝ) → ℕ → Matrix X P.Quot ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.TerminalDecoding.terminal_reliability_of_reference_bounds`

- statement (kernel-elaborated, sha256 `d3c7be326b4730b6`):

      ∀ {X : Type u_1} [inst : Fintype X] (d : SGC.Bridge.TerminalDecoding.Decoder X) (a r : Bool → SGC.Bridge.TerminalDecoding.ProbabilityRow X) (epsilon : Bool → ℝ) (beta p : Bool → ↑(Set.Icc 0 1)), (∀ (b : Bool), SGC.Bridge.TerminalDecoding.tv (a b).mass (r b).mass ≤ epsilon b) → (∀ (b : Bool), d.error (r b) b ≤ ↑(beta b)) → (∀ (b : Bool), ↑(beta b) + epsilon b ≤ ↑(p b)) → ∀ (b : Bool), d.error (a b) b ≤ ↑(p b)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.Decoder` (inductive, SGC.Bridge.TerminalDecoding): `Type u_4 → Type u_4`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.error` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.Decoder X → SGC.Bridge.TerminalDecoding.ProbabilityRow X → Bool → ℝ`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.loss` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → SGC.Bridge.TerminalDecoding.Decoder X → Bool → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.probOne` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → SGC.Bridge.TerminalDecoding.Decoder X → X → ℝ`

### `SGC.Bridge.TerminalDecoding.tv_data_processing`

- statement (kernel-elaborated, sha256 `702d202dae2b6106`):

      ∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype X] [inst_1 : Fintype Y] (p q : X → ℝ) {M : Matrix X Y ℝ}, SGC.Bridge.TerminalDecoding.RowStochastic M → SGC.Bridge.TerminalDecoding.tv (Matrix.vecMul p M) (Matrix.vecMul q M) ≤ SGC.Bridge.TerminalDecoding.tv p q

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`

### `SGC.Bridge.TerminalDecoding.tv_dobrushin_contraction`

- statement (kernel-elaborated, sha256 `b7063b78fa9adbb9`):

      ∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype X] [inst_1 : Fintype Y] (p q : SGC.Bridge.TerminalDecoding.ProbabilityRow X) (M : Matrix X Y ℝ), SGC.Bridge.TerminalDecoding.tv (Matrix.vecMul p.mass M) (Matrix.vecMul q.mass M) ≤ SGC.Bridge.TerminalDecoding.dobrushin M * SGC.Bridge.TerminalDecoding.tv p.mass q.mass

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.dobrushin` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowDifferences` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → Matrix X Y ℝ → Matrix (X × X) Y ℝ`

### `SGC.Bridge.TerminalDecoding.tv_le_one`

- statement (kernel-elaborated, sha256 `036a46471029630a`):

      ∀ {X : Type u_1} [inst : Fintype X] (p q : SGC.Bridge.TerminalDecoding.ProbabilityRow X), SGC.Bridge.TerminalDecoding.tv p.mass q.mass ≤ 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`

### `SGC.Bridge.TerminalDecoding.tv_lower_of_individual_error_bounds`

- statement (kernel-elaborated, sha256 `78abe6c50475fc4d`):

      ∀ {X : Type u_1} [inst : Fintype X] (d : SGC.Bridge.TerminalDecoding.Decoder X) (a : Bool → SGC.Bridge.TerminalDecoding.ProbabilityRow X) (p : Bool → ↑(Set.Icc 0 1)), (∀ (b : Bool), d.error (a b) b ≤ ↑(p b)) → max 0 (1 - ↑(p false) - ↑(p true)) ≤ SGC.Bridge.TerminalDecoding.tv (a false).mass (a true).mass

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.Decoder` (inductive, SGC.Bridge.TerminalDecoding): `Type u_4 → Type u_4`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.Decoder.error` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.Decoder X → SGC.Bridge.TerminalDecoding.ProbabilityRow X → Bool → ℝ`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.loss` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → SGC.Bridge.TerminalDecoding.Decoder X → Bool → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.probOne` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → SGC.Bridge.TerminalDecoding.Decoder X → X → ℝ`

### `SGC.Bridge.TerminalDecoding.tv_nonneg`

- statement (kernel-elaborated, sha256 `421b4e44cd029781`):

      ∀ {X : Type u_1} [inst : Fintype X] (p q : X → ℝ), 0 ≤ SGC.Bridge.TerminalDecoding.tv p q

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`

### `SGC.Bridge.TerminalDecoding.tv_self`

- statement (kernel-elaborated, sha256 `0d0a3646f6b7dc31`):

      ∀ {X : Type u_1} [inst : Fintype X] (p : X → ℝ), SGC.Bridge.TerminalDecoding.tv p p = 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=simp vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`

### `SGC.Bridge.TerminalDecoding.tv_symm`

- statement (kernel-elaborated, sha256 `63e7aa774dabbd62`):

      ∀ {X : Type u_1} [inst : Fintype X] (p q : X → ℝ), SGC.Bridge.TerminalDecoding.tv p q = SGC.Bridge.TerminalDecoding.tv q p

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`

### `SGC.Bridge.TerminalDecoding.tv_triangle`

- statement (kernel-elaborated, sha256 `0c27861e1ee6a433`):

      ∀ {X : Type u_1} [inst : Fintype X] (p q r : X → ℝ), SGC.Bridge.TerminalDecoding.tv p r ≤ SGC.Bridge.TerminalDecoding.tv p q + SGC.Bridge.TerminalDecoding.tv q r

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`

### `SGC.Bridge.TerminalDecoding.tv_vecMul_le_half_row_l1`

- statement (kernel-elaborated, sha256 `69f86903c968a4a7`):

      ∀ {X : Type u_1} {Y : Type u_2} [inst : Fintype X] [inst_1 : Fintype Y] (p : SGC.Bridge.TerminalDecoding.ProbabilityRow X) (M N : Matrix X Y ℝ), SGC.Bridge.TerminalDecoding.tv (Matrix.vecMul p.mass M) (Matrix.vecMul p.mass N) ≤ SGC.Bridge.TerminalDecoding.rowL1Norm (M - N) / 2

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`

## Trust surface (project axioms)

| axiom | type | consumers | unconstrained numeric params |
|---|---|---|---|
| `SGC.Approximate.rowsum_to_opNorm_bound` | `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (ε : ℝ), 0 ≤ ε → SGC.IsRowSumApproxLumpable L P ε → SGC.opNorm_pi pi_dist hπ (SGC.Approximate.DefectOperator L P pi_dist hπ) ≤ ↑(Fintype.card V) * ε` | 1 | - |
| `SGC.Approximate.Weyl_inequality_pi` | `∀ {V : Type u_1} [inst : Fintype V] (A B : (V → ℝ) →ₗ[ℝ] V → ℝ) (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (k : ℕ), SGC.Approximate.IsSelfAdjoint_pi A pi_dist → SGC.Approximate.IsSelfAdjoint_pi B pi_dist → ∃ eigenvalue_k, |eigenvalue_k A - eigenvalue_k B| ≤ SGC.opNorm_pi pi_dist hπ (A - B)` | 0 | - |
| `SGC.Approximate.NCD_defect_split` | `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L L_fast L_slow : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (ε γ : ℝ), SGC.Approximate.IsNCD L L_fast L_slow P pi_dist hπ ε γ → SGC.Approximate.DefectOperator L P pi_dist hπ = ε • SGC.Approximate.DefectOperator L_slow P pi_dist hπ` | 0 | - |
| `SGC.Approximate.NCD_integral_bound` | `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L L_fast L_slow : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (ε γ : ℝ), SGC.Approximate.IsNCD L L_fast L_slow P pi_dist hπ ε γ → ∀ (t : ℝ), 0 ≤ t → ∀ (f₀ : V → ℝ), f₀ = (SGC.Approximate.CoarseProjector P pi_dist hπ) f₀ → ∀ (M : ℝ), 0 ≤ M → (∀ (s : ℝ), 0 ≤ s → s ≤ t → SGC.norm_pi pi_dist ((SGC.Approximate.DefectOperator L P pi_dist hπ) ((SGC.Approximate.CoarseProjector P pi_dist hπ) ((SGC.Approximate.HeatKernelMap L s) f₀))) ≤ M * SGC.norm_pi pi_dist f₀) → SGC.norm_pi pi_dist ((SGC.Approximate.HeatKernelMap L t) f₀ - (SGC.Approximate.CoarseProjector P pi_dist hπ) ((SGC.Approximate.HeatKernelMap L t) f₀)) ≤ M / γ * SGC.norm_pi pi_dist f₀` | 0 | - |
| `SGC.Thermodynamics.hidden_entropy_bound_from_trajectory` | `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ) (hπ : ∀ (x : V), 0 < pi_dist x) (ε : ℝ), 0 ≤ ε → SGC.Approximate.IsApproxLumpable L P pi_dist hπ ε → ∀ (C_traj : ℝ), 0 < C_traj → SGC.Thermodynamics.HiddenEntropyProduction L P pi_dist ≤ ↑(Fintype.card V) * C_traj ^ 2 * ε ^ 2` | 1 | - |
| `SGC.Thermodynamics.gaspard_path_space_identity` | `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ) (hπ : ∀ (x : V), 0 < pi_dist x), (∀ (x y : V), x ≠ y → 0 ≤ L x y) → (∀ (v : V), ∑ u, pi_dist u * L u v = 0) → ∀ γ > 0, γ ≤ SGC.DirichletGap L pi_dist → γ * SGC.opNorm_pi pi_dist hπ (SGC.Approximate.DefectOperator L P pi_dist hπ) ^ 2 ≤ SGC.Thermodynamics.HiddenEntropyProduction L P pi_dist` | 2 | - |

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
