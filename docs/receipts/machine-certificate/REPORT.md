# lean-triage report: REVIEW

- receipt: `lean-triage-0ad4a6aab9b1-20260914T031444Z`  (hash_self `f5a76912a9b5b1f7...`)
- tool: lean-triage 0.2.1 (source `25bc5fa54832`, probe `97172a3b4b00`)
- repo: https://github.com/JasonShroyer/sgc-lean.git
- commit: 3d534fe1b33a6da3bc051993f9d1539a0ede22fb  dirty=True
- toolchain: leanprover/lean4:v4.25.2
- source tree sha256: `0ad4a6aab9b11ced056d3024b991833c75e6f6e5e9f3f4000724f4548717f23d`
- modules: SGC.Bridge.MachineCertificate

## Verdict

**REVIEW** - 0 fail, 15 warn, 104 info.

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
| warn | process | F12 | DIRTY_TREE | - | working tree has uncommitted changes; audited bytes may differ from the recorded commit |
| warn | heuristic | F10 | NARRATIVE_CLAIM_NEEDS_HUMAN_MAP | - | strong-claim vocabulary 'Millennium' appears 2x (THEORY.md:175, docs/bkm-formalization-design.md:46); a human must map the formal statements to it |
| warn | heuristic | F10 | NARRATIVE_CLAIM_NEEDS_HUMAN_MAP | - | strong-claim vocabulary 'Navier-Stokes' appears 5x (PRIORITY_CLAIMS.md:93, PRIORITY_CLAIMS.md:95, PRIORITY_CLAIMS.md:99, ...); a human must map the formal statements to it |
| warn | heuristic | F10 | NARRATIVE_CLAIM_NEEDS_HUMAN_MAP | - | strong-claim vocabulary 'Riemann' appears 26x (CHANGELOG.md:164, RESEARCH_JOURNAL.md:90, VERIFIED_CORE_MANIFEST.md:381, ...); a human must map the formal statements to it |
| warn | heuristic | F10 | NARRATIVE_CLAIM_NEEDS_HUMAN_MAP | - | strong-claim vocabulary 'fully verified' appears 5x (README.md:37, VERIFIED_CORE_MANIFEST.md:52, VERIFIED_CORE_MANIFEST.md:117, ...); a human must map the formal statements to it |
| warn | heuristic | F10 | NARRATIVE_CLAIM_NEEDS_HUMAN_MAP | - | strong-claim vocabulary 'settles' appears 3x (decisions/0016-curvature-descends-along-lumpable-quotients.md:50, reports/PHASE_4A_CANONICAL_WAVELET_FISHER_RAO_INTEGRATION.md:249, theory_context/SGC UPAT Methods Deep Dive.md:211); a human must map the formal statements to it |
| warn | heuristic | F10 | NARRATIVE_CLAIM_NEEDS_HUMAN_MAP | - | strong-claim vocabulary 'unconditional' appears 10x (RESEARCH_JOURNAL.md:285, RESEARCH_JOURNAL.md:567, RESEARCH_JOURNAL.md:816, ...); a human must map the formal statements to it |
| warn | process | F13 | TOOLCHAIN_ADVISORY | - | toolchain leanprover/lean4:v4.25.2 is below 4.32.2: Kernel soundness bug (nested inductive types with phantom parameters) allowed an axiom-free proof of False; #print axioms reported nothing. Fixed in Lean 4.32.2. |
| warn | process | F13 | TOOLCHAIN_ADVISORY | - | toolchain leanprover/lean4:v4.25.2 is below 4.32.2: Runtime reference-count overflow path that could corrupt memory and yield False (reported in the 2026 soundness-bug hunt). |
| info | witness | F07 | AUTOMATION_CLOSES_TARGET_UNDER_POLICY | SGC.Bridge.MachineCertificate.descends_fst_iff | the configured automation policy closes the statement (`rfl`); legitimate, but weigh against any strong narrative |
| info | kernel | F16 | AXIOM_UNREFERENCED | - | axiom SGC.Approximate.NCD_defect_split has no consumer in the loaded project modules; trust-surface bloat |
| info | kernel | F16 | AXIOM_UNREFERENCED | - | axiom SGC.Approximate.NCD_integral_bound has no consumer in the loaded project modules; trust-surface bloat |
| info | kernel | F16 | AXIOM_UNREFERENCED | - | axiom SGC.Approximate.Weyl_inequality_pi has no consumer in the loaded project modules; trust-surface bloat |
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
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.Regression.collapse_dobrushin_one | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.Regression.collapse_dobrushin_two_zero | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.Regression.collapse_sq_const | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.Regression.reader_Q_entry | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.Regression.reader_budget_sharp | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.Regression.reader_coarse_row | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.Regression.reader_defect_eq_one | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.Regression.reader_defect_exact | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.Regression.reader_dobrushin_zero | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.Regression.reader_mixing_budget | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.Regression.swap_Q_sq_ne_Q_block | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.Regression.swap_block_descends_not_step | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.agreeOn_mono | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.coarse_entry_le_one | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.coarse_output_mass_pos | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.defect_pos_of_leak | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.descends_fst_iff | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.descends_fst_of_autonomous | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.descends_iff_defect_lt_one | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.detKernel_commutator_entry | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.detKernel_row_residual_l1 | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.dobrushin_detKernel_eq_one | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.dobrushin_zero_iff_rows_equal | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.iterate_fst_of_autonomous | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.linear_certificate_implies_descends | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.machineDefect_gap | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.machineDefect_ge_one_of_not_descends | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.machineDefect_linear_budget_vacuous | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.machineDefect_lt_two | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.machine_error_of_dobrushin_zero | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.machine_point_law | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.machine_point_reference | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.machine_point_tv_eq_zero_iff | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.machine_point_tv_exact | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.machine_terminal_reliability | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.machine_terminal_tv | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.machine_terminal_tv_of_descends | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.mixing_budget_trivial_of_quotient_machine | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.pow_row_const_of_rows_equal | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.tmBlock_descends_shrink | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.tmStep_iterate_window | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.tmStep_window | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.tv_point_prob | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.MachineCertificate.windowRel_equivalence | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.Regression.collapse_dobrushin_one | 5 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.Regression.collapse_dobrushin_two_zero | 5 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.Regression.collapse_sq_const | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.Regression.reader_Q_entry | 14 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.Regression.reader_budget_sharp | 34 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.Regression.reader_coarse_row | 14 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.Regression.reader_defect_eq_one | 19 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.Regression.reader_defect_exact | 19 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.Regression.reader_dobrushin_zero | 18 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.Regression.reader_mixing_budget | 21 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.Regression.swap_Q_sq_ne_Q_block | 14 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.Regression.swap_block_descends_not_step | 6 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.agreeOn_mono | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.coarse_entry_le_one | 10 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.coarse_output_mass_pos | 10 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.defect_pos_of_leak | 16 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.descends_fst_iff | 5 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.descends_fst_of_autonomous | 5 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.descends_iff_defect_lt_one | 16 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.detKernel_commutator_entry | 13 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.detKernel_row_residual_l1 | 14 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.dobrushin_detKernel_eq_one | 4 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.dobrushin_zero_iff_rows_equal | 3 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.linear_certificate_implies_descends | 16 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.machineDefect_gap | 15 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.machineDefect_ge_one_of_not_descends | 16 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.machineDefect_linear_budget_vacuous | 16 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.machineDefect_lt_two | 15 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.machine_error_of_dobrushin_zero | 28 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.machine_point_law | 19 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.machine_point_reference | 22 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.machine_point_tv_eq_zero_iff | 25 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.machine_point_tv_exact | 25 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.machine_terminal_reliability | 29 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.machine_terminal_tv | 27 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.machine_terminal_tv_of_descends | 25 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.mixing_budget_trivial_of_quotient_machine | 16 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.pow_row_const_of_rows_equal | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.tmBlock_descends_shrink | 4 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.tmStep_iterate_window | 3 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.tmStep_window | 3 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.tv_point_prob | 4 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.MachineCertificate.windowRel_equivalence | 3 project-local definition(s) determine what this theorem is about; read them |

## Per-theorem receipt

### `SGC.Bridge.MachineCertificate.Regression.collapse_dobrushin_one`

- statement (kernel-elaborated, sha256 `23c6b4293954fa65`):

      SGC.Bridge.TerminalDecoding.dobrushin (SGC.Bridge.BlockRenormalization.detKernel SGC.Bridge.MachineCertificate.Regression.collapse) = 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.dobrushin` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Bridge.MachineCertificate.Regression.collapse` (def, SGC.Bridge.MachineCertificate): `Fin 3 → Fin 3`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowDifferences` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → Matrix X Y ℝ → Matrix (X × X) Y ℝ`

### `SGC.Bridge.MachineCertificate.Regression.collapse_dobrushin_two_zero`

- statement (kernel-elaborated, sha256 `2f7107ebf6ee799a`):

      SGC.Bridge.TerminalDecoding.dobrushin (SGC.Bridge.BlockRenormalization.detKernel SGC.Bridge.MachineCertificate.Regression.collapse ^ 2) = 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.dobrushin` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Bridge.MachineCertificate.Regression.collapse` (def, SGC.Bridge.MachineCertificate): `Fin 3 → Fin 3`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowDifferences` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → Matrix X Y ℝ → Matrix (X × X) Y ℝ`

### `SGC.Bridge.MachineCertificate.Regression.collapse_sq_const`

- statement (kernel-elaborated, sha256 `0569ba26935e1942`):

      ∀ (x : Fin 3), SGC.Bridge.MachineCertificate.Regression.collapse^[2] x = 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.MachineCertificate.Regression.collapse` (def, SGC.Bridge.MachineCertificate): `Fin 3 → Fin 3`

### `SGC.Bridge.MachineCertificate.Regression.reader_Q_entry`

- statement (kernel-elaborated, sha256 `1e4ba67ed78aa46b`):

      ∀ (A B : SGC.Bridge.DeterministicLumpability.Regression.byState.Quot), SGC.Thermodynamics.CoarseGenerator (SGC.Bridge.BlockRenormalization.detKernel SGC.Bridge.DeterministicLumpability.Regression.reader) SGC.Bridge.DeterministicLumpability.Regression.byState (fun x => 1) A B = 1 / 2

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.DeterministicLumpability.Regression.Cfg` (def, SGC.Bridge.DeterministicLumpability): `Type`
    - `SGC.Bridge.DeterministicLumpability.Regression.byState` (def, SGC.Bridge.DeterministicLumpability): `SGC.Partition SGC.Bridge.DeterministicLumpability.Regression.Cfg`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Bridge.DeterministicLumpability.Regression.reader` (def, SGC.Bridge.DeterministicLumpability): `SGC.Bridge.DeterministicLumpability.Regression.Cfg → SGC.Bridge.DeterministicLumpability.Regression.Cfg`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.MachineCertificate.Regression.reader_budget_sharp`

- statement (kernel-elaborated, sha256 `9bd4cb8f13fa3176`):

      ∀ (x : SGC.Bridge.DeterministicLumpability.Regression.Cfg) (h : ℕ), 1 ≤ h → SGC.Bridge.TerminalDecoding.tv (SGC.Bridge.TerminalDecoding.actualLaw (SGC.Bridge.BlockRenormalization.detKernel SGC.Bridge.DeterministicLumpability.Regression.reader) SGC.Bridge.DeterministicLumpability.Regression.byState ⋯ (SGC.Bridge.MachineCertificate.pointMass x) h).mass (SGC.Bridge.TerminalDecoding.referenceLaw (SGC.Bridge.BlockRenormalization.detKernel SGC.Bridge.DeterministicLumpability.Regression.reader) SGC.Bridge.DeterministicLumpability.Regression.byState ⋯ ⋯ (SGC.Bridge.MachineCertificate.pointMass x) h).mass = SGC.Bridge.TerminalDecoding.mixingBudget (SGC.Bridge.BlockRenormalization.detKernel SGC.Bridge.DeterministicLumpability.Regression.reader) SGC.Bridge.DeterministicLumpability.Regression.byState (fun x => 1) h

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DeterministicLumpability.Regression.Cfg` (def, SGC.Bridge.DeterministicLumpability): `Type`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.DeterministicLumpability.Regression.byState` (def, SGC.Bridge.DeterministicLumpability): `SGC.Partition SGC.Bridge.DeterministicLumpability.Regression.Cfg`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.actualLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Bridge.DeterministicLumpability.Regression.reader` (def, SGC.Bridge.DeterministicLumpability): `SGC.Bridge.DeterministicLumpability.Regression.Cfg → SGC.Bridge.DeterministicLumpability.Regression.Cfg`
    - `SGC.Bridge.BlockRenormalization.detKernel_isStochastic` (theorem, SGC.Bridge.BlockRenormalization): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V), SGC.Renormalization.KernelHorizon.IsStochastic (SGC.Bridge.BlockRenormalization.detKernel f)`
    - `SGC.Bridge.MachineCertificate.pointMass` (def, SGC.Bridge.MachineCertificate): `{V : Type u_1} → [inst : Fintype V] → [DecidableEq V] → V → SGC.Bridge.TerminalDecoding.ProbabilityRow V`
    - `SGC.Bridge.TerminalDecoding.referenceLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → {pi : X → ℝ} → (∀ (x : X), 0 < pi x) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.TerminalDecoding.mixingBudget` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → [inst : DecidableEq X] → Matrix X X ℝ → SGC.Partition X → (X → ℝ) → ℕ → ℝ`
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
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.dobrushin` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowDifferences` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → Matrix X Y ℝ → Matrix (X × X) Y ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.MachineCertificate.Regression.reader_coarse_row`

- statement (kernel-elaborated, sha256 `5509ee93e6f455bd`):

      ∀ (b : Bool) (B : SGC.Bridge.DeterministicLumpability.Regression.byState.Quot), SGC.Thermodynamics.CoarseGenerator (SGC.Bridge.BlockRenormalization.detKernel SGC.Bridge.DeterministicLumpability.Regression.reader) SGC.Bridge.DeterministicLumpability.Regression.byState (fun x => 1) (SGC.Bridge.DeterministicLumpability.Regression.byState.quot_map (b, b)) B = 1 / 2

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.DeterministicLumpability.Regression.Cfg` (def, SGC.Bridge.DeterministicLumpability): `Type`
    - `SGC.Bridge.DeterministicLumpability.Regression.byState` (def, SGC.Bridge.DeterministicLumpability): `SGC.Partition SGC.Bridge.DeterministicLumpability.Regression.Cfg`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Bridge.DeterministicLumpability.Regression.reader` (def, SGC.Bridge.DeterministicLumpability): `SGC.Bridge.DeterministicLumpability.Regression.Cfg → SGC.Bridge.DeterministicLumpability.Regression.Cfg`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.MachineCertificate.Regression.reader_defect_eq_one`

- statement (kernel-elaborated, sha256 `72f50f36145fd012`):

      ∀ {pi : SGC.Bridge.DeterministicLumpability.Regression.Cfg → ℝ}, (∀ (x : SGC.Bridge.DeterministicLumpability.Regression.Cfg), 0 < pi x) → SGC.Bridge.MachineCertificate.machineDefect SGC.Bridge.DeterministicLumpability.Regression.reader SGC.Bridge.DeterministicLumpability.Regression.byState pi ≥ 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DeterministicLumpability.Regression.Cfg` (def, SGC.Bridge.DeterministicLumpability): `Type`
    - `SGC.Bridge.MachineCertificate.machineDefect` (def, SGC.Bridge.MachineCertificate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (V → V) → SGC.Partition V → (V → ℝ) → ℝ`
    - `SGC.Bridge.DeterministicLumpability.Regression.reader` (def, SGC.Bridge.DeterministicLumpability): `SGC.Bridge.DeterministicLumpability.Regression.Cfg → SGC.Bridge.DeterministicLumpability.Regression.Cfg`
    - `SGC.Bridge.DeterministicLumpability.Regression.byState` (def, SGC.Bridge.DeterministicLumpability): `SGC.Partition SGC.Bridge.DeterministicLumpability.Regression.Cfg`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.MachineCertificate.Regression.reader_defect_exact`

- statement (kernel-elaborated, sha256 `0c7e33ba591a72cd`):

      (SGC.Bridge.MachineCertificate.machineDefect SGC.Bridge.DeterministicLumpability.Regression.reader SGC.Bridge.DeterministicLumpability.Regression.byState fun x => 1) = 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.MachineCertificate.machineDefect` (def, SGC.Bridge.MachineCertificate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (V → V) → SGC.Partition V → (V → ℝ) → ℝ`
    - `SGC.Bridge.DeterministicLumpability.Regression.Cfg` (def, SGC.Bridge.DeterministicLumpability): `Type`
    - `SGC.Bridge.DeterministicLumpability.Regression.reader` (def, SGC.Bridge.DeterministicLumpability): `SGC.Bridge.DeterministicLumpability.Regression.Cfg → SGC.Bridge.DeterministicLumpability.Regression.Cfg`
    - `SGC.Bridge.DeterministicLumpability.Regression.byState` (def, SGC.Bridge.DeterministicLumpability): `SGC.Partition SGC.Bridge.DeterministicLumpability.Regression.Cfg`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.MachineCertificate.Regression.reader_dobrushin_zero`

- statement (kernel-elaborated, sha256 `f6bb760e83f6ddcb`):

      SGC.Bridge.TerminalDecoding.dobrushin (SGC.Thermodynamics.CoarseGenerator (SGC.Bridge.BlockRenormalization.detKernel SGC.Bridge.DeterministicLumpability.Regression.reader) SGC.Bridge.DeterministicLumpability.Regression.byState fun x => 1) = 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.dobrushin` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.DeterministicLumpability.Regression.Cfg` (def, SGC.Bridge.DeterministicLumpability): `Type`
    - `SGC.Bridge.DeterministicLumpability.Regression.byState` (def, SGC.Bridge.DeterministicLumpability): `SGC.Partition SGC.Bridge.DeterministicLumpability.Regression.Cfg`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Bridge.DeterministicLumpability.Regression.reader` (def, SGC.Bridge.DeterministicLumpability): `SGC.Bridge.DeterministicLumpability.Regression.Cfg → SGC.Bridge.DeterministicLumpability.Regression.Cfg`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowDifferences` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → Matrix X Y ℝ → Matrix (X × X) Y ℝ`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.MachineCertificate.Regression.reader_mixing_budget`

- statement (kernel-elaborated, sha256 `24514d59e7ceb12f`):

      ∀ (h : ℕ), 1 ≤ h → SGC.Bridge.TerminalDecoding.mixingBudget (SGC.Bridge.BlockRenormalization.detKernel SGC.Bridge.DeterministicLumpability.Regression.reader) SGC.Bridge.DeterministicLumpability.Regression.byState (fun x => 1) h = 1 / 2

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.mixingBudget` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → [inst : DecidableEq X] → Matrix X X ℝ → SGC.Partition X → (X → ℝ) → ℕ → ℝ`
    - `SGC.Bridge.DeterministicLumpability.Regression.Cfg` (def, SGC.Bridge.DeterministicLumpability): `Type`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Bridge.DeterministicLumpability.Regression.reader` (def, SGC.Bridge.DeterministicLumpability): `SGC.Bridge.DeterministicLumpability.Regression.Cfg → SGC.Bridge.DeterministicLumpability.Regression.Cfg`
    - `SGC.Bridge.DeterministicLumpability.Regression.byState` (def, SGC.Bridge.DeterministicLumpability): `SGC.Partition SGC.Bridge.DeterministicLumpability.Regression.Cfg`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.dobrushin` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.rowDifferences` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → Matrix X Y ℝ → Matrix (X × X) Y ℝ`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.MachineCertificate.Regression.swap_Q_sq_ne_Q_block`

- statement (kernel-elaborated, sha256 `ea23f83abd413b68`):

      (SGC.Thermodynamics.CoarseGenerator (SGC.Bridge.BlockRenormalization.detKernel SGC.Bridge.MachineCertificate.Regression.swap2) SGC.Bridge.MachineCertificate.fstPartition fun x => 1) ^ 2 ≠ SGC.Thermodynamics.CoarseGenerator (SGC.Bridge.BlockRenormalization.detKernel SGC.Bridge.MachineCertificate.Regression.swap2^[2]) SGC.Bridge.MachineCertificate.fstPartition fun x => 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.MachineCertificate.fstPartition` (def, SGC.Bridge.MachineCertificate): `{A : Type u_2} → {B : Type u_3} → [inst : DecidableEq A] → [inst_1 : DecidableEq B] → SGC.Partition (A × B)`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Bridge.MachineCertificate.Regression.swap2` (def, SGC.Bridge.MachineCertificate): `Bool × Bool → Bool × Bool`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.MachineCertificate.Regression.swap_block_descends_not_step`

- statement (kernel-elaborated, sha256 `a5551eb8f6e0a963`):

      SGC.Bridge.DeterministicLumpability.Descends SGC.Bridge.MachineCertificate.Regression.swap2^[2] SGC.Bridge.MachineCertificate.fstPartition ∧ ¬SGC.Bridge.DeterministicLumpability.Descends SGC.Bridge.MachineCertificate.Regression.swap2 SGC.Bridge.MachineCertificate.fstPartition

- axioms: Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DeterministicLumpability.Descends` (def, SGC.Bridge.DeterministicLumpability): `{V : Type u_1} → [inst : DecidableEq V] → (V → V) → SGC.Partition V → Prop`
    - `SGC.Bridge.MachineCertificate.Regression.swap2` (def, SGC.Bridge.MachineCertificate): `Bool × Bool → Bool × Bool`
    - `SGC.Bridge.MachineCertificate.fstPartition` (def, SGC.Bridge.MachineCertificate): `{A : Type u_2} → {B : Type u_3} → [inst : DecidableEq A] → [inst_1 : DecidableEq B] → SGC.Partition (A × B)`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`

### `SGC.Bridge.MachineCertificate.agreeOn_mono`

- statement (kernel-elaborated, sha256 `58bfbeefb0da361b`):

      ∀ {Γ : Type u_3} {r r' : ℤ}, r' ≤ r → ∀ {t t' : ℤ → Γ}, SGC.Bridge.MachineCertificate.AgreeOn r t t' → SGC.Bridge.MachineCertificate.AgreeOn r' t t'

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.MachineCertificate.AgreeOn` (def, SGC.Bridge.MachineCertificate): `{Γ : Type u_3} → ℤ → (ℤ → Γ) → (ℤ → Γ) → Prop`

### `SGC.Bridge.MachineCertificate.coarse_entry_le_one`

- statement (kernel-elaborated, sha256 `263aa34a09d8d17a`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V) (P : SGC.Partition V) {pi : V → ℝ}, (∀ (x : V), 0 < pi x) → ∀ (A B : P.Quot), SGC.Thermodynamics.CoarseGenerator (SGC.Bridge.BlockRenormalization.detKernel f) P pi A B ≤ 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.MachineCertificate.coarse_output_mass_pos`

- statement (kernel-elaborated, sha256 `850bdb4520c1e3db`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V) (P : SGC.Partition V) {pi : V → ℝ}, (∀ (x : V), 0 < pi x) → ∀ (x : V), 0 < SGC.Thermodynamics.CoarseGenerator (SGC.Bridge.BlockRenormalization.detKernel f) P pi (P.quot_map x) (P.quot_map (f x))

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.MachineCertificate.defect_pos_of_leak`

- statement (kernel-elaborated, sha256 `9e7d5327f46f7972`):

      ∀ {A : Type u_2} {B : Type u_3} [inst : Fintype A] [inst_1 : Fintype B] [inst_2 : DecidableEq A] [inst_3 : DecidableEq B] (f : A × B → A × B) {a : A} {b₁ b₂ : B}, (f (a, b₁)).1 ≠ (f (a, b₂)).1 → ∀ {pi : A × B → ℝ}, (∀ (x : A × B), 0 < pi x) → 0 < SGC.Renormalization.MeasureReentry.defectSq (SGC.Bridge.BlockRenormalization.detKernel f) SGC.Bridge.MachineCertificate.fstPartition pi

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Renormalization.MeasureReentry.defectSq` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (V → ℝ) → ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Bridge.MachineCertificate.fstPartition` (def, SGC.Bridge.MachineCertificate): `{A : Type u_2} → {B : Type u_3} → [inst : DecidableEq A] → [inst_1 : DecidableEq B] → SGC.Partition (A × B)`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Renormalization.MeasureReentry.residual` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → V → P.Quot → ℝ`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.row_sum_block` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → V → P.Quot → ℝ`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.MachineCertificate.descends_fst_iff`

- statement (kernel-elaborated, sha256 `764e63762541e182`):

      ∀ {A : Type u_2} {B : Type u_3} [inst : DecidableEq A] [inst_1 : DecidableEq B] (f : A × B → A × B), SGC.Bridge.DeterministicLumpability.Descends f SGC.Bridge.MachineCertificate.fstPartition ↔ ∀ (x y : A × B), x.1 = y.1 → (f x).1 = (f y).1

- axioms: none
- unused hypotheses: none
- automation: trivial_by=rfl vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DeterministicLumpability.Descends` (def, SGC.Bridge.DeterministicLumpability): `{V : Type u_1} → [inst : DecidableEq V] → (V → V) → SGC.Partition V → Prop`
    - `SGC.Bridge.MachineCertificate.fstPartition` (def, SGC.Bridge.MachineCertificate): `{A : Type u_2} → {B : Type u_3} → [inst : DecidableEq A] → [inst_1 : DecidableEq B] → SGC.Partition (A × B)`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`

### `SGC.Bridge.MachineCertificate.descends_fst_of_autonomous`

- statement (kernel-elaborated, sha256 `f1486b01ac1d91a8`):

      ∀ {A : Type u_2} {B : Type u_3} [inst : DecidableEq A] [inst_1 : DecidableEq B] (f : A × B → A × B) (g : A → A), (∀ (x : A × B), (f x).1 = g x.1) → SGC.Bridge.DeterministicLumpability.Descends f SGC.Bridge.MachineCertificate.fstPartition

- axioms: none
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DeterministicLumpability.Descends` (def, SGC.Bridge.DeterministicLumpability): `{V : Type u_1} → [inst : DecidableEq V] → (V → V) → SGC.Partition V → Prop`
    - `SGC.Bridge.MachineCertificate.fstPartition` (def, SGC.Bridge.MachineCertificate): `{A : Type u_2} → {B : Type u_3} → [inst : DecidableEq A] → [inst_1 : DecidableEq B] → SGC.Partition (A × B)`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`

### `SGC.Bridge.MachineCertificate.descends_iff_defect_lt_one`

- statement (kernel-elaborated, sha256 `eb52a49d86560d63`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] [Nonempty V] (f : V → V) (P : SGC.Partition V) {pi : V → ℝ}, (∀ (x : V), 0 < pi x) → (SGC.Bridge.DeterministicLumpability.Descends f P ↔ SGC.Bridge.MachineCertificate.machineDefect f P pi < 1)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.DeterministicLumpability.Descends` (def, SGC.Bridge.DeterministicLumpability): `{V : Type u_1} → [inst : DecidableEq V] → (V → V) → SGC.Partition V → Prop`
    - `SGC.Bridge.MachineCertificate.machineDefect` (def, SGC.Bridge.MachineCertificate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (V → V) → SGC.Partition V → (V → ℝ) → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.MachineCertificate.detKernel_commutator_entry`

- statement (kernel-elaborated, sha256 `87594c91418a2d58`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V) (P : SGC.Partition V) (pi : V → ℝ) (x : V) (B : P.Quot), SGC.Renormalization.MeasureReentry.closureCommutator (SGC.Bridge.BlockRenormalization.detKernel f) P pi x B = (if P.quot_map (f x) = B then 1 else 0) - SGC.Thermodynamics.CoarseGenerator (SGC.Bridge.BlockRenormalization.detKernel f) P pi (P.quot_map x) B

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.MachineCertificate.detKernel_row_residual_l1`

- statement (kernel-elaborated, sha256 `8e9c68f44ad37311`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V) (P : SGC.Partition V) {pi : V → ℝ}, (∀ (x : V), 0 < pi x) → ∀ (x : V), SGC.Bridge.TerminalDecoding.l1 (SGC.Renormalization.MeasureReentry.closureCommutator (SGC.Bridge.BlockRenormalization.detKernel f) P pi x) = 2 * (1 - SGC.Thermodynamics.CoarseGenerator (SGC.Bridge.BlockRenormalization.detKernel f) P pi (P.quot_map x) (P.quot_map (f x)))

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.MachineCertificate.dobrushin_detKernel_eq_one`

- statement (kernel-elaborated, sha256 `90d8f37507dcdd83`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V) {x y : V}, f x ≠ f y → SGC.Bridge.TerminalDecoding.dobrushin (SGC.Bridge.BlockRenormalization.detKernel f) = 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.dobrushin` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowDifferences` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → Matrix X Y ℝ → Matrix (X × X) Y ℝ`

### `SGC.Bridge.MachineCertificate.dobrushin_zero_iff_rows_equal`

- statement (kernel-elaborated, sha256 `233780b560f95326`):

      ∀ {X : Type u_2} [inst : Fintype X] (M : Matrix X X ℝ), SGC.Bridge.TerminalDecoding.dobrushin M = 0 ↔ ∀ (x y : X), M x = M y

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.dobrushin` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowDifferences` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → Matrix X Y ℝ → Matrix (X × X) Y ℝ`

### `SGC.Bridge.MachineCertificate.iterate_fst_of_autonomous`

- statement (kernel-elaborated, sha256 `c05ee5c60d27509a`):

      ∀ {A : Type u_2} {B : Type u_3} (f : A × B → A × B) (g : A → A), (∀ (x : A × B), (f x).1 = g x.1) → ∀ (b : ℕ) (x : A × B), (f^[b] x).1 = g^[b] x.1

- axioms: none
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

### `SGC.Bridge.MachineCertificate.linear_certificate_implies_descends`

- statement (kernel-elaborated, sha256 `d95126ba4a9dd572`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] [Nonempty V] (f : V → V) (P : SGC.Partition V) {pi : V → ℝ}, (∀ (x : V), 0 < pi x) → ∀ {beta p : ℝ}, 0 ≤ beta → p < 1 / 2 → ∀ {h : ℕ}, 1 ≤ h → beta + min 1 (↑h * SGC.Bridge.MachineCertificate.machineDefect f P pi / 2) ≤ p → SGC.Bridge.DeterministicLumpability.Descends f P

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.MachineCertificate.machineDefect` (def, SGC.Bridge.MachineCertificate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (V → V) → SGC.Partition V → (V → ℝ) → ℝ`
    - `SGC.Bridge.DeterministicLumpability.Descends` (def, SGC.Bridge.DeterministicLumpability): `{V : Type u_1} → [inst : DecidableEq V] → (V → V) → SGC.Partition V → Prop`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.MachineCertificate.machineDefect_gap`

- statement (kernel-elaborated, sha256 `2cd3b5e913b65422`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] [Nonempty V] (f : V → V) (P : SGC.Partition V) {pi : V → ℝ}, (∀ (x : V), 0 < pi x) → SGC.Bridge.MachineCertificate.machineDefect f P pi = 0 ∨ 1 ≤ SGC.Bridge.MachineCertificate.machineDefect f P pi ∧ SGC.Bridge.MachineCertificate.machineDefect f P pi < 2

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.MachineCertificate.machineDefect` (def, SGC.Bridge.MachineCertificate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (V → V) → SGC.Partition V → (V → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.MachineCertificate.machineDefect_ge_one_of_not_descends`

- statement (kernel-elaborated, sha256 `fc92fddec1eed876`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V) (P : SGC.Partition V) {pi : V → ℝ}, (∀ (x : V), 0 < pi x) → ¬SGC.Bridge.DeterministicLumpability.Descends f P → 1 ≤ SGC.Bridge.MachineCertificate.machineDefect f P pi

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.DeterministicLumpability.Descends` (def, SGC.Bridge.DeterministicLumpability): `{V : Type u_1} → [inst : DecidableEq V] → (V → V) → SGC.Partition V → Prop`
    - `SGC.Bridge.MachineCertificate.machineDefect` (def, SGC.Bridge.MachineCertificate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (V → V) → SGC.Partition V → (V → ℝ) → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.MachineCertificate.machineDefect_linear_budget_vacuous`

- statement (kernel-elaborated, sha256 `f0e441019c6e1c8e`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V) (P : SGC.Partition V) {pi : V → ℝ}, (∀ (x : V), 0 < pi x) → ¬SGC.Bridge.DeterministicLumpability.Descends f P → 1 / 2 ≤ min 1 (↑1 * SGC.Bridge.MachineCertificate.machineDefect f P pi / 2) ∧ ∀ (h : ℕ), 2 ≤ h → min 1 (↑h * SGC.Bridge.MachineCertificate.machineDefect f P pi / 2) = 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.DeterministicLumpability.Descends` (def, SGC.Bridge.DeterministicLumpability): `{V : Type u_1} → [inst : DecidableEq V] → (V → V) → SGC.Partition V → Prop`
    - `SGC.Bridge.MachineCertificate.machineDefect` (def, SGC.Bridge.MachineCertificate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (V → V) → SGC.Partition V → (V → ℝ) → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.MachineCertificate.machineDefect_lt_two`

- statement (kernel-elaborated, sha256 `8d07fe4e8190daa8`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] [Nonempty V] (f : V → V) (P : SGC.Partition V) {pi : V → ℝ}, (∀ (x : V), 0 < pi x) → SGC.Bridge.MachineCertificate.machineDefect f P pi < 2

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.MachineCertificate.machineDefect` (def, SGC.Bridge.MachineCertificate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (V → V) → SGC.Partition V → (V → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.MachineCertificate.machine_error_of_dobrushin_zero`

- statement (kernel-elaborated, sha256 `15f7a72d7206d493`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V) (P : SGC.Partition V) {pi : V → ℝ} (hpi : ∀ (x : V), 0 < pi x), SGC.Bridge.TerminalDecoding.dobrushin (SGC.Thermodynamics.CoarseGenerator (SGC.Bridge.BlockRenormalization.detKernel f) P pi) = 0 → ∀ (x : V) (h : ℕ), 1 ≤ h → ∀ (A : P.Quot), SGC.Bridge.TerminalDecoding.tv (SGC.Bridge.TerminalDecoding.actualLaw (SGC.Bridge.BlockRenormalization.detKernel f) P ⋯ (SGC.Bridge.MachineCertificate.pointMass x) h).mass (SGC.Bridge.TerminalDecoding.referenceLaw (SGC.Bridge.BlockRenormalization.detKernel f) P hpi ⋯ (SGC.Bridge.MachineCertificate.pointMass x) h).mass = 1 - SGC.Thermodynamics.CoarseGenerator (SGC.Bridge.BlockRenormalization.detKernel f) P pi A (P.quot_map (f^[h] x))

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.TerminalDecoding.dobrushin` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.actualLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.BlockRenormalization.detKernel_isStochastic` (theorem, SGC.Bridge.BlockRenormalization): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V), SGC.Renormalization.KernelHorizon.IsStochastic (SGC.Bridge.BlockRenormalization.detKernel f)`
    - `SGC.Bridge.MachineCertificate.pointMass` (def, SGC.Bridge.MachineCertificate): `{V : Type u_1} → [inst : Fintype V] → [DecidableEq V] → V → SGC.Bridge.TerminalDecoding.ProbabilityRow V`
    - `SGC.Bridge.TerminalDecoding.referenceLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → {pi : X → ℝ} → (∀ (x : X), 0 < pi x) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowDifferences` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → Matrix X Y ℝ → Matrix (X × X) Y ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.push` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [inst : Fintype X] → [inst_1 : Fintype Y] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → (M : Matrix X Y ℝ) → SGC.Bridge.TerminalDecoding.RowStochastic M → SGC.Bridge.TerminalDecoding.ProbabilityRow Y`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Renormalization.KernelHorizon.IsStochastic.mk` (ctor, SGC.Renormalization.KernelHorizon): `∀ {V : Type u_1} [inst : Fintype V] {T : Matrix V V ℝ}, (∀ (i j : V), 0 ≤ T i j) → (∀ (i : V), ∑ j, T i j = 1) → SGC.Renormalization.KernelHorizon.IsStochastic T`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`

### `SGC.Bridge.MachineCertificate.machine_point_law`

- statement (kernel-elaborated, sha256 `c2029b6800e44157`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V) (P : SGC.Partition V) (x : V) (h : ℕ) (B : P.Quot), (SGC.Bridge.TerminalDecoding.actualLaw (SGC.Bridge.BlockRenormalization.detKernel f) P ⋯ (SGC.Bridge.MachineCertificate.pointMass x) h).mass B = if P.quot_map (f^[h] x) = B then 1 else 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Bridge.TerminalDecoding.actualLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel_isStochastic` (theorem, SGC.Bridge.BlockRenormalization): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V), SGC.Renormalization.KernelHorizon.IsStochastic (SGC.Bridge.BlockRenormalization.detKernel f)`
    - `SGC.Bridge.MachineCertificate.pointMass` (def, SGC.Bridge.MachineCertificate): `{V : Type u_1} → [inst : Fintype V] → [DecidableEq V] → V → SGC.Bridge.TerminalDecoding.ProbabilityRow V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.push` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [inst : Fintype X] → [inst_1 : Fintype Y] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → (M : Matrix X Y ℝ) → SGC.Bridge.TerminalDecoding.RowStochastic M → SGC.Bridge.TerminalDecoding.ProbabilityRow Y`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Renormalization.KernelHorizon.IsStochastic.mk` (ctor, SGC.Renormalization.KernelHorizon): `∀ {V : Type u_1} [inst : Fintype V] {T : Matrix V V ℝ}, (∀ (i j : V), 0 ≤ T i j) → (∀ (i : V), ∑ j, T i j = 1) → SGC.Renormalization.KernelHorizon.IsStochastic T`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`

### `SGC.Bridge.MachineCertificate.machine_point_reference`

- statement (kernel-elaborated, sha256 `57284109912c5008`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V) (P : SGC.Partition V) {pi : V → ℝ} (hpi : ∀ (x : V), 0 < pi x) (x : V) (h : ℕ) (B : P.Quot), (SGC.Bridge.TerminalDecoding.referenceLaw (SGC.Bridge.BlockRenormalization.detKernel f) P hpi ⋯ (SGC.Bridge.MachineCertificate.pointMass x) h).mass B = (SGC.Thermodynamics.CoarseGenerator (SGC.Bridge.BlockRenormalization.detKernel f) P pi ^ h) (P.quot_map x) B

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Bridge.TerminalDecoding.referenceLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → {pi : X → ℝ} → (∀ (x : X), 0 < pi x) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel_isStochastic` (theorem, SGC.Bridge.BlockRenormalization): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V), SGC.Renormalization.KernelHorizon.IsStochastic (SGC.Bridge.BlockRenormalization.detKernel f)`
    - `SGC.Bridge.MachineCertificate.pointMass` (def, SGC.Bridge.MachineCertificate): `{V : Type u_1} → [inst : Fintype V] → [DecidableEq V] → V → SGC.Bridge.TerminalDecoding.ProbabilityRow V`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.push` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [inst : Fintype X] → [inst_1 : Fintype Y] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → (M : Matrix X Y ℝ) → SGC.Bridge.TerminalDecoding.RowStochastic M → SGC.Bridge.TerminalDecoding.ProbabilityRow Y`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Renormalization.KernelHorizon.IsStochastic.mk` (ctor, SGC.Renormalization.KernelHorizon): `∀ {V : Type u_1} [inst : Fintype V] {T : Matrix V V ℝ}, (∀ (i j : V), 0 ≤ T i j) → (∀ (i : V), ∑ j, T i j = 1) → SGC.Renormalization.KernelHorizon.IsStochastic T`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.MachineCertificate.machine_point_tv_eq_zero_iff`

- statement (kernel-elaborated, sha256 `683a04bd18c21f20`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V) (P : SGC.Partition V) {pi : V → ℝ} (hpi : ∀ (x : V), 0 < pi x) (x : V) (h : ℕ), SGC.Bridge.TerminalDecoding.tv (SGC.Bridge.TerminalDecoding.actualLaw (SGC.Bridge.BlockRenormalization.detKernel f) P ⋯ (SGC.Bridge.MachineCertificate.pointMass x) h).mass (SGC.Bridge.TerminalDecoding.referenceLaw (SGC.Bridge.BlockRenormalization.detKernel f) P hpi ⋯ (SGC.Bridge.MachineCertificate.pointMass x) h).mass = 0 ↔ (SGC.Thermodynamics.CoarseGenerator (SGC.Bridge.BlockRenormalization.detKernel f) P pi ^ h) (P.quot_map x) (P.quot_map (f^[h] x)) = 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.actualLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel_isStochastic` (theorem, SGC.Bridge.BlockRenormalization): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V), SGC.Renormalization.KernelHorizon.IsStochastic (SGC.Bridge.BlockRenormalization.detKernel f)`
    - `SGC.Bridge.MachineCertificate.pointMass` (def, SGC.Bridge.MachineCertificate): `{V : Type u_1} → [inst : Fintype V] → [DecidableEq V] → V → SGC.Bridge.TerminalDecoding.ProbabilityRow V`
    - `SGC.Bridge.TerminalDecoding.referenceLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → {pi : X → ℝ} → (∀ (x : X), 0 < pi x) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.push` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [inst : Fintype X] → [inst_1 : Fintype Y] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → (M : Matrix X Y ℝ) → SGC.Bridge.TerminalDecoding.RowStochastic M → SGC.Bridge.TerminalDecoding.ProbabilityRow Y`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Renormalization.KernelHorizon.IsStochastic.mk` (ctor, SGC.Renormalization.KernelHorizon): `∀ {V : Type u_1} [inst : Fintype V] {T : Matrix V V ℝ}, (∀ (i j : V), 0 ≤ T i j) → (∀ (i : V), ∑ j, T i j = 1) → SGC.Renormalization.KernelHorizon.IsStochastic T`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.MachineCertificate.machine_point_tv_exact`

- statement (kernel-elaborated, sha256 `977dd6cee1f4fc51`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V) (P : SGC.Partition V) {pi : V → ℝ} (hpi : ∀ (x : V), 0 < pi x) (x : V) (h : ℕ), SGC.Bridge.TerminalDecoding.tv (SGC.Bridge.TerminalDecoding.actualLaw (SGC.Bridge.BlockRenormalization.detKernel f) P ⋯ (SGC.Bridge.MachineCertificate.pointMass x) h).mass (SGC.Bridge.TerminalDecoding.referenceLaw (SGC.Bridge.BlockRenormalization.detKernel f) P hpi ⋯ (SGC.Bridge.MachineCertificate.pointMass x) h).mass = 1 - (SGC.Thermodynamics.CoarseGenerator (SGC.Bridge.BlockRenormalization.detKernel f) P pi ^ h) (P.quot_map x) (P.quot_map (f^[h] x))

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.actualLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel_isStochastic` (theorem, SGC.Bridge.BlockRenormalization): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V), SGC.Renormalization.KernelHorizon.IsStochastic (SGC.Bridge.BlockRenormalization.detKernel f)`
    - `SGC.Bridge.MachineCertificate.pointMass` (def, SGC.Bridge.MachineCertificate): `{V : Type u_1} → [inst : Fintype V] → [DecidableEq V] → V → SGC.Bridge.TerminalDecoding.ProbabilityRow V`
    - `SGC.Bridge.TerminalDecoding.referenceLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → {pi : X → ℝ} → (∀ (x : X), 0 < pi x) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.push` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [inst : Fintype X] → [inst_1 : Fintype Y] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → (M : Matrix X Y ℝ) → SGC.Bridge.TerminalDecoding.RowStochastic M → SGC.Bridge.TerminalDecoding.ProbabilityRow Y`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Renormalization.KernelHorizon.IsStochastic.mk` (ctor, SGC.Renormalization.KernelHorizon): `∀ {V : Type u_1} [inst : Fintype V] {T : Matrix V V ℝ}, (∀ (i j : V), 0 ≤ T i j) → (∀ (i : V), ∑ j, T i j = 1) → SGC.Renormalization.KernelHorizon.IsStochastic T`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.MachineCertificate.machine_terminal_reliability`

- statement (kernel-elaborated, sha256 `89867018cb9850e1`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V) (P : SGC.Partition V) {pi : V → ℝ} (hpi : ∀ (x : V), 0 < pi x) (mu : Bool → SGC.Bridge.TerminalDecoding.ProbabilityRow V) (d : SGC.Bridge.TerminalDecoding.Decoder P.Quot) (beta p : Bool → ↑(Set.Icc 0 1)) (h : ℕ), (∀ (b : Bool), d.error (SGC.Bridge.TerminalDecoding.referenceLaw (SGC.Bridge.BlockRenormalization.detKernel f) P hpi ⋯ (mu b) h) b ≤ ↑(beta b)) → (∀ (b : Bool), ↑(beta b) + min 1 (↑h * SGC.Bridge.MachineCertificate.machineDefect f P pi / 2) ≤ ↑(p b)) → ∀ (b : Bool), d.error (SGC.Bridge.TerminalDecoding.actualLaw (SGC.Bridge.BlockRenormalization.detKernel f) P ⋯ (mu b) h) b ≤ ↑(p b)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.Decoder` (inductive, SGC.Bridge.TerminalDecoding): `Type u_4 → Type u_4`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.TerminalDecoding.Decoder.error` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.Decoder X → SGC.Bridge.TerminalDecoding.ProbabilityRow X → Bool → ℝ`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Bridge.TerminalDecoding.referenceLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → {pi : X → ℝ} → (∀ (x : X), 0 < pi x) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel_isStochastic` (theorem, SGC.Bridge.BlockRenormalization): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V), SGC.Renormalization.KernelHorizon.IsStochastic (SGC.Bridge.BlockRenormalization.detKernel f)`
    - `SGC.Bridge.MachineCertificate.machineDefect` (def, SGC.Bridge.MachineCertificate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (V → V) → SGC.Partition V → (V → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.actualLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.loss` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → SGC.Bridge.TerminalDecoding.Decoder X → Bool → X → ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.push` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [inst : Fintype X] → [inst_1 : Fintype Y] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → (M : Matrix X Y ℝ) → SGC.Bridge.TerminalDecoding.RowStochastic M → SGC.Bridge.TerminalDecoding.ProbabilityRow Y`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Renormalization.KernelHorizon.IsStochastic.mk` (ctor, SGC.Renormalization.KernelHorizon): `∀ {V : Type u_1} [inst : Fintype V] {T : Matrix V V ℝ}, (∀ (i j : V), 0 ≤ T i j) → (∀ (i : V), ∑ j, T i j = 1) → SGC.Renormalization.KernelHorizon.IsStochastic T`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.Decoder.probOne` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → SGC.Bridge.TerminalDecoding.Decoder X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.MachineCertificate.machine_terminal_tv`

- statement (kernel-elaborated, sha256 `a959997135cbf84e`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V) (P : SGC.Partition V) {pi : V → ℝ} (hpi : ∀ (x : V), 0 < pi x) (rho : SGC.Bridge.TerminalDecoding.ProbabilityRow V) (h : ℕ), SGC.Bridge.TerminalDecoding.tv (SGC.Bridge.TerminalDecoding.actualLaw (SGC.Bridge.BlockRenormalization.detKernel f) P ⋯ rho h).mass (SGC.Bridge.TerminalDecoding.referenceLaw (SGC.Bridge.BlockRenormalization.detKernel f) P hpi ⋯ rho h).mass ≤ min 1 (↑h * SGC.Bridge.MachineCertificate.machineDefect f P pi / 2)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.actualLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel_isStochastic` (theorem, SGC.Bridge.BlockRenormalization): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V), SGC.Renormalization.KernelHorizon.IsStochastic (SGC.Bridge.BlockRenormalization.detKernel f)`
    - `SGC.Bridge.TerminalDecoding.referenceLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → {pi : X → ℝ} → (∀ (x : X), 0 < pi x) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.MachineCertificate.machineDefect` (def, SGC.Bridge.MachineCertificate): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (V → V) → SGC.Partition V → (V → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.push` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [inst : Fintype X] → [inst_1 : Fintype Y] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → (M : Matrix X Y ℝ) → SGC.Bridge.TerminalDecoding.RowStochastic M → SGC.Bridge.TerminalDecoding.ProbabilityRow Y`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Renormalization.KernelHorizon.IsStochastic.mk` (ctor, SGC.Renormalization.KernelHorizon): `∀ {V : Type u_1} [inst : Fintype V] {T : Matrix V V ℝ}, (∀ (i j : V), 0 ≤ T i j) → (∀ (i : V), ∑ j, T i j = 1) → SGC.Renormalization.KernelHorizon.IsStochastic T`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mk` (ctor, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → (mass : X → ℝ) → (∀ (x : X), 0 ≤ mass x) → ∑ x, mass x = 1 → SGC.Bridge.TerminalDecoding.ProbabilityRow X`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.MachineCertificate.machine_terminal_tv_of_descends`

- statement (kernel-elaborated, sha256 `706c3937c17a1c2f`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V) (P : SGC.Partition V), SGC.Bridge.DeterministicLumpability.Descends f P → ∀ {pi : V → ℝ} (hpi : ∀ (x : V), 0 < pi x) (rho : SGC.Bridge.TerminalDecoding.ProbabilityRow V) (h : ℕ), SGC.Bridge.TerminalDecoding.tv (SGC.Bridge.TerminalDecoding.actualLaw (SGC.Bridge.BlockRenormalization.detKernel f) P ⋯ rho h).mass (SGC.Bridge.TerminalDecoding.referenceLaw (SGC.Bridge.BlockRenormalization.detKernel f) P hpi ⋯ rho h).mass = 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.DeterministicLumpability.Descends` (def, SGC.Bridge.DeterministicLumpability): `{V : Type u_1} → [inst : DecidableEq V] → (V → V) → SGC.Partition V → Prop`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.actualLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel_isStochastic` (theorem, SGC.Bridge.BlockRenormalization): `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V), SGC.Renormalization.KernelHorizon.IsStochastic (SGC.Bridge.BlockRenormalization.detKernel f)`
    - `SGC.Bridge.TerminalDecoding.referenceLaw` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [inst : Fintype X] → [inst_1 : DecidableEq X] → (T : Matrix X X ℝ) → (P : SGC.Partition X) → {pi : X → ℝ} → (∀ (x : X), 0 < pi x) → SGC.Renormalization.KernelHorizon.IsStochastic T → SGC.Bridge.TerminalDecoding.ProbabilityRow X → ℕ → SGC.Bridge.TerminalDecoding.ProbabilityRow P.Quot`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`
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

### `SGC.Bridge.MachineCertificate.mixing_budget_trivial_of_quotient_machine`

- statement (kernel-elaborated, sha256 `a2fe048d91110f79`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V) (P : SGC.Partition V) (hd : SGC.Bridge.DeterministicLumpability.Descends f P) {pi : V → ℝ}, (∀ (x : V), 0 < pi x) → ∀ {A B : P.Quot}, SGC.Bridge.DeterministicLumpability.quotMap f P hd A ≠ SGC.Bridge.DeterministicLumpability.quotMap f P hd B → SGC.Bridge.TerminalDecoding.dobrushin (SGC.Thermodynamics.CoarseGenerator (SGC.Bridge.BlockRenormalization.detKernel f) P pi) = 1

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.DeterministicLumpability.Descends` (def, SGC.Bridge.DeterministicLumpability): `{V : Type u_1} → [inst : DecidableEq V] → (V → V) → SGC.Partition V → Prop`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.DeterministicLumpability.quotMap` (def, SGC.Bridge.DeterministicLumpability): `{V : Type u_1} → [inst : DecidableEq V] → (f : V → V) → (P : SGC.Partition V) → SGC.Bridge.DeterministicLumpability.Descends f P → P.Quot → P.Quot`
    - `SGC.Bridge.TerminalDecoding.dobrushin` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Bridge.TerminalDecoding.rowL1Norm` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype X] → [Fintype Y] → Matrix X Y ℝ → ℝ`
    - `SGC.Bridge.TerminalDecoding.rowDifferences` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → Matrix X Y ℝ → Matrix (X × X) Y ℝ`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.MachineCertificate.pow_row_const_of_rows_equal`

- statement (kernel-elaborated, sha256 `e732c7842741aa1f`):

      ∀ {X : Type u_2} [inst : Fintype X] [inst_1 : DecidableEq X] (M : Matrix X X ℝ), SGC.Bridge.TerminalDecoding.RowStochastic M → (∀ (x y : X), M x = M y) → ∀ (h : ℕ), 1 ≤ h → ∀ (x x' : X), (M ^ h) x = M x'

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.RowStochastic` (inductive, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → {Y : Type u_2} → [Fintype Y] → Matrix X Y ℝ → Prop`

### `SGC.Bridge.MachineCertificate.tmBlock_descends_shrink`

- statement (kernel-elaborated, sha256 `3380f557f056703c`):

      ∀ {Q : Type u_2} {Γ : Type u_3} (nxt : Q → Γ → Q) (w : Q → Γ → Γ) (mv : Q → Γ → ℤ), (∀ (q : Q) (a : Γ), |mv q a| ≤ 1) → ∀ (b : ℕ) {r : ℤ}, ↑b ≤ r → ∀ {c c' : SGC.Bridge.MachineCertificate.TMCfg Q Γ}, SGC.Bridge.MachineCertificate.WindowRel r c c' → SGC.Bridge.MachineCertificate.WindowRel (r - ↑b) ((SGC.Bridge.MachineCertificate.tmStep nxt w mv)^[b] c) ((SGC.Bridge.MachineCertificate.tmStep nxt w mv)^[b] c')

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.MachineCertificate.TMCfg` (def, SGC.Bridge.MachineCertificate): `Type u_4 → Type u_5 → Type (max u_4 u_5)`
    - `SGC.Bridge.MachineCertificate.WindowRel` (def, SGC.Bridge.MachineCertificate): `{Q : Type u_2} → {Γ : Type u_3} → ℤ → SGC.Bridge.MachineCertificate.TMCfg Q Γ → SGC.Bridge.MachineCertificate.TMCfg Q Γ → Prop`
    - `SGC.Bridge.MachineCertificate.tmStep` (def, SGC.Bridge.MachineCertificate): `{Q : Type u_2} → {Γ : Type u_3} → (Q → Γ → Q) → (Q → Γ → Γ) → (Q → Γ → ℤ) → SGC.Bridge.MachineCertificate.TMCfg Q Γ → SGC.Bridge.MachineCertificate.TMCfg Q Γ`
    - `SGC.Bridge.MachineCertificate.AgreeOn` (def, SGC.Bridge.MachineCertificate): `{Γ : Type u_3} → ℤ → (ℤ → Γ) → (ℤ → Γ) → Prop`

### `SGC.Bridge.MachineCertificate.tmStep_iterate_window`

- statement (kernel-elaborated, sha256 `86bda649279f15e1`):

      ∀ {Q : Type u_2} {Γ : Type u_3} (nxt : Q → Γ → Q) (w : Q → Γ → Γ) (mv : Q → Γ → ℤ), (∀ (q : Q) (a : Γ), |mv q a| ≤ 1) → ∀ (b : ℕ) {r : ℤ}, ↑b ≤ r → ∀ {c c' : SGC.Bridge.MachineCertificate.TMCfg Q Γ}, c.1 = c'.1 → SGC.Bridge.MachineCertificate.AgreeOn r c.2 c'.2 → ((SGC.Bridge.MachineCertificate.tmStep nxt w mv)^[b] c).1 = ((SGC.Bridge.MachineCertificate.tmStep nxt w mv)^[b] c').1 ∧ SGC.Bridge.MachineCertificate.AgreeOn (r - ↑b) ((SGC.Bridge.MachineCertificate.tmStep nxt w mv)^[b] c).2 ((SGC.Bridge.MachineCertificate.tmStep nxt w mv)^[b] c').2

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.MachineCertificate.TMCfg` (def, SGC.Bridge.MachineCertificate): `Type u_4 → Type u_5 → Type (max u_4 u_5)`
    - `SGC.Bridge.MachineCertificate.AgreeOn` (def, SGC.Bridge.MachineCertificate): `{Γ : Type u_3} → ℤ → (ℤ → Γ) → (ℤ → Γ) → Prop`
    - `SGC.Bridge.MachineCertificate.tmStep` (def, SGC.Bridge.MachineCertificate): `{Q : Type u_2} → {Γ : Type u_3} → (Q → Γ → Q) → (Q → Γ → Γ) → (Q → Γ → ℤ) → SGC.Bridge.MachineCertificate.TMCfg Q Γ → SGC.Bridge.MachineCertificate.TMCfg Q Γ`

### `SGC.Bridge.MachineCertificate.tmStep_window`

- statement (kernel-elaborated, sha256 `d32a1cebb8ee6a4e`):

      ∀ {Q : Type u_2} {Γ : Type u_3} (nxt : Q → Γ → Q) (w : Q → Γ → Γ) (mv : Q → Γ → ℤ), (∀ (q : Q) (a : Γ), |mv q a| ≤ 1) → ∀ {r : ℤ}, 0 ≤ r → ∀ {c c' : SGC.Bridge.MachineCertificate.TMCfg Q Γ}, c.1 = c'.1 → SGC.Bridge.MachineCertificate.AgreeOn r c.2 c'.2 → (SGC.Bridge.MachineCertificate.tmStep nxt w mv c).1 = (SGC.Bridge.MachineCertificate.tmStep nxt w mv c').1 ∧ SGC.Bridge.MachineCertificate.AgreeOn (r - 1) (SGC.Bridge.MachineCertificate.tmStep nxt w mv c).2 (SGC.Bridge.MachineCertificate.tmStep nxt w mv c').2

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.MachineCertificate.TMCfg` (def, SGC.Bridge.MachineCertificate): `Type u_4 → Type u_5 → Type (max u_4 u_5)`
    - `SGC.Bridge.MachineCertificate.AgreeOn` (def, SGC.Bridge.MachineCertificate): `{Γ : Type u_3} → ℤ → (ℤ → Γ) → (ℤ → Γ) → Prop`
    - `SGC.Bridge.MachineCertificate.tmStep` (def, SGC.Bridge.MachineCertificate): `{Q : Type u_2} → {Γ : Type u_3} → (Q → Γ → Q) → (Q → Γ → Γ) → (Q → Γ → ℤ) → SGC.Bridge.MachineCertificate.TMCfg Q Γ → SGC.Bridge.MachineCertificate.TMCfg Q Γ`

### `SGC.Bridge.MachineCertificate.tv_point_prob`

- statement (kernel-elaborated, sha256 `a810ebdbe260abf9`):

      ∀ {X : Type u_2} [inst : Fintype X] [inst_1 : DecidableEq X] (x0 : X) (rho : SGC.Bridge.TerminalDecoding.ProbabilityRow X), SGC.Bridge.TerminalDecoding.tv (fun y => if y = x0 then 1 else 0) rho.mass = 1 - rho.mass x0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.TerminalDecoding.ProbabilityRow` (inductive, SGC.Bridge.TerminalDecoding): `(X : Type u_4) → [Fintype X] → Type u_4`
    - `SGC.Bridge.TerminalDecoding.tv` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → (X → ℝ) → ℝ`
    - `SGC.Bridge.TerminalDecoding.ProbabilityRow.mass` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_4} → [inst : Fintype X] → SGC.Bridge.TerminalDecoding.ProbabilityRow X → X → ℝ`
    - `SGC.Bridge.TerminalDecoding.l1` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → (X → ℝ) → ℝ`

### `SGC.Bridge.MachineCertificate.windowRel_equivalence`

- statement (kernel-elaborated, sha256 `4ec70e3eaacf4900`):

      ∀ {Q : Type u_2} {Γ : Type u_3} (r : ℤ), Equivalence (SGC.Bridge.MachineCertificate.WindowRel r)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.MachineCertificate.TMCfg` (def, SGC.Bridge.MachineCertificate): `Type u_4 → Type u_5 → Type (max u_4 u_5)`
    - `SGC.Bridge.MachineCertificate.WindowRel` (def, SGC.Bridge.MachineCertificate): `{Q : Type u_2} → {Γ : Type u_3} → ℤ → SGC.Bridge.MachineCertificate.TMCfg Q Γ → SGC.Bridge.MachineCertificate.TMCfg Q Γ → Prop`
    - `SGC.Bridge.MachineCertificate.AgreeOn` (def, SGC.Bridge.MachineCertificate): `{Γ : Type u_3} → ℤ → (ℤ → Γ) → (ℤ → Γ) → Prop`

## Trust surface (project axioms)

| axiom | type | consumers | unconstrained numeric params |
|---|---|---|---|
| `SGC.Approximate.rowsum_to_opNorm_bound` | `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (ε : ℝ), 0 ≤ ε → SGC.IsRowSumApproxLumpable L P ε → SGC.opNorm_pi pi_dist hπ (SGC.Approximate.DefectOperator L P pi_dist hπ) ≤ ↑(Fintype.card V) * ε` | 1 | - |
| `SGC.Approximate.Weyl_inequality_pi` | `∀ {V : Type u_1} [inst : Fintype V] (A B : (V → ℝ) →ₗ[ℝ] V → ℝ) (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (k : ℕ), SGC.Approximate.IsSelfAdjoint_pi A pi_dist → SGC.Approximate.IsSelfAdjoint_pi B pi_dist → ∃ eigenvalue_k, |eigenvalue_k A - eigenvalue_k B| ≤ SGC.opNorm_pi pi_dist hπ (A - B)` | 0 | - |
| `SGC.Approximate.NCD_defect_split` | `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L L_fast L_slow : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (ε γ : ℝ), SGC.Approximate.IsNCD L L_fast L_slow P pi_dist hπ ε γ → SGC.Approximate.DefectOperator L P pi_dist hπ = ε • SGC.Approximate.DefectOperator L_slow P pi_dist hπ` | 0 | - |
| `SGC.Approximate.NCD_integral_bound` | `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L L_fast L_slow : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ) (hπ : ∀ (v : V), 0 < pi_dist v) (ε γ : ℝ), SGC.Approximate.IsNCD L L_fast L_slow P pi_dist hπ ε γ → ∀ (t : ℝ), 0 ≤ t → ∀ (f₀ : V → ℝ), f₀ = (SGC.Approximate.CoarseProjector P pi_dist hπ) f₀ → ∀ (M : ℝ), 0 ≤ M → (∀ (s : ℝ), 0 ≤ s → s ≤ t → SGC.norm_pi pi_dist ((SGC.Approximate.DefectOperator L P pi_dist hπ) ((SGC.Approximate.CoarseProjector P pi_dist hπ) ((SGC.Approximate.HeatKernelMap L s) f₀))) ≤ M * SGC.norm_pi pi_dist f₀) → SGC.norm_pi pi_dist ((SGC.Approximate.HeatKernelMap L t) f₀ - (SGC.Approximate.CoarseProjector P pi_dist hπ) ((SGC.Approximate.HeatKernelMap L t) f₀)) ≤ M / γ * SGC.norm_pi pi_dist f₀` | 0 | - |
| `SGC.Thermodynamics.hidden_entropy_bound_from_trajectory` | `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ) (hπ : ∀ (x : V), 0 < pi_dist x) (ε : ℝ), 0 ≤ ε → SGC.Approximate.IsApproxLumpable L P pi_dist hπ ε → ∀ (C_traj : ℝ), 0 < C_traj → SGC.Thermodynamics.HiddenEntropyProduction L P pi_dist ≤ ↑(Fintype.card V) * C_traj ^ 2 * ε ^ 2` | 1 | - |
| `SGC.Thermodynamics.gaspard_path_space_identity` | `∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (L : Matrix V V ℝ) (P : SGC.Partition V) (pi_dist : V → ℝ) (hπ : ∀ (x : V), 0 < pi_dist x), (∀ (x y : V), x ≠ y → 0 ≤ L x y) → (∀ (v : V), ∑ u, pi_dist u * L u v = 0) → ∀ γ > 0, γ ≤ SGC.DirichletGap L pi_dist → γ * SGC.opNorm_pi pi_dist hπ (SGC.Approximate.DefectOperator L P pi_dist hπ) ^ 2 ≤ SGC.Thermodynamics.HiddenEntropyProduction L P pi_dist` | 2 | - |
| `SGC.Thermodynamics.non_normality_from_flux` | `∀ {V : Type u_1} [inst : Fintype V] (L : Matrix V V ℝ) (pi_dist : V → ℝ), (∀ (v : V), 0 < pi_dist v) → ∃ C > 0, ∀ (x y : V), |SGC.Thermodynamics.NonNormalityCommutator L pi_dist x y| ≤ C * ∑ z, |SGC.Thermodynamics.AntisymmetricPart L pi_dist x z| * |SGC.Thermodynamics.AntisymmetricPart L pi_dist z y|` | 0 | - |

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
