# lean-triage report: REVIEW

- receipt: `lean-triage-68bb4a04b60d-20260913T231606Z`  (hash_self `259a67ff2c1e1fe8...`)
- tool: lean-triage 0.2.1 (source `25bc5fa54832`, probe `36fb8cd228cf`)
- repo: https://github.com/JasonShroyer/sgc-lean.git
- commit: 4aa50546f7c335f8f444fcc698449b17f86ee701  dirty=True
- toolchain: leanprover/lean4:v4.25.2
- source tree sha256: `68bb4a04b60db071e9f0d9b90e797b8b2b394ab7c25982c6d22b25d80f5b0b1c`
- modules: SGC.Bridge.DeterministicLumpability

## Verdict

**REVIEW** - 0 fail, 15 warn, 56 info.

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
| info | witness | F07 | AUTOMATION_CLOSES_TARGET_UNDER_POLICY | SGC.Bridge.DeterministicLumpability.Regression.byState_rel | the configured automation policy closes the statement (`rfl`); legitimate, but weigh against any strong narrative |
| info | witness | F07 | AUTOMATION_CLOSES_TARGET_UNDER_POLICY | SGC.Bridge.DeterministicLumpability.quotMap_mk | the configured automation policy closes the statement (`rfl`); legitimate, but weigh against any strong narrative |
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
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DeterministicLumpability.Descends.iterate | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DeterministicLumpability.Regression.byState_rel | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DeterministicLumpability.Regression.oblivious_defect_zero | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DeterministicLumpability.Regression.oblivious_descends | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DeterministicLumpability.Regression.oblivious_stronglyLumpable | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DeterministicLumpability.Regression.reader_commutator_ne_zero | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DeterministicLumpability.Regression.reader_defect_pos | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DeterministicLumpability.Regression.reader_not_descends | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DeterministicLumpability.Regression.reader_not_stronglyLumpable | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DeterministicLumpability.closureCommutator_detKernel_eq_zero_iff | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DeterministicLumpability.coarseGenerator_detKernel_eq | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DeterministicLumpability.defectSq_detKernel_eq_zero_iff | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DeterministicLumpability.detKernel_pow_stronglyLumpable | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DeterministicLumpability.detKernel_stronglyLumpable_iff | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DeterministicLumpability.eternal_closure_detKernel | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DeterministicLumpability.quotMap_iterate | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DeterministicLumpability.quotMap_mk | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DeterministicLumpability.quot_map_eq_iff | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.DeterministicLumpability.row_sum_block_detKernel | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DeterministicLumpability.Descends.iterate | 3 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DeterministicLumpability.Regression.byState_rel | 5 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DeterministicLumpability.Regression.oblivious_defect_zero | 18 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DeterministicLumpability.Regression.oblivious_descends | 7 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DeterministicLumpability.Regression.oblivious_stronglyLumpable | 12 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DeterministicLumpability.Regression.reader_commutator_ne_zero | 17 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DeterministicLumpability.Regression.reader_defect_pos | 18 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DeterministicLumpability.Regression.reader_not_descends | 7 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DeterministicLumpability.Regression.reader_not_stronglyLumpable | 12 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DeterministicLumpability.closureCommutator_detKernel_eq_zero_iff | 14 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DeterministicLumpability.coarseGenerator_detKernel_eq | 12 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DeterministicLumpability.defectSq_detKernel_eq_zero_iff | 15 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DeterministicLumpability.detKernel_pow_stronglyLumpable | 9 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DeterministicLumpability.detKernel_stronglyLumpable_iff | 9 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DeterministicLumpability.eternal_closure_detKernel | 11 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DeterministicLumpability.quotMap_iterate | 7 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DeterministicLumpability.quotMap_mk | 6 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DeterministicLumpability.quot_map_eq_iff | 4 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.DeterministicLumpability.row_sum_block_detKernel | 8 project-local definition(s) determine what this theorem is about; read them |

## Per-theorem receipt

### `SGC.Bridge.DeterministicLumpability.Descends.iterate`

- statement (kernel-elaborated, sha256 `526228ae57a58f48`):

      ∀ {V : Type u_1} [inst : DecidableEq V] {f : V → V} {P : SGC.Partition V}, SGC.Bridge.DeterministicLumpability.Descends f P → ∀ (b : ℕ), SGC.Bridge.DeterministicLumpability.Descends f^[b] P

- axioms: Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.DeterministicLumpability.Descends` (def, SGC.Bridge.DeterministicLumpability): `{V : Type u_1} → [inst : DecidableEq V] → (V → V) → SGC.Partition V → Prop`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`

### `SGC.Bridge.DeterministicLumpability.Regression.byState_rel`

- statement (kernel-elaborated, sha256 `584cf36d3f2db291`):

      ∀ (x y : SGC.Bridge.DeterministicLumpability.Regression.Cfg), SGC.Bridge.DeterministicLumpability.Regression.byState.rel x y ↔ x.1 = y.1

- axioms: none
- unused hypotheses: none
- automation: trivial_by=rfl vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DeterministicLumpability.Regression.Cfg` (def, SGC.Bridge.DeterministicLumpability): `Type`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Bridge.DeterministicLumpability.Regression.byState` (def, SGC.Bridge.DeterministicLumpability): `SGC.Partition SGC.Bridge.DeterministicLumpability.Regression.Cfg`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`

### `SGC.Bridge.DeterministicLumpability.Regression.oblivious_defect_zero`

- statement (kernel-elaborated, sha256 `58e1cc8dc6c6e9a2`):

      ∀ {pi : SGC.Bridge.DeterministicLumpability.Regression.Cfg → ℝ}, (∀ (x : SGC.Bridge.DeterministicLumpability.Regression.Cfg), 0 < pi x) → SGC.Renormalization.MeasureReentry.defectSq (SGC.Bridge.BlockRenormalization.detKernel SGC.Bridge.DeterministicLumpability.Regression.oblivious) SGC.Bridge.DeterministicLumpability.Regression.byState pi = 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DeterministicLumpability.Regression.Cfg` (def, SGC.Bridge.DeterministicLumpability): `Type`
    - `SGC.Renormalization.MeasureReentry.defectSq` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (V → ℝ) → ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Bridge.DeterministicLumpability.Regression.oblivious` (def, SGC.Bridge.DeterministicLumpability): `SGC.Bridge.DeterministicLumpability.Regression.Cfg → SGC.Bridge.DeterministicLumpability.Regression.Cfg`
    - `SGC.Bridge.DeterministicLumpability.Regression.byState` (def, SGC.Bridge.DeterministicLumpability): `SGC.Partition SGC.Bridge.DeterministicLumpability.Regression.Cfg`
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

### `SGC.Bridge.DeterministicLumpability.Regression.oblivious_descends`

- statement (kernel-elaborated, sha256 `d664a57bf3c6c70e`):

      SGC.Bridge.DeterministicLumpability.Descends SGC.Bridge.DeterministicLumpability.Regression.oblivious SGC.Bridge.DeterministicLumpability.Regression.byState

- axioms: propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DeterministicLumpability.Descends` (def, SGC.Bridge.DeterministicLumpability): `{V : Type u_1} → [inst : DecidableEq V] → (V → V) → SGC.Partition V → Prop`
    - `SGC.Bridge.DeterministicLumpability.Regression.Cfg` (def, SGC.Bridge.DeterministicLumpability): `Type`
    - `SGC.Bridge.DeterministicLumpability.Regression.oblivious` (def, SGC.Bridge.DeterministicLumpability): `SGC.Bridge.DeterministicLumpability.Regression.Cfg → SGC.Bridge.DeterministicLumpability.Regression.Cfg`
    - `SGC.Bridge.DeterministicLumpability.Regression.byState` (def, SGC.Bridge.DeterministicLumpability): `SGC.Partition SGC.Bridge.DeterministicLumpability.Regression.Cfg`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`

### `SGC.Bridge.DeterministicLumpability.Regression.oblivious_stronglyLumpable`

- statement (kernel-elaborated, sha256 `333201cdd2201a10`):

      SGC.IsStronglyLumpable (SGC.Bridge.BlockRenormalization.detKernel SGC.Bridge.DeterministicLumpability.Regression.oblivious) SGC.Bridge.DeterministicLumpability.Regression.byState

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.IsStronglyLumpable` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → Prop`
    - `SGC.Bridge.DeterministicLumpability.Regression.Cfg` (def, SGC.Bridge.DeterministicLumpability): `Type`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Bridge.DeterministicLumpability.Regression.oblivious` (def, SGC.Bridge.DeterministicLumpability): `SGC.Bridge.DeterministicLumpability.Regression.Cfg → SGC.Bridge.DeterministicLumpability.Regression.Cfg`
    - `SGC.Bridge.DeterministicLumpability.Regression.byState` (def, SGC.Bridge.DeterministicLumpability): `SGC.Partition SGC.Bridge.DeterministicLumpability.Regression.Cfg`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.DeterministicLumpability.Regression.reader_commutator_ne_zero`

- statement (kernel-elaborated, sha256 `3265daf9e8cf4317`):

      ∀ {pi : SGC.Bridge.DeterministicLumpability.Regression.Cfg → ℝ}, (∀ (x : SGC.Bridge.DeterministicLumpability.Regression.Cfg), 0 < pi x) → SGC.Renormalization.MeasureReentry.closureCommutator (SGC.Bridge.BlockRenormalization.detKernel SGC.Bridge.DeterministicLumpability.Regression.reader) SGC.Bridge.DeterministicLumpability.Regression.byState pi ≠ 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DeterministicLumpability.Regression.Cfg` (def, SGC.Bridge.DeterministicLumpability): `Type`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.DeterministicLumpability.Regression.byState` (def, SGC.Bridge.DeterministicLumpability): `SGC.Partition SGC.Bridge.DeterministicLumpability.Regression.Cfg`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Bridge.DeterministicLumpability.Regression.reader` (def, SGC.Bridge.DeterministicLumpability): `SGC.Bridge.DeterministicLumpability.Regression.Cfg → SGC.Bridge.DeterministicLumpability.Regression.Cfg`
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

### `SGC.Bridge.DeterministicLumpability.Regression.reader_defect_pos`

- statement (kernel-elaborated, sha256 `38add8608eecbe68`):

      ∀ {pi : SGC.Bridge.DeterministicLumpability.Regression.Cfg → ℝ}, (∀ (x : SGC.Bridge.DeterministicLumpability.Regression.Cfg), 0 < pi x) → 0 < SGC.Renormalization.MeasureReentry.defectSq (SGC.Bridge.BlockRenormalization.detKernel SGC.Bridge.DeterministicLumpability.Regression.reader) SGC.Bridge.DeterministicLumpability.Regression.byState pi

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DeterministicLumpability.Regression.Cfg` (def, SGC.Bridge.DeterministicLumpability): `Type`
    - `SGC.Renormalization.MeasureReentry.defectSq` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (V → ℝ) → ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Bridge.DeterministicLumpability.Regression.reader` (def, SGC.Bridge.DeterministicLumpability): `SGC.Bridge.DeterministicLumpability.Regression.Cfg → SGC.Bridge.DeterministicLumpability.Regression.Cfg`
    - `SGC.Bridge.DeterministicLumpability.Regression.byState` (def, SGC.Bridge.DeterministicLumpability): `SGC.Partition SGC.Bridge.DeterministicLumpability.Regression.Cfg`
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

### `SGC.Bridge.DeterministicLumpability.Regression.reader_not_descends`

- statement (kernel-elaborated, sha256 `0675633376b3c8dc`):

      ¬SGC.Bridge.DeterministicLumpability.Descends SGC.Bridge.DeterministicLumpability.Regression.reader SGC.Bridge.DeterministicLumpability.Regression.byState

- axioms: propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.DeterministicLumpability.Descends` (def, SGC.Bridge.DeterministicLumpability): `{V : Type u_1} → [inst : DecidableEq V] → (V → V) → SGC.Partition V → Prop`
    - `SGC.Bridge.DeterministicLumpability.Regression.Cfg` (def, SGC.Bridge.DeterministicLumpability): `Type`
    - `SGC.Bridge.DeterministicLumpability.Regression.reader` (def, SGC.Bridge.DeterministicLumpability): `SGC.Bridge.DeterministicLumpability.Regression.Cfg → SGC.Bridge.DeterministicLumpability.Regression.Cfg`
    - `SGC.Bridge.DeterministicLumpability.Regression.byState` (def, SGC.Bridge.DeterministicLumpability): `SGC.Partition SGC.Bridge.DeterministicLumpability.Regression.Cfg`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`

### `SGC.Bridge.DeterministicLumpability.Regression.reader_not_stronglyLumpable`

- statement (kernel-elaborated, sha256 `8ec04de88148a198`):

      ¬SGC.IsStronglyLumpable (SGC.Bridge.BlockRenormalization.detKernel SGC.Bridge.DeterministicLumpability.Regression.reader) SGC.Bridge.DeterministicLumpability.Regression.byState

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.IsStronglyLumpable` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → Prop`
    - `SGC.Bridge.DeterministicLumpability.Regression.Cfg` (def, SGC.Bridge.DeterministicLumpability): `Type`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Bridge.DeterministicLumpability.Regression.reader` (def, SGC.Bridge.DeterministicLumpability): `SGC.Bridge.DeterministicLumpability.Regression.Cfg → SGC.Bridge.DeterministicLumpability.Regression.Cfg`
    - `SGC.Bridge.DeterministicLumpability.Regression.byState` (def, SGC.Bridge.DeterministicLumpability): `SGC.Partition SGC.Bridge.DeterministicLumpability.Regression.Cfg`
    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Partition.mk` (ctor, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (rel : Setoid V) → DecidableRel ⇑rel → SGC.Partition V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.DeterministicLumpability.closureCommutator_detKernel_eq_zero_iff`

- statement (kernel-elaborated, sha256 `374fe4332a00d578`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V) (P : SGC.Partition V) {pi : V → ℝ}, (∀ (x : V), 0 < pi x) → (SGC.Renormalization.MeasureReentry.closureCommutator (SGC.Bridge.BlockRenormalization.detKernel f) P pi = 0 ↔ SGC.Bridge.DeterministicLumpability.Descends f P)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Renormalization.MeasureReentry.closureCommutator` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix V P.Quot ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Bridge.DeterministicLumpability.Descends` (def, SGC.Bridge.DeterministicLumpability): `{V : Type u_1} → [inst : DecidableEq V] → (V → V) → SGC.Partition V → Prop`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.DeterministicLumpability.coarseGenerator_detKernel_eq`

- statement (kernel-elaborated, sha256 `26e44edecfe23077`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V) (P : SGC.Partition V) (h : SGC.Bridge.DeterministicLumpability.Descends f P) {pi : V → ℝ}, (∀ (x : V), 0 < pi x) → SGC.Thermodynamics.CoarseGenerator (SGC.Bridge.BlockRenormalization.detKernel f) P pi = SGC.Bridge.BlockRenormalization.detKernel (SGC.Bridge.DeterministicLumpability.quotMap f P h)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.DeterministicLumpability.Descends` (def, SGC.Bridge.DeterministicLumpability): `{V : Type u_1} → [inst : DecidableEq V] → (V → V) → SGC.Partition V → Prop`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Bridge.DeterministicLumpability.quotMap` (def, SGC.Bridge.DeterministicLumpability): `{V : Type u_1} → [inst : DecidableEq V] → (f : V → V) → (P : SGC.Partition V) → SGC.Bridge.DeterministicLumpability.Descends f P → P.Quot → P.Quot`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.DeterministicLumpability.defectSq_detKernel_eq_zero_iff`

- statement (kernel-elaborated, sha256 `b5e65b4e8ec1857d`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V) (P : SGC.Partition V) {pi : V → ℝ}, (∀ (x : V), 0 < pi x) → (SGC.Renormalization.MeasureReentry.defectSq (SGC.Bridge.BlockRenormalization.detKernel f) P pi = 0 ↔ SGC.Bridge.DeterministicLumpability.Descends f P)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Renormalization.MeasureReentry.defectSq` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → (V → ℝ) → ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Bridge.DeterministicLumpability.Descends` (def, SGC.Bridge.DeterministicLumpability): `{V : Type u_1} → [inst : DecidableEq V] → (V → V) → SGC.Partition V → Prop`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Renormalization.MeasureReentry.residual` (def, SGC.Renormalization.MeasureReentry): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → V → P.Quot → ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.row_sum_block` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → V → P.Quot → ℝ`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.DeterministicLumpability.detKernel_pow_stronglyLumpable`

- statement (kernel-elaborated, sha256 `6b9194a430418e30`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V) (P : SGC.Partition V), SGC.Bridge.DeterministicLumpability.Descends f P → ∀ (b : ℕ), SGC.IsStronglyLumpable (SGC.Bridge.BlockRenormalization.detKernel f ^ b) P

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.DeterministicLumpability.Descends` (def, SGC.Bridge.DeterministicLumpability): `{V : Type u_1} → [inst : DecidableEq V] → (V → V) → SGC.Partition V → Prop`
    - `SGC.IsStronglyLumpable` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → Prop`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.DeterministicLumpability.detKernel_stronglyLumpable_iff`

- statement (kernel-elaborated, sha256 `78b2f0209d07f2c6`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V) (P : SGC.Partition V), SGC.IsStronglyLumpable (SGC.Bridge.BlockRenormalization.detKernel f) P ↔ SGC.Bridge.DeterministicLumpability.Descends f P

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.IsStronglyLumpable` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → SGC.Partition V → Prop`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Bridge.DeterministicLumpability.Descends` (def, SGC.Bridge.DeterministicLumpability): `{V : Type u_1} → [inst : DecidableEq V] → (V → V) → SGC.Partition V → Prop`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.DeterministicLumpability.eternal_closure_detKernel`

- statement (kernel-elaborated, sha256 `a10f0ac42ad1a06a`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V) (P : SGC.Partition V) (h : SGC.Bridge.DeterministicLumpability.Descends f P) {pi : V → ℝ}, (∀ (x : V), 0 < pi x) → ∀ (n : ℕ), SGC.Bridge.BlockRenormalization.detKernel f ^ n * SGC.lift_matrix P = SGC.lift_matrix P * SGC.Bridge.BlockRenormalization.detKernel (SGC.Bridge.DeterministicLumpability.quotMap f P h) ^ n

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.DeterministicLumpability.Descends` (def, SGC.Bridge.DeterministicLumpability): `{V : Type u_1} → [inst : DecidableEq V] → (V → V) → SGC.Partition V → Prop`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Bridge.DeterministicLumpability.quotMap` (def, SGC.Bridge.DeterministicLumpability): `{V : Type u_1} → [inst : DecidableEq V] → (f : V → V) → (P : SGC.Partition V) → SGC.Bridge.DeterministicLumpability.Descends f P → P.Quot → P.Quot`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

### `SGC.Bridge.DeterministicLumpability.quotMap_iterate`

- statement (kernel-elaborated, sha256 `5fadbd7eee64bc5b`):

      ∀ {V : Type u_1} [inst : DecidableEq V] (f : V → V) (P : SGC.Partition V) (h : SGC.Bridge.DeterministicLumpability.Descends f P) (b : ℕ), SGC.Bridge.DeterministicLumpability.quotMap f^[b] P ⋯ = (SGC.Bridge.DeterministicLumpability.quotMap f P h)^[b]

- axioms: Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.DeterministicLumpability.Descends` (def, SGC.Bridge.DeterministicLumpability): `{V : Type u_1} → [inst : DecidableEq V] → (V → V) → SGC.Partition V → Prop`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.DeterministicLumpability.quotMap` (def, SGC.Bridge.DeterministicLumpability): `{V : Type u_1} → [inst : DecidableEq V] → (f : V → V) → (P : SGC.Partition V) → SGC.Bridge.DeterministicLumpability.Descends f P → P.Quot → P.Quot`
    - `SGC.Bridge.DeterministicLumpability.Descends.iterate` (theorem, SGC.Bridge.DeterministicLumpability): `∀ {V : Type u_1} [inst : DecidableEq V] {f : V → V} {P : SGC.Partition V}, SGC.Bridge.DeterministicLumpability.Descends f P → ∀ (b : ℕ), SGC.Bridge.DeterministicLumpability.Descends f^[b] P`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`

### `SGC.Bridge.DeterministicLumpability.quotMap_mk`

- statement (kernel-elaborated, sha256 `4d0ff21cd015685e`):

      ∀ {V : Type u_1} [inst : DecidableEq V] (f : V → V) (P : SGC.Partition V) (h : SGC.Bridge.DeterministicLumpability.Descends f P) (x : V), SGC.Bridge.DeterministicLumpability.quotMap f P h (P.quot_map x) = P.quot_map (f x)

- axioms: Quot.sound [lean-core]
- unused hypotheses: none
- automation: trivial_by=rfl vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Bridge.DeterministicLumpability.Descends` (def, SGC.Bridge.DeterministicLumpability): `{V : Type u_1} → [inst : DecidableEq V] → (V → V) → SGC.Partition V → Prop`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.DeterministicLumpability.quotMap` (def, SGC.Bridge.DeterministicLumpability): `{V : Type u_1} → [inst : DecidableEq V] → (f : V → V) → (P : SGC.Partition V) → SGC.Bridge.DeterministicLumpability.Descends f P → P.Quot → P.Quot`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`

### `SGC.Bridge.DeterministicLumpability.quot_map_eq_iff`

- statement (kernel-elaborated, sha256 `1aab190ab89f68b1`):

      ∀ {V : Type u_1} [inst : DecidableEq V] (P : SGC.Partition V) (x y : V), P.quot_map x = P.quot_map y ↔ P.rel x y

- axioms: Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`

### `SGC.Bridge.DeterministicLumpability.row_sum_block_detKernel`

- statement (kernel-elaborated, sha256 `9d29fcdefcfc07a1`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V) (P : SGC.Partition V) (x : V) (B : P.Quot), SGC.row_sum_block (SGC.Bridge.BlockRenormalization.detKernel f) P x B = if P.quot_map (f x) = B then 1 else 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.row_sum_block` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → V → P.Quot → ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`

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
