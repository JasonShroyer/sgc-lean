# lean-triage report: REVIEW

- receipt: `lean-triage-71ef010b1b24-20260912T215134Z`  (hash_self `1bb8691f6e082666...`)
- tool: lean-triage 0.2.1 (source `7e7d28e056e9`, probe `7e0354b09345`)
- repo: https://github.com/JasonShroyer/sgc-lean.git
- commit: df242c3682f33f198bb70c3f892a124664188cda  dirty=True
- toolchain: leanprover/lean4:v4.25.2
- source tree sha256: `71ef010b1b248ecf127c2efd5a11a4cedae21fda2fad56bd285c26f4b97c5703`
- modules: SGC.Bridge.AbstractBKM

## Verdict

**REVIEW** - 0 fail, 15 warn, 27 info.

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
| warn | heuristic | F10 | NARRATIVE_CLAIM_NEEDS_HUMAN_MAP | - | strong-claim vocabulary 'Millennium' appears 2x (THEORY.md:175, docs/bkm-formalization-design.md:41); a human must map the formal statements to it |
| warn | heuristic | F10 | NARRATIVE_CLAIM_NEEDS_HUMAN_MAP | - | strong-claim vocabulary 'Navier-Stokes' appears 4x (PRIORITY_CLAIMS.md:93, PRIORITY_CLAIMS.md:95, docs/bkm-formalization-design.md:46, ...); a human must map the formal statements to it |
| warn | heuristic | F10 | NARRATIVE_CLAIM_NEEDS_HUMAN_MAP | - | strong-claim vocabulary 'Riemann' appears 26x (CHANGELOG.md:164, RESEARCH_JOURNAL.md:90, VERIFIED_CORE_MANIFEST.md:381, ...); a human must map the formal statements to it |
| warn | heuristic | F10 | NARRATIVE_CLAIM_NEEDS_HUMAN_MAP | - | strong-claim vocabulary 'fully verified' appears 5x (README.md:37, VERIFIED_CORE_MANIFEST.md:52, VERIFIED_CORE_MANIFEST.md:117, ...); a human must map the formal statements to it |
| warn | heuristic | F10 | NARRATIVE_CLAIM_NEEDS_HUMAN_MAP | - | strong-claim vocabulary 'settles' appears 3x (decisions/0016-curvature-descends-along-lumpable-quotients.md:50, reports/PHASE_4A_CANONICAL_WAVELET_FISHER_RAO_INTEGRATION.md:249, theory_context/SGC UPAT Methods Deep Dive.md:211); a human must map the formal statements to it |
| warn | heuristic | F10 | NARRATIVE_CLAIM_NEEDS_HUMAN_MAP | - | strong-claim vocabulary 'unconditional' appears 10x (RESEARCH_JOURNAL.md:285, RESEARCH_JOURNAL.md:567, RESEARCH_JOURNAL.md:816, ...); a human must map the formal statements to it |
| warn | process | F13 | TOOLCHAIN_ADVISORY | - | toolchain leanprover/lean4:v4.25.2 is below 4.32.2: Kernel soundness bug (nested inductive types with phantom parameters) allowed an axiom-free proof of False; #print axioms reported nothing. Fixed in Lean 4.32.2. |
| warn | process | F13 | TOOLCHAIN_ADVISORY | - | toolchain leanprover/lean4:v4.25.2 is below 4.32.2: Runtime reference-count overflow path that could corrupt memory and yield False (reported in the 2026 soundness-bug hunt). |
| info | witness | F07 | AUTOMATION_CLOSES_TARGET_UNDER_POLICY | SGC.Bridge.AbstractBKM.budget_zero | the configured automation policy closes the statement (`simp`); legitimate, but weigh against any strong narrative |
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
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.AbstractBKM.bounded_of_budget_le | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.AbstractBKM.budget_zero | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.AbstractBKM.exists_budget_gt_of_norm_gt | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.AbstractBKM.hasDerivAt_budget | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.AbstractBKM.norm_le_barrier_of_budget_control | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.AbstractBKM.norm_le_exp_budget | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.AbstractBKM.bounded_of_budget_le | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.AbstractBKM.budget_zero | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.AbstractBKM.exists_budget_gt_of_norm_gt | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.AbstractBKM.hasDerivAt_budget | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.AbstractBKM.norm_le_barrier_of_budget_control | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.AbstractBKM.norm_le_exp_budget | 1 project-local definition(s) determine what this theorem is about; read them |

## Per-theorem receipt

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

## Trust surface (project axioms)

none declared in the loaded project modules

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
