# lean-triage report: REVIEW

- receipt: `lean-triage-e89d3677eb8e-20260913T014427Z`  (hash_self `19ac344976d2c6d6...`)
- tool: lean-triage 0.2.1 (source `7e7d28e056e9`, probe `a1b7c82824c9`)
- repo: https://github.com/JasonShroyer/sgc-lean.git
- commit: 0012a5a5b16f7e4e26465e84c3772627a17a5fd0  dirty=True
- toolchain: leanprover/lean4:v4.25.2
- source tree sha256: `e89d3677eb8e5f4786260c363c42abee52e585bdc414c8f76b8fe057b8fbdb1c`
- modules: SGC.Bridge.ResidualHorizon

## Verdict

**REVIEW** - 0 fail, 16 warn, 22 info.

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
| warn | kernel | F09 | UNUSED_HYPOTHESIS | SGC.Bridge.ResidualHorizon.within_tolerance_of_residual_small | hypothesis `hT` never occurs in the proof term; the statement may be over-constrained or mis-stated |
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
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.ResidualHorizon.exact_tracking_of_zero_residual | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.ResidualHorizon.residual_horizon | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.ResidualHorizon.residual_horizon_explicit | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.ResidualHorizon.within_tolerance_of_residual_small | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.ResidualHorizon.exact_tracking_of_zero_residual | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.ResidualHorizon.residual_horizon | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.ResidualHorizon.residual_horizon_explicit | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.ResidualHorizon.within_tolerance_of_residual_small | 1 project-local definition(s) determine what this theorem is about; read them |

## Per-theorem receipt

### `SGC.Bridge.ResidualHorizon.exact_tracking_of_zero_residual`

- statement (kernel-elaborated, sha256 `33b7a167896ffc63`):

      ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {v : ℝ → E → E} {s : ℝ → Set E} {K : NNReal} {f f' g : ℝ → E} {T : ℝ}, (∀ t ∈ Set.Ico 0 T, LipschitzOnWith K (v t) (s t)) → ContinuousOn f (Set.Icc 0 T) → (∀ t ∈ Set.Ico 0 T, HasDerivWithinAt f (f' t) (Set.Ici t) t) → (∀ t ∈ Set.Ico 0 T, SGC.Bridge.ResidualHorizon.residual v f f' t = 0) → (∀ t ∈ Set.Ico 0 T, f t ∈ s t) → ContinuousOn g (Set.Icc 0 T) → (∀ t ∈ Set.Ico 0 T, HasDerivWithinAt g (v t (g t)) (Set.Ici t) t) → (∀ t ∈ Set.Ico 0 T, g t ∈ s t) → f 0 = g 0 → ∀ t ∈ Set.Icc 0 T, f t = g t

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.ResidualHorizon.residual` (def, SGC.Bridge.ResidualHorizon): `{E : Type u_1} → [NormedAddCommGroup E] → (ℝ → E → E) → (ℝ → E) → (ℝ → E) → ℝ → E`

### `SGC.Bridge.ResidualHorizon.residual_horizon`

- statement (kernel-elaborated, sha256 `894fe5bd2922dbf8`):

      ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {v : ℝ → E → E} {s : ℝ → Set E} {K : NNReal} {f f' g : ℝ → E} {T ε : ℝ}, (∀ t ∈ Set.Ico 0 T, LipschitzOnWith K (v t) (s t)) → ContinuousOn f (Set.Icc 0 T) → (∀ t ∈ Set.Ico 0 T, HasDerivWithinAt f (f' t) (Set.Ici t) t) → (∀ t ∈ Set.Ico 0 T, ‖SGC.Bridge.ResidualHorizon.residual v f f' t‖ ≤ ε) → (∀ t ∈ Set.Ico 0 T, f t ∈ s t) → ContinuousOn g (Set.Icc 0 T) → (∀ t ∈ Set.Ico 0 T, HasDerivWithinAt g (v t (g t)) (Set.Ici t) t) → (∀ t ∈ Set.Ico 0 T, g t ∈ s t) → f 0 = g 0 → ∀ t ∈ Set.Icc 0 T, dist (f t) (g t) ≤ gronwallBound 0 (↑K) ε t

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.ResidualHorizon.residual` (def, SGC.Bridge.ResidualHorizon): `{E : Type u_1} → [NormedAddCommGroup E] → (ℝ → E → E) → (ℝ → E) → (ℝ → E) → ℝ → E`

### `SGC.Bridge.ResidualHorizon.residual_horizon_explicit`

- statement (kernel-elaborated, sha256 `0a4bcb4a9429691a`):

      ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {v : ℝ → E → E} {s : ℝ → Set E} {K : NNReal} {f f' g : ℝ → E} {T ε : ℝ}, ↑K ≠ 0 → (∀ t ∈ Set.Ico 0 T, LipschitzOnWith K (v t) (s t)) → ContinuousOn f (Set.Icc 0 T) → (∀ t ∈ Set.Ico 0 T, HasDerivWithinAt f (f' t) (Set.Ici t) t) → (∀ t ∈ Set.Ico 0 T, ‖SGC.Bridge.ResidualHorizon.residual v f f' t‖ ≤ ε) → (∀ t ∈ Set.Ico 0 T, f t ∈ s t) → ContinuousOn g (Set.Icc 0 T) → (∀ t ∈ Set.Ico 0 T, HasDerivWithinAt g (v t (g t)) (Set.Ici t) t) → (∀ t ∈ Set.Ico 0 T, g t ∈ s t) → f 0 = g 0 → ∀ t ∈ Set.Icc 0 T, dist (f t) (g t) ≤ ε / ↑K * (Real.exp (↑K * t) - 1)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.ResidualHorizon.residual` (def, SGC.Bridge.ResidualHorizon): `{E : Type u_1} → [NormedAddCommGroup E] → (ℝ → E → E) → (ℝ → E) → (ℝ → E) → ℝ → E`

### `SGC.Bridge.ResidualHorizon.within_tolerance_of_residual_small`

- statement (kernel-elaborated, sha256 `0e94ab89dd063733`):

      ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {v : ℝ → E → E} {s : ℝ → Set E} {K : NNReal} {f f' g : ℝ → E} {T ε η : ℝ}, ↑K ≠ 0 → 0 ≤ T → (∀ t ∈ Set.Ico 0 T, LipschitzOnWith K (v t) (s t)) → ContinuousOn f (Set.Icc 0 T) → (∀ t ∈ Set.Ico 0 T, HasDerivWithinAt f (f' t) (Set.Ici t) t) → (∀ t ∈ Set.Ico 0 T, ‖SGC.Bridge.ResidualHorizon.residual v f f' t‖ ≤ ε) → 0 ≤ ε → (∀ t ∈ Set.Ico 0 T, f t ∈ s t) → ContinuousOn g (Set.Icc 0 T) → (∀ t ∈ Set.Ico 0 T, HasDerivWithinAt g (v t (g t)) (Set.Ici t) t) → (∀ t ∈ Set.Ico 0 T, g t ∈ s t) → f 0 = g 0 → ε / ↑K * (Real.exp (↑K * T) - 1) ≤ η → ∀ t ∈ Set.Icc 0 T, dist (f t) (g t) ≤ η

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: hT
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.ResidualHorizon.residual` (def, SGC.Bridge.ResidualHorizon): `{E : Type u_1} → [NormedAddCommGroup E] → (ℝ → E → E) → (ℝ → E) → (ℝ → E) → ℝ → E`

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
