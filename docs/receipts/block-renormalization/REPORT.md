# lean-triage report: REVIEW

- receipt: `lean-triage-5b3c3f276704-20260913T224217Z`  (hash_self `dba44f6ca9eca5ac...`)
- tool: lean-triage 0.2.1 (source `25bc5fa54832`, probe `8988909f4e39`)
- repo: https://github.com/JasonShroyer/sgc-lean.git
- commit: f1197389f7cb7747b85ce61e09018697d5e39c8e  dirty=True
- toolchain: leanprover/lean4:v4.25.2
- source tree sha256: `5b3c3f2767044c9f624993179b649ef98cbdb9bbaefb313c2426b87ecd7fbe4c`
- modules: SGC.Bridge.BlockRenormalization

## Verdict

**REVIEW** - 0 fail, 15 warn, 36 info.

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
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.BlockRenormalization.blocked_terminalError_eq | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.BlockRenormalization.detKernel_block_pow | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.BlockRenormalization.detKernel_isStochastic | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.BlockRenormalization.detKernel_mul | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.BlockRenormalization.detKernel_pow | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.BlockRenormalization.detKernel_vecMul_point | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.BlockRenormalization.evalDom_iff_block_halts | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.BlockRenormalization.halts_iff_block_halts | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.BlockRenormalization.multistep_add | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | attestation | F10 | CLAIM_MAP_UNATTESTED | SGC.Bridge.BlockRenormalization.multistep_mul | no human-attested mapping from an informal claim to this statement; the printed statement is the only claim |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.BlockRenormalization.blocked_terminalError_eq | 13 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.BlockRenormalization.detKernel_block_pow | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.BlockRenormalization.detKernel_isStochastic | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.BlockRenormalization.detKernel_mul | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.BlockRenormalization.detKernel_pow | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.BlockRenormalization.detKernel_vecMul_point | 1 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.BlockRenormalization.evalDom_iff_block_halts | 3 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.BlockRenormalization.halts_iff_block_halts | 3 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.BlockRenormalization.multistep_add | 2 project-local definition(s) determine what this theorem is about; read them |
| info | kernel | F08 | DEFINITION_CONE_INDEX | SGC.Bridge.BlockRenormalization.multistep_mul | 3 project-local definition(s) determine what this theorem is about; read them |

## Per-theorem receipt

### `SGC.Bridge.BlockRenormalization.blocked_terminalError_eq`

- statement (kernel-elaborated, sha256 `82bf93cd12f166bd`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V) (P : SGC.Partition V) (pi : V → ℝ) (b h : ℕ), SGC.Bridge.TerminalDecoding.terminalError (SGC.Bridge.BlockRenormalization.detKernel f^[b]) P pi h = SGC.Bridge.BlockRenormalization.detKernel f ^ (b * h) * SGC.lift_matrix P - SGC.lift_matrix P * SGC.Thermodynamics.CoarseGenerator (SGC.Bridge.BlockRenormalization.detKernel f^[b]) P pi ^ h

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Partition` (inductive, SGC.Renormalization.Lumpability): `(V : Type u_2) → [DecidableEq V] → Type u_2`
    - `SGC.Partition.Quot` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Type u_2`
    - `SGC.Bridge.TerminalDecoding.terminalError` (def, SGC.Bridge.TerminalDecoding): `{X : Type u_1} → [Fintype X] → [inst : DecidableEq X] → Matrix X X ℝ → (P : SGC.Partition X) → (X → ℝ) → ℕ → Matrix X P.Quot ℝ`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`
    - `SGC.lift_matrix` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → Matrix V P.Quot ℝ`
    - `SGC.Partition.instFintype` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → Fintype P.Quot`
    - `SGC.Partition.instDecidableEq` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (P : SGC.Partition V) → DecidableEq P.Quot`
    - `SGC.Thermodynamics.CoarseGenerator` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → Matrix V V ℝ → (P : SGC.Partition V) → (V → ℝ) → Matrix P.Quot P.Quot ℝ`
    - `SGC.Partition.rel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → SGC.Partition V → Setoid V`
    - `SGC.Partition.quot_map` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [inst : DecidableEq V] → (P : SGC.Partition V) → V → P.Quot`
    - `SGC.Partition.decRel` (def, SGC.Renormalization.Lumpability): `{V : Type u_2} → [inst : DecidableEq V] → (self : SGC.Partition V) → DecidableRel ⇑self.rel`
    - `SGC.Thermodynamics.CoarseStationaryDist` (def, SGC.Thermodynamics.EntropyProduction): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`
    - `SGC.pi_bar` (def, SGC.Renormalization.Lumpability): `{V : Type u_1} → [Fintype V] → [inst : DecidableEq V] → (P : SGC.Partition V) → (V → ℝ) → P.Quot → ℝ`

### `SGC.Bridge.BlockRenormalization.detKernel_block_pow`

- statement (kernel-elaborated, sha256 `b2980fc60ec21823`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V) (b h : ℕ), SGC.Bridge.BlockRenormalization.detKernel f^[b] ^ h = SGC.Bridge.BlockRenormalization.detKernel f ^ (b * h)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`

### `SGC.Bridge.BlockRenormalization.detKernel_isStochastic`

- statement (kernel-elaborated, sha256 `d375a82f843f0da3`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V), SGC.Renormalization.KernelHorizon.IsStochastic (SGC.Bridge.BlockRenormalization.detKernel f)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Renormalization.KernelHorizon.IsStochastic` (inductive, SGC.Renormalization.KernelHorizon): `{V : Type u_1} → [Fintype V] → Matrix V V ℝ → Prop`
    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`

### `SGC.Bridge.BlockRenormalization.detKernel_mul`

- statement (kernel-elaborated, sha256 `b67407936dc9df64`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f g : V → V), SGC.Bridge.BlockRenormalization.detKernel f * SGC.Bridge.BlockRenormalization.detKernel g = SGC.Bridge.BlockRenormalization.detKernel (g ∘ f)

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`

### `SGC.Bridge.BlockRenormalization.detKernel_pow`

- statement (kernel-elaborated, sha256 `2e151ddc8a124ca0`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V) (b : ℕ), SGC.Bridge.BlockRenormalization.detKernel f ^ b = SGC.Bridge.BlockRenormalization.detKernel f^[b]

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`

### `SGC.Bridge.BlockRenormalization.detKernel_vecMul_point`

- statement (kernel-elaborated, sha256 `ebd9435557e45514`):

      ∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] (f : V → V) (x : V) (m : ℕ), Matrix.vecMul (fun y => if y = x then 1 else 0) (SGC.Bridge.BlockRenormalization.detKernel f ^ m) = fun y => if y = f^[m] x then 1 else 0

- axioms: Classical.choice [lean-core], Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.BlockRenormalization.detKernel` (def, SGC.Bridge.BlockRenormalization): `{V : Type u_1} → [DecidableEq V] → (V → V) → Matrix V V ℝ`

### `SGC.Bridge.BlockRenormalization.evalDom_iff_block_halts`

- statement (kernel-elaborated, sha256 `1d90e8749802e541`):

      ∀ {σ : Type u_1} (f : σ → Option σ) (a : σ) {b : ℕ}, 0 < b → ((Turing.eval f a).Dom ↔ ∃ h, SGC.Bridge.HaltingCompiler.multistep (SGC.Bridge.BlockRenormalization.blockStep f b) a h = none)

- axioms: Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.HaltingCompiler.multistep` (def, SGC.Bridge.HaltingCompiler): `{σ : Type u_1} → (σ → Option σ) → σ → ℕ → Option σ`
    - `SGC.Bridge.BlockRenormalization.blockStep` (def, SGC.Bridge.BlockRenormalization): `{σ : Type u_1} → (σ → Option σ) → ℕ → σ → Option σ`
    - `SGC.Bridge.HaltingCompiler.multistep.match_1` (def, SGC.Bridge.HaltingCompiler): `(motive : ℕ → Sort u_1) → (x : ℕ) → (Unit → motive 0) → ((n : ℕ) → motive n.succ) → motive x`

### `SGC.Bridge.BlockRenormalization.halts_iff_block_halts`

- statement (kernel-elaborated, sha256 `2cecdf8b705532e9`):

      ∀ {σ : Type u_1} (f : σ → Option σ) (a : σ) {b : ℕ}, 0 < b → ((∃ n, SGC.Bridge.HaltingCompiler.multistep f a n = none) ↔ ∃ h, SGC.Bridge.HaltingCompiler.multistep (SGC.Bridge.BlockRenormalization.blockStep f b) a h = none)

- axioms: Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.HaltingCompiler.multistep` (def, SGC.Bridge.HaltingCompiler): `{σ : Type u_1} → (σ → Option σ) → σ → ℕ → Option σ`
    - `SGC.Bridge.BlockRenormalization.blockStep` (def, SGC.Bridge.BlockRenormalization): `{σ : Type u_1} → (σ → Option σ) → ℕ → σ → Option σ`
    - `SGC.Bridge.HaltingCompiler.multistep.match_1` (def, SGC.Bridge.HaltingCompiler): `(motive : ℕ → Sort u_1) → (x : ℕ) → (Unit → motive 0) → ((n : ℕ) → motive n.succ) → motive x`

### `SGC.Bridge.BlockRenormalization.multistep_add`

- statement (kernel-elaborated, sha256 `165ce15353a453d6`):

      ∀ {σ : Type u_1} (f : σ → Option σ) (a : σ) (m n : ℕ), SGC.Bridge.HaltingCompiler.multistep f a (m + n) = (SGC.Bridge.HaltingCompiler.multistep f a m).bind fun a' => SGC.Bridge.HaltingCompiler.multistep f a' n

- axioms: Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.HaltingCompiler.multistep` (def, SGC.Bridge.HaltingCompiler): `{σ : Type u_1} → (σ → Option σ) → σ → ℕ → Option σ`
    - `SGC.Bridge.HaltingCompiler.multistep.match_1` (def, SGC.Bridge.HaltingCompiler): `(motive : ℕ → Sort u_1) → (x : ℕ) → (Unit → motive 0) → ((n : ℕ) → motive n.succ) → motive x`

### `SGC.Bridge.BlockRenormalization.multistep_mul`

- statement (kernel-elaborated, sha256 `909746762c510343`):

      ∀ {σ : Type u_1} (f : σ → Option σ) (a : σ) (b h : ℕ), SGC.Bridge.HaltingCompiler.multistep (SGC.Bridge.BlockRenormalization.blockStep f b) a h = SGC.Bridge.HaltingCompiler.multistep f a (b * h)

- axioms: Quot.sound [lean-core], propext [lean-core]
- unused hypotheses: none
- automation: trivial_by=None vacuous_by=None empty_domain=None
- claim map: UNATTESTED

- definitions to read (project-local, reachable from the statement):

    - `SGC.Bridge.HaltingCompiler.multistep` (def, SGC.Bridge.HaltingCompiler): `{σ : Type u_1} → (σ → Option σ) → σ → ℕ → Option σ`
    - `SGC.Bridge.BlockRenormalization.blockStep` (def, SGC.Bridge.BlockRenormalization): `{σ : Type u_1} → (σ → Option σ) → ℕ → σ → Option σ`
    - `SGC.Bridge.HaltingCompiler.multistep.match_1` (def, SGC.Bridge.HaltingCompiler): `(motive : ℕ → Sort u_1) → (x : ℕ) → (Unit → motive 0) → ((n : ℕ) → motive n.succ) → motive x`

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
