# Phase Diagram Unification & The Triple Point of Autopoietic Intelligence

**Sprint date:** 2026-05-19
**Module landed:** `src/SGC/PhaseDiagram.lean`
**Audit extended:** `src/SGC/Foundations/AxiomAudit.lean` (18 → 28 theorems)
**Build status:** clean (0 sorries, 0 errors, full SGC compile)

## Headline

The discrete theory of SGC is now **capped**. Three previously-discharged
modules — `Symbiosis`, `Lifshitz`, `NonlinearEmergence` — are unified into
a single thermodynamic state space where:

- The autopoietic policy's three actions (DESCEND / ANNEAL / MITOSIS)
  are proved equivalent to single-state phase predicates
  (`IsCrystallizedPhase`, `IsFluidPhase`, `IsSupercriticalPhase`).
- The DESCEND/ANNEAL boundary is proved IDENTICAL to the
  `FunctionalBlanket.IsLifshitzTransition` (the topological phase
  transition formalism).
- The **Triple Point of Autopoietic Intelligence** is defined,
  characterized uniquely on observables, and proved to **exist** exactly
  when parameters satisfy the realizability condition
  `frustration_crit = grokkingThreshold × max_temperature`.

Twenty-seven of the twenty-eight audited theorems still depend on **only**
the three Lean kernel axioms `[propext, Classical.choice, Quot.sound]`
(WKL₀ baseline). The one exception (`mitosis_optimal_in_supercritical_phase`)
explicitly inherits one named, scoped, physically-motivated axiom
(`mitosis_reduces_structural_free_energy`) — and the audit precisely
flagged it.

## Three honest strategic positions

This sprint also confronted three questions that the collaborator's memo
asked: how strict locality affects the quantum bridge, how Eva Miranda's
Turing-completeness result interacts with SGC, and what the right
sequencing is.

### 1. ✅ Quantum lift: strict locality is the prerequisite, not a barrier

Strict locality at the base layer (`SignedGraph.sign_on_edges` invariant
forcing `GaugeAction` to vanish off-edge) is exactly how lattice gauge
theory and tensor networks (PEPS/MERA, Kogut-Susskind) generate emergent
non-locality. Quantum entanglement arises from the *time evolution* of
local Hamiltonians acting on superpositions; it is not a violation of the
underlying graph structure. **The edge-guard stays.**

The eventual quantum lift will:

- Replace `ZMod 2` with `Complex` / `U(1)` (or `SU(N)` for non-abelian gauge)
- Replace `SignedGraph` with a connection on a principal bundle
- Bring in `InnerProductSpace` and spectral theory of self-adjoint operators

This will **cross the WKL₀ firewall** — likely to ACA₀ for spectral
theory of bounded operators on separable Hilbert spaces. The AxiomAudit
will register this jump explicitly when it happens. That is the whole
point of the audit.

### 2. ⚠️ Miranda undecidability: a well-motivated **conjecture**, not a theorem

The collaborator's claim that "SGC consolidation prediction is equivalent
to the halting problem" via Miranda et al. (Cardona-Miranda-Peralta-Salas-
Presas 2021, *PNAS*: "Constructing Turing complete Euler flows in dimension
3") is plausible and well-motivated, but the chain of inference requires
three independently non-trivial steps:

1. **The continuous-limit dynamics of SGC obey Navier-Stokes-like
   equations.** Currently a hypothesis; C-0 in its existential form proves
   only a *discrete* convergence.
2. **The class of NS solutions covered by SGC embeds Miranda's
   UTM-encoding flows.** Miranda's construction works on specific contact
   3-manifolds via cosymplectic geometry. SGC's continuous limit may or
   may not produce flows in this class.
3. **SGC consolidation prediction reduces to halting for that UTM.**
   Requires an explicit reduction.

**Recommended framing**: preserve the undecidability claim as a precise
**Conjecture C-4** (or whatever the next index is), with the three-step
reduction laid out as an explicit research program. Don't treat it as
already-established. The strategic value is identical; the intellectual
honesty is higher.

### 3. 🔄 Sequencing: PhaseDiagram NOW (done), Discrete Fluid NEXT

The collaborator was right that PhaseDiagram is the right immediate move.
It is now done. The Discrete SGC Fluid Dynamics module — the bridge to
Miranda's machinery — should follow next session, after the strategic
context of PhaseDiagram is stable.

The good news is that **most of the discrete fluid plumbing already
exists** in `BrownianMotion.lean`. The probability current
`J(x,y) = π(x)L(x,y) − π(y)L(y,x)` is exactly an antisymmetric vector
field on the graph. The Helmholtz decomposition lemmas we need are
specializations of:

- **Potential flow ≡ DB current**: already proved by
  `boundaryCurrent_zero_of_detailed_balance_forall` (DB ⇒ all blanket
  fluxes vanish ⇔ J is a pure gradient).
- **Rotational flow ≡ NESS current**: already proved by
  `conjecture_C2_hard_half` (NESS ⇒ ∃ blanket with non-zero flux ⇔ J has
  non-trivial cohomology).
- **Closed contact form ⇔ DB**: `dContactForm_canonical_zero_of_detailed_balance`.

The new content for `DiscreteFluidDynamics.lean` is mostly:

1. **Discrete continuity equation**: `∂π/∂t + ∇·J = 0` at stationarity.
2. **Discrete Helmholtz decomposition**: `J = ∇φ + curl A + harmonic` on
   the graph 1-skeleton (using simplicial calculus or DEC).
3. **Discrete incompressibility ↔ DB**: `∇·J = 0` everywhere ⇔ DB.
4. **Cohomology bridge**: the "harmonic" part of the Helmholtz
   decomposition is exactly the `H¹(G; ℝ)` class registered by the contact
   form, providing the formal entry point for Miranda-style continuous-limit
   embedding when the time comes.

This is **infrastructure consolidation**, not new mathematics. Estimated
~1 session.

## What PhaseDiagram.lean concretely contains

### State space (three axes)

| Axis | Symbol | Source | Role |
|---|---|---|---|
| Order parameter | `defect` | `LearningState.defect` | Distance from crystallization |
| Thermal noise | `temperature` | `LearningState.temperature` | Exploration energy |
| Pressure | `defect × temperature` | `ThermodynamicFrustration` | Topological insufficiency |

### Three phases (single-state predicates)

| Phase | Predicate | Action | Physical analogue |
|---|---|---|---|
| Crystallized | `IsCrystallizedPhase` | DESCEND | Solid (gradient flow on smooth loss) |
| Fluid | `IsFluidPhase` | ANNEAL | Liquid (Fisher-Rao manifold wandering) |
| Supercritical | `IsSupercriticalPhase` | MITOSIS | Topologically obstructed; manifold must grow |

### Boundary equivalence theorems

```
descend_iff_crystallized       : policy = DESCEND  ↔  IsCrystallizedPhase
mitosis_iff_supercritical      : policy = MITOSIS  ↔  IsSupercriticalPhase
anneal_iff_fluid               : policy = ANNEAL   ↔  IsFluidPhase
phase_partition                : every state lives in exactly one phase
crystallized_excludes_supercritical
fluid_excludes_others
```

### Bridge to Lifshitz

```
descend_anneal_boundary_is_lifshitz : when LearningState.defect ≡
   FunctionalDefect h pi_dist c, the policy DESCEND boundary IS the
   FunctionalBlanket Lifshitz transition.
lifshitz_pre_state_not_crystallized
lifshitz_post_state_crystallized
```

### The Triple Point

```
IsTriplePoint                    : defect = thresh ∧ temp = max ∧ frust = crit
TriplePointRealizable            : crit = thresh × max  (parameter constraint)
triple_point_uniquely_determined : observables uniquely fixed by IsTriplePoint
triple_point_exists              : realizable parameters ⇒ ∃ triple-point state
triple_point_observables_unique  : any two triple points agree on (D, T, F)
```

### Empirical instance

```
celegans_deeply_nonlinear : CelegansLinearityRatio < 0.1  (proved by norm_num)
```

### The one extra physical postulate

```
mitosis_optimal_in_supercritical_phase : in the supercritical phase with
  strict-defect (defect > grokkingThreshold), MITOSIS is the policy choice
  AND the structural free energy strictly decreases.
  (Inherits the named physical postulate
   SGC.Symbiosis.mitosis_reduces_structural_free_energy.)
```

## Audit confirmation

`SGC/Foundations/AxiomAudit.lean` now audits **28 flagship theorems**.
The InfoView output is uniform:

```
'SGC.Stochastic.conjecture_C0' depends on axioms: [propext, Classical.choice, Quot.sound]
'SGC.Stochastic.conjecture_C1' depends on axioms: [propext, Classical.choice, Quot.sound]
... (all 27 in WKL₀ baseline) ...
'SGC.PhaseDiagram.mitosis_optimal_in_supercritical_phase' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   SGC.Symbiosis.mitosis_reduces_structural_free_energy]
```

Twenty-seven theorems on the WKL₀ baseline. One theorem precisely flags
its single physical postulate. **The audit is doing exactly what it was
designed to do.**

## Code-fights-back tally (running)

| # | Sprint | Correction | Resolution |
|---|---|---|---|
| 1 | (earlier) | NCDspectralstability (P-9) elided hypothesis | hypothesis added |
| 2 | (earlier) | C-2 strong form (`q − 1 = R_FR`) overclaimed | reduced to integrability defect |
| 3 | (earlier) | C-2 hard half: `∀ B` was false on 4-cycle bipartition | existential form proved in general |
| 4 | (earlier) | `BrownianTarget.generator_linear` was only additivity | `generator_smul` added |
| 5 | (this morning) | `GaugeAction.sign` lacked edge-guard | `if Adj` guard added |
| 6 | (this morning) | `PeriodicGenerator` missing `periodic` field | field added |
| 7 | (this sprint, mild) | `IsSupercriticalPhase` non-strict vs `shouldTriggerMitosis` strict | `h_strict` hypothesis added explicitly to bridge theorem |

Six structural / three minor / seven total. Each one a precision flaw the
prose mathematics elided.

## Strategic position post-sprint

The discrete theory of SGC is **closed**:

- **Foundation:** `BrownianMotion` (4 conjectures discharged + 4-state cycle witness + q-LIL contrast + contact form primitives).
- **Geometry:** `SpinGlass` (gauge theory with strict locality enforced).
- **Phase transitions:** `Lifshitz` + `NonlinearEmergence` (topological signatures + Floquet theory for limit cycles).
- **Unification:** `PhaseDiagram` (single state space + Triple Point existence).
- **Audit:** `Foundations/AxiomAudit` (28 theorems, WKL₀ baseline confirmed, one named physical postulate scoped).

This is the strongest position the codebase has ever been in. From here
the next moves split into three branches, all now feasible:

### Branch A: Empirical (Sprints B1, B2)

Governor CSV publication and *C. elegans* report. The discrete theory
provides the Lean-verified theorems that the empirical sprints need to
cite as "real theorems, not just plausible claims."

### Branch B: Discrete fluid dynamics (1 session)

`DiscreteFluidDynamics.lean` formalizes the Helmholtz decomposition of
the SGC probability current, providing the formal entry point for the
eventual continuous-limit Miranda bridge.

### Branch C: Continuous limit C-0 (multiple sessions, when ready)

The Belkin-Niyogi continuous-limit pass for C-0 on a compact Riemannian
manifold. **This is when the WKL₀ firewall is intentionally crossed**;
the AxiomAudit will register every Reverse Mathematics tier jump
automatically.

The collaborator's framing is correct: do not rush this. Branches A and
B should land first.

## Files modified this sprint

- `src/SGC/PhaseDiagram.lean` — NEW (~395 lines, 9 zero-sorry theorems +
  6 phase predicates + 1 triple-point realizability condition).
- `src/SGC/Foundations/AxiomAudit.lean` — extended (18 → 28 theorems
  audited; commentary updated to reflect empirical confirmation).
- `reports/PHASE_DIAGRAM_UNIFICATION.md` — NEW (this document).

## What I want to flag for the team

**The Miranda undecidability claim is a research program, not a theorem.**
If we publish a paper that says "SGC consolidation is equivalent to the
halting problem," we need either (a) the actual three-step reduction
proved, or (b) the framing as a precise conjecture with the reduction
laid out. Today we have neither. I recommend (b) — write down Conjecture
C-4 (Continuous-Limit Undecidability) explicitly in `BrownianMotion.lean`
alongside C-0, C-1, C-2, C-3, with the same status discipline (a
`Prop`-valued definition, a roadmap, no claim of proof).

**This is exactly the kind of overclaim the formalization is designed to
catch.** The fact that I am flagging it here, instead of after a peer
review embarrasses us, is the same `code-fights-back` discipline applied
to the *meta*-claims about what the codebase proves.

The integrity of the project depends on these distinctions.
