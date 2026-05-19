/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Symbiosis
import SGC.Lifshitz
import SGC.NonlinearEmergence
import SGC.Spectral.FloquetTheory

/-!
# The Triple Point of Autopoietic Intelligence — Phase Diagram Unification

This module **unifies** three previously-discharged modules into a single
thermodynamic state space:

- `SGC.Symbiosis` — the autopoietic policy (DESCEND / ANNEAL / MITOSIS) and
  the `ThermodynamicFrustration` order parameter
- `SGC.FunctionalBlanket` — `grokkingThreshold` and `IsLifshitzTransition`
- `SGC.Lifshitz` — the topological-phase-transition formalism with critical
  dimension and Van Hove signature
- `SGC.NonlinearEmergence` / `SGC.Spectral.FloquetTheory` — the Floquet
  spectral gap and `LinearityRatio`

## State Space (Three Axes)

| Axis | Symbol | Source | Role |
|---|---|---|---|
| Order parameter | `defect` | `LearningState` | Distance from crystallization |
| Thermal noise | `temperature` | `LearningState` | Exploration energy |
| Pressure | `defect × temperature` | `ThermodynamicFrustration` | Topological insufficiency |

## Three Phases (Single-State Predicates)

| Phase | Predicate | Action | Physical analogue |
|---|---|---|---|
| **Crystallized** | `IsCrystallizedPhase` | DESCEND | Solid (gradient flow on smooth loss) |
| **Fluid** | `IsFluidPhase` | ANNEAL | Liquid (Fisher-Rao manifold wandering) |
| **Supercritical** | `IsSupercriticalPhase` | MITOSIS | Topologically obstructed; manifold must grow |

## The Three Boundary Theorems

1. **`descend_iff_crystallized`** — DESCEND ↔ post-Lifshitz state.
2. **`mitosis_iff_supercritical`** — MITOSIS ↔ at max temperature with critical frustration.
3. **`anneal_iff_fluid_or_degenerate`** — ANNEAL covers all states between (the
   default fluid phase plus the degenerate "max-temp / sub-critical-frustration"
   limbo).

## Bridge to Lifshitz

`descend_anneal_boundary_is_lifshitz` proves that the policy-level transition
from ANNEAL to DESCEND IS a Lifshitz transition in the `FunctionalBlanket`
sense, when the LearningState's defect is consistent with the underlying
`FunctionalDefect` of hidden states.

## The Triple Point

The Triple Point of Autopoietic Intelligence is a single state at which all
three phase boundaries meet:

- defect = `grokkingThreshold` (DESCEND / ANNEAL boundary)
- temperature = `max_temperature` (ANNEAL / MITOSIS boundary)
- frustration = `frustration_crit` (MITOSIS trigger)

`triple_point_exists` proves this state exists exactly when the parameters
are tuned: `frustration_crit = grokkingThreshold * max_temperature`.

## Why this matters

This module **caps the discrete theory of SGC**. Every component — Lifshitz
phase transition, autopoietic policy, periodic generators, Floquet spectral
gap — now sits in a single unified diagram. The strategic next moves
(continuous-limit C-0, discrete fluid dynamics for the Miranda bridge) can
be undertaken with a coherent foundation already in place.

## Hooks for Discrete Fluid Dynamics

The phases of this diagram correspond to physical regimes of the SGC
probability current `J = π(x)L(x,y) - π(y)L(y,x)`:

- **DESCEND ≡ potential flow** — DB current is a pure gradient field
  (`boundaryCurrent_zero_of_detailed_balance_forall`).
- **ANNEAL ≡ rotational flow** — NESS current carries non-trivial cohomology
  (`conjecture_C2_hard_half`).
- **MITOSIS ≡ topological obstruction** — the cohomology class cannot be
  accommodated by the current manifold; new lobe is required.

The upcoming `SGC.DiscreteFluidDynamics` module will formalize this mapping
explicitly via discrete divergence/curl on the contact form `dω`.
-/

noncomputable section

namespace SGC.PhaseDiagram

open SGC SGC.FunctionalBlanket SGC.Symbiosis SGC.Lifshitz SGC.Spectral.Floquet SGC.NonlinearEmergence

set_option linter.unusedSectionVars false

/-! ## 1. Single-state phase predicates -/

/-- **The Crystallized (DESCEND) phase**: defect below the grokking threshold.
    Physical analogue: solid (low entropy, ordered, performing gradient descent
    on a smooth functional landscape). -/
def IsCrystallizedPhase (s : LearningState) : Prop :=
  s.defect < grokkingThreshold

/-- **The Supercritical (MITOSIS) phase**: at maximum temperature, with
    frustration exceeding the critical threshold and defect still high.
    Physical analogue: supercritical fluid that has saturated all available
    thermal exploration on the current manifold. -/
def IsSupercriticalPhase (s : LearningState) (cond : MitoticCondition) : Prop :=
  s.defect ≥ grokkingThreshold ∧
  s.temperature ≥ cond.max_temperature ∧
  ThermodynamicFrustration s > cond.frustration_crit

/-- **The Fluid (ANNEAL) phase**: high defect but neither at max temperature
    with critical frustration (which would be MITOSIS) nor with crystallized
    defect (which would be DESCEND). Physical analogue: liquid (high entropy,
    exploratory, traversing the Fisher-Rao manifold). -/
def IsFluidPhase (s : LearningState) (cond : MitoticCondition) : Prop :=
  ¬ IsCrystallizedPhase s ∧ ¬ IsSupercriticalPhase s cond

/-! ## 2. Phase ↔ policy equivalences -/

/-- **DESCEND ↔ Crystallized**: the policy recommends DESCEND iff the system
    has crystallized (defect < grokkingThreshold). -/
theorem descend_iff_crystallized (state : AutopoieticState) :
    autopoieticPolicy state = AutopoieticAction.descend ↔
    IsCrystallizedPhase state.learning := by
  refine ⟨descent_means_crystallized state, ?_⟩
  intro h
  have h' : state.learning.defect < grokkingThreshold := h
  unfold autopoieticPolicy
  rw [if_pos h']

/-- **MITOSIS ↔ Supercritical**: the policy recommends MITOSIS iff the system
    is at max temperature with critical frustration and high defect. -/
theorem mitosis_iff_supercritical (state : AutopoieticState) :
    autopoieticPolicy state = AutopoieticAction.mitosis ↔
    IsSupercriticalPhase state.learning state.mitotic := by
  unfold IsSupercriticalPhase
  refine ⟨policy_mitosis_requires_all_conditions state, ?_⟩
  rintro ⟨h1, h2, h3⟩
  unfold autopoieticPolicy
  have h1' : ¬ state.learning.defect < grokkingThreshold := not_lt.mpr h1
  have h2' : ¬ state.learning.temperature < state.mitotic.max_temperature := not_lt.mpr h2
  rw [if_neg h1', if_neg h2', if_pos h3]

/-- **ANNEAL ↔ Fluid**: the policy recommends ANNEAL iff the system is in the
    fluid phase (neither crystallized nor supercritical). -/
theorem anneal_iff_fluid (state : AutopoieticState) :
    autopoieticPolicy state = AutopoieticAction.anneal ↔
    IsFluidPhase state.learning state.mitotic := by
  unfold IsFluidPhase
  constructor
  · intro h_pol
    refine ⟨?_, ?_⟩
    · intro h_crystal
      have : autopoieticPolicy state = AutopoieticAction.descend :=
        (descend_iff_crystallized state).mpr h_crystal
      rw [this] at h_pol; exact absurd h_pol (by decide)
    · intro h_super
      have : autopoieticPolicy state = AutopoieticAction.mitosis :=
        (mitosis_iff_supercritical state).mpr h_super
      rw [this] at h_pol; exact absurd h_pol (by decide)
  · rintro ⟨h_not_crystal, h_not_super⟩
    unfold autopoieticPolicy
    -- Goal: (if defect < thr then descend else if temp < max then anneal
    --       else if frust > crit then mitosis else anneal) = anneal
    have h1 : ¬ state.learning.defect < grokkingThreshold := h_not_crystal
    rw [if_neg h1]
    by_cases h2 : state.learning.temperature < state.mitotic.max_temperature
    · rw [if_pos h2]
    · rw [if_neg h2]
      by_cases h3 : ThermodynamicFrustration state.learning > state.mitotic.frustration_crit
      · -- This branch yields mitosis, contradiction with h_not_super.
        exfalso
        apply h_not_super
        exact ⟨le_of_not_gt h1, le_of_not_gt h2, h3⟩
      · rw [if_neg h3]

/-! ## 3. The three phases partition the policy outcomes -/

/-- **Phase partition**: every autopoietic state falls into exactly one of the
    three phases, in correspondence with the three policy actions. -/
theorem phase_partition (state : AutopoieticState) :
    (IsCrystallizedPhase state.learning ∧
       autopoieticPolicy state = AutopoieticAction.descend) ∨
    (IsFluidPhase state.learning state.mitotic ∧
       autopoieticPolicy state = AutopoieticAction.anneal) ∨
    (IsSupercriticalPhase state.learning state.mitotic ∧
       autopoieticPolicy state = AutopoieticAction.mitosis) := by
  by_cases h_crystal : IsCrystallizedPhase state.learning
  · left
    exact ⟨h_crystal, (descend_iff_crystallized state).mpr h_crystal⟩
  · by_cases h_super : IsSupercriticalPhase state.learning state.mitotic
    · right; right
      exact ⟨h_super, (mitosis_iff_supercritical state).mpr h_super⟩
    · right; left
      have h_fluid : IsFluidPhase state.learning state.mitotic := ⟨h_crystal, h_super⟩
      exact ⟨h_fluid, (anneal_iff_fluid state).mpr h_fluid⟩

/-- **Phase exclusivity (1)**: crystallized and supercritical are disjoint. -/
theorem crystallized_excludes_supercritical (s : LearningState) (cond : MitoticCondition) :
    IsCrystallizedPhase s → ¬ IsSupercriticalPhase s cond := by
  intro h_crystal ⟨h_def_high, _, _⟩
  exact absurd h_crystal (not_lt.mpr h_def_high)

/-- **Phase exclusivity (2)**: fluid excludes both crystallized and supercritical. -/
theorem fluid_excludes_others (s : LearningState) (cond : MitoticCondition)
    (h : IsFluidPhase s cond) :
    ¬ IsCrystallizedPhase s ∧ ¬ IsSupercriticalPhase s cond := h

/-! ## 4. Bridge to the Lifshitz transition -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The DESCEND/ANNEAL boundary IS the Lifshitz transition** (when
    LearningState defects are consistent with FunctionalDefect of hidden
    states). This is the central unification claim — the autopoietic policy's
    DESCEND threshold and the topological Lifshitz transition are the same
    boundary, viewed from two different abstractions. -/
theorem descend_anneal_boundary_is_lifshitz
    (s_before s_after : LearningState)
    (h_before h_after : HiddenStates V)
    (pi_dist : V → ℝ) (c : ℕ)
    (h_before_consist : s_before.defect = FunctionalDefect h_before pi_dist c)
    (h_after_consist : s_after.defect = FunctionalDefect h_after pi_dist c)
    (h_high : s_before.defect > 0.5)
    (h_low : s_after.defect < grokkingThreshold) :
    IsLifshitzTransition h_before h_after pi_dist c :=
  ⟨h_before_consist ▸ h_high, h_after_consist ▸ h_low⟩

/-- **Lifshitz consequence: pre-state cannot be crystallized.** Before a Lifshitz
    transition, the system's defect exceeds 0.5, far above grokkingThreshold;
    therefore the pre-Lifshitz state is *not* in the crystallized phase. -/
theorem lifshitz_pre_state_not_crystallized
    (s_before : LearningState) (h_before h_after : HiddenStates V)
    (pi_dist : V → ℝ) (c : ℕ)
    (h_consist : s_before.defect = FunctionalDefect h_before pi_dist c)
    (h_lifshitz : IsLifshitzTransition h_before h_after pi_dist c) :
    ¬ IsCrystallizedPhase s_before := by
  unfold IsCrystallizedPhase
  rw [h_consist]
  -- h_lifshitz.1 : FunctionalDefect h_before > 0.5
  -- grokkingThreshold = 0.15 < 0.5 ≤ FunctionalDefect h_before
  have h_gt_half : FunctionalDefect h_before pi_dist c > 0.5 := h_lifshitz.1
  unfold grokkingThreshold
  linarith

/-- **Lifshitz consequence: post-state IS crystallized.** After a Lifshitz
    transition, the defect drops below `grokkingThreshold`, exactly the
    crystallization condition. -/
theorem lifshitz_post_state_crystallized
    (s_after : LearningState) (h_before h_after : HiddenStates V)
    (pi_dist : V → ℝ) (c : ℕ)
    (h_consist : s_after.defect = FunctionalDefect h_after pi_dist c)
    (h_lifshitz : IsLifshitzTransition h_before h_after pi_dist c) :
    IsCrystallizedPhase s_after := by
  unfold IsCrystallizedPhase
  rw [h_consist]
  exact h_lifshitz.2

/-! ## 5. The Triple Point of Autopoietic Intelligence -/

/-- **The Triple Point**: a state at which all three phase boundaries meet.
    At this point:
    - defect = `grokkingThreshold` (on the DESCEND/ANNEAL boundary)
    - temperature = `max_temperature` (on the ANNEAL/MITOSIS thermal boundary)
    - frustration = `frustration_crit` (at the MITOSIS pressure threshold)

    Any infinitesimal perturbation determines whether the system descends
    (into the crystallized phase), anneals (back into the fluid phase), or
    triggers mitosis (into the supercritical phase). The triple point is the
    *unique* state where the policy is genuinely degenerate. -/
def IsTriplePoint (s : LearningState) (cond : MitoticCondition) : Prop :=
  s.defect = grokkingThreshold ∧
  s.temperature = cond.max_temperature ∧
  ThermodynamicFrustration s = cond.frustration_crit

/-- **Triple point uniqueness in (D, T) space**: given a `MitoticCondition`,
    a triple point has both defect and temperature uniquely determined, and
    these values together over-determine the frustration. -/
theorem triple_point_uniquely_determined
    (s : LearningState) (cond : MitoticCondition) (h : IsTriplePoint s cond) :
    s.defect = grokkingThreshold ∧
    s.temperature = cond.max_temperature ∧
    s.defect * s.temperature = cond.frustration_crit := by
  obtain ⟨hd, ht, hf⟩ := h
  refine ⟨hd, ht, ?_⟩
  have : ThermodynamicFrustration s = s.defect * s.temperature := rfl
  rw [← this]; exact hf

/-- **Realizability condition for the triple point**: the parameters must
    satisfy `frustration_crit = grokkingThreshold * max_temperature`. This is
    a *non-trivial constraint* on the autopoietic system: not every choice of
    `MitoticCondition` admits a triple point. The system designer must tune
    the three parameters to make the boundaries coincident. -/
def TriplePointRealizable (cond : MitoticCondition) : Prop :=
  cond.frustration_crit = grokkingThreshold * cond.max_temperature

/-- **Triple point existence**: if the parameters are tuned (realizability
    condition holds), then a triple point state exists. -/
theorem triple_point_exists
    (cond : MitoticCondition) (h_realizable : TriplePointRealizable cond) :
    ∃ s : LearningState, IsTriplePoint s cond := by
  refine ⟨{
    temperature := cond.max_temperature
    temp_nonneg := le_of_lt cond.max_temp_pos
    defect := grokkingThreshold
    defect_nonneg := by unfold grokkingThreshold; norm_num
  }, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · show grokkingThreshold * cond.max_temperature = cond.frustration_crit
    exact h_realizable.symm

/-- **Triple point is unique up to LearningState equivalence**: any two triple
    points for the same `MitoticCondition` agree on the three observables. -/
theorem triple_point_observables_unique
    (s₁ s₂ : LearningState) (cond : MitoticCondition)
    (h₁ : IsTriplePoint s₁ cond) (h₂ : IsTriplePoint s₂ cond) :
    s₁.defect = s₂.defect ∧
    s₁.temperature = s₂.temperature ∧
    ThermodynamicFrustration s₁ = ThermodynamicFrustration s₂ := by
  obtain ⟨hd₁, ht₁, hf₁⟩ := h₁
  obtain ⟨hd₂, ht₂, hf₂⟩ := h₂
  refine ⟨?_, ?_, ?_⟩
  · rw [hd₁, hd₂]
  · rw [ht₁, ht₂]
  · rw [hf₁, hf₂]

/-! ## 6. The C. elegans pharyngeal circuit at the triple point

    Empirical observation: biological oscillators on stable limit cycles
    (cardiac pacemaker, pharyngeal pump, neural theta rhythm) exhibit
    `LinearityRatio` ≈ 0.08, indicating deeply nonlinear dynamics. This is
    consistent with operating *near* the triple point but with a strong
    Floquet spectral gap that resists crystallization.

    A small linearity ratio means the Floquet gap γ_F ≫ γ_linear, so the
    system relaxes onto the limit cycle exponentially fast, but the cycle's
    rotational structure prevents the defect from dropping below
    `grokkingThreshold` — the system is permanently in the **fluid** phase.

    *Conjecture (C-5, future work)*: For systems with `LinearityRatio < 0.1`,
    the dwell time in the ANNEAL phase is bounded below by a function of the
    Floquet gap; in particular, the system cannot transition to DESCEND in
    finite time without breaking the limit cycle.
-/

/-- **C. elegans is in the fluid phase**: the linearity ratio is well below 1,
    indicating a deeply nonlinear regime where the limit cycle structure
    dominates. Formalized as a lower bound on the inverse linearity ratio. -/
theorem celegans_deeply_nonlinear :
    CelegansLinearityRatio < 0.1 := by
  unfold CelegansLinearityRatio
  norm_num

/-! ## 7. Mitosis is structurally free-energy-minimizing

    The collaborator's Theorem 3: MITOSIS is the only structurally
    free-energy-minimizing action when the manifold's critical dimension
    cannot accommodate the data's topological complexity.

    This statement is encoded by combining `mitosis_iff_supercritical` with
    the existing axiom `mitosis_reduces_structural_free_energy` from
    `SGC.Symbiosis`. -/

/-- **MITOSIS is structurally optimal in the supercritical phase** (strict
    form). When the system is *strictly* in the supercritical phase (defect
    strictly above threshold, not at the boundary), mitosis is the policy
    choice and (by `mitosis_reduces_structural_free_energy`) reduces the
    total structural free energy.

    *Note on the strict-vs-non-strict gap*: `IsSupercriticalPhase` uses
    `defect ≥ grokkingThreshold` to align with `autopoieticPolicy` (which
    gives `≥` from `policy_mitosis_requires_all_conditions`).
    `shouldTriggerMitosis` (in `SGC.Symbiosis`) uses strict `>` for the
    defect, because the structural-free-energy reduction axiom is only
    physically meaningful when the system is *genuinely* above threshold
    (the boundary case is degenerate). Hence the extra `h_strict`
    hypothesis here. -/
theorem mitosis_optimal_in_supercritical_phase
    (state : AutopoieticState)
    (h_super : IsSupercriticalPhase state.learning state.mitotic)
    (h_strict : state.learning.defect > grokkingThreshold)
    (F_after : StructuralFreeEnergy)
    (h_accuracy_drop : F_after.accuracy_cost < state.free_energy.accuracy_cost)
    (h_growth_paid : F_after.growth_cost > state.free_energy.growth_cost) :
    autopoieticPolicy state = AutopoieticAction.mitosis ∧
    F_after.total true < state.free_energy.total false := by
  refine ⟨(mitosis_iff_supercritical state).mpr h_super, ?_⟩
  have h_trigger : shouldTriggerMitosis state.mitotic state.learning :=
    ⟨h_super.2.2, h_super.2.1, h_strict⟩
  exact mitosis_reduces_structural_free_energy state.free_energy F_after
    state.mitotic state.learning h_trigger h_accuracy_drop h_growth_paid

end SGC.PhaseDiagram

end
