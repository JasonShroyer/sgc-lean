/-
  # SGC/Foundations/AxiomAudit.lean

  **Proof-theoretic baseline audit for SGC's discharged conjectures.**

  ## Why this module exists

  Every theorem in this codebase that lives behind the `[Fintype V]` firewall
  is comfortably provable in **WKL₀** (Weak König's Lemma over RCA₀). When
  the continuous limit of conjecture C-0 (non-reversible Belkin-Niyogi
  convergence on a compact manifold) is eventually attacked, we will need
  to leave `[Fintype V]` and the proof-theoretic strength will jump,
  potentially to **ATR₀** (arithmetic transfinite recursion) or
  **Π¹₁-CA₀** (Π¹₁ comprehension) for theorems involving uncountable
  suprema, real-valued Borel hierarchies, or fixed-point constructions
  on continuous state spaces.

  This module is the **baseline snapshot before that jump**. Each
  `#print axioms` call below emits, in the Lean InfoView, the explicit
  axiom set used by a flagship discharged theorem. When the continuous
  pass starts, we re-run this file and diff against the baseline to see
  exactly where the proof-theoretic strength has increased.

  ## Reverse Mathematics tier reference

  | Tier             | Strength                       | What it proves                                              |
  |------------------|--------------------------------|-------------------------------------------------------------|
  | **RCA₀**         | Recursive Comprehension        | Constructive base; computable functions, finite arithmetic. |
  | **WKL₀**         | Weak König's Lemma             | Compactness for `2^ℕ`; Heine-Borel for `[0,1]^n`.            |
  | **ACA₀**         | Arithmetical Comprehension     | Bolzano-Weierstrass; Riemann integrability of continuous f. |
  | **ATR₀**         | Arithmetic Transfinite Recursion | Borel determinacy at finite levels; comparability of WO.    |
  | **Π¹₁-CA₀**      | Π¹₁ Comprehension              | Cantor-Bendixson; perfect-set theorem; full Borel hierarchy. |

  **Where SGC currently sits**: every discharged theorem in this codebase
  uses only `propext`, `Classical.choice`, and `Quot.sound` from Lean's
  kernel. With `[Fintype V]` everywhere, the *mathematical* content is
  RCA₀-comfortable; `Classical.choice` is invoked formally but the
  underlying constructions are constructive (decidability via `open
  Classical` is a notational convenience, not a strength jump).

  ## What to expect when you open this file

  Open this file in Lean and the InfoView will show, for each `#print
  axioms` line, output of the form:

      'theorem_name' depends on axioms: [propext, Classical.choice, Quot.sound]

  These three are the minimum used by Mathlib in any nontrivial proof.
  Anything *beyond* these three (e.g., `Classical.byContradiction` invoked
  directly, `LE.le.lt_of_ne` traced to choice, or new axioms introduced
  by the user) is a **proof-theoretic warning sign** that should be audited.

  ## Update protocol

  When new theorems are discharged or the continuous-limit pass begins:
  1. Add a `#print axioms` line for each new flagship theorem.
  2. Before merging, diff against the previous output.
  3. Any *new* axiom appearing for an old theorem indicates an upstream
     Mathlib change pulled in additional strength; investigate.
  4. Any new axiom for a *new* theorem that exceeds the current tier
     (e.g., the first appearance of `Classical.byContradiction` invoked
     non-trivially) should be documented in the per-theorem commentary
     below.
-/

import SGC.Stochastic.BrownianMotion
import SGC.SpinGlass
import SGC.PhaseDiagram
import SGC.Bridge.CelegansFloquetTsallis
import SGC.Thermodynamics.EntropyProduction
import SGC.Thermodynamics.FluxDecomposition

noncomputable section

namespace SGC.Foundations.AxiomAudit

/-! ## 1. BrownianMotion module — discharged conjectures C-0, C-1, C-2, C-3 -/

/-! ### 1.1 The four foundational conjectures -/

-- Conjecture C-0: existential FP convergence sequence.
#print axioms SGC.Stochastic.conjecture_C0

-- Conjecture C-1: q-deformed LIL witness walk.
#print axioms SGC.Stochastic.conjecture_C1

-- Conjecture C-2 hard half: NESS ⇒ ∃ blanket with non-zero current.
#print axioms SGC.Stochastic.conjecture_C2_hard_half

-- Conjecture C-2 top-level: both halves under physical q ↔ DB hypothesis.
#print axioms SGC.Stochastic.conjecture_C2_holds_of_NESS_at_q_gt_one

-- Conjecture C-3: every antisymmetric current is realisable.
#print axioms SGC.Stochastic.conjecture_C3

/-! ### 1.2 Supporting theorems used by the four conjectures -/

-- Universal easy half of C-2 (DB ⇒ all blankets have zero current).
#print axioms SGC.Stochastic.boundaryCurrent_zero_of_detailed_balance_forall

-- Per-blanket easy half of C-2.
#print axioms SGC.Stochastic.boundaryCurrent_zero_of_detailed_balance

-- The closed 1-form: DB ⇒ canonical contact form vanishes.
#print axioms SGC.Stochastic.dContactForm_canonical_zero_of_detailed_balance

-- DB ⇒ no contact blanket.
#print axioms SGC.Stochastic.not_isContactBlanket_of_detailed_balance

/-! ### 1.3 The 4-state cycle worked example -/

-- Cycle is in NESS (genuine non-equilibrium witness).
#print axioms SGC.Stochastic.FourStateCycle.cycle_not_detailed_balance

-- Cycle's boundary current equals 1/4 (explicit value).
#print axioms SGC.Stochastic.FourStateCycle.cycle_boundaryCurrent_eq_quarter

-- Cycle witnesses C-2 hard half (now an instance of the general theorem).
#print axioms SGC.Stochastic.FourStateCycle.cycle_witnesses_C2

-- Cycle is a contact blanket.
#print axioms SGC.Stochastic.FourStateCycle.cycle_isContactBlanket

/-! ### 1.4 q-LIL scaling (formal UGM contrast) -/

-- q = 1: scaling exponent matches UGM.
#print axioms SGC.Stochastic.qLIL_scaling_at_one

-- q ∈ (1, 2): scaling exponent strictly less than UGM.
#print axioms SGC.Stochastic.qLIL_scaling_lt_UGM_for_q_gt_one

-- q = 2: scaling exponent vanishes.
#print axioms SGC.Stochastic.qLIL_scaling_at_two

-- Strict antitonicity of scaling exponent in q.
#print axioms SGC.Stochastic.qLIL_scaling_strictAnti

/-! ## 2. SpinGlass module — discharged gauge invariance theorems -/

-- Gauge transformation preserves edge satisfiability (per-edge).
#print axioms SGC.SpinGlass.gauge_preserves_satisfiability

-- Unfrustrated ↔ gauge-equivalent to ferromagnetic.
#print axioms SGC.SpinGlass.unfrustrated_iff_gauge_positive

/-! ## 2b. PhaseDiagram module — Triple Point of Autopoietic Intelligence -/

-- DESCEND ↔ Crystallized phase.
#print axioms SGC.PhaseDiagram.descend_iff_crystallized

-- MITOSIS ↔ Supercritical phase.
#print axioms SGC.PhaseDiagram.mitosis_iff_supercritical

-- ANNEAL ↔ Fluid phase.
#print axioms SGC.PhaseDiagram.anneal_iff_fluid

-- Phase partition (every state lives in exactly one phase).
#print axioms SGC.PhaseDiagram.phase_partition

-- The DESCEND/ANNEAL boundary IS a Lifshitz transition.
#print axioms SGC.PhaseDiagram.descend_anneal_boundary_is_lifshitz

-- Triple-point existence under realizability.
#print axioms SGC.PhaseDiagram.triple_point_exists

-- Triple-point uniqueness on observables.
#print axioms SGC.PhaseDiagram.triple_point_observables_unique

-- C. elegans operates in the deeply nonlinear regime.
#print axioms SGC.PhaseDiagram.celegans_deeply_nonlinear

-- MITOSIS minimizes structural free energy in the supercritical phase.
#print axioms SGC.PhaseDiagram.mitosis_optimal_in_supercritical_phase

/-! ## 2c. CelegansFloquetTsallis bridge — empirical Branch A anchor -/

-- Structural identity: predicted α = r / 2.
#print axioms SGC.Bridge.CelegansFloquetTsallis.predicted_alpha_eq_r_half

-- C. elegans bridge: α = r / 2 instantiated at the measured value.
#print axioms SGC.Bridge.CelegansFloquetTsallis.celegans_alpha_eq_r_half

-- The numerical prediction: α = 0.04.
#print axioms SGC.Bridge.CelegansFloquetTsallis.celegans_anomalous_diffusion_value

-- C. elegans is sub-UGM (formal separation from Brownian baseline).
#print axioms SGC.Bridge.CelegansFloquetTsallis.celegans_scaling_lt_UGM

-- C. elegans is sub-Brownian by an order of magnitude (α < 1/10).
#print axioms SGC.Bridge.CelegansFloquetTsallis.celegans_scaling_lt_one_tenth

-- C. elegans Tsallis q sits in the genuine NESS regime (1, 2).
#print axioms SGC.Bridge.CelegansFloquetTsallis.celegans_tsallis_q_in_NESS_regime

-- Strict separation chain.
#print axioms SGC.Bridge.CelegansFloquetTsallis.celegans_alpha_strictly_between_zero_and_UGM

/-! ## 2d. EntropyProduction module — KL divergence and hidden entropy bounds

  These theorems live behind the `gaspard_maes_bridge` and
  `hidden_entropy_bound_from_trajectory` axioms. The audit makes the
  dependency on the named physical axiom explicit.
-/

-- KL divergence is non-negative (Gibbs).
#print axioms SGC.Thermodynamics.KLDiv_nonneg

-- KL divergence is zero iff the distributions are equal.
#print axioms SGC.Thermodynamics.KLDiv_eq_zero_iff

-- Hidden entropy upper bound from approximate lumpability (uses
-- `hidden_entropy_bound_from_trajectory` axiom).
#print axioms SGC.Thermodynamics.hidden_entropy_bounded_by_defect

-- Hidden entropy lower bound (uses `gaspard_path_space_identity` axiom,
-- renamed from `gaspard_maes_bridge` on 2026-05-25).
-- This audit line is the **leverage marker**: closing the path-space
-- identity removes its appearance here.
#print axioms SGC.Thermodynamics.hidden_entropy_lower_bound

-- Efficiency requires prediction (chains through `gaspard_path_space_identity`).
#print axioms SGC.Thermodynamics.efficiency_requires_prediction

/-! ## 2e. FluxDecomposition module — NESS stability and non-normality

  Symmetric / antisymmetric generator splitting `L = L_sym + L_anti`,
  Hatano-Sasa housekeeping decomposition, π-adjoint, sector condition.
  All listed theorems are zero-sorry; some chain through the small
  algebraic axioms in the same file.
-/

-- The fundamental decomposition L = L_sym + L_anti.
#print axioms SGC.Thermodynamics.generator_decomposition

-- L_sym satisfies π-detailed balance (defining property).
#print axioms SGC.Thermodynamics.symmetric_part_detailed_balance

-- L_anti is π-antisymmetric (defining property).
#print axioms SGC.Thermodynamics.antisymmetric_part_antisymmetric

-- L_anti = 0 iff detailed balance holds.
#print axioms SGC.Thermodynamics.antisymmetric_part_zero_iff_detailed_balance

-- Antisymmetric part contributes zero to the quadratic form (flux doesn't dissipate).
#print axioms SGC.Thermodynamics.antisymmetric_part_zero_quadratic

-- Dirichlet form sees only the symmetric part.
#print axioms SGC.Thermodynamics.dirichlet_form_eq_symmetric_part

-- Self-adjointness (under π) is equivalent to detailed balance.
#print axioms SGC.Thermodynamics.self_adjoint_iff_detailed_balance

-- Housekeeping entropy vanishes iff detailed balance (uses
-- `zero_entropy_implies_zero_current` axiom).
#print axioms SGC.Thermodynamics.housekeeping_zero_iff_detailed_balance

/-! ## 3. Per-theorem proof-theoretic commentary — **CONFIRMED 2026-05-19**

  **Forty-eight** flagship theorems are audited above (35 from the May 19
  sprint baseline, plus 5 EntropyProduction and 8 FluxDecomposition
  additions in the entropy-axiom-closure follow-up). Of these:

  - **Forty-three** depend on **exactly** the three Lean kernel axioms:
    `[propext, Classical.choice, Quot.sound]` — the **WKL₀-comfortable
    baseline**, empirically confirmed by the build output of this file.
  - **Five** additionally depend on **named, scoped, physically-motivated
    axioms** (four distinct named axioms across these five theorems),
    each documented in its source file:
    - `mitosis_optimal_in_supercritical_phase` →
      `SGC.Symbiosis.mitosis_reduces_structural_free_energy` (free-energy
      postulate; dischargeable via Lifshitz critical-dimension formalism).
    - `hidden_entropy_lower_bound` and `efficiency_requires_prediction` →
      `SGC.Thermodynamics.gaspard_path_space_identity` (renamed from
      `gaspard_maes_bridge` on 2026-05-25 to make the path-space gap
      explicit). Full closure requires path-space probability measures +
      time-reversal operator + Donsker-Varadhan / Maes-Netočný identity —
      none of this infrastructure exists in Mathlib in the form needed
      for finite Markov chains. The renamed axiom's docstring enumerates
      precisely the four-step staging and which steps are
      infrastructure-comfortable vs. genuinely open.
    - `hidden_entropy_bounded_by_defect` →
      `SGC.Thermodynamics.hidden_entropy_bound_from_trajectory` (upper
      bound from trajectory averages; companion to the lower bound).
    - `housekeeping_zero_iff_detailed_balance` →
      `SGC.Thermodynamics.zero_entropy_implies_zero_current` (Gibbs
      case-equality applied pointwise to the Schnakenberg formula).

  The seven `CelegansFloquetTsallis` bridge theorems all sit at the
  WKL₀ baseline. They are the Branch A empirical anchor: they prove
  `r = 0.08 → q = 1.92 → α = 0.04` symbolically, with no biological
  assumptions beyond the single named constant `CelegansLinearityRatio`
  (which is itself just a literal `def`, not an axiom). Any empirical
  measurement of `α ≈ 0.04` in C. elegans pharyngeal pump dynamics
  confirms the discrete Floquet–Tsallis ↔ q-LIL bridge.

  The eight `FluxDecomposition` theorems formalize the symmetric /
  antisymmetric generator splitting `L = L_sym + L_anti`. Seven of them
  sit at the WKL₀ baseline; only `housekeeping_zero_iff_detailed_balance`
  invokes the small `zero_entropy_implies_zero_current` axiom. The
  remaining four FluxDecomposition axioms (`pi_adjoint_inner`,
  `normal_of_self_adjoint`, `sector_condition_companion`,
  `non_normality_from_flux`) are scoped to that file; the first three
  are routine algebra (closure tracked in this sprint), the fourth is
  a research conjecture about non-normality bounds.

  This is a strong empirical statement: the SGC formalization is, today,
  fully constructive in mathematical content (the `Classical.choice`
  invocations are notational — `open Classical` for decidability sugar
  and Filter.Tendsto manipulation — not load-bearing for actual real-
  number content beyond what RCA₀ provides via the `[Fintype V]` firewall).
  Where we *do* postulate non-trivially, each is a named, scoped,
  physically-motivated axiom — explicitly enumerated in the bullet list
  above.

  Specific notes:

  - **`conjecture_C0`**: uses `Classical.choice` indirectly via
    `Filter.Tendsto.congr'` (which uses `Filter.eventually_atTop`,
    which uses choice for the `∃ N` quantifier). The structural step
    (indicator decomposition + matrix encoding) is fully constructive;
    only the convergence statement uses choice.

  - **`conjecture_C1`**: same as C-0; the key step
    `Filter.Tendsto.congr'` uses choice. Eventual positivity from
    `Real.exp_one_lt_d9` is constructive (numeric bound).

  - **`conjecture_C2_hard_half`**: fully constructive once the
    asymmetric blanket is constructed. Uses `Classical.byContradiction`
    only via `push_neg`, which is propext-comfortable.

  - **`conjecture_C3`**: case split on sign of `T.current x y` uses
    `le_or_gt`, which is decidable on `ℝ` (excluded middle, hence
    `Classical.choice` formally).

  - **`gauge_preserves_satisfiability`**: pure ℤ₂ algebra.
    `fin_cases` is constructive on finite types; `decide` on ZMod 2
    is computational.

  - **`unfrustrated_iff_gauge_positive`**: structural reasoning via
    proof-irrelevance + `subst`. The `signedGraph_ext` helper uses
    `cases` + `subst` + `rfl`, fully constructive.

  ## 4. The continuous-limit firewall

  When `[Fintype V]` is unfrozen for the deeper Belkin-Niyogi pass on a
  compact Riemannian manifold, we expect the following new axioms to
  appear:

  - **`Classical.byContradiction`** directly (currently only via `push_neg`).
  - **`Real.sSup`** / **`sInf`** for unbounded suprema (ATR₀ territory).
  - **Lebesgue measure / Borel σ-algebra** machinery (Π¹₁-CA₀ for the full
    Borel hierarchy, though most physics-level uses stay in ACA₀).
  - **Fixed-point theorems on infinite-dimensional spaces** (Schauder,
    Banach) which Mathlib proves via `Classical.choice` essentially.

  Each new axiom appearing in this audit *is* the Reverse Mathematics
  jump made explicit. That is the signal we want.
-/

end SGC.Foundations.AxiomAudit
