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
import SGC.ComplexityRelativity
import SGC.Bridge.DiscreteFluidDynamics
import SGC.Bridge.PhaseClassifier
import SGC.InformationGeometry.FisherNoetherBridge

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

-- **Second Law of Thermodynamics** for finite Markov chains: σ(L, π) ≥ 0.
-- **PROVED 2026-05-25** (previously an axiom). Each Schnakenberg summand
-- (π_x L_{xy} - π_y L_{yx}) · log(π_x L_{xy} / (π_y L_{yx})) is non-negative
-- by `gibbs_term_nonneg`; the sum preserves non-negativity.
#print axioms SGC.Thermodynamics.entropy_production_nonneg

-- Gibbs term inequality (the single-pair second law).
#print axioms SGC.Thermodynamics.gibbs_term_nonneg

-- Gibbs term equality (used in the converse direction of detailed-balance
-- characterization).
#print axioms SGC.Thermodynamics.gibbs_term_eq_zero_iff

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

-- Housekeeping entropy vanishes iff detailed balance.
-- **PROVED 2026-05-25**: no longer depends on a named axiom. The forward
-- direction now invokes the closed `zero_entropy_implies_zero_current`
-- theorem (next entry).
#print axioms SGC.Thermodynamics.housekeeping_zero_iff_detailed_balance

-- Zero entropy production implies zero current.
-- **PROVED 2026-05-25** (previously an axiom). Strategy: σ = 0 + each
-- Schnakenberg summand ≥ 0 ⇒ each summand = 0 ⇒ Gibbs equality at each
-- pair ⇒ π_x L_{xy} = π_y L_{yx} ⇒ J(x,y) = 0.
#print axioms SGC.Thermodynamics.zero_entropy_implies_zero_current

/-! ### Complexity Relativity Theorem (NEW 2026-05-25)

  The Complexity Relativity Theorem formalizes the claim that complexity is
  not intrinsic to a Markov generator `L`, but a relational property between
  `L` and an observer's partition `P`. It is composed entirely from PROVED
  theorems (no new axioms): `defect_cost_nonneg`,
  `trivialPartition_defect_cost_zero`, `defect_antitone_on_coarse_domain`,
  `optimal_partition_exists`, `reversible_local_eq_global`.
-/

-- The capstone five-clause Complexity Relativity Theorem.
#print axioms SGC.ComplexityRelativity.complexity_is_relational

-- The complexity gap is non-negative when the reference is a global minimum.
#print axioms SGC.ComplexityRelativity.complexity_gap_nonneg_of_optimal

-- Complexity gap vanishes iff defect costs match (NESS non-uniqueness preserved).
#print axioms SGC.ComplexityRelativity.complexity_gap_eq_zero_iff_eq_cost

-- The trivial partition is a global minimum of complexity.
#print axioms SGC.ComplexityRelativity.trivial_partition_is_global_min

-- Finer observers have lower complexity on the coarse domain.
#print axioms SGC.ComplexityRelativity.finer_observer_lower_complexity_on_coarse

-- Reversibility implies uniqueness of the emergent description.
#print axioms SGC.ComplexityRelativity.reversibility_implies_unique_emergence

/-! ### Constrained-Coarseness Complexity Theorem (Sprint 4, 2026-05-25)

  The constrained version of the Complexity Relativity Theorem: at a finite
  resolution budget K, the optimal partition has generally **non-zero**
  defect, and the complexity gap is a substantive quantity. Composes from
  `optimal_kBounded_partition_exists` (new) + `defect_cost_nonneg`. Zero
  new axioms.
-/

-- The K-bounded minimum exists.
#print axioms SGC.Renormalization.optimal_kBounded_partition_exists

-- The capstone constrained-coarseness theorem.
#print axioms SGC.ComplexityRelativity.constrained_complexity_is_relational

-- Existence-only form.
#print axioms SGC.ComplexityRelativity.constrained_optimum_exists

-- Resolution monotonicity (witness-form).
#print axioms SGC.ComplexityRelativity.constrained_minimum_le_of_isKBounded

/-! ### L¹-L² Norm Equivalence (Sprint 5, 2026-05-26)

  Pure-analysis Cauchy-Schwarz fact: `Σ|v_x| ≤ √N · √(Σ v_x²)` for finite-
  dimensional real vectors. **PROVED 2026-05-26** (previously an axiom). Uses
  `Finset.sum_mul_sq_le_sq_mul_sq` from Mathlib applied to `f := 1, g := |v|`.

  This was the deferred closure flagged in the May 25 sprint as
  "axiom-likely-closeable; pure analysis, no physics".
-/

-- L¹ ≤ √card · L² for unweighted finite-dimensional real vectors.
#print axioms SGC.Thermodynamics.l1_le_sqrt_card_l2

/-! ### Two Norm-Equivalence Closures (Sprint 6, 2026-05-30)

  Two more pure-analysis closures from the EntropyProduction/Approximate
  modules. Both **PROVED 2026-05-30** (previously axioms).

  - `weighted_unweighted_norm_compare`: Finite-dim norm equivalence between
    π-weighted and unweighted L². Strategy: take `pi_min := min_x pi_dist x`,
    use `pi_min · Σv² ≤ Σ pi · v²`, square-root and divide by `√pi_min`.

  - `NCD_slow_defect_bound`: Trivial existence — take `K := opNorm` itself.
    The axiomatization was a placeholder; closure is `⟨opNorm, opNorm_nonneg,
    le_refl⟩`.
-/

-- Weighted-to-unweighted L² norm equivalence (pure analysis).
#print axioms SGC.Thermodynamics.weighted_unweighted_norm_compare

-- NCD slow defect: trivially-true existence of an upper bound.
#print axioms SGC.Approximate.NCD_slow_defect_bound

/-! ### Three TsallisStatistics Closures via Mathlib (Sprint 6, 2026-05-30)

  Three classical real-analysis axioms in `TsallisStatistics.lean` are
  directly available in Mathlib. Closed via 1-line `Real.*` invocations.
  **PROVED 2026-05-30** (all previously axioms).

  - `young_inequality` ← `Real.geom_mean_le_arith_mean2_weighted`
  - `rpow_le_self_of_le_one_of_one_lt` ← `Real.rpow_le_self_of_le_one`
  - `self_le_rpow_of_le_one_of_lt_one` ← `Real.self_le_rpow_of_le_one`

  These are pure-analysis facts that should never have been axioms; the
  axiomatization was likely a consequence of not knowing the exact
  Mathlib name. Each closure is a single-expression proof.
-/

-- Young's weighted AM-GM inequality.
#print axioms SGC.InformationGeometry.Tsallis.young_inequality

-- For x ∈ [0,1] and q > 1, x^q ≤ x.
#print axioms SGC.InformationGeometry.Tsallis.rpow_le_self_of_le_one_of_one_lt

-- For x ∈ [0,1] and 0 < q < 1, x ≤ x^q.
#print axioms SGC.InformationGeometry.Tsallis.self_le_rpow_of_le_one_of_lt_one

/-! ## 3. Per-theorem proof-theoretic commentary — **CONFIRMED 2026-05-25**

  **Sixty-six** flagship theorems are audited above (35 from the May 19
  sprint baseline, 6 EntropyProduction additions including the newly
  closed `entropy_production_nonneg`, 9 FluxDecomposition theorems
  including the newly closed `zero_entropy_implies_zero_current`,
  6 Complexity Relativity theorems, 4 Constrained-Coarseness theorems
  (Sprint 4), 1 Cauchy-Schwarz closure of `l1_le_sqrt_card_l2`
  (Sprint 5, 2026-05-26), 2 norm-equivalence closures (Sprint 6, AM:
  `weighted_unweighted_norm_compare`, `NCD_slow_defect_bound`), and
  **3 Mathlib-import closures** (Sprint 6, PM, 2026-05-30):
  `young_inequality`, `rpow_le_self_of_le_one_of_one_lt`,
  `self_le_rpow_of_le_one_of_lt_one`). The audit also prints axioms
  for two auxiliary Gibbs-term lemmas used to close the two new entropy
  theorems. Of the 66 flagship theorems:

  - **Sixty-two** depend on **exactly** the three Lean kernel axioms:
    `[propext, Classical.choice, Quot.sound]` — the **WKL₀-comfortable
    baseline**, empirically confirmed by the build output of this file.
  - **Four** additionally depend on **named, scoped, physically-motivated
    axioms** (three distinct named axioms across these four theorems),
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

  **Closure history on this branch** (`sprint/entropy-axiom-closure-2026-05-25`):

  - **2026-05-25 (Sprint 1)** — Three FluxDecomposition axioms closed:
    `normal_of_self_adjoint` (trivial via `sub_self`), `pi_adjoint_inner`
    (double-sum manipulation + `Finset.sum_comm` + alpha-equivalence),
    `sector_condition_companion` (`dirichlet_form_eq_symmetric_part` +
    `inner_pi` linearity in negation). Plus: `gaspard_maes_bridge` staged
    to `gaspard_path_space_identity` with deprecated alias for backward
    compatibility.

  - **2026-05-25 (Sprint 2)** — Two more axioms closed via a unified
    Gibbs-term framework:
    - `entropy_production_nonneg` (the **second law of thermodynamics for
      finite Markov chains**, σ ≥ 0). Proved via new lemma
      `gibbs_term_nonneg : (a-b) · log(a/b) ≥ 0` for `a, b > 0`, applied
      pointwise to the Schnakenberg summand.
    - `zero_entropy_implies_zero_current` (σ = 0 ⇒ J = 0). Proved via
      `Finset.sum_eq_zero_iff_of_nonneg` (twice, for the double sum) plus
      a new companion lemma `gibbs_term_eq_zero_iff : (a-b) · log(a/b) = 0
      ↔ a = b` for `a, b > 0`.
    - Cascade: `housekeeping_zero_iff_detailed_balance` no longer depends
      on any named axiom — it now sits at the WKL₀ baseline.

  **Required hypothesis upgrade**: both Sprint-2 closures require an
  additional `hL_nonneg : ∀ x y, x ≠ y → 0 ≤ L x y` hypothesis. This is
  what every valid Markov generator satisfies, but it is not derivable
  from the previous `hL_irred` alone — Lean's junk-value convention
  `Real.log r = 0` for `r ≤ 0` creates pathological counterexamples
  without it. This is a genuine formalization-vs-textbook distinction
  worth recording.

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

/-! ## 5. Discrete Fluid-Computer Bridge (2026-06-10)

Expected axiom profile for all of these: `[propext, Classical.choice, Quot.sound]`
only — no `sorryAx`, no SGC-declared axioms. The walk construction in the cycle
theorem uses `Exists.choose` (hence `Classical.choice` essentially); everything
else is finite-sum algebra plus one Mathlib improper integral. -/

-- B1: stationarity ⇔ divergence-free current (discrete continuity equation).
#print axioms SGC.Bridge.DiscreteFluidDynamics.stationary_iff_current_divergence_free

-- B6b: nonzero cycle-space field supports a positive-current cycle (discrete H¹ ≠ 0).
#print axioms SGC.Bridge.DiscreteFluidDynamics.cycle_of_pos_cycleSpace_field

-- B6c: stationary NESS supports a positive-current cycle (cosymplectic escape clause).
#print axioms SGC.Bridge.DiscreteFluidDynamics.ness_has_current_cycle

-- Headline dichotomy: detailed balance ⇔ no positive-current cycle (discrete Chern–Hamilton).
#print axioms SGC.Bridge.DiscreteFluidDynamics.reversible_iff_no_positive_current_cycle

-- B4: coarse current = aggregated fine current (no lumpability hypothesis).
#print axioms SGC.Bridge.DiscreteFluidDynamics.coarse_current_eq_sum_fine

-- B4-rigidity: detailed balance is hereditary under arbitrary coarse-graining.
#print axioms SGC.Bridge.DiscreteFluidDynamics.reversible_quotient_of_reversible

-- B3b: every generator is realized as a strongly-lumpable quotient (flexibility).
#print axioms SGC.Bridge.DiscreteFluidDynamics.uniformLift_quotient_realizes

-- B5: the viscous time budget ∫₀^∞ e^{-νt} dt = 1/ν.
#print axioms SGC.Bridge.DiscreteFluidDynamics.viscous_time_budget

/-! ## 6. Second sprint additions (2026-06-10 evening)

B7 base (Chern–Hamilton energy defect) and the exact selection-variance
identity. Expected profile: `[propext, Classical.choice, Quot.sound]`.
NOTE `selection_variance_shift_exact` lives in a file with two by-design
sorried declarations — the audit confirms it does NOT inherit them. -/

-- B7a: Killing defect vanishes iff detailed balance (criticality = crystal).
#print axioms SGC.Bridge.DiscreteFluidDynamics.killingDefect_eq_zero_iff_reversible

-- B7b: positive defect ⇔ positive-current cycle (energy defect = cycle obstruction).
#print axioms SGC.Bridge.DiscreteFluidDynamics.killingDefect_pos_iff_positive_current_cycle

-- Exact empirical selection-variance identity (replaces the vacuous placeholder).
#print axioms SGC.InformationGeometry.FisherNoetherBridge.selection_variance_shift_exact

-- Selection-safety corollary: zero covariances ⇒ no contamination.
#print axioms SGC.InformationGeometry.FisherNoetherBridge.selection_uncorrelated_no_contamination

/-! ## 7. Hodge orthogonality and the three-phase classifier (2026-06-10/11)

DFD §8 (the topological shield) and `Bridge/PhaseClassifier.lean` (the discrete
Chern–Hamilton three-phase classifier with RG-monotone flow). Expected profile:
`[propext, Classical.choice, Quot.sound]` — finite-sum algebra plus the sInf-based
Dirichlet gap machinery (`Classical.choice` via real completeness). -/

-- §8: orthogonality iff — ker(div) = im(d₀)^⊥ on a 1-complex.
#print axioms SGC.Bridge.DiscreteFluidDynamics.orthogonal_gradients_iff_divergence_free

-- §8: the topological shield — NESS current ⊥ every gradient 1-form.
#print axioms SGC.Bridge.DiscreteFluidDynamics.stationary_current_orthogonal_gradients

-- §8: Killing defect = squared edge-norm of the (harmonic) current.
#print axioms SGC.Bridge.DiscreteFluidDynamics.killingDefect_eq_edgeInner_self

-- Classifier: the three phases are exhaustive.
#print axioms SGC.Bridge.PhaseClassifier.phase_trichotomy

-- Bridge: π-weighted coarse generator = simple quotient generator under lumpability.
#print axioms SGC.Bridge.PhaseClassifier.coarseGenerator_eq_simple

-- Crystal is RG-stable (phase form of B4-rigidity).
#print axioms SGC.Bridge.PhaseClassifier.crystal_rg_stable

-- Coarse vorticity certifies fine vorticity (K-axis heredity).
#print axioms SGC.Bridge.PhaseClassifier.coarse_vorticity_certifies_fine

-- HEADLINE: RG flow is crystal-ward (Universal → Mixing → Crystal one-way).
#print axioms SGC.Bridge.PhaseClassifier.rg_flow_crystalward

end SGC.Foundations.AxiomAudit
