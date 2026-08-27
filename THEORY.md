# The SGC Codex

**The Spectral Geometry of Consolidation: a kernel-checked theory of emergence
in finite stochastic systems.**

Version 1.0 — 2026-08-26. Every theorem named below is machine-checked in
Lean 4 against Mathlib, closes over exactly the classical axioms
`[propext, Classical.choice, Quot.sound]`, and is pinned by a per-theorem
dependency certificate in `scripts/AxiomAudit.lean` (56 gated theorems;
build green; public archive: branch `formalization` of
[JasonShroyer/sgc-lean](https://github.com/JasonShroyer/sgc-lean), indexed
on the Lean Reservoir).

---

## 0. The subject, in one breath

> **A macro-level is a description that has forgotten where probability sits
> inside its blocks. When the forgetting is exact, one operation makes the
> world smoother, less informative, and less dissipative at once, and the
> macro-law is exact forever. When it is imperfect, the forgotten measure
> re-enters as a single canonical defect — simultaneously a field, a number,
> and an operator — whose size prices the validity of every macroscopic
> prediction in physical time, whose zero set is exact emergence, and whose
> topological shadow is priced by entropy production.**

Everything below is the development of this subject.

---

## 1. The objects (the ladder)

| Object | Lean name | Module |
|---|---|---|
| Partition / coarse-graining | `Partition V`, `lift_matrix` | `Renormalization.Lumpability` |
| Exact lumpability | `IsStronglyLumpable` | `Renormalization.Lumpability` |
| Structural quotient | `QuotientGeneratorSimple` | `Renormalization.Lumpability` |
| Physical (π-weighted) quotient | `CoarseGenerator` | `Thermodynamics.EntropyProduction` |
| Residual field (measure re-entry, pointwise) | `residual` | `Renormalization.MeasureReentry` |
| The defect 𝔇_π² (measure re-entry, scalar) | `defectSq` | `Renormalization.MeasureReentry` |
| Closure commutator 𝒞 = LK − KQ^π (operator) | `closureCommutator` | `Renormalization.MeasureReentry` |
| Affinity charge (cycle holonomy / Wilson loop) | `AffinityCharge` | `Bridge.AffinityProtection` |
| Killing defect (Frobenius mass of current) | `KillingDefect`, `KillingDefectDT` | `Bridge.DiscreteFluidDynamics`, `Bridge.TopologicalSensing` |
| Entropy production | `EntropyProductionRate` | `Thermodynamics.EntropyProduction` |
| Winding / loop observables | `windingSum`, `cycleSum`, `flux` | `Bridge.TopologicalSensing` |
| Weighted adjoint (constructed, not assumed) | `adjoint_pi` | `Axioms.GeometryGeneral` |

---

## 2. The theorem ring

### Register A — exact emergence (ε = 0)

- **The Unification Lemma** (`coarseGenerator_eq_quotientGeneratorSimple`):
  at exact lumpability the physical and structural quotients are the SAME
  operator — **the stationary measure is gauge at ε = 0**; it drops out of
  renormalization entirely.
- **The Trinity** (`three_arrows`): for one exactly lumpable coarse-graining,
  the single quotient chain is simultaneously
  (i) at least as curved (`RicciCurvatureBound_quotient` — CD(ρ,∞) descends),
  (ii) at most as dissipative (`hidden_entropy_nonneg` via
  `coarse_ep_eq_quotient_ep`),
  (iii) at most as informative (`data_processing_inequality`).
  One operation, three one-way laws, one theorem.
- **Eternal closure**, discrete and continuous: zero commutator gives exact
  intertwining at every power (`eternal_closure_of_zero_commutator`) and for
  the true CTMC semigroup at every real time
  (`exp_closure_of_zero_commutator`, via rectangular exponential
  intertwining `exp_intertwine`).
- Strictness: coarse-graining can strictly IMPROVE curvature
  (`StarExample.curvature_hiding` — curvature can be created, i.e. hidden,
  by quotients; prior art: Pedrotti–Salez, Cushing–Kamtue–Liu–Peyerimhoff).
- Mechanism inclusions: symmetry-induced lumpability is a strict subclass of
  equitable structure (`SymmetryLumpability`); optimal partitions exist
  (`optimal_partition_exists`).

### Register B — the language of imperfection (ε > 0)

- **Three faces, one object**: the commutator's entries ARE the residual
  field (`closureCommutator_entry`); 𝔇_π² IS its π-weighted Frobenius norm²
  (`defectSq_eq_weighted_commutator_frobenius`) — identities, not bounds.
- **The zero-defect equivalence** (`defectSq_eq_zero_iff_stronglyLumpable`):
  exact emergence is the exact zero set of the defect. The Trinity is the
  boundary condition of the ε > 0 theory.
- `Q^π` is the conditional exit average — canonical, representative-free
  (`coarseGenerator_eq_conditional_exit_average`); the coarse kernel of a
  stochastic kernel is stochastic (`coarseKernel_isStochastic`): the
  macro-law is bona fide dynamics at EVERY defect level.
- **The discrete Duhamel identity** (`power_closure_telescoping`): every
  finite-time closure error is a sum of single re-entry events, propagated
  by the fine dynamics before the event and the macro law after it. Hidden
  memory is the accumulated re-entry series — exactly, as algebra.

### Register C — horizons (defect prices prediction, in physical time)

- **Kernel Horizon** (`kernel_closure_error_le`):
  ‖Tⁿ K − K T̂ⁿ‖∞ ≤ n·‖𝒞‖∞ — linear in steps, rate = one re-entry event.
  Tolerance reading: `within_tolerance_of_defect_small` (inverse-defect
  horizon).
- **Norm conversion** (`commutator_linfty_le_sqrt_defect`):
  ‖𝒞‖∞ ≤ √(|Quot|·𝔇_π²/p_min); end-to-end chain
  (`end_to_end_physical_horizon`): 𝔇_π ⟹ ‖𝒞‖∞ ⟹ error(t) in physical time.
- **The exact Euler bridge**: coarse(1+ΔtL) = 1+ΔtQ^π and
  𝒞(1+ΔtL) = Δt·𝒞(L) EXACTLY (`coarseGenerator_eulerStep`,
  `closureCommutator_eulerStep`) — no O(Δt²) loss; error(t=nΔt) ≤ t·‖𝒞_L‖
  uniformly in the discretization (`physical_time_closure_error`).
- **Eternal approximate validity under mixing**
  (`kernel_closure_error_le_uniform`): with contraction rate α < 1, the
  closure error NEVER exceeds ‖𝒞‖/(1−α) at any horizon — the leak is
  bounded, not cumulative. The commutator's columns are π-centered
  (`commutator_columns_centered`): the re-entry field lives in exactly the
  subspace mixing contracts. Validity becomes an error-budget criterion:
  ‖𝒞‖/(1−α) ≤ η.
- Earlier trajectory forms: `trajectory_closure_bound` (O(εt), all
  generators), `NCD_uniform_error_bound` (O(ε/γ)); and the formally
  DISPROVED `NCD_spectral_stability` (horizontal phase drift is real).

### Register D — charge, dissipation, topology (what protects, what leaks)

- **Kolmogorov obstruction / protection**: one charged cycle (nonzero
  affinity holonomy) forces strictly positive Killing defect for EVERY
  measure (`killingDefect_pos_of_affinityCharge_ne_zero`); charge-conserving
  annealing can never reach reversibility (`annealing_protection`).
- **Gauge protection is exact and eternal** (`windingSum_exact`,
  `cycleSum_gauge_invariant`): loop observables cancel all local (gauge)
  clutter deterministically, on every sample path.
- **Silence theorems**: stationarity kills gauge flux
  (`flux_exact_eq_zero_of_stationary`); detailed balance kills the mean
  drift of every antisymmetric loop observable
  (`flux_eq_zero_of_detailedBalance`).
- **The dissipation bound** (`flux_sq_le_killingDefect`):
  (2·flux ξ)² ≤ KillingDefect·‖ξ‖² — systematic topological drift is priced
  by irreversibility (elementary finite cousin of the mean-current half of
  thermodynamic uncertainty relations; variance-form TUR NOT claimed).
  Linear drift law: E[winding](t) = t·flux
  (`expectedWinding_eq_time_mul_flux`).
- **THE HODGE DECOMPOSITION** (`HodgeDecomposition`, the ring's capstone):
  every antisymmetric edge field splits explicitly and uniquely into an
  exact (gauge) part and a divergence-free (circulating) part, with
  CLOSED-FORM potential `g_ξ = div(ξ)/|V|` (`div_harmonicPart_eq_zero`,
  `hodge_pythagoras`, `hodge_unique`). **Kirchhoff formalized**
  (`div_currentMatrix_eq_zero`): the stationary current is a pure
  circulation — the Killing defect is a cycle-space quantity. Holonomy AND
  drift factor through the Hodge class, and the dissipation bound SHARPENS
  to the circulating norm alone (`flux_sq_le_killingDefect_sharp`); bundle:
  `holonomy_ring_unification`. Prior art: Eckmann 1944, Jiang–Lim–Yao–Ye
  2011, Schnakenberg 1976.

### Register E — boundaries of the knowable

- Classical channels force zero coherent backaction
  (`classical_embedding_forces_alpha_zero`) — no quantum-style error
  correction in classical stochastic systems.
- Curvature-comparison undecidability (`CurvatureUndecidability` +
  `HaltingCompiler` via Mathlib's `Turing.TM0`): geometric questions about
  generators inherit the halting problem. Halting is a cylinder observable
  with a resolution horizon (`CantorHalting`), formalizing the
  Moore–Miranda bridge at the finite level.
- The p-adic/Cantor path-space substrate (`PadicPathSpace`); the priced
  boundary (`BoundaryReadout`, `DissipationFloor`: two-sided price of
  interiority).

---

## 3. The verification apparatus (the methodology IS a result)

1. **Per-theorem certificates, not project-wide counts**: 56 audit-gated
   theorems, each `#print axioms`-pinned to the classical trio.
2. **Satisfiability-first axiom auditing**: axioms are stress-tested for
   degenerate-parameter models before being trusted. This discipline
   mechanically derived `False` twice from plausible axiom families (the
   unhypothesized weighted-adjoint spec; the unlinked Bakry–Émery energy
   family) — both repaired same-day, with counterexamples preserved. The
   same disease (vacuous satisfiability) was independently found by the
   community in a public Millennium-problem formalization.
3. **Definitional discharge over trust**: the entire adjoint interface
   (6 axioms) replaced by a concrete construction + kernel theorems;
   `inner_self_adjoint_real` proven with NO positivity hypothesis
   (self-adjointness kills degenerate weights by itself:
   `isSelfAdjoint_inner_symm`).
4. **Tiered trusted surface, archive-not-delete**: 210 → 100 axiom
   declarations (102 unreferenced ones ledgered verbatim and removed; 19
   tiered RESEARCH ARCHIVE; ~81 active, each classified). Nothing deleted;
   everything recoverable; dormant branches labeled with reconnect
   conditions.
5. **Negative results reported**: `NCD_spectral_stability` disproved; the
   spectral-gap exponential-lifetime conjecture for topological protection
   rejected with counterexample before formalization.

---

## 4. Falsifiable hypotheses (NOT theorems; the empirical frontier)

- **H1 (horizon)**: empirical T_η correlates with 1/𝔇_π at fixed mixing.
- **H2 (two faces)**: 𝔇_π and 𝔇_∞ dissociate on rare-state systems; the
  worst-case face governs when initial mass hits rare states.
- **H3 (computation band)**: task utility of physical reservoirs peaks at
  0 < 𝔇_π < 𝔇_critical (nonzero but bounded re-entry). "Computation band"
  is a hypothesis; universal computation claims require a separate encoding
  theorem.
- **Homonym gap**: the SVD-tail sensor ε of the discovery engine relates to
  𝔇_π of a spectrally-defined partition (P1 of the delusion audit).
- Pre-registered acceptance thresholds: `insights/0011-closure-atlas-design`.

## 5. Open problems, ranked

1. ~~Discrete Hodge decomposition~~ — **PROVEN 2026-08-26**
   (`holonomy_ring_unification` + sharpened dissipation bound).
2. **Approximate Trinity**: quantified degradation of all three arrows in
   𝔇_π (geometric/informational/thermodynamic leakage bounds).
3. **BKM L0**: the abstract budget-continuation dichotomy for quadratic
   ODEs (`docs/bkm-formalization-design.md`) — the horizon family's
   continuum anchor; Galerkin NS as first instance.
3. **Finite path-space expectation API** (retires trajectory-level
   modeling axioms; makes `expectedWinding` fully intrinsic).
4. **Spectral-gap → contraction-rate instantiation** for the uniform
   horizon (makes α computable from the chain).
5. **Conditional exponential lifetime** with explicit barrier hypothesis
   (βκΔ_E > h); gambler's-ruin toy first.
6. **ε > 0 Duhamel integral** for the true semigroup (`ExpBridge` docstring
   lists the exact missing assembly).
7. Pinsker (isolated debt); satisfiability sweep of remaining active
   axioms; variance-form TUR.

## 6. Prior art and neighbors (honesty ledger)

Kemeny–Snell (lumpability); Simon–Ando (NCD); Pedrotti–Salez 2025 and
Cushing–Kamtue–Liu–Peyerimhoff 2021 (curvature under quotients — predates
our "curvature hiding" novelty claims, acknowledged in-module);
Schnakenberg (cycle theory of NESS); Barato–Seifert (TUR — our dissipation
bound is the elementary mean-current shadow); Jacobson (thermodynamic
derivation of dynamics — dictionary entry only, no continuum claim);
Renner/SciNet (question-conditioned latents — Atlas candidate partitions);
Moore 1990, Cardona–Miranda–Peralta-Salas (fluid computation and trajectory
undecidability — our `CantorHalting`/`HaltingCompiler` formalize the finite
shadow); Tao (computational blow-up program — see BKM design note).

---

*The theory's own moral, applied to itself: this document is the lumpable
partition of a five-week fine-grained trajectory. Its defect against the
full corpus is nonzero but bounded; its validity horizon is long; its
maintenance is the continuing proof that the system persists.*
