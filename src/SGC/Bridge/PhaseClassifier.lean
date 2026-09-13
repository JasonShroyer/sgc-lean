/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Bridge.DiscreteFluidDynamics

/-!
# The Three-Phase SGC Classifier (discrete Chern–Hamilton phases)

Discrete, finite-system formalization of the three-leg classification suggested by
the Chern–Hamilton resolution (Mitsumatsu–Peralta-Salas–Slobodeanu, arXiv:2311.15833:
critical compatible metrics exist iff Sasakian or algebraic Anosov) and proposed as
"Module III" of the Unified Field Theory synthesis (vault: `raw/new papers/A Unified
Field Theory of Spectral Geometry.docx`, triage 2026-06-11).

## The classifier

For a generator `L` with weight `π` and an explicit gap threshold `γ`:

* **Crystal**   — `KillingDefect L π = 0` (detailed balance; Sasakian/critical leg);
* **Mixing**    — `0 < KillingDefect` and `γ ≤ DirichletGap` (current-carrying but
  coercive: the discrete shadow of the structured/Anosov leg);
* **Universal** — `0 < KillingDefect` and `DirichletGap < γ` (current-carrying with
  collapsed coercivity: the regime where computation can persist).

## The theorems (all kernel-targeted, no new axioms)

1. `phase_trichotomy` / disjointness: the three phases partition parameter space.
2. `crystal_iff_reversible`, `mixing_or_universal_has_cycle`: the phases inherit the
   §7 dictionary — crystal = equilibrium, non-crystal = positive-current cycle.
3. `coarseGenerator_eq_simple`: under strong lumpability the π-weighted coarse
   generator (`CoarseGenerator`, any-partition current aggregation) coincides with
   the representative-based `QuotientGeneratorSimple` (Dirichlet-gap machinery) —
   the bridge that lets both legs of the classifier travel together under RG.
4. **`rg_flow_crystalward`** (headline): under strong lumpability, coarse-graining
   can only move a system DOWN the hierarchy Universal → Mixing → Crystal:
   crystal stays crystal, mixing never coarsens to universal, and coarse
   universality certifies fine universality. Consolidation is a one-way flow
   toward rigidity.

## Honest scope (epistemic hygiene)

* `γ` is an EXPLICIT threshold parameter. A fixed finite system has a fixed gap;
  the prose phrase "λ_gap → 0" is meaningful only for families/limits and is NOT
  formalized. The classifier is a `γ`-indexed family of trichotomies.
* `DirichletGap` is the Rayleigh-infimum coercivity constant (see the caveat in
  `Lumpability.lean`): for the non-reversible generators populating the two
  current-carrying phases it is NOT an eigenvalue gap. All statements here use it
  only through the proven `dirichlet_gap_non_decrease`.
* Structural stability of the Anosov leg (noise robustness of conjugacy classes)
  is NOT formalized — no discrete structural-stability theory exists in this
  development. "Mixing" names the regime by analogy; its kernel content is the
  `(K > 0, γ ≤ gap)` predicate and the RG theorems below.
-/

noncomputable section

namespace SGC.Bridge.PhaseClassifier

open Finset Matrix
open SGC.Thermodynamics
open SGC.Bridge.DiscreteFluidDynamics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## §1. The three phases -/

/-- **Crystal phase**: zero Killing defect — equilibrium/detailed balance, the
    discrete Sasakian (critical) leg. -/
def CrystalPhase (L : Matrix V V ℝ) (pi_dist : V → ℝ) : Prop :=
  KillingDefect L pi_dist = 0

/-- **Mixing phase** (threshold `γ`): positive Killing defect with coercivity at
    least `γ` — current-carrying but spectrally stiff. Discrete shadow of the
    algebraic-Anosov leg of arXiv:2311.15833. -/
def MixingPhase (γ : ℝ) (L : Matrix V V ℝ) (pi_dist : V → ℝ) : Prop :=
  0 < KillingDefect L pi_dist ∧ γ ≤ DirichletGap L pi_dist

/-- **Universal phase** (threshold `γ`): positive Killing defect with coercivity
    below `γ` — persistent current with collapsed stiffness, the regime in which
    long computations can survive. -/
def UniversalPhase (γ : ℝ) (L : Matrix V V ℝ) (pi_dist : V → ℝ) : Prop :=
  0 < KillingDefect L pi_dist ∧ DirichletGap L pi_dist < γ

/-! ## §2. Trichotomy and disjointness -/

/-- Every system is in exactly one phase (existence half). -/
theorem phase_trichotomy (γ : ℝ) (L : Matrix V V ℝ) (pi_dist : V → ℝ) :
    CrystalPhase L pi_dist ∨ MixingPhase γ L pi_dist ∨ UniversalPhase γ L pi_dist := by
  rcases (killingDefect_nonneg L pi_dist).eq_or_gt with heq | hpos
  · exact Or.inl heq
  · rcases lt_or_ge (DirichletGap L pi_dist) γ with hlt | hge
    · exact Or.inr (Or.inr ⟨hpos, hlt⟩)
    · exact Or.inr (Or.inl ⟨hpos, hge⟩)

theorem crystal_not_mixing (γ : ℝ) (L : Matrix V V ℝ) (pi_dist : V → ℝ) :
    ¬ (CrystalPhase L pi_dist ∧ MixingPhase γ L pi_dist) := by
  rintro ⟨hc, hpos, -⟩
  rw [CrystalPhase] at hc
  rw [hc] at hpos
  exact lt_irrefl 0 hpos

theorem crystal_not_universal (γ : ℝ) (L : Matrix V V ℝ) (pi_dist : V → ℝ) :
    ¬ (CrystalPhase L pi_dist ∧ UniversalPhase γ L pi_dist) := by
  rintro ⟨hc, hpos, -⟩
  rw [CrystalPhase] at hc
  rw [hc] at hpos
  exact lt_irrefl 0 hpos

theorem mixing_not_universal (γ : ℝ) (L : Matrix V V ℝ) (pi_dist : V → ℝ) :
    ¬ (MixingPhase γ L pi_dist ∧ UniversalPhase γ L pi_dist) := by
  rintro ⟨⟨-, hge⟩, ⟨-, hlt⟩⟩
  exact absurd hlt (not_lt.mpr hge)

/-! ## §3. Semantic anchors: phases inherit the §7 dictionary -/

/-- Crystal = equilibrium: the crystal phase is exactly detailed balance. -/
theorem crystal_iff_reversible (L : Matrix V V ℝ) (pi_dist : V → ℝ) :
    CrystalPhase L pi_dist ↔ DetailedBalance L pi_dist :=
  killingDefect_eq_zero_iff_reversible L pi_dist

/-- Both current-carrying phases support a directed cycle of strictly positive
    probability current — the topological signature shared by Mixing and
    Universal, distinguishing them from Crystal. -/
theorem mixing_or_universal_has_cycle (γ : ℝ) (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hrow : ∀ x, ∑ y, L x y = 0) (hstat : IsStationary L pi_dist)
    (h : MixingPhase γ L pi_dist ∨ UniversalPhase γ L pi_dist) :
    ∃ (len : ℕ) (c : ℕ → V), 0 < len ∧ c 0 = c len ∧
      ∀ m < len, 0 < ProbabilityCurrent L pi_dist (c m) (c (m + 1)) := by
  have hK : 0 < KillingDefect L pi_dist := by rcases h with ⟨hK, -⟩ | ⟨hK, -⟩ <;> exact hK
  exact (killingDefect_pos_iff_positive_current_cycle L pi_dist hrow hstat).mp hK

/-! ## §4. The coarse-generator bridge

`CoarseGenerator` (EntropyProduction; π-weighted, any partition) powers the current
and Killing-defect heredity theorems of `DiscreteFluidDynamics` §4. The Dirichlet-gap
machinery of `Lumpability` runs on `QuotientGeneratorSimple`. Under strong
lumpability the two coincide, so the classifier's two axes coarse-grain together. -/

/-- The π-weighted coarse generator equals the Lumpability weighted quotient
    generator — a lumpability-free sum identity (collapse the inner `y`-sum). -/
lemma coarseGenerator_eq_weighted (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (A B : P.Quot) :
    CoarseGenerator L P pi_dist A B = QuotientGenerator L P pi_dist hπ A B := by
  simp only [CoarseGenerator, CoarseStationaryDist, QuotientGenerator, row_sum_block]
  rw [if_neg (ne_of_gt (pi_bar_pos P hπ A)), one_div, inv_mul_eq_div]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : P.quot_map x = A
  · simp only [hx, true_and, if_true, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : P.quot_map y = B <;> simp [hy]
  · simp [hx]

/-- Under strong lumpability the π-weighted coarse generator coincides with the
    representative-based simple quotient generator. -/
lemma coarseGenerator_eq_simple (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (hL : IsStronglyLumpable L P) :
    CoarseGenerator L P pi_dist = QuotientGeneratorSimple L P := by
  ext A B
  rw [coarseGenerator_eq_weighted L P pi_dist hπ A B,
      quotient_generator_eq_simple L P pi_dist hπ hL A B]

/-- The Dirichlet gap of the π-weighted coarse system IS the quotient Dirichlet gap
    of the Lumpability tower — the gap axis of the classifier transports along RG. -/
lemma dirichletGap_coarse_eq_bar (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (hL : IsStronglyLumpable L P) :
    DirichletGap (CoarseGenerator L P pi_dist) (pi_bar P pi_dist)
      = DirichletGap_bar L P pi_dist := by
  rw [DirichletGap, DirichletGap_bar, coarseGenerator_eq_simple L P pi_dist hπ hL]
  rfl

/-! ## §5. RG heredity of the Killing-defect axis -/

/-- **Crystal is RG-stable**: a crystal stays a crystal under any coarse-graining
    (phase-vocabulary form of `reversible_quotient_of_reversible`). -/
theorem crystal_rg_stable (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (h : CrystalPhase L pi_dist) :
    CrystalPhase (CoarseGenerator L P pi_dist) (pi_bar P pi_dist) :=
  (killingDefect_eq_zero_iff_reversible _ _).mpr
    (reversible_quotient_of_reversible L P pi_dist hπ
      ((killingDefect_eq_zero_iff_reversible L pi_dist).mp h))

/-- **Coarse vorticity certifies fine vorticity**: positive coarse Killing defect
    forces positive fine Killing defect — current cycles seen at the coarse scale
    are never artifacts of the coarse-graining. -/
theorem coarse_vorticity_certifies_fine (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (h : 0 < KillingDefect (CoarseGenerator L P pi_dist) (pi_bar P pi_dist)) :
    0 < KillingDefect L pi_dist := by
  rcases (killingDefect_nonneg L pi_dist).eq_or_gt with heq | hlt
  · exfalso
    have hdb : DetailedBalance L pi_dist :=
      (killingDefect_eq_zero_iff_reversible L pi_dist).mp heq
    have hzero : KillingDefect (CoarseGenerator L P pi_dist) (pi_bar P pi_dist) = 0 :=
      (killingDefect_eq_zero_iff_reversible _ _).mpr
        (reversible_quotient_of_reversible L P pi_dist hπ hdb)
    rw [hzero] at h
    exact lt_irrefl 0 h
  · exact hlt

/-! ## §6. The headline: RG flow is crystal-ward -/

/-- **Coarse universality certifies fine universality**: if the coarse-grained
    system is in the Universal phase, so is the fine system. Contrapositive of the
    one-way flow: consolidation can destroy universality but never create it. -/
theorem coarse_universal_certifies_fine_universal (γ : ℝ) (L : Matrix V V ℝ)
    (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (hL : IsStronglyLumpable L P)
    (hS : (RayleighSetBlockConstant L P pi_dist).Nonempty)
    (hT_bdd : BddBelow (RayleighSet L pi_dist))
    (h : UniversalPhase γ (CoarseGenerator L P pi_dist) (pi_bar P pi_dist)) :
    UniversalPhase γ L pi_dist := by
  obtain ⟨hK, hgap⟩ := h
  refine ⟨coarse_vorticity_certifies_fine L P pi_dist hπ hK, ?_⟩
  rw [dirichletGap_coarse_eq_bar L P pi_dist hπ hL] at hgap
  exact lt_of_le_of_lt (dirichlet_gap_non_decrease L P pi_dist hL hS hT_bdd) hgap

/-- **RG flow is crystal-ward**: under strong lumpability, coarse-graining is
    monotone on the phase hierarchy Universal > Mixing > Crystal:
    (i) crystal stays crystal; (ii) mixing never coarsens to universal;
    (iii) coarse universality certifies fine universality.
    Discrete, kernel-sealed form of "consolidation flows toward rigidity" — the
    RG-monotone refinement of the Chern–Hamilton phase picture. -/
theorem rg_flow_crystalward (γ : ℝ) (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (hL : IsStronglyLumpable L P)
    (hS : (RayleighSetBlockConstant L P pi_dist).Nonempty)
    (hT_bdd : BddBelow (RayleighSet L pi_dist)) :
    (CrystalPhase L pi_dist →
        CrystalPhase (CoarseGenerator L P pi_dist) (pi_bar P pi_dist)) ∧
    (MixingPhase γ L pi_dist →
        ¬ UniversalPhase γ (CoarseGenerator L P pi_dist) (pi_bar P pi_dist)) ∧
    (UniversalPhase γ (CoarseGenerator L P pi_dist) (pi_bar P pi_dist) →
        UniversalPhase γ L pi_dist) := by
  refine ⟨crystal_rg_stable L P pi_dist hπ, ?_,
    coarse_universal_certifies_fine_universal γ L P pi_dist hπ hL hS hT_bdd⟩
  rintro ⟨-, hge⟩ ⟨-, hlt⟩
  rw [dirichletGap_coarse_eq_bar L P pi_dist hπ hL] at hlt
  exact absurd (le_trans hge (dirichlet_gap_non_decrease L P pi_dist hL hS hT_bdd))
    (not_le.mpr hlt)

end SGC.Bridge.PhaseClassifier
