/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Thermodynamics.FluxDecomposition
import SGC.Renormalization.Lumpability
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The Discrete Fluid-Computer Bridge

Discrete dictionary for the Miranda-program results on fluid computers
(Cardona–Miranda–Peralta-Salas et al.), at the finite-state Markov-generator layer.
Realizes bridge lemmas B1–B6 of `miranda_report.md` (vault, 2026-06-10).

## The Dictionary (continuum ↔ discrete)

| Continuum (steady Euler / contact mirror)       | Discrete (this module)                       |
|-------------------------------------------------|----------------------------------------------|
| velocity field `u` of a steady fluid            | probability current `J(x,y) = πₓLₓᵧ − πᵧLᵧₓ` |
| incompressibility `∇·u = 0`                     | `stationary_iff_current_divergence_free`     |
| static fluid (no rotation)                      | `current_zero_iff_reversible` (lib. cited)   |
| harmonic 1-form / `H¹(M) ≠ 0` escape clause     | `ness_has_current_cycle`                     |
| Chern–Hamilton rigidity (no TC at critical `g`) | `reversible_iff_no_positive_current_cycle`   |
| h-principle flexibility (Reeb embeddings)       | `uniformLift_*` (every quotient is realized) |
| h-principle rigidity (hereditary obstruction)   | `reversible_quotient_of_reversible`          |
| viscous horizon `τ∞ = M/ν` ([PNAS] pp. 8–9)     | `viscous_time_budget`                        |

## Continuum anchors (verified sources)

* Cardona–Miranda–Peralta-Salas–(et al.), PNAS 118 (2021): Turing-complete Euler flows
  in dimension 3; viscous reparametrization budget `∫₀^∞ e^{-νt} dt = 1/ν` (pp. 8–9).
* Dyhr–González-Prieto–Miranda–Peralta-Salas, PNAS Nexus 5:5 (2026), arXiv:2507.07696:
  Turing-complete *stationary Navier–Stokes* states for any `ν ≥ 0` on manifolds with a
  nonvanishing harmonic 1-form (`H¹(M) ≠ 0`). Discrete echo: NESS current survives iff
  the graph carries a positive-current cycle (`ness_has_current_cycle`).
* Mitsumatsu–Peralta-Salas–Slobodeanu, arXiv:2311.15833: critical Chern–Hamilton metrics
  exist iff Sasakian or algebraic Anosov — the rigid (non-universal) phases. Discrete
  echo: `reversible_iff_no_positive_current_cycle` (equilibrium = no cycle).

## Epistemic state

Every declaration in this file is **kernel-proven** (no `sorry`, no new axioms; classical
choice only, via `Exists.choose` in the walk construction). `current_zero_iff_reversible`
is a re-export of the library theorem `detailed_balance_iff_zero_current`
(`Thermodynamics/FluxDecomposition.lean`). The *continuum* statements in the table are
NOT formalized here — the table is a research dictionary, not a claim of equivalence.
-/

noncomputable section

namespace SGC.Bridge.DiscreteFluidDynamics

open Finset BigOperators Matrix Real
open SGC.Thermodynamics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## §1. Divergence and stationarity (B1) -/

/-- `π` is a stationary measure for the generator `L`: the row vector `πᵀL` vanishes
    (columnwise: `∑ₓ π(x) L(x,y) = 0` for every `y`). -/
def IsStationary (L : Matrix V V ℝ) (pi_dist : V → ℝ) : Prop :=
  ∀ y, ∑ x, pi_dist x * L x y = 0

/-- Divergence of an edge field at `x`: the net outflow `∑_y J(x,y)`. -/
def divergence (J : V → V → ℝ) (x : V) : ℝ := ∑ y, J x y

/-- For a conservative generator (zero row sums), the divergence of the probability
    current at `x` is minus the stationarity residual at `x`. -/
lemma divergence_current_eq_neg_residual (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hrow : ∀ x, ∑ y, L x y = 0) (x : V) :
    divergence (ProbabilityCurrent L pi_dist) x = -(∑ z, pi_dist z * L z x) := by
  simp only [divergence, ProbabilityCurrent]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hrow x, mul_zero, zero_sub]

/-- **B1 (discrete continuity equation)**: for a conservative generator, `π` is
    stationary iff the probability current is divergence-free — the discrete `∇·u = 0`
    of a steady flow, in both directions. -/
theorem stationary_iff_current_divergence_free (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hrow : ∀ x, ∑ y, L x y = 0) :
    IsStationary L pi_dist ↔
      ∀ x, divergence (ProbabilityCurrent L pi_dist) x = 0 := by
  constructor
  · intro hstat x
    rw [divergence_current_eq_neg_residual L pi_dist hrow x, hstat x, neg_zero]
  · intro hdiv y
    have h := hdiv y
    rw [divergence_current_eq_neg_residual L pi_dist hrow y] at h
    linarith

/-! ## §2. Equilibrium as a static fluid (B2) -/

/-- **B2 (static fluid = equilibrium)**: the current vanishes everywhere iff `L`
    satisfies detailed balance. Re-export of the kernel-proven library theorem
    `detailed_balance_iff_zero_current`. -/
theorem current_zero_iff_reversible (L : Matrix V V ℝ) (pi_dist : V → ℝ) :
    (∀ x y, ProbabilityCurrent L pi_dist x y = 0) ↔ DetailedBalance L pi_dist :=
  (detailed_balance_iff_zero_current L pi_dist).symm

/-! ## §3. The cycle space and the discrete `H¹ ≠ 0` obstruction (B6)

A nonzero divergence-free current cannot live on a tree: it must close a directed cycle
of strictly positive current. Equilibrium is exactly the absence of such a cycle — the
discrete Chern–Hamilton rigidity dichotomy. -/

/-- Membership in the (discrete) cycle space: antisymmetric and divergence-free. -/
def InCycleSpace (J : V → V → ℝ) : Prop :=
  (∀ x y, J x y = -J y x) ∧ (∀ x, divergence J x = 0)

/-- **B6a**: at stationarity the probability current lies in the cycle space. -/
theorem stationary_current_in_cycle_space (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hrow : ∀ x, ∑ y, L x y = 0) (hstat : IsStationary L pi_dist) :
    InCycleSpace (ProbabilityCurrent L pi_dist) :=
  ⟨fun x y => current_antisymm L pi_dist x y,
   (stationary_iff_current_divergence_free L pi_dist hrow).mp hstat⟩

/-- One step of the positive-current walk: from an edge with positive current, choose a
    successor edge with positive current. -/
private def walkStep {J : V → V → ℝ}
    (hstep : ∀ p : {p : V × V // 0 < J p.1 p.2}, ∃ z, 0 < J p.val.2 z) :
    {p : V × V // 0 < J p.1 p.2} → {p : V × V // 0 < J p.1 p.2} :=
  fun p => ⟨(p.val.2, (hstep p).choose), (hstep p).choose_spec⟩

/-- Pigeonhole closure: an infinite walk along positively-weighted edges in a finite
    state space closes a cycle of positively-weighted edges. -/
private lemma exists_cycle_of_walk {J : V → V → ℝ} (f : ℕ → V)
    (hedge : ∀ n, 0 < J (f n) (f (n + 1))) :
    ∃ (len : ℕ) (c : ℕ → V), 0 < len ∧ c 0 = c len ∧
      ∀ m < len, 0 < J (c m) (c (m + 1)) := by
  obtain ⟨i, j, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  rcases hne.lt_or_gt with hij | hji
  · refine ⟨j - i, fun m => f (i + m), Nat.sub_pos_of_lt hij, ?_, ?_⟩
    · simp only [Nat.add_zero, Nat.add_sub_cancel' hij.le]
      exact heq
    · intro m _
      show 0 < J (f (i + m)) (f (i + (m + 1)))
      have hidx : i + (m + 1) = (i + m) + 1 := by omega
      rw [hidx]
      exact hedge (i + m)
  · refine ⟨i - j, fun m => f (j + m), Nat.sub_pos_of_lt hji, ?_, ?_⟩
    · simp only [Nat.add_zero, Nat.add_sub_cancel' hji.le]
      exact heq.symm
    · intro m _
      show 0 < J (f (j + m)) (f (j + (m + 1)))
      have hidx : j + (m + 1) = (j + m) + 1 := by omega
      rw [hidx]
      exact hedge (j + m)

/-- **B6b (cycle theorem)**: a cycle-space field with one strictly positive edge
    supports a directed cycle of strictly positive edges — nonzero divergence-free
    current forces nontrivial topology (discrete `H¹ ≠ 0`). -/
theorem cycle_of_pos_cycleSpace_field {J : V → V → ℝ} (hJ : InCycleSpace J)
    {x₀ y₀ : V} (hpos : 0 < J x₀ y₀) :
    ∃ (len : ℕ) (c : ℕ → V), 0 < len ∧ c 0 = c len ∧
      ∀ m < len, 0 < J (c m) (c (m + 1)) := by
  obtain ⟨hanti, hdiv⟩ := hJ
  have hstep : ∀ p : {p : V × V // 0 < J p.1 p.2}, ∃ z, 0 < J p.val.2 z := by
    rintro ⟨⟨x, y⟩, hxy⟩
    dsimp only at hxy ⊢
    by_contra hcon
    push_neg at hcon
    have hyx : J y x < 0 := by
      have h := hanti x y
      linarith
    have hsum : ∑ z, J y z = 0 := hdiv y
    have hall := (Finset.sum_eq_zero_iff_of_nonpos (fun z _ => hcon z)).mp hsum
    have hx := hall x (Finset.mem_univ x)
    linarith
  apply exists_cycle_of_walk
    (fun n => ((walkStep hstep)^[n] (⟨(x₀, y₀), hpos⟩ : {p : V × V // 0 < J p.1 p.2})).val.1)
  intro n
  have hsucc : ((walkStep hstep)^[n + 1] (⟨(x₀, y₀), hpos⟩ : {p : V × V // 0 < J p.1 p.2})).val.1
      = ((walkStep hstep)^[n] (⟨(x₀, y₀), hpos⟩ : {p : V × V // 0 < J p.1 p.2})).val.2 := by
    rw [Function.iterate_succ_apply']
    rfl
  rw [hsucc]
  exact ((walkStep hstep)^[n] (⟨(x₀, y₀), hpos⟩ : {p : V × V // 0 < J p.1 p.2})).property

/-- **B6c (NESS ⇒ topological cycle)**: a stationary non-equilibrium steady state
    supports a directed cycle of strictly positive probability current — the discrete
    form of "irreversibility survives only where `H¹ ≠ 0`" (arXiv:2507.07696). -/
theorem ness_has_current_cycle (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hrow : ∀ x, ∑ y, L x y = 0) (hstat : IsStationary L pi_dist)
    (hness : ¬ DetailedBalance L pi_dist) :
    ∃ (len : ℕ) (c : ℕ → V), 0 < len ∧ c 0 = c len ∧
      ∀ m < len, 0 < ProbabilityCurrent L pi_dist (c m) (c (m + 1)) := by
  have hJ := stationary_current_in_cycle_space L pi_dist hrow hstat
  rw [detailed_balance_iff_zero_current] at hness
  push_neg at hness
  obtain ⟨x, y, hxy⟩ := hness
  rcases hxy.lt_or_gt with hneg | hpos
  · have hpos' : 0 < ProbabilityCurrent L pi_dist y x := by
      have h := current_antisymm L pi_dist x y
      linarith
    exact cycle_of_pos_cycleSpace_field hJ hpos'
  · exact cycle_of_pos_cycleSpace_field hJ hpos

/-- **The discrete rigidity dichotomy**: equilibrium (detailed balance) holds iff there
    is *no* directed cycle of strictly positive current. Discrete twin of the
    Chern–Hamilton classification (arXiv:2311.15833): the rigid/static phase versus the
    current-carrying phase where universality becomes possible. -/
theorem reversible_iff_no_positive_current_cycle (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hrow : ∀ x, ∑ y, L x y = 0) (hstat : IsStationary L pi_dist) :
    DetailedBalance L pi_dist ↔
      ¬ ∃ (len : ℕ) (c : ℕ → V), 0 < len ∧ c 0 = c len ∧
          ∀ m < len, 0 < ProbabilityCurrent L pi_dist (c m) (c (m + 1)) := by
  constructor
  · rintro hdb ⟨len, c, hlen, -, hposc⟩
    have h0 := (detailed_balance_iff_zero_current L pi_dist).mp hdb (c 0) (c (0 + 1))
    have h1 := hposc 0 hlen
    rw [h0] at h1
    exact lt_irrefl 0 h1
  · intro hno
    by_contra hness
    exact hno (ness_has_current_cycle L pi_dist hrow hstat hness)

/-! ## §4. h-principle rigidity: current aggregation and heredity (B4)

The π-weighted coarse generator (`CoarseGenerator`, EntropyProduction.lean) aggregates
the fine current exactly: the coarse current of a block pair is the sum of fine currents
crossing it. Consequently detailed balance is *hereditary* downward (fine equilibrium
forces coarse equilibrium), and irreversibility is *hereditary* upward (a NESS quotient
admits no reversible fine model) — for ANY partition, no lumpability needed. -/

/-- The coarse mass `π̄(A)` times the coarse rate `L̄(A,B)` equals the aggregated fine
    flux from block `A` to block `B`. -/
lemma pibar_mul_coarseGenerator (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (A B : P.Quot) :
    pi_bar P pi_dist A * CoarseGenerator L P pi_dist A B =
      ∑ x, ∑ y, (if P.quot_map x = A ∧ P.quot_map y = B
                 then pi_dist x * L x y else 0) := by
  have hne : CoarseStationaryDist P pi_dist A ≠ 0 :=
    ne_of_gt (pi_bar_pos P hπ A)
  simp only [CoarseGenerator, CoarseStationaryDist] at hne ⊢
  rw [if_neg hne]
  field_simp

/-- **B4 (current aggregation / intertwining)**: the probability current of the coarse
    model is the blockwise sum of the fine probability current. The discrete shadow of
    "vorticity pushes forward along the mirror". -/
theorem coarse_current_eq_sum_fine (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (A B : P.Quot) :
    ProbabilityCurrent (CoarseGenerator L P pi_dist) (pi_bar P pi_dist) A B =
      ∑ x, ∑ y, (if P.quot_map x = A ∧ P.quot_map y = B
                 then ProbabilityCurrent L pi_dist x y else 0) := by
  have hsplit : (∑ x, ∑ y, (if P.quot_map x = A ∧ P.quot_map y = B
        then ProbabilityCurrent L pi_dist x y else 0))
      = (∑ x, ∑ y, (if P.quot_map x = A ∧ P.quot_map y = B then pi_dist x * L x y else 0))
      - (∑ x, ∑ y, (if P.quot_map x = A ∧ P.quot_map y = B then pi_dist y * L y x else 0)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h : P.quot_map x = A ∧ P.quot_map y = B
    · simp [h, ProbabilityCurrent]
    · simp [h]
  have hswap : (∑ x, ∑ y, (if P.quot_map x = A ∧ P.quot_map y = B
        then pi_dist y * L y x else 0))
      = (∑ x, ∑ y, (if P.quot_map x = B ∧ P.quot_map y = A then pi_dist x * L x y else 0)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases h1 : P.quot_map a = B <;> by_cases h2 : P.quot_map b = A <;>
      simp [h1, h2, and_comm]
  show pi_bar P pi_dist A * CoarseGenerator L P pi_dist A B
      - pi_bar P pi_dist B * CoarseGenerator L P pi_dist B A = _
  rw [pibar_mul_coarseGenerator L P pi_dist hπ A B,
      pibar_mul_coarseGenerator L P pi_dist hπ B A, hsplit, hswap]

/-- **B4-rigidity (heredity of equilibrium)**: if the fine model satisfies detailed
    balance, every coarse-graining of it does too. Equivalently (contrapositive): an
    irreversible coarse model admits NO reversible fine completion — irreversibility is
    a hereditary obstruction that cannot be "patched" by adding hidden states. -/
theorem reversible_quotient_of_reversible (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (hdb : DetailedBalance L pi_dist) :
    DetailedBalance (CoarseGenerator L P pi_dist) (pi_bar P pi_dist) := by
  rw [detailed_balance_iff_zero_current]
  intro A B
  rw [coarse_current_eq_sum_fine L P pi_dist hπ A B]
  have h0 := (detailed_balance_iff_zero_current L pi_dist).mp hdb
  refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
  by_cases h : P.quot_map x = A ∧ P.quot_map y = B
  · simp [h, h0 x y]
  · simp [h]

/-- **B4-contrapositive (NESS heredity)**: a non-equilibrium quotient forces a
    non-equilibrium fine model. Coarse vorticity certifies fine vorticity. -/
theorem ness_quotient_forces_ness_fine (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (hness : ¬ DetailedBalance (CoarseGenerator L P pi_dist) (pi_bar P pi_dist)) :
    ¬ DetailedBalance L pi_dist :=
  fun hdb => hness (reversible_quotient_of_reversible L P pi_dist hπ hdb)

/-! ## §5. h-principle flexibility: every coarse model is realized (B3)

The flexibility half of the discrete h-principle pair: ANY generator `M` on a coarse
space `W` is the strongly-lumpable quotient of a fine model on `W × F` (spread uniformly
over the fiber `F`). With §4 this gives the full discrete flexibility/rigidity duality:
you can always *add* hidden structure (B3), but you can never *remove* irreversibility
by doing so (B4). -/

section Flexibility

variable (W : Type*) [Fintype W] [DecidableEq W] (F : Type*) [Fintype F] [DecidableEq F]

/-- The fiber partition on `W × F`: states are equivalent iff they share the base point. -/
def fiberPartition : Partition (W × F) where
  rel := ⟨fun p q => p.1 = q.1, ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩⟩
  decRel := fun p q => inferInstanceAs (Decidable (p.1 = q.1))

/-- The uniform lift of a coarse generator: spread each coarse rate evenly over the fiber. -/
def uniformLift (M : Matrix W W ℝ) : Matrix (W × F) (W × F) ℝ :=
  fun p q => M p.1 q.1 / (Fintype.card F : ℝ)

/-- Block membership in the fiber partition is base-point equality. -/
lemma fiberPartition_quot_map_eq_iff (p : W × F) (B : (fiberPartition W F).Quot) :
    (fiberPartition W F).quot_map p = B ↔ p.1 = (Quotient.out B).1 := by
  constructor
  · intro h
    have hmk : Quotient.mk (fiberPartition W F).rel p
        = Quotient.mk (fiberPartition W F).rel (Quotient.out B) := by
      rw [Quotient.out_eq]
      exact h
    exact Quotient.eq'.mp hmk
  · intro h
    have hrel : (fiberPartition W F).rel.r p (Quotient.out B) := h
    show Quotient.mk (fiberPartition W F).rel p = B
    rw [← Quotient.out_eq B]
    exact Quotient.sound hrel

variable [Nonempty F]

/-- Block row sums of the uniform lift recover the coarse generator entries. -/
lemma uniformLift_row_sum_block (M : Matrix W W ℝ) (p : W × F)
    (B : (fiberPartition W F).Quot) :
    row_sum_block (uniformLift W F M) (fiberPartition W F) p B
      = M p.1 (Quotient.out B).1 := by
  have hc : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold row_sum_block uniformLift
  rw [Fintype.sum_prod_type]
  simp_rw [fiberPartition_quot_map_eq_iff W F]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ ((Quotient.out B).1)
      (fun w => (Fintype.card F : ℝ) * (M p.1 w / (Fintype.card F : ℝ)))]
  simp only [Finset.mem_univ, if_true]
  field_simp

/-- **B3a**: the uniform lift is strongly lumpable w.r.t. the fiber partition. -/
theorem uniformLift_stronglyLumpable (M : Matrix W W ℝ) :
    IsStronglyLumpable (uniformLift W F M) (fiberPartition W F) := by
  intro p q hpq B
  show row_sum_block (uniformLift W F M) (fiberPartition W F) p B
      = row_sum_block (uniformLift W F M) (fiberPartition W F) q B
  rw [uniformLift_row_sum_block W F M p B, uniformLift_row_sum_block W F M q B]
  have hbase : p.1 = q.1 := hpq
  rw [hbase]

/-- **B3b (realization)**: the quotient of the uniform lift IS the coarse generator —
    every finite Markov generator embeds as the strongly-lumpable shadow of a model with
    `|F|`-fold hidden codimension. Discrete flexibility h-principle. -/
theorem uniformLift_quotient_realizes (M : Matrix W W ℝ) (w w' : W) (f f' : F) :
    QuotientGeneratorSimple (uniformLift W F M) (fiberPartition W F)
      ((fiberPartition W F).quot_map (w, f)) ((fiberPartition W F).quot_map (w', f'))
      = M w w' := by
  rw [quot_gen_eq_row_sum _ _ (uniformLift_stronglyLumpable W F M) (w, f),
      uniformLift_row_sum_block W F M (w, f)]
  have hout : (Quotient.out ((fiberPartition W F).quot_map (w', f'))).1 = w' :=
    ((fiberPartition_quot_map_eq_iff W F (w', f')
      ((fiberPartition W F).quot_map (w', f'))).mp rfl).symm
  rw [hout]

/-- The uniform lift of a conservative generator is conservative. -/
theorem uniformLift_row_sum_zero (M : Matrix W W ℝ) (hM : ∀ w, ∑ w', M w w' = 0)
    (p : W × F) : ∑ q, uniformLift W F M p q = 0 := by
  have hc : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Fintype.sum_prod_type]
  simp only [uniformLift, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hterm : ∀ w', (Fintype.card F : ℝ) * (M p.1 w' / (Fintype.card F : ℝ)) = M p.1 w' := by
    intro w'
    field_simp
  simp_rw [hterm]
  exact hM p.1

/-- Lifting a stationary measure uniformly over fibers preserves stationarity. -/
theorem uniformLift_stationary (M : Matrix W W ℝ) (piW : W → ℝ)
    (hstat : IsStationary M piW) :
    IsStationary (uniformLift W F M) (fun r => piW r.1 / (Fintype.card F : ℝ)) := by
  intro q
  have hc : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Fintype.sum_prod_type]
  simp only [uniformLift, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hterm : ∀ w, (Fintype.card F : ℝ) *
      (piW w / (Fintype.card F : ℝ) * (M w q.1 / (Fintype.card F : ℝ)))
      = piW w * M w q.1 / (Fintype.card F : ℝ) := by
    intro w
    field_simp
  simp_rw [hterm, ← Finset.sum_div]
  rw [hstat q.1, zero_div]

/-- **B3c (current refinement scaling)**: the lifted current is the coarse current
    scaled by `1/|F|²` — lifting adds hidden room but creates no new vorticity, the
    quantitative content of "flexibility without anomaly". -/
theorem uniformLift_current_scales (M : Matrix W W ℝ) (piW : W → ℝ) (p q : W × F) :
    ProbabilityCurrent (uniformLift W F M) (fun r => piW r.1 / (Fintype.card F : ℝ)) p q
      = ProbabilityCurrent M piW p.1 q.1 / (Fintype.card F : ℝ) ^ 2 := by
  have hc : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [ProbabilityCurrent, uniformLift]
  field_simp

end Flexibility

/-! ## §6. The viscous horizon (B5)

[PNAS] pp. 8–9: the damped Beltrami solution `u(·,t) = M X₀ e^{-νt}` reparametrizes the
Turing-complete flow with a strictly finite total simulated-time budget `τ∞ = M/ν`. The
kernel content is the integral identity below (here for unit energy `M = 1`); coupling
with the SGC validity horizon `T* ~ 1/ε` (`trajectory_closure_bound`, Approximate.lean)
gives the combined budget `1/(νε)`. -/

section ViscousHorizon

open MeasureTheory Set

/-- **B5 (viscous time budget)**: the total reparametrized computation time of a
    `ν`-damped flow is finite: `∫₀^∞ e^{-νt} dt = 1/ν`. -/
theorem viscous_time_budget {ν : ℝ} (hν : 0 < ν) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(ν * t))) = 1 / ν := by
  have h := MeasureTheory.integral_comp_mul_left_Ioi (fun x => Real.exp (-x)) 0 hν
  simp only [mul_zero] at h
  rw [h, integral_exp_neg_Ioi, neg_zero, Real.exp_zero, smul_eq_mul, mul_one, one_div]

/-- **B5-coupling (dissipative validity budget)**: physical time budget `1/ν` times the
    coarse-model validity rate `1/ε` gives the combined budget `1/(νε)` — finite for any
    positive dissipation and positive defect. Infinite-horizon faithful computation
    requires `ν = 0` (no leak) or `ε = 0` (sealed crystal). -/
theorem damped_validity_budget {ν ε : ℝ} (hν : 0 < ν) (_hε : 0 < ε) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(ν * t))) * (1 / ε) = 1 / (ν * ε) := by
  rw [viscous_time_budget hν, div_mul_div_comm, one_mul]

end ViscousHorizon

end SGC.Bridge.DiscreteFluidDynamics
