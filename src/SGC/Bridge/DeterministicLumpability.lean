/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Bridge.BlockRenormalization

/-!
# Exact lumpability of a deterministic dynamics is a factor map

Answers the external reviewer's question Q2 (2026-09-12): *what is the correct SGC object
for a deterministic generalized shift, given that the Bernoulli tower does not formalize
Moore's machines?* The answer is a theorem, not a relabelling:

**for a deterministic dynamics `f : V → V`, SGC's strong lumpability of the kernel
`T_f = [f x = y]` with respect to a partition `P` holds iff `f` descends to the quotient**
(`detKernel_stronglyLumpable_iff`): `x ~ y → f x ~ f y`. That is exactly the
semiconjugacy / factor-map condition `π ∘ f = f̄ ∘ π` of symbolic dynamics - the notion
Moore (1991) and Cardona-Miranda-Peralta-Salas-Presas (2021) actually use to encode a
machine into a flow (`π ∘ Φ = σ ∘ π` on the Cantor transversal).

Consequences, all kernel-checked:

* `closureCommutator_detKernel_eq_zero_iff` / `defectSq_detKernel_eq_zero_iff` -
  the measure-reentry defect of a deterministic dynamics vanishes iff `f` descends;
  the SGC `ε = 0` pole *is* the existence of a factor map.
* `coarseGenerator_detKernel_eq` - under lumpability, the canonical `π`-weighted coarse
  kernel is the deterministic kernel of the induced quotient map `quotMap f P`:
  **the renormalized machine is again a machine**, and the reference measure `π` is
  gauge (drops out), for every strictly positive `π`.
* `eternal_closure_detKernel` - the quotient dynamics tracks the projected fine dynamics
  exactly at every time (`T_f^n K = K T_{f̄}^n`), i.e. infinite validity horizon.
* `detKernel_pow_stronglyLumpable` - blocking preserves lumpability: if `f` descends, so
  does every `f^[b]`, with quotient `(quotMap f P)^[b]`. The temporal tower of
  `BlockRenormalization` and the spatial quotient commute.

## What this settles and what it does not

It settles the vocabulary: "exactly lumpable" = "factor map" for deterministic systems,
so any deterministic generalized shift that is a factor of a machine (Moore's
construction) *is* an exactly lumpable SGC quotient, and conversely. It does **not** by
itself produce a Turing simulation - that requires exhibiting `f`, `P`, and the
simulation relation, which is Moore's theorem, not ours. Nor does it say anything about
robustness under perturbation (CMPP Remark 5.3; Bournez-Graça-Hainry), about fluids, or
about the Bernoulli tower, which remains a separate (i.i.d.-input) object.
-/

noncomputable section

namespace SGC.Bridge.DeterministicLumpability

open Finset Matrix
open SGC SGC.Thermodynamics SGC.Renormalization.MeasureReentry
open SGC.Bridge.BlockRenormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `f` descends to the quotient of `P`: equivalent points have equivalent images. -/
def Descends (f : V → V) (P : Partition V) : Prop :=
  ∀ x y, P.rel.r x y → P.rel.r (f x) (f y)

lemma row_sum_block_detKernel (f : V → V) (P : Partition V) (x : V) (B : P.Quot) :
    row_sum_block (detKernel f) P x B = if P.quot_map (f x) = B then 1 else 0 := by
  unfold row_sum_block detKernel
  rw [Finset.sum_eq_single (f x)]
  · simp
  · intro z _ hz
    simp [Ne.symm hz]
  · simp

omit [Fintype V] in
lemma quot_map_eq_iff (P : Partition V) (x y : V) :
    P.quot_map x = P.quot_map y ↔ P.rel.r x y :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- **Exact lumpability of a deterministic dynamics is a factor map.** -/
theorem detKernel_stronglyLumpable_iff (f : V → V) (P : Partition V) :
    IsStronglyLumpable (detKernel f) P ↔ Descends f P := by
  constructor
  · intro h x y hxy
    have hb : row_sum_block (detKernel f) P x (P.quot_map (f x)) =
        row_sum_block (detKernel f) P y (P.quot_map (f x)) := h x y hxy (P.quot_map (f x))
    rw [row_sum_block_detKernel, row_sum_block_detKernel] at hb
    simp only [if_true] at hb
    by_contra hcon
    have hne : P.quot_map (f y) ≠ P.quot_map (f x) := fun h' =>
      hcon ((quot_map_eq_iff P _ _).mp h'.symm)
    rw [if_neg hne] at hb
    exact one_ne_zero hb
  · intro h x y hxy B
    change row_sum_block (detKernel f) P x B = row_sum_block (detKernel f) P y B
    rw [row_sum_block_detKernel, row_sum_block_detKernel,
      (quot_map_eq_iff P _ _).mpr (h x y hxy)]

/-- The measure-reentry closure commutator of a deterministic dynamics vanishes iff `f`
descends - for every strictly positive reference measure. -/
theorem closureCommutator_detKernel_eq_zero_iff (f : V → V) (P : Partition V)
    {pi : V → ℝ} (hpi : ∀ x, 0 < pi x) :
    closureCommutator (detKernel f) P pi = 0 ↔ Descends f P := by
  rw [closureCommutator_eq_zero_iff_stronglyLumpable _ P hpi, detKernel_stronglyLumpable_iff]

/-- The measure-reentry defect `𝔇_π²` of a deterministic dynamics vanishes iff `f` descends. -/
theorem defectSq_detKernel_eq_zero_iff (f : V → V) (P : Partition V)
    {pi : V → ℝ} (hpi : ∀ x, 0 < pi x) :
    defectSq (detKernel f) P pi = 0 ↔ Descends f P := by
  rw [defectSq_eq_zero_iff_stronglyLumpable _ P hpi, detKernel_stronglyLumpable_iff]

/-- The induced map on the quotient, when `f` descends. -/
def quotMap (f : V → V) (P : Partition V) (h : Descends f P) : P.Quot → P.Quot :=
  Quotient.lift (fun x => P.quot_map (f x)) (fun x y hxy => Quotient.sound (h x y hxy))

omit [Fintype V] in
@[simp] lemma quotMap_mk (f : V → V) (P : Partition V) (h : Descends f P) (x : V) :
    quotMap f P h (P.quot_map x) = P.quot_map (f x) := rfl

/-- **The renormalized machine is a machine.** Under lumpability the canonical
`π`-weighted coarse kernel is the deterministic kernel of the quotient map; `π` is gauge. -/
theorem coarseGenerator_detKernel_eq (f : V → V) (P : Partition V) (h : Descends f P)
    {pi : V → ℝ} (hpi : ∀ x, 0 < pi x) :
    CoarseGenerator (detKernel f) P pi = detKernel (quotMap f P h) := by
  ext A B
  rw [coarseGenerator_eq_conditional_exit_average _ P hpi]
  have hpos : 0 < pi_bar P pi A := pi_bar_pos P hpi A
  have hrow : ∀ x, P.quot_map x = A →
      row_sum_block (detKernel f) P x B = if quotMap f P h A = B then 1 else 0 := by
    intro x hx
    rw [row_sum_block_detKernel, ← hx, quotMap_mk]
  have hsum : (∑ x : V, if P.quot_map x = A
      then pi x * row_sum_block (detKernel f) P x B else 0)
      = (if quotMap f P h A = B then 1 else 0) * pi_bar P pi A := by
    unfold pi_bar
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : P.quot_map x = A
    · rw [if_pos hx, if_pos hx, hrow x hx]; ring
    · simp [hx]
  rw [hsum, detKernel]
  field_simp

/-- **Infinite validity horizon**: the quotient machine tracks the projected fine machine
exactly at every time. -/
theorem eternal_closure_detKernel (f : V → V) (P : Partition V) (h : Descends f P)
    {pi : V → ℝ} (hpi : ∀ x, 0 < pi x) (n : ℕ) :
    (detKernel f) ^ n * lift_matrix P = lift_matrix P * (detKernel (quotMap f P h)) ^ n := by
  rw [← coarseGenerator_detKernel_eq f P h hpi]
  exact SGC.Renormalization.KernelHorizon.eternal_closure_of_zero_commutator _ P pi
    ((closureCommutator_detKernel_eq_zero_iff f P hpi).mpr h) n

omit [Fintype V] in
/-- Descent is preserved by iteration. -/
lemma Descends.iterate {f : V → V} {P : Partition V} (h : Descends f P) (b : ℕ) :
    Descends (f^[b]) P := by
  induction b with
  | zero => intro x y hxy; simpa using hxy
  | succ b ih =>
    intro x y hxy
    rw [Function.iterate_succ', Function.comp_apply, Function.comp_apply]
    exact h _ _ (ih x y hxy)

omit [Fintype V] in
/-- **Blocking preserves lumpability**, and the quotient of the block map is the block of
the quotient map: the temporal tower and the spatial quotient commute. -/
theorem quotMap_iterate (f : V → V) (P : Partition V) (h : Descends f P) (b : ℕ) :
    quotMap (f^[b]) P (h.iterate b) = (quotMap f P h)^[b] := by
  funext A
  obtain ⟨x, rfl⟩ := Quotient.exists_rep A
  change quotMap (f^[b]) P (h.iterate b) (P.quot_map x) = (quotMap f P h)^[b] (P.quot_map x)
  rw [quotMap_mk]
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [Function.iterate_succ', Function.iterate_succ', Function.comp_apply,
      Function.comp_apply, ← ih, quotMap_mk]

theorem detKernel_pow_stronglyLumpable (f : V → V) (P : Partition V) (h : Descends f P)
    (b : ℕ) : IsStronglyLumpable ((detKernel f) ^ b) P := by
  rw [detKernel_pow, detKernel_stronglyLumpable_iff]
  exact h.iterate b

/-! ## Regression: coarse-graining a machine by its control state

Two two-state, two-symbol machines on the finite configuration space `Bool × Bool`
(control state, symbol under the head). The partition `byState` identifies configurations
with the same control state.

* `oblivious` flips the control state and ignores the symbol. Coarse-graining by state is
  **exact**: the quotient is the one-state-flip machine and the defect is zero.
* `reader` moves to state `true` iff it reads `1`. Coarse-graining by state is **inexact**:
  the closure commutator is nonzero and the measure-reentry defect is positive for every
  positive `π` - the SGC signature of a computation that *reads its tape*. -/

namespace Regression

/-- Configurations: `(control state, symbol under the head)`. -/
abbrev Cfg := Bool × Bool

/-- Partition by control state. -/
def byState : Partition Cfg where
  rel := ⟨fun x y => x.1 = y.1, ⟨fun _ => rfl, fun h => h.symm, fun h h' => h.trans h'⟩⟩
  decRel := fun x y => inferInstanceAs (Decidable (x.1 = y.1))

lemma byState_rel (x y : Cfg) : byState.rel.r x y ↔ x.1 = y.1 := Iff.rfl

/-- A machine that flips its state and ignores the symbol. -/
def oblivious (c : Cfg) : Cfg := (!c.1, c.2)

/-- A machine whose next state is the symbol it reads. -/
def reader (c : Cfg) : Cfg := (c.2, c.2)

theorem oblivious_descends : Descends oblivious byState := by
  intro x y h
  simp only [byState_rel, oblivious] at *
  rw [h]

theorem oblivious_stronglyLumpable : IsStronglyLumpable (detKernel oblivious) byState :=
  (detKernel_stronglyLumpable_iff _ _).mpr oblivious_descends

theorem oblivious_defect_zero {pi : Cfg → ℝ} (hpi : ∀ x, 0 < pi x) :
    defectSq (detKernel oblivious) byState pi = 0 :=
  (defectSq_detKernel_eq_zero_iff _ _ hpi).mpr oblivious_descends

theorem reader_not_descends : ¬ Descends reader byState := by
  intro h
  have := h (false, false) (false, true) rfl
  simp [reader] at this

theorem reader_not_stronglyLumpable : ¬ IsStronglyLumpable (detKernel reader) byState :=
  fun h => reader_not_descends ((detKernel_stronglyLumpable_iff _ _).mp h)

theorem reader_commutator_ne_zero {pi : Cfg → ℝ} (hpi : ∀ x, 0 < pi x) :
    closureCommutator (detKernel reader) byState pi ≠ 0 :=
  fun h => reader_not_descends ((closureCommutator_detKernel_eq_zero_iff _ _ hpi).mp h)

/-- **Reading the tape is measured by the defect**: for every positive reference measure
the measure-reentry defect of the `reader` machine, coarse-grained by control state, is
strictly positive. -/
theorem reader_defect_pos {pi : Cfg → ℝ} (hpi : ∀ x, 0 < pi x) :
    0 < defectSq (detKernel reader) byState pi := by
  have hne : defectSq (detKernel reader) byState pi ≠ 0 :=
    fun h => reader_not_descends ((defectSq_detKernel_eq_zero_iff _ _ hpi).mp h)
  exact lt_of_le_of_ne (defectSq_nonneg _ _ fun x => (hpi x).le) hne.symm

end Regression

end SGC.Bridge.DeterministicLumpability

end
