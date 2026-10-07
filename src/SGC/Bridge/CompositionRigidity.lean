/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Composition is rigid; invariance is not

Three properties of a learned representation of a group operation (here `(a, b) ↦ a + b` on `ZMod p`)
must be kept apart:

* **invariance** — the representation is constant on the *observed* pairs with the same answer
  (block-constant on the label partition restricted to the data);
* **sufficiency** — the answer can be read off the representation;
* **composition** — the representation *respects the operation*: there is a map `z : ZMod p → G`
  into a group with `z (a + b) = z a * z b`.

The two theorems below are the formal reason composition generalizes and invariance alone does not.

`step_determines_hom`: if `z` respects the operation on the **generator only** — the `p` relations
`z (a + 1) = z a * z 1` — then `z` is a homomorphism on all `p²` pairs. The law is determined by its
behaviour on a generating set (rigidity ratio `p² / p = p`).

`invariance_on_observed_not_determined`: a representation that is block-constant on any proper
subset of the pairs can be changed on an unobserved pair without disturbing any observed relation.
Invariance on the data does not determine the unobserved answers.

Lumpability reading: composition says the translation action `T_t : (a, b) ↦ (a + t, b)` is
*lumpable* with respect to the partition induced by the representation (it maps blocks to blocks by a
fixed rule); invariance says the representation is block-constant on the orbits of the gauge action
`(a, b) ↦ (a + t, b − t)`. The first is a statement about the dynamics, the second about one partition
on one data set — the dynamics term and the task term of `MacroSelection.three_mode_bound`.
-/

namespace SGC.Bridge.CompositionRigidity

variable {G : Type*} [Group G]

/-- `g ^ m = g ^ (m % p)` whenever `g ^ p = 1`. -/
lemma pow_mod_of_pow_eq_one (g : G) {p : ℕ} (hg : g ^ p = 1) (m : ℕ) : g ^ m = g ^ (m % p) := by
  conv_lhs => rw [← Nat.mod_add_div m p]
  rw [pow_add, pow_mul, hg, one_pow, mul_one]

variable {p : ℕ} [NeZero p]

/-- Respecting the generator step on every element forces `z a = z 1 ^ a.val`. -/
theorem val_pow_of_step (z : ZMod p → G) (h0 : z 0 = 1) (hstep : ∀ a, z (a + 1) = z a * z 1) :
    ∀ a : ZMod p, z a = z 1 ^ a.val := by
  have hnat : ∀ n : ℕ, z (n : ZMod p) = z 1 ^ n := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih => rw [Nat.cast_succ, hstep, ih, pow_succ]
  intro a
  simpa [ZMod.natCast_zmod_val] using hnat a.val

/-- The generator has order dividing `p`: `z 1 ^ p = 1`. -/
theorem gen_pow_card (z : ZMod p → G) (h0 : z 0 = 1) (hstep : ∀ a, z (a + 1) = z a * z 1) :
    z 1 ^ p = 1 := by
  have hnat : ∀ n : ℕ, z (n : ZMod p) = z 1 ^ n := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih => rw [Nat.cast_succ, hstep, ih, pow_succ]
  have := hnat p
  rwa [ZMod.natCast_self, h0, eq_comm] at this

/-- **Rigidity of composition.** The `p` generator relations imply all `p²` composition relations:
`z (a + b) = z a * z b` for every pair. -/
theorem step_determines_hom (z : ZMod p → G) (h0 : z 0 = 1)
    (hstep : ∀ a, z (a + 1) = z a * z 1) :
    ∀ a b : ZMod p, z (a + b) = z a * z b := by
  intro a b
  have hg := gen_pow_card z h0 hstep
  rw [val_pow_of_step z h0 hstep, val_pow_of_step z h0 hstep a, val_pow_of_step z h0 hstep b,
    ← pow_add, ZMod.val_add, ← pow_mod_of_pow_eq_one (z 1) hg]

/-- A homomorphism from `ZMod p` is determined by the image of the generator: two representations
that agree on `1` (and respect the step) agree everywhere. -/
theorem hom_ext_of_gen (z w : ZMod p → G) (hz0 : z 0 = 1) (hw0 : w 0 = 1)
    (hz : ∀ a, z (a + 1) = z a * z 1) (hw : ∀ a, w (a + 1) = w a * w 1) (h1 : z 1 = w 1) :
    z = w := by
  funext a
  rw [val_pow_of_step z hz0 hz, val_pow_of_step w hw0 hw, h1]

/-- **Invariance on the observed pairs does not determine the unobserved ones.** For any
representation `h` of pairs and any pair `u` outside the observed set `D`, there is a representation
`h'` agreeing with `h` on every observed pair (hence block-constant on `D` whenever `h` is) that
differs from `h` at `u`. Requires the codomain to have two distinct values. -/
theorem invariance_on_observed_not_determined {α β : Type*} [DecidableEq α]
    (h : α → β) (D : Set α) (u : α) (hu : u ∉ D) (v : β) (hv : v ≠ h u) :
    ∃ h' : α → β, (∀ x ∈ D, h' x = h x) ∧ h' u ≠ h u := by
  refine ⟨fun x => if x = u then v else h x, ?_, ?_⟩
  · intro x hx
    have hxu : x ≠ u := fun hxu => hu (hxu ▸ hx)
    simp [hxu]
  · simp [hv]


/-!
## The bridge: equivariance is lumpability of the fibers

"Composition is lumpability" made exact. For a representation `z : X → V` and a transformation
`T : X → X`, the fibers of `z` (its induced partition) are *lumpable* for `T` — `T` maps each fiber
into a single fiber — if and only if `T` descends to the image: there is a map `R : V → V` with
`z (T x) = R (z x)` for all `x` (equivariance). The theorem is stated for arbitrary `T`, so it covers
every element of a group action separately; for a group action the family `R_t` is the quotient action.
-/

section Bridge

variable {X V : Type*}

/-- Fibers of `z` are lumpable for `T`: equal representations have equal representations after `T`. -/
def FibersLumpable (z : X → V) (T : X → X) : Prop :=
  ∀ x y, z x = z y → z (T x) = z (T y)

/-- `z` is `T`-equivariant: `T` descends to a map on the representation space. -/
def Equivariant (z : X → V) (T : X → X) : Prop :=
  ∃ R : V → V, ∀ x, z (T x) = R (z x)

/-- **Equivariance ⇔ lumpability of the fibers.** -/
theorem equivariant_iff_fibersLumpable [Nonempty V] (z : X → V) (T : X → X) :
    Equivariant z T ↔ FibersLumpable z T := by
  constructor
  · rintro ⟨R, hR⟩ x y hxy
    rw [hR, hR, hxy]
  · intro h
    classical
    refine ⟨fun v => if hv : ∃ x, z x = v then z (T hv.choose) else Classical.arbitrary V, ?_⟩
    intro x
    have hx : ∃ y, z y = z x := ⟨x, rfl⟩
    simp only [dif_pos hx]
    exact (h _ _ hx.choose_spec).symm

/-- Composition for a group action: if every generator step is equivariant, so is every iterate
(`T^[n]`), with the descended maps composing. -/
theorem equivariant_iterate (z : X → V) (T : X → X) (h : Equivariant z T) (n : ℕ) :
    Equivariant z (T^[n]) := by
  obtain ⟨R, hR⟩ := h
  refine ⟨R^[n], ?_⟩
  intro x
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hR]

end Bridge


/-!
## The exact ceiling: invariance plus one witness per orbit is correctness

For modular addition the task-preserving action is the gauge shift `T_t (a, b) = (a + t, b − t)`,
whose orbits are exactly the label classes `{(a, b) | a + b = c}`. If a predictor `f` is invariant
under every `T_t` and the observed data contain, for every sum `c`, one pair with that sum on which
`f` is correct, then `f` is correct on every pair. This is the second review's direct argument; for
the invariant case it is sharper than composition rigidity and it is the benchmark for the
label-free contradiction sensor: a violation of invariance between two inputs with the same sum is a
contradiction (both predictions cannot be correct), and invariance everywhere plus one witness per
class is sufficiency everywhere.
-/

section Ceiling

variable {p : ℕ} [NeZero p]

/-- The gauge shift on pairs. -/
def gaugeShift (t : ZMod p) (x : ZMod p × ZMod p) : ZMod p × ZMod p := (x.1 + t, x.2 - t)

/-- Gauge shifts preserve the sum. -/
theorem gaugeShift_sum (t : ZMod p) (x : ZMod p × ZMod p) :
    (gaugeShift t x).1 + (gaugeShift t x).2 = x.1 + x.2 := by
  simp only [gaugeShift]
  ring

/-- Any two pairs with the same sum are related by a gauge shift. -/
theorem exists_gaugeShift_of_sum_eq (x w : ZMod p × ZMod p) (h : w.1 + w.2 = x.1 + x.2) :
    gaugeShift (x.1 - w.1) w = x := by
  ext
  · simp [gaugeShift]
  · simp only [gaugeShift]
    linear_combination h

/-- **Exact ceiling.** A gauge-invariant predictor that is correct on one observed pair per sum class
is correct everywhere. -/
theorem correct_everywhere_of_invariant (f : ZMod p × ZMod p → ZMod p) (D : Set (ZMod p × ZMod p))
    (hinv : ∀ t x, f (gaugeShift t x) = f x)
    (hwit : ∀ c : ZMod p, ∃ w ∈ D, w.1 + w.2 = c ∧ f w = c) :
    ∀ x, f x = x.1 + x.2 := by
  intro x
  obtain ⟨w, -, hsum, hfw⟩ := hwit (x.1 + x.2)
  have hx : gaugeShift (x.1 - w.1) w = x := exists_gaugeShift_of_sum_eq x w hsum
  calc f x = f (gaugeShift (x.1 - w.1) w) := by rw [hx]
    _ = f w := hinv _ _
    _ = x.1 + x.2 := hfw

/-- **Contradiction.** If the label is gauge-invariant, two inputs on one orbit with different
predictions cannot both be correct: at least one prediction is wrong. -/
theorem contradiction_of_orbit_disagreement (f : ZMod p × ZMod p → ZMod p) (t : ZMod p)
    (x : ZMod p × ZMod p) (hne : f (gaugeShift t x) ≠ f x) :
    f x ≠ x.1 + x.2 ∨ f (gaugeShift t x) ≠ (gaugeShift t x).1 + (gaugeShift t x).2 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  exact hne (by rw [h2, gaugeShift_sum, h1])

end Ceiling

end SGC.Bridge.CompositionRigidity
