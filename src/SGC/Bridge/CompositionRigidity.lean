/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fintype.Card

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

end SGC.Bridge.CompositionRigidity
