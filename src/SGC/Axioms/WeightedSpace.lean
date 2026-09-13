/-
Copyright (c) 2025 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Team
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Complex.Basic

/-!
# Weighted Inner Product Spaces

This file implements the **Type Synonym Pattern** to define weighted inner product spaces
that integrate cleanly with Mathlib's `InnerProductSpace` hierarchy.

## The Diamond Problem

Mathlib's `PiLp 2 (fun _ : V => ℂ)` comes with a built-in `InnerProductSpace` instance
using the standard (unweighted) inner product. This creates a "diamond" when we try to
define a different (weighted) inner product on the same type `V → ℂ`.

## Solution: Type Synonym

We define `WeightedSpace V` as a type synonym for `V → ℂ`. This fresh type has no
pre-existing `InnerProductSpace` instance, so we can define one with the weighted
inner product:

  ⟨f, g⟩_π = Σ_x π(x) · conj(f(x)) · g(x)

## Main Definitions

* `WeightedSpace V` - Type synonym for `V → ℂ`
* `WeightedSpace.weightedCore` - The `InnerProductSpace.Core` for weighted inner product
-/

noncomputable section

open scoped ComplexConjugate
open Finset BigOperators Complex

namespace SGC.Axioms

/-- `WeightedSpace V` is a type synonym for `V → ℂ`. -/
def WeightedSpace (V : Type*) := V → ℂ

namespace WeightedSpace

variable {V : Type*}

@[inline] def mk (f : V → ℂ) : WeightedSpace V := f
@[inline] def toFun (f : WeightedSpace V) : V → ℂ := f

instance : CoeFun (WeightedSpace V) (fun _ => V → ℂ) where coe := toFun

@[ext] theorem ext {f g : WeightedSpace V} (h : ∀ x, f x = g x) : f = g := funext h

def ones : WeightedSpace V := fun _ => 1

instance : Zero (WeightedSpace V) := ⟨fun _ => 0⟩

variable [Fintype V]

instance : AddCommGroup (WeightedSpace V) := inferInstanceAs (AddCommGroup (V → ℂ))
instance : Module ℂ (WeightedSpace V) := inferInstanceAs (Module ℂ (V → ℂ))

/-! ## Weighted Inner Product -/

def weightedInner (π : V → ℝ) (f g : WeightedSpace V) : ℂ :=
  ∑ x : V, (π x : ℂ) * conj (f x) * g x

theorem weightedInner_conj_symm (π : V → ℝ) (f g : WeightedSpace V) :
    conj (weightedInner π g f) = weightedInner π f g := by
  unfold weightedInner
  rw [map_sum]
  congr 1; ext x
  simp only [map_mul, conj_ofReal, starRingEnd_self_apply]
  ring

theorem weightedInner_re_nonneg (π : V → ℝ) (hπ : ∀ x, 0 < π x) (f : WeightedSpace V) :
    0 ≤ (weightedInner π f f).re := by
  unfold weightedInner
  rw [re_sum]
  apply Finset.sum_nonneg
  intro x _
  have h1 : conj (f x) * f x = (normSq (f x) : ℂ) := by rw [mul_comm, mul_conj]
  have h2 : ((π x : ℂ) * conj (f x) * f x).re = π x * normSq (f x) := by
    rw [mul_assoc, h1]
    simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  rw [h2]
  exact mul_nonneg (le_of_lt (hπ x)) (normSq_nonneg _)

theorem weightedInner_add_left (π : V → ℝ) (f g h : WeightedSpace V) :
    weightedInner π (f + g) h = weightedInner π f h + weightedInner π g h := by
  unfold weightedInner
  rw [← Finset.sum_add_distrib]
  congr 1; ext x
  -- (f + g) x = f x + g x by definition of addition on WeightedSpace
  have hadd : (f + g) x = f x + g x := rfl
  rw [hadd, map_add]
  ring

theorem weightedInner_smul_left (π : V → ℝ) (f g : WeightedSpace V) (c : ℂ) :
    weightedInner π (c • f) g = conj c * weightedInner π f g := by
  unfold weightedInner
  rw [Finset.mul_sum]
  congr 1; ext x
  rw [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem weightedInner_definite (π : V → ℝ) (hπ : ∀ x, 0 < π x) (f : WeightedSpace V) :
    weightedInner π f f = 0 → f = 0 := by
  intro h
  ext x
  have h_re : (weightedInner π f f).re = 0 := by simp only [h, zero_re]
  unfold weightedInner at h_re
  rw [re_sum] at h_re
  have h_term : ∀ y, ((π y : ℂ) * conj (f y) * f y).re = π y * normSq (f y) := by
    intro y
    have h1 : conj (f y) * f y = (normSq (f y) : ℂ) := by rw [mul_comm, mul_conj]
    rw [mul_assoc, h1]
    simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  simp only [h_term] at h_re
  have h_nonneg : ∀ y ∈ Finset.univ, 0 ≤ π y * normSq (f y) := fun y _ =>
    mul_nonneg (le_of_lt (hπ y)) (normSq_nonneg _)
  have h_each := Finset.sum_eq_zero_iff_of_nonneg h_nonneg |>.mp h_re x (Finset.mem_univ x)
  have h_normSq : normSq (f x) = 0 := by
    cases mul_eq_zero.mp h_each with
    | inl hp => exact absurd hp (ne_of_gt (hπ x))
    | inr hn => exact hn
  exact normSq_eq_zero.mp h_normSq

/-- The `InnerProductSpace.Core` structure for the weighted inner product. -/
def weightedCore (π : V → ℝ) (hπ : ∀ x, 0 < π x) : InnerProductSpace.Core ℂ (WeightedSpace V) where
  inner := weightedInner π
  conj_inner_symm := weightedInner_conj_symm π
  re_inner_nonneg := weightedInner_re_nonneg π hπ
  definite := weightedInner_definite π hπ
  add_left := weightedInner_add_left π
  smul_left := weightedInner_smul_left π

/-- The `NormedAddCommGroup` instance induced by the weighted inner product. -/
def toNormedAddCommGroup (π : V → ℝ) (hπ : ∀ x, 0 < π x) : NormedAddCommGroup (WeightedSpace V) :=
  (weightedCore π hπ).toNormedAddCommGroup

/-! ## Non-degeneracy and Extension Lemmas

These replace the axioms in GeometryGeneral.lean for the ℂ case. -/

/-- The weighted inner product is non-degenerate: if ⟨f, g⟩ = 0 for all g, then f = 0. -/
theorem weightedInner_nondegenerate (π : V → ℝ) (hπ : ∀ x, 0 < π x) (f : WeightedSpace V) :
    (∀ g, weightedInner π f g = 0) → f = 0 := by
  intro h
  apply weightedInner_definite π hπ
  exact h f

/-- Two linear maps are equal if they produce equal weighted inner products for all vectors. -/
theorem linearMap_ext_weightedInner (π : V → ℝ) (hπ : ∀ x, 0 < π x)
    (A B : WeightedSpace V →ₗ[ℂ] WeightedSpace V) :
    (∀ u v, weightedInner π (A u) v = weightedInner π (B u) v) → A = B := by
  intro h
  ext u
  -- Show A u = B u by non-degeneracy
  have h_diff : A u - B u = 0 := by
    apply weightedInner_nondegenerate π hπ
    intro v
    have h_sub : weightedInner π (A u - B u) v =
                 weightedInner π (A u) v - weightedInner π (B u) v := by
      have h1 : A u - B u = A u + (-1 : ℂ) • B u := by simp [sub_eq_add_neg]
      rw [h1, weightedInner_add_left, weightedInner_smul_left]
      simp only [map_neg, map_one, neg_mul, one_mul]
      ring
    rw [h_sub, h u v, sub_self]
  simp only [sub_eq_zero] at h_diff
  exact congrFun h_diff _

/-- For any vector f, ⟨f, f⟩ is real (imaginary part is zero). -/
theorem weightedInner_self_real (π : V → ℝ) (f : WeightedSpace V) :
    (weightedInner π f f).im = 0 := by
  have h := weightedInner_conj_symm π f f
  have h2 : weightedInner π f f = conj (weightedInner π f f) := h.symm
  have him : (weightedInner π f f).im = (conj (weightedInner π f f)).im := congrArg Complex.im h2
  simp only [conj_im] at him
  -- him : x = -x, so 2x = 0, so x = 0
  have : 2 * (weightedInner π f f).im = 0 := by linarith
  linarith

/-! ## Convenience Lemmas -/

theorem normSq_eq_sum (π : V → ℝ) (f : WeightedSpace V) :
    (weightedInner π f f).re = ∑ x, π x * normSq (f x) := by
  unfold weightedInner
  rw [re_sum]
  congr 1; ext x
  have h1 : conj (f x) * f x = (normSq (f x) : ℂ) := by rw [mul_comm, mul_conj]
  rw [mul_assoc, h1]
  simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]

theorem ones_normSq_pos [Nonempty V] (π : V → ℝ) (hπ : ∀ x, 0 < π x) :
    0 < (weightedInner π ones ones).re := by
  rw [normSq_eq_sum]
  apply Finset.sum_pos
  · intro x _
    apply mul_pos (hπ x)
    simp only [ones, normSq_one, zero_lt_one]
  · exact Finset.univ_nonempty

omit [Fintype V] in
theorem ones_ne_zero [Nonempty V] : ones ≠ (0 : WeightedSpace V) := by
  intro h
  have : (ones : WeightedSpace V) (Classical.arbitrary V) = 0 := by rw [h]; rfl
  simp only [ones, one_ne_zero] at this

theorem ones_inner_eq_sum (π : V → ℝ) : weightedInner π ones ones = ∑ x, (π x : ℂ) := by
  unfold weightedInner ones
  simp only [map_one, mul_one]

end WeightedSpace

end SGC.Axioms
