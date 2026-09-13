/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Bridge.DiscreteFluidDynamics

/-!
# Deterministic kernels: detailed balance is involution; directed dynamics carries current

Two small theorems that pin down, in SGC's own vocabulary, what "a computation cannot be
a palindrome" does and does not mean.

## Setting

A deterministic dynamics `f : Equiv.Perm V` on a finite state space, viewed as the
rate-one jump generator `detGenerator f = T_f - I` (`T_f x y = [f x = y]`). A strictly
positive stationary measure `π` (for a permutation, stationarity is `π ∘ f = π`).

## Results

* `detailedBalance_iff_involutive` - `DetailedBalance (detGenerator f) π ↔ ∀ x, f (f x) = x`.
  A deterministic dynamics is reversible in the detailed-balance sense (relative to a
  full-support invariant measure) **iff it is an involution**: every orbit has length
  one or two. "Palindrome = involution = no arrow."
* `directed_dynamics_has_current_cycle` - a deterministic dynamics with some orbit of
  length `> 2` is a non-equilibrium steady state: it carries a directed cycle of strictly
  positive probability current (via `ness_has_current_cycle`).
* `bare_two_level_compatible` - the *bare* two-level "program preservation plus energy
  transfer" requirement is trivially satisfiable: a factor map onto the program state can
  commute exactly with a step that moves all activity to the fine level. So any
  obstruction of the kind "a scale-cascading fluid computer cannot both copy its program
  and hand down its energy" must come from **physical constraints not present in the bare
  abstract toy** (locality, divergence-free structure, energy identity, bandwidth, finite
  precision, noise). This lemma exists to stop that slogan from being stated without them.

## What is and is not claimed

PROVEN: the three statements above, on finite `V`.

NOT CLAIMED: that computation requires irreversibility. Reversible universal Turing
machines exist (Bennett 1973); Moore's generalized shifts are homeomorphisms; the
Cardona-Miranda-Peralta-Salas constructions are volume-preserving. What the first theorem
says is narrower and exact: *directed* deterministic dynamics (an orbit of length `> 2`)
is never a detailed-balance equilibrium and always carries a current cycle. Directed
drift is a statement about probability current, not about dissipation, logical
irreversibility, or entropy production. Nothing here is about fluids.

Attribution: the sharpened statements and the warning label were the product of a
multi-agent review of a handwritten sketch (2026-09-13); the formalization is ours.
-/

noncomputable section

namespace SGC.Bridge.DeterministicKernels

open Finset BigOperators
open SGC.Thermodynamics SGC.Bridge.DiscreteFluidDynamics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The rate-one jump generator of a deterministic map `f`: `L x y = [f x = y] - [x = y]`. -/
def detGenerator (f : V → V) : Matrix V V ℝ :=
  fun x y => (if f x = y then (1 : ℝ) else 0) - (if x = y then (1 : ℝ) else 0)

lemma detGenerator_rowsum (f : V → V) (x : V) : ∑ y, detGenerator f x y = 0 := by
  simp [detGenerator, Finset.sum_sub_distrib, Finset.sum_ite_eq]

/-- For a permutation, stationarity of a measure is invariance `π ∘ f = π`. -/
lemma stationary_iff_invariant (f : Equiv.Perm V) (π : V → ℝ) :
    IsStationary (detGenerator f) π ↔ ∀ x, π (f x) = π x := by
  have key : ∀ y, ∑ x, π x * detGenerator f x y = π (f.symm y) - π y := by
    intro y
    simp only [detGenerator, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
    have h1 : (∑ x, if f x = y then π x else 0) = π (f.symm y) := by
      rw [Finset.sum_eq_single (f.symm y)]
      · simp
      · intro b _ hb
        have : f b ≠ y := fun h => hb (by rw [← h]; simp)
        simp [this]
      · simp
    have h2 : (∑ x, if x = y then π x else 0) = π y := by simp
    rw [h1, h2]
  constructor
  · intro hstat x
    have := hstat (f x)
    rw [key] at this
    simp at this
    linarith
  · intro hinv y
    rw [key]
    have := hinv (f.symm y)
    simp at this
    linarith

/-- **Detailed balance is involution.** For a deterministic dynamics with a strictly
positive invariant measure, detailed balance holds iff `f ∘ f = id`. -/
theorem detailedBalance_iff_involutive (f : Equiv.Perm V) (π : V → ℝ)
    (hπ : ∀ v, 0 < π v) (hinv : ∀ x, π (f x) = π x) :
    DetailedBalance (detGenerator f) π ↔ ∀ x, f (f x) = x := by
  constructor
  · intro hdb x
    by_cases hfx : f x = x
    · rw [hfx, hfx]
    · have h := hdb x (f x)
      simp only [detGenerator] at h
      have hne : x ≠ f x := fun h' => hfx h'.symm
      rw [hinv x] at h
      simp [hne, hfx] at h
      -- h : π x = π x * (if f (f x) = x then 1 else 0)  (after simp normal form)
      by_contra hcon
      simp [hcon] at h
      exact (hπ x).ne' h
  · intro hinvol x y
    simp only [DetailedBalance, detGenerator]
    by_cases hxy : x = y
    · subst hxy; ring
    · have hyx : y ≠ x := fun h => hxy h.symm
      have hiff : f x = y ↔ f y = x := by
        constructor
        · intro h; rw [← h, hinvol]
        · intro h; rw [← h, hinvol]
      by_cases hfx : f x = y
      · have hfy : f y = x := hiff.mp hfx
        have hπxy : π y = π x := by rw [← hfx, hinv]
        simp [hfx, hfy, hxy, hyx, hπxy]
      · have hfy : f y ≠ x := fun h => hfx (hiff.mpr h)
        simp [hfx, hfy, hxy, hyx]

/-- **Directed dynamics is a NESS.** A deterministic dynamics with a positive invariant
measure and an orbit of length `> 2` carries a directed cycle of strictly positive
probability current. -/
theorem directed_dynamics_has_current_cycle (f : Equiv.Perm V) (π : V → ℝ)
    (hπ : ∀ v, 0 < π v) (hinv : ∀ x, π (f x) = π x)
    (hdir : ∃ x, f (f x) ≠ x) :
    ∃ (len : ℕ) (c : ℕ → V), 0 < len ∧ c 0 = c len ∧
      ∀ m < len, 0 < ProbabilityCurrent (detGenerator f) π (c m) (c (m + 1)) := by
  apply ness_has_current_cycle (detGenerator f) π (detGenerator_rowsum f)
    ((stationary_iff_invariant f π).mpr hinv)
  intro hdb
  obtain ⟨x, hx⟩ := hdir
  exact hx ((detailedBalance_iff_involutive f π hπ hinv).mp hdb x)

/-! ## The bare two-level toy is compatible -/

/-- A two-level state: a program state and a level flag (`false` = coarse, `true` = fine). -/
abbrev TwoLevel (C : Type*) := C × Bool

/-- One step: advance the program by `S` and move all activity to the fine level. -/
def handoff {C : Type*} (S : C → C) (x : TwoLevel C) : TwoLevel C := (S x.1, true)

/-- Activity (energy) observable: `1` on the fine level, `0` on the coarse level. -/
def activity {C : Type*} (x : TwoLevel C) : ℝ := if x.2 then 1 else 0

/-- **The bare toy is compatible.** The program projection `Prod.fst` is an exact factor
map for `handoff S` (exact information preservation), and every step starting on the
coarse level transfers all activity to the fine level. Hence "exact program preservation
plus definite energy transfer" is jointly satisfiable in the abstract; an obstruction, if
any, must come from additional physical constraints. -/
theorem bare_two_level_compatible {C : Type*} (S : C → C) :
    (∀ x : TwoLevel C, (handoff S x).1 = S x.1) ∧
    (∀ c : C, activity (handoff S (c, false)) = activity (c, false) + 1) := by
  refine ⟨fun x => rfl, fun c => ?_⟩
  simp [handoff, activity]

end SGC.Bridge.DeterministicKernels

end
