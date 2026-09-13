/-
Copyright (c) 2026 Jason Shroyer. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Computability.PostTuringMachine
import SGC.Bridge.CurvatureUndecidability

/-!
# The Halting Compiler: from Turing machines to curvature-encoding generators

`SGC.Bridge.CurvatureUndecidability.cd0_haltW_iff` is a marker-parameterized
gadget lemma: for ANY Boolean marker `H : ℤ → Bool` that fires at most once,
the weighted line `haltW H` satisfies `CD(0, ∞)` iff `H` never fires. By
itself it says nothing about Turing machines, because an arbitrary `H` need
not be computable — this was the correct external criticism of the module
(2026-08-05 review, "required computability bridge", items 1–6).

This module supplies the missing compiler, against **Mathlib's own machine
model** (`Turing.TM0`, `Mathlib.Computability.PostTuringMachine`) and
**Mathlib's own halting predicate** (`(TM0.eval M w).Dom`):

* `multistep f a n` — fuel-indexed simulation of a step function
  `f : σ → Option σ`: `n`-fold `Option.bind`. Total, structurally recursive.
* `haltMarkerNat M w n` — the exact-step marker: `true` iff the compiled run
  of `M` on input `w` is live at fuel `n` and halted at fuel `n + 1`. A total
  `Bool`-valued function; no decidable equality on configurations is needed,
  only `Option.isSome`.
* `haltMarker M w : ℤ → Bool` — the marker shifted onto the bi-infinite path
  (`false` at negative positions). This is the compiler
  `(M, w) ↦ H_{M,w}` requested by the review.
* `haltMarker_at_most_once` — a deterministic machine halts at exactly one
  fuel level: the `hone` hypothesis of `cd0_haltW_iff` is a theorem for
  compiled markers, not an assumption.
* `reaches_iff_multistep` / `evalDom_iff_multistep` — the bridge between the
  fuel-indexed simulation and Mathlib's `PFun.fix`-based evaluation:
  `(Turing.eval f a).Dom ↔ ∃ n, multistep f a n = none`.

## Main results

* `cd0_compiled_iff` :
  `CD0 (haltW (haltMarker M w)) ↔ ¬ (TM0.eval M w).Dom`
* `not_cd0_compiled_iff` :
  `¬ CD0 (haltW (haltMarker M w)) ↔ (TM0.eval M w).Dom`

Reading: deciding the global Bakry-Émery bound `CD(0, ∞)` on the compiled
generator family is *exactly* deciding non-halting for Mathlib's `TM0`
machines. Since the halting problem is undecidable (classical; not re-proved
here), no algorithm decides the global curvature bound on this family — the
honest Π⁰₁-hardness form of the target. Pointwise curvature remains locally
computable throughout: the family varies only a single edge rate.

## Concrete poles

Both poles of the reduction are inhabited by explicit machines:

* `not_cd0_haltNow` — the machine with no transitions halts immediately;
  its compiled chain **violates** `CD(0, ∞)`.
* `cd0_spinRight` — the machine that moves right forever never halts;
  its compiled chain is the flat line and **satisfies** `CD(0, ∞)`.

## Honest scope

* Π⁰₁ *membership* (upper semicomputability of the global infimum) is a
  prose remark, not formalized here.
* The undecidability of `TM0` halting itself is not re-proved; this module
  contributes the reduction, which is the load-bearing step.
-/

namespace SGC.Bridge.HaltingCompiler

open Turing
open SGC.Bridge.CurvatureUndecidability

/-! ## 1. Fuel-indexed simulation of a step function -/

variable {σ : Type*}

/-- `n`-fold iteration of a step function `f : σ → Option σ` from `a`,
threading the possibility of halting through `Option.bind`. `none` means the
run has halted strictly before (or at) fuel `n`. -/
def multistep (f : σ → Option σ) (a : σ) : ℕ → Option σ
  | 0 => some a
  | n + 1 => (multistep f a n).bind f

@[simp] lemma multistep_zero (f : σ → Option σ) (a : σ) :
    multistep f a 0 = some a := rfl

lemma multistep_succ (f : σ → Option σ) (a : σ) (n : ℕ) :
    multistep f a (n + 1) = (multistep f a n).bind f := rfl

/-- Halting is absorbing: once the run is `none` it stays `none`. -/
lemma multistep_none_succ {f : σ → Option σ} {a : σ} {n : ℕ}
    (h : multistep f a n = none) : multistep f a (n + 1) = none := by
  rw [multistep_succ, h]; rfl

/-- Halting is absorbing, monotone form. -/
lemma multistep_none_mono {f : σ → Option σ} {a : σ} {m n : ℕ} (hmn : m ≤ n)
    (h : multistep f a m = none) : multistep f a n = none := by
  induction n, hmn using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact multistep_none_succ ih

/-! ## 2. The bridge to Mathlib's evaluation semantics

`Turing.eval` is defined by `PFun.fix`; `Turing.Reaches` is the reflexive
transitive closure of the step relation. The two lemmas below identify both
with the fuel-indexed simulation, so that Mathlib's halting predicate
`(Turing.eval f a).Dom` becomes `∃ n, multistep f a n = none`. -/

/-- A live simulation state is reachable. -/
lemma reaches_of_multistep {f : σ → Option σ} {a : σ} :
    ∀ {n : ℕ} {b : σ}, multistep f a n = some b → Reaches f a b := by
  intro n
  induction n with
  | zero =>
    intro b h
    simp only [multistep_zero, Option.some.injEq] at h
    subst h
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro b h
    rw [multistep_succ] at h
    cases hc : multistep f a n with
    | none => rw [hc] at h; simp at h
    | some c =>
      rw [hc] at h
      simp only [Option.bind_some] at h
      exact Relation.ReflTransGen.tail (ih hc) (Option.mem_def.mpr h)

/-- Every reachable state is a live simulation state at some fuel. -/
lemma multistep_of_reaches {f : σ → Option σ} {a b : σ} (h : Reaches f a b) :
    ∃ n, multistep f a n = some b := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hbc ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    rw [multistep_succ, hn, Option.bind_some]
    exact Option.mem_def.mp hbc

/-- A halted simulation pinpoints a terminal reachable state. -/
lemma halted_of_multistep_none {f : σ → Option σ} {a : σ} :
    ∀ {n : ℕ}, multistep f a n = none → ∃ b, Reaches f a b ∧ f b = none := by
  intro n
  induction n with
  | zero => intro h; simp at h
  | succ n ih =>
    intro h
    cases hc : multistep f a n with
    | none => exact ih hc
    | some b =>
      rw [multistep_succ, hc] at h
      simp only [Option.bind_some] at h
      exact ⟨b, reaches_of_multistep hc, h⟩

/-- **The evaluation bridge.** Mathlib's `PFun.fix`-based halting predicate
coincides with halting of the fuel-indexed simulation. -/
lemma evalDom_iff_multistep {f : σ → Option σ} {a : σ} :
    (Turing.eval f a).Dom ↔ ∃ n, multistep f a n = none := by
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨hr, hstop⟩ := Turing.mem_eval.mp hb
    obtain ⟨n, hn⟩ := multistep_of_reaches hr
    refine ⟨n + 1, ?_⟩
    rw [multistep_succ, hn, Option.bind_some]
    exact hstop
  · rintro ⟨n, hn⟩
    obtain ⟨b, hr, hstop⟩ := halted_of_multistep_none hn
    exact ⟨b, Turing.mem_eval.mpr ⟨hr, hstop⟩⟩

/-! ## 3. The compiler -/

variable {Γ : Type*} [Inhabited Γ] {Λ : Type*} [Inhabited Λ]

/-- The exact-step halting marker: `true` at fuel `n` iff the run of `M` on
input `w` is live at fuel `n` and halted at fuel `n + 1`. Total and
`Bool`-valued by construction; only `Option.isSome` is inspected, so no
decidable equality on configurations is required. -/
def haltMarkerNat (M : TM0.Machine Γ Λ) (w : List Γ) (n : ℕ) : Bool :=
  (multistep (TM0.step M) (TM0.init w) n).isSome
    && !(multistep (TM0.step M) (TM0.init w) (n + 1)).isSome

/-- **The compiler** `(M, w) ↦ H_{M,w}`: the exact-step marker transported to
the bi-infinite path (`false` at negative positions), in the input format of
`SGC.Bridge.CurvatureUndecidability.haltW`. -/
def haltMarker (M : TM0.Machine Γ Λ) (w : List Γ) : ℤ → Bool :=
  fun i => if 0 ≤ i then haltMarkerNat M w i.toNat else false

/-- A fired marker at fuel `m` silences the marker at all later fuels:
determinism makes the halting step unique. -/
lemma haltMarkerNat_eq_false_of_lt {M : TM0.Machine Γ Λ} {w : List Γ}
    {m n : ℕ} (hmn : m < n) (hm : haltMarkerNat M w m = true) :
    haltMarkerNat M w n = false := by
  have hdead : multistep (TM0.step M) (TM0.init w) (m + 1) = none := by
    cases hc : multistep (TM0.step M) (TM0.init w) (m + 1) with
    | none => rfl
    | some c => rw [haltMarkerNat, hc] at hm; simp at hm
  have hn : multistep (TM0.step M) (TM0.init w) n = none :=
    multistep_none_mono (by omega) hdead
  simp [haltMarkerNat, hn]

/-- **At most once (ℕ).** The compiled marker fires at most one fuel level. -/
lemma haltMarkerNat_at_most_once (M : TM0.Machine Γ Λ) (w : List Γ)
    {m n : ℕ} (hm : haltMarkerNat M w m = true) (hn : haltMarkerNat M w n = true) :
    m = n := by
  rcases lt_trichotomy m n with h | h | h
  · exact absurd hn (by simp [haltMarkerNat_eq_false_of_lt h hm])
  · exact h
  · exact absurd hm (by simp [haltMarkerNat_eq_false_of_lt h hn])

/-- **At most once (ℤ).** The `hone` hypothesis of `cd0_haltW_iff` is a
theorem for compiled markers. -/
lemma haltMarker_at_most_once (M : TM0.Machine Γ Λ) (w : List Γ) :
    ∀ i j, haltMarker M w i = true → haltMarker M w j = true → i = j := by
  intro i j hi hj
  unfold haltMarker at hi hj
  split at hi
  · split at hj
    · have := haltMarkerNat_at_most_once M w hi hj
      omega
    · simp at hj
  · simp at hi

/-- The ℤ-marker never fires iff the ℕ-marker never fires. -/
lemma haltMarker_all_false_iff (M : TM0.Machine Γ Λ) (w : List Γ) :
    (∀ i : ℤ, haltMarker M w i = false) ↔ ∀ n : ℕ, haltMarkerNat M w n = false := by
  constructor
  · intro h n
    have := h (n : ℤ)
    unfold haltMarker at this
    rw [if_pos (Int.natCast_nonneg n)] at this
    simpa using this
  · intro h i
    unfold haltMarker
    split
    · exact h _
    · rfl

/-- The ℕ-marker never fires iff the run is live at every fuel level. -/
lemma haltMarkerNat_all_false_iff (M : TM0.Machine Γ Λ) (w : List Γ) :
    (∀ n, haltMarkerNat M w n = false) ↔
      ∀ n, (multistep (TM0.step M) (TM0.init w) n).isSome = true := by
  constructor
  · intro h n
    induction n with
    | zero => simp
    | succ n ih =>
      cases hc : multistep (TM0.step M) (TM0.init w) (n + 1) with
      | some c => rfl
      | none =>
        exfalso
        have hn := h n
        rw [haltMarkerNat, hc] at hn
        simp [ih] at hn
  · intro h n
    simp [haltMarkerNat, h n, h (n + 1)]

/-! ## 4. Main results -/

/-- **The compiled reduction.** The generator compiled from a Turing machine
and its input satisfies the global Bakry-Émery bound `CD(0, ∞)` iff the
machine does **not** halt — with halting in Mathlib's own sense,
`(TM0.eval M w).Dom`. Deciding the global curvature bound on this computable
generator family is deciding the complement of the halting problem. -/
theorem cd0_compiled_iff (M : TM0.Machine Γ Λ) (w : List Γ) :
    CD0 (haltW (haltMarker M w)) ↔ ¬ (TM0.eval M w).Dom := by
  rw [cd0_haltW_iff _ (haltMarker_at_most_once M w),
    haltMarker_all_false_iff, haltMarkerNat_all_false_iff]
  have hdom : (TM0.eval M w).Dom ↔ (Turing.eval (TM0.step M) (TM0.init w)).Dom :=
    Iff.rfl
  rw [hdom, evalDom_iff_multistep]
  constructor
  · intro h hex
    obtain ⟨n, hn⟩ := hex
    have := h n
    rw [hn] at this
    simp at this
  · intro h n
    cases hc : multistep (TM0.step M) (TM0.init w) n with
    | none => exact absurd ⟨n, hc⟩ h
    | some c => rfl

/-- Contrapositive form: a curvature violation in the compiled generator is
exactly a halting certificate. -/
theorem not_cd0_compiled_iff (M : TM0.Machine Γ Λ) (w : List Γ) :
    ¬ CD0 (haltW (haltMarker M w)) ↔ (TM0.eval M w).Dom :=
  (cd0_compiled_iff M w).not.trans not_not

/-- A halting machine's compiled chain has a curvature defect. -/
theorem not_cd0_compiled_of_halts (M : TM0.Machine Γ Λ) (w : List Γ)
    (h : (TM0.eval M w).Dom) : ¬ CD0 (haltW (haltMarker M w)) :=
  (not_cd0_compiled_iff M w).mpr h

/-! ## 5. Both poles are inhabited -/

/-- The machine with no transitions: halts immediately on any input. -/
def haltNow : TM0.Machine Γ Λ := fun _ _ => none

/-- The machine that moves right forever: never halts on any input. -/
def spinRight : TM0.Machine Γ Λ := fun q _ => some (q, TM0.Stmt.move Dir.right)

lemma step_haltNow (c : TM0.Cfg Γ Λ) : TM0.step (haltNow (Γ := Γ) (Λ := Λ)) c = none := by
  rcases c with ⟨q, T⟩; rfl

lemma step_spinRight (c : TM0.Cfg Γ Λ) :
    TM0.step (spinRight (Γ := Γ) (Λ := Λ)) c = some ⟨c.q, c.Tape.move Dir.right⟩ := by
  rcases c with ⟨q, T⟩; rfl

/-- **The negative pole is concrete**: the immediately halting machine
compiles to a generator that violates `CD(0, ∞)`. -/
theorem not_cd0_haltNow (w : List Γ) :
    ¬ CD0 (haltW (haltMarker (haltNow (Γ := Γ) (Λ := Λ)) w)) := by
  apply not_cd0_compiled_of_halts
  have : (Turing.eval (TM0.step (haltNow (Γ := Γ) (Λ := Λ))) (TM0.init w)).Dom := by
    rw [evalDom_iff_multistep]
    exact ⟨1, by rw [multistep_succ, multistep_zero, Option.bind_some, step_haltNow]⟩
  exact this

/-- **The positive pole is concrete**: the never-halting machine compiles to
a generator that satisfies `CD(0, ∞)` (it is the flat line). -/
theorem cd0_spinRight (w : List Γ) :
    CD0 (haltW (haltMarker (spinRight (Γ := Γ) (Λ := Λ)) w)) := by
  rw [cd0_compiled_iff]
  intro hdom
  have : (Turing.eval (TM0.step (spinRight (Γ := Γ) (Λ := Λ))) (TM0.init w)).Dom := hdom
  rw [evalDom_iff_multistep] at this
  obtain ⟨n, hn⟩ := this
  have hlive : ∀ n, (multistep (TM0.step (spinRight (Γ := Γ) (Λ := Λ))) (TM0.init w) n).isSome = true := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      cases hc : multistep (TM0.step (spinRight (Γ := Γ) (Λ := Λ))) (TM0.init w) n with
      | none => rw [hc] at ih; simp at ih
      | some c =>
        rw [multistep_succ, hc, Option.bind_some, step_spinRight]
        rfl
  have := hlive n
  rw [hn] at this
  simp at this

end SGC.Bridge.HaltingCompiler
