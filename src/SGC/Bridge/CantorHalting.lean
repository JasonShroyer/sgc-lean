/-
Copyright (c) 2026 Jason Shroyer. All rights reserved.
Released under Apache 2.0 license.
-/
import SGC.Bridge.HaltingCompiler
import SGC.Bridge.CantorShiftTower

/-!
# The Resolution Horizon: halting fuel = cylinder depth = defect location

Composition bridge between three kernel-verified layers:

* `SGC.Bridge.HaltingCompiler` — the exact-step halting marker
  `haltMarkerNat M w : ℕ → Bool` for Mathlib's `Turing.TM0` machines;
* `SGC.Topology.PadicPathSpace` — the symbolic trajectory space
  `PathSpace A = ℕ → A` with its depth-`n` truncations (the Cantor set,
  `PathSpace (Fin p) ≃ₜ ℤ_[p]`);
* `SGC.Bridge.CurvatureUndecidability` — the weighted line whose global
  Bakry-Émery bound encodes halting through a single heavy edge.

The theorem cluster: for a machine that halts at exactly fuel `T`, the number
`T` is simultaneously, in three formal registers,

1. **the cylinder depth**: the halting event is read off coordinate `T` of
   the depth-`(T+1)` truncation of the marker path (`haltsAt_iff_truncate`),
   and at every depth `n ≤ T` the marker path is *indistinguishable* from the
   never-halting path (`truncate_markerPath_eq_of_le`) — they separate at
   depth `T + 1` exactly (`truncate_markerPath_ne_at_horizon`);
2. **the halting fuel**: `HaltsAt M w T` is the exact-step predicate of the
   compiler (definitionally);
3. **the curvature-defect location**: the compiled generator
   `haltW (haltMarker M w)` has pointwise `Γ₂ ≥ 0` at every site whose
   Γ₂-stencil avoids the single heavy edge `{T, T+1}`
   (`compiled_gam2_nonneg_away`), where the stencil is *derived*, not
   assumed: `Γ₂(f)(x)` inspects exactly the four edge rates
   `q(x−2), q(x−1), q(x), q(x+1)` (`gam2_local_eq`).

`resolution_horizon` packages the three registers under the single explicit
hypothesis `HaltsAt M w T`.

## Index convention

Fuel `0` is the initial configuration (always live); `HaltsAt M w T` means
the run completes exactly `T` steps and the `none` transition occurs between
fuel `T` and `T + 1`. `haltNow` halts at `T = 0` (`haltsAt_haltNow`). There
is no total "horizon" object: all statements are conditional on `HaltsAt`,
and the never-halting comparison point is `neverHaltPath = const 0`, realized
concretely by `spinRight` (`markerPath_spinRight`).

## What is NOT claimed (recorded per design note, docs/cantor-halting-design.md)

* No ε(n) activation law for a halting-decorated shift kernel — that is an
  open construction project, not a corollary of this module.
* No claim that lattice strain "is" projected symbolic drift;
  `SGC.Geometry.OperatorStrain` is algebraically independent of this module.
-/

namespace SGC.Bridge.CantorHalting

open Turing
open SGC.Topology.PadicPathSpace
open SGC.Bridge.CurvatureUndecidability
open SGC.Bridge.HaltingCompiler

variable {Γ : Type*} [Inhabited Γ] {Λ : Type*} [Inhabited Λ]

/-! ## §1. The halting history as a Cantor point -/

/-- The machine halts at exactly fuel `T`: the exact-step predicate of the
compiler, as a `Prop`. Fuel `0` is the initial configuration. -/
def HaltsAt (M : TM0.Machine Γ Λ) (w : List Γ) (T : ℕ) : Prop :=
  haltMarkerNat M w T = true

/-- The marker path: the halting history of `(M, w)` as a point of the
symbolic trajectory space `PathSpace (Fin 2)` — coordinate `n` is `1` iff the
machine halts at exactly fuel `n`. Under `pathSpace_homeo_padicInt` this is a
point of the 2-adic Cantor set `ℤ_[2]`. -/
def markerPath (M : TM0.Machine Γ Λ) (w : List Γ) : PathSpace (Fin 2) :=
  fun n => if haltMarkerNat M w n then 1 else 0

/-- The trajectory of any never-halting computation: the constant path. -/
def neverHaltPath : PathSpace (Fin 2) := fun _ => 0

@[simp] lemma markerPath_apply_eq_one_iff (M : TM0.Machine Γ Λ) (w : List Γ)
    (n : ℕ) : markerPath M w n = 1 ↔ haltMarkerNat M w n = true := by
  unfold markerPath
  split <;> simp_all

@[simp] lemma markerPath_apply_eq_zero_iff (M : TM0.Machine Γ Λ) (w : List Γ)
    (n : ℕ) : markerPath M w n = 0 ↔ haltMarkerNat M w n = false := by
  unfold markerPath
  split <;> simp_all

/-- The never-halting pole is realized: the marker path of `spinRight` is the
constant path. -/
lemma markerPath_spinRight (w : List Γ) :
    markerPath (spinRight (Γ := Γ) (Λ := Λ)) w = neverHaltPath := by
  funext n
  have hlive : ∀ m, (multistep (TM0.step (spinRight (Γ := Γ) (Λ := Λ)))
      (TM0.init w) m).isSome = true := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      cases hc : multistep (TM0.step (spinRight (Γ := Γ) (Λ := Λ))) (TM0.init w) m with
      | none => rw [hc] at ih; simp at ih
      | some c =>
        rw [multistep_succ, hc, Option.bind_some, step_spinRight]
        rfl
  have : haltMarkerNat (spinRight (Γ := Γ) (Λ := Λ)) w n = false := by
    simp [haltMarkerNat, hlive n, hlive (n + 1)]
  simp [markerPath, neverHaltPath, this]

/-- The immediately-halting pole: `haltNow` halts at exactly fuel `0`. -/
lemma haltsAt_haltNow (w : List Γ) : HaltsAt (haltNow (Γ := Γ) (Λ := Λ)) w 0 := by
  unfold HaltsAt haltMarkerNat
  rw [multistep_succ, multistep_zero, Option.bind_some, step_haltNow]
  rfl

/-! ## §2. Register 1: halting is a depth-`(T+1)` cylinder event -/

/-- **The cylinder representation, with the exact bound.** Halting at exactly
fuel `T` is read off coordinate `T` of the depth-`(T + 1)` truncation of the
marker path. Coordinate `T` exists in `Fin (T + 1)` and in no shallower
truncation: the event is a cylinder observable of depth exactly `T + 1`. -/
theorem haltsAt_iff_truncate (M : TM0.Machine Γ Λ) (w : List Γ) (T : ℕ) :
    HaltsAt M w T ↔
      truncate (Fin 2) (T + 1) (markerPath M w) ⟨T, Nat.lt_succ_self T⟩ = 1 := by
  rw [truncate_apply]
  exact (markerPath_apply_eq_one_iff M w T).symm

/-- **Resolution blindness below the horizon.** If the machine halts at
exactly fuel `T`, then at every truncation depth `n ≤ T` the marker path is
*equal* — not merely close — to the never-halting path. A depth-`n` observer
provably cannot distinguish the halting machine from `spinRight`. -/
theorem truncate_markerPath_eq_of_le (M : TM0.Machine Γ Λ) (w : List Γ)
    {T n : ℕ} (hT : HaltsAt M w T) (hn : n ≤ T) :
    truncate (Fin 2) n (markerPath M w) = truncate (Fin 2) n neverHaltPath := by
  funext i
  simp only [truncate_apply]
  have hlt : (i : ℕ) < T := lt_of_lt_of_le i.isLt hn
  have hfalse : haltMarkerNat M w i = false := by
    cases hb : haltMarkerNat M w i with
    | false => rfl
    | true =>
      exact absurd (haltMarkerNat_at_most_once M w hb hT) (Nat.ne_of_lt hlt)
  simp [markerPath, neverHaltPath, hfalse]

/-- **Separation at the horizon.** At depth `T + 1` the marker path and the
never-halting path differ: `T + 1` is the *exact* resolution at which the
halting machine becomes distinguishable from the flat tower. -/
theorem truncate_markerPath_ne_at_horizon (M : TM0.Machine Γ Λ) (w : List Γ)
    {T : ℕ} (hT : HaltsAt M w T) :
    truncate (Fin 2) (T + 1) (markerPath M w) ≠
      truncate (Fin 2) (T + 1) neverHaltPath := by
  intro h
  have := congrFun h ⟨T, Nat.lt_succ_self T⟩
  simp only [truncate_apply] at this
  rw [(markerPath_apply_eq_one_iff M w T).mpr hT] at this
  simp [neverHaltPath] at this

/-! ## §3. Register 3: the Γ₂ stencil, derived not assumed -/

/-- **The localized discrete Bochner identity.** `Γ₂(f)(x)` on the weighted
line inspects exactly the four edge rates `q(x−2), q(x−1), q(x), q(x+1)` —
the same support as the proved gadget certificate `gam2_heavy_eq`. If those
four rates are `1`, the Bochner sum-of-squares holds at `x` regardless of the
rates anywhere else on the line. -/
theorem gam2_local_eq (q : Weights) (x : ℤ)
    (h2 : q (x - 2) = 1) (h1 : q (x - 1) = 1) (h0 : q x = 1) (hp : q (x + 1) = 1)
    (f : ℤ → ℝ) :
    gam2 q f f x
      = 1 / 4 * (f (x - 2) - 2 * f (x - 1) + f x) ^ 2
      + 1 / 2 * (f (x - 1) - 2 * f x + f (x + 1)) ^ 2
      + 1 / 4 * (f x - 2 * f (x + 1) + f (x + 2)) ^ 2 := by
  have e1 : x - 1 - 1 = x - 2 := by ring
  have e2 : x - 1 + 1 = x := by ring
  have e3 : x + 1 - 1 = x := by ring
  have e4 : x + 1 + 1 = x + 2 := by ring
  simp only [gam2, gam, lineGen, e1, e2, e3, e4, h2, h1, h0, hp]
  ring

/-- **Localized flatness.** Unit rates on the four stencil edges force
pointwise nonnegative Bakry-Émery curvature at `x`. -/
theorem gam2_nonneg_of_unit_stencil (q : Weights) (x : ℤ)
    (h2 : q (x - 2) = 1) (h1 : q (x - 1) = 1) (h0 : q x = 1) (hp : q (x + 1) = 1)
    (f : ℤ → ℝ) : 0 ≤ gam2 q f f x := by
  rw [gam2_local_eq q x h2 h1 h0 hp f]
  have s1 : (0:ℝ) ≤ (f (x - 2) - 2 * f (x - 1) + f x) ^ 2 := sq_nonneg _
  have s2 : (0:ℝ) ≤ (f (x - 1) - 2 * f x + f (x + 1)) ^ 2 := sq_nonneg _
  have s3 : (0:ℝ) ≤ (f x - 2 * f (x + 1) + f (x + 2)) ^ 2 := sq_nonneg _
  linarith

/-- For a machine halting at exactly fuel `T`, every rate of the compiled
generator away from index `(T : ℤ)` is `1`: the heavy edge is unique. -/
lemma compiled_rate_eq_one (M : TM0.Machine Γ Λ) (w : List Γ)
    {T : ℕ} (hT : HaltsAt M w T) {j : ℤ} (hj : j ≠ (T : ℤ)) :
    haltW (haltMarker M w) j = 1 := by
  cases hb : haltMarker M w j with
  | false => exact haltW_eq_one hb
  | true =>
    exfalso
    have hTz : haltMarker M w (T : ℤ) = true := by
      unfold haltMarker
      rw [if_pos (Int.natCast_nonneg T)]
      simpa using hT
    exact hj (haltMarker_at_most_once M w j (T : ℤ) hb hTz)

/-- **The defect support is exactly the stencil of the heavy edge.** For a
machine halting at fuel `T`, the compiled generator has pointwise `Γ₂ ≥ 0`
at every site `x` whose stencil `{x−2, x−1, x, x+1}` avoids `(T : ℤ)` — i.e.
everywhere except the four sites adjacent to the heavy edge `{T, T+1}`. -/
theorem compiled_gam2_nonneg_away (M : TM0.Machine Γ Λ) (w : List Γ)
    {T : ℕ} (hT : HaltsAt M w T) {x : ℤ}
    (hx : x - 2 ≠ (T : ℤ) ∧ x - 1 ≠ (T : ℤ) ∧ x ≠ (T : ℤ) ∧ x + 1 ≠ (T : ℤ))
    (f : ℤ → ℝ) : 0 ≤ gam2 (haltW (haltMarker M w)) f f x := by
  obtain ⟨g2, g1, g0, gp⟩ := hx
  exact gam2_nonneg_of_unit_stencil _ x
    (compiled_rate_eq_one M w hT g2) (compiled_rate_eq_one M w hT g1)
    (compiled_rate_eq_one M w hT g0) (compiled_rate_eq_one M w hT gp) f

/-! ## §4. The three registers, met -/

/-- **The Resolution Horizon.** If `(M, w)` halts at exactly fuel `T`, then
the single number `T` is simultaneously:

1. the cylinder depth — the halting event is coordinate `T` of the
   depth-`(T+1)` truncation, and at every depth `n ≤ T` the marker path
   *equals* the never-halting path (the event lives in the kernel of every
   coarse truncation below the horizon);
2. the halting fuel — by hypothesis;
3. the curvature-defect location — the compiled generator's `Γ₂` is
   pointwise nonnegative at every site whose four-edge stencil avoids
   `(T : ℤ)`; the global `CD(0,∞)` violation certified by
   `not_cd0_compiled_iff` is supported entirely on the heavy edge `{T, T+1}`.

Below the halting scale the symbolic and geometric registers are exactly
flat; the undecidable content is concentrated at one resolution depth and
one lattice edge, and they are the same number. -/
theorem resolution_horizon (M : TM0.Machine Γ Λ) (w : List Γ)
    {T : ℕ} (hT : HaltsAt M w T) :
    (truncate (Fin 2) (T + 1) (markerPath M w) ⟨T, Nat.lt_succ_self T⟩ = 1) ∧
    (∀ n ≤ T, truncate (Fin 2) n (markerPath M w) = truncate (Fin 2) n neverHaltPath) ∧
    (∀ x : ℤ, x - 2 ≠ (T : ℤ) → x - 1 ≠ (T : ℤ) → x ≠ (T : ℤ) → x + 1 ≠ (T : ℤ) →
      ∀ f : ℤ → ℝ, 0 ≤ gam2 (haltW (haltMarker M w)) f f x) :=
  ⟨(haltsAt_iff_truncate M w T).mp hT,
   fun _ hn => truncate_markerPath_eq_of_le M w hT hn,
   fun _ g2 g1 g0 gp f => compiled_gam2_nonneg_away M w hT ⟨g2, g1, g0, gp⟩ f⟩

end SGC.Bridge.CantorHalting
