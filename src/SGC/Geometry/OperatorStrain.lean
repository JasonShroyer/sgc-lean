/-
Copyright (c) 2026 Jason Shroyer. All rights reserved.
Released under Apache 2.0 license.
-/
import SGC.Bridge.CurvatureUndecidability

/-!
# The Discrete Operator-Strain Bridge

Discrete-first formalization of NS-Table goal 1 — the operator-strain
identity `Ric_BE(νΔ + u·∇) = νRic_g − S_u` (flat space: `= −S_u`) — at the
weighted-line layer where the SGC Γ-calculus is already kernel-verified.

Every identity below was derived and residual-checked by computer algebra
BEFORE formalization (`scripts/derivations/`, design note
`docs/operator-strain-design.md`); the Lean proofs are `ring`-level closures
of CAS-verified statements.

## The identity (discrete Bochner-with-strain)

For symmetric edge weights `q` (edge `{x, x+1}` has rate `q x`,
`SGC.Bridge.CurvatureUndecidability` conventions), **unconditionally**:

`Γ₂(f)(x) = [Hessian sum-of-squares with coefficients q(x−1)q(x−2)/4,
q(x−1)q(x)/2, q(x)q(x+1)/4] + q(x−1)/4·strainL(x)·(∇f)² + q(x)/4·strainR(x)·(∇f)²`

with `strainL(x) = 4q(x−1) − 3q(x) − q(x−2)` and
`strainR(x) = 4q(x) − 3q(x−1) − q(x+1)` — the deviation of the rate field
from local flatness. This is the exact discrete shadow of
`Γ₂ = ν²‖Hess f‖² + (νRic − S_u)(∇f, ∇f)`:

* zero strain (constant rates) ⇒ pure sum of squares ⇒ `CD(0,∞)`
  (`gam2_nonneg_of_zero_strain`, `cd0_const`; recovers `cd0_unitW` at `q ≡ 1`);
* **uniform drift is strain-free** (`driftline_bochner`, `cd0_driftline`):
  the asymmetric constant-rate generator `P(f(x+1)−f(x)) + M(f(x−1)−f(x))`
  has `Γ₂ = M²/4·D² + MP/2·D² + P²/4·D²` — the discrete "constant vector
  field on flat space has `S_u = 0`".

## The linear witness and the strain dipole

For a single strained edge `q(T) = 1 + s`:

* `Γ₂(id)(T−1) = −s/4 < 0` for **every** `s > 0` (`not_cd0_heavyW`): any
  strain, however small, breaks the global bound, witnessed by the identity
  function. The rate-4 gadget of `CurvatureUndecidability` is the `s = 3`
  member of this family — its margin was never needed.
* The total strain `σ(x) = 4·Γ₂(id)(x)` forms a **dipole**:
  `(−s, s(4s+1), s(4s+1), −s)` at `x = T−1, T, T+1, T+2`, zero elsewhere,
  summing to `8s² ≥ 0` (`heavyW_dipole_sum`). Compression at the flanks,
  extension at the core, net stretching positive — the discrete precursor of
  the continuum fact that incompressible strain is trace-free, hence nonzero
  strain forces a negative curvature direction *somewhere*. Negative operator
  curvature is generic; this is the cold-water guardrail made visible at the
  discrete layer.

## What is NOT claimed

No continuum statement (the `Ric_BE = −S_u` correspondence is prose); no
dependency on `SGC.Bridge.CantorHalting` (algebraically independent); the
variable-drift mixed identity and the continuum decaying-shear cold-water
theorem are deferred (design note).
-/

namespace SGC.Geometry.OperatorStrain

open SGC.Bridge.CurvatureUndecidability

/-! ## §1. Strain of a rate field -/

/-- Left strain coefficient at `x`: the deviation of the rate field from
local flatness, weighting `(f(x) − f(x−1))²` in the Bochner-with-strain
identity. Vanishes for constant rates. -/
def strainL (q : Weights) (x : ℤ) : ℝ := 4 * q (x - 1) - 3 * q x - q (x - 2)

/-- Right strain coefficient at `x`, weighting `(f(x+1) − f(x))²`. -/
def strainR (q : Weights) (x : ℤ) : ℝ := 4 * q x - 3 * q (x - 1) - q (x + 1)

/-- Total strain at `x`: the rate-weighted sum of the two strain
coefficients. Equals `4·Γ₂(id)(x)` (`gam2_linear_eq_totalStrain`). -/
def totalStrain (q : Weights) (x : ℤ) : ℝ :=
  q (x - 1) * strainL q x + q x * strainR q x

@[simp] lemma strainL_const (c : ℝ) (x : ℤ) : strainL (fun _ => c) x = 0 := by
  simp [strainL]; ring

@[simp] lemma strainR_const (c : ℝ) (x : ℤ) : strainR (fun _ => c) x = 0 := by
  simp [strainR]; ring

/-! ## §2. The discrete Bochner-with-strain identity -/

/-- **The discrete operator-strain identity** (unconditional). `Γ₂` on the
weighted line splits exactly into a Hessian sum-of-squares (second
differences, with rate-product coefficients) plus the strain quadratic form
on the gradient — the discrete shadow of
`Γ₂ = ν²‖Hess f‖² + (νRic − S_u)(∇f, ∇f)` on flat space. -/
theorem gam2_strain_eq (q : Weights) (f : ℤ → ℝ) (x : ℤ) :
    gam2 q f f x
      = q (x - 1) * q (x - 2) / 4 * (f (x - 2) - 2 * f (x - 1) + f x) ^ 2
      + q (x - 1) * q x / 2 * (f (x - 1) - 2 * f x + f (x + 1)) ^ 2
      + q x * q (x + 1) / 4 * (f x - 2 * f (x + 1) + f (x + 2)) ^ 2
      + q (x - 1) * strainL q x / 4 * (f x - f (x - 1)) ^ 2
      + q x * strainR q x / 4 * (f (x + 1) - f x) ^ 2 := by
  have e1 : x - 1 - 1 = x - 2 := by ring
  have e2 : x - 1 + 1 = x := by ring
  have e3 : x + 1 - 1 = x := by ring
  have e4 : x + 1 + 1 = x + 2 := by ring
  simp only [gam2, gam, lineGen, strainL, strainR, e1, e2, e3, e4]
  ring

/-- **Zero strain forces pointwise flatness.** If the two strain coefficients
vanish at `x` and the rates are nonnegative on the stencil, then
`Γ₂(f)(x) ≥ 0` for every observable. -/
theorem gam2_nonneg_of_zero_strain (q : Weights) (x : ℤ)
    (hq2 : 0 ≤ q (x - 2)) (hq1 : 0 ≤ q (x - 1)) (hq0 : 0 ≤ q x)
    (hqp : 0 ≤ q (x + 1))
    (hL : strainL q x = 0) (hR : strainR q x = 0) (f : ℤ → ℝ) :
    0 ≤ gam2 q f f x := by
  rw [gam2_strain_eq, hL, hR]
  have s1 : (0:ℝ) ≤ q (x - 1) * q (x - 2) / 4 * (f (x - 2) - 2 * f (x - 1) + f x) ^ 2 :=
    mul_nonneg (by positivity) (sq_nonneg _)
  have s2 : (0:ℝ) ≤ q (x - 1) * q x / 2 * (f (x - 1) - 2 * f x + f (x + 1)) ^ 2 :=
    mul_nonneg (by positivity) (sq_nonneg _)
  have s3 : (0:ℝ) ≤ q x * q (x + 1) / 4 * (f x - 2 * f (x + 1) + f (x + 2)) ^ 2 :=
    mul_nonneg (by positivity) (sq_nonneg _)
  linarith

/-- Constant rates satisfy `CD(0,∞)` for any `c ≥ 0`: zero strain everywhere.
Recovers `cd0_unitW` at `c = 1`. -/
theorem cd0_const {c : ℝ} (hc : 0 ≤ c) : CD0 (fun _ => c) := fun f x =>
  gam2_nonneg_of_zero_strain _ x hc hc hc hc (strainL_const c x)
    (strainR_const c x) f

/-! ## §3. Uniform drift is strain-free -/

/-- Generic carré du champ for an arbitrary line operator (needed because
`gam` is specialized to symmetric weights). -/
noncomputable def gamOp (Lop : (ℤ → ℝ) → ℤ → ℝ) (f g : ℤ → ℝ) : ℤ → ℝ := fun x =>
  (1 / 2) * (Lop (fun y => f y * g y) x - f x * Lop g x - g x * Lop f x)

/-- Generic iterated carré du champ. -/
noncomputable def gam2Op (Lop : (ℤ → ℝ) → ℤ → ℝ) (f g : ℤ → ℝ) : ℤ → ℝ := fun x =>
  (1 / 2) * (Lop (gamOp Lop f g) x - gamOp Lop f (Lop g) x - gamOp Lop (Lop f) g x)

/-- The generic Γ-calculus restricts to the symmetric-weight one. -/
lemma gamOp_lineGen (q : Weights) : gamOp (lineGen q) = gam q := rfl

lemma gam2Op_lineGen (q : Weights) : gam2Op (lineGen q) = gam2 q := rfl

/-- The uniformly drifted line: forward rate `P`, backward rate `M`
(viscosity `ν = (P+M)/2`, drift `b = P − M`). The discrete constant vector
field on flat space. -/
def driftGen (P M : ℝ) (f : ℤ → ℝ) : ℤ → ℝ := fun x =>
  P * (f (x + 1) - f x) + M * (f (x - 1) - f x)

/-- **Uniform drift generates no strain.** `Γ₂` of the drifted line is a pure
Hessian sum of squares — the exact discrete analogue of `S_u = 0` for a
constant vector field `u` on the flat torus. Note the drift-split
coefficients `M²/4, MP/2, P²/4` (at `P = M = 1`: the flat Bochner identity
`gam2_unitW_eq`). -/
theorem driftline_bochner (P M : ℝ) (f : ℤ → ℝ) (x : ℤ) :
    gam2Op (driftGen P M) f f x
      = M ^ 2 / 4 * (f (x - 2) - 2 * f (x - 1) + f x) ^ 2
      + M * P / 2 * (f (x - 1) - 2 * f x + f (x + 1)) ^ 2
      + P ^ 2 / 4 * (f x - 2 * f (x + 1) + f (x + 2)) ^ 2 := by
  have e1 : x - 1 - 1 = x - 2 := by ring
  have e2 : x - 1 + 1 = x := by ring
  have e3 : x + 1 - 1 = x := by ring
  have e4 : x + 1 + 1 = x + 2 := by ring
  simp only [gam2Op, gamOp, driftGen, e1, e2, e3, e4]
  ring

/-- **`CD(0,∞)` for every uniformly drifted line.** No amount of uniform
drift can create negative operator curvature: viscosity-scale asymmetry
without inhomogeneity is curvature-neutral. -/
theorem cd0_driftline {P M : ℝ} (hP : 0 ≤ P) (hM : 0 ≤ M) (f : ℤ → ℝ) (x : ℤ) :
    0 ≤ gam2Op (driftGen P M) f f x := by
  rw [driftline_bochner]
  have s1 : (0:ℝ) ≤ M ^ 2 / 4 * (f (x - 2) - 2 * f (x - 1) + f x) ^ 2 :=
    mul_nonneg (by positivity) (sq_nonneg _)
  have s2 : (0:ℝ) ≤ M * P / 2 * (f (x - 1) - 2 * f x + f (x + 1)) ^ 2 :=
    mul_nonneg (by positivity) (sq_nonneg _)
  have s3 : (0:ℝ) ≤ P ^ 2 / 4 * (f x - 2 * f (x + 1) + f (x + 2)) ^ 2 :=
    mul_nonneg (by positivity) (sq_nonneg _)
  linarith

/-! ## §4. The linear witness and the strain dipole -/

/-- **`Γ₂` of the identity function reads off the total strain.** The linear
observable kills every second difference, so the Bochner part vanishes and
`Γ₂(id)(x) = σ(x)/4` exactly: the identity function is the universal strain
meter. -/
theorem gam2_linear_eq_totalStrain (q : Weights) (x : ℤ) :
    gam2 q (fun n => (n : ℝ)) (fun n => (n : ℝ)) x = totalStrain q x / 4 := by
  rw [gam2_strain_eq]
  simp only [totalStrain, strainL, strainR]
  push_cast
  ring

/-- The single strained edge: rate `1 + s` on edge `{T, T+1}`, rate `1`
everywhere else. The rate-4 gadget of `CurvatureUndecidability` is `s = 3`. -/
def heavyW (T : ℤ) (s : ℝ) : Weights := fun i => if i = T then 1 + s else 1

@[simp] lemma heavyW_self (T : ℤ) (s : ℝ) : heavyW T s T = 1 + s := if_pos rfl

lemma heavyW_ne (T : ℤ) (s : ℝ) {i : ℤ} (h : i ≠ T) : heavyW T s i = 1 :=
  if_neg h

/-- Compression at the left flank: `σ(T−1) = −s`. -/
lemma totalStrain_heavyW_left_flank (T : ℤ) (s : ℝ) :
    totalStrain (heavyW T s) (T - 1) = -s := by
  have h1 : T - 1 - 1 ≠ T := by omega
  have h2 : T - 1 - 2 ≠ T := by omega
  have h3 : T - 1 ≠ T := by omega
  have h4 : T - 1 + 1 = T := by ring
  simp only [totalStrain, strainL, strainR, heavyW_ne T s h1, heavyW_ne T s h2,
    heavyW_ne T s h3, h4, heavyW_self]
  ring

/-- Extension at the core: `σ(T) = s(4s + 1)`. -/
lemma totalStrain_heavyW_core (T : ℤ) (s : ℝ) :
    totalStrain (heavyW T s) T = s * (4 * s + 1) := by
  have h1 : T - 1 ≠ T := by omega
  have h2 : T - 2 ≠ T := by omega
  have h3 : T + 1 ≠ T := by omega
  simp only [totalStrain, strainL, strainR, heavyW_ne T s h1, heavyW_ne T s h2,
    heavyW_ne T s h3, heavyW_self]
  ring

/-- **Any strain breaks `CD(0,∞)`, witnessed by the identity function.** For
every `s > 0`, however small, the single strained edge violates the global
Bakry-Émery bound: `Γ₂(id)(T−1) = −s/4 < 0`. Negative operator curvature is
generic under rate inhomogeneity — the discrete form of the guardrail that
negative curvature alone can never certify singular behaviour. -/
theorem not_cd0_heavyW (T : ℤ) {s : ℝ} (hs : 0 < s) : ¬ CD0 (heavyW T s) := by
  intro h
  have hb := h (fun n => (n : ℝ)) (T - 1)
  rw [gam2_linear_eq_totalStrain, totalStrain_heavyW_left_flank] at hb
  linarith

/-- **The strain dipole sum rule.** The four nonzero total-strain values of
the strained edge sum to `8s² = 4[(∇q)² at each flank]`: compression `−s` at
the flanks, extension `s(4s+1)` at the core, net stretching nonnegative. The
discrete precursor of "incompressible strain is trace-free": local negative
strain is forced by any inhomogeneity even though the net is nonnegative. -/
theorem heavyW_dipole_sum (T : ℤ) (s : ℝ) :
    totalStrain (heavyW T s) (T - 1) + totalStrain (heavyW T s) T
      + totalStrain (heavyW T s) (T + 1) + totalStrain (heavyW T s) (T + 2)
      = 8 * s ^ 2 := by
  have hright : totalStrain (heavyW T s) (T + 1) = s * (4 * s + 1) := by
    have h1 : T + 1 ≠ T := by omega
    have h2 : T + 1 - 1 = T := by ring
    have h3 : T + 1 - 2 ≠ T := by omega
    have h4 : T + 1 + 1 ≠ T := by omega
    simp only [totalStrain, strainL, strainR, heavyW_ne T s h1, h2,
      heavyW_ne T s h3, heavyW_ne T s h4, heavyW_self]
    ring
  have hflank : totalStrain (heavyW T s) (T + 2) = -s := by
    have h1 : T + 2 ≠ T := by omega
    have h2 : T + 2 - 1 ≠ T := by omega
    have h3 : T + 2 - 2 = T := by ring
    have h4 : T + 2 + 1 ≠ T := by omega
    simp only [totalStrain, strainL, strainR, heavyW_ne T s h1, heavyW_ne T s h2,
      h3, heavyW_ne T s h4, heavyW_self]
    ring
  rw [totalStrain_heavyW_left_flank, totalStrain_heavyW_core, hright, hflank]
  ring

/-- Away from the strained edge the total strain vanishes: the dipole is the
entire strain content. -/
lemma totalStrain_heavyW_away (T : ℤ) (s : ℝ) {x : ℤ}
    (hx : x < T - 1 ∨ T + 2 < x) :
    totalStrain (heavyW T s) x = 0 := by
  have h1 : x - 1 ≠ T := by omega
  have h2 : x - 2 ≠ T := by omega
  have h3 : x ≠ T := by omega
  have h4 : x + 1 ≠ T := by omega
  simp only [totalStrain, strainL, strainR, heavyW_ne T s h1, heavyW_ne T s h2,
    heavyW_ne T s h3, heavyW_ne T s h4]
  ring

end SGC.Geometry.OperatorStrain
