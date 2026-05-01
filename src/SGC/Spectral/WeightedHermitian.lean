/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import SGC.Axioms.Geometry

/-!
# WeightedHermitian: π-self-adjoint matrices and constructive functional calculus

This module formalises the **finite-dimensional spectral calculus bridge**
described in `@c:\Lean4 Projects\reports\DESIGN_REPRESENTED_STABILITY_FLOW.md`
Phase R1.  Its purpose is to retire the three axioms
`SectorialFunctionalCalculus`, `functional_calculus_commutes_semigroup`,
and `functional_calculus_scaling` in
`@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean` by
constructively defining `ψ(sL)` as a matrix when `L` is *self-adjoint
under the π-weighted inner product* (`IsSymmPi`).

## Naming

We use `pi_dist` (not `π`) for distribution arguments because `π` is the
reserved name for `Real.pi` once `open Real` is active.  Internal lemma
hypotheses use `hπ` for `∀ v, 0 < pi_dist v`, matching
`@c:\Lean4 Projects\src\SGC\Spectral\NormedBridge.lean`.

## Main results in this file

* `IsSymmPi` — π-weighted self-adjointness predicate.
* `IsSymmPi.detailedBalance` — equivalence with the matrix DB form.
* `IsSymmPi.smul` — preserved under scalar multiplication.
* `Dsqrt`, `Dinvsqrt` — diagonal weight matrices.
* `Dsqrt_mul_Dinvsqrt`, `Dinvsqrt_mul_Dsqrt` — they cancel to `1`.
* `Dsqrt_isUnit`, `Dsqrt_inv_eq_Dinvsqrt` — invertibility.
* `toStdMatrix` — the conjugated matrix `D^{1/2} L D^{-1/2}`.
* `toStdMatrix_apply` — its entry-wise formula.
* `toStdMatrix_isHermitian` — the conjugated matrix is `IsHermitian`.
* `toStdMatrix_smul` — conjugation respects scalar multiplication.

The constructive `funCalculus_SA` and the two property theorems built on
top of these foundations live in a downstream section
(`@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean` post-Phase-R1).
-/

noncomputable section

namespace SGC.Spectral.WeightedHermitian

open Matrix Real

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The π-weighted self-adjointness predicate -/

/-- A matrix `L : Matrix V V ℝ` is **π-symmetric** (or π-self-adjoint) if
    `⟨L u, v⟩_π = ⟨u, L v⟩_π` for all `u, v : V → ℝ`.

    For positive `pi_dist`, this is equivalent to the *detailed-balance*
    relation `pi_dist x · L_{x,y} = pi_dist y · L_{y,x}` (see
    `IsSymmPi.detailedBalance` below). -/
def IsSymmPi (L : Matrix V V ℝ) (pi_dist : V → ℝ) (_hπ : ∀ v, 0 < pi_dist v) :
    Prop :=
  ∀ u v : V → ℝ, inner_pi pi_dist (L *ᵥ u) v = inner_pi pi_dist u (L *ᵥ v)

/-- Helper: `(L *ᵥ Pi.single y 1) v = L v y`. -/
private lemma mulVec_single_one_apply (L : Matrix V V ℝ) (y v : V) :
    (L *ᵥ Pi.single y (1 : ℝ)) v = L v y := by
  rw [Matrix.mulVec_single_one]
  rfl

/-- Helper: `inner_pi pi_dist (Pi.single x 1) f = pi_dist x · f x`. -/
private lemma inner_pi_single_left (pi_dist : V → ℝ) (x : V) (f : V → ℝ) :
    inner_pi pi_dist (Pi.single x (1 : ℝ)) f = pi_dist x * f x := by
  unfold inner_pi
  rw [Finset.sum_eq_single x]
  · simp [Pi.single_eq_same]
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro hx; exact (hx (Finset.mem_univ x)).elim

/-- Helper: `inner_pi pi_dist f (Pi.single x 1) = pi_dist x · f x`. -/
private lemma inner_pi_single_right (pi_dist : V → ℝ) (x : V) (f : V → ℝ) :
    inner_pi pi_dist f (Pi.single x (1 : ℝ)) = pi_dist x * f x := by
  unfold inner_pi
  rw [Finset.sum_eq_single x]
  · simp [Pi.single_eq_same]
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro hx; exact (hx (Finset.mem_univ x)).elim

/-- Detailed-balance form of `IsSymmPi`:
    `pi_dist x · L_{x,y} = pi_dist y · L_{y,x}`.

    Apply `IsSymmPi` to the basis vectors `Pi.single y 1` and
    `Pi.single x 1`. -/
lemma IsSymmPi.detailedBalance {L : Matrix V V ℝ} {pi_dist : V → ℝ}
    {hπ : ∀ v, 0 < pi_dist v} (hL : IsSymmPi L pi_dist hπ) (x y : V) :
    pi_dist x * L x y = pi_dist y * L y x := by
  have h := hL (Pi.single y 1) (Pi.single x 1)
  -- LHS: `inner_pi pi (L *ᵥ e_y) e_x = pi x · (L *ᵥ e_y) x = pi x · L x y`.
  have lhs_eq : inner_pi pi_dist (L *ᵥ Pi.single y (1 : ℝ)) (Pi.single x 1) =
                pi_dist x * L x y := by
    rw [inner_pi_single_right]
    rw [mulVec_single_one_apply]
  -- RHS: `inner_pi pi e_y (L *ᵥ e_x) = pi y · (L *ᵥ e_x) y = pi y · L y x`.
  have rhs_eq : inner_pi pi_dist (Pi.single y (1 : ℝ)) (L *ᵥ Pi.single x 1) =
                pi_dist y * L y x := by
    rw [inner_pi_single_left]
    rw [mulVec_single_one_apply]
  linarith [lhs_eq.symm.trans (h.trans rhs_eq)]

/-- `IsSymmPi` is preserved under scalar multiplication. -/
lemma IsSymmPi.smul {L : Matrix V V ℝ} {pi_dist : V → ℝ}
    {hπ : ∀ v, 0 < pi_dist v} (hL : IsSymmPi L pi_dist hπ) (c : ℝ) :
    IsSymmPi (c • L) pi_dist hπ := by
  intro u v
  -- `((c • L) *ᵥ u) = c • (L *ᵥ u)` and `inner_pi` is bilinear.
  have hL_smul : (c • L) *ᵥ u = c • (L *ᵥ u) := Matrix.smul_mulVec _ _ _
  rw [hL_smul]
  -- And similarly for `((c • L) *ᵥ v)`.
  have hL_smul' : (c • L) *ᵥ v = c • (L *ᵥ v) := Matrix.smul_mulVec _ _ _
  rw [hL_smul']
  -- Now reduce to `inner_pi (c • a) b = c · inner_pi a b` (and same on the right).
  have lhs : inner_pi pi_dist (c • (L *ᵥ u)) v = c * inner_pi pi_dist (L *ᵥ u) v := by
    unfold inner_pi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    simp [Pi.smul_apply, smul_eq_mul]; ring
  have rhs : inner_pi pi_dist u (c • (L *ᵥ v)) = c * inner_pi pi_dist u (L *ᵥ v) := by
    unfold inner_pi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    simp [Pi.smul_apply, smul_eq_mul]; ring
  rw [lhs, rhs, hL u v]

/-! ## 2. The diagonal weight matrices `D^{1/2}` and `D^{-1/2}` -/

/-- `D^{1/2}` — the diagonal matrix with entries `√(pi_dist v)`. -/
def Dsqrt (pi_dist : V → ℝ) : Matrix V V ℝ :=
  Matrix.diagonal (fun v => Real.sqrt (pi_dist v))

/-- `D^{-1/2}` — the diagonal matrix with entries `1 / √(pi_dist v)`. -/
def Dinvsqrt (pi_dist : V → ℝ) : Matrix V V ℝ :=
  Matrix.diagonal (fun v => 1 / Real.sqrt (pi_dist v))

/-- `D^{1/2}` is `IsHermitian` (any real diagonal matrix is). -/
lemma Dsqrt_isHermitian (pi_dist : V → ℝ) :
    (Dsqrt pi_dist : Matrix V V ℝ).IsHermitian :=
  Matrix.isHermitian_diagonal _

/-- `D^{-1/2}` is `IsHermitian` (any real diagonal matrix is). -/
lemma Dinvsqrt_isHermitian (pi_dist : V → ℝ) :
    (Dinvsqrt pi_dist : Matrix V V ℝ).IsHermitian :=
  Matrix.isHermitian_diagonal _

/-- `D^{1/2}` and `D^{-1/2}` multiply to the identity (right cancellation). -/
lemma Dsqrt_mul_Dinvsqrt {pi_dist : V → ℝ} (hπ : ∀ v, 0 < pi_dist v) :
    (Dsqrt pi_dist : Matrix V V ℝ) * Dinvsqrt pi_dist = 1 := by
  unfold Dsqrt Dinvsqrt
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    have hπi_ne : Real.sqrt (pi_dist i) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (hπ i))
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, mul_one_div_cancel hπi_ne]
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

/-- `D^{-1/2}` and `D^{1/2}` multiply to the identity (left cancellation). -/
lemma Dinvsqrt_mul_Dsqrt {pi_dist : V → ℝ} (hπ : ∀ v, 0 < pi_dist v) :
    (Dinvsqrt pi_dist : Matrix V V ℝ) * Dsqrt pi_dist = 1 := by
  unfold Dsqrt Dinvsqrt
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    have hπi_ne : Real.sqrt (pi_dist i) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (hπ i))
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, one_div_mul_cancel hπi_ne]
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

/-- `D^{1/2}` is invertible with inverse `D^{-1/2}`. -/
lemma Dsqrt_isUnit {pi_dist : V → ℝ} (hπ : ∀ v, 0 < pi_dist v) :
    IsUnit (Dsqrt pi_dist : Matrix V V ℝ) :=
  ⟨⟨Dsqrt pi_dist, Dinvsqrt pi_dist,
      Dsqrt_mul_Dinvsqrt hπ, Dinvsqrt_mul_Dsqrt hπ⟩, rfl⟩

/-- `(D^{1/2})⁻¹ = D^{-1/2}` in the matrix-inverse sense. -/
lemma Dsqrt_inv_eq_Dinvsqrt {pi_dist : V → ℝ} (hπ : ∀ v, 0 < pi_dist v) :
    (Dsqrt pi_dist : Matrix V V ℝ)⁻¹ = Dinvsqrt pi_dist :=
  Matrix.inv_eq_left_inv (Dinvsqrt_mul_Dsqrt hπ)

/-! ## 3. The conjugated matrix `L_std = D^{1/2} L D^{-1/2}` -/

/-- The transported matrix `L_std := D^{1/2} L D^{-1/2}`.  When `L` is
    π-symmetric, this is `IsHermitian` (under the standard inner product),
    so Mathlib's continuous functional calculus applies. -/
def toStdMatrix (L : Matrix V V ℝ) (pi_dist : V → ℝ) : Matrix V V ℝ :=
  Dsqrt pi_dist * L * Dinvsqrt pi_dist

/-- Entry-wise formula for `toStdMatrix L pi_dist`:
    `(L_std)_{x,y} = √(pi_dist x) · L_{x,y} / √(pi_dist y)`. -/
lemma toStdMatrix_apply (L : Matrix V V ℝ) (pi_dist : V → ℝ) (x y : V) :
    toStdMatrix L pi_dist x y =
    Real.sqrt (pi_dist x) * L x y * (1 / Real.sqrt (pi_dist y)) := by
  unfold toStdMatrix Dsqrt Dinvsqrt
  -- Use left-associativity: `(Dsqrt * L) * Dinvsqrt`.
  -- Apply `Matrix.mul_diagonal` (right diag) then `Matrix.diagonal_mul` (left diag).
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- `toStdMatrix L pi_dist` is symmetric (`IsHermitian` over ℝ) when `L`
    is π-symmetric.

    **Proof.** Entry-wise: `(L_std)_{x,y} = √π_x · L_{x,y} / √π_y` and
    `(L_std)_{y,x} = √π_y · L_{y,x} / √π_x`.  Their equality is the
    detailed-balance relation `π_x · L_{x,y} = π_y · L_{y,x}` divided by
    `√(π_x · π_y)`, which is exactly the content of
    `IsSymmPi.detailedBalance`. -/
theorem toStdMatrix_isHermitian {L : Matrix V V ℝ} {pi_dist : V → ℝ}
    {hπ : ∀ v, 0 < pi_dist v} (hL : IsSymmPi L pi_dist hπ) :
    (toStdMatrix L pi_dist).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro x y
  -- `star = id` over ℝ, so the goal reduces to showing
  -- `toStdMatrix L pi_dist y x = toStdMatrix L pi_dist x y`.
  show star (toStdMatrix L pi_dist y x) = toStdMatrix L pi_dist x y
  rw [show star (toStdMatrix L pi_dist y x) = toStdMatrix L pi_dist y x from rfl]
  rw [toStdMatrix_apply, toStdMatrix_apply]
  -- Goal: √π_y · L y x · (1/√π_x) = √π_x · L x y · (1/√π_y).
  have hπx_ne : Real.sqrt (pi_dist x) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (hπ x))
  have hπy_ne : Real.sqrt (pi_dist y) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (hπ y))
  have hπxx : Real.sqrt (pi_dist x) * Real.sqrt (pi_dist x) = pi_dist x :=
    Real.mul_self_sqrt (le_of_lt (hπ x))
  have hπyy : Real.sqrt (pi_dist y) * Real.sqrt (pi_dist y) = pi_dist y :=
    Real.mul_self_sqrt (le_of_lt (hπ y))
  have hdb := hL.detailedBalance x y
  -- `mul_one_div : a * (1/b) = a / b`.  By left-associativity
  -- `√π_y * L y x * (1/√π_x) = (√π_y * L y x) * (1/√π_x) = (√π_y * L y x) / √π_x`.
  rw [mul_one_div, mul_one_div]
  -- Goal: (√π_y · L y x) / √π_x = (√π_x · L x y) / √π_y.
  rw [div_eq_div_iff hπx_ne hπy_ne]
  -- Goal now: √π_y · L y x · √π_y = √π_x · L x y · √π_x.
  have h1 : Real.sqrt (pi_dist y) * L y x * Real.sqrt (pi_dist y) =
            pi_dist y * L y x := by
    have hassoc : Real.sqrt (pi_dist y) * L y x * Real.sqrt (pi_dist y) =
                  (Real.sqrt (pi_dist y) * Real.sqrt (pi_dist y)) * L y x := by ring
    rw [hassoc, hπyy]
  have h2 : Real.sqrt (pi_dist x) * L x y * Real.sqrt (pi_dist x) =
            pi_dist x * L x y := by
    have hassoc : Real.sqrt (pi_dist x) * L x y * Real.sqrt (pi_dist x) =
                  (Real.sqrt (pi_dist x) * Real.sqrt (pi_dist x)) * L x y := by ring
    rw [hassoc, hπxx]
  rw [h1, h2]
  linarith

/-! ## 4. Scalar-multiplication compatibility -/

/-- `toStdMatrix (c • L) pi_dist = c • toStdMatrix L pi_dist`. -/
theorem toStdMatrix_smul (L : Matrix V V ℝ) (pi_dist : V → ℝ) (c : ℝ) :
    toStdMatrix (c • L) pi_dist = c • toStdMatrix L pi_dist := by
  unfold toStdMatrix
  -- `Dsqrt * (c • L) = c • (Dsqrt * L)` (by `Matrix.mul_smul`),
  -- then `(c • X) * Dinvsqrt = c • (X * Dinvsqrt)` (by `Matrix.smul_mul`).
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- `t • toStdMatrix L pi_dist = D^{1/2} * (t • L) * D^{-1/2}`. -/
lemma smul_toStdMatrix_eq_conj (L : Matrix V V ℝ) (pi_dist : V → ℝ) (t : ℝ) :
    t • toStdMatrix L pi_dist =
    Dsqrt pi_dist * (t • L) * Dinvsqrt pi_dist := by
  unfold toStdMatrix
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-! ## 5. The constructive sectorial functional calculus -/

/-- The constructive `ψ(sL)` operator for π-self-adjoint `L`.

    Defined by transport: conjugate `L` to the standard inner product
    via `D^{1/2}`, apply Mathlib's continuous functional calculus
    (`cfc`), then transport back via `D^{-1/2}`.

    `funCalculus_SA L π hπ hL_sa ψ s := D^{-1/2} · cfc (ψ ∘ (s • ·)) L_std · D^{1/2}`.

    This replaces the formerly-axiomatised `SectorialFunctionalCalculus`
    in `@c:\Lean4 Projects\src\SGC\Bridge\CanonicalWavelet.lean` for the
    self-adjoint case (`IsSymmPi L pi_dist hπ`). -/
def funCalculus_SA (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (_hL_sa : IsSymmPi L pi_dist hπ)
    (f : ℝ → ℝ) (s : ℝ) : Matrix V V ℝ :=
  Dinvsqrt pi_dist * cfc (fun x => f (s * x)) (toStdMatrix L pi_dist) *
    Dsqrt pi_dist

/-! ### 5a. Conjugation identity for the matrix exponential -/

/-- `exp ℝ (t • L_std) = D^{1/2} · exp ℝ (t • L) · D^{-1/2}`.

    **Proof.** `t • L_std = D^{1/2} · (t • L) · D^{-1/2}` by
    `smul_toStdMatrix_eq_conj`.  Then `Matrix.exp_conj` (the conjugation
    identity for matrix `exp` under similarity) gives the result, using
    `Dsqrt_isUnit` and `Dsqrt_inv_eq_Dinvsqrt`. -/
lemma exp_smul_toStdMatrix
    (L : Matrix V V ℝ) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (t : ℝ) :
    NormedSpace.exp ℝ (t • toStdMatrix L pi_dist) =
    Dsqrt pi_dist * NormedSpace.exp ℝ (t • L) * Dinvsqrt pi_dist := by
  rw [smul_toStdMatrix_eq_conj]
  -- Express `Dinvsqrt = (Dsqrt)⁻¹` and apply `Matrix.exp_conj`.
  conv_lhs => rw [show (Dinvsqrt pi_dist : Matrix V V ℝ) =
                     (Dsqrt pi_dist : Matrix V V ℝ)⁻¹ from
                   (Dsqrt_inv_eq_Dinvsqrt hπ).symm]
  rw [Matrix.exp_conj ℝ (Dsqrt pi_dist) (t • L) (Dsqrt_isUnit hπ)]
  rw [Dsqrt_inv_eq_Dinvsqrt hπ]

/-- A direct rearrangement: `D^{1/2} · exp ℝ (t • L) = exp ℝ (t • L_std) · D^{1/2}`. -/
lemma Dsqrt_mul_exp_smul
    (L : Matrix V V ℝ) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (t : ℝ) :
    Dsqrt pi_dist * NormedSpace.exp ℝ (t • L) =
    NormedSpace.exp ℝ (t • toStdMatrix L pi_dist) * Dsqrt pi_dist := by
  rw [exp_smul_toStdMatrix L pi_dist hπ t]
  rw [Matrix.mul_assoc]
  rw [Dinvsqrt_mul_Dsqrt hπ]
  rw [Matrix.mul_one]

/-- A direct rearrangement: `D^{-1/2} · exp ℝ (t • L_std) = exp ℝ (t • L) · D^{-1/2}`. -/
lemma Dinvsqrt_mul_exp_smul_toStdMatrix
    (L : Matrix V V ℝ) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (t : ℝ) :
    Dinvsqrt pi_dist * NormedSpace.exp ℝ (t • toStdMatrix L pi_dist) =
    NormedSpace.exp ℝ (t • L) * Dinvsqrt pi_dist := by
  rw [exp_smul_toStdMatrix L pi_dist hπ t]
  -- Left-associate everything via `← Matrix.mul_assoc`, then cancel `Dinvsqrt * Dsqrt = 1`.
  simp only [← Matrix.mul_assoc]
  rw [Dinvsqrt_mul_Dsqrt hπ, Matrix.one_mul]

/-! ### 5b. The semigroup commutation theorem -/

/-- **Theorem (formerly `functional_calculus_commutes_semigroup` axiom)**:
    For π-self-adjoint `L`, the constructive `ψ(sL)` commutes with the
    heat semigroup `e^{tL}`.

    **Proof.**  The two operators are conjugate-by-`D^{1/2}` of
    `cfc (ψ ∘ (s•·)) L_std` and `exp(t • L_std)` respectively.  Their
    standard-basis counterparts commute by `Commute.cfc_real` (both are
    functions of the same self-adjoint matrix `L_std`).  Conjugation
    preserves commutation, so the originals commute.  Algebraically:
    push the exponential through the `D^{1/2}` factor using
    `Dsqrt_mul_exp_smul`, swap the inner `cfc` and `exp`, then push back
    out using `Dinvsqrt_mul_exp_smul_toStdMatrix`. -/
theorem funCalculus_SA_commute_HeatKernel
    (L : Matrix V V ℝ) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (hL_sa : IsSymmPi L pi_dist hπ) (f : ℝ → ℝ) (s t : ℝ) :
    funCalculus_SA L pi_dist hπ hL_sa f s * NormedSpace.exp ℝ (t • L) =
    NormedSpace.exp ℝ (t • L) * funCalculus_SA L pi_dist hπ hL_sa f s := by
  unfold funCalculus_SA
  -- Standard-basis commutation: `cfc f L_std` and `exp(t • L_std)` commute.
  have hC : Commute (toStdMatrix L pi_dist)
                    (NormedSpace.exp ℝ (t • toStdMatrix L pi_dist)) :=
    Commute.exp_right ℝ ((Commute.refl _).smul_right t)
  have hCcfc : Commute (cfc (fun x => f (s * x)) (toStdMatrix L pi_dist))
                       (NormedSpace.exp ℝ (t • toStdMatrix L pi_dist)) :=
    Commute.cfc_real hC _
  -- Calc chain.  Each `simp only [Matrix.mul_assoc]` step canonicalises
  -- associativity to right-associated form, then a targeted `rw` consumes
  -- one of the conjugation/commutation identities.
  calc Dinvsqrt pi_dist * cfc (fun x => f (s * x)) (toStdMatrix L pi_dist) *
       Dsqrt pi_dist * NormedSpace.exp ℝ (t • L)
      _ = Dinvsqrt pi_dist * cfc (fun x => f (s * x)) (toStdMatrix L pi_dist) *
          (Dsqrt pi_dist * NormedSpace.exp ℝ (t • L)) := by
            simp only [Matrix.mul_assoc]
      _ = Dinvsqrt pi_dist * cfc (fun x => f (s * x)) (toStdMatrix L pi_dist) *
          (NormedSpace.exp ℝ (t • toStdMatrix L pi_dist) * Dsqrt pi_dist) := by
            rw [Dsqrt_mul_exp_smul L pi_dist hπ t]
      _ = Dinvsqrt pi_dist *
          (cfc (fun x => f (s * x)) (toStdMatrix L pi_dist) *
           NormedSpace.exp ℝ (t • toStdMatrix L pi_dist)) *
          Dsqrt pi_dist := by
            simp only [Matrix.mul_assoc]
      _ = Dinvsqrt pi_dist *
          (NormedSpace.exp ℝ (t • toStdMatrix L pi_dist) *
           cfc (fun x => f (s * x)) (toStdMatrix L pi_dist)) *
          Dsqrt pi_dist := by rw [hCcfc.eq]
      _ = Dinvsqrt pi_dist * NormedSpace.exp ℝ (t • toStdMatrix L pi_dist) *
          cfc (fun x => f (s * x)) (toStdMatrix L pi_dist) * Dsqrt pi_dist := by
            simp only [Matrix.mul_assoc]
      _ = NormedSpace.exp ℝ (t • L) * Dinvsqrt pi_dist *
          cfc (fun x => f (s * x)) (toStdMatrix L pi_dist) * Dsqrt pi_dist := by
            rw [Dinvsqrt_mul_exp_smul_toStdMatrix L pi_dist hπ t]
      _ = NormedSpace.exp ℝ (t • L) * (Dinvsqrt pi_dist *
          cfc (fun x => f (s * x)) (toStdMatrix L pi_dist) * Dsqrt pi_dist) := by
            simp only [Matrix.mul_assoc]

/-! ### 5c. The scaling theorem -/

/-- **Theorem (formerly `functional_calculus_scaling` axiom)**:
    For π-self-adjoint `L` and continuous `f`, the constructive
    `ψ((cs)L) = ψ(s(cL))`.

    **Note on hypothesis**: the original axiom did not require any
    continuity hypothesis on `f`, but Mathlib's `cfc_comp_const_mul`
    requires `ContinuousOn f (image)`.  Continuity of `f` on all of
    `ℝ` is sufficient and matches the BandPassFilter setting (where
    `f = psi.func` is a smooth scalar profile). -/
theorem funCalculus_SA_scaling
    (L : Matrix V V ℝ) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (hL_sa : IsSymmPi L pi_dist hπ) (f : ℝ → ℝ) (hf : Continuous f) (s c : ℝ) :
    funCalculus_SA L pi_dist hπ hL_sa f (c * s) =
    funCalculus_SA (c • L) pi_dist hπ (hL_sa.smul c) f s := by
  unfold funCalculus_SA
  -- `toStdMatrix (c • L) = c • toStdMatrix L`.
  rw [toStdMatrix_smul]
  -- Reduce to a CFC identity; the wrapping `Dinvsqrt * · * Dsqrt` is the same on both sides.
  congr 1
  congr 1
  -- Now: `cfc (fun x => f ((c*s)*x)) L_std = cfc (fun x => f (s*x)) (c • L_std)`.
  -- Rewrite LHS to make it match `cfc_comp_const_mul`:
  --   `(fun x => f ((c*s)*x)) = (fun y => f (s*y)) ∘ (c * ·)`.
  rw [show (fun x => f (c * s * x)) = (fun y => f (s * y)) ∘ (fun x => c * x) from by
        ext x; show f (c * s * x) = f (s * (c * x)); congr 1; ring]
  -- Apply `cfc_comp_const_mul` with continuity coming from `Continuous.comp`.
  exact cfc_comp_const_mul c (fun y => f (s * y)) (toStdMatrix L pi_dist)
    (by fun_prop) (toStdMatrix_isHermitian hL_sa).isSelfAdjoint

end SGC.Spectral.WeightedHermitian

end
