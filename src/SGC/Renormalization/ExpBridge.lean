/-
Copyright (c) 2026 Jason Shroyer. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import SGC.Renormalization.MeasureReentry

/-!
# The Exponential Bridge: continuous-time closure at zero defect

The first genuine `Matrix`-exponential result of the measure-reentry
program: **rectangular exponential intertwining**. If a fine operator, a
macro operator, and a lift satisfy the algebraic intertwining `L·K = K·Q`,
then their true continuous-time semigroups intertwine for all time:

`exp(L)·K = K·exp(Q)`, hence `exp(tL)·K = K·exp(tQ)` for every `t`.

Composed with the measure-reentry theory: **zero closure commutator gives
eternal exact closure of the genuine CTMC semigroup** — the `ε = 0` pole
of the continuous-time bridge, now kernel-proven (previously only the
discrete-power and Euler versions existed).

## Proof route

`exp` is the summable power series; multiplication by a fixed rectangular
matrix on either side is a continuous linear map (finite dimensions), so
it passes through the `tsum`; termwise, power intertwining
(`L^n·K = K·Q^n`) is induction from the hypothesis.

## The ε > 0 design target (NOT proven here; recorded)

The full continuous-time Duhamel identity
`exp(tL)·K − K·exp(tQ) = ∫₀ᵗ exp((t−s)L)·𝒞·exp(sQ) ds`
needs: interval integrals of matrix-valued curves, differentiation of
`s ↦ exp((t−s)L)·M·exp(sQ)` (`NormedSpace.exp` has `hasDerivAt` API), and
FTC — all present in Mathlib but a full assembly sprint. Until then the
Euler bridge (`PhysicalHorizon`) carries the quantitative ε > 0 story in
physical time, and this module carries the exact ε = 0 endpoint.
-/

namespace SGC.Renormalization.ExpBridge

open Matrix NormedSpace
open SGC SGC.Thermodynamics SGC.Renormalization.MeasureReentry

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Right multiplication by a fixed rectangular matrix, as a continuous
linear map (finite dimensions). -/
noncomputable def mulRightCLM (K : Matrix V W ℝ) :
    Matrix V V ℝ →L[ℝ] Matrix V W ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M * K
      map_add' := fun M N => Matrix.add_mul M N K
      map_smul' := fun c M => by simp [Matrix.smul_mul] }

/-- Left multiplication by a fixed rectangular matrix, as a continuous
linear map (finite dimensions). -/
noncomputable def mulLeftCLM (K : Matrix V W ℝ) :
    Matrix W W ℝ →L[ℝ] Matrix V W ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => K * M
      map_add' := fun M N => Matrix.mul_add K M N
      map_smul' := fun c M => by simp [Matrix.mul_smul] }

/-- **Rectangular exponential intertwining**: algebraic intertwining
propagates through the genuine matrix exponential. -/
theorem exp_intertwine (L : Matrix V V ℝ) (Q : Matrix W W ℝ)
    (K : Matrix V W ℝ) (h : L * K = K * Q) :
    exp ℝ L * K = K * exp ℝ Q := by
  have hpow : ∀ n : ℕ, L ^ n * K = K * Q ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc L ^ (n + 1) * K = L ^ n * (L * K) := by
            rw [pow_succ, Matrix.mul_assoc]
        _ = L ^ n * (K * Q) := by rw [h]
        _ = (L ^ n * K) * Q := by rw [Matrix.mul_assoc]
        _ = K * Q ^ n * Q := by rw [ih]
        _ = K * Q ^ (n + 1) := by rw [Matrix.mul_assoc, ← pow_succ]
  have hsumL : Summable fun n : ℕ => (n.factorial : ℝ)⁻¹ • L ^ n :=
    expSeries_summable' (𝕂 := ℝ) L
  have hsumQ : Summable fun n : ℕ => (n.factorial : ℝ)⁻¹ • Q ^ n :=
    expSeries_summable' (𝕂 := ℝ) Q
  rw [exp_eq_tsum, exp_eq_tsum]
  have hstep1 : (∑' n : ℕ, (n.factorial : ℝ)⁻¹ • L ^ n) * K
      = ∑' n : ℕ, (n.factorial : ℝ)⁻¹ • (L ^ n * K) := by
    have := (hsumL.hasSum.mapL (mulRightCLM K)).tsum_eq
    simp only [mulRightCLM, LinearMap.coe_toContinuousLinearMap',
      LinearMap.coe_mk, AddHom.coe_mk] at this
    rw [← this]
    congr 1
    ext n
    rw [Matrix.smul_mul]
  have hstep2 : (∑' n : ℕ, (n.factorial : ℝ)⁻¹ • (K * Q ^ n))
      = K * ∑' n : ℕ, (n.factorial : ℝ)⁻¹ • Q ^ n := by
    have := (hsumQ.hasSum.mapL (mulLeftCLM K)).tsum_eq
    simp only [mulLeftCLM, LinearMap.coe_toContinuousLinearMap',
      LinearMap.coe_mk, AddHom.coe_mk] at this
    rw [← this]
    congr 1
    ext n
    rw [Matrix.mul_smul]
  rw [hstep1]
  simp_rw [hpow]
  exact hstep2

/-- **CONTINUOUS-TIME ETERNAL CLOSURE AT ZERO DEFECT.** If the closure
commutator vanishes, the genuine CTMC semigroup of the fine generator
intertwines with the semigroup of the canonical macro-generator at every
physical time `t`: coarse observables evolved by `exp(tL)` agree exactly
with the macro-law's own evolution, forever. The `ε = 0` pole of the
continuous-time bridge. -/
theorem exp_closure_of_zero_commutator (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ)
    (h : closureCommutator L P pi_dist = 0) (t : ℝ) :
    exp ℝ (t • L) * lift_matrix P
      = lift_matrix P * exp ℝ (t • CoarseGenerator L P pi_dist) := by
  have hLK : L * lift_matrix P
      = lift_matrix P * CoarseGenerator L P pi_dist := by
    have := sub_eq_zero.mp h
    exact this
  refine exp_intertwine (t • L) (t • CoarseGenerator L P pi_dist)
    (lift_matrix P) ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, hLK]

end SGC.Renormalization.ExpBridge
