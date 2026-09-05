/-
Copyright (c) 2026 Jason Shroyer. All rights reserved.
Released under Apache 2.0 license.
-/
import SGC.Observation.DeterministicReadout

/-!
# The Composition Stack: how defects add along the ladder

T0 of the entropic-bridge program (2026-09-04 review), and the theorem
the lattice's receipts have been waiting for: a reported observational
mismatch decomposes EXACTLY into a dynamical-quotient term and an
observation-channel term. "How much of an apparent physical discrepancy
belongs to the world, and how much to the map by which the world became
data?" — answered, at the level of kernel identities.

Ladder convention (matching `DeterministicReadout`): latent dynamics
`P_X` on `X`; quotient lift `Λ_Q : Y ⇝ X` with intended quotient law
`P_Y`; observation lift `Λ_O : Z ⇝ Y` with intended reported law `P_Z`.
The composite channel is `Λ_C = Λ_O · Λ_Q : Z ⇝ X`.

## Main results

* `IsKernel.mul` — kernels compose.
* `composite_intertwining` — exact closures compose: two commuting
  squares stack into a commuting rectangle.
* **`composite_defect_identity`** — the compositional law:
  `𝒟_C = Λ_O·𝒟_Q + 𝒟_O·Λ_Q`. Defect is a Leibniz-rule quantity: the
  failure of the rectangle is the failure of the top square pushed
  through the bottom channel, plus the failure of the bottom square fed
  by the top lift.
* `composite_defect_bound` — `‖𝒟_C‖ ≤ ‖Λ_O‖·‖𝒟_Q‖ + ‖𝒟_O‖·‖Λ_Q‖`
  (norm-hypothesis form, per the review's contraction-convention
  discipline).
* `composite_defect_bound_contractive` — for stochastic lifts, in the
  L∞ operator norm: `‖𝒟_C‖ ≤ ‖𝒟_Q‖ + ‖𝒟_O‖`. Defects are additive
  currency.
* **`composite_observation_horizon`** — the receipt-level budget:
  `‖Λ_C·P_Xⁿ − P_Zⁿ·Λ_C‖ ≤ n·(‖𝒟_Q‖ + ‖𝒟_O‖)`. The two-term error
  budget, over time, for the whole world → quotient → data ladder.

## Honest scope

Deterministic-readout regime (Phase I); the norm is the L∞ operator norm
with row-stochastic contractivity — the convention is part of the
statement, not folklore. Composite compatibility (`π_C ♯ Λ_C = I`) and
stochastic channels are Phase II.
-/

namespace SGC.Observation

open Finset Matrix
open scoped NNReal

attribute [local instance] Matrix.linftyOpNormedAddCommGroup

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

/-- Row-stochastic kernels compose. -/
theorem IsKernel.mul {A : Matrix Z Y ℝ} {B : Matrix Y X ℝ}
    (hA : IsKernel A) (hB : IsKernel B) : IsKernel (A * B) where
  nonneg := by
    intro z x
    exact Finset.sum_nonneg fun y _ =>
      mul_nonneg (hA.nonneg z y) (hB.nonneg y x)
  row_sum_one := by
    intro z
    have : ∑ x, (A * B) z x = ∑ y, A z y * ∑ x, B y x := by
      simp only [Matrix.mul_apply]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun y _ => by rw [Finset.mul_sum]
    rw [this]
    simp_rw [fun y => hB.row_sum_one y]
    simpa using hA.row_sum_one z

/-- Exact closures compose: commuting squares stack. -/
theorem composite_intertwining
    {P_X : Matrix X X ℝ} {P_Y : Matrix Y Y ℝ} {P_Z : Matrix Z Z ℝ}
    {ΛQ : Matrix Y X ℝ} {ΛO : Matrix Z Y ℝ}
    (hQ : Intertwines P_X P_Y ΛQ) (hO : Intertwines P_Y P_Z ΛO) :
    Intertwines P_X P_Z (ΛO * ΛQ) := by
  unfold Intertwines at *
  calc ΛO * ΛQ * P_X = ΛO * (ΛQ * P_X) := by rw [Matrix.mul_assoc]
    _ = ΛO * (P_Y * ΛQ) := by rw [hQ]
    _ = (ΛO * P_Y) * ΛQ := by rw [Matrix.mul_assoc]
    _ = (P_Z * ΛO) * ΛQ := by rw [hO]
    _ = P_Z * (ΛO * ΛQ) := by rw [Matrix.mul_assoc]

/-- **The compositional law of defects** (the Leibniz rule of the square
calculus): `𝒟_C = Λ_O·𝒟_Q + 𝒟_O·Λ_Q`. -/
theorem composite_defect_identity
    (P_X : Matrix X X ℝ) (P_Y : Matrix Y Y ℝ) (P_Z : Matrix Z Z ℝ)
    (ΛQ : Matrix Y X ℝ) (ΛO : Matrix Z Y ℝ) :
    obsDefect P_X P_Z (ΛO * ΛQ)
      = ΛO * obsDefect P_X P_Y ΛQ + obsDefect P_Y P_Z ΛO * ΛQ := by
  unfold obsDefect
  rw [Matrix.mul_sub, Matrix.sub_mul]
  simp only [Matrix.mul_assoc]
  abel

/-- Norm form of the compositional law (contraction hypotheses explicit,
per the convention discipline). -/
theorem composite_defect_bound
    (P_X : Matrix X X ℝ) (P_Y : Matrix Y Y ℝ) (P_Z : Matrix Z Z ℝ)
    (ΛQ : Matrix Y X ℝ) (ΛO : Matrix Z Y ℝ) :
    ‖obsDefect P_X P_Z (ΛO * ΛQ)‖
      ≤ ‖ΛO‖ * ‖obsDefect P_X P_Y ΛQ‖
        + ‖obsDefect P_Y P_Z ΛO‖ * ‖ΛQ‖ := by
  rw [composite_defect_identity]
  calc ‖ΛO * obsDefect P_X P_Y ΛQ + obsDefect P_Y P_Z ΛO * ΛQ‖
      ≤ ‖ΛO * obsDefect P_X P_Y ΛQ‖ + ‖obsDefect P_Y P_Z ΛO * ΛQ‖ :=
        norm_add_le _ _
    _ ≤ ‖ΛO‖ * ‖obsDefect P_X P_Y ΛQ‖
        + ‖obsDefect P_Y P_Z ΛO‖ * ‖ΛQ‖ := by
        exact add_le_add (Matrix.linfty_opNorm_mul _ _)
          (Matrix.linfty_opNorm_mul _ _)

/-- For stochastic lifts, defects are ADDITIVE CURRENCY:
`‖𝒟_C‖ ≤ ‖𝒟_Q‖ + ‖𝒟_O‖`. -/
theorem composite_defect_bound_contractive
    (P_X : Matrix X X ℝ) (P_Y : Matrix Y Y ℝ) (P_Z : Matrix Z Z ℝ)
    {ΛQ : Matrix Y X ℝ} {ΛO : Matrix Z Y ℝ}
    (hΛQ : IsKernel ΛQ) (hΛO : IsKernel ΛO) :
    ‖obsDefect P_X P_Z (ΛO * ΛQ)‖
      ≤ ‖obsDefect P_X P_Y ΛQ‖ + ‖obsDefect P_Y P_Z ΛO‖ := by
  refine le_trans (composite_defect_bound P_X P_Y P_Z ΛQ ΛO) ?_
  have h1 : ‖ΛO‖ * ‖obsDefect P_X P_Y ΛQ‖ ≤ ‖obsDefect P_X P_Y ΛQ‖ := by
    calc ‖ΛO‖ * ‖obsDefect P_X P_Y ΛQ‖
        ≤ 1 * ‖obsDefect P_X P_Y ΛQ‖ :=
          mul_le_mul_of_nonneg_right (kernel_norm_le_one hΛO)
            (norm_nonneg _)
      _ = ‖obsDefect P_X P_Y ΛQ‖ := one_mul _
  have h2 : ‖obsDefect P_Y P_Z ΛO‖ * ‖ΛQ‖ ≤ ‖obsDefect P_Y P_Z ΛO‖ := by
    calc ‖obsDefect P_Y P_Z ΛO‖ * ‖ΛQ‖
        ≤ ‖obsDefect P_Y P_Z ΛO‖ * 1 :=
          mul_le_mul_of_nonneg_left (kernel_norm_le_one hΛQ)
            (norm_nonneg _)
      _ = ‖obsDefect P_Y P_Z ΛO‖ := mul_one _
  linarith

/-- **The receipt-level budget**: over `n` steps, the whole
world → quotient → data ladder's discrepancy is at most
`n·(‖𝒟_Q‖ + ‖𝒟_O‖)` — the two-term error budget, as a theorem.
A reported mismatch can arise from the dynamical quotient, from the
observation channel, or from both; the instrument must estimate and
report them separately before inventing new latent dynamics. -/
theorem composite_observation_horizon
    (P_X : Matrix X X ℝ) (P_Y : Matrix Y Y ℝ) (P_Z : Matrix Z Z ℝ)
    {ΛQ : Matrix Y X ℝ} {ΛO : Matrix Z Y ℝ}
    (hPX : IsKernel P_X) (hPZ : IsKernel P_Z)
    (hΛQ : IsKernel ΛQ) (hΛO : IsKernel ΛO) (n : ℕ) :
    ‖(ΛO * ΛQ) * P_X ^ n - P_Z ^ n * (ΛO * ΛQ)‖
      ≤ (n : ℝ) * (‖obsDefect P_X P_Y ΛQ‖ + ‖obsDefect P_Y P_Z ΛO‖) := by
  refine le_trans (observation_error_le P_X P_Z (ΛO * ΛQ) hPX hPZ n) ?_
  exact mul_le_mul_of_nonneg_left
    (composite_defect_bound_contractive P_X P_Y P_Z hΛQ hΛO)
    (Nat.cast_nonneg n)

end SGC.Observation
