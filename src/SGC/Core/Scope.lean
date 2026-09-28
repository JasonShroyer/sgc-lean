/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.InformationGeometry.MarkovPathMixing
import SGC.InformationGeometry.MarkovPathInitialLaw
import SGC.InformationGeometry.ContinuousTimeKernel

/-!
# `SGC.Scope`: a certified evaluation scope

A scope is a fine discrete-time kernel, a partition (the coarse projection),
and a strictly positive stationary law. The defect is computed, never stored:
it is the canonical measure-reentry defect `MeasureReentry.defectSq`. Exactness
is a derived proposition, equivalent to zero defect.

## What is proved and what is not

* `defectSq_eq_zero_iff` — zero defect iff exact strong lumpability.
* `fisherLoss_le` — for a block-pair tilt with row energy at most `Bmax`, the
  path Fisher information lost by the macro-observer over `T` steps is at most
  `T² · Bmax · 𝔇_π²` (proved, `MarkovPathFisher`).
* `informationHorizon` / `fisherLoss_le_of_le_horizon` — the proved horizon:
  for `T ≤ √(ε / (Bmax · 𝔇_π²))` the loss is at most `ε`.
* `fisherLoss_le_mixing` — under the `L²(π)` contraction hypothesis
  `MixingContraction` with `σ < 1` (reversibility not assumed), the loss is at
  most `T · Bmax · 𝔇_π² · (1+σ)/(1-σ)`; `fisherLoss_le_of_le_mixingHorizon`
  gives the corresponding horizon `ε / mixingLossRate`. That `MixingContraction`
  holds with some `σ < 1` for positive kernels is standard but assumed here.

These horizons bound information about a parameter direction lost by coarse
observation. They are not prediction-error horizons; those are
`KernelHorizon` / `PhysicalHorizon` statements about `‖Tⁿ K − K Qⁿ‖`.
-/

noncomputable section

namespace SGC.Core

open Matrix SGC.InformationGeometry

/-- A certified evaluation scope. -/
structure Scope (V : Type*) [Fintype V] [DecidableEq V] where
  kernel : Matrix V V ℝ
  partition : Partition V
  pi : V → ℝ
  kernel_pos : ∀ x y, 0 < kernel x y
  kernel_row : ∀ x, ∑ y, kernel x y = 1
  pi_pos : ∀ x, 0 < pi x
  pi_stationary : pi ᵥ* kernel = pi

namespace Scope

variable {V : Type*} [Fintype V] [DecidableEq V] (S : Scope V)

/-- The canonical measure-reentry defect `𝔇_π²` of the scope. -/
def defectSq : ℝ := SGC.Renormalization.MeasureReentry.defectSq S.kernel S.partition S.pi

/-- The scope is exact when the partition is strongly lumpable for the kernel. -/
def IsExact : Prop := IsStronglyLumpable S.kernel S.partition

theorem defectSq_nonneg : 0 ≤ S.defectSq :=
  SGC.Renormalization.MeasureReentry.defectSq_nonneg _ _ (fun x => (S.pi_pos x).le)

theorem defectSq_eq_zero_iff : S.defectSq = 0 ↔ S.IsExact :=
  SGC.Renormalization.MeasureReentry.defectSq_eq_zero_iff_stronglyLumpable _ _ S.pi_pos

/-- Fisher information lost over `T` steps by the macro-observer, for a
block-pair tilt `b`. -/
def fisherLoss (b : S.partition.Quot → S.partition.Quot → ℝ) (T : ℕ) : ℝ :=
  ScoreProjection.fineFisher (MarkovPathFisher.pathProb S.kernel S.pi T)
      (MarkovPathFisher.pathDeriv S.kernel S.partition.quot_map S.pi b T)
    - ScoreProjection.coarseFisher (MarkovPathFisher.macroPath S.partition.quot_map T)
      (MarkovPathFisher.pathProb S.kernel S.pi T)
      (MarkovPathFisher.pathDeriv S.kernel S.partition.quot_map S.pi b T)

theorem fisherLoss_le (b : S.partition.Quot → S.partition.Quot → ℝ) {Bmax : ℝ}
    (hB : ∀ A, ∑ C, b A C ^ 2 ≤ Bmax) (T : ℕ) :
    S.fisherLoss b T ≤ (T : ℝ) ^ 2 * (Bmax * S.defectSq) :=
  MarkovPathFisher.fisherLoss_markov_path_le_measureReentry S.kernel S.pi T S.partition
    S.kernel_pos S.kernel_row S.pi_pos S.pi_stationary b hB

/-- An exact scope loses no information about any block-pair tilt. -/
theorem fisherLoss_eq_zero_of_exact (hex : S.IsExact)
    (b : S.partition.Quot → S.partition.Quot → ℝ) (T : ℕ) : S.fisherLoss b T ≤ 0 := by
  have hB : ∀ A, ∑ C, b A C ^ 2 ≤ ∑ A', ∑ C, b A' C ^ 2 := fun A =>
    Finset.single_le_sum (f := fun A => ∑ C, b A C ^ 2)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ A)
  have h := S.fisherLoss_le b hB T
  rwa [(S.defectSq_eq_zero_iff).mpr hex, mul_zero, mul_zero] at h

/-- The proved information horizon `√(ε / (Bmax · 𝔇_π²))`. -/
def informationHorizon (ε Bmax : ℝ) : ℝ := Real.sqrt (ε / (Bmax * S.defectSq))

theorem fisherLoss_le_of_le_horizon (b : S.partition.Quot → S.partition.Quot → ℝ)
    {Bmax ε : ℝ} (hB : ∀ A, ∑ C, b A C ^ 2 ≤ Bmax) (hBpos : 0 < Bmax)
    (hD : 0 < S.defectSq) (hε : 0 ≤ ε) (T : ℕ)
    (hT : (T : ℝ) ≤ S.informationHorizon ε Bmax) : S.fisherLoss b T ≤ ε := by
  have hc : 0 < Bmax * S.defectSq := mul_pos hBpos hD
  have hsq : (T : ℝ) ^ 2 ≤ ε / (Bmax * S.defectSq) := by
    have := pow_le_pow_left₀ (Nat.cast_nonneg T) hT 2
    rwa [informationHorizon, Real.sq_sqrt (div_nonneg hε hc.le)] at this
  have h2 : (T : ℝ) ^ 2 * (Bmax * S.defectSq) ≤ ε := by
    rwa [le_div_iff₀ hc] at hsq
  exact (S.fisherLoss_le b hB T).trans h2

/-- Linear-in-`T` loss rate under mixing with `L²(π)` contraction `σ` on
mean-zero functions. -/
def mixingLossRate (Bmax σ : ℝ) : ℝ := Bmax * S.defectSq * (1 + σ) / (1 - σ)

/-- **Linear information-loss bound under mixing** (proved,
`MarkovPathMixing`): `loss(T) ≤ T · mixingLossRate`. -/
theorem fisherLoss_le_mixing (b : S.partition.Quot → S.partition.Quot → ℝ) {Bmax σ : ℝ}
    (hB : ∀ A, ∑ C, b A C ^ 2 ≤ Bmax)
    (hσ : MarkovPathMixing.MixingContraction S.kernel S.pi σ) (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    (T : ℕ) : S.fisherLoss b T ≤ (T : ℝ) * S.mixingLossRate Bmax σ := by
  have h := MarkovPathMixing.fisherLoss_markov_path_le_mixing_measureReentry S.kernel S.pi T
    S.partition S.kernel_pos S.kernel_row S.pi_pos S.pi_stationary hσ hσ0 hσ1 b hB
  have heq : (T : ℝ) * ((1 + σ) / (1 - σ)) * (Bmax * S.defectSq)
      = (T : ℝ) * S.mixingLossRate Bmax σ := by
    unfold mixingLossRate
    ring
  exact h.trans (le_of_eq heq)

/-- **Unconditional linear bound.** Every scope (with `π` a probability vector)
has a Doeblin constant `c ∈ (0,1]` such that, for every block-pair tilt,
`loss(T) ≤ T · (2 - c)/c · Bmax · 𝔇_π²`. No mixing hypothesis is assumed. -/
theorem exists_linear_fisherLoss_bound [Nonempty V] (hsum : ∑ x, S.pi x = 1) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (b : S.partition.Quot → S.partition.Quot → ℝ) (Bmax : ℝ),
      (∀ A, ∑ C, b A C ^ 2 ≤ Bmax) → ∀ T : ℕ,
        S.fisherLoss b T ≤ (T : ℝ) * ((2 - c) / c) * (Bmax * S.defectSq) := by
  obtain ⟨c, hc0, hc1, hmin⟩ := MarkovPathMixing.exists_doeblin S.kernel S.kernel_pos
    S.kernel_row (fun x => (S.pi_pos x).le) hsum
  exact ⟨c, hc0, hc1, fun b Bmax hB T =>
    MarkovPathMixing.fisherLoss_markov_path_le_doeblin S.kernel S.pi T S.partition S.kernel_pos
      S.kernel_row S.pi_pos hsum S.pi_stationary hc0 hc1 hmin b hB⟩

/-- The mixing information horizon `ε / mixingLossRate`: within it the loss is
at most `ε`. -/
def mixingHorizon (ε Bmax σ : ℝ) : ℝ := ε / S.mixingLossRate Bmax σ

theorem fisherLoss_le_of_le_mixingHorizon (b : S.partition.Quot → S.partition.Quot → ℝ)
    {Bmax σ ε : ℝ} (hB : ∀ A, ∑ C, b A C ^ 2 ≤ Bmax)
    (hσ : MarkovPathMixing.MixingContraction S.kernel S.pi σ) (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    (hrate : 0 < S.mixingLossRate Bmax σ) (T : ℕ)
    (hT : (T : ℝ) ≤ S.mixingHorizon ε Bmax σ) : S.fisherLoss b T ≤ ε := by
  have h := S.fisherLoss_le_mixing b hB hσ hσ0 hσ1 T
  unfold mixingHorizon at hT
  rw [le_div_iff₀ hrate] at hT
  exact h.trans hT

/-! ### Parameter-dependent start -/

/-- Fisher loss when the chain starts from `μ` with initial score `s₀`. -/
def fisherLossFrom (μ : V → ℝ) (s₀ : V → ℝ) (b : S.partition.Quot → S.partition.Quot → ℝ)
    (T : ℕ) : ℝ :=
  ScoreProjection.fineFisher (MarkovPathFisher.pathProb S.kernel μ T)
      (MarkovPathInitialLaw.pathDerivInit S.kernel S.partition.quot_map μ b s₀ T)
    - ScoreProjection.coarseFisher (MarkovPathFisher.macroPath S.partition.quot_map T)
      (MarkovPathFisher.pathProb S.kernel μ T)
      (MarkovPathInitialLaw.pathDerivInit S.kernel S.partition.quot_map μ b s₀ T)

/-- The initial-law defect `V₀` of a start `(μ, s₀)`: within-block variance of the initial score. -/
def initialDefect (μ s₀ : V → ℝ) : ℝ :=
  MarkovPathInitialLaw.initialDefect S.partition.quot_map μ s₀

/-- A start is feasible for tolerance `ε` when its initial-law defect alone does not
exhaust the budget: `2 V₀ < ε`. Otherwise no horizon exists (the offset does not decay). -/
def initiallyFeasible (μ s₀ : V → ℝ) (ε : ℝ) : Prop := 2 * S.initialDefect μ s₀ < ε

/-- **Linear bound from a dominated start.** -/
theorem fisherLossFrom_le_mixing [Nonempty V] (μ s₀ : V → ℝ) (hμ : ∀ x, 0 < μ x) {κ : ℝ}
    (hdom : ∀ x, μ x ≤ κ * S.pi x) (b : S.partition.Quot → S.partition.Quot → ℝ) {Bmax σ : ℝ}
    (hB : ∀ A, ∑ C, b A C ^ 2 ≤ Bmax)
    (hσ : MarkovPathMixing.MixingContraction S.kernel S.pi σ) (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    (T : ℕ) :
    S.fisherLossFrom μ s₀ b T
      ≤ 2 * κ * (T : ℝ) * S.mixingLossRate Bmax σ + 2 * S.initialDefect μ s₀ := by
  have h := MarkovPathInitialLaw.fisherLoss_initialLaw_le_mixing S.kernel S.partition.quot_map S.pi μ
    b s₀ T S.kernel_pos S.kernel_row S.pi_pos S.pi_stationary hμ hdom hσ hσ0 hσ1 hB
  unfold fisherLossFrom
  refine h.trans (le_of_eq ?_)
  rw [MarkovPathFisher.defectSq_eq_measureReentry S.kernel S.pi S.partition S.pi_pos]
  unfold mixingLossRate defectSq initialDefect
  ring

/-- Horizon from a dominated start: `(ε − 2V₀) / (2 κ · mixingLossRate)`; meaningful only
when `initiallyFeasible`. -/
def nonstationaryHorizon (μ s₀ : V → ℝ) (ε κ Bmax σ : ℝ) : ℝ :=
  (ε - 2 * S.initialDefect μ s₀) / (2 * κ * S.mixingLossRate Bmax σ)

theorem fisherLossFrom_le_of_le_horizon [Nonempty V] (μ s₀ : V → ℝ) (hμ : ∀ x, 0 < μ x) {κ : ℝ}
    (hdom : ∀ x, μ x ≤ κ * S.pi x) (b : S.partition.Quot → S.partition.Quot → ℝ) {Bmax σ ε : ℝ}
    (hB : ∀ A, ∑ C, b A C ^ 2 ≤ Bmax)
    (hσ : MarkovPathMixing.MixingContraction S.kernel S.pi σ) (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    (hrate : 0 < 2 * κ * S.mixingLossRate Bmax σ) (T : ℕ)
    (hT : (T : ℝ) ≤ S.nonstationaryHorizon μ s₀ ε κ Bmax σ) : S.fisherLossFrom μ s₀ b T ≤ ε := by
  have h := S.fisherLossFrom_le_mixing μ s₀ hμ hdom b hB hσ hσ0 hσ1 T
  unfold nonstationaryHorizon at hT
  rw [le_div_iff₀ hrate] at hT
  linarith

/-! ### Scopes from continuous-time generators -/

open scoped Matrix.Norms.Operator in
/-- **A scope from a generator.** For a finite-state generator `L` with positive
off-diagonal rates, a step `h > 0`, a partition, and a positive law `π` with
`π L = 0`, the sampled semigroup `exp (h • L)` is a positive stochastic kernel
with stationary law `π`; every path-space theorem of this file applies to it. -/
def ofGenerator (L : Matrix V V ℝ) (hL : InformationGeometry.ContinuousTimeKernel.IsGenerator L)
    (hoff : ∀ x y, x ≠ y → 0 < L x y) {h : ℝ} (hh : 0 < h) (Part : Partition V) (π : V → ℝ)
    (hπ : ∀ x, 0 < π x) (hπL : π ᵥ* L = 0) : Scope V where
  kernel := NormedSpace.exp ℝ (h • L)
  partition := Part
  pi := π
  kernel_pos := InformationGeometry.ContinuousTimeKernel.exp_entry_pos (h • L)
    (InformationGeometry.ContinuousTimeKernel.isGenerator_smul L hL hh.le)
    (InformationGeometry.ContinuousTimeKernel.offdiag_pos_smul L hoff hh)
  kernel_row := InformationGeometry.ContinuousTimeKernel.exp_row_sum (h • L)
    (InformationGeometry.ContinuousTimeKernel.isGenerator_smul L hL hh.le).row_zero
  pi_pos := hπ
  pi_stationary := InformationGeometry.ContinuousTimeKernel.exp_stationary (h • L) (by
    rw [Matrix.vecMul_smul, hπL, smul_zero])

end Scope

end SGC.Core
