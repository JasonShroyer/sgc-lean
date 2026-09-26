/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.InformationGeometry.MarkovPathFisher

/-!
# Parameter-dependent initial law: the second defect

Relaxes H4 of `MarkovPathFisher`. The chain starts from a positive law `μ`
whose `θ`-dependence contributes an *initial score* `s₀ : V → ℝ` (for
`μ_θ` this is `∂_θ log μ_θ` at the base point; here it is arbitrary data, so
the result is independent of how `μ_θ` is parameterized). The fine path
score is `s₀(X₀) + Σ_t step scores`.

## Main results

* `vecMul_pow_le_of_le` — domination: `μ ≤ κ π` entrywise implies
  `μ Pᵗ ≤ κ π` for every `t` (positivity of `P`, stationarity of `π`).
* `initialDefect` — `V₀ = Σ_A μ(A) · Var_{μ_A}(s₀)`, the within-block
  variance of the initial score: the part of the initial law's
  `θ`-dependence hidden inside blocks. Zero iff `s₀` is block-measurable.
* `fisherLoss_initialLaw_le` — **`loss(T) ≤ 2 κ T² Bmax D_π² + 2 V₀`**.

The offset `V₀` does not decay with `T`: the exact identity
`loss = E[Var(Σ_t δ(X_t) − s̃₀(X₀) | Y)]` (from `ScoreProjection.fisherLoss_eq_condVar`)
shows the observer can never recover more about `s̃₀(X₀)` than the macro-history
reveals, and the bound above does not claim she recovers any of it.
-/

noncomputable section

namespace SGC.InformationGeometry.MarkovPathInitialLaw

open Finset Matrix SGC.InformationGeometry
open SGC.InformationGeometry.MarkovPathFisher

set_option linter.unusedSectionVars false

variable {V β : Type*} [Fintype V] [DecidableEq V] [Fintype β] [DecidableEq β]

/-! ### Domination of non-stationary marginals -/

lemma vecMul_le_of_le (P : Matrix V V ℝ) (hP : ∀ x y, 0 ≤ P x y) {μ ν : V → ℝ}
    (h : ∀ x, μ x ≤ ν x) : ∀ y, (μ ᵥ* P) y ≤ (ν ᵥ* P) y := by
  intro y
  simp only [vecMul, dotProduct]
  exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_right (h x) (hP x y))

/-- `μ ≤ κ π` implies `μ Pᵗ ≤ κ π` for all `t`. -/
theorem vecMul_pow_le_of_le (P : Matrix V V ℝ) (hP : ∀ x y, 0 ≤ P x y) {π μ : V → ℝ}
    (hstat : π ᵥ* P = π) {κ : ℝ} (hdom : ∀ x, μ x ≤ κ * π x) :
    ∀ t : ℕ, ∀ x, (μ ᵥ* P ^ t) x ≤ κ * π x := by
  intro t
  induction t with
  | zero => simpa using hdom
  | succ t ih =>
    intro x
    rw [pow_succ, ← vecMul_vecMul]
    have h1 := vecMul_le_of_le P hP ih x
    have h2 : ((fun y => κ * π y) ᵥ* P) x = κ * π x := by
      have := congrFun hstat x
      simp only [vecMul, dotProduct] at this ⊢
      rw [← this, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun y _ => by ring)
    exact h1.trans (le_of_eq h2)

/-! ### Initial score and the second defect -/

variable (P : Matrix V V ℝ) (q : V → β) (π μ : V → ℝ) (b : β → β → ℝ) (s₀ : V → ℝ) (T : ℕ)

/-- Block-conditional mean of the initial score under `μ`. -/
def blockMean (A : β) : ℝ :=
  (∑ x ∈ univ.filter (fun x => q x = A), μ x * s₀ x) / ∑ x ∈ univ.filter (fun x => q x = A), μ x

/-- Within-block deviation of the initial score. -/
def tildeS (x : V) : ℝ := s₀ x - blockMean q μ s₀ (q x)

/-- **Initial-law defect** `V₀`: the `μ`-weighted within-block variance of `s₀`. -/
def initialDefect : ℝ := ∑ x, μ x * tildeS q μ s₀ x ^ 2

/-- Fine path score with the initial term. -/
def pathScoreInit (ω : Fin (T + 1) → V) : ℝ := s₀ (ω 0) + pathScore P q b T ω

/-- Derivative data `p · S` under the initial law `μ`. -/
def pathDerivInit (ω : Fin (T + 1) → V) : ℝ := pathProb P μ T ω * pathScoreInit P q b s₀ T ω

/-- Block-measurable surrogate including the initial block mean. -/
def surrogateInit (Y : Fin (T + 1) → β) : ℝ := blockMean q μ s₀ (Y 0) + surrogate P q π b T Y

/-- The error term: accumulated directional defect minus the initial deviation. -/
def errInit (ω : Fin (T + 1) → V) : ℝ := pathDefect P q π b T ω - tildeS q μ s₀ (ω 0)

lemma pathScoreInit_split (ω : Fin (T + 1) → V) :
    pathScoreInit P q b s₀ T ω
      = surrogateInit P q π μ b s₀ T (macroPath q T ω) - errInit P q π μ b s₀ T ω := by
  unfold pathScoreInit surrogateInit errInit tildeS
  rw [pathScore_split P q π b T ω]
  simp only [macroPath]
  ring

/-- **Loss bound with a parameter-dependent initial law.** -/
theorem fisherLoss_initialLaw_le [Nonempty V] (hP : ∀ x y, 0 < P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (hπ : ∀ x, 0 < π x) (hstat : π ᵥ* P = π) (hμ : ∀ x, 0 < μ x) {κ : ℝ}
    (hdom : ∀ x, μ x ≤ κ * π x) {Bmax : ℝ} (hB : ∀ A, ∑ C, b A C ^ 2 ≤ Bmax) :
    ScoreProjection.fineFisher (pathProb P μ T) (pathDerivInit P q μ b s₀ T)
      - ScoreProjection.coarseFisher (macroPath q T) (pathProb P μ T) (pathDerivInit P q μ b s₀ T)
      ≤ 2 * κ * (T : ℝ) ^ 2 * (Bmax * BlockPairTilt.defectSq q π (blockExit P q))
        + 2 * initialDefect q μ s₀ := by
  set δ := BlockPairTilt.delta q π (blockExit P q) b
  have hpos := pathProb_pos P hP hμ T
  -- best-approximation bound with the surrogate including the initial block mean
  have hs : ∀ ω, pathDerivInit P q μ b s₀ T ω / pathProb P μ T ω
      = (fun ω => surrogateInit P q π μ b s₀ T (macroPath q T ω)) ω - errInit P q π μ b s₀ T ω := by
    intro ω
    unfold pathDerivInit
    rw [mul_div_cancel_left₀ _ (hpos ω).ne', pathScoreInit_split]
  have h1 := ScoreProjection.fisherLoss_le_errorSq (macroPath q T) (pathDerivInit P q μ b s₀ T) hpos
    (fun ω => surrogateInit P q π μ b s₀ T (macroPath q T ω)) (errInit P q π μ b s₀ T)
    (surrogateInit P q π μ b s₀ T) (fun _ => rfl) hs
  refine h1.trans ?_
  -- (a - c)^2 <= 2 a^2 + 2 c^2 pointwise
  have hsq : ∀ ω, pathProb P μ T ω * errInit P q π μ b s₀ T ω ^ 2
      ≤ pathProb P μ T ω * (2 * pathDefect P q π b T ω ^ 2 + 2 * tildeS q μ s₀ (ω 0) ^ 2) := by
    intro ω
    refine mul_le_mul_of_nonneg_left ?_ (hpos ω).le
    unfold errInit
    nlinarith [sq_nonneg (pathDefect P q π b T ω + tildeS q μ s₀ (ω 0))]
  refine (Finset.sum_le_sum (fun ω _ => hsq ω)).trans ?_
  have hsplit : ∑ ω, pathProb P μ T ω * (2 * pathDefect P q π b T ω ^ 2 + 2 * tildeS q μ s₀ (ω 0) ^ 2)
      = 2 * ∑ ω, pathProb P μ T ω * pathDefect P q π b T ω ^ 2
        + 2 * ∑ ω, pathProb P μ T ω * tildeS q μ s₀ (ω 0) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun ω _ => by ring)
  rw [hsplit]
  -- initial term: marginal at time 0 is mu
  have hinit : ∑ ω, pathProb P μ T ω * tildeS q μ s₀ (ω 0) ^ 2 = initialDefect q μ s₀ := by
    have := sum_pathProb_marginal P hrow T 0 μ (fun x => tildeS q μ s₀ x ^ 2)
    simpa [initialDefect] using this
  -- defect term: Cauchy-Schwarz over steps, then domination of marginals
  have hcs : ∀ ω, pathProb P μ T ω * pathDefect P q π b T ω ^ 2
      ≤ pathProb P μ T ω * ((T : ℝ) * ∑ t : Fin T, δ (ω (Fin.castSucc t)) ^ 2) := by
    intro ω
    refine mul_le_mul_of_nonneg_left ?_ (hpos ω).le
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin T)))
      (f := fun t => δ (ω (Fin.castSucc t)))
    simpa [pathDefect, Finset.card_univ, Fintype.card_fin] using this
  have hmarg : ∀ t : Fin T, ∑ ω, pathProb P μ T ω * δ (ω (Fin.castSucc t)) ^ 2
      ≤ κ * ∑ x, π x * δ x ^ 2 := by
    intro t
    rw [sum_pathProb_marginal P hrow T (Fin.castSucc t) μ (fun x => δ x ^ 2), Finset.mul_sum]
    refine Finset.sum_le_sum (fun x _ => ?_)
    have := vecMul_pow_le_of_le P (fun x y => (hP x y).le) hstat hdom (Fin.castSucc t) x
    calc (μ ᵥ* P ^ ((Fin.castSucc t : Fin (T + 1)) : ℕ)) x * δ x ^ 2
        ≤ κ * π x * δ x ^ 2 := mul_le_mul_of_nonneg_right this (sq_nonneg _)
      _ = κ * (π x * δ x ^ 2) := by ring
  have hdef : ∑ ω, pathProb P μ T ω * pathDefect P q π b T ω ^ 2
      ≤ κ * (T : ℝ) ^ 2 * (Bmax * BlockPairTilt.defectSq q π (blockExit P q)) := by
    have hE := BlockPairTilt.delta_energy_le q π (blockExit P q) b hπ hB
    have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    have hκ : 0 ≤ κ := by
      obtain ⟨x⟩ := (inferInstance : Nonempty V)
      have := hdom x
      have := hμ x
      have := hπ x
      nlinarith
    calc ∑ ω, pathProb P μ T ω * pathDefect P q π b T ω ^ 2
        ≤ ∑ ω, pathProb P μ T ω * ((T : ℝ) * ∑ t : Fin T, δ (ω (Fin.castSucc t)) ^ 2) :=
          Finset.sum_le_sum (fun ω _ => hcs ω)
      _ = (T : ℝ) * ∑ t : Fin T, ∑ ω, pathProb P μ T ω * δ (ω (Fin.castSucc t)) ^ 2 := by
          have hswap : ∀ ω, pathProb P μ T ω * ((T : ℝ) * ∑ t : Fin T, δ (ω (Fin.castSucc t)) ^ 2)
              = (T : ℝ) * ∑ t : Fin T, pathProb P μ T ω * δ (ω (Fin.castSucc t)) ^ 2 := by
            intro ω
            rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl (fun t _ => by ring)
          rw [Finset.sum_congr rfl (fun ω _ => hswap ω), ← Finset.mul_sum, Finset.sum_comm]
      _ ≤ (T : ℝ) * ∑ _t : Fin T, κ * ∑ x, π x * δ x ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun t _ => hmarg t)) hT
      _ = κ * (T : ℝ) ^ 2 * ∑ x, π x * δ x ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
      _ ≤ κ * (T : ℝ) ^ 2 * (Bmax * BlockPairTilt.defectSq q π (blockExit P q)) :=
          mul_le_mul_of_nonneg_left hE (mul_nonneg hκ (sq_nonneg _))
  rw [hinit]
  linarith [hdef]

end SGC.InformationGeometry.MarkovPathInitialLaw
