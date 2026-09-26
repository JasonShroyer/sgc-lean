/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.InformationGeometry.MarkovPathFisher

/-!
# One-step lower bound: the defect is two-sided when blocks exit alike

For a single transition `(X₀, X₁)` observed through the partition, the Fisher
loss about a block-pair tilt is

  `loss(1) = ‖δ_b‖²_π − Σ_{(A,C)} M_{A,C} · (E[δ_b | q X₀ = A, q X₁ = C])²`

and the explained part is controlled by how differently the states of a block
exit. With the block χ²-divergence

  `χ²_A = Σ_C (Σ_{x∈A} π x · res(x,C)²) / (Σ_{x∈A} π x · R(x,C))`

(the `π`-average over `A` of the χ² divergence between a state's exit
distribution and the block's average exit distribution),

  `loss(1) ≥ Σ_A (1 − χ²_A) · Σ_{x∈A} π x · δ_b(x)²`.

## Main results

* `sum_sq_dev_eq` — explained-variance identity for any coarse-graining.
* `oneStepLoss_eq` — the exact one-step loss as `‖δ‖² − explained`.
* `oneStepLoss_ge` — **the lower bound above** (kernel-checked).

## What is not claimed

No universal constant `c` with `loss(1) ≥ c‖δ_b‖²` exists: in a block whose two
states exit to different blocks with probability `1 − ε`, the next block
identifies the state and `loss(1)/‖δ_b‖² → 0` as `ε → 0` (numerical witness,
`closure_sufficiency_v4`). `χ²_A → 1` in that family, so the bound above is
not vacuous there; it is exact for blocks of two states.
-/

noncomputable section

namespace SGC.InformationGeometry.OneStepLowerBound

open Finset Matrix SGC.InformationGeometry
open SGC.InformationGeometry.MarkovPathFisher

set_option linter.unusedSectionVars false

variable {Ω β : Type*} [Fintype Ω] [Fintype β] [DecidableEq β]

/-- Explained-variance identity for `ScoreProjection.blockAvg`. -/
theorem sum_sq_dev_eq (q : Ω → β) {p : Ω → ℝ} (hp : ∀ ω, 0 < p ω) (e : Ω → ℝ) :
    ∑ ω, p ω * (e ω - ScoreProjection.blockAvg q p e (q ω)) ^ 2
      = ∑ ω, p ω * e ω ^ 2
        - ∑ b, ScoreProjection.blockMass q p b * ScoreProjection.blockAvg q p e b ^ 2 := by
  rw [ScoreProjection.sum_fibers q (fun ω => p ω * (e ω - ScoreProjection.blockAvg q p e (q ω)) ^ 2),
    ScoreProjection.sum_fibers q (fun ω => p ω * e ω ^ 2), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have hc : ∀ ω ∈ univ.filter (fun ω => q ω = b),
      p ω * (e ω - ScoreProjection.blockAvg q p e (q ω)) ^ 2
        = p ω * (e ω - ScoreProjection.blockAvg q p e b) ^ 2 := by
    intro ω hω
    rw [(Finset.mem_filter.mp hω).2]
  rw [Finset.sum_congr rfl hc]
  set m := ScoreProjection.blockAvg q p e b
  set M := ScoreProjection.blockMass q p b
  have hexp : ∀ ω, p ω * (e ω - m) ^ 2 = p ω * e ω ^ 2 - 2 * m * (p ω * e ω) + m ^ 2 * p ω :=
    fun ω => by ring
  rw [Finset.sum_congr rfl (fun ω _ => hexp ω), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  change _ - 2 * m * ∑ ω ∈ univ.filter (fun ω => q ω = b), p ω * e ω + m ^ 2 * M = _
  rcases eq_or_ne M 0 with hM | hM
  · have hempty : univ.filter (fun ω => q ω = b) = ∅ := by
      by_contra hne
      obtain ⟨ω, hω⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have : 0 < M := Finset.sum_pos (fun ω _ => hp ω) ⟨ω, hω⟩
      linarith
    simp [hempty, hM]
  · have hM' : ScoreProjection.blockMass q p b ≠ 0 := hM
    have hS : ∑ ω ∈ univ.filter (fun ω => q ω = b), p ω * e ω = m * M := by
      simp only [m, M, ScoreProjection.blockAvg]
      exact (div_mul_cancel₀ _ hM').symm
    rw [hS]
    ring

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (P : Matrix V V ℝ) (q : V → β) (π : V → ℝ) (b : β → β → ℝ)

/-- Coarse map on one transition. -/
def Q (ω : V × V) : β × β := (q ω.1, q ω.2)

/-- Law of one transition from the stationary start. -/
def stepProb (ω : V × V) : ℝ := π ω.1 * P ω.1 ω.2

/-- Derivative data `p · score` of one transition under the block-pair tilt. -/
def stepDeriv (ω : V × V) : ℝ :=
  stepProb P π ω * BlockPairTilt.stepScore q b (blockExit P q) ω.1 (q ω.2)

/-- One-step Fisher loss. -/
def oneStepLoss : ℝ :=
  ScoreProjection.fineFisher (stepProb P π) (stepDeriv P q π b)
    - ScoreProjection.coarseFisher (Q q) (stepProb P π) (stepDeriv P q π b)

/-- Block-indicator sum. -/
def blockSum (A : β) (f : V → ℝ) : ℝ := ∑ x, if q x = A then f x else 0

/-- Block χ² divergence of exit distributions. -/
def chiSq (A : β) : ℝ :=
  ∑ C, blockSum q A (fun x => π x * BlockPairTilt.res q π (blockExit P q) x C ^ 2)
        / blockSum q A (fun x => π x * blockExit P q x C)

/-- `π`-weighted energy of the directional defect on a block. -/
def blockEnergy (A : β) : ℝ :=
  blockSum q A (fun x => π x * BlockPairTilt.delta q π (blockExit P q) b x ^ 2)

lemma stepProb_pos (hP : ∀ x y, 0 < P x y) (hπ : ∀ x, 0 < π x) (ω : V × V) :
    0 < stepProb P π ω := mul_pos (hπ _) (hP _ _)

/-- Fiber sums on `V × V` as indicator double sums. -/
lemma sum_fiber_prod (A C : β) (F : V × V → ℝ) :
    ∑ ω ∈ univ.filter (fun ω : V × V => Q q ω = (A, C)), F ω
      = ∑ x, if q x = A then ∑ y ∈ univ.filter (fun y => q y = C), F (x, y) else 0 := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hx : q x = A
  · rw [if_pos hx, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    by_cases hy : q y = C
    · simp [Q, hx, hy]
    · simp [Q, hy]
  · rw [if_neg hx]
    refine Finset.sum_eq_zero (fun y _ => ?_)
    simp [Q, hx]

lemma blockMass_eq (A C : β) :
    ScoreProjection.blockMass (Q q) (stepProb P π) (A, C)
      = blockSum q A (fun x => π x * blockExit P q x C) := by
  unfold ScoreProjection.blockMass blockSum
  rw [sum_fiber_prod]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  split_ifs
  · simp only [stepProb, blockExit, Finset.mul_sum]
  · rfl

lemma blockWeighted_eq (A C : β) :
    ∑ ω ∈ univ.filter (fun ω : V × V => Q q ω = (A, C)),
        stepProb P π ω * BlockPairTilt.delta q π (blockExit P q) b ω.1
      = blockSum q A (fun x => π x * blockExit P q x C * BlockPairTilt.delta q π (blockExit P q) b x) := by
  unfold blockSum
  rw [sum_fiber_prod]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  split_ifs
  · simp only [stepProb, blockExit, Finset.mul_sum, Finset.sum_mul]
  · rfl

/-- Per-block mean-zero of the directional defect. -/
lemma delta_block_mean_zero (hπ : ∀ x, 0 < π x) (A : β) :
    blockSum q A (fun x => π x * BlockPairTilt.delta q π (blockExit P q) b x) = 0 := by
  unfold blockSum BlockPairTilt.delta
  have h : ∀ x, (if q x = A then π x * ∑ C, BlockPairTilt.res q π (blockExit P q) x C * b (q x) C else 0)
      = ∑ C, b A C * (if q x = A then π x * BlockPairTilt.res q π (blockExit P q) x C else 0) := by
    intro x
    split_ifs with hx
    · rw [hx, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun C _ => by ring)
    · simp
  rw [Finset.sum_congr rfl (fun x _ => h x), Finset.sum_comm]
  refine Finset.sum_eq_zero (fun C _ => ?_)
  rw [← Finset.mul_sum]
  have := BlockPairTilt.res_block_mean_zero q π (blockExit P q) hπ A C
  rw [Finset.sum_filter] at this
  rw [this, mul_zero]

/-- `Σ_{x∈A} π x R(x,C) δ(x) = Σ_{x∈A} π x res(x,C) δ(x)`. -/
lemma blockWeighted_res (hπ : ∀ x, 0 < π x) (A C : β) :
    blockSum q A (fun x => π x * blockExit P q x C * BlockPairTilt.delta q π (blockExit P q) b x)
      = blockSum q A (fun x => π x * BlockPairTilt.res q π (blockExit P q) x C
          * BlockPairTilt.delta q π (blockExit P q) b x) := by
  have h0 := delta_block_mean_zero P q π b hπ A
  unfold blockSum at h0 ⊢
  have hsplit : ∀ x, (if q x = A then π x * blockExit P q x C * BlockPairTilt.delta q π (blockExit P q) b x else 0)
      = (if q x = A then π x * BlockPairTilt.res q π (blockExit P q) x C
            * BlockPairTilt.delta q π (blockExit P q) b x else 0)
        + BlockPairTilt.Rbar q π (blockExit P q) A C
          * (if q x = A then π x * BlockPairTilt.delta q π (blockExit P q) b x else 0) := by
    intro x
    split_ifs with hx
    · unfold BlockPairTilt.res
      rw [hx]
      ring
    · simp
  rw [Finset.sum_congr rfl (fun x _ => hsplit x), Finset.sum_add_distrib, ← Finset.mul_sum, h0,
    mul_zero, add_zero]

/-- Weighted Cauchy–Schwarz with indicator weights. -/
lemma blockSum_cs (hπ : ∀ x, 0 < π x) (A : β) (u v : V → ℝ) :
    blockSum q A (fun x => π x * u x * v x) ^ 2
      ≤ blockSum q A (fun x => π x * u x ^ 2) * blockSum q A (fun x => π x * v x ^ 2) := by
  unfold blockSum
  have h := Finset.sum_mul_sq_le_sq_mul_sq univ
    (fun x => if q x = A then Real.sqrt (π x) * u x else 0)
    (fun x => if q x = A then Real.sqrt (π x) * v x else 0)
  have e1 : ∀ x, (if q x = A then Real.sqrt (π x) * u x else 0) * (if q x = A then Real.sqrt (π x) * v x else 0)
      = if q x = A then π x * u x * v x else 0 := by
    intro x
    split_ifs
    · have := Real.mul_self_sqrt (hπ x).le
      calc _ = (Real.sqrt (π x) * Real.sqrt (π x)) * (u x * v x) := by ring
        _ = _ := by rw [this]; ring
    · simp
  have e2 : ∀ (w : V → ℝ) x, (if q x = A then Real.sqrt (π x) * w x else 0) ^ 2
      = if q x = A then π x * w x ^ 2 else 0 := by
    intro w x
    split_ifs
    · rw [mul_pow, Real.sq_sqrt (hπ x).le]
    · simp
  simp only [e1, e2] at h
  exact h

/-- **Exact one-step loss.** -/
theorem oneStepLoss_eq (hP : ∀ x y, 0 < P x y) (hrow : ∀ x, ∑ y, P x y = 1) (hπ : ∀ x, 0 < π x) :
    oneStepLoss P q π b
      = ∑ x, π x * BlockPairTilt.delta q π (blockExit P q) b x ^ 2
        - ∑ f : β × β, ScoreProjection.blockMass (Q q) (stepProb P π) f
            * ScoreProjection.blockAvg (Q q) (stepProb P π)
                (fun ω => BlockPairTilt.delta q π (blockExit P q) b ω.1) f ^ 2 := by
  unfold oneStepLoss
  set δ := BlockPairTilt.delta q π (blockExit P q) b
  have hs : ∀ ω : V × V, stepDeriv P q π b ω / stepProb P π ω
      = (fun ω : V × V => BlockPairTilt.stepScore q b (fun x C => BlockPairTilt.Rbar q π (blockExit P q) (q x) C)
          ω.1 (q ω.2)) ω - δ ω.1 := by
    intro ω
    unfold stepDeriv
    rw [mul_div_cancel_left₀ _ (stepProb_pos P π hP hπ ω).ne']
    have h := BlockPairTilt.surrogate_error_eq q π (blockExit P q) b ω.1 (q ω.2)
    simp only [δ]
    linarith
  set g' : β × β → ℝ := fun f => b f.1 f.2 - ∑ C, BlockPairTilt.Rbar q π (blockExit P q) f.1 C * b f.1 C
  have hg : ∀ ω : V × V, BlockPairTilt.stepScore q b (fun x C => BlockPairTilt.Rbar q π (blockExit P q) (q x) C)
      ω.1 (q ω.2) = g' (Q q ω) := by
    intro ω
    rfl
  rw [ScoreProjection.fisherLoss_eq_condVar (Q q) (stepDeriv P q π b) (stepProb_pos P π hP hπ)
    (fun ω : V × V => BlockPairTilt.stepScore q b (fun x C => BlockPairTilt.Rbar q π (blockExit P q) (q x) C) ω.1 (q ω.2))
    (fun ω => δ ω.1) g' hg hs, sum_sq_dev_eq (Q q) (stepProb_pos P π hP hπ)]
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [stepProb]
  have : ∀ y, π x * P x y * δ x ^ 2 = (π x * δ x ^ 2) * P x y := fun y => by ring
  rw [Finset.sum_congr rfl (fun y _ => this y), ← Finset.mul_sum, hrow x, mul_one]

/-- **One-step lower bound.** -/
theorem oneStepLoss_ge (hP : ∀ x y, 0 < P x y) (hrow : ∀ x, ∑ y, P x y = 1) (hπ : ∀ x, 0 < π x) :
    ∑ A, (1 - chiSq P q π A) * blockEnergy P q π b A ≤ oneStepLoss P q π b := by
  rw [oneStepLoss_eq P q π b hP hrow hπ]
  set δ := BlockPairTilt.delta q π (blockExit P q) b
  -- total energy splits over blocks
  have htot : ∑ x, π x * δ x ^ 2 = ∑ A, blockEnergy P q π b A := by
    unfold blockEnergy blockSum
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_ite_eq]
    simp [δ]
  -- explained variance bounded blockwise
  have hexpl : ∑ f : β × β, ScoreProjection.blockMass (Q q) (stepProb P π) f
      * ScoreProjection.blockAvg (Q q) (stepProb P π) (fun ω => δ ω.1) f ^ 2
      ≤ ∑ A, chiSq P q π A * blockEnergy P q π b A := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum (fun A _ => ?_)
    unfold chiSq
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun C _ => ?_)
    -- single fiber (A, C)
    set M := blockSum q A (fun x => π x * blockExit P q x C)
    set S := blockSum q A (fun x => π x * BlockPairTilt.res q π (blockExit P q) x C * δ x)
    have hM_eq := blockMass_eq P q π A C
    have hW : ∑ ω ∈ univ.filter (fun ω : V × V => Q q ω = (A, C)), stepProb P π ω * δ ω.1 = S := by
      rw [blockWeighted_eq, blockWeighted_res P q π b hπ]
    have hMnn : 0 ≤ M := Finset.sum_nonneg (fun x _ => by
      split_ifs
      · exact mul_nonneg (hπ x).le (Finset.sum_nonneg (fun y _ => (hP x y).le))
      · exact le_rfl)
    have hcs := blockSum_cs q π hπ A (fun x => BlockPairTilt.res q π (blockExit P q) x C) δ
    have hcs' : S ^ 2 ≤ blockSum q A (fun x => π x * BlockPairTilt.res q π (blockExit P q) x C ^ 2)
        * blockEnergy P q π b A := by
      unfold blockEnergy
      simpa [S, blockSum] using hcs
    unfold ScoreProjection.blockAvg
    rw [hM_eq, hW]
    change M * (S / M) ^ 2 ≤ _ / M * blockEnergy P q π b A
    rcases eq_or_ne M 0 with hM0 | hM0
    · simp [hM0]
    · have hMpos : 0 < M := lt_of_le_of_ne hMnn (Ne.symm hM0)
      have hred : M * (S / M) ^ 2 = S ^ 2 / M := by
        field_simp
      rw [hred, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hcs' hMpos.le
  have hsplit : ∑ A, (1 - chiSq P q π A) * blockEnergy P q π b A
      = ∑ A, blockEnergy P q π b A - ∑ A, chiSq P q π A * blockEnergy P q π b A := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun A _ => by ring)
  rw [hsplit, htot]
  linarith

end SGC.InformationGeometry.OneStepLowerBound
