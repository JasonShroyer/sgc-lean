/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.InformationGeometry.ScoreProjection
import SGC.InformationGeometry.BlockPairTilt
import SGC.Renormalization.MeasureReentry
import Mathlib.Algebra.Order.Chebyshev

/-!
# Fisher information lost by observing a Markov chain through a partition

Finite-horizon path-space assembly of the directional closure bound.

Setting: a row-stochastic matrix `P` with positive entries on a finite state
space `V`, a strictly positive stationary law `π` (`π ᵥ* P = π`), a map
`q : V → β` to blocks, a block-pair tilt `b : β → β → ℝ`, and horizon `T`.
The fine observer sees `X₀..X_T`; the coarse observer sees `q X₀..q X_T`.
The fine path score is the sum of block-pair-tilt step scores
`b (q x) (q y) - Σ_C R x C * b (q x) C`, with `R` the block exit
probabilities of `P` (for `P_θ = row-softmax(A + θ B)`, `B x y = b (q x) (q y)`,
this is `∂_θ log P_θ(x,y)` at `θ = 0`; see `FiniteExponentialFamily.hasDerivAt_logProb_line`
applied row by row). The initial law does not depend on `θ`.

## Main results

* `sum_pathProb_marginal` — the time-`k` marginal of the path law is `μ ᵥ* P^k`;
  `sum_pathProb_stationary` — it is `π` at every time for a stationary start.
* `fisherLoss_markov_path_condVar` — **exact**: the Fisher loss equals the
  expected within-macro-history variance of `Σ_t δ(X_t)`.
* `fisherLoss_markov_path_le` — `loss ≤ T² · Bmax · D_π²`.
* `fisherLoss_markov_path_le_measureReentry` — the same bound with the
  repository's canonical defect `MeasureReentry.defectSq` for a `Partition`.

The linear-in-`T` refinement under mixing is not proved here.
-/

noncomputable section

namespace SGC.InformationGeometry.MarkovPathFisher

open Finset Matrix

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Probability of a path of length `T` under initial law `μ`. -/
def pathProb (P : Matrix V V ℝ) (μ : V → ℝ) (T : ℕ) (ω : Fin (T + 1) → V) : ℝ :=
  μ (ω 0) * ∏ t : Fin T, P (ω (Fin.castSucc t)) (ω (Fin.succ t))

lemma pathProb_cons (P : Matrix V V ℝ) (μ : V → ℝ) (T : ℕ) (x : V) (ω : Fin (T + 1) → V) :
    pathProb P μ (T + 1) (Fin.cons x ω) = μ x * pathProb P (P x) T ω := by
  unfold pathProb
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.castSucc_zero, Fin.cons_succ, ← Fin.succ_castSucc]

lemma sum_cons (T : ℕ) (F : (Fin (T + 2) → V) → ℝ) :
    ∑ ω, F ω = ∑ x, ∑ ω' : Fin (T + 1) → V, F (Fin.cons x ω') := by
  rw [← (Fin.consEquiv fun _ => V).sum_comp, Fintype.sum_prod_type]
  rfl

lemma sum_row_vecMul (P M : Matrix V V ℝ) (μ : V → ℝ) (y : V) :
    ∑ x, μ x * (P x ᵥ* M) y = (μ ᵥ* (P * M)) y := by
  simp only [vecMul, dotProduct, Matrix.mul_apply, Finset.mul_sum]

/-- **Path marginals.** The time-`k` marginal of the path law is `μ ᵥ* P^k`. -/
theorem sum_pathProb_marginal (P : Matrix V V ℝ) (hrow : ∀ x, ∑ y, P x y = 1) :
    ∀ (T : ℕ) (k : Fin (T + 1)) (μ f : V → ℝ),
      ∑ ω, pathProb P μ T ω * f (ω k) = ∑ x, (μ ᵥ* P ^ (k : ℕ)) x * f x := by
  intro T
  induction T with
  | zero =>
    intro k μ f
    obtain ⟨k, hk⟩ := k
    obtain rfl : k = 0 := by omega
    change ∑ ω : Fin 1 → V, pathProb P μ 0 ω * f (ω 0) = _
    rw [← (Equiv.funUnique (Fin 1) V).symm.sum_comp]
    simp [pathProb]
  | succ T ih =>
    intro k μ f
    rw [sum_cons]
    simp only [pathProb_cons]
    refine Fin.cases ?_ (fun k' => ?_) k
    · simp only [Fin.cons_zero, Fin.val_zero, pow_zero, vecMul_one]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      have htot := ih 0 (P x) (fun _ => 1)
      simp only [mul_one, Fin.val_zero, pow_zero, vecMul_one] at htot
      have hsum : ∑ ω' : Fin (T + 1) → V, μ x * pathProb P (P x) T ω' * f x
          = μ x * f x * ∑ ω', pathProb P (P x) T ω' := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun ω' _ => by ring)
      rw [hsum, htot, hrow x, mul_one]
    · simp only [Fin.cons_succ, Fin.val_succ]
      have hstep : ∀ x, ∑ ω' : Fin (T + 1) → V, μ x * pathProb P (P x) T ω' * f (ω' k')
          = μ x * ∑ y, (P x ᵥ* P ^ (k' : ℕ)) y * f y := by
        intro x
        rw [← ih k' (P x) f, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun ω' _ => by ring)
      rw [Finset.sum_congr rfl (fun x _ => hstep x)]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [pow_succ', ← sum_row_vecMul, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun x _ => by ring)

lemma vecMul_pow_stationary (P : Matrix V V ℝ) {π : V → ℝ} (hπ : π ᵥ* P = π) :
    ∀ k : ℕ, π ᵥ* P ^ k = π := by
  intro k
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← vecMul_vecMul, ih, hπ]

/-- For a stationary start, every time marginal of the path law is `π`. -/
theorem sum_pathProb_stationary (P : Matrix V V ℝ) (hrow : ∀ x, ∑ y, P x y = 1)
    {π : V → ℝ} (hπ : π ᵥ* P = π) (T : ℕ) (k : Fin (T + 1)) (f : V → ℝ) :
    ∑ ω, pathProb P π T ω * f (ω k) = ∑ x, π x * f x := by
  rw [sum_pathProb_marginal P hrow T k π f, vecMul_pow_stationary P hπ]

lemma pathProb_pos (P : Matrix V V ℝ) (hP : ∀ x y, 0 < P x y) {μ : V → ℝ}
    (hμ : ∀ x, 0 < μ x) (T : ℕ) (ω : Fin (T + 1) → V) : 0 < pathProb P μ T ω :=
  mul_pos (hμ _) (Finset.prod_pos (fun _ _ => hP _ _))

/-! ### Block-pair tilt on path space -/

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- Block exit probabilities of `P`. -/
def blockExit (P : Matrix V V ℝ) (q : V → β) (x : V) (C : β) : ℝ :=
  ∑ y ∈ univ.filter (fun y => q y = C), P x y

/-- Fine path score of the block-pair tilt. -/
def pathScore (P : Matrix V V ℝ) (q : V → β) (b : β → β → ℝ) (T : ℕ)
    (ω : Fin (T + 1) → V) : ℝ :=
  ∑ t : Fin T, BlockPairTilt.stepScore q b (blockExit P q) (ω (Fin.castSucc t)) (q (ω (Fin.succ t)))

/-- Accumulated directional closure defect along a path. -/
def pathDefect (P : Matrix V V ℝ) (q : V → β) (π : V → ℝ) (b : β → β → ℝ) (T : ℕ)
    (ω : Fin (T + 1) → V) : ℝ :=
  ∑ t : Fin T, BlockPairTilt.delta q π (blockExit P q) b (ω (Fin.castSucc t))

/-- The macro-history of a path. -/
def macroPath (q : V → β) (T : ℕ) (ω : Fin (T + 1) → V) : Fin (T + 1) → β := fun t => q (ω t)

/-- Block-measurable surrogate score. -/
def surrogate (P : Matrix V V ℝ) (q : V → β) (π : V → ℝ) (b : β → β → ℝ) (T : ℕ)
    (Y : Fin (T + 1) → β) : ℝ :=
  ∑ t : Fin T, (b (Y (Fin.castSucc t)) (Y (Fin.succ t))
    - ∑ C, BlockPairTilt.Rbar q π (blockExit P q) (Y (Fin.castSucc t)) C * b (Y (Fin.castSucc t)) C)

lemma pathScore_split (P : Matrix V V ℝ) (q : V → β) (π : V → ℝ) (b : β → β → ℝ) (T : ℕ)
    (ω : Fin (T + 1) → V) :
    pathScore P q b T ω = surrogate P q π b T (macroPath q T ω) - pathDefect P q π b T ω := by
  unfold pathScore surrogate pathDefect macroPath
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  have h := BlockPairTilt.surrogate_error_eq q π (blockExit P q) b
    (ω (Fin.castSucc t)) (q (ω (Fin.succ t)))
  unfold BlockPairTilt.stepScore at h ⊢
  linarith

variable (P : Matrix V V ℝ) (q : V → β) (π : V → ℝ) (b : β → β → ℝ) (T : ℕ)

/-- Derivative data of the path law: `p · S`. -/
def pathDeriv (ω : Fin (T + 1) → V) : ℝ := pathProb P π T ω * pathScore P q b T ω

lemma pathDeriv_div (hP : ∀ x y, 0 < P x y) (hπ : ∀ x, 0 < π x) (ω : Fin (T + 1) → V) :
    pathDeriv P q π b T ω / pathProb P π T ω
      = surrogate P q π b T (macroPath q T ω) - pathDefect P q π b T ω := by
  unfold pathDeriv
  rw [mul_div_cancel_left₀ _ (pathProb_pos P hP hπ T ω).ne', pathScore_split P q π b T ω]

/-- **Exact path-space Fisher loss.** The information about a block-pair tilt
lost by observing only the macro-history equals the expected
within-macro-history variance of the accumulated directional closure defect. -/
theorem fisherLoss_markov_path_condVar (hP : ∀ x y, 0 < P x y) (hπ : ∀ x, 0 < π x) :
    ScoreProjection.fineFisher (pathProb P π T) (pathDeriv P q π b T)
      - ScoreProjection.coarseFisher (macroPath q T) (pathProb P π T) (pathDeriv P q π b T)
      = ∑ ω, pathProb P π T ω * (pathDefect P q π b T ω
          - ScoreProjection.blockAvg (macroPath q T) (pathProb P π T) (pathDefect P q π b T)
              (macroPath q T ω)) ^ 2 :=
  ScoreProjection.fisherLoss_eq_condVar (macroPath q T) (pathDeriv P q π b T)
    (pathProb_pos P hP hπ T) (fun ω => surrogate P q π b T (macroPath q T ω))
    (pathDefect P q π b T) (surrogate P q π b T) (fun _ => rfl) (pathDeriv_div P q π b T hP hπ)

/-- **Energy form of the directional bound:** `loss(T) ≤ T² · ‖δ_b‖²_π`. -/
theorem fisherLoss_markov_path_le_energy (hP : ∀ x y, 0 < P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (hπ : ∀ x, 0 < π x) (hstat : π ᵥ* P = π) :
    ScoreProjection.fineFisher (pathProb P π T) (pathDeriv P q π b T)
      - ScoreProjection.coarseFisher (macroPath q T) (pathProb P π T) (pathDeriv P q π b T)
      ≤ (T : ℝ) ^ 2 * ∑ x, π x * BlockPairTilt.delta q π (blockExit P q) b x ^ 2 := by
  set δ := BlockPairTilt.delta q π (blockExit P q) b
  have h1 := ScoreProjection.fisherLoss_le_errorSq (macroPath q T) (pathDeriv P q π b T)
    (pathProb_pos P hP hπ T) (fun ω => surrogate P q π b T (macroPath q T ω))
    (pathDefect P q π b T) (surrogate P q π b T) (fun _ => rfl) (pathDeriv_div P q π b T hP hπ)
  refine h1.trans ?_
  have hcs : ∀ ω, pathProb P π T ω * pathDefect P q π b T ω ^ 2
      ≤ pathProb P π T ω * ((T : ℝ) * ∑ t : Fin T, δ (ω (Fin.castSucc t)) ^ 2) := by
    intro ω
    refine mul_le_mul_of_nonneg_left ?_ (pathProb_pos P hP hπ T ω).le
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin T)))
      (f := fun t => δ (ω (Fin.castSucc t)))
    simpa [pathDefect, Finset.card_univ, Fintype.card_fin] using this
  have hmarg : ∑ ω, pathProb P π T ω * ((T : ℝ) * ∑ t : Fin T, δ (ω (Fin.castSucc t)) ^ 2)
      = (T : ℝ) * ∑ t : Fin T, ∑ x, π x * δ x ^ 2 := by
    have hswap : ∀ ω, pathProb P π T ω * ((T : ℝ) * ∑ t : Fin T, δ (ω (Fin.castSucc t)) ^ 2)
        = (T : ℝ) * ∑ t : Fin T, pathProb P π T ω * δ (ω (Fin.castSucc t)) ^ 2 := by
      intro ω
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun t _ => by ring)
    rw [Finset.sum_congr rfl (fun ω _ => hswap ω), ← Finset.mul_sum, Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl (fun t _ =>
      sum_pathProb_stationary P hrow hstat T (Fin.castSucc t) (fun x => δ x ^ 2))
  calc ∑ ω, pathProb P π T ω * pathDefect P q π b T ω ^ 2
      ≤ ∑ ω, pathProb P π T ω * ((T : ℝ) * ∑ t : Fin T, δ (ω (Fin.castSucc t)) ^ 2) :=
        Finset.sum_le_sum (fun ω _ => hcs ω)
    _ = (T : ℝ) ^ 2 * ∑ x, π x * δ x ^ 2 := by
        rw [hmarg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **Directional closure bound on path space.** -/
theorem fisherLoss_markov_path_le (hP : ∀ x y, 0 < P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (hπ : ∀ x, 0 < π x) (hstat : π ᵥ* P = π) {Bmax : ℝ} (hB : ∀ A, ∑ C, b A C ^ 2 ≤ Bmax) :
    ScoreProjection.fineFisher (pathProb P π T) (pathDeriv P q π b T)
      - ScoreProjection.coarseFisher (macroPath q T) (pathProb P π T) (pathDeriv P q π b T)
      ≤ (T : ℝ) ^ 2 * (Bmax * BlockPairTilt.defectSq q π (blockExit P q)) := by
  set δ := BlockPairTilt.delta q π (blockExit P q) b
  have h1 := ScoreProjection.fisherLoss_le_errorSq (macroPath q T) (pathDeriv P q π b T)
    (pathProb_pos P hP hπ T) (fun ω => surrogate P q π b T (macroPath q T ω))
    (pathDefect P q π b T) (surrogate P q π b T) (fun _ => rfl) (pathDeriv_div P q π b T hP hπ)
  refine h1.trans ?_
  have hcs : ∀ ω, pathProb P π T ω * pathDefect P q π b T ω ^ 2
      ≤ pathProb P π T ω * ((T : ℝ) * ∑ t : Fin T, δ (ω (Fin.castSucc t)) ^ 2) := by
    intro ω
    refine mul_le_mul_of_nonneg_left ?_ (pathProb_pos P hP hπ T ω).le
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin T)))
      (f := fun t => δ (ω (Fin.castSucc t)))
    simpa [pathDefect, Finset.card_univ, Fintype.card_fin] using this
  have hmarg : ∑ ω, pathProb P π T ω * ((T : ℝ) * ∑ t : Fin T, δ (ω (Fin.castSucc t)) ^ 2)
      = (T : ℝ) * ∑ t : Fin T, ∑ x, π x * δ x ^ 2 := by
    have hswap : ∀ ω, pathProb P π T ω * ((T : ℝ) * ∑ t : Fin T, δ (ω (Fin.castSucc t)) ^ 2)
        = (T : ℝ) * ∑ t : Fin T, pathProb P π T ω * δ (ω (Fin.castSucc t)) ^ 2 := by
      intro ω
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun t _ => by ring)
    rw [Finset.sum_congr rfl (fun ω _ => hswap ω), ← Finset.mul_sum, Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl (fun t _ =>
      sum_pathProb_stationary P hrow hstat T (Fin.castSucc t) (fun x => δ x ^ 2))
  have hE := BlockPairTilt.delta_energy_le q π (blockExit P q) b hπ hB
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  calc ∑ ω, pathProb P π T ω * pathDefect P q π b T ω ^ 2
      ≤ ∑ ω, pathProb P π T ω * ((T : ℝ) * ∑ t : Fin T, δ (ω (Fin.castSucc t)) ^ 2) :=
        Finset.sum_le_sum (fun ω _ => hcs ω)
    _ = (T : ℝ) * ((T : ℝ) * ∑ x, π x * δ x ^ 2) := by
        rw [hmarg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ (T : ℝ) ^ 2 * (Bmax * BlockPairTilt.defectSq q π (blockExit P q)) := by
        have := mul_le_mul_of_nonneg_left hE (mul_nonneg hT hT)
        nlinarith [this]

/-! ### Towers of partitions -/

section Tower

variable {γ : Type*} [Fintype γ] [DecidableEq γ]

lemma macroPath_comp (f : β → γ) (ω : Fin (T + 1) → V) :
    macroPath (fun x => f (q x)) T ω = (fun Y : Fin (T + 1) → β => fun t => f (Y t)) (macroPath q T ω) :=
  rfl

lemma macroPath_surjective (hq : Function.Surjective q) :
    Function.Surjective (macroPath q T) := by
  intro Y
  refine ⟨fun t => Classical.choose (hq (Y t)), ?_⟩
  funext t
  exact Classical.choose_spec (hq (Y t))

/-- **Chain rule on path space.** For a tower `V → β → γ` of partitions, the loss
through the composite partition equals the loss through `q` plus the loss of the
`β`-observer's pushed-forward path family through `f`. No hypotheses. -/
theorem fisherLoss_markov_chain (f : β → γ) (μ : V → ℝ) (d : (Fin (T + 1) → V) → ℝ) :
    ScoreProjection.fineFisher (pathProb P μ T) d
      - ScoreProjection.coarseFisher (macroPath (fun x => f (q x)) T) (pathProb P μ T) d
      = (ScoreProjection.fineFisher (pathProb P μ T) d
          - ScoreProjection.coarseFisher (macroPath q T) (pathProb P μ T) d)
        + (ScoreProjection.fineFisher (ScoreProjection.blockMass (macroPath q T) (pathProb P μ T))
              (ScoreProjection.blockDeriv (macroPath q T) d)
          - ScoreProjection.coarseFisher (fun Y : Fin (T + 1) → β => fun t => f (Y t))
              (ScoreProjection.blockMass (macroPath q T) (pathProb P μ T))
              (ScoreProjection.blockDeriv (macroPath q T) d)) := by
  have hcomp : macroPath (fun x => f (q x)) T
      = fun ω => (fun Y : Fin (T + 1) → β => fun t => f (Y t)) (macroPath q T ω) := rfl
  rw [hcomp]
  exact ScoreProjection.fisherLoss_chain (macroPath q T) d (fun Y => fun t => f (Y t))

/-- **Monotonicity in refinement on path space.** A coarser partition loses at
least as much Fisher information as any finer partition it factors through. -/
theorem fisherLoss_markov_mono (hP : ∀ x y, 0 < P x y) {μ : V → ℝ} (hμ : ∀ x, 0 < μ x)
    (hq : Function.Surjective q) (f : β → γ) (d : (Fin (T + 1) → V) → ℝ) :
    ScoreProjection.fineFisher (pathProb P μ T) d
      - ScoreProjection.coarseFisher (macroPath q T) (pathProb P μ T) d
      ≤ ScoreProjection.fineFisher (pathProb P μ T) d
      - ScoreProjection.coarseFisher (macroPath (fun x => f (q x)) T) (pathProb P μ T) d := by
  rw [fisherLoss_markov_chain P q T f μ d]
  have h := ScoreProjection.coarseFisher_le (fun Y : Fin (T + 1) → β => fun t => f (Y t))
    (ScoreProjection.blockDeriv (macroPath q T) d)
    (ScoreProjection.blockMass_pos (macroPath q T) (pathProb_pos P hP hμ T)
      (macroPath_surjective q T hq))
  linarith

/-- Strong lumpability of `q` for `P`: block exit probabilities are constant on blocks. -/
def Lumpable (P : Matrix V V ℝ) (q : V → β) : Prop :=
  ∀ x y, q x = q y → ∀ C, blockExit P q x C = blockExit P q y C

lemma res_eq_zero_of_lumpable (P : Matrix V V ℝ) (q : V → β) (π : V → ℝ) (hπ : ∀ x, 0 < π x)
    (hl : Lumpable P q) (x : V) (C : β) : BlockPairTilt.res q π (blockExit P q) x C = 0 := by
  unfold BlockPairTilt.res BlockPairTilt.Rbar
  have hM : 0 < BlockPairTilt.blockMass q π (q x) :=
    Finset.sum_pos (fun y _ => hπ y) ⟨x, by simp⟩
  have hconst : ∑ y ∈ univ.filter (fun y => q y = q x), π y * blockExit P q y C
      = blockExit P q x C * BlockPairTilt.blockMass q π (q x) := by
    unfold BlockPairTilt.blockMass
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    rw [hl y x (Finset.mem_filter.mp hy).2 C]
    ring
  rw [hconst, mul_div_assoc, div_self hM.ne', mul_one, sub_self]

/-- **A lumpable level is transparent.** Under strong lumpability of `q`, the
macro-observer loses no Fisher information about any block-pair tilt. -/
theorem fisherLoss_markov_path_eq_zero_of_lumpable (hP : ∀ x y, 0 < P x y) (hπ : ∀ x, 0 < π x)
    (hl : Lumpable P q) :
    ScoreProjection.fineFisher (pathProb P π T) (pathDeriv P q π b T)
      - ScoreProjection.coarseFisher (macroPath q T) (pathProb P π T) (pathDeriv P q π b T) = 0 := by
  have hδ : ∀ x, BlockPairTilt.delta q π (blockExit P q) b x = 0 := by
    intro x
    unfold BlockPairTilt.delta
    exact Finset.sum_eq_zero (fun C _ => by rw [res_eq_zero_of_lumpable P q π hπ hl x C, zero_mul])
  have hdef : ∀ ω, pathDefect P q π b T ω = 0 := by
    intro ω
    unfold pathDefect
    exact Finset.sum_eq_zero (fun t _ => hδ _)
  have h1 := ScoreProjection.fisherLoss_le_errorSq (macroPath q T) (pathDeriv P q π b T)
    (pathProb_pos P hP hπ T) (fun ω => surrogate P q π b T (macroPath q T ω))
    (pathDefect P q π b T) (surrogate P q π b T) (fun _ => rfl) (pathDeriv_div P q π b T hP hπ)
  have h2 := ScoreProjection.coarseFisher_le (macroPath q T) (pathDeriv P q π b T)
    (pathProb_pos P hP hπ T)
  simp only [hdef, sq, mul_zero, Finset.sum_const_zero] at h1
  linarith

/-- **Tower collapse at an exact level.** If the inner partition `q` is lumpable, the
composite loss through `f ∘ q` equals the second-level loss of the pushed-forward
path family. (That this family is the path law of the lumped chain is the remaining
step, checked numerically to `1e-15`, not yet formalized.) -/
theorem fisherLoss_markov_tower_of_lumpable {γ : Type*} [Fintype γ] [DecidableEq γ]
    (hP : ∀ x y, 0 < P x y) (hπ : ∀ x, 0 < π x) (hl : Lumpable P q) (f : β → γ) :
    ScoreProjection.fineFisher (pathProb P π T) (pathDeriv P q π b T)
      - ScoreProjection.coarseFisher (macroPath (fun x => f (q x)) T) (pathProb P π T)
          (pathDeriv P q π b T)
      = ScoreProjection.fineFisher (ScoreProjection.blockMass (macroPath q T) (pathProb P π T))
            (ScoreProjection.blockDeriv (macroPath q T) (pathDeriv P q π b T))
        - ScoreProjection.coarseFisher (fun Y : Fin (T + 1) → β => fun t => f (Y t))
            (ScoreProjection.blockMass (macroPath q T) (pathProb P π T))
            (ScoreProjection.blockDeriv (macroPath q T) (pathDeriv P q π b T)) := by
  rw [fisherLoss_markov_chain P q T f π (pathDeriv P q π b T),
    fisherLoss_markov_path_eq_zero_of_lumpable P q π b T hP hπ hl, zero_add]

end Tower

/-! ### The canonical measure-reentry defect -/

open SGC SGC.Renormalization.MeasureReentry in
/-- The local defect coincides with the repository's canonical
`MeasureReentry.defectSq` for a `Partition`. -/
theorem defectSq_eq_measureReentry (Part : Partition V) (hπ : ∀ x, 0 < π x) :
    BlockPairTilt.defectSq Part.quot_map π (blockExit P Part.quot_map)
      = SGC.Renormalization.MeasureReentry.defectSq P Part π := by
  unfold BlockPairTilt.defectSq SGC.Renormalization.MeasureReentry.defectSq
  refine Finset.sum_congr rfl (fun x _ => ?_)
  congr 1
  refine Finset.sum_congr rfl (fun B _ => ?_)
  congr 1
  unfold BlockPairTilt.res SGC.Renormalization.MeasureReentry.residual
  have hexit : ∀ y C, blockExit P Part.quot_map y C = row_sum_block P Part y C := by
    intro y C
    unfold blockExit row_sum_block
    rw [Finset.sum_filter]
  rw [hexit, coarseGenerator_eq_conditional_exit_average P Part hπ]
  congr 1
  unfold BlockPairTilt.Rbar BlockPairTilt.blockMass
  rw [Finset.sum_filter, Finset.sum_filter]
  simp only [hexit]
  have hpb : pi_bar Part π (Part.quot_map x) = ∑ a, if Part.quot_map a = Part.quot_map x then π a else 0 := rfl
  rw [hpb]
  field_simp

open SGC SGC.Renormalization.MeasureReentry in
/-- **Headline.** For a partition, the Fisher information about a block-pair
tilt lost by the macro-observer over `T` steps is at most
`T² · Bmax · 𝔇_π²`, with `𝔇_π²` the canonical measure-reentry defect. -/
theorem fisherLoss_markov_path_le_measureReentry (Part : Partition V)
    (hP : ∀ x y, 0 < P x y) (hrow : ∀ x, ∑ y, P x y = 1) (hπ : ∀ x, 0 < π x)
    (hstat : π ᵥ* P = π) (b : Part.Quot → Part.Quot → ℝ) {Bmax : ℝ}
    (hB : ∀ A, ∑ C, b A C ^ 2 ≤ Bmax) :
    ScoreProjection.fineFisher (pathProb P π T) (pathDeriv P Part.quot_map π b T)
      - ScoreProjection.coarseFisher (macroPath Part.quot_map T) (pathProb P π T)
          (pathDeriv P Part.quot_map π b T)
      ≤ (T : ℝ) ^ 2 * (Bmax * SGC.Renormalization.MeasureReentry.defectSq P Part π) := by
  rw [← defectSq_eq_measureReentry P π Part hπ]
  exact fisherLoss_markov_path_le P Part.quot_map π b T hP hrow hπ hstat hB

end SGC.InformationGeometry.MarkovPathFisher
