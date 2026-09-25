/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.InformationGeometry.FiniteExponentialFamily

/-!
# Fisher information under coarse-graining: exact loss and sufficiency

Let `q : Ω → β` be a deterministic coarse-graining of a finite exponential
family `p_θ`. The coarse observer sees only the pushforward `P_θ(b) = Σ_{q ω = b} p_θ(ω)`.

## Main results

* `pushScore_eq` — the coarse directional score is the conditional
  expectation of the fine score on each fiber.
* `fisher_eq_pushFisher_add` — **exact decomposition**:

    `I_fine(v) = I_coarse(v) + Σ_ω p_θ(ω) (s_v(ω) - E[s_v | q](q ω))²`.

  The information lost by coarse-graining is exactly the within-fiber
  variance of the fine score.
* `pushFisher_le` — Fisher information cannot increase under coarse-graining
  (finite, deterministic data-processing inequality).
* `pushFisher_eq_iff_sufficient` — equality holds iff the coarse variable
  determines the directional statistic on the support: the quotient is
  lossless in direction `v` exactly when it is sufficient in that direction.

## SGC reading (structural, not an identity)

The loss term has the same algebraic form as the measure-reentry residual of
`SGC.Renormalization.MeasureReentry`: a within-block deviation from a
block-conditional average under the conditional measure. Here the averaged
object is the score; there it is the block exit rate. This module proves the
information-side statement only; no equality between the two defects is
claimed.

## Scope

Deterministic coarse-grainings of finite regular exponential families, one
direction at a time. Chentsov's uniqueness theorem and stochastic Markov
morphisms are not proved here.
-/

noncomputable section

namespace SGC.InformationGeometry.FiniteExponentialFamily

open Real Finset

set_option linter.unusedSectionVars false

variable {Ω ι β : Type*} [Fintype Ω] [Fintype ι] [Fintype β] [DecidableEq β]

namespace Family

variable (F : Family Ω ι) (q : Ω → β)

/-- Centered directional statistic, the fine score on the support. -/
def centered (θ v : ι → ℝ) (ω : Ω) : ℝ := F.dirStat v ω - F.expect θ (F.dirStat v)

/-- Pushforward (coarse) probability of a block. -/
def pushProb (θ : ι → ℝ) (b : β) : ℝ :=
  ∑ ω ∈ univ.filter (fun ω => q ω = b), F.prob θ ω

/-- Coarse directional score. -/
def pushScore (θ v : ι → ℝ) (b : β) : ℝ :=
  deriv (fun s : ℝ => log (F.pushProb q (θ + s • v) b)) 0

/-- Coarse Fisher information in direction `v`. -/
def pushFisher (θ v : ι → ℝ) : ℝ := ∑ b, F.pushProb q θ b * F.pushScore q θ v b ^ 2

/-- Conditional expectation of the fine score on the block `b`. -/
def condMean (θ v : ι → ℝ) (b : β) : ℝ :=
  (∑ ω ∈ univ.filter (fun ω => q ω = b), F.prob θ ω * F.centered θ v ω) / F.pushProb q θ b

lemma pushProb_nonneg (θ : ι → ℝ) (b : β) : 0 ≤ F.pushProb q θ b :=
  Finset.sum_nonneg (fun ω _ => F.prob_nonneg θ ω)

lemma prob_le_pushProb (θ : ι → ℝ) (ω : Ω) : F.prob θ ω ≤ F.pushProb q θ (q ω) :=
  Finset.single_le_sum (f := fun ω => F.prob θ ω) (fun ω' _ => F.prob_nonneg θ ω')
    (by simp)

/-- Derivative of a single model probability along `v`. -/
lemma hasDerivAt_prob_line (θ v : ι → ℝ) (ω : Ω) :
    HasDerivAt (fun s : ℝ => F.prob (θ + s • v) ω) (F.prob θ ω * F.centered θ v ω) 0 := by
  have hw : HasDerivAt (fun s : ℝ => F.weight (θ + s • v) ω) (F.weight θ ω * F.dirStat v ω) 0 := by
    have hfun : (fun s : ℝ => F.weight (θ + s • v) ω)
        = fun s : ℝ => F.base ω * exp (pair θ (F.stat ω) + s * F.dirStat v ω) := by
      funext s
      exact F.weight_line θ v s ω
    rw [hfun]
    have h := (((hasDerivAt_mul_const (x := (0 : ℝ)) (F.dirStat v ω)).const_add
      (pair θ (F.stat ω))).exp).const_mul (F.base ω)
    convert h using 1
    simp [weight]
    ring
  have hZ := F.hasDerivAt_partition_line θ v 0
  have hZ0 : F.partition (θ + (0 : ℝ) • v) ≠ 0 := (F.partition_pos _).ne'
  have hq := hw.fun_div hZ hZ0
  convert hq using 1
  simp only [zero_smul, add_zero]
  unfold centered prob
  rw [F.expect_eq_div]
  have hZp := F.partition_pos θ
  unfold partition at hZp ⊢
  field_simp

lemma hasDerivAt_pushProb (θ v : ι → ℝ) (b : β) :
    HasDerivAt (fun s : ℝ => F.pushProb q (θ + s • v) b)
      (∑ ω ∈ univ.filter (fun ω => q ω = b), F.prob θ ω * F.centered θ v ω) 0 := by
  unfold pushProb
  exact HasDerivAt.fun_sum (fun ω _ => F.hasDerivAt_prob_line θ v ω)

/-- **Coarse score = conditional expectation of the fine score.** -/
lemma pushScore_eq (θ v : ι → ℝ) {b : β} (hb : 0 < F.pushProb q θ b) :
    F.pushScore q θ v b = F.condMean q θ v b := by
  have hb' : F.pushProb q (θ + (0 : ℝ) • v) b ≠ 0 := by simpa using hb.ne'
  have h := (F.hasDerivAt_pushProb q θ v b).log hb'
  unfold pushScore
  rw [h.deriv]
  simp [condMean]

/-- Per-fiber decomposition. -/
lemma fiber_identity (θ v : ι → ℝ) (b : β) :
    ∑ ω ∈ univ.filter (fun ω => q ω = b), F.prob θ ω * F.centered θ v ω ^ 2
      = F.pushProb q θ b * F.pushScore q θ v b ^ 2
        + ∑ ω ∈ univ.filter (fun ω => q ω = b),
            F.prob θ ω * (F.centered θ v ω - F.condMean q θ v (q ω)) ^ 2 := by
  have hcm : ∀ ω ∈ univ.filter (fun ω => q ω = b),
      F.prob θ ω * (F.centered θ v ω - F.condMean q θ v (q ω)) ^ 2
        = F.prob θ ω * (F.centered θ v ω - F.condMean q θ v b) ^ 2 := by
    intro ω hω
    rw [(Finset.mem_filter.mp hω).2]
  rw [Finset.sum_congr rfl hcm]
  rcases (F.pushProb_nonneg q θ b).lt_or_eq with hpos | hzero
  · rw [F.pushScore_eq q θ v hpos]
    set m := F.condMean q θ v b with hm
    have hS : ∑ ω ∈ univ.filter (fun ω => q ω = b), F.prob θ ω * F.centered θ v ω
        = m * F.pushProb q θ b := by
      rw [hm]
      unfold condMean
      field_simp
    have hexp : ∀ ω, F.prob θ ω * (F.centered θ v ω - m) ^ 2
        = F.prob θ ω * F.centered θ v ω ^ 2 - 2 * m * (F.prob θ ω * F.centered θ v ω)
          + m ^ 2 * F.prob θ ω := fun ω => by ring
    rw [Finset.sum_congr rfl (fun ω _ => hexp ω), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hS]
    unfold pushProb
    ring
  · have hz : ∀ ω ∈ univ.filter (fun ω => q ω = b), F.prob θ ω = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun ω _ => F.prob_nonneg θ ω)).mp hzero.symm
    rw [← hzero]
    simp only [zero_mul, zero_add]
    exact Finset.sum_congr rfl (fun ω hω => by rw [hz ω hω, zero_mul, zero_mul])

/-- **Exact decomposition of Fisher information under coarse-graining.** -/
theorem fisher_eq_pushFisher_add (θ v : ι → ℝ) :
    F.fisher θ v = F.pushFisher q θ v
      + ∑ ω, F.prob θ ω * (F.centered θ v ω - F.condMean q θ v (q ω)) ^ 2 := by
  rw [F.fisher_eq_variance]
  have hvar : F.variance θ (F.dirStat v) = ∑ ω, F.prob θ ω * F.centered θ v ω ^ 2 := rfl
  rw [hvar, ← Finset.sum_fiberwise Finset.univ q,
    ← Finset.sum_fiberwise Finset.univ q
      (fun ω => F.prob θ ω * (F.centered θ v ω - F.condMean q θ v (q ω)) ^ 2)]
  unfold pushFisher
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun b _ => F.fiber_identity q θ v b)

/-- **Fisher information cannot increase under coarse-graining.** -/
theorem pushFisher_le (θ v : ι → ℝ) : F.pushFisher q θ v ≤ F.fisher θ v := by
  rw [F.fisher_eq_pushFisher_add q]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg (fun ω _ => mul_nonneg (F.prob_nonneg θ ω) (sq_nonneg _)))

/-- **Losslessness iff sufficiency.** Coarse-graining preserves the Fisher
information in direction `v` iff the coarse variable determines the
directional statistic on the support. -/
theorem pushFisher_eq_iff_sufficient (θ v : ι → ℝ) :
    F.pushFisher q θ v = F.fisher θ v ↔
      ∃ g : β → ℝ, ∀ ω, 0 < F.base ω → F.dirStat v ω = g (q ω) := by
  have hres : ∀ ω, 0 ≤ F.prob θ ω * (F.centered θ v ω - F.condMean q θ v (q ω)) ^ 2 :=
    fun ω => mul_nonneg (F.prob_nonneg θ ω) (sq_nonneg _)
  rw [F.fisher_eq_pushFisher_add q]
  constructor
  · intro h
    have h0 : ∑ ω, F.prob θ ω * (F.centered θ v ω - F.condMean q θ v (q ω)) ^ 2 = 0 := by
      linarith
    refine ⟨fun b => F.condMean q θ v b + F.expect θ (F.dirStat v), fun ω hω => ?_⟩
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun ω _ => hres ω)).mp h0 ω
      (Finset.mem_univ ω)
    rcases mul_eq_zero.mp hterm with hp | hs
    · exact absurd hp (F.prob_pos θ hω).ne'
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hs
      unfold centered at this
      linarith
  · rintro ⟨g, hg⟩
    suffices hz : ∀ ω, F.prob θ ω * (F.centered θ v ω - F.condMean q θ v (q ω)) ^ 2 = 0 by
      rw [Finset.sum_eq_zero (fun ω _ => hz ω), add_zero]
    intro ω
    by_cases hω : 0 < F.base ω
    · have hP : 0 < F.pushProb q θ (q ω) :=
        lt_of_lt_of_le (F.prob_pos θ hω) (F.prob_le_pushProb q θ ω)
      set E := F.expect θ (F.dirStat v)
      have hconst : ∀ ω' ∈ univ.filter (fun ω' => q ω' = q ω),
          F.prob θ ω' * F.centered θ v ω' = F.prob θ ω' * (g (q ω) - E) := by
        intro ω' hω'
        by_cases hb : 0 < F.base ω'
        · unfold centered
          rw [hg ω' hb, (Finset.mem_filter.mp hω').2]
        · rw [F.prob_eq_zero θ hb, zero_mul, zero_mul]
      have hm : F.condMean q θ v (q ω) = g (q ω) - E := by
        unfold condMean
        rw [Finset.sum_congr rfl hconst, ← Finset.sum_mul]
        change F.pushProb q θ (q ω) * (g (q ω) - E) / F.pushProb q θ (q ω) = _
        field_simp
      unfold centered
      rw [hm, hg ω hω]
      ring
    · rw [F.prob_eq_zero θ hω, zero_mul]

end Family

end SGC.InformationGeometry.FiniteExponentialFamily
