/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Algebra.BigOperators.Field

/-!
# Finite exponential families: Fisher information is covariance

This module supplies, on a finite sample space, the step that
`FisherNoetherBridge` explicitly deferred: for an exponential family

  `p_θ(ω) = h(ω) exp ⟨θ, T ω⟩ / Z(θ)`,

the Fisher information in natural coordinates is the covariance of the
sufficient statistic, and it is the second directional derivative of the
log-partition function. Everything is proved from the definitions; no
measure theory and no axioms beyond Lean's standard three are used.

## Main results

* `hasDerivAt_logProb_line` — the directional score of `log p_θ(ω)` along `v`
  is the centered statistic `⟨v, T ω⟩ - E_θ ⟨v, T⟩` (on the support).
* `fisher_eq_variance` — expected squared score = `Var_θ ⟨v, T⟩`.
* `logPartition_second_deriv` — `d²/ds² log Z(θ + s v) |_{s=0} = Var_θ ⟨v, T⟩`.
* `variance_eq_zero_iff` and `prob_line_invariant_iff` — the Fisher kernel is
  exactly the set of directions whose statistic is constant on the support of
  the base measure, and those are exactly the directions along which the
  whole distribution is unchanged for every step size. The kernel is
  independent of `θ`: it is a global non-identifiability quotient.
* `categorical_fisher` — for the full categorical family, the Fisher form at a
  strictly positive `π` is the `π`-weighted centered square norm.
* `spin_square_fisher_null` / `spin_linear_fisher_pos` — on `±1` spins the
  lifted square `x²` is Fisher-null in every direction, while the linear
  statistic `x` is not.

## Scope

This is a finite, regular exponential family in natural coordinates, with
covariance taken under the model distribution `p_θ`. It does not identify an
empirical covariance of data with Fisher information, and the kernel theorem
is an identifiability statement, not a Noether theorem: no group action or
conserved quantity of a dynamics is involved.
-/

noncomputable section

namespace SGC.InformationGeometry.FiniteExponentialFamily

open Real Finset

set_option linter.unusedSectionVars false

/-- A finite exponential family with sufficient statistic `stat` and base
measure `base` (nonnegative, not identically zero). -/
structure Family (Ω ι : Type*) where
  stat : Ω → ι → ℝ
  base : Ω → ℝ
  base_nonneg : ∀ ω, 0 ≤ base ω
  base_pos : ∃ ω, 0 < base ω

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

/-- Pairing of a natural parameter with a statistic value. -/
def pair (θ t : ι → ℝ) : ℝ := ∑ i, θ i * t i

lemma pair_line (θ v t : ι → ℝ) (s : ℝ) :
    pair (θ + s • v) t = pair θ t + s * pair v t := by
  unfold pair
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => by ring)

namespace Family

variable (F : Family Ω ι)

/-- The statistic in direction `v`: `⟨v, T ω⟩`. -/
def dirStat (v : ι → ℝ) (ω : Ω) : ℝ := pair v (F.stat ω)

/-- Unnormalized weight `h(ω) exp ⟨θ, T ω⟩`. -/
def weight (θ : ι → ℝ) (ω : Ω) : ℝ := F.base ω * exp (pair θ (F.stat ω))

/-- Partition function. -/
def partition (θ : ι → ℝ) : ℝ := ∑ ω, F.weight θ ω

/-- Log-partition function. -/
def logPartition (θ : ι → ℝ) : ℝ := log (F.partition θ)

/-- Model probability. -/
def prob (θ : ι → ℝ) (ω : Ω) : ℝ := F.weight θ ω / F.partition θ

/-- Expectation under the model. -/
def expect (θ : ι → ℝ) (f : Ω → ℝ) : ℝ := ∑ ω, F.prob θ ω * f ω

/-- Variance under the model. -/
def variance (θ : ι → ℝ) (f : Ω → ℝ) : ℝ :=
  F.expect θ (fun ω => (f ω - F.expect θ f) ^ 2)

/-- Directional score: derivative of `log p` along `v` at `θ`. -/
def score (θ v : ι → ℝ) (ω : Ω) : ℝ :=
  deriv (fun s : ℝ => log (F.prob (θ + s • v) ω)) 0

/-- Fisher information quadratic form: expected squared directional score. -/
def fisher (θ v : ι → ℝ) : ℝ := ∑ ω, F.prob θ ω * F.score θ v ω ^ 2

/-- The statistic in direction `v` is constant on the support of the base
measure. -/
def SupportInvariant (v : ι → ℝ) : Prop :=
  ∃ c : ℝ, ∀ ω, 0 < F.base ω → F.dirStat v ω = c

/-! ### Positivity and normalization -/

lemma weight_nonneg (θ : ι → ℝ) (ω : Ω) : 0 ≤ F.weight θ ω :=
  mul_nonneg (F.base_nonneg ω) (exp_pos _).le

lemma weight_pos (θ : ι → ℝ) {ω : Ω} (h : 0 < F.base ω) : 0 < F.weight θ ω :=
  mul_pos h (exp_pos _)

lemma weight_eq_zero (θ : ι → ℝ) {ω : Ω} (h : ¬ 0 < F.base ω) : F.weight θ ω = 0 := by
  have : F.base ω = 0 := le_antisymm (not_lt.mp h) (F.base_nonneg ω)
  simp [weight, this]

lemma partition_pos (θ : ι → ℝ) : 0 < F.partition θ := by
  obtain ⟨ω₀, h₀⟩ := F.base_pos
  exact lt_of_lt_of_le (F.weight_pos θ h₀)
    (Finset.single_le_sum (fun ω _ => F.weight_nonneg θ ω) (Finset.mem_univ ω₀))

lemma prob_nonneg (θ : ι → ℝ) (ω : Ω) : 0 ≤ F.prob θ ω :=
  div_nonneg (F.weight_nonneg θ ω) (F.partition_pos θ).le

lemma prob_pos (θ : ι → ℝ) {ω : Ω} (h : 0 < F.base ω) : 0 < F.prob θ ω :=
  div_pos (F.weight_pos θ h) (F.partition_pos θ)

lemma prob_eq_zero (θ : ι → ℝ) {ω : Ω} (h : ¬ 0 < F.base ω) : F.prob θ ω = 0 := by
  simp [prob, F.weight_eq_zero θ h]

lemma sum_prob (θ : ι → ℝ) : ∑ ω, F.prob θ ω = 1 := by
  unfold prob
  rw [← Finset.sum_div]
  exact div_self (F.partition_pos θ).ne'

lemma expect_eq_div (θ : ι → ℝ) (f : Ω → ℝ) :
    F.expect θ f = (∑ ω, F.weight θ ω * f ω) / F.partition θ := by
  unfold expect prob
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun ω _ => by ring)

lemma variance_eq (θ : ι → ℝ) (f : Ω → ℝ) :
    F.variance θ f = F.expect θ (fun ω => f ω * f ω) - F.expect θ f ^ 2 := by
  unfold variance
  set m := F.expect θ f with hm
  have hs := F.sum_prob θ
  unfold expect at hm ⊢
  have : ∀ ω, F.prob θ ω * (f ω - m) ^ 2
      = F.prob θ ω * (f ω * f ω) - 2 * m * (F.prob θ ω * f ω) + m ^ 2 * F.prob θ ω :=
    fun ω => by ring
  rw [Finset.sum_congr rfl (fun ω _ => this ω), Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs, ← hm]
  ring

lemma expect_eq_const (θ : ι → ℝ) {f : Ω → ℝ} {c : ℝ}
    (hf : ∀ ω, 0 < F.base ω → f ω = c) : F.expect θ f = c := by
  unfold expect
  have : ∀ ω, F.prob θ ω * f ω = F.prob θ ω * c := by
    intro ω
    by_cases h : 0 < F.base ω
    · rw [hf ω h]
    · rw [F.prob_eq_zero θ h, zero_mul, zero_mul]
  rw [Finset.sum_congr rfl (fun ω _ => this ω), ← Finset.sum_mul, F.sum_prob θ, one_mul]

/-! ### Derivatives along a line in natural coordinates -/

lemma weight_line (θ v : ι → ℝ) (s : ℝ) (ω : Ω) :
    F.weight (θ + s • v) ω
      = F.base ω * exp (pair θ (F.stat ω) + s * F.dirStat v ω) := by
  simp only [weight, dirStat, pair_line]

/-- Derivative of a weighted sum `∑ w_{θ+sv}(ω) g(ω)` along the line. -/
lemma hasDerivAt_weightedSum (θ v : ι → ℝ) (g : Ω → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∑ ω, F.weight (θ + s • v) ω * g ω)
      (∑ ω, F.weight (θ + t • v) ω * F.dirStat v ω * g ω) t := by
  have hfun : (fun s : ℝ => ∑ ω, F.weight (θ + s • v) ω * g ω)
      = fun s : ℝ => ∑ ω, F.base ω * g ω * exp (pair θ (F.stat ω) + s * F.dirStat v ω) := by
    funext s
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    rw [F.weight_line]
    ring
  rw [hfun]
  refine HasDerivAt.fun_sum (u := Finset.univ)
    (A := fun ω s => F.base ω * g ω * exp (pair θ (F.stat ω) + s * F.dirStat v ω))
    (A' := fun ω => F.weight (θ + t • v) ω * F.dirStat v ω * g ω) (fun ω _ => ?_)
  have h := (((hasDerivAt_mul_const (x := t) (F.dirStat v ω)).const_add
    (pair θ (F.stat ω))).exp).const_mul (F.base ω * g ω)
  convert h using 1
  simp only [F.weight_line]
  ring

lemma hasDerivAt_partition_line (θ v : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F.partition (θ + s • v))
      (∑ ω, F.weight (θ + t • v) ω * F.dirStat v ω) t := by
  have h := F.hasDerivAt_weightedSum θ v (fun _ => 1) t
  simp only [mul_one] at h
  exact h

/-- First derivative of the log-partition function along `v` is the mean of
the directional statistic. -/
lemma hasDerivAt_logPartition_line (θ v : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F.logPartition (θ + s • v))
      (F.expect (θ + t • v) (F.dirStat v)) t := by
  have h := (F.hasDerivAt_partition_line θ v t).log (F.partition_pos (θ + t • v)).ne'
  rw [F.expect_eq_div]
  exact h

/-- **Score identity.** On the support, the directional score of the model
log-likelihood is the centered directional statistic. -/
theorem hasDerivAt_logProb_line (θ v : ι → ℝ) {ω : Ω} (hω : 0 < F.base ω) :
    HasDerivAt (fun s : ℝ => log (F.prob (θ + s • v) ω))
      (F.dirStat v ω - F.expect θ (F.dirStat v)) 0 := by
  have hfun : (fun s : ℝ => log (F.prob (θ + s • v) ω))
      = fun s : ℝ => log (F.base ω) + (pair θ (F.stat ω) + s * F.dirStat v ω)
          - F.logPartition (θ + s • v) := by
    funext s
    unfold prob logPartition
    rw [Real.log_div (F.weight_pos _ hω).ne' (F.partition_pos _).ne', F.weight_line,
      Real.log_mul hω.ne' (exp_pos _).ne', Real.log_exp]
  rw [hfun]
  have hlin : HasDerivAt (fun s : ℝ => log (F.base ω) + (pair θ (F.stat ω) + s * F.dirStat v ω))
      (F.dirStat v ω) 0 :=
    ((hasDerivAt_mul_const (F.dirStat v ω)).const_add _).const_add _
  convert hlin.sub (F.hasDerivAt_logPartition_line θ v 0) using 1
  simp

lemma score_eq (θ v : ι → ℝ) {ω : Ω} (hω : 0 < F.base ω) :
    F.score θ v ω = F.dirStat v ω - F.expect θ (F.dirStat v) :=
  (F.hasDerivAt_logProb_line θ v hω).deriv

/-- **Fisher information equals covariance of the sufficient statistic**
(directional form): the expected squared score is `Var_θ ⟨v, T⟩`. -/
theorem fisher_eq_variance (θ v : ι → ℝ) :
    F.fisher θ v = F.variance θ (F.dirStat v) := by
  unfold fisher variance expect
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  by_cases h : 0 < F.base ω
  · rw [F.score_eq θ v h]
    rfl
  · rw [F.prob_eq_zero θ h, zero_mul, zero_mul]

/-- Derivative of a model expectation along `v`: the covariance of `f` with
the directional statistic. -/
lemma hasDerivAt_expect_line (θ v : ι → ℝ) (f : Ω → ℝ) :
    HasDerivAt (fun s : ℝ => F.expect (θ + s • v) f)
      (F.expect θ (fun ω => f ω * F.dirStat v ω)
        - F.expect θ f * F.expect θ (F.dirStat v)) 0 := by
  have hN := F.hasDerivAt_weightedSum θ v f 0
  have hZ := F.hasDerivAt_partition_line θ v 0
  have hZ0 : F.partition (θ + (0 : ℝ) • v) ≠ 0 := (F.partition_pos _).ne'
  have hq := hN.fun_div hZ hZ0
  have hfun : (fun s : ℝ => F.expect (θ + s • v) f)
      = fun s : ℝ => (∑ ω, F.weight (θ + s • v) ω * f ω) / F.partition (θ + s • v) := by
    funext s
    exact F.expect_eq_div _ f
  rw [hfun]
  convert hq using 1
  simp only [zero_smul, add_zero]
  rw [F.expect_eq_div, F.expect_eq_div, F.expect_eq_div]
  have hZp := F.partition_pos θ
  unfold partition at hZp ⊢
  field_simp
  have e1 : ∀ ω, F.weight θ ω * F.dirStat v ω * f ω = F.weight θ ω * (f ω * F.dirStat v ω) :=
    fun ω => by ring
  rw [Finset.sum_congr rfl (fun ω _ => e1 ω)]
  ring

/-- **Hessian of the log-partition function is the Fisher information**
(directional form). -/
theorem logPartition_second_deriv (θ v : ι → ℝ) :
    deriv (fun s : ℝ => deriv (fun r : ℝ => F.logPartition (θ + r • v)) s) 0
      = F.variance θ (F.dirStat v) := by
  have hfirst : (fun s : ℝ => deriv (fun r : ℝ => F.logPartition (θ + r • v)) s)
      = fun s : ℝ => F.expect (θ + s • v) (F.dirStat v) := by
    funext s
    exact (F.hasDerivAt_logPartition_line θ v s).deriv
  rw [hfirst, (F.hasDerivAt_expect_line θ v (F.dirStat v)).deriv, F.variance_eq]
  ring

/-! ### The Fisher kernel is exact, global non-identifiability -/

/-- **Kernel theorem (variance form).** The Fisher form vanishes in direction
`v` iff the directional statistic is constant on the support. The right-hand
side does not mention `θ`. -/
theorem variance_eq_zero_iff (θ v : ι → ℝ) :
    F.variance θ (F.dirStat v) = 0 ↔ F.SupportInvariant v := by
  constructor
  · intro h0
    refine ⟨F.expect θ (F.dirStat v), fun ω hω => ?_⟩
    unfold variance expect at h0
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun ω _ =>
      mul_nonneg (F.prob_nonneg θ ω) (sq_nonneg _))).mp h0 ω (Finset.mem_univ ω)
    rcases mul_eq_zero.mp hterm with hp | hs
    · exact absurd hp (F.prob_pos θ hω).ne'
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hs
      unfold expect
      linarith
  · rintro ⟨c, hc⟩
    have hm : F.expect θ (F.dirStat v) = c := F.expect_eq_const θ hc
    unfold variance
    rw [hm]
    exact F.expect_eq_const θ (fun ω hω => by rw [hc ω hω, sub_self]; ring)

theorem fisher_eq_zero_iff (θ v : ι → ℝ) :
    F.fisher θ v = 0 ↔ F.SupportInvariant v := by
  rw [F.fisher_eq_variance]
  exact F.variance_eq_zero_iff θ v

/-- **Kernel theorem (identifiability form).** The model distribution is
unchanged along the entire line `θ + t v` iff `v` is a support invariant.
Fisher-null directions are therefore globally, not just locally,
unidentifiable. -/
theorem prob_line_invariant_iff (θ v : ι → ℝ) :
    (∀ t : ℝ, F.prob (θ + t • v) = F.prob θ) ↔ F.SupportInvariant v := by
  constructor
  · intro hline
    refine ⟨log (F.partition (θ + (1 : ℝ) • v) / F.partition θ), fun ω hω => ?_⟩
    have h := congrFun (hline 1) ω
    unfold prob at h
    rw [F.weight_line, one_mul] at h
    have hZ0 := F.partition_pos θ
    have hZ1 := F.partition_pos (θ + (1 : ℝ) • v)
    rw [div_eq_div_iff hZ1.ne' hZ0.ne'] at h
    have h2 : F.weight θ ω * (exp (F.dirStat v ω) * F.partition θ)
        = F.weight θ ω * F.partition (θ + (1 : ℝ) • v) := by
      rw [exp_add] at h
      unfold weight at h ⊢
      linear_combination h
    have h3 := mul_left_cancel₀ (F.weight_pos θ hω).ne' h2
    rw [← h3, mul_div_assoc, div_self hZ0.ne', mul_one, Real.log_exp]
  · rintro ⟨c, hc⟩ t
    have hw : ∀ ω, F.weight (θ + t • v) ω = F.weight θ ω * exp (t * c) := by
      intro ω
      by_cases h : 0 < F.base ω
      · rw [F.weight_line, hc ω h, exp_add]
        unfold weight
        ring
      · rw [F.weight_eq_zero _ h, F.weight_eq_zero _ h, zero_mul]
    have hZ : F.partition (θ + t • v) = F.partition θ * exp (t * c) := by
      unfold partition
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun ω _ => hw ω)
    funext ω
    unfold prob
    rw [hw, hZ, mul_div_mul_right _ _ (exp_pos _).ne']

/-! ### Specializations -/

section Categorical

variable (Ω) [DecidableEq Ω] [Nonempty Ω]

/-- The full categorical family on `Ω`: indicator statistics, unit base. -/
def categorical : Family Ω Ω where
  stat ω i := if ω = i then 1 else 0
  base _ := 1
  base_nonneg _ := zero_le_one
  base_pos := ⟨Classical.arbitrary Ω, one_pos⟩

variable {Ω}

lemma categorical_dirStat (v : Ω → ℝ) (ω : Ω) : (categorical Ω).dirStat v ω = v ω := by
  simp [dirStat, pair, categorical]

lemma categorical_prob (π : Ω → ℝ) (hπ : ∀ ω, 0 < π ω) (hsum : ∑ ω, π ω = 1) :
    (categorical Ω).prob (fun i => log (π i)) = π := by
  have hw : ∀ ω, (categorical Ω).weight (fun i => log (π i)) ω = π ω := by
    intro ω
    simp [weight, pair, categorical, Real.exp_log (hπ ω)]
  funext ω
  simp only [prob, partition, hw, hsum, div_one]

/-- For the full categorical family at a strictly positive `π`, the Fisher
form is the `π`-weighted centered square norm: the weighted `L²(π)` geometry
of mean-zero perturbations is Fisher geometry. -/
theorem categorical_fisher (π : Ω → ℝ) (hπ : ∀ ω, 0 < π ω) (hsum : ∑ ω, π ω = 1)
    (v : Ω → ℝ) :
    (categorical Ω).fisher (fun i => log (π i)) v
      = ∑ ω, π ω * (v ω - ∑ ω', π ω' * v ω') ^ 2 := by
  rw [fisher_eq_variance]
  unfold variance expect
  rw [categorical_prob π hπ hsum]
  simp only [categorical_dirStat]

end Categorical

section Spin

/-- The `±1` value of a spin. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

lemma spin_sq (b : Bool) : spin b ^ 2 = 1 := by cases b <;> norm_num [spin]

/-- Family on one spin with the lifted square statistic `x ⊗ x = x²`. -/
def spinSquare : Family Bool Unit where
  stat b _ := spin b ^ 2
  base _ := 1
  base_nonneg _ := zero_le_one
  base_pos := ⟨true, one_pos⟩

/-- Family on one spin with the linear statistic `x`. -/
def spinLinear : Family Bool Unit where
  stat b _ := spin b
  base _ := 1
  base_nonneg _ := zero_le_one
  base_pos := ⟨true, one_pos⟩

/-- **Lifted-square degeneracy.** On `±1` spins the diagonal lift `x²` is
constant, so every direction is Fisher-null at every parameter. Diagonal
entries of `x ⊗ x` on spin variables are identifiability artifacts. -/
theorem spin_square_fisher_null (θ v : Unit → ℝ) : spinSquare.fisher θ v = 0 := by
  rw [fisher_eq_zero_iff]
  exact ⟨v (), fun b _ => by simp [dirStat, pair, spinSquare, spin_sq]⟩

/-- Non-vacuity witness: the linear statistic has unit Fisher information at
`θ = 0`. -/
theorem spin_linear_fisher_pos : spinLinear.fisher 0 (fun _ => 1) = 1 := by
  rw [fisher_eq_variance, variance_eq]
  simp [expect, prob, partition, weight, dirStat, pair, spinLinear, spin]
  norm_num

end Spin

end Family

end SGC.InformationGeometry.FiniteExponentialFamily
