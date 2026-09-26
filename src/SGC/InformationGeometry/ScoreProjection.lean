/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Score projection: Fisher loss under any deterministic coarse-graining

A parameterization-free version of `FisherCoarseGraining`. On a finite sample
space (for example, the set of all paths of a Markov chain of length `T`),
let `p ω > 0` be the model probabilities at a parameter value and `d ω` their
derivatives along a direction. The fine score is `s = d / p` and the coarse
score of a block is `(Σ_block d) / (Σ_block p)`.

## Main results

* `score_eq_logDeriv` — `d / p` is the derivative of `log p`.
* `fisherLoss_eq` — fine Fisher minus coarse Fisher equals the `p`-weighted
  squared distance of the fine score from its block average.
* `fisherLoss_le` — **best-approximation bound**: for every block function
  `g`, the loss is at most `Σ p (s - g ∘ q)²`. Any block-measurable surrogate
  score therefore upper-bounds the information lost.
* `coarseFisher_le` — Fisher information cannot increase.

The best-approximation bound is the abstract step behind the closure-defect
bound for block-pair tilts of Markov chains: the surrogate replaces each
state's block exit rates with their stationary block averages. No exponential
family structure is assumed here.
-/

noncomputable section

namespace SGC.InformationGeometry.ScoreProjection

open Finset

set_option linter.unusedSectionVars false

variable {Ω β : Type*} [Fintype Ω] [Fintype β] [DecidableEq β]

/-- The fine score of a positive family at a point: `d / p`. -/
theorem score_eq_logDeriv {f : ℝ → ℝ} {d x : ℝ} (hf : HasDerivAt f d x) (hpos : 0 < f x) :
    HasDerivAt (fun y => Real.log (f y)) (d / f x) x :=
  hf.log hpos.ne'

variable (q : Ω → β) (p d : Ω → ℝ)

/-- Fine Fisher information `Σ d² / p`. -/
def fineFisher : ℝ := ∑ ω, d ω ^ 2 / p ω

/-- Block mass. -/
def blockMass (b : β) : ℝ := ∑ ω ∈ univ.filter (fun ω => q ω = b), p ω

/-- Block derivative. -/
def blockDeriv (b : β) : ℝ := ∑ ω ∈ univ.filter (fun ω => q ω = b), d ω

/-- Coarse Fisher information `Σ_b (Σ_b d)² / (Σ_b p)`. -/
def coarseFisher : ℝ := ∑ b, blockDeriv q d b ^ 2 / blockMass q p b

/-- Coarse score (block average of the fine score). -/
def coarseScore (b : β) : ℝ := blockDeriv q d b / blockMass q p b

variable {p}

lemma fiber_sq_expand (hp : ∀ ω, 0 < p ω) (b : β) (c : ℝ) :
    ∑ ω ∈ univ.filter (fun ω => q ω = b), p ω * (d ω / p ω - c) ^ 2
      = ∑ ω ∈ univ.filter (fun ω => q ω = b), d ω ^ 2 / p ω
        - 2 * c * blockDeriv q d b + c ^ 2 * blockMass q p b := by
  unfold blockDeriv blockMass
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  have := (hp ω).ne'
  field_simp
  ring

lemma blockDeriv_eq_zero_of_mass (hp : ∀ ω, 0 < p ω) {b : β} (h : blockMass q p b = 0) :
    blockDeriv q d b = 0 := by
  have hempty : univ.filter (fun ω => q ω = b) = ∅ := by
    by_contra hne
    obtain ⟨ω, hω⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have : 0 < blockMass q p b :=
      Finset.sum_pos (fun ω _ => hp ω) ⟨ω, hω⟩
    linarith
  simp [blockDeriv, hempty]

/-- Per-block identity: squared distance to any constant `c` splits into the
block's Fisher loss plus `M (m - c)²`. -/
lemma fiber_identity (hp : ∀ ω, 0 < p ω) (b : β) (c : ℝ) :
    ∑ ω ∈ univ.filter (fun ω => q ω = b), p ω * (d ω / p ω - c) ^ 2
      = (∑ ω ∈ univ.filter (fun ω => q ω = b), d ω ^ 2 / p ω)
        - blockDeriv q d b ^ 2 / blockMass q p b
        + blockMass q p b * (coarseScore q p d b - c) ^ 2 := by
  rw [fiber_sq_expand q d hp b c]
  unfold coarseScore
  rcases eq_or_ne (blockMass q p b) 0 with hM | hM
  · rw [hM, blockDeriv_eq_zero_of_mass q d hp hM]
    simp
  · field_simp
    ring

lemma sum_fibers (f : Ω → ℝ) :
    ∑ ω, f ω = ∑ b, ∑ ω ∈ univ.filter (fun ω => q ω = b), f ω :=
  (Finset.sum_fiberwise univ q f).symm

/-- **Exact Fisher loss under coarse-graining.** -/
theorem fisherLoss_eq (hp : ∀ ω, 0 < p ω) :
    fineFisher p d - coarseFisher q p d
      = ∑ ω, p ω * (d ω / p ω - coarseScore q p d (q ω)) ^ 2 := by
  unfold fineFisher coarseFisher
  rw [sum_fibers q (fun ω => d ω ^ 2 / p ω),
    sum_fibers q (fun ω => p ω * (d ω / p ω - coarseScore q p d (q ω)) ^ 2),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have hc : ∀ ω ∈ univ.filter (fun ω => q ω = b),
      p ω * (d ω / p ω - coarseScore q p d (q ω)) ^ 2
        = p ω * (d ω / p ω - coarseScore q p d b) ^ 2 := by
    intro ω hω
    rw [(Finset.mem_filter.mp hω).2]
  rw [Finset.sum_congr rfl hc, fiber_identity q d hp b]
  simp

/-- **Best-approximation bound.** Any block-measurable surrogate score `g ∘ q`
upper-bounds the Fisher information lost by coarse-graining. -/
theorem fisherLoss_le (hp : ∀ ω, 0 < p ω) (g : β → ℝ) :
    fineFisher p d - coarseFisher q p d ≤ ∑ ω, p ω * (d ω / p ω - g (q ω)) ^ 2 := by
  unfold fineFisher coarseFisher
  rw [sum_fibers q (fun ω => d ω ^ 2 / p ω),
    sum_fibers q (fun ω => p ω * (d ω / p ω - g (q ω)) ^ 2), ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum (fun b _ => ?_)
  have hc : ∀ ω ∈ univ.filter (fun ω => q ω = b),
      p ω * (d ω / p ω - g (q ω)) ^ 2 = p ω * (d ω / p ω - g b) ^ 2 := by
    intro ω hω
    rw [(Finset.mem_filter.mp hω).2]
  rw [Finset.sum_congr rfl hc, fiber_identity q d hp b]
  have hM : 0 ≤ blockMass q p b := Finset.sum_nonneg (fun ω _ => (hp ω).le)
  nlinarith [mul_nonneg hM (sq_nonneg (coarseScore q p d b - g b))]

/-- Block average of a function under `p`. -/
def blockAvg (w e : Ω → ℝ) (b : β) : ℝ :=
  (∑ ω ∈ univ.filter (fun ω => q ω = b), w ω * e ω) / blockMass q w b

/-- **Conditional-variance form of the loss.** If the fine score splits as a
block-measurable part minus an error `e`, the Fisher loss is exactly the
`p`-weighted within-block variance of `e`: the part of `e` that the coarse
variable cannot predict. -/
theorem fisherLoss_eq_condVar (hp : ∀ ω, 0 < p ω) (g e : Ω → ℝ) (g' : β → ℝ)
    (hg : ∀ ω, g ω = g' (q ω)) (hs : ∀ ω, d ω / p ω = g ω - e ω) :
    fineFisher p d - coarseFisher q p d
      = ∑ ω, p ω * (e ω - blockAvg q p e (q ω)) ^ 2 := by
  rw [fisherLoss_eq q d hp]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  have hcs : coarseScore q p d (q ω) = g' (q ω) - blockAvg q p e (q ω) := by
    unfold coarseScore blockAvg blockDeriv
    have hd : ∀ ω' ∈ univ.filter (fun ω' => q ω' = q ω),
        d ω' = p ω' * g' (q ω) - p ω' * e ω' := by
      intro ω' hω'
      have h1 := hs ω'
      rw [hg ω', (Finset.mem_filter.mp hω').2] at h1
      have := (hp ω').ne'
      field_simp at h1
      linarith
    rw [Finset.sum_congr rfl hd, Finset.sum_sub_distrib, ← Finset.sum_mul]
    change (blockMass q p (q ω) * g' (q ω) - _) / blockMass q p (q ω) = _
    have hM : 0 < blockMass q p (q ω) :=
      Finset.sum_pos (fun ω _ => hp ω) ⟨ω, by simp⟩
    field_simp
  rw [hcs, hs ω, hg ω]
  ring

/-- **Variance bound.** Under the same splitting, the loss is at most the
`p`-weighted second moment of the error. -/
theorem fisherLoss_le_errorSq (hp : ∀ ω, 0 < p ω) (g e : Ω → ℝ) (g' : β → ℝ)
    (hg : ∀ ω, g ω = g' (q ω)) (hs : ∀ ω, d ω / p ω = g ω - e ω) :
    fineFisher p d - coarseFisher q p d ≤ ∑ ω, p ω * e ω ^ 2 := by
  have h := fisherLoss_le q d hp g'
  have heq : ∀ ω, p ω * (d ω / p ω - g' (q ω)) ^ 2 = p ω * e ω ^ 2 := by
    intro ω
    rw [hs ω, hg ω]
    ring
  simpa only [heq] using h

/-- Fisher information cannot increase under coarse-graining. -/
theorem coarseFisher_le (hp : ∀ ω, 0 < p ω) : coarseFisher q p d ≤ fineFisher p d := by
  have h := fisherLoss_eq q d hp
  have : 0 ≤ ∑ ω, p ω * (d ω / p ω - coarseScore q p d (q ω)) ^ 2 :=
    Finset.sum_nonneg (fun ω _ => mul_nonneg (hp ω).le (sq_nonneg _))
  linarith

/-! ### Composition along a tower `Ω → β → γ` -/

section Tower

variable {γ : Type*} [Fintype γ] [DecidableEq γ]

/-- Fiber sums compose along a tower. -/
lemma sum_filter_comp (f : β → γ) (c : γ) (F : Ω → ℝ) :
    ∑ ω ∈ univ.filter (fun ω => f (q ω) = c), F ω
      = ∑ b ∈ univ.filter (fun b => f b = c), ∑ ω ∈ univ.filter (fun ω => q ω = b), F ω := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ.filter (fun ω => f (q ω) = c))
    (t := univ.filter (fun b => f b = c)) (g := q)]
  · refine Finset.sum_congr rfl (fun b hb => ?_)
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨by rw [h]; exact (Finset.mem_filter.mp hb).2, h⟩
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact hω

/-- Pushed-forward mass and derivative along `q` are the block quantities. -/
theorem blockMass_comp (f : β → γ) (c : γ) :
    blockMass (fun ω => f (q ω)) p c = blockMass f (blockMass q p) c := by
  unfold blockMass
  exact sum_filter_comp q f c p

theorem blockDeriv_comp (f : β → γ) (c : γ) :
    blockDeriv (fun ω => f (q ω)) d c = blockDeriv f (blockDeriv q d) c := by
  unfold blockDeriv
  exact sum_filter_comp q f c d

/-- **Coarse Fisher information composes.** The composite coarse Fisher equals
the coarse Fisher of the pushed-forward family. -/
theorem coarseFisher_comp (f : β → γ) :
    coarseFisher (fun ω => f (q ω)) p d = coarseFisher f (blockMass q p) (blockDeriv q d) := by
  unfold coarseFisher
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [blockMass_comp q f c, blockDeriv_comp q d f c]

/-- The coarse Fisher of `q` is the fine Fisher of the pushed-forward family. -/
theorem coarseFisher_eq_fineFisher_push :
    coarseFisher q p d = fineFisher (blockMass q p) (blockDeriv q d) := rfl

/-- **Chain rule for Fisher loss.** Along a tower `Ω → β → γ`, the loss through
the composite equals the loss at the first level plus the loss at the second
level (computed for the pushed-forward family). No hypotheses. -/
theorem fisherLoss_chain (f : β → γ) :
    fineFisher p d - coarseFisher (fun ω => f (q ω)) p d
      = (fineFisher p d - coarseFisher q p d)
        + (fineFisher (blockMass q p) (blockDeriv q d)
            - coarseFisher f (blockMass q p) (blockDeriv q d)) := by
  rw [coarseFisher_comp q d f]
  have h : coarseFisher q p d = fineFisher (blockMass q p) (blockDeriv q d) := rfl
  rw [h]
  ring

/-- Pushed-forward mass is positive when every fiber is nonempty. -/
lemma blockMass_pos (hp : ∀ ω, 0 < p ω) (hq : Function.Surjective q) (b : β) :
    0 < blockMass q p b := by
  obtain ⟨ω, rfl⟩ := hq b
  exact Finset.sum_pos (fun ω _ => hp ω) ⟨ω, by simp⟩

/-- **Loss is monotone in refinement.** A coarser view loses at least as much as
any finer view it factors through. -/
theorem fisherLoss_mono (hp : ∀ ω, 0 < p ω) (hq : Function.Surjective q) (f : β → γ) :
    fineFisher p d - coarseFisher q p d
      ≤ fineFisher p d - coarseFisher (fun ω => f (q ω)) p d := by
  rw [fisherLoss_chain q d f]
  have h := coarseFisher_le f (blockDeriv q d) (blockMass_pos q hp hq)
  linarith

/-- The second-level loss is also dominated by the composite loss. -/
theorem fisherLoss_second_le (hp : ∀ ω, 0 < p ω) (f : β → γ) :
    fineFisher (blockMass q p) (blockDeriv q d) - coarseFisher f (blockMass q p) (blockDeriv q d)
      ≤ fineFisher p d - coarseFisher (fun ω => f (q ω)) p d := by
  rw [fisherLoss_chain q d f]
  have h := coarseFisher_le q d hp
  linarith

end Tower


end SGC.InformationGeometry.ScoreProjection
