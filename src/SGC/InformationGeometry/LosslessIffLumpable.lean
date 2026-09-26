/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.InformationGeometry.MarkovPathFisher

/-!
# Lossless for every block-pair tilt iff strongly lumpable

For a single direction `b`, zero loss is *not* equivalent to lumpability (tilts
orthogonal to the residual rows lose nothing on non-lumpable chains). The correct
converse quantifies over directions:

* `fisherLoss_eq_zero_iff_delta_zero` — for `T ≥ 1` steps and a positive kernel,
  the macro-observer loses nothing about `b` iff `δ_b ≡ 0`.
* `lossless_all_iff_lumpable` — lossless for **every** block-pair tilt iff `q` is
  strongly lumpable for `P`.

The forward direction uses the exact identity: zero loss makes the accumulated
defect a function of the block path; comparing two paths that differ only at
one step within a block forces `δ_b` to be constant on blocks, and its block
means vanish, so `δ_b ≡ 0`. Choosing indicator tilts then kills every residual.
-/

noncomputable section

namespace SGC.InformationGeometry.LosslessIffLumpable

open Finset Matrix SGC.InformationGeometry
open SGC.InformationGeometry.MarkovPathFisher

set_option linter.unusedSectionVars false

variable {V β : Type*} [Fintype V] [DecidableEq V] [Fintype β] [DecidableEq β]
variable (P : Matrix V V ℝ) (q : V → β) (π : V → ℝ) (b : β → β → ℝ) (T : ℕ)

/-- The loss functional at `T + 1` steps. -/
def loss : ℝ :=
  ScoreProjection.fineFisher (pathProb P π (T + 1)) (pathDeriv P q π b (T + 1))
    - ScoreProjection.coarseFisher (macroPath q (T + 1)) (pathProb P π (T + 1))
        (pathDeriv P q π b (T + 1))

lemma pathDefect_cons_const (x x' : V) :
    pathDefect P q π b (T + 1) (Fin.cons x' (fun _ : Fin (T + 1) => x))
      = BlockPairTilt.delta q π (blockExit P q) b x'
        + ∑ _i : Fin T, BlockPairTilt.delta q π (blockExit P q) b x := by
  unfold pathDefect
  rw [Fin.sum_univ_succ]
  simp [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ]

/-- Zero loss forces the accumulated defect to be block-path-measurable, hence
`δ_b` is constant on blocks. -/
lemma delta_const_on_blocks_of_loss_zero (hP : ∀ x y, 0 < P x y) (hπ : ∀ x, 0 < π x)
    (h0 : loss P q π b T = 0) {x x' : V} (hq : q x = q x') :
    BlockPairTilt.delta q π (blockExit P q) b x = BlockPairTilt.delta q π (blockExit P q) b x' := by
  set δ := BlockPairTilt.delta q π (blockExit P q) b
  have hpos := pathProb_pos P hP hπ (T + 1)
  have hid := fisherLoss_markov_path_condVar P q π b (T + 1) hP hπ
  unfold loss at h0
  rw [hid] at h0
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun ω _ =>
    mul_nonneg (hpos ω).le (sq_nonneg _))).mp h0
  have hfix : ∀ ω, pathDefect P q π b (T + 1) ω
      = ScoreProjection.blockAvg (macroPath q (T + 1)) (pathProb P π (T + 1))
          (pathDefect P q π b (T + 1)) (macroPath q (T + 1) ω) := by
    intro ω
    have := hterm ω (Finset.mem_univ ω)
    rcases mul_eq_zero.mp this with hp | hs
    · exact absurd hp (hpos ω).ne'
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hs
      linarith
  set ω₁ : Fin (T + 2) → V := Fin.cons x (fun _ => x)
  set ω₂ : Fin (T + 2) → V := Fin.cons x' (fun _ => x)
  have hmacro : macroPath q (T + 1) ω₁ = macroPath q (T + 1) ω₂ := by
    funext t
    refine Fin.cases ?_ (fun i => ?_) t
    · simp [macroPath, ω₁, ω₂, hq]
    · simp [macroPath, ω₁, ω₂]
  have h1 := hfix ω₁
  have h2 := hfix ω₂
  rw [hmacro] at h1
  have heq : pathDefect P q π b (T + 1) ω₁ = pathDefect P q π b (T + 1) ω₂ := by rw [h1, h2]
  simp only [ω₁, ω₂, pathDefect_cons_const] at heq
  linarith

lemma delta_block_sum_zero (hπ : ∀ x, 0 < π x) (A : β) :
    ∑ x ∈ univ.filter (fun x => q x = A), π x * BlockPairTilt.delta q π (blockExit P q) b x = 0 := by
  unfold BlockPairTilt.delta
  have h : ∀ x ∈ univ.filter (fun x => q x = A),
      π x * ∑ C, BlockPairTilt.res q π (blockExit P q) x C * b (q x) C
        = ∑ C, b A C * (π x * BlockPairTilt.res q π (blockExit P q) x C) := by
    intro x hx
    rw [(Finset.mem_filter.mp hx).2, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun C _ => by ring)
  rw [Finset.sum_congr rfl h, Finset.sum_comm]
  refine Finset.sum_eq_zero (fun C _ => ?_)
  rw [← Finset.mul_sum, BlockPairTilt.res_block_mean_zero q π (blockExit P q) hπ A C, mul_zero]

/-- Block-constant plus block-mean-zero forces `δ_b ≡ 0`. -/
lemma delta_zero_of_const (hπ : ∀ x, 0 < π x)
    (hc : ∀ x x', q x = q x' → BlockPairTilt.delta q π (blockExit P q) b x
      = BlockPairTilt.delta q π (blockExit P q) b x') (x : V) :
    BlockPairTilt.delta q π (blockExit P q) b x = 0 := by
  set δ := BlockPairTilt.delta q π (blockExit P q) b
  have h0 := delta_block_sum_zero P q π b hπ (q x)
  have hconst : ∀ y ∈ univ.filter (fun y => q y = q x), π y * δ y = π y * δ x := by
    intro y hy
    rw [hc y x (Finset.mem_filter.mp hy).2]
  rw [Finset.sum_congr rfl hconst, ← Finset.sum_mul] at h0
  have hM : 0 < ∑ y ∈ univ.filter (fun y => q y = q x), π y :=
    Finset.sum_pos (fun y _ => hπ y) ⟨x, by simp⟩
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd h hM.ne'
  · exact h

/-- **Single direction:** zero loss at `T + 1` steps iff `δ_b ≡ 0`. -/
theorem fisherLoss_eq_zero_iff_delta_zero (hP : ∀ x y, 0 < P x y) (hπ : ∀ x, 0 < π x) :
    loss P q π b T = 0 ↔ ∀ x, BlockPairTilt.delta q π (blockExit P q) b x = 0 := by
  constructor
  · intro h0 x
    exact delta_zero_of_const P q π b hπ
      (fun x x' hq => delta_const_on_blocks_of_loss_zero P q π b T hP hπ h0 hq) x
  · intro hδ
    have hdef : ∀ ω, pathDefect P q π b (T + 1) ω = 0 := by
      intro ω
      unfold pathDefect
      exact Finset.sum_eq_zero (fun t _ => hδ _)
    have h1 := ScoreProjection.fisherLoss_le_errorSq (macroPath q (T + 1)) (pathDeriv P q π b (T + 1))
      (pathProb_pos P hP hπ (T + 1)) (fun ω => surrogate P q π b (T + 1) (macroPath q (T + 1) ω))
      (pathDefect P q π b (T + 1)) (surrogate P q π b (T + 1)) (fun _ => rfl)
      (pathDeriv_div P q π b (T + 1) hP hπ)
    have h2 := ScoreProjection.coarseFisher_le (macroPath q (T + 1)) (pathDeriv P q π b (T + 1))
      (pathProb_pos P hP hπ (T + 1))
    simp only [hdef, sq, mul_zero, Finset.sum_const_zero] at h1
    unfold loss
    linarith

/-- Indicator tilt selecting the block pair `(A, C)`. -/
def indTilt (A C : β) : β → β → ℝ := fun A' C' => if A' = A ∧ C' = C then 1 else 0

lemma delta_indTilt (A C : β) (x : V) (hx : q x = A) :
    BlockPairTilt.delta q π (blockExit P q) (indTilt A C) x
      = BlockPairTilt.res q π (blockExit P q) x C := by
  unfold BlockPairTilt.delta indTilt
  rw [hx]
  simp [Finset.sum_ite_eq']

/-- **Quantified converse.** Lossless for every block-pair tilt iff strongly lumpable. -/
theorem lossless_all_iff_lumpable (hP : ∀ x y, 0 < P x y) (hπ : ∀ x, 0 < π x) :
    (∀ b : β → β → ℝ, loss P q π b T = 0) ↔ Lumpable P q := by
  constructor
  · intro h x y hxy C
    have hres : ∀ z, BlockPairTilt.res q π (blockExit P q) z C = 0 := by
      intro z
      have := (fisherLoss_eq_zero_iff_delta_zero P q π (indTilt (q z) C) T hP hπ).mp
        (h (indTilt (q z) C)) z
      rwa [delta_indTilt P q π (q z) C z rfl] at this
    have hx := hres x
    have hy := hres y
    unfold BlockPairTilt.res at hx hy
    rw [hxy] at hx
    linarith
  · intro hl b
    unfold loss
    exact fisherLoss_markov_path_eq_zero_of_lumpable P q π b (T + 1) hP hπ hl

end SGC.InformationGeometry.LosslessIffLumpable
