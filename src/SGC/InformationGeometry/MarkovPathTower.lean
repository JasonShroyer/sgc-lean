/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.InformationGeometry.MarkovPathFisher

/-!
# Towers with an exact inner level reduce to the lumped chain

If `q : V → β` is strongly lumpable for `P`, the `β`-observer's pushed-forward
path family is exactly the path family of the **lumped chain**
`P̄(A,C) = R̄(A,C)` started from `π̄ = push q π`, and the pushed-forward
derivative is the lumped chain's tilt derivative. Hence, by the chain rule of
`MarkovPathFisher`, the loss of the composite observer `f ∘ q` with tilt
`bt ∘ (f × f)` equals the loss of the lumped chain observed through `f` with
tilt `bt`, and inherits every bound proved for a single level with the lumped
chain's canonical defect.

## Main results

* `push_pathProb` — pushforward of the path law is the lumped path law (any start).
* `lumped_pos`, `lumped_row`, `push_pos`, `push_stationary` — the lumped chain
  with `π̄` satisfies the hypotheses of every single-level theorem.
* `blockDeriv_pathDeriv_eq` — pushed derivative = lumped `pathDeriv`.
* `tower_loss_eq_lumped` — composite loss = lumped-chain loss.
* `tower_loss_le` — composite loss `≤ T² · Bmax · D̄²` with the lumped defect.
-/

noncomputable section

namespace SGC.InformationGeometry.MarkovPathTower

open Finset Matrix SGC.InformationGeometry
open SGC.InformationGeometry.MarkovPathFisher

set_option linter.unusedSectionVars false

variable {V β : Type*} [Fintype V] [DecidableEq V] [Fintype β] [DecidableEq β]
variable (P : Matrix V V ℝ) (q : V → β) (π : V → ℝ)

/-- Lumped kernel: `π`-averaged block exit probabilities. -/
def lumped : Matrix β β ℝ := fun A C => BlockPairTilt.Rbar q π (blockExit P q) A C

/-- Pushforward of a measure along `q`. -/
def push (ν : V → ℝ) : β → ℝ := fun B => ∑ x ∈ univ.filter (fun x => q x = B), ν x

lemma push_row (x : V) : push q (P x) = fun C => blockExit P q x C := rfl

lemma blockExit_eq_lumped (hπ : ∀ x, 0 < π x) (hl : Lumpable P q) (x : V) (C : β) :
    blockExit P q x C = lumped P q π (q x) C := by
  have h := res_eq_zero_of_lumpable P q π hπ hl x C
  unfold BlockPairTilt.res at h
  unfold lumped
  linarith

lemma push_row_eq_lumped (hπ : ∀ x, 0 < π x) (hl : Lumpable P q) (x : V) :
    push q (P x) = lumped P q π (q x) := by
  funext C
  exact blockExit_eq_lumped P q π hπ hl x C

lemma macroPath_cons (T : ℕ) (x : V) (ω : Fin (T + 1) → V) :
    macroPath q (T + 1) (Fin.cons x ω) = Fin.cons (q x) (macroPath q T ω) := by
  funext t
  refine Fin.cases ?_ (fun i => ?_) t
  · simp [macroPath]
  · simp [macroPath]

/-- **Pushforward of the path law is the lumped path law.** -/
theorem push_pathProb (hπ : ∀ x, 0 < π x) (hl : Lumpable P q) :
    ∀ (T : ℕ) (ν : V → ℝ) (Y : Fin (T + 1) → β),
      ∑ ω ∈ univ.filter (fun ω => macroPath q T ω = Y), pathProb P ν T ω
        = pathProb (lumped P q π) (push q ν) T Y := by
  intro T
  induction T with
  | zero =>
    intro ν Y
    rw [Finset.sum_filter]
    change ∑ ω : Fin 1 → V, (if macroPath q 0 ω = Y then pathProb P ν 0 ω else 0) = _
    rw [← (Equiv.funUnique (Fin 1) V).symm.sum_comp]
    have hiff : ∀ x : V, (macroPath q 0 ((Equiv.funUnique (Fin 1) V).symm x) = Y) ↔ q x = Y 0 := by
      intro x
      constructor
      · intro h
        have := congrFun h 0
        simpa [macroPath] using this
      · intro h
        funext t
        have ht : t = 0 := Fin.ext (by have := t.isLt; omega)
        subst ht
        simpa [macroPath] using h
    simp only [hiff, pathProb, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    simp only [Equiv.funUnique_symm_apply]
    unfold push
    rw [Finset.sum_filter]
    rfl
  | succ T ih =>
    intro ν Y
    rw [Finset.sum_filter, MarkovPathFisher.sum_cons]
    simp only [pathProb_cons, macroPath_cons]
    have hY : Fin.cons (Y 0) (Fin.tail Y) = Y := Fin.cons_self_tail Y
    have hcond : ∀ (x : V) (ω' : Fin (T + 1) → V),
        (Fin.cons (q x) (macroPath q T ω') = Y) ↔ (q x = Y 0 ∧ macroPath q T ω' = Fin.tail Y) := by
      intro x ω'
      conv_lhs => rw [← hY]
      exact Fin.cons_inj
    simp only [hcond, ite_and]
    have hin : ∀ x : V,
        ∑ ω' : Fin (T + 1) → V, (if q x = Y 0 then (if macroPath q T ω' = Fin.tail Y
            then ν x * pathProb P (P x) T ω' else 0) else 0)
          = (if q x = Y 0 then ν x else 0)
            * pathProb (lumped P q π) (lumped P q π (Y 0)) T (Fin.tail Y) := by
      intro x
      by_cases h : q x = Y 0
      · simp only [h, if_true]
        rw [← h, ← push_row_eq_lumped P q π hπ hl x, ← ih (P x) (Fin.tail Y), Finset.sum_filter,
          Finset.mul_sum]
        refine Finset.sum_congr rfl (fun ω' _ => ?_)
        split_ifs <;> simp
      · simp only [h, if_false, Finset.sum_const_zero, zero_mul]
    rw [Finset.sum_congr rfl (fun x _ => hin x), ← Finset.sum_mul]
    conv_rhs => rw [← hY, pathProb_cons]
    congr 1
    unfold push
    rw [Finset.sum_filter]

/-! ### The lumped chain is a valid single-level chain -/

lemma push_pos (hπ : ∀ x, 0 < π x) (hq : Function.Surjective q) (B : β) : 0 < push q π B := by
  obtain ⟨x, rfl⟩ := hq B
  exact Finset.sum_pos (fun y _ => hπ y) ⟨x, by simp⟩

lemma blockExit_pos (hP : ∀ x y, 0 < P x y) (hq : Function.Surjective q) (x : V) (C : β) :
    0 < blockExit P q x C := by
  obtain ⟨y, rfl⟩ := hq C
  exact Finset.sum_pos (fun y _ => hP x y) ⟨y, by simp⟩

lemma sum_blockExit (hrow : ∀ x, ∑ y, P x y = 1) (x : V) : ∑ C, blockExit P q x C = 1 := by
  unfold blockExit
  rw [Finset.sum_fiberwise univ q (fun y => P x y)]
  exact hrow x

lemma lumped_pos (hP : ∀ x y, 0 < P x y) (hπ : ∀ x, 0 < π x) (hq : Function.Surjective q)
    (A C : β) : 0 < lumped P q π A C := by
  unfold lumped BlockPairTilt.Rbar
  obtain ⟨x, rfl⟩ := hq A
  refine div_pos (Finset.sum_pos (fun y _ => mul_pos (hπ y) (blockExit_pos P q hP hq y C))
    ⟨x, by simp⟩) (Finset.sum_pos (fun y _ => hπ y) ⟨x, by simp⟩)

lemma lumped_row (hrow : ∀ x, ∑ y, P x y = 1) (hπ : ∀ x, 0 < π x) (hq : Function.Surjective q)
    (A : β) : ∑ C, lumped P q π A C = 1 := by
  unfold lumped BlockPairTilt.Rbar
  rw [← Finset.sum_div]
  have hM : 0 < BlockPairTilt.blockMass q π A := by
    obtain ⟨x, rfl⟩ := hq A
    exact Finset.sum_pos (fun y _ => hπ y) ⟨x, by simp⟩
  rw [div_eq_one_iff_eq hM.ne']
  rw [Finset.sum_comm]
  unfold BlockPairTilt.blockMass
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← Finset.mul_sum, sum_blockExit P q hrow x, mul_one]

lemma push_stationary (hπ : ∀ x, 0 < π x) (hstat : π ᵥ* P = π) :
    push q π ᵥ* lumped P q π = push q π := by
  funext C
  simp only [vecMul, dotProduct]
  -- Σ_A π̄(A) R̄(A,C) = Σ_A Σ_{x∈A} π x · blockExit x C
  have hterm : ∀ A, push q π A * lumped P q π A C
      = ∑ x ∈ univ.filter (fun x => q x = A), π x * blockExit P q x C := by
    intro A
    unfold push lumped BlockPairTilt.Rbar BlockPairTilt.blockMass
    rcases eq_or_ne (∑ x ∈ univ.filter (fun x => q x = A), π x) 0 with h0 | h0
    · have hempty : univ.filter (fun x => q x = A) = ∅ := by
        by_contra hne
        obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        have : 0 < ∑ x ∈ univ.filter (fun x => q x = A), π x :=
          Finset.sum_pos (fun y _ => hπ y) ⟨x, hx⟩
        linarith
      simp [hempty]
    · field_simp
  simp only [hterm]
  rw [Finset.sum_fiberwise univ q (fun x => π x * blockExit P q x C)]
  -- Σ_x π x · Σ_{y∈C} P x y = Σ_{y∈C} (π P) y = π̄ C
  unfold blockExit push
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  have := congrFun hstat y
  simp only [vecMul, dotProduct] at this
  exact this

/-! ### Pushed derivative -/

variable (T : ℕ)

lemma blockExit_id (M : Matrix β β ℝ) (A C : β) : blockExit M (fun B => B) A C = M A C := by
  unfold blockExit
  rw [Finset.sum_filter]
  simp

/-- The `β`-level surrogate is the lumped chain's own path score. -/
lemma surrogate_eq_lumped_pathScore (b : β → β → ℝ) (Y : Fin (T + 1) → β) :
    surrogate P q π b T Y = pathScore (lumped P q π) (fun B => B) b T Y := by
  unfold surrogate pathScore BlockPairTilt.stepScore
  refine Finset.sum_congr rfl (fun t _ => ?_)
  simp only [blockExit_id, lumped]

/-- **Pushed derivative = lumped derivative.** -/
theorem blockDeriv_pathDeriv_eq (_hP : ∀ x y, 0 < P x y) (hπ : ∀ x, 0 < π x) (hl : Lumpable P q)
    (b : β → β → ℝ) (Y : Fin (T + 1) → β) :
    ScoreProjection.blockDeriv (macroPath q T) (pathDeriv P q π b T) Y
      = pathDeriv (lumped P q π) (fun B => B) (push q π) b T Y := by
  unfold ScoreProjection.blockDeriv pathDeriv
  have hscore : ∀ ω, pathScore P q b T ω = surrogate P q π b T (macroPath q T ω) := by
    intro ω
    rw [pathScore_split P q π b T ω]
    have : pathDefect P q π b T ω = 0 := by
      unfold pathDefect
      refine Finset.sum_eq_zero (fun t _ => ?_)
      unfold BlockPairTilt.delta
      exact Finset.sum_eq_zero (fun C _ => by
        rw [res_eq_zero_of_lumpable P q π hπ hl, zero_mul])
    rw [this, sub_zero]
  have hc : ∀ ω ∈ univ.filter (fun ω => macroPath q T ω = Y),
      pathProb P π T ω * pathScore P q b T ω = pathProb P π T ω * surrogate P q π b T Y := by
    intro ω hω
    rw [hscore ω, (Finset.mem_filter.mp hω).2]
  rw [Finset.sum_congr rfl hc, ← Finset.sum_mul, push_pathProb P q π hπ hl T π Y,
    surrogate_eq_lumped_pathScore]

theorem blockMass_pathProb_eq (hπ : ∀ x, 0 < π x) (hl : Lumpable P q) (Y : Fin (T + 1) → β) :
    ScoreProjection.blockMass (macroPath q T) (pathProb P π T) Y
      = pathProb (lumped P q π) (push q π) T Y := by
  unfold ScoreProjection.blockMass
  exact push_pathProb P q π hπ hl T π Y

/-! ### Tower collapse to the lumped chain -/

variable {γ : Type*} [Fintype γ] [DecidableEq γ]

/-- Tilt on `β` induced by a tilt on `γ` through `f`. -/
def liftTilt (f : β → γ) (bt : γ → γ → ℝ) : β → β → ℝ := fun A C => bt (f A) (f C)

/-- The lumped chain's `f`-tilt derivative equals its `id`-tilt derivative with the lifted tilt. -/
lemma lumped_pathDeriv_lift (f : β → γ) (bt : γ → γ → ℝ) (Y : Fin (T + 1) → β) :
    pathDeriv (lumped P q π) (fun B => B) (push q π) (liftTilt f bt) T Y
      = pathDeriv (lumped P q π) f (push q π) bt T Y := by
  unfold pathDeriv pathScore BlockPairTilt.stepScore liftTilt
  congr 1
  refine Finset.sum_congr rfl (fun t _ => ?_)
  congr 1
  -- Σ_C M(A,C) bt(fA, fC) = Σ_{C'} blockExit M f A C' · bt(fA, C')
  simp only [blockExit_id]
  unfold blockExit
  rw [← Finset.sum_fiberwise univ f (fun C => lumped P q π (Y (Fin.castSucc t)) C
    * bt (f (Y (Fin.castSucc t))) (f C))]
  refine Finset.sum_congr rfl (fun C' _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun C hC => ?_)
  rw [(Finset.mem_filter.mp hC).2]

/-- **Tower collapse.** With a lumpable inner level, the composite observer's loss
equals the lumped chain's loss through `f`. -/
theorem tower_loss_eq_lumped (hP : ∀ x y, 0 < P x y) (hπ : ∀ x, 0 < π x) (hl : Lumpable P q)
    (f : β → γ) (bt : γ → γ → ℝ) :
    ScoreProjection.fineFisher (pathProb P π T) (pathDeriv P q π (liftTilt f bt) T)
      - ScoreProjection.coarseFisher (macroPath (fun x => f (q x)) T) (pathProb P π T)
          (pathDeriv P q π (liftTilt f bt) T)
      = ScoreProjection.fineFisher (pathProb (lumped P q π) (push q π) T)
          (pathDeriv (lumped P q π) f (push q π) bt T)
        - ScoreProjection.coarseFisher (macroPath f T) (pathProb (lumped P q π) (push q π) T)
          (pathDeriv (lumped P q π) f (push q π) bt T) := by
  rw [fisherLoss_markov_tower_of_lumpable P q π (liftTilt f bt) T hP hπ hl f]
  have hm : ScoreProjection.blockMass (macroPath q T) (pathProb P π T)
      = pathProb (lumped P q π) (push q π) T := funext (blockMass_pathProb_eq P q π T hπ hl)
  have hd : ScoreProjection.blockDeriv (macroPath q T) (pathDeriv P q π (liftTilt f bt) T)
      = pathDeriv (lumped P q π) f (push q π) bt T := by
    funext Y
    rw [blockDeriv_pathDeriv_eq P q π T hP hπ hl, lumped_pathDeriv_lift]
  rw [hm, hd]
  rfl

/-- **Inherited bound.** The composite observer's loss is bounded by the lumped
chain's own directional closure bound. -/
theorem tower_loss_le (hP : ∀ x y, 0 < P x y) (hrow : ∀ x, ∑ y, P x y = 1) (hπ : ∀ x, 0 < π x)
    (hstat : π ᵥ* P = π) (hq : Function.Surjective q) (hl : Lumpable P q) (f : β → γ)
    (bt : γ → γ → ℝ) {Bmax : ℝ} (hB : ∀ A, ∑ C, bt A C ^ 2 ≤ Bmax) :
    ScoreProjection.fineFisher (pathProb P π T) (pathDeriv P q π (liftTilt f bt) T)
      - ScoreProjection.coarseFisher (macroPath (fun x => f (q x)) T) (pathProb P π T)
          (pathDeriv P q π (liftTilt f bt) T)
      ≤ (T : ℝ) ^ 2 * (Bmax * BlockPairTilt.defectSq f (push q π) (blockExit (lumped P q π) f)) := by
  rw [tower_loss_eq_lumped P q π T hP hπ hl f bt]
  exact fisherLoss_markov_path_le (lumped P q π) f (push q π) bt T (lumped_pos P q π hP hπ hq)
    (lumped_row P q π hrow hπ hq) (push_pos q π hπ hq) (push_stationary P q π hπ hstat) hB

end SGC.InformationGeometry.MarkovPathTower
