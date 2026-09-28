/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.InformationGeometry.MarkovPathMixing
import SGC.InformationGeometry.GeneralOneStep

/-!
# Multi-step bounds for an arbitrary direction

For an arbitrary step score `s : V → V → ℝ` (any parameter direction of the
transition law, not only a block-pair tilt), the `T`-step Fisher loss through a
partition `q` is controlled by the one-step fiber-variance objective
`J₁ = Σ_{x,y} π x P x y (s x y − m (q x) (q y))²` (module `GeneralOneStep`):

* `loss(T) ≤ T² · J₁` unconditionally;
* `loss(T) ≤ T · (3 − σ)/(1 − σ) · J₁` under `MixingContraction P π σ`.

The residual `r x y = m (q x) (q y) − s x y` is a function of a *pair* of
consecutive states, so the correlation machinery needs pair-time marginals of
the path law (`sum_pathProb_point_pair`, `sum_pathProb_pair_pair`), proved here.
The key estimate is `|E[r_t r_u]| ≤ σ^{u−t−1} J₁`: conditioning the later
residual on its first state gives `g = P-average of r`, which is `π`-mean-zero
and has `‖g‖²_π ≤ J₁` by Jensen; the earlier residual is then paired with
`P^{u−t−1} g` by Cauchy–Schwarz.

These bounds certify the greedy `J₁`-merge of decision 0075 at every horizon.
-/

noncomputable section

namespace SGC.InformationGeometry.GeneralPathBound

open Finset Matrix SGC.InformationGeometry.MarkovPathFisher
  SGC.InformationGeometry.MarkovPathMixing

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `P`-average of a pair function in its second argument. -/
def Hbar (P : Matrix V V ℝ) (H : V → V → ℝ) (x : V) : ℝ := ∑ y, P x y * H x y

/-! ### Pair-time marginals -/

/-- Point at `j`, pair at `(u, u+1)`, `j ≤ u`. -/
theorem sum_pathProb_point_pair (P : Matrix V V ℝ) (hrow : ∀ x, ∑ y, P x y = 1) :
    ∀ (T : ℕ) (j : Fin (T + 1)) (u : Fin T), (j : ℕ) ≤ u → ∀ (μ f : V → ℝ) (H : V → V → ℝ),
      ∑ ω, pathProb P μ T ω * (f (ω j) * H (ω (Fin.castSucc u)) (ω (Fin.succ u)))
        = ∑ x, (μ ᵥ* P ^ (j : ℕ)) x * (f x * (P ^ ((u : ℕ) - j) *ᵥ Hbar P H) x) := by
  intro T
  induction T with
  | zero => intro _ u; exact u.elim0
  | succ T ih =>
    intro j u hju μ f H
    rw [MarkovPathFisher.sum_cons]
    simp only [pathProb_cons]
    revert hju
    refine Fin.cases ?_ (fun j' => ?_) j <;> refine Fin.cases ?_ (fun u' => ?_) u <;> intro hju
    · -- j = 0, u = 0
      simp only [Fin.cons_zero, Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.val_zero, pow_zero,
        vecMul_one, Nat.sub_self, one_mulVec]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      have h1 : ∀ ω' : Fin (T + 1) → V, (Fin.cons x ω' : Fin (T + 2) → V) 1 = ω' 0 := by
        intro ω'
        rw [← Fin.succ_zero_eq_one]
        exact Fin.cons_succ (α := fun _ => V) x ω' (0 : Fin (T + 1))
      simp only [h1]
      have hs : ∑ ω' : Fin (T + 1) → V, μ x * pathProb P (P x) T ω' * (f x * H x (ω' 0))
          = μ x * f x * ∑ ω', pathProb P (P x) T ω' * H x (ω' 0) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun ω' _ => by ring)
      rw [hs, sum_pathProb_marginal P hrow T 0 (P x) (H x)]
      simp only [Fin.val_zero, pow_zero, vecMul_one, Hbar]
      ring
    · -- j = 0, u = u' + 1
      simp only [Fin.cons_zero, Fin.val_zero, pow_zero, vecMul_one, Fin.val_succ, Nat.sub_zero,
        ← Fin.succ_castSucc, Fin.cons_succ]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      have hs : ∑ ω' : Fin (T + 1) → V, μ x * pathProb P (P x) T ω'
            * (f x * H (ω' (Fin.castSucc u')) (ω' (Fin.succ u')))
          = μ x * f x * ∑ ω', pathProb P (P x) T ω'
            * ((fun _ => (1 : ℝ)) (ω' 0) * H (ω' (Fin.castSucc u')) (ω' (Fin.succ u'))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun ω' _ => by ring)
      rw [hs, ih 0 u' (by simp) (P x) (fun _ => 1) H]
      simp only [Fin.val_zero, pow_zero, vecMul_one, Nat.sub_zero, one_mul]
      have hm : ∑ y, P x y * (P ^ (u' : ℕ) *ᵥ Hbar P H) y
          = (P ^ ((u' : ℕ) + 1) *ᵥ Hbar P H) x := by
        rw [pow_succ', ← mulVec_mulVec]
        simp [Matrix.mulVec, dotProduct]
      rw [hm]
      ring
    · -- j = j' + 1, u = 0: impossible
      simp at hju
    · -- j = j' + 1, u = u' + 1
      simp only [Fin.cons_succ, Fin.val_succ, ← Fin.succ_castSucc] at hju ⊢
      have hs : ∑ x, ∑ ω' : Fin (T + 1) → V, μ x * pathProb P (P x) T ω'
            * (f (ω' j') * H (ω' (Fin.castSucc u')) (ω' (Fin.succ u')))
          = ∑ ω', pathProb P (μ ᵥ* P) T ω'
            * (f (ω' j') * H (ω' (Fin.castSucc u')) (ω' (Fin.succ u'))) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun ω' _ => ?_)
        rw [← sum_pathProb_row, Finset.sum_mul]
      rw [hs, ih j' u' (by omega) (μ ᵥ* P) f H, Nat.add_sub_add_right, vecMul_vecMul, ← pow_succ']

/-- Pair at `(t, t+1)`, pair at `(u, u+1)`, `t < u`. -/
theorem sum_pathProb_pair_pair (P : Matrix V V ℝ) (hrow : ∀ x, ∑ y, P x y = 1) :
    ∀ (T : ℕ) (t u : Fin T), (t : ℕ) < u → ∀ (μ : V → ℝ) (F H : V → V → ℝ),
      ∑ ω, pathProb P μ T ω * (F (ω (Fin.castSucc t)) (ω (Fin.succ t))
          * H (ω (Fin.castSucc u)) (ω (Fin.succ u)))
        = ∑ x, (μ ᵥ* P ^ (t : ℕ)) x
            * ∑ y, P x y * (F x y * (P ^ ((u : ℕ) - t - 1) *ᵥ Hbar P H) y) := by
  intro T
  induction T with
  | zero => intro t; exact t.elim0
  | succ T ih =>
    intro t u htu μ F H
    rw [MarkovPathFisher.sum_cons]
    simp only [pathProb_cons]
    revert htu
    refine Fin.cases ?_ (fun t' => ?_) t <;> refine Fin.cases ?_ (fun u' => ?_) u <;> intro htu
    · simp at htu
    · -- t = 0, u = u' + 1
      simp only [Fin.cons_zero, Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.val_zero, pow_zero,
        vecMul_one, Fin.val_succ, Nat.sub_zero, Nat.add_sub_cancel, ← Fin.succ_castSucc,
        Fin.cons_succ]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      have h1 : ∀ ω' : Fin (T + 1) → V, (Fin.cons x ω' : Fin (T + 2) → V) 1 = ω' 0 := by
        intro ω'
        rw [← Fin.succ_zero_eq_one]
        exact Fin.cons_succ (α := fun _ => V) x ω' (0 : Fin (T + 1))
      simp only [h1]
      have hs : ∑ ω' : Fin (T + 1) → V, μ x * pathProb P (P x) T ω'
            * (F x (ω' 0) * H (ω' (Fin.castSucc u')) (ω' (Fin.succ u')))
          = μ x * ∑ ω', pathProb P (P x) T ω'
            * (F x (ω' 0) * H (ω' (Fin.castSucc u')) (ω' (Fin.succ u'))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun ω' _ => by ring)
      rw [hs, sum_pathProb_point_pair P hrow T 0 u' (by simp) (P x) (F x) H]
      simp only [Fin.val_zero, pow_zero, vecMul_one, Nat.sub_zero]
    · simp at htu
    · -- t = t' + 1, u = u' + 1
      simp only [Fin.cons_succ, Fin.val_succ, ← Fin.succ_castSucc] at htu ⊢
      have hs : ∑ x, ∑ ω' : Fin (T + 1) → V, μ x * pathProb P (P x) T ω'
            * (F (ω' (Fin.castSucc t')) (ω' (Fin.succ t'))
              * H (ω' (Fin.castSucc u')) (ω' (Fin.succ u')))
          = ∑ ω', pathProb P (μ ᵥ* P) T ω'
            * (F (ω' (Fin.castSucc t')) (ω' (Fin.succ t'))
              * H (ω' (Fin.castSucc u')) (ω' (Fin.succ u'))) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun ω' _ => ?_)
        rw [← sum_pathProb_row, Finset.sum_mul]
      rw [hs, ih t' u' (by omega) (μ ᵥ* P) F H, Nat.add_sub_add_right, vecMul_vecMul, ← pow_succ']

/-! ### Residual, surrogate, and path score for an arbitrary direction -/

variable {β : Type*} [Fintype β] [DecidableEq β]
variable (P : Matrix V V ℝ) (q : V → β) (π : V → ℝ) (s : V → V → ℝ)

/-- Fiber mean of the step score on the block pair `(A, C)`. -/
def m (A C : β) : ℝ := GeneralOneStep.fiberMean P q π s (A, C)

/-- Residual: fiber mean minus score. -/
def r (x y : V) : ℝ := m P q π s (q x) (q y) - s x y

/-- One-step residual energy `J = Σ_x π x Σ_y P x y r x y²`. -/
def J : ℝ := ∑ x, π x * ∑ y, P x y * r P q π s x y ^ 2

/-- `J` is the fiber-variance objective of `GeneralOneStep`. -/
theorem J_eq_J1 : J P q π s = GeneralOneStep.J1 P q π s := by
  unfold J GeneralOneStep.J1
  rw [Fintype.sum_prod_type]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  simp only [GeneralOneStep.w, GeneralOneStep.Q, r, m]
  ring

lemma J_nonneg (hP : ∀ x y, 0 < P x y) (hπ : ∀ x, 0 < π x) : 0 ≤ J P q π s :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (hπ x).le
    (Finset.sum_nonneg (fun y _ => mul_nonneg (hP x y).le (sq_nonneg _))))

/-- `P`-average of the residual in its second argument. -/
def g : V → ℝ := Hbar P (r P q π s)

lemma sum_w_r_zero (hP : ∀ x y, 0 < P x y) (hπ : ∀ x, 0 < π x) :
    ∑ ω : V × V, GeneralOneStep.w P π ω * r P q π s ω.1 ω.2 = 0 := by
  rw [ScoreProjection.sum_fibers (GeneralOneStep.Q q)]
  refine Finset.sum_eq_zero (fun f _ => ?_)
  have hr : ∀ ω ∈ univ.filter (fun ω => GeneralOneStep.Q q ω = f),
      GeneralOneStep.w P π ω * r P q π s ω.1 ω.2
        = GeneralOneStep.fiberMean P q π s f * GeneralOneStep.w P π ω
          - GeneralOneStep.w P π ω * s ω.1 ω.2 := by
    intro ω hω
    have hQ := (Finset.mem_filter.mp hω).2
    have hm : m P q π s (q ω.1) (q ω.2) = GeneralOneStep.fiberMean P q π s f := by
      unfold m
      rw [← hQ]
      rfl
    unfold r
    rw [hm]
    ring
  rw [Finset.sum_congr rfl hr, Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold GeneralOneStep.fiberMean ScoreProjection.blockAvg
  by_cases hM : ScoreProjection.blockMass (GeneralOneStep.Q q) (GeneralOneStep.w P π) f = 0
  · have h0 := ScoreProjection.blockDeriv_eq_zero_of_mass (GeneralOneStep.Q q)
      (fun ω : V × V => GeneralOneStep.w P π ω * s ω.1 ω.2)
      (GeneralOneStep.w_pos P π hP hπ) hM
    unfold ScoreProjection.blockDeriv at h0
    unfold ScoreProjection.blockMass at hM
    rw [hM, h0]
    simp
  · unfold ScoreProjection.blockMass at hM ⊢
    field_simp
    ring

lemma g_mean_zero (hP : ∀ x y, 0 < P x y) (hπ : ∀ x, 0 < π x) :
    ∑ x, π x * g P q π s x = 0 := by
  have h := sum_w_r_zero P q π s hP hπ
  rw [Fintype.sum_prod_type] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  unfold g Hbar
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  simp only [GeneralOneStep.w]
  ring

lemma g_sq_le (hP : ∀ x y, 0 < P x y) (hrow : ∀ x, ∑ y, P x y = 1) (x : V) :
    g P q π s x ^ 2 ≤ ∑ y, P x y * r P q π s x y ^ 2 := by
  unfold g Hbar
  have h := weighted_cs (π := P x) (fun y => (hP x y).le) (r P q π s x) (fun _ => 1)
  simp only [mul_one, one_pow, hrow x] at h
  exact h

lemma g_energy_le (hP : ∀ x y, 0 < P x y) (hrow : ∀ x, ∑ y, P x y = 1) (hπ : ∀ x, 0 < π x) :
    ∑ x, π x * g P q π s x ^ 2 ≤ J P q π s :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (g_sq_le P q π s hP hrow x) (hπ x).le)

variable (T : ℕ)

/-- Fine path score `Σ_t s (ω_t, ω_{t+1})`. -/
def pathScoreG (ω : Fin (T + 1) → V) : ℝ :=
  ∑ t : Fin T, s (ω (Fin.castSucc t)) (ω (Fin.succ t))

/-- Block-measurable surrogate `Σ_t m (Y_t, Y_{t+1})`. -/
def pathSurrG (Y : Fin (T + 1) → β) : ℝ :=
  ∑ t : Fin T, m P q π s (Y (Fin.castSucc t)) (Y (Fin.succ t))

/-- Accumulated residual `Σ_t r (ω_t, ω_{t+1})`. -/
def pathErr (ω : Fin (T + 1) → V) : ℝ :=
  ∑ t : Fin T, r P q π s (ω (Fin.castSucc t)) (ω (Fin.succ t))

lemma pathScoreG_split (ω : Fin (T + 1) → V) :
    pathScoreG s T ω = pathSurrG P q π s T (macroPath q T ω) - pathErr P q π s T ω := by
  unfold pathScoreG pathSurrG pathErr macroPath r
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun t _ => by ring)

/-- Derivative data of the path law in the direction `s`. -/
def pathDerivG (ω : Fin (T + 1) → V) : ℝ := pathProb P π T ω * pathScoreG s T ω

lemma pathDerivG_div (hP : ∀ x y, 0 < P x y) (hπ : ∀ x, 0 < π x) (ω : Fin (T + 1) → V) :
    pathDerivG P π s T ω / pathProb P π T ω
      = pathSurrG P q π s T (macroPath q T ω) - pathErr P q π s T ω := by
  unfold pathDerivG
  rw [mul_div_cancel_left₀ _ (pathProb_pos P hP hπ T ω).ne', pathScoreG_split P q π s T ω]

/-- `T`-step Fisher loss through `q` about the direction `s`. -/
def lossG : ℝ :=
  ScoreProjection.fineFisher (pathProb P π T) (pathDerivG P π s T)
    - ScoreProjection.coarseFisher (macroPath q T) (pathProb P π T) (pathDerivG P π s T)

/-- **Exact identity for an arbitrary direction:** the loss is the conditional
variance of the accumulated residual given the block path. -/
theorem lossG_eq_condVar (hP : ∀ x y, 0 < P x y) (hπ : ∀ x, 0 < π x) :
    lossG P q π s T = ∑ ω, pathProb P π T ω
      * (pathErr P q π s T ω
          - ScoreProjection.blockAvg (macroPath q T) (pathProb P π T) (pathErr P q π s T)
              (macroPath q T ω)) ^ 2 :=
  ScoreProjection.fisherLoss_eq_condVar (macroPath q T) (pathDerivG P π s T)
    (pathProb_pos P hP hπ T) (fun ω => pathSurrG P q π s T (macroPath q T ω))
    (pathErr P q π s T) (pathSurrG P q π s T) (fun _ => rfl) (pathDerivG_div P q π s T hP hπ)

theorem lossG_le_errSq (hP : ∀ x y, 0 < P x y) (hπ : ∀ x, 0 < π x) :
    lossG P q π s T ≤ ∑ ω, pathProb P π T ω * pathErr P q π s T ω ^ 2 :=
  ScoreProjection.fisherLoss_le_errorSq (macroPath q T) (pathDerivG P π s T)
    (pathProb_pos P hP hπ T) (fun ω => pathSurrG P q π s T (macroPath q T ω))
    (pathErr P q π s T) (pathSurrG P q π s T) (fun _ => rfl) (pathDerivG_div P q π s T hP hπ)

/-! ### Correlations of the residual -/

/-- Same-time term: `E[r_t²] = J`. -/
lemma diag_eq (hrow : ∀ x, ∑ y, P x y = 1) (hstat : π ᵥ* P = π) (t : Fin T) :
    ∑ ω, pathProb P π T ω * (r P q π s (ω (Fin.castSucc t)) (ω (Fin.succ t))
        * r P q π s (ω (Fin.castSucc t)) (ω (Fin.succ t))) = J P q π s := by
  have h := sum_pathProb_point_pair P hrow T (Fin.castSucc t) t (by simp) π (fun _ => 1)
    (fun x y => r P q π s x y * r P q π s x y)
  simp only [one_mul, Fin.coe_castSucc, Nat.sub_self, pow_zero, one_mulVec,
    vecMul_pow_stationary P hstat] at h
  rw [h]
  unfold J Hbar
  refine Finset.sum_congr rfl (fun x _ => ?_)
  congr 1
  exact Finset.sum_congr rfl (fun y _ => by ring)

/-- Two-time term: `|E[r_t r_u]| ≤ σ^{u−t−1} J` for `t < u`. -/
lemma offdiag_le (hP : ∀ x y, 0 < P x y) (hrow : ∀ x, ∑ y, P x y = 1) (hπ : ∀ x, 0 < π x)
    (hstat : π ᵥ* P = π) {σ : ℝ} (hσ : MixingContraction P π σ) (hσ0 : 0 ≤ σ)
    (t u : Fin T) (htu : (t : ℕ) < u) :
    |∑ ω, pathProb P π T ω * (r P q π s (ω (Fin.castSucc t)) (ω (Fin.succ t))
        * r P q π s (ω (Fin.castSucc u)) (ω (Fin.succ u)))|
      ≤ σ ^ ((u : ℕ) - t - 1) * J P q π s := by
  set k := (u : ℕ) - t - 1
  set A := J P q π s
  have hA : 0 ≤ A := J_nonneg P q π s hP hπ
  rw [sum_pathProb_pair_pair P hrow T t u htu π (r P q π s) (r P q π s),
    vecMul_pow_stationary P hstat]
  set h := P ^ k *ᵥ Hbar P (r P q π s)
  have hrw : ∑ x, π x * ∑ y, P x y * (r P q π s x y * h y)
      = ∑ ω : V × V, GeneralOneStep.w P π ω * (r P q π s ω.1 ω.2 * h ω.2) := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    simp only [GeneralOneStep.w]
    ring
  rw [hrw]
  have hcs := weighted_cs (π := GeneralOneStep.w P π) (fun ω => (GeneralOneStep.w_pos P π hP hπ ω).le)
    (fun ω => r P q π s ω.1 ω.2) (fun ω => h ω.2)
  have hJ : ∑ ω : V × V, GeneralOneStep.w P π ω * (r P q π s ω.1 ω.2) ^ 2 = A := by
    unfold A J
    rw [Fintype.sum_prod_type]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    simp only [GeneralOneStep.w]
    ring
  have hh : ∑ ω : V × V, GeneralOneStep.w P π ω * (h ω.2) ^ 2 = ∑ y, π y * h y ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    have hst : ∑ x, π x * P x y = π y := by
      have := congrFun hstat y
      simpa [vecMul, dotProduct] using this
    simp only [GeneralOneStep.w]
    rw [← hst, Finset.sum_mul]
  have hcontr := pow_contract P hstat hσ (g P q π s) (g_mean_zero P q π s hP hπ) k
  have hgE := g_energy_le P q π s hP hrow hπ
  have hh' : ∑ y, π y * h y ^ 2 ≤ (σ ^ 2) ^ k * A :=
    hcontr.trans (mul_le_mul_of_nonneg_left hgE (pow_nonneg (sq_nonneg σ) k))
  refine abs_le_of_sq_le_sq ?_ (mul_nonneg (pow_nonneg hσ0 k) hA)
  calc (∑ ω : V × V, GeneralOneStep.w P π ω * (r P q π s ω.1 ω.2 * h ω.2)) ^ 2
      ≤ A * ∑ y, π y * h y ^ 2 := by rw [← hJ, ← hh]; exact hcs
    _ ≤ A * ((σ ^ 2) ^ k * A) := mul_le_mul_of_nonneg_left hh' hA
    _ = (σ ^ k * A) ^ 2 := by ring

/-- Row sum of the correlation coefficients `c(s,u) = 1` if `s = u`, else `σ^{|s−u|−1}`. -/
lemma sum_corr_coeff_le {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (T s : ℕ) (hs : s < T) :
    ∑ u ∈ range T, (if s = u then (1 : ℝ) else σ ^ (tdist s u - 1)) ≤ (3 - σ) / (1 - σ) := by
  rw [← Finset.sum_range_add_sum_Ico _ hs.le, Finset.sum_eq_sum_Ico_succ_bot hs]
  have h1 : ∑ u ∈ range s, (if s = u then (1 : ℝ) else σ ^ (tdist s u - 1))
      = ∑ j ∈ range s, σ ^ j := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj' := Finset.mem_range.mp hj
    rw [if_neg (by omega)]
    unfold tdist
    rw [if_neg (by omega), show s - (s - 1 - j) - 1 = j by omega]
  have h2 : ∑ u ∈ Ico (s + 1) T, (if s = u then (1 : ℝ) else σ ^ (tdist s u - 1))
      = ∑ k ∈ range (T - (s + 1)), σ ^ k := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [if_neg (by omega)]
    unfold tdist
    rw [if_pos (by omega), show s + 1 + k - s - 1 = k by omega]
  rw [h1, h2, if_pos rfl]
  have g1 := geom_range_le hσ0 hσ1 s
  have g2 := geom_range_le hσ0 hσ1 (T - (s + 1))
  have hden : 0 < 1 - σ := by linarith
  calc ∑ j ∈ range s, σ ^ j + (1 + ∑ k ∈ range (T - (s + 1)), σ ^ k)
      ≤ 1 / (1 - σ) + (1 + 1 / (1 - σ)) := by linarith
    _ = (3 - σ) / (1 - σ) := by field_simp; ring

lemma errSq_expand (ω : Fin (T + 1) → V) :
    pathProb P π T ω * pathErr P q π s T ω ^ 2
      = ∑ t : Fin T, ∑ u : Fin T, pathProb P π T ω
          * (r P q π s (ω (Fin.castSucc t)) (ω (Fin.succ t))
            * r P q π s (ω (Fin.castSucc u)) (ω (Fin.succ u))) := by
  unfold pathErr
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun t _ => by rw [Finset.mul_sum])

/-- **Linear residual-variance bound for an arbitrary direction.** -/
theorem errSq_le_linear (hP : ∀ x y, 0 < P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (hπ : ∀ x, 0 < π x) (hstat : π ᵥ* P = π) {σ : ℝ} (hσ : MixingContraction P π σ)
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    ∑ ω, pathProb P π T ω * pathErr P q π s T ω ^ 2
      ≤ (T : ℝ) * ((3 - σ) / (1 - σ)) * J P q π s := by
  set A := J P q π s
  have hA : 0 ≤ A := J_nonneg P q π s hP hπ
  have hpair : ∀ t u : Fin T,
      ∑ ω, pathProb P π T ω * (r P q π s (ω (Fin.castSucc t)) (ω (Fin.succ t))
          * r P q π s (ω (Fin.castSucc u)) (ω (Fin.succ u)))
        ≤ (if (t : ℕ) = u then (1 : ℝ) else σ ^ (tdist t u - 1)) * A := by
    intro t u
    by_cases htu : (t : ℕ) = u
    · have : t = u := Fin.ext htu
      subst this
      rw [if_pos rfl, one_mul]
      exact (diag_eq P q π s T hrow hstat t).le
    · rw [if_neg htu]
      rcases lt_or_gt_of_ne htu with h | h
      · have := offdiag_le P q π s T hP hrow hπ hstat hσ hσ0 t u h
        unfold tdist
        rw [if_pos h.le]
        exact (le_abs_self _).trans this
      · have hswap : ∀ ω : Fin (T + 1) → V,
            pathProb P π T ω * (r P q π s (ω (Fin.castSucc t)) (ω (Fin.succ t))
              * r P q π s (ω (Fin.castSucc u)) (ω (Fin.succ u)))
            = pathProb P π T ω * (r P q π s (ω (Fin.castSucc u)) (ω (Fin.succ u))
              * r P q π s (ω (Fin.castSucc t)) (ω (Fin.succ t))) := fun ω => by ring
        rw [Finset.sum_congr rfl (fun ω _ => hswap ω)]
        have := offdiag_le P q π s T hP hrow hπ hstat hσ hσ0 u t h
        unfold tdist
        rw [if_neg (not_le.mpr h)]
        exact (le_abs_self _).trans this
  have hexpand : ∑ ω, pathProb P π T ω * pathErr P q π s T ω ^ 2
      = ∑ t : Fin T, ∑ u : Fin T, ∑ ω, pathProb P π T ω
          * (r P q π s (ω (Fin.castSucc t)) (ω (Fin.succ t))
            * r P q π s (ω (Fin.castSucc u)) (ω (Fin.succ u))) := by
    rw [Finset.sum_congr rfl (fun ω _ => errSq_expand P q π s T ω), Finset.sum_comm]
    exact Finset.sum_congr rfl (fun t _ => Finset.sum_comm)
  rw [hexpand]
  have hrow_bound : ∀ t : Fin T,
      ∑ u : Fin T, (if (t : ℕ) = u then (1 : ℝ) else σ ^ (tdist t u - 1)) * A
        ≤ (3 - σ) / (1 - σ) * A := by
    intro t
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ hA
    rw [Fin.sum_univ_eq_sum_range (fun u => if (t : ℕ) = u then (1 : ℝ) else σ ^ (tdist t u - 1)) T]
    exact sum_corr_coeff_le hσ0 hσ1 T t t.isLt
  calc ∑ t : Fin T, ∑ u : Fin T, ∑ ω, pathProb P π T ω
        * (r P q π s (ω (Fin.castSucc t)) (ω (Fin.succ t))
          * r P q π s (ω (Fin.castSucc u)) (ω (Fin.succ u)))
      ≤ ∑ t : Fin T, ∑ u : Fin T, (if (t : ℕ) = u then (1 : ℝ) else σ ^ (tdist t u - 1)) * A :=
        Finset.sum_le_sum (fun t _ => Finset.sum_le_sum (fun u _ => hpair t u))
    _ ≤ ∑ _t : Fin T, (3 - σ) / (1 - σ) * A := Finset.sum_le_sum (fun t _ => hrow_bound t)
    _ = (T : ℝ) * ((3 - σ) / (1 - σ)) * A := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **Unconditional `T²` bound for an arbitrary direction.** -/
theorem errSq_le_sq (hP : ∀ x y, 0 < P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (hπ : ∀ x, 0 < π x) (hstat : π ᵥ* P = π) :
    ∑ ω, pathProb P π T ω * pathErr P q π s T ω ^ 2 ≤ (T : ℝ) ^ 2 * J P q π s := by
  have hcs : ∀ ω : Fin (T + 1) → V, pathProb P π T ω * pathErr P q π s T ω ^ 2
      ≤ pathProb P π T ω * ((T : ℝ) * ∑ t : Fin T,
          r P q π s (ω (Fin.castSucc t)) (ω (Fin.succ t)) ^ 2) := by
    intro ω
    refine mul_le_mul_of_nonneg_left ?_ (pathProb_pos P hP hπ T ω).le
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin T)))
      (f := fun t => r P q π s (ω (Fin.castSucc t)) (ω (Fin.succ t)))
    simpa [pathErr, Finset.card_univ, Fintype.card_fin] using this
  have hmarg : ∑ ω, pathProb P π T ω * ((T : ℝ) * ∑ t : Fin T,
        r P q π s (ω (Fin.castSucc t)) (ω (Fin.succ t)) ^ 2)
      = (T : ℝ) * ∑ t : Fin T, J P q π s := by
    have hswap : ∀ ω : Fin (T + 1) → V, pathProb P π T ω * ((T : ℝ) * ∑ t : Fin T,
          r P q π s (ω (Fin.castSucc t)) (ω (Fin.succ t)) ^ 2)
        = (T : ℝ) * ∑ t : Fin T, pathProb P π T ω
            * (r P q π s (ω (Fin.castSucc t)) (ω (Fin.succ t))
              * r P q π s (ω (Fin.castSucc t)) (ω (Fin.succ t))) := by
      intro ω
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun t _ => by ring)
    rw [Finset.sum_congr rfl (fun ω _ => hswap ω), ← Finset.mul_sum, Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl (fun t _ => diag_eq P q π s T hrow hstat t)
  calc ∑ ω, pathProb P π T ω * pathErr P q π s T ω ^ 2
      ≤ ∑ ω, pathProb P π T ω * ((T : ℝ) * ∑ t : Fin T,
          r P q π s (ω (Fin.castSucc t)) (ω (Fin.succ t)) ^ 2) :=
        Finset.sum_le_sum (fun ω _ => hcs ω)
    _ = (T : ℝ) ^ 2 * J P q π s := by
        rw [hmarg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ### Converse for an arbitrary direction -/

lemma pathErr_cons (x : V) (ρ : Fin (T + 1) → V) :
    pathErr P q π s (T + 1) (Fin.cons x ρ) = r P q π s x (ρ 0) + pathErr P q π s T ρ := by
  unfold pathErr
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.castSucc_zero, Fin.cons_succ, ← Fin.succ_castSucc]

lemma macroPath_cons_congr {x x' : V} (hx : q x = q x') (ρ : Fin (T + 1) → V) :
    macroPath q (T + 1) (Fin.cons x ρ) = macroPath q (T + 1) (Fin.cons x' ρ) := by
  funext t
  refine Fin.cases ?_ (fun t' => ?_) t
  · simp [macroPath, hx]
  · simp [macroPath]

/-- **Lossless at any horizon `T ≥ 1` iff the residual vanishes identically:**
the step score is constant on every block pair. -/
theorem lossG_eq_zero_iff (hT : 1 ≤ T) (hP : ∀ x y, 0 < P x y) (hπ : ∀ x, 0 < π x) :
    lossG P q π s T = 0 ↔ ∀ x y, r P q π s x y = 0 := by
  constructor
  · intro h0
    obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
    rw [lossG_eq_condVar P q π s (T' + 1) hP hπ] at h0
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun ω _ =>
      mul_nonneg (pathProb_pos P hP hπ (T' + 1) ω).le (sq_nonneg _))).mp h0
    have hfix : ∀ ω, pathErr P q π s (T' + 1) ω
        = ScoreProjection.blockAvg (macroPath q (T' + 1)) (pathProb P π (T' + 1))
            (pathErr P q π s (T' + 1)) (macroPath q (T' + 1) ω) := by
      intro ω
      have := hterm ω (Finset.mem_univ ω)
      rcases mul_eq_zero.mp this with hw | hsq
      · exact absurd hw (pathProb_pos P hP hπ (T' + 1) ω).ne'
      · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
        linarith
    have key : ∀ ω ω' : Fin (T' + 2) → V, macroPath q (T' + 1) ω = macroPath q (T' + 1) ω' →
        pathErr P q π s (T' + 1) ω = pathErr P q π s (T' + 1) ω' := by
      intro ω ω' hY
      rw [hfix ω, hfix ω', hY]
    -- invariance in the first argument
    have hx : ∀ x x' y, q x = q x' → r P q π s x y = r P q π s x' y := by
      intro x x' y hxx'
      have := key (Fin.cons x (fun _ => y)) (Fin.cons x' (fun _ => y))
        (macroPath_cons_congr q T' hxx' _)
      rw [pathErr_cons, pathErr_cons] at this
      simpa using this
    -- invariance of the inner path under a block-preserving change of its first state
    have hinner : ∀ (n : ℕ) (a a' : V) (ρ : Fin n → V), q a = q a' →
        pathErr P q π s n (Fin.cons a ρ) = pathErr P q π s n (Fin.cons a' ρ) := by
      intro n a a' ρ haa'
      rcases n with _ | n
      · simp [pathErr]
      · rw [pathErr_cons, pathErr_cons, hx a a' (ρ 0) haa']
    -- invariance in the second argument
    have hy : ∀ x y y', q y = q y' → r P q π s x y = r P q π s x y' := by
      intro x y y' hyy'
      have hmac : macroPath q (T' + 1) (Fin.cons x (Fin.cons y (fun _ => y)))
          = macroPath q (T' + 1) (Fin.cons x (Fin.cons y' (fun _ => y))) := by
        funext t
        refine Fin.cases ?_ (fun t' => ?_) t
        · simp [macroPath]
        · refine Fin.cases ?_ (fun t'' => ?_) t'
          · simp [macroPath, hyy']
          · simp [macroPath]
      have := key _ _ hmac
      rw [pathErr_cons, pathErr_cons, hinner T' y y' _ hyy'] at this
      simpa using this
    -- block-pair measurable and fiber-centered ⇒ zero
    intro x y
    have hconst : ∀ x' y', q x' = q x → q y' = q y → r P q π s x' y' = r P q π s x y := by
      intro x' y' hx' hy'
      rw [hx x' x y' hx', hy x y' y hy']
    -- the fiber sum of `w · r` on the block pair of `(x, y)` vanishes (`r = m − s`)
    have hfib : ∑ ω ∈ univ.filter (fun ω : V × V => GeneralOneStep.Q q ω = (q x, q y)),
        GeneralOneStep.w P π ω * r P q π s ω.1 ω.2 = 0 := by
      have hr : ∀ ω ∈ univ.filter (fun ω : V × V => GeneralOneStep.Q q ω = (q x, q y)),
          GeneralOneStep.w P π ω * r P q π s ω.1 ω.2
            = GeneralOneStep.fiberMean P q π s (q x, q y) * GeneralOneStep.w P π ω
              - GeneralOneStep.w P π ω * s ω.1 ω.2 := by
        intro ω hω
        have hQ := (Finset.mem_filter.mp hω).2
        have hm : m P q π s (q ω.1) (q ω.2) = GeneralOneStep.fiberMean P q π s (q x, q y) := by
          unfold m
          rw [← hQ]
          rfl
        unfold r
        rw [hm]
        ring
      rw [Finset.sum_congr rfl hr, Finset.sum_sub_distrib, ← Finset.mul_sum]
      unfold GeneralOneStep.fiberMean ScoreProjection.blockAvg ScoreProjection.blockMass
      have hM : 0 < ∑ ω ∈ univ.filter (fun ω : V × V => GeneralOneStep.Q q ω = (q x, q y)),
          GeneralOneStep.w P π ω :=
        Finset.sum_pos (fun ω _ => GeneralOneStep.w_pos P π hP hπ ω) ⟨(x, y), by simp [GeneralOneStep.Q]⟩
      field_simp
      ring
    have hconstsum : ∑ ω ∈ univ.filter (fun ω : V × V => GeneralOneStep.Q q ω = (q x, q y)),
        GeneralOneStep.w P π ω * r P q π s ω.1 ω.2
        = r P q π s x y * ∑ ω ∈ univ.filter (fun ω : V × V => GeneralOneStep.Q q ω = (q x, q y)),
            GeneralOneStep.w P π ω := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ω hω => ?_)
      have hQ := (Finset.mem_filter.mp hω).2
      simp only [GeneralOneStep.Q, Prod.mk.injEq] at hQ
      rw [hconst ω.1 ω.2 hQ.1 hQ.2]
      ring
    rw [hconstsum] at hfib
    have hM : 0 < ∑ ω ∈ univ.filter (fun ω : V × V => GeneralOneStep.Q q ω = (q x, q y)),
        GeneralOneStep.w P π ω :=
      Finset.sum_pos (fun ω _ => GeneralOneStep.w_pos P π hP hπ ω) ⟨(x, y), by simp [GeneralOneStep.Q]⟩
    rcases mul_eq_zero.mp hfib with h | h
    · exact h
    · exact absurd h hM.ne'
  · intro hr
    have he : pathErr P q π s T = fun _ => 0 :=
      funext (fun ω => Finset.sum_eq_zero (fun t _ => hr _ _))
    rw [lossG_eq_condVar P q π s T hP hπ, he]
    simp [ScoreProjection.blockAvg]

/-! ### Headline bounds in terms of `J₁` -/

/-- **`loss(T) ≤ T² · J₁`** for any direction. -/
theorem lossG_le_sq (hP : ∀ x y, 0 < P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (hπ : ∀ x, 0 < π x) (hstat : π ᵥ* P = π) :
    lossG P q π s T ≤ (T : ℝ) ^ 2 * GeneralOneStep.J1 P q π s := by
  rw [← J_eq_J1]
  exact (lossG_le_errSq P q π s T hP hπ).trans (errSq_le_sq P q π s T hP hrow hπ hstat)

/-- **`loss(T) ≤ T · (3−σ)/(1−σ) · J₁`** for any direction, under mixing. -/
theorem lossG_le_mixing (hP : ∀ x y, 0 < P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (hπ : ∀ x, 0 < π x) (hstat : π ᵥ* P = π) {σ : ℝ} (hσ : MixingContraction P π σ)
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    lossG P q π s T ≤ (T : ℝ) * ((3 - σ) / (1 - σ)) * GeneralOneStep.J1 P q π s := by
  rw [← J_eq_J1]
  exact (lossG_le_errSq P q π s T hP hπ).trans
    (errSq_le_linear P q π s T hP hrow hπ hstat hσ hσ0 hσ1)

/-- **Unconditional linear bound** via a Doeblin constant `c`: `loss(T) ≤ T · (2+c)/c · J₁`. -/
theorem lossG_le_doeblin (hP : ∀ x y, 0 < P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (hπ : ∀ x, 0 < π x) (hsum : ∑ x, π x = 1) (hstat : π ᵥ* P = π) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hmin : ∀ x y, c * π y ≤ P x y) :
    lossG P q π s T ≤ (T : ℝ) * ((2 + c) / c) * GeneralOneStep.J1 P q π s := by
  have hσ := mixingContraction_of_doeblin P (fun x => (hπ x).le) hsum hstat hrow hc1 hmin
  have h := lossG_le_mixing P q π s T hP hrow hπ hstat hσ (by linarith) (by linarith)
  have heq : (3 - (1 - c)) / (1 - (1 - c)) = (2 + c) / c := by ring_nf
  rwa [heq] at h

end SGC.InformationGeometry.GeneralPathBound
