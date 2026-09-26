/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.InformationGeometry.MarkovPathFisher
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Linear-in-time directional closure bound under mixing

Continues `MarkovPathFisher` (same setting H1-H5; reversibility is NOT assumed).
Mixing enters through a named hypothesis on the `L²(π)` operator norm of `P`
on mean-zero functions:

  `MixingContraction P π σ : ∀ f, Σ π f = 0 → Σ π (P f)² ≤ σ² Σ π f²`.

## Main results

* `sum_pathProb_two` — two-time path marginals:
  `E[f(X_j) g(X_k)] = Σ_x (μ Pʲ)(x) f(x) (P^{k-j} g)(x)` for `j ≤ k`.
* `corr_le` — `|⟨f, Pᵏ f⟩_π| ≤ σᵏ ‖f‖²_π` for mean-zero `f`.
* `sum_dist_pow_le` — `Σ_{t<T} σ^{|t-s|} ≤ (1+σ)/(1-σ)`.
* `fisherLoss_markov_path_le_mixing` — **linear bound**:
  `loss(T) ≤ T · (1+σ)/(1-σ) · Bmax · D_π²`.
* `fisherLoss_markov_path_le_mixing_measureReentry` — the same with the
  canonical `MeasureReentry.defectSq` for a `Partition`.

* `mixingContraction_of_doeblin` — if `P x y ≥ c π y`, then
  `MixingContraction P π (1 - c)` (no reversibility needed);
  `exists_doeblin` — every strictly positive kernel has such `c > 0`.
* `fisherLoss_markov_path_le_doeblin` — **unconditional linear bound**:
  `loss(T) ≤ T · (2 - c)/c · Bmax · 𝔇_π²`.
-/

noncomputable section

namespace SGC.InformationGeometry.MarkovPathMixing

open Finset Matrix SGC.InformationGeometry.MarkovPathFisher

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Two-time marginals -/

lemma sum_pathProb_row (P : Matrix V V ℝ) (μ : V → ℝ) (T : ℕ) (ω : Fin (T + 1) → V) :
    ∑ x, μ x * pathProb P (P x) T ω = pathProb P (μ ᵥ* P) T ω := by
  unfold pathProb
  simp only [vecMul, dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun x _ => by ring)

lemma pathProb_total (P : Matrix V V ℝ) (hrow : ∀ x, ∑ y, P x y = 1) (T : ℕ) (ν : V → ℝ) :
    ∑ ω, pathProb P ν T ω = ∑ x, ν x := by
  have h := sum_pathProb_marginal P hrow T 0 ν (fun _ => 1)
  simpa using h

lemma sum_vecMul_eq_mulVec (P M : Matrix V V ℝ) (x : V) (g : V → ℝ) :
    ∑ y, (P x ᵥ* M) y * g y = ((P * M) *ᵥ g) x := by
  rw [← mulVec_mulVec]
  have h := dotProduct_mulVec (P x) M g
  simp only [dotProduct] at h
  rw [← h]
  rfl

/-- **Two-time path marginals.** -/
theorem sum_pathProb_two (P : Matrix V V ℝ) (hrow : ∀ x, ∑ y, P x y = 1) :
    ∀ (T : ℕ) (j k : Fin (T + 1)), (j : ℕ) ≤ k → ∀ (μ f g : V → ℝ),
      ∑ ω, pathProb P μ T ω * (f (ω j) * g (ω k))
        = ∑ x, (μ ᵥ* P ^ (j : ℕ)) x * (f x * (P ^ ((k : ℕ) - j) *ᵥ g) x) := by
  intro T
  induction T with
  | zero =>
    intro j k _ μ f g
    obtain ⟨j, hj⟩ := j
    obtain ⟨k, hk⟩ := k
    obtain rfl : j = 0 := by omega
    obtain rfl : k = 0 := by omega
    change ∑ ω : Fin 1 → V, pathProb P μ 0 ω * (f (ω 0) * g (ω 0)) = _
    rw [← (Equiv.funUnique (Fin 1) V).symm.sum_comp]
    simp [pathProb]
  | succ T ih =>
    intro j k hjk μ f g
    rw [MarkovPathFisher.sum_cons]
    simp only [pathProb_cons]
    revert hjk
    refine Fin.cases ?_ (fun j' => ?_) j <;> refine Fin.cases ?_ (fun k' => ?_) k <;> intro hjk
    · -- j = 0, k = 0
      simp only [Fin.cons_zero, Fin.val_zero, pow_zero, vecMul_one, Nat.sub_self, one_mulVec]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      have hs : ∑ ω' : Fin (T + 1) → V, μ x * pathProb P (P x) T ω' * (f x * g x)
          = μ x * (f x * g x) * ∑ ω', pathProb P (P x) T ω' := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun ω' _ => by ring)
      rw [hs, pathProb_total P hrow, hrow x, mul_one]
    · -- j = 0, k = k' + 1
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, vecMul_one, Fin.val_succ,
        Nat.sub_zero]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      have hs : ∑ ω' : Fin (T + 1) → V, μ x * pathProb P (P x) T ω' * (f x * g (ω' k'))
          = μ x * f x * ∑ ω', pathProb P (P x) T ω' * g (ω' k') := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun ω' _ => by ring)
      rw [hs, sum_pathProb_marginal P hrow T k' (P x) g, sum_vecMul_eq_mulVec, ← pow_succ']
      ring
    · -- j = j' + 1, k = 0: impossible
      simp at hjk
    · -- j = j' + 1, k = k' + 1
      simp only [Fin.cons_succ, Fin.val_succ] at hjk ⊢
      have hs : ∑ x, ∑ ω' : Fin (T + 1) → V, μ x * pathProb P (P x) T ω' * (f (ω' j') * g (ω' k'))
          = ∑ ω', pathProb P (μ ᵥ* P) T ω' * (f (ω' j') * g (ω' k')) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun ω' _ => ?_)
        rw [← sum_pathProb_row, Finset.sum_mul]
      rw [hs, ih j' k' (by omega) (μ ᵥ* P) f g, Nat.add_sub_add_right, vecMul_vecMul, ← pow_succ']

/-! ### Contraction on mean-zero functions -/

/-- Mixing hypothesis: `σ` bounds the `L²(π)` operator norm of `P` on mean-zero
functions. -/
def MixingContraction (P : Matrix V V ℝ) (π : V → ℝ) (σ : ℝ) : Prop :=
  ∀ f : V → ℝ, ∑ x, π x * f x = 0 → ∑ x, π x * (P *ᵥ f) x ^ 2 ≤ σ ^ 2 * ∑ x, π x * f x ^ 2

lemma mean_mulVec (P : Matrix V V ℝ) {π : V → ℝ} (hstat : π ᵥ* P = π) (f : V → ℝ) :
    ∑ x, π x * (P *ᵥ f) x = ∑ x, π x * f x := by
  have h := dotProduct_mulVec π P f
  rw [hstat] at h
  simpa [dotProduct] using h

lemma mean_pow_mulVec (P : Matrix V V ℝ) {π : V → ℝ} (hstat : π ᵥ* P = π) (f : V → ℝ) :
    ∀ k : ℕ, ∑ x, π x * (P ^ k *ᵥ f) x = ∑ x, π x * f x := by
  intro k
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', ← mulVec_mulVec, mean_mulVec P hstat, ih]

lemma pow_contract (P : Matrix V V ℝ) {π : V → ℝ} {σ : ℝ} (hstat : π ᵥ* P = π)
    (hσ : MixingContraction P π σ) (f : V → ℝ) (hf : ∑ x, π x * f x = 0) :
    ∀ k : ℕ, ∑ x, π x * (P ^ k *ᵥ f) x ^ 2 ≤ (σ ^ 2) ^ k * ∑ x, π x * f x ^ 2 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← mulVec_mulVec]
    have hm : ∑ x, π x * (P ^ k *ᵥ f) x = 0 := by rw [mean_pow_mulVec P hstat f k, hf]
    calc ∑ x, π x * (P *ᵥ (P ^ k *ᵥ f)) x ^ 2
        ≤ σ ^ 2 * ∑ x, π x * (P ^ k *ᵥ f) x ^ 2 := hσ _ hm
      _ ≤ σ ^ 2 * ((σ ^ 2) ^ k * ∑ x, π x * f x ^ 2) :=
          mul_le_mul_of_nonneg_left ih (sq_nonneg σ)
      _ = (σ ^ 2) ^ (k + 1) * ∑ x, π x * f x ^ 2 := by ring

lemma weighted_cs {π : V → ℝ} (hπ : ∀ x, 0 ≤ π x) (a c : V → ℝ) :
    (∑ x, π x * (a x * c x)) ^ 2 ≤ (∑ x, π x * a x ^ 2) * ∑ x, π x * c x ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq univ (fun x => Real.sqrt (π x) * a x)
    (fun x => Real.sqrt (π x) * c x)
  have e1 : ∀ x, Real.sqrt (π x) * a x * (Real.sqrt (π x) * c x) = π x * (a x * c x) := by
    intro x
    have := Real.mul_self_sqrt (hπ x)
    calc _ = (Real.sqrt (π x) * Real.sqrt (π x)) * (a x * c x) := by ring
      _ = _ := by rw [this]
  have e2 : ∀ x (u : V → ℝ), (Real.sqrt (π x) * u x) ^ 2 = π x * u x ^ 2 := by
    intro x u
    rw [mul_pow, Real.sq_sqrt (hπ x)]
  simp only [e1] at h
  simpa only [e2] using h

/-- **Doeblin contraction.** If `P x y ≥ c · π y` for all `x y` (with `π` a
stationary probability vector), then `MixingContraction P π (1 - c)`. Every
strictly positive kernel satisfies this with some `c > 0`, so the mixing
hypothesis is never vacuous for such kernels. -/
theorem mixingContraction_of_doeblin (P : Matrix V V ℝ) {π : V → ℝ} (hπ : ∀ x, 0 ≤ π x)
    (hsum : ∑ x, π x = 1) (hstat : π ᵥ* P = π) (hrow : ∀ x, ∑ y, P x y = 1) {c : ℝ}
    (hc1 : c ≤ 1) (hmin : ∀ x y, c * π y ≤ P x y) : MixingContraction P π (1 - c) := by
  intro f hf
  set R : V → V → ℝ := fun x y => P x y - c * π y
  have hR : ∀ x y, 0 ≤ R x y := fun x y => sub_nonneg.mpr (hmin x y)
  have hPf : ∀ x, (P *ᵥ f) x = ∑ y, R x y * f y := by
    intro x
    simp only [mulVec, dotProduct, R, sub_mul, Finset.sum_sub_distrib]
    have : ∑ y, c * π y * f y = c * ∑ y, π y * f y := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun y _ => by ring)
    rw [this, hf, mul_zero, sub_zero]
  have hrowR : ∀ x, ∑ y, R x y = 1 - c := by
    intro x
    simp only [R, Finset.sum_sub_distrib, ← Finset.mul_sum, hrow x, hsum, mul_one]
  have hcolR : ∀ y, ∑ x, π x * R x y = (1 - c) * π y := by
    intro y
    have hs : ∑ x, π x * P x y = π y := by
      have := congrFun hstat y
      simpa [vecMul, dotProduct] using this
    simp only [R, mul_sub, Finset.sum_sub_distrib, hs]
    have : ∑ x, π x * (c * π y) = c * π y := by
      rw [← Finset.sum_mul, hsum, one_mul]
    rw [this]
    ring
  have hcs : ∀ x, (∑ y, R x y * f y) ^ 2 ≤ (1 - c) * ∑ y, R x y * f y ^ 2 := by
    intro x
    have h := weighted_cs (hR x) (fun _ => 1) f
    simp only [one_mul, one_pow, mul_one] at h
    rwa [hrowR x] at h
  have h1c : 0 ≤ 1 - c := by linarith
  calc ∑ x, π x * (P *ᵥ f) x ^ 2
      = ∑ x, π x * (∑ y, R x y * f y) ^ 2 := by simp only [hPf]
    _ ≤ ∑ x, π x * ((1 - c) * ∑ y, R x y * f y ^ 2) :=
        Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hcs x) (hπ x))
    _ = (1 - c) * ∑ y, (∑ x, π x * R x y) * f y ^ 2 := by
        rw [Finset.mul_sum]
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x _ => by ring))
    _ = (1 - c) ^ 2 * ∑ x, π x * f x ^ 2 := by
        simp only [hcolR]
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun y _ => by ring)

/-- **Correlation decay.** -/
theorem corr_le (P : Matrix V V ℝ) {π : V → ℝ} {σ : ℝ} (hπ : ∀ x, 0 ≤ π x)
    (hstat : π ᵥ* P = π) (hσ : MixingContraction P π σ) (hσ0 : 0 ≤ σ)
    (f : V → ℝ) (hf : ∑ x, π x * f x = 0) (k : ℕ) :
    |∑ x, π x * (f x * (P ^ k *ᵥ f) x)| ≤ σ ^ k * ∑ x, π x * f x ^ 2 := by
  set A := ∑ x, π x * f x ^ 2
  have hA : 0 ≤ A := Finset.sum_nonneg (fun x _ => mul_nonneg (hπ x) (sq_nonneg _))
  refine abs_le_of_sq_le_sq ?_ (mul_nonneg (pow_nonneg hσ0 k) hA)
  calc (∑ x, π x * (f x * (P ^ k *ᵥ f) x)) ^ 2
      ≤ A * ∑ x, π x * (P ^ k *ᵥ f) x ^ 2 := weighted_cs hπ f _
    _ ≤ A * ((σ ^ 2) ^ k * A) := mul_le_mul_of_nonneg_left (pow_contract P hstat hσ f hf k) hA
    _ = (σ ^ k * A) ^ 2 := by ring

/-! ### Two-sided geometric sum -/

/-- Distance between two times. -/
def tdist (s t : ℕ) : ℕ := if s ≤ t then t - s else s - t

lemma geom_range_le {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (n : ℕ) :
    ∑ k ∈ range n, σ ^ k ≤ 1 / (1 - σ) := by
  have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hσ0 hσ1
  rwa [← Finset.range_eq_Ico, pow_zero] at h

theorem sum_dist_pow_le {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (T s : ℕ) (hs : s ≤ T) :
    ∑ t ∈ range T, σ ^ tdist s t ≤ (1 + σ) / (1 - σ) := by
  rw [← Finset.sum_range_add_sum_Ico _ hs]
  have h1 : ∑ t ∈ range s, σ ^ tdist s t = σ * ∑ j ∈ range s, σ ^ j := by
    rw [← Finset.sum_range_reflect, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj' := Finset.mem_range.mp hj
    unfold tdist
    rw [if_neg (by omega), show s - (s - 1 - j) = j + 1 by omega, pow_succ]
    ring
  have h2 : ∑ t ∈ Ico s T, σ ^ tdist s t = ∑ k ∈ range (T - s), σ ^ k := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    unfold tdist
    rw [if_pos (by omega), show s + k - s = k by omega]
  rw [h1, h2]
  have g1 := geom_range_le hσ0 hσ1 s
  have g2 := geom_range_le hσ0 hσ1 (T - s)
  have hden : 0 < 1 - σ := by linarith
  calc σ * ∑ j ∈ range s, σ ^ j + ∑ k ∈ range (T - s), σ ^ k
      ≤ σ * (1 / (1 - σ)) + 1 / (1 - σ) := by nlinarith
    _ = (1 + σ) / (1 - σ) := by field_simp; ring

/-! ### Linear bound on path space -/

variable {β : Type*} [Fintype β] [DecidableEq β]

theorem pathDefect_sq_le_linear (P : Matrix V V ℝ) (q : V → β) (π : V → ℝ) (b : β → β → ℝ)
    (T : ℕ) (hrow : ∀ x, ∑ y, P x y = 1) (hπ : ∀ x, 0 < π x) (hstat : π ᵥ* P = π)
    {σ : ℝ} (hσ : MixingContraction P π σ) (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    ∑ ω, pathProb P π T ω * pathDefect P q π b T ω ^ 2
      ≤ (T : ℝ) * ((1 + σ) / (1 - σ))
          * ∑ x, π x * BlockPairTilt.delta q π (blockExit P q) b x ^ 2 := by
  set δ := BlockPairTilt.delta q π (blockExit P q) b
  set A := ∑ x, π x * δ x ^ 2
  have hA : 0 ≤ A := Finset.sum_nonneg (fun x _ => mul_nonneg (hπ x).le (sq_nonneg _))
  have hmean : ∑ x, π x * δ x = 0 := BlockPairTilt.delta_mean_zero q π (blockExit P q) b hπ
  -- correlation of the defect at two times
  have hpair : ∀ s t : Fin T,
      |∑ ω, pathProb P π T ω * (δ (ω (Fin.castSucc s)) * δ (ω (Fin.castSucc t)))|
        ≤ σ ^ tdist s t * A := by
    intro s t
    by_cases hst : (s : ℕ) ≤ t
    · rw [sum_pathProb_two P hrow T _ _ (by simpa using hst), vecMul_pow_stationary P hstat]
      have := corr_le P (fun x => (hπ x).le) hstat hσ hσ0 δ hmean ((t : ℕ) - s)
      simpa [tdist, hst] using this
    · have hswap : ∀ ω : Fin (T + 1) → V, pathProb P π T ω * (δ (ω (Fin.castSucc s))
          * δ (ω (Fin.castSucc t))) = pathProb P π T ω * (δ (ω (Fin.castSucc t))
          * δ (ω (Fin.castSucc s))) := fun ω => by ring
      rw [Finset.sum_congr rfl (fun ω _ => hswap ω),
        sum_pathProb_two P hrow T _ _ (by simp; omega), vecMul_pow_stationary P hstat]
      have := corr_le P (fun x => (hπ x).le) hstat hσ hσ0 δ hmean ((s : ℕ) - t)
      simpa [tdist, hst] using this
  have hexpand : ∑ ω, pathProb P π T ω * pathDefect P q π b T ω ^ 2
      = ∑ s : Fin T, ∑ t : Fin T,
          ∑ ω, pathProb P π T ω * (δ (ω (Fin.castSucc s)) * δ (ω (Fin.castSucc t))) := by
    have hω : ∀ ω : Fin (T + 1) → V, pathProb P π T ω * pathDefect P q π b T ω ^ 2
        = ∑ s : Fin T, ∑ t : Fin T,
            pathProb P π T ω * (δ (ω (Fin.castSucc s)) * δ (ω (Fin.castSucc t))) := by
      intro ω
      unfold pathDefect
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun s _ => by rw [Finset.mul_sum])
    rw [Finset.sum_congr rfl (fun ω _ => hω ω), Finset.sum_comm]
    exact Finset.sum_congr rfl (fun s _ => Finset.sum_comm)
  rw [hexpand]
  have hrow_bound : ∀ s : Fin T, ∑ t : Fin T, σ ^ tdist s t * A ≤ (1 + σ) / (1 - σ) * A := by
    intro s
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ hA
    rw [Fin.sum_univ_eq_sum_range (fun t => σ ^ tdist s t) T]
    exact sum_dist_pow_le hσ0 hσ1 T s (by omega)
  calc ∑ s : Fin T, ∑ t : Fin T,
        ∑ ω, pathProb P π T ω * (δ (ω (Fin.castSucc s)) * δ (ω (Fin.castSucc t)))
      ≤ ∑ s : Fin T, ∑ t : Fin T, σ ^ tdist s t * A :=
        Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun t _ => (le_abs_self _).trans (hpair s t)))
    _ ≤ ∑ _s : Fin T, (1 + σ) / (1 - σ) * A := Finset.sum_le_sum (fun s _ => hrow_bound s)
    _ = (T : ℝ) * ((1 + σ) / (1 - σ)) * A := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **Linear-in-time directional closure bound.** -/
theorem fisherLoss_markov_path_le_mixing (P : Matrix V V ℝ) (q : V → β) (π : V → ℝ)
    (b : β → β → ℝ) (T : ℕ) (hP : ∀ x y, 0 < P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (hπ : ∀ x, 0 < π x) (hstat : π ᵥ* P = π) {σ : ℝ} (hσ : MixingContraction P π σ)
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) {Bmax : ℝ} (hB : ∀ A, ∑ C, b A C ^ 2 ≤ Bmax) :
    ScoreProjection.fineFisher (pathProb P π T) (pathDeriv P q π b T)
      - ScoreProjection.coarseFisher (macroPath q T) (pathProb P π T) (pathDeriv P q π b T)
      ≤ (T : ℝ) * ((1 + σ) / (1 - σ)) * (Bmax * BlockPairTilt.defectSq q π (blockExit P q)) := by
  have h1 := ScoreProjection.fisherLoss_le_errorSq (macroPath q T) (pathDeriv P q π b T)
    (pathProb_pos P hP hπ T) (fun ω => surrogate P q π b T (macroPath q T ω))
    (pathDefect P q π b T) (surrogate P q π b T) (fun _ => rfl) (pathDeriv_div P q π b T hP hπ)
  have h2 := pathDefect_sq_le_linear P q π b T hrow hπ hstat hσ hσ0 hσ1
  have h3 := BlockPairTilt.delta_energy_le q π (blockExit P q) b hπ hB
  have hc : 0 ≤ (T : ℝ) * ((1 + σ) / (1 - σ)) :=
    mul_nonneg (Nat.cast_nonneg T) (div_nonneg (by linarith) (by linarith))
  exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 hc))

open SGC in
/-- **Headline (linear).** With the canonical measure-reentry defect. -/
theorem fisherLoss_markov_path_le_mixing_measureReentry (P : Matrix V V ℝ) (π : V → ℝ)
    (T : ℕ) (Part : Partition V) (hP : ∀ x y, 0 < P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (hπ : ∀ x, 0 < π x) (hstat : π ᵥ* P = π) {σ : ℝ} (hσ : MixingContraction P π σ)
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (b : Part.Quot → Part.Quot → ℝ) {Bmax : ℝ}
    (hB : ∀ A, ∑ C, b A C ^ 2 ≤ Bmax) :
    ScoreProjection.fineFisher (pathProb P π T) (pathDeriv P Part.quot_map π b T)
      - ScoreProjection.coarseFisher (macroPath Part.quot_map T) (pathProb P π T)
          (pathDeriv P Part.quot_map π b T)
      ≤ (T : ℝ) * ((1 + σ) / (1 - σ))
          * (Bmax * SGC.Renormalization.MeasureReentry.defectSq P Part π) := by
  rw [← defectSq_eq_measureReentry P π Part hπ]
  exact fisherLoss_markov_path_le_mixing P Part.quot_map π b T hP hrow hπ hstat hσ hσ0 hσ1 hB

/-- Every strictly positive stochastic kernel has a Doeblin constant: take
`c = min P`. -/
theorem exists_doeblin [Nonempty V] (P : Matrix V V ℝ) (hP : ∀ x y, 0 < P x y)
    (hrow : ∀ x, ∑ y, P x y = 1) {π : V → ℝ} (hπ : ∀ x, 0 ≤ π x) (hsum : ∑ x, π x = 1) :
    ∃ c, 0 < c ∧ c ≤ 1 ∧ ∀ x y, c * π y ≤ P x y := by
  obtain ⟨⟨x₀, y₀⟩, hmin⟩ := Finite.exists_min (fun p : V × V => P p.1 p.2)
  refine ⟨P x₀ y₀, hP x₀ y₀, ?_, fun x y => ?_⟩
  · calc P x₀ y₀ ≤ ∑ y, P x₀ y :=
          Finset.single_le_sum (fun y _ => (hP x₀ y).le) (Finset.mem_univ y₀)
      _ = 1 := hrow x₀
  · have hπ1 : π y ≤ 1 := hsum ▸ Finset.single_le_sum (fun x _ => hπ x) (Finset.mem_univ y)
    calc P x₀ y₀ * π y ≤ P x₀ y₀ * 1 := mul_le_mul_of_nonneg_left hπ1 (hP x₀ y₀).le
      _ = P x₀ y₀ := mul_one _
      _ ≤ P x y := hmin (x, y)

open SGC in
/-- **Unconditional linear bound.** For a strictly positive kernel with
Doeblin constant `c > 0` (`P x y ≥ c π y`), no mixing hypothesis is needed:
`loss(T) ≤ T · (2 - c)/c · Bmax · 𝔇_π²`. -/
theorem fisherLoss_markov_path_le_doeblin (P : Matrix V V ℝ) (π : V → ℝ) (T : ℕ)
    (Part : Partition V) (hP : ∀ x y, 0 < P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (hπ : ∀ x, 0 < π x) (hsum : ∑ x, π x = 1) (hstat : π ᵥ* P = π) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hmin : ∀ x y, c * π y ≤ P x y)
    (b : Part.Quot → Part.Quot → ℝ) {Bmax : ℝ} (hB : ∀ A, ∑ C, b A C ^ 2 ≤ Bmax) :
    ScoreProjection.fineFisher (pathProb P π T) (pathDeriv P Part.quot_map π b T)
      - ScoreProjection.coarseFisher (macroPath Part.quot_map T) (pathProb P π T)
          (pathDeriv P Part.quot_map π b T)
      ≤ (T : ℝ) * ((2 - c) / c)
          * (Bmax * SGC.Renormalization.MeasureReentry.defectSq P Part π) := by
  have hσ := mixingContraction_of_doeblin P (fun x => (hπ x).le) hsum hstat hrow hc1 hmin
  have h := fisherLoss_markov_path_le_mixing_measureReentry P π T Part hP hrow hπ hstat hσ
    (by linarith) (by linarith) b hB
  have heq : (1 + (1 - c)) / (1 - (1 - c)) = (2 - c) / c := by ring_nf
  rwa [heq] at h

end SGC.InformationGeometry.MarkovPathMixing
