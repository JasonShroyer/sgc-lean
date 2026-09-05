/-
Copyright (c) 2026 Jason Shroyer. All rights reserved.
Released under Apache 2.0 license.
-/
import SGC.Observation.ObservationalEntropy

/-!
# The Entropic Square (T3) and the ε-H-Theorem (T4)

The summit of the entropic-bridge program (insight 0020; review of
2026-09-04). Two theorems weld observational entropy's second laws to the
square calculus:

* **T3, `entropic_square_exact`** — the exact H-theorem for a commuting
  description square, WITH its transfer conditions: macro-stationarity
  plus DPI give macro relative-entropy contraction (`macro_H_step`), and
  exact closure (intertwining + compatibility + compatible
  initialization) licenses reading that contraction as a statement about
  the OBSERVED fine evolution. Neither ingredient alone suffices — the
  2026-09-04 review's hierarchy, formalized.

* **T4, `epsilon_H_theorem`** — the defect-priced second law: for an
  ε-closed square, the observed coarse relative entropy can violate
  monotonicity by at most
  `(1 + |log c| + B) · (2n+1) · ‖𝒟‖`
  at step `n`, under declared floors (`c` ≤ observed and model marginals
  ≤ 1), a log-bounded reference (`|log τ̄| ≤ B`), and the L∞ contraction
  convention. The constant inherits exactly what the review predicted:
  the horizon growth of the trajectory error, the continuity modulus of
  entropy (`xlogx_diff_le` — unstable near vanishing mass, hence the
  floor), and the reference's support behavior. That complexity is the
  physics, not a nuisance.

## Honest scope

Finite spaces; deterministic-readout regime; floors and log-bounds are
HYPOTHESES (the instrument must check them — receipts carry them as
scope fields); the bound is an upper bound. Everything else is exactly
as stated: zero sorries, kernel axioms only.
-/

namespace SGC.Observation

open Finset Matrix
open scoped NNReal

attribute [local instance] Matrix.linftyOpNormedAddCommGroup

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-! ## §1. Kernel powers -/

theorem isKernel_one : IsKernel (1 : Matrix X X ℝ) where
  nonneg := by
    intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  row_sum_one := by
    intro i
    simp [Matrix.one_apply]

theorem IsKernel.pow {P : Matrix X X ℝ} (hP : IsKernel P) (n : ℕ) :
    IsKernel (P ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact isKernel_one
  | succ n ih => rw [pow_succ]; exact ih.mul hP

/-! ## §2. The macro H-theorem and the exact entropic square (T3) -/

/-- **Macro H-step**: stationarity + DPI ⟹ relative-entropy contraction
under the macro kernel. Requires NO lumpability — this is the review's
first hierarchy level. -/
theorem macro_H_step {Pbar : Matrix Y Y ℝ} (hPbar : IsKernel Pbar)
    {τbar ν : Y → ℝ} (hstat : Matrix.vecMul τbar Pbar = τbar)
    (hτpos : ∀ y, 0 < τbar y) (hν : ∀ y, 0 ≤ ν y) :
    klDiv (Matrix.vecMul ν Pbar) τbar ≤ klDiv ν τbar := by
  have hqM : ∀ y, 0 < pushforward Pbar τbar y := by
    intro y
    show 0 < Matrix.vecMul τbar Pbar y
    rw [hstat]
    exact hτpos y
  have h := klDiv_dpi Pbar hPbar ν τbar hν hτpos hqM
  have hrw : pushforward Pbar τbar = τbar := hstat
  rw [hrw] at h
  exact h

/-- **T3: the exact entropic square.** Exact closure (compatibility +
intertwining + compatible initialization) transfers the macro H-theorem
to the OBSERVED fine evolution: the readout marginal's relative entropy
to the stationary reference is monotone under the true dynamics. The
second hierarchy level: closure is what licenses the physical reading. -/
theorem entropic_square_exact (P : Matrix X X ℝ) (Pbar : Matrix Y Y ℝ)
    (Lam : Matrix Y X ℝ) (pi_map : X → Y)
    (hcomp : Compatible pi_map Lam) (hint : Intertwines P Pbar Lam)
    (hPbar : IsKernel Pbar) (μY τbar : Y → ℝ) (hμ0 : ∀ y, 0 ≤ μY y)
    (hstat : Matrix.vecMul τbar Pbar = τbar) (hτpos : ∀ y, 0 < τbar y)
    (n : ℕ) :
    klDiv (push pi_map
        (Matrix.vecMul (Matrix.vecMul μY Lam) (P ^ (n + 1)))) τbar
      ≤ klDiv (push pi_map
          (Matrix.vecMul (Matrix.vecMul μY Lam) (P ^ n))) τbar := by
  rw [(observation_closure_exact P Pbar Lam pi_map hcomp hint μY (n + 1)).2,
      (observation_closure_exact P Pbar Lam pi_map hcomp hint μY n).2]
  have hrw : Matrix.vecMul μY (Pbar ^ (n + 1))
      = Matrix.vecMul (Matrix.vecMul μY (Pbar ^ n)) Pbar := by
    rw [Matrix.vecMul_vecMul, ← pow_succ]
  rw [hrw]
  exact macro_H_step hPbar hstat hτpos
    (fun y => pushforward_nonneg (hPbar.pow n) hμ0 y)

/-! ## §3. Entropy continuity under a mass floor -/

private lemma xlogx_diff_le_of_le {c a b : ℝ} (hc : 0 < c) (hab : b ≤ a)
    (ha : a ∈ Set.Icc c 1) (hb : b ∈ Set.Icc c 1) :
    |a * Real.log a - b * Real.log b| ≤ (1 + |Real.log c|) * (a - b) := by
  have hbpos : 0 < b := lt_of_lt_of_le hc hb.1
  have hapos : 0 < a := lt_of_lt_of_le hc ha.1
  have hdecomp : a * Real.log a - b * Real.log b
      = (a - b) * Real.log a + b * (Real.log a - Real.log b) := by ring
  have hla : |Real.log a| ≤ |Real.log c| := by
    have h1 : Real.log a ≤ 0 := Real.log_nonpos hapos.le ha.2
    have h2 : Real.log c ≤ Real.log a := Real.log_le_log hc ha.1
    have h3 : Real.log c ≤ 0 := h2.trans h1
    rw [abs_of_nonpos h1, abs_of_nonpos h3]
    linarith
  have hmono : Real.log b ≤ Real.log a := Real.log_le_log hbpos hab
  have hub : b * (Real.log a - Real.log b) ≤ a - b := by
    have hlog : Real.log a - Real.log b ≤ a / b - 1 := by
      have h := Real.log_le_sub_one_of_pos (div_pos hapos hbpos)
      rwa [Real.log_div hapos.ne' hbpos.ne'] at h
    calc b * (Real.log a - Real.log b) ≤ b * (a / b - 1) :=
          mul_le_mul_of_nonneg_left hlog hbpos.le
      _ = a - b := by field_simp
  have hnn : 0 ≤ b * (Real.log a - Real.log b) :=
    mul_nonneg hbpos.le (by linarith)
  rw [hdecomp]
  calc |(a - b) * Real.log a + b * (Real.log a - Real.log b)|
      ≤ |(a - b) * Real.log a| + |b * (Real.log a - Real.log b)| :=
        abs_add_le _ _
    _ = (a - b) * |Real.log a| + b * (Real.log a - Real.log b) := by
        rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ a - b),
            abs_of_nonneg hnn]
    _ ≤ (a - b) * |Real.log c| + (a - b) :=
        add_le_add (mul_le_mul_of_nonneg_left hla (by linarith)) hub
    _ = (1 + |Real.log c|) * (a - b) := by ring

/-- `x·log x` is Lipschitz on `[c, 1]` with constant `1 + |log c|`: the
continuity modulus of entropy under a mass floor. The blow-up as
`c → 0` is real physics — entropy is unstable near vanishing mass. -/
lemma xlogx_diff_le {c a b : ℝ} (hc : 0 < c)
    (ha : a ∈ Set.Icc c 1) (hb : b ∈ Set.Icc c 1) :
    |a * Real.log a - b * Real.log b| ≤ (1 + |Real.log c|) * |a - b| := by
  rcases le_total b a with h | h
  · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ a - b)]
    exact xlogx_diff_le_of_le hc h ha hb
  · have h1 : |a * Real.log a - b * Real.log b|
        = |b * Real.log b - a * Real.log a| := abs_sub_comm _ _
    have h2 : |a - b| = b - a := by
      rw [abs_sub_comm]
      exact abs_of_nonneg (by linarith)
    rw [h1, h2]
    exact xlogx_diff_le_of_le hc h hb ha

/-- KL continuity in the first argument, under a mass floor and a
log-bounded reference: linear modulus with the explicit constant
`1 + |log c| + B`. -/
lemma klDiv_continuity {c B : ℝ} (hc : 0 < c) {p r τ : Y → ℝ}
    (hτ : ∀ y, 0 < τ y) (hτB : ∀ y, |Real.log (τ y)| ≤ B)
    (hp : ∀ y, p y ∈ Set.Icc c 1) (hr : ∀ y, r y ∈ Set.Icc c 1) :
    |klDiv p τ - klDiv r τ|
      ≤ (1 + |Real.log c| + B) * ∑ y, |p y - r y| := by
  have hppos : ∀ y, 0 < p y := fun y => lt_of_lt_of_le hc (hp y).1
  have hrpos : ∀ y, 0 < r y := fun y => lt_of_lt_of_le hc (hr y).1
  have hterm : ∀ y, p y * Real.log (p y / τ y) - r y * Real.log (r y / τ y)
      = (p y * Real.log (p y) - r y * Real.log (r y))
        - (p y - r y) * Real.log (τ y) := by
    intro y
    rw [Real.log_div (hppos y).ne' (hτ y).ne',
        Real.log_div (hrpos y).ne' (hτ y).ne']
    ring
  have hdiff : klDiv p τ - klDiv r τ
      = ∑ y, ((p y * Real.log (p y) - r y * Real.log (r y))
          - (p y - r y) * Real.log (τ y)) := by
    unfold klDiv
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => hterm y
  rw [hdiff]
  calc |∑ y, ((p y * Real.log (p y) - r y * Real.log (r y))
          - (p y - r y) * Real.log (τ y))|
      ≤ ∑ y, |(p y * Real.log (p y) - r y * Real.log (r y))
          - (p y - r y) * Real.log (τ y)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y, (1 + |Real.log c| + B) * |p y - r y| := by
        refine Finset.sum_le_sum fun y _ => ?_
        calc |(p y * Real.log (p y) - r y * Real.log (r y))
              - (p y - r y) * Real.log (τ y)|
            ≤ |p y * Real.log (p y) - r y * Real.log (r y)|
              + |(p y - r y) * Real.log (τ y)| := abs_sub _ _
          _ ≤ (1 + |Real.log c|) * |p y - r y| + |p y - r y| * B := by
              refine add_le_add (xlogx_diff_le hc (hp y) (hr y)) ?_
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_left (hτB y) (abs_nonneg _)
          _ = (1 + |Real.log c| + B) * |p y - r y| := by ring
    _ = (1 + |Real.log c| + B) * ∑ y, |p y - r y| := by
        rw [Finset.mul_sum]

/-! ## §4. Trajectory ℓ¹ control from the operator norm -/

/-- Row absolute sums are dominated by the L∞ operator norm. -/
lemma row_abs_sum_le_norm (D : Matrix Y X ℝ) (y : Y) :
    ∑ x, |D y x| ≤ ‖D‖ := by
  rw [Matrix.linfty_opNorm_def]
  have hle : (∑ x, ‖D y x‖₊ : ℝ≥0)
      ≤ Finset.univ.sup (fun i => ∑ x, ‖D i x‖₊) :=
    Finset.le_sup (f := fun i => ∑ x, ‖D i x‖₊) (Finset.mem_univ y)
  have hcoe : ((∑ x, ‖D y x‖₊ : ℝ≥0) : ℝ) = ∑ x, |D y x| := by
    push_cast
    exact Finset.sum_congr rfl fun x _ => Real.norm_eq_abs _
  rw [← hcoe]
  exact_mod_cast hle

/-- ℓ¹ contraction of row-measures through a matrix, priced by the L∞
operator norm and the measure's mass. -/
lemma vecMul_abs_sum_le (ν : Y → ℝ) (D : Matrix Y X ℝ) :
    ∑ x, |Matrix.vecMul ν D x| ≤ (∑ y, |ν y|) * ‖D‖ := by
  have hpt : ∀ x, |Matrix.vecMul ν D x| ≤ ∑ y, |ν y| * |D y x| := by
    intro x
    have : Matrix.vecMul ν D x = ∑ y, ν y * D y x := rfl
    rw [this]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    exact le_of_eq (Finset.sum_congr rfl fun y _ => abs_mul _ _)
  calc ∑ x, |Matrix.vecMul ν D x|
      ≤ ∑ x, ∑ y, |ν y| * |D y x| := Finset.sum_le_sum fun x _ => hpt x
    _ = ∑ y, |ν y| * ∑ x, |D y x| := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun y _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ y, |ν y| * ‖D‖ :=
        Finset.sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_left (row_abs_sum_le_norm D y) (abs_nonneg _)
    _ = (∑ y, |ν y|) * ‖D‖ := by rw [← Finset.sum_mul]

/-- The readout pushforward contracts ℓ¹ distances (fibers partition the
domain). -/
lemma push_abs_sum_le (pi_map : X → Y) (u : X → ℝ) :
    ∑ y, |push pi_map u y| ≤ ∑ x, |u x| := by
  have hfib : ∑ y, ∑ x ∈ Finset.univ.filter (fun x => pi_map x = y), |u x|
      = ∑ x, |u x| :=
    Finset.sum_fiberwise_of_maps_to (fun x _ => Finset.mem_univ _) _
  calc ∑ y, |push pi_map u y|
      ≤ ∑ y, ∑ x ∈ Finset.univ.filter (fun x => pi_map x = y), |u x| :=
        Finset.sum_le_sum fun y _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, |u x| := hfib

/-! ## §5. T4: the ε-H-theorem -/

/-- **T4: THE ε-H-THEOREM** (defect-priced second law). Let `o k` be the
true observed marginal at step `k` (readout of the fine evolution from a
compatibly-initialized state) and let the macro model `m k = μY·P̄ᵏ` be
its intended law. Under: kernels everywhere; compatibility; a stationary,
strictly positive, log-`B`-bounded reference `τ̄`; and mass floors
`c ≤ o, m ≤ 1` at steps `n` and `n+1` — the observed coarse relative
entropy can violate monotonicity by at most

  `(1 + |log c| + B) · (2n+1) · ‖𝒟‖`.

At `𝒟 = 0` the exact H-theorem is recovered. The constant is the honest
product of the review's three ingredients: horizon growth (`n·‖𝒟‖` and
`(n+1)·‖𝒟‖` trajectory errors), the entropy continuity modulus
(`1 + |log c|`), and the reference's support behavior (`B`). -/
theorem epsilon_H_theorem
    (P : Matrix X X ℝ) (Pbar : Matrix Y Y ℝ) (Lam : Matrix Y X ℝ)
    (pi_map : X → Y) (μY τbar : Y → ℝ) {c B : ℝ} (n : ℕ)
    (hP : IsKernel P) (hPbar : IsKernel Pbar)
    (hcomp : Compatible pi_map Lam)
    (hμ0 : ∀ y, 0 ≤ μY y) (hμ1 : ∑ y, μY y = 1)
    (hstat : Matrix.vecMul τbar Pbar = τbar) (hτpos : ∀ y, 0 < τbar y)
    (hτB : ∀ y, |Real.log (τbar y)| ≤ B) (hB : 0 ≤ B) (hc : 0 < c)
    (h_o_n : ∀ y, push pi_map
        (Matrix.vecMul (Matrix.vecMul μY Lam) (P ^ n)) y ∈ Set.Icc c 1)
    (h_o_n1 : ∀ y, push pi_map
        (Matrix.vecMul (Matrix.vecMul μY Lam) (P ^ (n+1))) y ∈ Set.Icc c 1)
    (h_m_n : ∀ y, Matrix.vecMul μY (Pbar ^ n) y ∈ Set.Icc c 1)
    (h_m_n1 : ∀ y, Matrix.vecMul μY (Pbar ^ (n+1)) y ∈ Set.Icc c 1) :
    klDiv (push pi_map
        (Matrix.vecMul (Matrix.vecMul μY Lam) (P ^ (n+1)))) τbar
      - klDiv (push pi_map
          (Matrix.vecMul (Matrix.vecMul μY Lam) (P ^ n))) τbar
      ≤ (1 + |Real.log c| + B)
          * ((2 * n + 1) * ‖obsDefect P Pbar Lam‖) := by
  set K := 1 + |Real.log c| + B with hK
  set ε := ‖obsDefect P Pbar Lam‖ with hε
  have hεnn : 0 ≤ ε := norm_nonneg _
  have hKnn : 0 ≤ K := by
    have h1 := abs_nonneg (Real.log c)
    rw [hK]
    linarith
  -- ℓ¹ trajectory control at any step k.
  have hl1 : ∀ k : ℕ,
      (∑ y, |push pi_map (Matrix.vecMul (Matrix.vecMul μY Lam) (P ^ k)) y
        - Matrix.vecMul μY (Pbar ^ k) y|) ≤ (k : ℝ) * ε := by
    intro k
    -- rewrite the model marginal as the pushforward of the lifted model
    have hm : Matrix.vecMul μY (Pbar ^ k)
        = push pi_map (Matrix.vecMul (Matrix.vecMul μY (Pbar ^ k)) Lam) :=
      (push_vecMul_lift pi_map Lam hcomp (Matrix.vecMul μY (Pbar ^ k))).symm
    -- pointwise difference is the pushforward of a vecMul by the
    -- horizon-defect matrix
    have hpt : ∀ y,
        push pi_map (Matrix.vecMul (Matrix.vecMul μY Lam) (P ^ k)) y
          - Matrix.vecMul μY (Pbar ^ k) y
        = push pi_map
            (Matrix.vecMul μY (Lam * P ^ k - Pbar ^ k * Lam)) y := by
      intro y
      rw [hm]
      unfold push
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul]
      show Matrix.vecMul μY (Lam * P ^ k) x
          - Matrix.vecMul μY (Pbar ^ k * Lam) x
        = Matrix.vecMul μY (Lam * P ^ k - Pbar ^ k * Lam) x
      simp only [Matrix.vecMul, dotProduct, Matrix.sub_apply,
        mul_sub, Finset.sum_sub_distrib]
    calc ∑ y, |push pi_map (Matrix.vecMul (Matrix.vecMul μY Lam) (P ^ k)) y
          - Matrix.vecMul μY (Pbar ^ k) y|
        = ∑ y, |push pi_map
            (Matrix.vecMul μY (Lam * P ^ k - Pbar ^ k * Lam)) y| := by
          exact Finset.sum_congr rfl fun y _ => by rw [hpt y]
      _ ≤ ∑ x, |Matrix.vecMul μY (Lam * P ^ k - Pbar ^ k * Lam) x| :=
          push_abs_sum_le pi_map _
      _ ≤ (∑ y, |μY y|) * ‖Lam * P ^ k - Pbar ^ k * Lam‖ :=
          vecMul_abs_sum_le μY _
      _ = ‖Lam * P ^ k - Pbar ^ k * Lam‖ := by
          have : ∑ y, |μY y| = 1 := by
            rw [← hμ1]
            exact Finset.sum_congr rfl fun y _ => abs_of_nonneg (hμ0 y)
          rw [this, one_mul]
      _ ≤ (k : ℝ) * ε := observation_error_le P Pbar Lam hP hPbar k
  -- continuity transfers at steps n and n+1
  have hcont_n := klDiv_continuity (τ := τbar) hc hτpos hτB h_o_n h_m_n
  have hcont_n1 := klDiv_continuity (τ := τbar) hc hτpos hτB h_o_n1 h_m_n1
  -- macro H-step between model marginals
  have hmacro : klDiv (Matrix.vecMul μY (Pbar ^ (n+1))) τbar
      ≤ klDiv (Matrix.vecMul μY (Pbar ^ n)) τbar := by
    have hrw : Matrix.vecMul μY (Pbar ^ (n+1))
        = Matrix.vecMul (Matrix.vecMul μY (Pbar ^ n)) Pbar := by
      rw [Matrix.vecMul_vecMul, ← pow_succ]
    rw [hrw]
    exact macro_H_step hPbar hstat hτpos
      (fun y => pushforward_nonneg (hPbar.pow n) hμ0 y)
  -- assemble
  have h1 : klDiv (push pi_map
      (Matrix.vecMul (Matrix.vecMul μY Lam) (P ^ (n+1)))) τbar
      ≤ klDiv (Matrix.vecMul μY (Pbar ^ (n+1))) τbar
        + K * ((n + 1 : ℕ) * ε) := by
    have habs := (abs_le.mp hcont_n1).2
    have := hl1 (n + 1)
    nlinarith [mul_le_mul_of_nonneg_left (hl1 (n+1)) hKnn]
  have h2 : klDiv (Matrix.vecMul μY (Pbar ^ n)) τbar
      ≤ klDiv (push pi_map
          (Matrix.vecMul (Matrix.vecMul μY Lam) (P ^ n))) τbar
        + K * ((n : ℕ) * ε) := by
    have habs := (abs_le.mp hcont_n).1
    nlinarith [mul_le_mul_of_nonneg_left (hl1 n) hKnn]
  have hfinal := (h1.trans (add_le_add_right hmacro _)).trans
    (add_le_add_right h2 _)
  calc klDiv (push pi_map
        (Matrix.vecMul (Matrix.vecMul μY Lam) (P ^ (n+1)))) τbar
      - klDiv (push pi_map
          (Matrix.vecMul (Matrix.vecMul μY Lam) (P ^ n))) τbar
      ≤ K * ((n : ℕ) * ε) + K * ((n + 1 : ℕ) * ε) := by
        push_cast at hfinal ⊢
        linarith
    _ = K * ((2 * n + 1) * ε) := by push_cast; ring

end SGC.Observation
