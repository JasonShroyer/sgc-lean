/-
Copyright (c) 2026 Jason Shroyer. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.MeanInequalities
import SGC.InformationGeometry.TsallisStatistics

/-!
# Constructive Tsallis DPI: the nonlinear informational arrow

Retires the (freshly repaired) `TsallisDPI` axiom as a kernel theorem, by
the geometric-mean route. Pre-flight discipline applied throughout
(`docs/axiom-preflight.md`):

* **Range**: everything is proven for exponent `α = 2 − q ∈ (0,1)`, i.e.
  exactly `q ∈ (1,2)` (`NonExtensiveSystem`) — the convexity domain. No
  claim outside it; the module's `q ≈ 2.5` grokking regime stays outside,
  correctly.
* **Convention**: column-stochastic kernels only (`∑_v T v w = 1`) — the
  mass-conserving convention (the transposed version was numerically
  falsified on 2026-08-26; counterexample preserved in the ledger).
* **No hidden `q = 1` additivity** (the audit of 2026-08-26): addition
  appears only as (i) measure pushforward (Kolmogorov additivity of
  classical measures — Tsallis non-extensivity concerns entropy of
  INDEPENDENT SUBSYSTEMS, never formed here), (ii) the defining sum of the
  divergence (definitional for the module's own `TsallisDivergence`), and
  (iii) convex/AM–GM combination with reverse-kernel probability weights.
  The only q-dependent ingredient is the two-point weighted AM–GM
  `p^α r^{1−α} ≤ αp + (1−α)r` applied per edge — the q-deformed heart
  itself.

## Structure

1. `geomMean_kernel_superadditive` — for `α ∈ (0,1)` and a nonnegative
   column-stochastic kernel: `∑_w T v w · p_w^α r_w^{1−α}` per output state
   is dominated by `(Tp)_v^α (Tr)_v^{1−α}`, hence globally
   `∑ p^α r^{1−α} ≤ ∑ (Tp)^α (Tr)^{1−α}`.
2. **`TsallisDPI`** (theorem, formerly axiom): monotonicity of the module's
   Tsallis divergence under mass-conserving stochastic maps for
   `q ∈ (1,2)`, with NO normalization assumptions on `p, ref` (the proof
   is positively homogeneous — strictly more general than the classical
   normalized statement).
-/

noncomputable section

namespace SGC.InformationGeometry.Tsallis

open Finset Real

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Two-point step: for `α ∈ (0,1)`, `A, B > 0` and `x, y ≥ 0`,
`x^α y^{1−α} ≤ A^α B^{1−α} · (α·x/A + (1−α)·y/B)`. Weighted AM–GM after
normalizing by the aggregates. -/
lemma geomMean_pointwise_bound {α A B x y : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hA : 0 < A) (hB : 0 < B)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ α * y ^ (1 - α)
      ≤ A ^ α * B ^ (1 - α) * (α * (x / A) + (1 - α) * (y / B)) := by
  have hxA : (0:ℝ) ≤ x / A := div_nonneg hx hA.le
  have hyB : (0:ℝ) ≤ y / B := div_nonneg hy hB.le
  have hamgm : (x / A) ^ α * (y / B) ^ (1 - α)
      ≤ α * (x / A) + (1 - α) * (y / B) :=
    Real.geom_mean_le_arith_mean2_weighted hα0.le (by linarith) hxA hyB
      (by ring)
  have hxdiv : (x / A) ^ α = x ^ α / A ^ α := Real.div_rpow hx hA.le α
  have hydiv : (y / B) ^ (1 - α) = y ^ (1 - α) / B ^ (1 - α) :=
    Real.div_rpow hy hB.le (1 - α)
  have hApos : (0:ℝ) < A ^ α := Real.rpow_pos_of_pos hA α
  have hBpos : (0:ℝ) < B ^ (1 - α) := Real.rpow_pos_of_pos hB (1 - α)
  have hmul := mul_le_mul_of_nonneg_left hamgm
    (mul_pos hApos hBpos).le
  calc x ^ α * y ^ (1 - α)
      = A ^ α * B ^ (1 - α) * ((x / A) ^ α * (y / B) ^ (1 - α)) := by
        rw [hxdiv, hydiv]
        field_simp
    _ ≤ A ^ α * B ^ (1 - α) * (α * (x / A) + (1 - α) * (y / B)) := hmul

/-- **Kernel superadditivity of the weighted geometric mean**: pushing a
pair of positive vectors through a nonnegative column-stochastic kernel can
only increase the total geometric-mean mass `∑ p^α r^{1−α}` (`α ∈ (0,1)`).
The engine of the Tsallis data-processing inequality. -/
theorem geomMean_kernel_superadditive {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (p r : V → ℝ) (hp : ∀ v, 0 < p v) (hr : ∀ v, 0 < r v)
    (T : Matrix V V ℝ)
    (hT : ∀ w, (∀ v, 0 ≤ T v w) ∧ ∑ v, T v w = 1) :
    (∑ w : V, (p w) ^ α * (r w) ^ (1 - α))
      ≤ ∑ v : V, (∑ w, T v w * p w) ^ α * (∑ w, T v w * r w) ^ (1 - α) := by
  have hTnn : ∀ v w, 0 ≤ T v w := fun v w => (hT w).1 v
  -- Per output state v: bound Σ_w T v w · p_w^α r_w^{1−α} by the aggregate.
  have hper : ∀ v : V,
      (∑ w : V, T v w * ((p w) ^ α * (r w) ^ (1 - α)))
        ≤ (∑ w, T v w * p w) ^ α * (∑ w, T v w * r w) ^ (1 - α) := by
    intro v
    set A := ∑ w, T v w * p w with hAdef
    set B := ∑ w, T v w * r w with hBdef
    have hAnn : 0 ≤ A := Finset.sum_nonneg fun w _ =>
      mul_nonneg (hTnn v w) (hp w).le
    have hBnn : 0 ≤ B := Finset.sum_nonneg fun w _ =>
      mul_nonneg (hTnn v w) (hr w).le
    rcases eq_or_lt_of_le hBnn with hB0 | hBpos
    · -- Zero row: every T v w = 0 (since r > 0), so both sides vanish.
      have hrow0 : ∀ w, T v w = 0 := by
        intro w
        by_contra hne
        have hTpos : 0 < T v w := lt_of_le_of_ne (hTnn v w) (Ne.symm hne)
        have : 0 < B := by
          rw [hBdef]
          exact Finset.sum_pos' (fun x _ => mul_nonneg (hTnn v x) (hr x).le)
            ⟨w, Finset.mem_univ w, mul_pos hTpos (hr w)⟩
        linarith [hB0]
      have hA0 : A = 0 := by
        rw [hAdef]
        exact Finset.sum_eq_zero fun w _ => by rw [hrow0 w, zero_mul]
      have hL0 : (∑ w : V, T v w * ((p w) ^ α * (r w) ^ (1 - α))) = 0 :=
        Finset.sum_eq_zero fun w _ => by rw [hrow0 w, zero_mul]
      rw [hL0, hA0, ← hB0]
      have h0α : (0:ℝ) ^ α = 0 := Real.zero_rpow hα0.ne'
      rw [h0α, zero_mul]
    · -- Positive row: A > 0 too (p > 0 wherever T v w > 0 contributes).
      have hApos : 0 < A := by
        rcases Finset.exists_lt_of_sum_lt (f := fun _ => (0:ℝ))
          (g := fun w => T v w * r w) (by simpa [hBdef] using hBpos)
          with ⟨w, _, hw⟩
        have hTpos : 0 < T v w := by
          by_contra hne
          push_neg at hne
          have : T v w = 0 := le_antisymm hne (hTnn v w)
          rw [this, zero_mul] at hw
          exact lt_irrefl 0 hw
        rw [hAdef]
        exact Finset.sum_pos' (fun x _ => mul_nonneg (hTnn v x) (hp x).le)
          ⟨w, Finset.mem_univ w, mul_pos hTpos (hp w)⟩
      -- Pointwise AM–GM, then sum.
      have hbound : ∀ w : V, T v w * ((p w) ^ α * (r w) ^ (1 - α))
          ≤ A ^ α * B ^ (1 - α)
            * (α * (T v w * p w / A) + (1 - α) * (T v w * r w / B)) := by
        intro w
        have h := geomMean_pointwise_bound hα0 hα1 hApos hBpos
          (hp w).le (hr w).le
        calc T v w * ((p w) ^ α * (r w) ^ (1 - α))
            ≤ T v w * (A ^ α * B ^ (1 - α)
                * (α * (p w / A) + (1 - α) * (r w / B))) :=
              mul_le_mul_of_nonneg_left h (hTnn v w)
          _ = A ^ α * B ^ (1 - α)
                * (α * (T v w * p w / A) + (1 - α) * (T v w * r w / B)) := by
              ring
      calc (∑ w : V, T v w * ((p w) ^ α * (r w) ^ (1 - α)))
          ≤ ∑ w : V, A ^ α * B ^ (1 - α)
              * (α * (T v w * p w / A) + (1 - α) * (T v w * r w / B)) :=
            Finset.sum_le_sum fun w _ => hbound w
        _ = A ^ α * B ^ (1 - α)
              * ((α / A) * A + ((1 - α) / B) * B) := by
            rw [← Finset.mul_sum]
            congr 1
            have hrw : ∀ w : V,
                α * (T v w * p w / A) + (1 - α) * (T v w * r w / B)
                  = (α / A) * (T v w * p w) + ((1 - α) / B) * (T v w * r w) := by
              intro w
              ring
            rw [Finset.sum_congr rfl fun w _ => hrw w]
            rw [Finset.sum_add_distrib]
            rw [← Finset.mul_sum, ← Finset.mul_sum]
        _ = A ^ α * B ^ (1 - α) := by
            rw [div_mul_cancel₀ _ hApos.ne', div_mul_cancel₀ _ hBpos.ne']
            ring
  -- Sum over v and reindex via column-stochasticity.
  calc (∑ w : V, (p w) ^ α * (r w) ^ (1 - α))
      = ∑ w : V, (∑ v : V, T v w) * ((p w) ^ α * (r w) ^ (1 - α)) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [(hT w).2, one_mul]
    _ = ∑ v : V, ∑ w : V, T v w * ((p w) ^ α * (r w) ^ (1 - α)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun w _ => by rw [Finset.sum_mul]
    _ ≤ ∑ v : V, (∑ w, T v w * p w) ^ α * (∑ w, T v w * r w) ^ (1 - α) :=
        Finset.sum_le_sum fun v _ => hper v

/-- **The Tsallis Data-Processing Inequality — THEOREM** (axiom retired
2026-08-26). For `q ∈ (1,2)` and any mass-conserving stochastic map, the
Tsallis divergence contracts. Positively homogeneous proof: no
normalization of `p, ref` needed. The nonlinear informational arrow. -/
theorem TsallisDPI_proved {q : ℝ} [NonExtensiveSystem q]
    (p ref : V → ℝ) (hp : ∀ v, 0 < p v) (href : ∀ v, 0 < ref v)
    (T : Matrix V V ℝ)
    (hT_stoch : ∀ w, (∀ v, 0 ≤ T v w) ∧ ∑ v, T v w = 1) :
    TsallisDivergence q (fun v => ∑ w, T v w * p w) (fun v => ∑ w, T v w * ref w) ≤
    TsallisDivergence q p ref := by
  have hq1 : 1 < q := NonExtensiveSystem.one_lt_q
  have hq2 : q < 2 := NonExtensiveSystem.q_lt_two
  have hα0 : (0:ℝ) < 2 - q := by linarith
  have hα1 : 2 - q < 1 := by linarith
  have hkey := geomMean_kernel_superadditive hα0 hα1 p ref hp href T hT_stoch
  unfold TsallisDivergence
  have hexp : ∀ (a b : V → ℝ),
      (∑ v : V, (a v) ^ (2 - q) * (b v) ^ (q - 1))
        = ∑ v : V, (a v) ^ (2 - q) * (b v) ^ (1 - (2 - q)) := by
    intro a b
    refine Finset.sum_congr rfl fun v _ => ?_
    congr 1
    ring_nf
  have h1 : (∑ v : V, (p v) ^ (2 - q) * (ref v) ^ (q - 1))
      ≤ ∑ v : V, ((∑ w, T v w * p w) ^ (2 - q)
          * (∑ w, T v w * ref w) ^ (q - 1)) := by
    rw [hexp p ref, hexp (fun v => ∑ w, T v w * p w)
      (fun v => ∑ w, T v w * ref w)]
    exact hkey
  have hq1' : (0:ℝ) < q - 1 := by linarith
  gcongr <;> linarith

end SGC.InformationGeometry.Tsallis
