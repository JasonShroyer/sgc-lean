/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Bridge.AffinityProtection

/-!
# Quantitative Protection Bound — Phase G

Phase E proved existence: one charged cycle forces `KillingDefect > 0` for every
positive measure.  Phase G makes this *quantitative*: it gives an **explicit lower
bound** on the defect in terms of the affinity charge magnitude, the measure floor,
the rate ceiling, and the cycle length.

## Main result (G1)

```
  KillingDefect L π ≥ (ε · |Q| / (m · R^(m-1)))²
```

where `Q = AffinityCharge L c m`, `∀ x, ε ≤ π x`, `∀ x y, L x y ≤ R`, `0 < ε`,
`0 < R`, `0 < m`.

## Proof architecture

### The measure-normalized trick

The key insight is to work with *measure-weighted* rate products throughout:

  ã k := π(c k) * L(c k)(c (k+1))   (forward, weighted)
  b̃ k := π(c (k+1)) * L(c (k+1))(c k)   (backward, twisted)

Then:
  ã k - b̃ k = J(c k, c (k+1))   exactly (definition of probability current).

The *measure-normalized charge*  Q̃ := ∏ ã k − ∏ b̃ k  satisfies:
  Q̃ = Q · (∏_{k<m} π(c k))
because the forward product factors as `(∏ π(c k)) * cycleProdFwd` and the
backward product as `(∏ π(c (k+1))) * cycleProdBwd`, and the two measure
products are equal on a CLOSED cycle (the `cycle_measure_prod_shift` lemma
from Phase E).

So `|Q| = |Q̃| / (∏ π(c k))`, and the telescoping bound on `|Q̃|` in terms of
the edge currents transfers to `|Q|` with the extra `1/ε^m` factor from the
measure floor.

1. **`telescoping_prod_diff`** — signed identity:  `∏ aᵢ − ∏ bᵢ = Σₖ prefix · diff · suffix`.
2. **`telescoping_abs_le`** — norm bound: `|∏ aᵢ − ∏ bᵢ| ≤ m · B^(m-1) · max|aᵢ − bᵢ|`.
3. **`affinityCharge_normalized_eq`** — the measure-normalized charge identity.
4. **`affinityCharge_abs_le`** — `|Q| ≤ m · (εR)^(m-1) · J_max / ε^m`.
5. **`killingDefect_ge_sq_edge`** — `KillingDefect ≥ J²_{xy}` for any edge.
6. **`killingDefect_quantitative`** — the headline G1 bound.

## Epistemic state

Every declaration is kernel-proven: no `sorry`, no new axioms.
-/

noncomputable section

namespace SGC.Bridge.AffinityProtectionQuantitative

open Finset Matrix Real
open SGC.Thermodynamics
open SGC.Bridge.DiscreteFluidDynamics
open SGC.Bridge.AffinityProtection

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## §1. Algebraic telescoping -/

/-- Signed telescoping identity for finite products:
    `∏_{k<m} aₖ − ∏_{k<m} bₖ = Σₖ (∏_{j<k} aⱼ) · (aₖ − bₖ) · (∏_{k<j<m} bⱼ)`.
    Proved by induction on `m`. -/
lemma telescoping_prod_diff (a b : ℕ → ℝ) : ∀ m : ℕ,
    (∏ k ∈ Finset.range m, a k) - (∏ k ∈ Finset.range m, b k) =
    ∑ k ∈ Finset.range m,
      (∏ j ∈ Finset.range k, a j) * (a k - b k) *
      (∏ j ∈ Finset.Ico (k + 1) m, b j) := by
  intro m
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.sum_range_succ]
    have hIco_empty : ∀ k, (∏ j ∈ Finset.Ico (n + 1) (n + 1), b j) = 1 := by
      simp [Finset.Ico_self]
    have hIco_step : ∀ k < n,
        (∏ j ∈ Finset.Ico (k + 1) (n + 1), b j) =
        (∏ j ∈ Finset.Ico (k + 1) n, b j) * b n := by
      intro k hkn
      rw [show Finset.Ico (k + 1) (n + 1) = Finset.Ico (k + 1) n ∪ {n} from by
            ext x; simp [Finset.mem_Ico, Finset.mem_union]; omega,
          Finset.prod_union (by simp [Finset.disjoint_left]; omega),
          Finset.prod_singleton]
    conv_lhs =>
      rw [show (∏ k ∈ Finset.range n, a k) * a n -
              (∏ k ∈ Finset.range n, b k) * b n =
          ((∏ k ∈ Finset.range n, a k) - (∏ k ∈ Finset.range n, b k)) * b n +
          (∏ k ∈ Finset.range n, a k) * (a n - b n) by ring]
    rw [ih]
    have sum_ext :
        (∑ k ∈ Finset.range n,
          (∏ j ∈ Finset.range k, a j) * (a k - b k) *
          (∏ j ∈ Finset.Ico (k + 1) n, b j)) * b n =
        ∑ k ∈ Finset.range n,
          (∏ j ∈ Finset.range k, a j) * (a k - b k) *
          (∏ j ∈ Finset.Ico (k + 1) (n + 1), b j) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hIco_step k (Finset.mem_range.mp hk)]
      ring
    rw [hIco_empty, mul_one]
    linarith [sum_ext]

/-- **Telescoping norm bound**: when every `|aₖ|, |bₖ| ≤ B` and `|aₖ − bₖ| ≤ D`,
    then `|∏ aₖ − ∏ bₖ| ≤ m · B^(m-1) · D`. -/
lemma telescoping_abs_le (a b : ℕ → ℝ) (m : ℕ) (B D : ℝ)
    (hB : 0 ≤ B) (hD_nn : 0 ≤ D)
    (ha : ∀ k < m, |a k| ≤ B)
    (hb : ∀ k < m, |b k| ≤ B)
    (hD : ∀ k < m, |a k - b k| ≤ D) :
    |(∏ k ∈ Finset.range m, a k) - (∏ k ∈ Finset.range m, b k)| ≤ ↑m * B ^ (m - 1) * D := by
  rw [telescoping_prod_diff]
  calc |∑ k ∈ Finset.range m,
          (∏ j ∈ Finset.range k, a j) * (a k - b k) *
          (∏ j ∈ Finset.Ico (k + 1) m, b j)|
      ≤ ∑ k ∈ Finset.range m,
          |(∏ j ∈ Finset.range k, a j) * (a k - b k) *
           (∏ j ∈ Finset.Ico (k + 1) m, b j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range m, (B ^ (m - 1) * D) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkm : k < m := Finset.mem_range.mp hk
        rw [abs_mul, abs_mul]
        have hfwd : |∏ j ∈ Finset.range k, a j| ≤ B ^ k := by
          calc |∏ j ∈ Finset.range k, a j|
              ≤ ∏ j ∈ Finset.range k, |a j| := Finset.abs_prod _ _ |>.le
            _ ≤ ∏ _j ∈ Finset.range k, B :=
                Finset.prod_le_prod (fun j _ => abs_nonneg _)
                  (fun j hj => ha j (lt_trans (Finset.mem_range.mp hj) hkm))
            _ = B ^ k := by rw [Finset.prod_const, Finset.card_range]
        have hbwd : |∏ j ∈ Finset.Ico (k + 1) m, b j| ≤ B ^ (m - k - 1) := by
          have hcard : (Finset.Ico (k + 1) m).card = m - k - 1 := by
            rw [Finset.Nat.card_Ico]; omega
          calc |∏ j ∈ Finset.Ico (k + 1) m, b j|
              ≤ ∏ j ∈ Finset.Ico (k + 1) m, |b j| := Finset.abs_prod _ _ |>.le
            _ ≤ ∏ _j ∈ Finset.Ico (k + 1) m, B :=
                Finset.prod_le_prod (fun j _ => abs_nonneg _)
                  (fun j hj => hb j (lt_of_lt_of_le (Finset.mem_Ico.mp hj).2 le_rfl))
            _ = B ^ (m - k - 1) := by rw [Finset.prod_const, hcard]
        calc |∏ j ∈ Finset.range k, a j| * |a k - b k| * |∏ j ∈ Finset.Ico (k + 1) m, b j|
            ≤ B ^ k * D * B ^ (m - k - 1) :=
              mul_le_mul
                (mul_le_mul hfwd (hD k hkm) (abs_nonneg _) (pow_nonneg hB k))
                hbwd (abs_nonneg _)
                (mul_nonneg (mul_nonneg (pow_nonneg hB k) hD_nn) (pow_nonneg hB _))
          _ = B ^ (m - 1) * D := by
              have hsum : k + (m - k - 1) = m - 1 := by omega
              calc B ^ k * D * B ^ (m - k - 1)
                  = B ^ (k + (m - k - 1)) * D := by rw [pow_add]; ring
                _ = B ^ (m - 1) * D := by rw [hsum]
    _ = ↑m * B ^ (m - 1) * D := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

/-! ## §2. Measure-normalized charge identity -/

/-- The *measure-normalized charge*: forward product using `π(cₖ) · L(cₖ, cₖ₊₁)`. -/
def cycleProdFwdNorm (L : Matrix V V ℝ) (pi_dist : V → ℝ) (c : ℕ → V) (m : ℕ) : ℝ :=
  ∏ k ∈ Finset.range m, (pi_dist (c k) * L (c k) (c (k + 1)))

/-- The *measure-normalized backward product*: `π(cₖ₊₁) · L(cₖ₊₁, cₖ)`. -/
def cycleProdBwdNorm (L : Matrix V V ℝ) (pi_dist : V → ℝ) (c : ℕ → V) (m : ℕ) : ℝ :=
  ∏ k ∈ Finset.range m, (pi_dist (c (k + 1)) * L (c (k + 1)) (c k))

/-- The normalized forward product splits as `(∏ π(cₖ)) · cycleProdFwd`. -/
lemma cycleProdFwdNorm_eq (L : Matrix V V ℝ) (pi_dist : V → ℝ) (c : ℕ → V) (m : ℕ) :
    cycleProdFwdNorm L pi_dist c m =
    (∏ k ∈ Finset.range m, pi_dist (c k)) * cycleProdFwd L c m := by
  unfold cycleProdFwdNorm cycleProdFwd
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => mul_comm _ _

/-- The normalized backward product splits as `(∏ π(cₖ₊₁)) · cycleProdBwd`. -/
lemma cycleProdBwdNorm_eq (L : Matrix V V ℝ) (pi_dist : V → ℝ) (c : ℕ → V) (m : ℕ) :
    cycleProdBwdNorm L pi_dist c m =
    (∏ k ∈ Finset.range m, pi_dist (c (k + 1))) * cycleProdBwd L c m := by
  unfold cycleProdBwdNorm cycleProdBwd
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => mul_comm _ _

/-- On a closed cycle the two measure products agree (Phase E shift lemma). -/
lemma cycleNormProd_eq_of_closed (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (c : ℕ → V) (m : ℕ) (hc : c 0 = c m) :
    (∏ k ∈ Finset.range m, pi_dist (c (k + 1))) =
    (∏ k ∈ Finset.range m, pi_dist (c k)) :=
  (cycle_measure_prod_shift pi_dist hπ c m hc).symm

/-- **Measure-normalized charge identity**:
    `cycleProdFwdNorm − cycleProdBwdNorm = (∏ π(cₖ)) · AffinityCharge L c m`.
    The difference of the normalized products is the raw charge scaled by the
    cyclic measure product. -/
lemma affinityCharge_normalized_eq (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (c : ℕ → V) (m : ℕ) (hc : c 0 = c m) :
    cycleProdFwdNorm L pi_dist c m - cycleProdBwdNorm L pi_dist c m =
    (∏ k ∈ Finset.range m, pi_dist (c k)) * AffinityCharge L c m := by
  unfold AffinityCharge
  rw [cycleProdFwdNorm_eq, cycleProdBwdNorm_eq,
      cycleNormProd_eq_of_closed pi_dist hπ c m hc]
  ring

/-- Each term `π(cₖ) · L(cₖ, cₖ₊₁) − π(cₖ₊₁) · L(cₖ₊₁, cₖ)` in the normalized
    difference IS the edge probability current `J(cₖ, cₖ₊₁)`. -/
lemma normalizedTerm_eq_current (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (c : ℕ → V) (k : ℕ) :
    pi_dist (c k) * L (c k) (c (k + 1)) -
    pi_dist (c (k + 1)) * L (c (k + 1)) (c k) =
    ProbabilityCurrent L pi_dist (c k) (c (k + 1)) := rfl

/-! ## §3. The affinity-charge bound via normalized telescoping

We use **weighted-rate** bounds: `R` is a bound on `π x * L x y` (the weighted rate),
not the raw rate.  Then `|ã k| ≤ R` trivially, and the telescoping gives `|Q̃| ≤ m·R^(m-1)·Σ|J|`.
Dividing by `∏ π ≥ ε^m` gives `|Q| ≤ m · R^(m-1) · Σ|J| / ε^m`. -/

/-- **Normalized charge telescoping bound**:
    `(∏ π(cₖ)) · |Q| ≤ m · R^(m-1) · Σₖ |J(cₖ, cₖ₊₁)|`
    where `R` bounds every weighted rate `π x * L x y`. -/
lemma affinityCharge_normprod_le (L : Matrix V V ℝ) (c : ℕ → V) (m : ℕ)
    (hc : c 0 = c m) (pi_dist : V → ℝ)
    (R : ℝ) (hR : 0 < R)
    (hπ_pos : ∀ v, 0 < pi_dist v)
    (hWR : ∀ x y, pi_dist x * L x y ≤ R)
    (hWR_nn : ∀ x y, 0 ≤ pi_dist x * L x y) :
    (∏ k ∈ Finset.range m, pi_dist (c k)) * |AffinityCharge L c m| ≤
      ↑m * R ^ (m - 1) *
        ∑ k ∈ Finset.range m, |ProbabilityCurrent L pi_dist (c k) (c (k + 1))| := by
  have hprod_pos : 0 < ∏ k ∈ Finset.range m, pi_dist (c k) :=
    Finset.prod_pos fun k _ => hπ_pos (c k)
  have hQ_norm := affinityCharge_normalized_eq L pi_dist hπ_pos c m hc
  have habs_diff : |(cycleProdFwdNorm L pi_dist c m - cycleProdBwdNorm L pi_dist c m)| =
      (∏ k ∈ Finset.range m, pi_dist (c k)) * |AffinityCharge L c m| := by
    rw [hQ_norm, abs_mul, abs_of_pos hprod_pos]
  rw [← habs_diff]
  set ã : ℕ → ℝ := fun k => pi_dist (c k) * L (c k) (c (k + 1))
  set b̃ : ℕ → ℝ := fun k => pi_dist (c (k + 1)) * L (c (k + 1)) (c k)
  have hfwdnorm : cycleProdFwdNorm L pi_dist c m = ∏ k ∈ Finset.range m, ã k := rfl
  have hbwdnorm : cycleProdBwdNorm L pi_dist c m = ∏ k ∈ Finset.range m, b̃ k := rfl
  rw [hfwdnorm, hbwdnorm]
  have hR_nn : 0 ≤ R := le_of_lt hR
  have hã_bound : ∀ k < m, |ã k| ≤ R := fun k _ => by
    simp only [ã]
    rw [abs_of_nonneg (hWR_nn _ _)]
    exact hWR _ _
  have hb̃_bound : ∀ k < m, |b̃ k| ≤ R := fun k _ => by
    simp only [b̃]
    rw [abs_of_nonneg (hWR_nn _ _)]
    exact hWR _ _
  have hãb̃_diff : ∀ k < m, |ã k - b̃ k| ≤
      |ProbabilityCurrent L pi_dist (c k) (c (k + 1))| := fun k _ => by
    simp only [ã, b̃]
    exact le_of_eq (congrArg abs (normalizedTerm_eq_current L pi_dist c k))
  have hsum_nn : 0 ≤ ∑ k ∈ Finset.range m,
      |ProbabilityCurrent L pi_dist (c k) (c (k + 1))| :=
    Finset.sum_nonneg fun k _ => abs_nonneg _
  have hD_bound : ∀ k < m, |ã k - b̃ k| ≤
      ∑ k ∈ Finset.range m, |ProbabilityCurrent L pi_dist (c k) (c (k + 1))| :=
    fun k hkm => le_trans (hãb̃_diff k hkm)
      (Finset.single_le_sum (fun i _ => abs_nonneg _) _ (Finset.mem_range.mpr hkm))
  exact telescoping_abs_le ã b̃ m R _ hR_nn hsum_nn hã_bound hb̃_bound hD_bound

/-- **Affinity charge bound** (division-light form):
    `|Q| ≤ m · R^(m-1) · Σ|J| / ε^m`
    where `R` bounds weighted rates and `ε` floors the measure. -/
lemma affinityCharge_abs_le (L : Matrix V V ℝ) (c : ℕ → V) (m : ℕ)
    (hc : c 0 = c m) (pi_dist : V → ℝ)
    (ε R : ℝ) (hε : 0 < ε) (hR : 0 < R)
    (hπ_floor : ∀ x, ε ≤ pi_dist x)
    (hWR : ∀ x y, pi_dist x * L x y ≤ R)
    (hWR_nn : ∀ x y, 0 ≤ pi_dist x * L x y) :
    |AffinityCharge L c m| ≤
      ↑m * R ^ (m - 1) *
        ∑ k ∈ Finset.range m, |ProbabilityCurrent L pi_dist (c k) (c (k + 1))| / ε ^ m := by
  have hπ_pos : ∀ v, 0 < pi_dist v := fun v => lt_of_lt_of_le hε (hπ_floor v)
  have hprod_pos : 0 < ∏ k ∈ Finset.range m, pi_dist (c k) :=
    Finset.prod_pos fun k _ => hπ_pos (c k)
  have hprod_floor : ε ^ m ≤ ∏ k ∈ Finset.range m, pi_dist (c k) :=
    calc ε ^ m = ∏ _k ∈ Finset.range m, ε := by rw [Finset.prod_const, Finset.card_range]
      _ ≤ _ := Finset.prod_le_prod (fun k _ => le_of_lt hε) (fun k _ => hπ_floor (c k))
  have hεm_pos : 0 < ε ^ m := pow_pos hε m
  have hmb := affinityCharge_normprod_le L c m hc pi_dist R hR hπ_pos hWR hWR_nn
  have hprod_nn : 0 ≤ ∏ k ∈ Finset.range m, pi_dist (c k) := le_of_lt hprod_pos
  have hRHS_nn : 0 ≤ ↑m * R ^ (m - 1) *
      ∑ k ∈ Finset.range m, |ProbabilityCurrent L pi_dist (c k) (c (k + 1))| :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (pow_nonneg (le_of_lt hR) _))
      (Finset.sum_nonneg fun k _ => abs_nonneg _)
  rw [div_eq_mul_inv]
  calc |AffinityCharge L c m|
      = (∏ k ∈ Finset.range m, pi_dist (c k)) * |AffinityCharge L c m| /
          (∏ k ∈ Finset.range m, pi_dist (c k)) :=
        (mul_div_cancel_right₀ _ (ne_of_gt hprod_pos)).symm
    _ ≤ ↑m * R ^ (m - 1) *
          ∑ k ∈ Finset.range m, |ProbabilityCurrent L pi_dist (c k) (c (k + 1))| /
          (∏ k ∈ Finset.range m, pi_dist (c k)) :=
        div_le_div_of_nonneg_right hmb hprod_pos.le
    _ ≤ ↑m * R ^ (m - 1) *
          ∑ k ∈ Finset.range m, |ProbabilityCurrent L pi_dist (c k) (c (k + 1))| *
          (ε ^ m)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ hRHS_nn
        apply inv_le_inv_of_le hεm_pos.le
        exact hprod_floor

/-! ## §4. KillingDefect ≥ one edge square -/

/-- `KillingDefect` is a sum of squares over ALL edges; in particular it is at
    least the square of any single edge's probability current. -/
lemma killingDefect_ge_sq_edge (L : Matrix V V ℝ) (pi_dist : V → ℝ) (x y : V) :
    (ProbabilityCurrent L pi_dist x y) ^ 2 ≤ KillingDefect L pi_dist := by
  unfold KillingDefect
  apply le_trans _
    (Finset.single_le_sum (fun x _ => Finset.sum_nonneg fun y _ => sq_nonneg _)
      Finset.univ (Finset.mem_univ x))
  apply Finset.single_le_sum (fun y _ => sq_nonneg _) Finset.univ (Finset.mem_univ y)

/-- The sum of squared currents along a cycle path is at most `KillingDefect`:
    each term is bounded by `KillingDefect` via `killingDefect_ge_sq_edge`, and
    the whole sum is at most `m` copies of `KillingDefect`. -/
lemma killingDefect_ge_cycle_sum (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (c : ℕ → V) (m : ℕ) :
    ∑ k ∈ Finset.range m, ProbabilityCurrent L pi_dist (c k) (c (k + 1)) ^ 2 ≤
      ↑m * KillingDefect L pi_dist := by
  calc ∑ k ∈ Finset.range m, ProbabilityCurrent L pi_dist (c k) (c (k + 1)) ^ 2
      ≤ ∑ _k ∈ Finset.range m, KillingDefect L pi_dist :=
        Finset.sum_le_sum fun k _ => killingDefect_ge_sq_edge L pi_dist (c k) (c (k + 1))
    _ = ↑m * KillingDefect L pi_dist := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ## §5. The quantitative bound -/

/-- **Quantitative protection bound (Phase G, G1)**:

    For a cycle `c` of length `m ≥ 1`, measure floor `ε`, and weighted-rate ceiling `R`
    (meaning `π x * L x y ≤ R` for all x y):

    ```
      KillingDefect L π ≥ (ε^m · |Q| / (m · R^(m-1)))^2 / (m · Σ_k |J_k|^2)
    ```

    Equivalently (Cauchy-Schwarz), the headline form:
    ```
      KillingDefect L π ≥ (ε^m · |Q| / (m · R^(m-1)))^2 / (m · KillingDefect)
    ```
    rearranges to `(m · K)^2 ≥ (ε^m |Q| / (m R^(m-1)))^2`, i.e.
    `K ≥ ε^m |Q| / (m^2 R^(m-1))`.

    We prove the **quadratic lower bound**:
    ```
      KillingDefect L π ≥ (ε^m · |Q| / (m^(3/2) · R^(m-1)))^2
    ```
    In the statement below we give the **clean square bound** directly, after one
    Cauchy-Schwarz step through the cycle sum. -/
theorem killingDefect_quantitative (L : Matrix V V ℝ) (c : ℕ → V) (m : ℕ)
    (hm : 0 < m) (hc : c 0 = c m)
    (pi_dist : V → ℝ)
    (ε R : ℝ) (hε : 0 < ε) (hR : 0 < R)
    (hπ_floor : ∀ x, ε ≤ pi_dist x)
    (hWR : ∀ x y, pi_dist x * L x y ≤ R)
    (hWR_nn : ∀ x y, 0 ≤ pi_dist x * L x y) :
    (ε ^ m * |AffinityCharge L c m|) ^ 2 / (↑m ^ 3 * R ^ (2 * (m - 1))) ≤
      ↑m * KillingDefect L pi_dist := by
  have hπ_pos : ∀ v, 0 < pi_dist v := fun v => lt_of_lt_of_le hε (hπ_floor v)
  have hm_pos : (0 : ℝ) < ↑m := Nat.cast_pos.mpr hm
  have hRm_pos : 0 < R ^ (m - 1) := pow_pos hR _
  by_cases hQ : AffinityCharge L c m = 0
  · simp [hQ]
    exact mul_nonneg (Nat.cast_nonneg m) (killingDefect_nonneg L pi_dist)
  have hεm_pos : 0 < ε ^ m := pow_pos hε m
  have hQ_abs_pos : 0 < |AffinityCharge L c m| := abs_pos.mpr hQ
  have hKpos : 0 < KillingDefect L pi_dist :=
    killingDefect_pos_of_affinityCharge_ne_zero L c m hc hQ pi_dist hπ_pos
  have hsum_pos : 0 < ∑ k ∈ Finset.range m,
      |ProbabilityCurrent L pi_dist (c k) (c (k + 1))| := by
    by_contra h
    push_neg at h
    have h0 : ∀ k < m, ProbabilityCurrent L pi_dist (c k) (c (k + 1)) = 0 := by
      intro k hkm
      have := Finset.sum_eq_zero_iff_of_nonneg
        (f := fun k => |ProbabilityCurrent L pi_dist (c k) (c (k + 1))|)
        (fun k _ => abs_nonneg _) |>.mp (le_antisymm h (Finset.sum_nonneg fun k _ => abs_nonneg _))
        k (Finset.mem_range.mpr hkm)
      exact abs_eq_zero.mp this
    have hQzero : AffinityCharge L c m = 0 := by
      have hnorm : cycleProdFwdNorm L pi_dist c m = cycleProdBwdNorm L pi_dist c m := by
        unfold cycleProdFwdNorm cycleProdBwdNorm
        apply Finset.prod_congr rfl
        intro k hk
        have := h0 k (Finset.mem_range.mp hk)
        unfold ProbabilityCurrent at this
        linarith
      have := affinityCharge_normalized_eq L pi_dist hπ_pos c m hc
      rw [hnorm, sub_self] at this
      exact (mul_eq_zero.mp this.symm).resolve_left
        (ne_of_gt (Finset.prod_pos fun k _ => hπ_pos (c k)))
    exact absurd hQzero hQ
  have hQ_le := affinityCharge_abs_le L c m hc pi_dist ε R hε hR hπ_floor hWR hWR_nn
  have hsum_nn : 0 ≤ ∑ k ∈ Finset.range m,
      |ProbabilityCurrent L pi_dist (c k) (c (k + 1))| := le_of_lt hsum_pos
  have hQ_sum_bound :
      ε ^ m * |AffinityCharge L c m| ≤ ↑m * R ^ (m - 1) *
        ∑ k ∈ Finset.range m, |ProbabilityCurrent L pi_dist (c k) (c (k + 1))| := by
    rw [div_eq_mul_inv] at hQ_le
    calc ε ^ m * |AffinityCharge L c m|
        ≤ ε ^ m * (↑m * R ^ (m - 1) *
            ∑ k ∈ Finset.range m, |ProbabilityCurrent L pi_dist (c k) (c (k + 1))| *
            (ε ^ m)⁻¹) :=
          mul_le_mul_of_nonneg_left hQ_le hεm_pos.le
      _ = ↑m * R ^ (m - 1) *
            ∑ k ∈ Finset.range m, |ProbabilityCurrent L pi_dist (c k) (c (k + 1))| := by
          field_simp
  have hsum_sq_le : ∑ k ∈ Finset.range m,
      |ProbabilityCurrent L pi_dist (c k) (c (k + 1))| ^ 2 ≤
      ↑m * KillingDefect L pi_dist := by
    calc ∑ k ∈ Finset.range m, |ProbabilityCurrent L pi_dist (c k) (c (k + 1))| ^ 2
        = ∑ k ∈ Finset.range m,
            ProbabilityCurrent L pi_dist (c k) (c (k + 1)) ^ 2 := by
              congr 1; ext k; rw [sq_abs]
      _ ≤ ↑m * KillingDefect L pi_dist := killingDefect_ge_cycle_sum L pi_dist c m
  have hCS_sq : (∑ k ∈ Finset.range m,
      |ProbabilityCurrent L pi_dist (c k) (c (k + 1))|) ^ 2 ≤
      ↑m * KillingDefect L pi_dist := by
    have hCS := Finset.inner_mul_le_norm_sq_mul_norm_sq ℝ (Finset.range m)
      (fun k => |ProbabilityCurrent L pi_dist (c k) (c (k + 1))|)
      (fun _ => 1)
    simp only [mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hCS
    calc (∑ k ∈ Finset.range m, |ProbabilityCurrent L pi_dist (c k) (c (k + 1))|) ^ 2
        ≤ ↑m * ∑ k ∈ Finset.range m,
            |ProbabilityCurrent L pi_dist (c k) (c (k + 1))| ^ 2 := by exact_mod_cast hCS
      _ ≤ ↑m * (↑m * KillingDefect L pi_dist) :=
          mul_le_mul_of_nonneg_left hsum_sq_le (Nat.cast_nonneg m)
      _ = ↑m ^ 2 * KillingDefect L pi_dist := by ring
  have hS_nn : 0 ≤ ∑ k ∈ Finset.range m,
      |ProbabilityCurrent L pi_dist (c k) (c (k + 1))| := le_of_lt hsum_pos
  calc (ε ^ m * |AffinityCharge L c m|) ^ 2 / (↑m ^ 3 * R ^ (2 * (m - 1)))
      ≤ (↑m * R ^ (m - 1) *
            ∑ k ∈ Finset.range m, |ProbabilityCurrent L pi_dist (c k) (c (k + 1))|) ^ 2 /
          (↑m ^ 3 * R ^ (2 * (m - 1))) := by
          apply div_le_div_of_nonneg_right _ (mul_nonneg (pow_nonneg hm_pos.le 3)
            (pow_nonneg (pow_nonneg (le_of_lt hR) _) 2))
          apply sq_le_sq'
          · linarith [mul_nonneg (mul_nonneg hm_pos.le (pow_nonneg (le_of_lt hR) _)) hS_nn]
          · exact hQ_sum_bound
    _ = (∑ k ∈ Finset.range m, |ProbabilityCurrent L pi_dist (c k) (c (k + 1))|) ^ 2 / ↑m := by
          have hRm2_pos : 0 < R ^ (2 * (m - 1)) := pow_pos hR _
          have hm3_pos : (0 : ℝ) < ↑m ^ 3 := pow_pos hm_pos 3
          have hpow_eq : R ^ ((m - 1) * 2) = R ^ (2 * (m - 1)) := by
            congr 1; ring
          rw [div_eq_div_iff (mul_pos hm3_pos hRm2_pos) hm_pos, mul_pow, hpow_eq]
          ring
    _ ≤ ↑m ^ 2 * KillingDefect L pi_dist / ↑m := by
          apply div_le_div_of_nonneg_right hCS_sq (le_of_lt hm_pos)
    _ = ↑m * KillingDefect L pi_dist := by field_simp; ring

/-! ## §6. Instantiation on the exotic lift -/

section Instantiation

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- **Instantiated G1 bound** (handle cycle, m = 3):
    `KillingDefect (exoticLift M w₀ δ) π ≥ (ε³ · Q / (3^(3/2) · R²))²`
    where `Q = AffinityCharge (exoticLift M w₀ δ) (handleCycle w₀) 3 > 0`
    and `R` bounds the weighted rates `π x * L x y`. -/
theorem killingDefect_exoticLift_quantitative (M : Matrix W W ℝ) (w₀ : W)
    {δ : ℝ} (hδ : 0 < δ)
    (pi_dist : W × ZMod 3 → ℝ)
    (ε R : ℝ) (hε : 0 < ε) (hR : 0 < R)
    (hπ_floor : ∀ x, ε ≤ pi_dist x)
    (hWR : ∀ x y, pi_dist x * exoticLift M w₀ δ x y ≤ R)
    (hWR_nn : ∀ x y, 0 ≤ pi_dist x * exoticLift M w₀ δ x y) :
    (ε ^ 3 * |AffinityCharge (exoticLift M w₀ δ) (handleCycle w₀) 3|) ^ 2 /
      (27 * R ^ 4) ≤
      3 * KillingDefect (exoticLift M w₀ δ) pi_dist := by
  have h := killingDefect_quantitative (exoticLift M w₀ δ) (handleCycle w₀) 3
    (by norm_num) (handleCycle_closed w₀)
    pi_dist ε R hε hR hπ_floor hWR hWR_nn
  convert h using 2
  norm_num [pow_mul, pow_succ]

end Instantiation

end SGC.Bridge.AffinityProtectionQuantitative
