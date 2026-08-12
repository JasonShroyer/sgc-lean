/-
Copyright (c) 2026 Jason Shroyer. All rights reserved.
Released under Apache 2.0 license.
-/
import SGC.Bridge.AffinityProtectionQuantitative

/-!
# The Dissipation Floor: entropy production is bounded below by topology

Final link of the predictive-thermodynamics chain
(`docs/predictive-thermodynamics-chain-design.md`): a quantitative bridge
from the **thermodynamic register** (Schnakenberg entropy production, the
physical cost of maintaining a nonequilibrium state) to the **topological
register** (the affinity charge of a cycle, which no measure re-weighting
can erase).

## The three steps

1. `gibbs_quadratic_lower` — the sharpened Gibbs inequality
   `(a−b)²/(a+b) ≤ (a−b)·log(a/b)` for `a, b > 0`. The elementary
   quadratic lower bound that turns the second law from a sign statement
   (`gibbs_term_nonneg`, `EntropyProduction.lean`) into a *quantity*.
   Proof needs only `log x ≤ x − 1` (Mathlib), applied on the smaller side.
2. `entropyProductionRate_ge_killingDefect_div` — summing step:
   `σ(L,π) ≥ KillingDefect(L,π) / (4R)` whenever the weighted rates lie in
   `(0, R]`. Dissipation dominates the squared Frobenius mass of the
   probability current: **entropy production and the Killing defect are the
   same object up to rate bounds** — the thermodynamic and geometric
   registers exchange at rate `1/(4R)`.
3. `dissipation_floor` — composing with `killingDefect_quantitative`:
   `(ε^m·|Q|)² / (m³·R^{2(m−1)}) ≤ 4·R·m·σ(L,π)`.
   A nonzero affinity charge around any cycle forces strictly positive
   entropy production, quantitatively, for **every** admissible measure.

## Reading (the CRH / boundary-readout consequence)

No optimization of a readout — no annealing, no attention re-weighting, no
choice of stationary measure within the admissible class — can reduce the
maintenance cost of a state below its topological charge. Together with the
validity-horizon chain (`trajectory_closure_bound`, `T* ~ 1/ε`) this makes
predictive validity a thermodynamically priced resource with a topological
floor: *foresight has an energy price, and the price has a charge floor.*

## Conventions and honest scope

* Stated for **rate/kernel matrices** (all `π`-weighted entries nonnegative,
  off-diagonal strictly positive), matching `killingDefect_quantitative`.
  The diagonal never enters: the Schnakenberg sum guards `x = y` and the
  cycle products are off-diagonal.
* "Near-equilibrium quadratic equivalence" is used in the direction that
  holds **globally** (dissipation ≥ quadratic); the converse upper bound is
  false in general and not claimed.
* No selection dynamics is claimed here; this is the floor that selection
  (the descent ladder) cannot pass. The selection statement is L3a of the
  design note.
-/

namespace SGC.Bridge.DissipationFloor

open Finset Matrix
open SGC.Thermodynamics
open SGC.Bridge.DiscreteFluidDynamics
open SGC.Bridge.AffinityProtection
open SGC.Bridge.AffinityProtectionQuantitative

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## §1. The sharpened Gibbs inequality -/

/-- Auxiliary: the ordered case `b ≤ a`. From `log(b/a) ≤ b/a − 1` (Mathlib)
we get `log(a/b) ≥ (a−b)/a`, and `(a−b)²/(a+b) ≤ (a−b)²/a` closes it. -/
lemma gibbs_quadratic_aux {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    (a - b) ^ 2 / (a + b) ≤ (a - b) * Real.log (a / b) := by
  have hab : 0 ≤ a - b := sub_nonneg.mpr hba
  have hlog : (a - b) / a ≤ Real.log (a / b) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hb ha)
    have hinv : Real.log (b / a) = -Real.log (a / b) := by
      rw [← Real.log_inv, inv_div]
    rw [hinv] at h
    have h3 : (a - b) / a = 1 - b / a := by field_simp
    rw [h3]
    linarith
  have hstep : (a - b) ^ 2 / (a + b) ≤ (a - b) ^ 2 / a := by
    rw [div_le_div_iff₀ (by linarith) ha]
    nlinarith [sq_nonneg (a - b), hb.le]
  calc (a - b) ^ 2 / (a + b) ≤ (a - b) ^ 2 / a := hstep
    _ = (a - b) * ((a - b) / a) := by ring
    _ ≤ (a - b) * Real.log (a / b) := mul_le_mul_of_nonneg_left hlog hab

/-- **The sharpened Gibbs inequality.** For positive `a, b`:
`(a − b)²/(a + b) ≤ (a − b)·log(a/b)`. Upgrades the second-law sign
(`gibbs_term_nonneg`) to a quadratic quantity — the per-edge exchange rate
between dissipation and squared current. -/
lemma gibbs_quadratic_lower {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a - b) ^ 2 / (a + b) ≤ (a - b) * Real.log (a / b) := by
  rcases le_total b a with h | h
  · exact gibbs_quadratic_aux ha hb h
  · have hsym := gibbs_quadratic_aux hb ha h
    have hlog : Real.log (a / b) = -Real.log (b / a) := by
      rw [← Real.log_inv, inv_div]
    calc (a - b) ^ 2 / (a + b) = (b - a) ^ 2 / (b + a) := by ring_nf
      _ ≤ (b - a) * Real.log (b / a) := hsym
      _ = (a - b) * Real.log (a / b) := by rw [hlog]; ring

/-! ## §2. Entropy production dominates the Killing defect -/

/-- **Dissipation dominates squared current.** If all `π`-weighted rates are
strictly positive off the diagonal and bounded by `R`, then the Schnakenberg
entropy production rate is at least the Killing defect over `4R`:

`σ(L, π) ≥ KillingDefect(L, π) / (4R)`.

The thermodynamic and geometric registers measure the same nonequilibrium
content, exchanging at rate `1/(4R)`. -/
theorem entropyProductionRate_ge_killingDefect_div (L : Matrix V V ℝ)
    (pi_dist : V → ℝ) {R : ℝ} (hR : 0 < R)
    (hw_pos : ∀ x y, x ≠ y → 0 < pi_dist x * L x y)
    (hWR : ∀ x y, pi_dist x * L x y ≤ R) :
    KillingDefect L pi_dist / (4 * R) ≤ EntropyProductionRate L pi_dist := by
  have hterm : ∀ x y, (ProbabilityCurrent L pi_dist x y) ^ 2 / (2 * R) ≤
      (if x = y ∨ L x y = 0 then 0
       else (pi_dist x * L x y - pi_dist y * L y x) *
            Real.log (pi_dist x * L x y / (pi_dist y * L y x))) := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      simp [ProbabilityCurrent]
    · have ha := hw_pos x y hxy
      have hb := hw_pos y x (Ne.symm hxy)
      have hLxy : L x y ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at ha
        exact lt_irrefl 0 ha
      rw [if_neg (by push_neg; exact ⟨hxy, hLxy⟩)]
      have hsum : pi_dist x * L x y + pi_dist y * L y x ≤ 2 * R := by
        have h1 := hWR x y
        have h2 := hWR y x
        linarith
      have hJ : ProbabilityCurrent L pi_dist x y
          = pi_dist x * L x y - pi_dist y * L y x := rfl
      have h2 : (ProbabilityCurrent L pi_dist x y) ^ 2 / (2 * R) ≤
          (ProbabilityCurrent L pi_dist x y) ^ 2 /
            (pi_dist x * L x y + pi_dist y * L y x) := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith [sq_nonneg (ProbabilityCurrent L pi_dist x y)]
      calc (ProbabilityCurrent L pi_dist x y) ^ 2 / (2 * R)
          ≤ (ProbabilityCurrent L pi_dist x y) ^ 2 /
              (pi_dist x * L x y + pi_dist y * L y x) := h2
        _ ≤ (pi_dist x * L x y - pi_dist y * L y x) *
              Real.log (pi_dist x * L x y / (pi_dist y * L y x)) := by
            rw [hJ]
            exact gibbs_quadratic_lower ha hb
  have hsum : (∑ x, ∑ y, (ProbabilityCurrent L pi_dist x y) ^ 2 / (2 * R)) ≤
      ∑ x, ∑ y, (if x = y ∨ L x y = 0 then 0
        else (pi_dist x * L x y - pi_dist y * L y x) *
             Real.log (pi_dist x * L x y / (pi_dist y * L y x))) :=
    Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hterm x y
  have hdiv : (∑ x, ∑ y, (ProbabilityCurrent L pi_dist x y) ^ 2 / (2 * R))
      = KillingDefect L pi_dist / (2 * R) := by
    unfold KillingDefect
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun x _ => (Finset.sum_div _ _ _).symm
  rw [hdiv] at hsum
  unfold EntropyProductionRate
  have hhalf : KillingDefect L pi_dist / (4 * R)
      = (1 / 2 : ℝ) * (KillingDefect L pi_dist / (2 * R)) := by ring
  rw [hhalf]
  exact mul_le_mul_of_nonneg_left hsum (by norm_num)

/-! ## §3. The topological floor on dissipation -/

/-- **The Dissipation Floor.** A nonzero affinity charge around any cycle
forces strictly positive entropy production, quantitatively:

`(ε^m · |Q|)² / (m³ · R^{2(m−1)}) ≤ 4 · R · m · σ(L, π)`

for every measure `π` with floor `ε` and weighted-rate ceiling `R`. No
re-weighting of the measure — no annealing, no readout optimization — can
dissipate below the topological charge of the cycle structure. Composition
of `killingDefect_quantitative` (charge bounds current) with
`entropyProductionRate_ge_killingDefect_div` (current bounds dissipation). -/
theorem dissipation_floor (L : Matrix V V ℝ) (c : ℕ → V) (m : ℕ)
    (hm : 0 < m) (hc : c 0 = c m)
    (pi_dist : V → ℝ) (ε R : ℝ) (hε : 0 < ε) (hR : 0 < R)
    (hπ_floor : ∀ x, ε ≤ pi_dist x)
    (hw_pos : ∀ x y, x ≠ y → 0 < pi_dist x * L x y)
    (hWR_nn : ∀ x y, 0 ≤ pi_dist x * L x y)
    (hWR : ∀ x y, pi_dist x * L x y ≤ R) :
    (ε ^ m * |AffinityCharge L c m|) ^ 2 / (↑m ^ 3 * R ^ (2 * (m - 1))) ≤
      4 * R * ↑m * EntropyProductionRate L pi_dist := by
  have hK := killingDefect_quantitative L c m hm hc pi_dist ε R hε hR
    hπ_floor hWR hWR_nn
  have hσ := entropyProductionRate_ge_killingDefect_div L pi_dist hR hw_pos hWR
  -- from hσ : K/(4R) ≤ σ, get K ≤ 4Rσ
  have hK4R : KillingDefect L pi_dist ≤ 4 * R * EntropyProductionRate L pi_dist := by
    have h4R : (0:ℝ) < 4 * R := by linarith
    calc KillingDefect L pi_dist
        = (KillingDefect L pi_dist / (4 * R)) * (4 * R) := by field_simp
      _ ≤ EntropyProductionRate L pi_dist * (4 * R) :=
          mul_le_mul_of_nonneg_right hσ h4R.le
      _ = 4 * R * EntropyProductionRate L pi_dist := by ring
  have hm_nn : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  calc (ε ^ m * |AffinityCharge L c m|) ^ 2 / (↑m ^ 3 * R ^ (2 * (m - 1)))
      ≤ ↑m * KillingDefect L pi_dist := hK
    _ ≤ ↑m * (4 * R * EntropyProductionRate L pi_dist) :=
        mul_le_mul_of_nonneg_left hK4R hm_nn
    _ = 4 * R * ↑m * EntropyProductionRate L pi_dist := by ring

/-- Strict form: a nonzero charge forces strictly positive dissipation. -/
theorem entropyProduction_pos_of_affinityCharge (L : Matrix V V ℝ) (c : ℕ → V)
    (m : ℕ) (hm : 0 < m) (hc : c 0 = c m)
    (pi_dist : V → ℝ) (ε R : ℝ) (hε : 0 < ε) (hR : 0 < R)
    (hπ_floor : ∀ x, ε ≤ pi_dist x)
    (hw_pos : ∀ x y, x ≠ y → 0 < pi_dist x * L x y)
    (hWR_nn : ∀ x y, 0 ≤ pi_dist x * L x y)
    (hWR : ∀ x y, pi_dist x * L x y ≤ R)
    (hQ : AffinityCharge L c m ≠ 0) :
    0 < EntropyProductionRate L pi_dist := by
  have hfloor := dissipation_floor L c m hm hc pi_dist ε R hε hR
    hπ_floor hw_pos hWR_nn hWR
  have hnum : 0 < (ε ^ m * |AffinityCharge L c m|) ^ 2 := by
    have h1 : 0 < ε ^ m := pow_pos hε m
    have h2 : 0 < |AffinityCharge L c m| := abs_pos.mpr hQ
    positivity
  have hden : 0 < (m : ℝ) ^ 3 * R ^ (2 * (m - 1)) := by
    have hm' : (0:ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
    positivity
  have hlhs : 0 < (ε ^ m * |AffinityCharge L c m|) ^ 2 /
      ((m : ℝ) ^ 3 * R ^ (2 * (m - 1))) := div_pos hnum hden
  have hm' : (0:ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have h4rm : (0:ℝ) < 4 * R * (m : ℝ) := by positivity
  have hprod : 0 < 4 * R * (m : ℝ) * EntropyProductionRate L pi_dist :=
    lt_of_lt_of_le hlhs hfloor
  by_contra hσ
  push_neg at hσ
  have hle : 4 * R * (m : ℝ) * EntropyProductionRate L pi_dist ≤ 0 :=
    mul_nonpos_iff.mpr (Or.inl ⟨h4rm.le, hσ⟩)
  linarith

end SGC.Bridge.DissipationFloor
