/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Structure.CoherenceDynamics
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Residual Descent: quantified dissipation and vanishing incoherence

Energy descent alone (`SGC.Structure.CoherenceDynamics`) proves only that
the scalar `E(A_t)` converges.  This module adds the quantified descent
inequality

  `E(A_t) − E(A_{t+1}) ≥ c · R(A_t)²,  c > 0`

for a nonnegative **incoherence residual** `R`, and draws the first
conclusion that deserves the phrase "approaches coherence":

1. **`rate_mul_sum_le`** — dissipation telescopes: the total dissipated
   quantity `c · Σ_{t<T} R(A_t)²` is bounded by the initial energy.
2. **`summable_residual_sq`** — hence `Σ R(A_t)²` converges, with
   **`tsum_residual_sq_le`**: `Σ_t R(A_t)² ≤ E(A_0)/c`.
3. **`residual_tendsto_zero`** (Level 2) — therefore `R(A_t) → 0`.

What is still NOT claimed: `A_t → A⋆`.  State convergence needs a finite
state space, compactness plus continuity, contraction, or an isolated
fixed point — deliberately beyond this layer.
-/

namespace SGC.Coherence

open Filter Finset

variable {α : Type*}

/-- A coherence dynamics with a quantified descent certificate: each
    update dissipates at least `rate · R(a)²` of energy, where `R` is a
    nonnegative incoherence residual (local mismatch, gluing defect,
    gradient norm — any scalar measure of remaining incoherence). -/
structure ResidualDynamics (α : Type*) extends CoherenceDynamics α where
  /-- The incoherence residual `R` of an active state. -/
  residual : α → ℝ
  /-- The residual is nonnegative. -/
  residual_nonneg : ∀ a, 0 ≤ residual a
  /-- The dissipation rate `c`. -/
  rate : ℝ
  /-- The rate is strictly positive. -/
  rate_pos : 0 < rate
  /-- Quantified descent: `E(a) − E(U(a)) ≥ c · R(a)²`. -/
  quantified : ∀ a, rate * residual a ^ 2 ≤ energy a - energy (update a)

namespace ResidualDynamics

variable (D : ResidualDynamics α)

/-- The orbit of the underlying coherence dynamics. -/
abbrev orbit (a₀ : α) (t : ℕ) : α :=
  D.toCoherenceDynamics.orbit a₀ t

@[simp] theorem orbit_zero (a₀ : α) : D.orbit a₀ 0 = a₀ :=
  rfl

theorem orbit_succ (a₀ : α) (t : ℕ) :
    D.orbit a₀ (t + 1) = D.update (D.orbit a₀ t) :=
  D.toCoherenceDynamics.orbit_succ a₀ t

/-- **Dissipation telescopes**: over any finite horizon, the total
    dissipated residual is paid for by the initial energy:
    `c · Σ_{t<T} R(A_t)² ≤ E(A_0)`. -/
theorem rate_mul_sum_le (a₀ : α) (T : ℕ) :
    D.rate * ∑ t ∈ range T, D.residual (D.orbit a₀ t) ^ 2 ≤ D.energy a₀ := by
  rw [mul_sum]
  calc ∑ t ∈ range T, D.rate * D.residual (D.orbit a₀ t) ^ 2
      ≤ ∑ t ∈ range T,
          (D.energy (D.orbit a₀ t) - D.energy (D.orbit a₀ (t + 1))) := by
        refine sum_le_sum fun t _ => ?_
        have h := D.quantified (D.orbit a₀ t)
        rwa [← D.orbit_succ] at h
    _ = D.energy (D.orbit a₀ 0) - D.energy (D.orbit a₀ T) :=
        sum_range_sub' (fun t => D.energy (D.orbit a₀ t)) T
    _ ≤ D.energy a₀ := by
        have h0 := D.nonneg (D.orbit a₀ T)
        simp only [orbit_zero]
        linarith

/-- The partial sums of squared residuals are uniformly bounded by
    `E(A_0)/c`. -/
theorem sum_residual_sq_le (a₀ : α) (T : ℕ) :
    ∑ t ∈ range T, D.residual (D.orbit a₀ t) ^ 2 ≤ D.energy a₀ / D.rate := by
  rw [le_div_iff₀ D.rate_pos]
  have h := D.rate_mul_sum_le a₀ T
  linarith

/-- **Residual summability**: the squared residuals form a summable
    series — the budget `E(A_0)/c` pays for all dissipation, forever. -/
theorem summable_residual_sq (a₀ : α) :
    Summable fun t => D.residual (D.orbit a₀ t) ^ 2 :=
  summable_of_sum_range_le (fun _ => sq_nonneg _) (D.sum_residual_sq_le a₀)

/-- The total squared residual is bounded by the initial budget:
    `Σ_t R(A_t)² ≤ E(A_0)/c`. -/
theorem tsum_residual_sq_le (a₀ : α) :
    ∑' t, D.residual (D.orbit a₀ t) ^ 2 ≤ D.energy a₀ / D.rate :=
  Real.tsum_le_of_sum_range_le (fun _ => sq_nonneg _)
    (D.sum_residual_sq_le a₀)

/-- **The residual vanishes** (Level 2): under quantified descent, the
    incoherence residual tends to zero along every orbit —
    `R(A_t) → 0`.  This is the first theorem that deserves the phrase
    "the active trajectory approaches coherence". -/
theorem residual_tendsto_zero (a₀ : α) :
    Tendsto (fun t => D.residual (D.orbit a₀ t)) atTop (nhds 0) := by
  have hsq : Tendsto (fun t => D.residual (D.orbit a₀ t) ^ 2)
      atTop (nhds 0) :=
    (D.summable_residual_sq a₀).tendsto_atTop_zero
  have hs : Tendsto (fun t => Real.sqrt (D.residual (D.orbit a₀ t) ^ 2))
      atTop (nhds 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa [Function.comp, Real.sqrt_zero] using h
  have hfun : (fun t => Real.sqrt (D.residual (D.orbit a₀ t) ^ 2)) =
      fun t => D.residual (D.orbit a₀ t) :=
    funext fun t => Real.sqrt_sq (D.residual_nonneg _)
  rwa [hfun] at hs

end ResidualDynamics

end SGC.Coherence
