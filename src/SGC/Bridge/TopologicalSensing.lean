/-
Copyright (c) 2026 Jason Shroyer. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Order.Chebyshev
import SGC.Renormalization.KernelHorizon

/-!
# Topological Sensing: winding, charge, and the dissipation bound

Primitive 22, formalized honestly. The original proposal (exponential
validity horizon `T* ∝ e^{cLλ}` from the diffusion spectral gap alone) is
FALSE — on a cycle of length `L` the gap scales like `1/L²` and an
unconfined defect winds in diffusive time `O(L²)`, not `e^{cL}`; the
exponential regime requires an extensive barrier/confinement hypothesis
(recorded as future conditional work). What IS true — and deeper — is a
three-register ladder connecting loop observables to the repository's
existing charge and dissipation theory:

1. **Gauge protection is exact and eternal** (`windingSum_exact`,
   `cycleSum_exact_eq_zero`, `cycleSum_gauge_invariant`): for an exact
   edge-form `ξ = dg`, the winding sum along ANY trajectory telescopes to
   `g(end) − g(start)` — deterministically bounded forever, on every
   sample path. Local sensor recalibration (gauge clutter) can NEVER move
   a loop observable. This is the additive shadow of `AffinityProtection`'s
   multiplicative Kolmogorov telescope.

2. **Stationarity silences gauge flux; reversibility silences ALL flux**
   (`flux_exact_eq_zero_of_stationary`, `flux_eq_zero_of_detailedBalance`):
   the mean winding rate of an exact form vanishes for every stationary
   kernel; detailed balance kills the mean rate of every antisymmetric
   edge observable. Systematic winding REQUIRES irreversibility.

3. **THE DISSIPATION BOUND** (`flux_sq_le_killingDefect`): for any
   antisymmetric edge-form, `(2·flux ξ)² ≤ KillingDefect · ‖ξ‖²` — the
   squared mean winding rate is bounded by the (discrete-time) Killing
   defect, the Frobenius mass of the probability current. Cauchy–Schwarz
   against the current matrix. Physical reading: **a drifting
   interferometric loop closure is a thermometer for entropy production**;
   reversible clutter produces only zero-mean noise on topological
   observables. This is an elementary, exact, finite-state cousin of the
   mean-current half of thermodynamic uncertainty relations
   (Barato–Seifert 2015; Schnakenberg cycle theory) — the full TUR
   (variance form) is NOT claimed.

4. **Expected winding grows linearly with time at rate = flux**
   (`expectedWinding_eq_time_mul_flux`), hence eternally zero under
   detailed balance and defect-bounded in general
   (`expectedWinding_sq_le`).

## Honest scope

* `expectedWinding` is DEFINED by the standard Markov-marginal formula
  `Σ_{k<t} Σ_{u,v} (π·Pᵏ)(u) P(u,v) ξ(u,v)`; the identification with a
  kernel-level finite path-space expectation is standard but not itself
  formalized here (finite path-space API = recorded next step; it would
  also serve the trajectory axioms in `EntropyProduction`).
* No exponential-in-`L` lifetime is claimed anywhere. The conditional
  barrier→horizon theorem is future work with an explicit
  energy–entropy hypothesis (`βκΔ_E > h`).
* Discrete-time throughout; `KillingDefectDT` is the DTMC analogue of
  `DiscreteFluidDynamics`' generator-level defect.
-/

namespace SGC.Bridge.TopologicalSensing

open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## §1. Edge forms, gauge forms, cycle and winding sums -/

/-- The differential of a vertex potential: the exact (gauge) edge-form
`(dg)(u,v) = g v − g u`. Local recalibration of sensors is exactly a
change `ξ ↦ ξ + dg`. -/
def dPot (g : V → ℝ) : V → V → ℝ := fun u v => g v - g u

/-- Winding sum of an edge-form along a trajectory: the additive
accumulation `Σ_{k<t} ξ(x_k, x_{k+1})`. For an oriented gate/cycle form
this is the (lifted) winding coordinate. -/
def windingSum (ξ : V → V → ℝ) (x : ℕ → V) (t : ℕ) : ℝ :=
  ∑ k ∈ Finset.range t, ξ (x k) (x (k + 1))

/-- Cycle sum (holonomy) of an edge-form around a closed cycle. -/
def cycleSum (ξ : V → V → ℝ) (c : ℕ → V) (len : ℕ) : ℝ :=
  windingSum ξ c len

/-- **Gauge forms telescope on every trajectory**: the winding sum of an
exact form is the potential difference of the endpoints — bounded
deterministically, for all time, on every sample path. Eternal exact
protection of loop observables against local clutter. -/
theorem windingSum_exact (g : V → ℝ) (x : ℕ → V) (t : ℕ) :
    windingSum (dPot g) x t = g (x t) - g (x 0) := by
  unfold windingSum dPot
  exact Finset.sum_range_sub (fun k => g (x k)) t

/-- Holonomy of a gauge form around any closed cycle vanishes. -/
theorem cycleSum_exact_eq_zero (g : V → ℝ) (c : ℕ → V) (len : ℕ)
    (hc : c 0 = c len) :
    cycleSum (dPot g) c len = 0 := by
  unfold cycleSum
  rw [windingSum_exact, hc, sub_self]

/-- **Gauge invariance of loop closure**: adding any local recalibration
`dg` to the phase field leaves every cycle holonomy unchanged. The
multistatic interferometric closure cancels ALL purely local sensor
offsets — exactly, not approximately. -/
theorem cycleSum_gauge_invariant (ξ : V → V → ℝ) (g : V → ℝ)
    (c : ℕ → V) (len : ℕ) (hc : c 0 = c len) :
    cycleSum (fun u v => ξ u v + dPot g u v) c len = cycleSum ξ c len := by
  unfold cycleSum windingSum
  rw [Finset.sum_add_distrib]
  have := cycleSum_exact_eq_zero g c len hc
  unfold cycleSum windingSum at this
  rw [this, add_zero]

/-- Robustness: perturbing the phase field moves any cycle sum by at most
the accumulated perturbation along the cycle. Gauge clutter cancels
exactly; non-gauge clutter enters only through its own holonomy. -/
theorem cycleSum_perturbation (ξ η : V → V → ℝ) (c : ℕ → V) (len : ℕ) :
    |cycleSum (fun u v => ξ u v + η u v) c len - cycleSum ξ c len|
      ≤ ∑ k ∈ Finset.range len, |η (c k) (c (k + 1))| := by
  unfold cycleSum windingSum
  rw [Finset.sum_add_distrib]
  simp only [add_sub_cancel_left]
  exact Finset.abs_sum_le_sum_abs _ _

/-! ## §2. Currents, flux, and the silence theorems -/

/-- The probability current of a kernel–measure pair on an ordered edge:
`J(u,v) = π(u)P(u,v) − π(v)P(v,u)`. -/
def currentMatrix (P : Matrix V V ℝ) (pi_dist : V → ℝ) : V → V → ℝ :=
  fun u v => pi_dist u * P u v - pi_dist v * P v u

/-- Mean flux (drift rate) of an edge-form in one step at measure `π`:
`Σ_{u,v} π(u) P(u,v) ξ(u,v)`. -/
def flux (P : Matrix V V ℝ) (pi_dist : V → ℝ) (ξ : V → V → ℝ) : ℝ :=
  ∑ u : V, ∑ v : V, pi_dist u * P u v * ξ u v

/-- Discrete-time detailed balance. -/
def DetailedBalanceDT (P : Matrix V V ℝ) (pi_dist : V → ℝ) : Prop :=
  ∀ u v, pi_dist u * P u v = pi_dist v * P v u

/-- Antisymmetry of an edge-form (orientation-compatible observables). -/
def Antisymm (ξ : V → V → ℝ) : Prop := ∀ u v, ξ v u = -ξ u v

/-- **Discrete-time Killing defect**: the Frobenius mass of the
probability current — the DTMC analogue of the Chern–Hamilton defect of
`DiscreteFluidDynamics`. Zero iff detailed balance. -/
def KillingDefectDT (P : Matrix V V ℝ) (pi_dist : V → ℝ) : ℝ :=
  ∑ u : V, ∑ v : V, (currentMatrix P pi_dist u v) ^ 2

/-- For antisymmetric forms the flux is half the pairing with the current:
`flux ξ = ½ Σ J(u,v) ξ(u,v)`. -/
theorem flux_eq_half_current_pairing (P : Matrix V V ℝ) (pi_dist : V → ℝ)
    (ξ : V → V → ℝ) (hξ : Antisymm ξ) :
    flux P pi_dist ξ
      = (1 / 2) * ∑ u : V, ∑ v : V, currentMatrix P pi_dist u v * ξ u v := by
  unfold flux currentMatrix
  have hswap : (∑ u : V, ∑ v : V, pi_dist u * P u v * ξ u v)
      = ∑ u : V, ∑ v : V, pi_dist v * P v u * ξ v u := by
    exact Finset.sum_comm
  have hexp : (∑ u : V, ∑ v : V,
      (pi_dist u * P u v - pi_dist v * P v u) * ξ u v)
      = (∑ u : V, ∑ v : V, pi_dist u * P u v * ξ u v)
        - ∑ u : V, ∑ v : V, pi_dist v * P v u * ξ u v := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  have hanti : (∑ u : V, ∑ v : V, pi_dist v * P v u * ξ u v)
      = -∑ u : V, ∑ v : V, pi_dist u * P u v * ξ u v := by
    rw [hswap]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hξ u v]
    ring
  rw [hexp, hanti]
  ring

/-- **Reversibility silences every topological drift**: under detailed
balance the mean winding rate of EVERY antisymmetric edge observable is
zero. Systematic loop drift certifies irreversibility. -/
theorem flux_eq_zero_of_detailedBalance (P : Matrix V V ℝ) (pi_dist : V → ℝ)
    (ξ : V → V → ℝ) (hξ : Antisymm ξ) (hdb : DetailedBalanceDT P pi_dist) :
    flux P pi_dist ξ = 0 := by
  rw [flux_eq_half_current_pairing P pi_dist ξ hξ]
  have : ∀ u v, currentMatrix P pi_dist u v = 0 := by
    intro u v
    unfold currentMatrix
    rw [hdb u v, sub_self]
  rw [Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by
    rw [this u v, zero_mul]]
  simp

/-- **Stationarity silences gauge flux**: for a row-stochastic kernel with
stationary measure, the mean drift of every EXACT form vanishes — even
without reversibility. Gauge observables never accumulate in expectation. -/
theorem flux_exact_eq_zero_of_stationary (P : Matrix V V ℝ)
    (pi_dist : V → ℝ) (g : V → ℝ)
    (hrow : ∀ u, ∑ v, P u v = 1)
    (hstat : ∀ v, ∑ u, pi_dist u * P u v = pi_dist v) :
    flux P pi_dist (dPot g) = 0 := by
  unfold flux dPot
  have hsplit : (∑ u : V, ∑ v : V, pi_dist u * P u v * (g v - g u))
      = (∑ u : V, ∑ v : V, pi_dist u * P u v * g v)
        - ∑ u : V, ∑ v : V, pi_dist u * P u v * g u := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [hsplit]
  have h1 : (∑ u : V, ∑ v : V, pi_dist u * P u v * g v)
      = ∑ v : V, pi_dist v * g v := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.sum_mul, hstat v]
  have h2 : (∑ u : V, ∑ v : V, pi_dist u * P u v * g u)
      = ∑ u : V, pi_dist u * g u := by
    refine Finset.sum_congr rfl fun u _ => ?_
    calc (∑ v : V, pi_dist u * P u v * g u)
        = (pi_dist u * g u) * ∑ v : V, P u v := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun v _ => by ring
      _ = pi_dist u * g u := by rw [hrow u, mul_one]
  rw [h1, h2, sub_self]

/-! ## §3. The dissipation bound -/

/-- **THE DISSIPATION BOUND** (mean-current TUR shadow): the squared mean
winding rate of any antisymmetric edge observable is bounded by the
Killing defect times the observable's squared mass:

`(2·flux ξ)² ≤ KillingDefectDT · Σ ξ²`.

Cauchy–Schwarz against the probability current. A drifting loop closure
is quantitative evidence of entropy production; zero defect (detailed
balance) forces zero drift on every topological observable. -/
theorem flux_sq_le_killingDefect (P : Matrix V V ℝ) (pi_dist : V → ℝ)
    (ξ : V → V → ℝ) (hξ : Antisymm ξ) :
    (2 * flux P pi_dist ξ) ^ 2
      ≤ KillingDefectDT P pi_dist * ∑ u : V, ∑ v : V, (ξ u v) ^ 2 := by
  rw [flux_eq_half_current_pairing P pi_dist ξ hξ]
  have hpair : 2 * ((1 / 2) * ∑ u : V, ∑ v : V,
      currentMatrix P pi_dist u v * ξ u v)
      = ∑ u : V, ∑ v : V, currentMatrix P pi_dist u v * ξ u v := by ring
  rw [hpair]
  -- Flatten the double sums to a single sum over pairs, then Cauchy–Schwarz.
  have e1 : (∑ p : V × V, currentMatrix P pi_dist p.1 p.2 * ξ p.1 p.2)
      = ∑ u : V, ∑ v : V, currentMatrix P pi_dist u v * ξ u v :=
    Fintype.sum_prod_type _
  have e2 : (∑ p : V × V, (currentMatrix P pi_dist p.1 p.2) ^ 2)
      = ∑ u : V, ∑ v : V, (currentMatrix P pi_dist u v) ^ 2 :=
    Fintype.sum_prod_type _
  have e3 : (∑ p : V × V, (ξ p.1 p.2) ^ 2)
      = ∑ u : V, ∑ v : V, (ξ u v) ^ 2 :=
    Fintype.sum_prod_type _
  rw [← e1]
  unfold KillingDefectDT
  rw [← e2, ← e3]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun p : V × V => currentMatrix P pi_dist p.1 p.2)
    (fun p : V × V => ξ p.1 p.2)

/-! ## §4. Expected winding: linear growth at rate = flux -/

/-- Expected winding after `t` steps from initial measure `π₀`, by the
standard Markov marginal formula: step `k` occupies edge `(u,v)` with
probability `(π₀ Pᵏ)(u) P(u,v)`. (Identification with a formal path-space
expectation is standard; the finite path-space API is recorded future
work.) -/
def expectedWinding (P : Matrix V V ℝ) (pi0 : V → ℝ) (ξ : V → V → ℝ)
    (t : ℕ) : ℝ :=
  ∑ k ∈ Finset.range t, ∑ u : V, ∑ v : V,
    (∑ w : V, pi0 w * (P ^ k) w u) * P u v * ξ u v

/-- A stationary measure stays stationary under every power. -/
lemma stationary_pow (P : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hstat : ∀ v, ∑ u, pi_dist u * P u v = pi_dist v) (k : ℕ) :
    ∀ v, ∑ w, pi_dist w * (P ^ k) w v = pi_dist v := by
  induction k with
  | zero =>
    intro v
    simp [Matrix.one_apply]
  | succ k ih =>
    intro v
    have hexpand : ∀ w, (P ^ (k + 1)) w v = ∑ u, (P ^ k) w u * P u v := by
      intro w
      rw [pow_succ]
      rfl
    calc (∑ w, pi_dist w * (P ^ (k + 1)) w v)
        = ∑ w, ∑ u, pi_dist w * (P ^ k) w u * P u v := by
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [hexpand w, Finset.mul_sum]
          exact Finset.sum_congr rfl fun u _ => by ring
      _ = ∑ u, (∑ w, pi_dist w * (P ^ k) w u) * P u v := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun u _ => by rw [Finset.sum_mul]
      _ = ∑ u, pi_dist u * P u v := by
          exact Finset.sum_congr rfl fun u _ => by rw [ih u]
      _ = pi_dist v := hstat v

/-- **Linear drift law**: from a stationary start, expected winding grows
exactly linearly in time, at rate `flux`. With the silence theorems:
eternally zero under detailed balance; with the dissipation bound: rate²
≤ defect·‖ξ‖²/4. -/
theorem expectedWinding_eq_time_mul_flux (P : Matrix V V ℝ)
    (pi_dist : V → ℝ) (ξ : V → V → ℝ)
    (hstat : ∀ v, ∑ u, pi_dist u * P u v = pi_dist v) (t : ℕ) :
    expectedWinding P pi_dist ξ t = (t : ℝ) * flux P pi_dist ξ := by
  unfold expectedWinding flux
  have hstep : ∀ k ∈ Finset.range t, (∑ u : V, ∑ v : V,
      (∑ w : V, pi_dist w * (P ^ k) w u) * P u v * ξ u v)
      = ∑ u : V, ∑ v : V, pi_dist u * P u v * ξ u v := by
    intro k _
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    rw [stationary_pow P pi_dist hstat k u]
  rw [Finset.sum_congr rfl hstep, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]

/-- Detailed balance keeps every antisymmetric loop observable centered
for ALL time: zero expected winding at every horizon. Diffusive noise is
possible; systematic drift is not. -/
theorem expectedWinding_eq_zero_of_detailedBalance (P : Matrix V V ℝ)
    (pi_dist : V → ℝ) (ξ : V → V → ℝ) (hξ : Antisymm ξ)
    (hstat : ∀ v, ∑ u, pi_dist u * P u v = pi_dist v)
    (hdb : DetailedBalanceDT P pi_dist) (t : ℕ) :
    expectedWinding P pi_dist ξ t = 0 := by
  rw [expectedWinding_eq_time_mul_flux P pi_dist ξ hstat t,
    flux_eq_zero_of_detailedBalance P pi_dist ξ hξ hdb, mul_zero]

/-- Defect-bounded drift at every horizon:
`(2·E[S_t])² ≤ t² · KillingDefect · ‖ξ‖²`. -/
theorem expectedWinding_sq_le (P : Matrix V V ℝ) (pi_dist : V → ℝ)
    (ξ : V → V → ℝ) (hξ : Antisymm ξ)
    (hstat : ∀ v, ∑ u, pi_dist u * P u v = pi_dist v) (t : ℕ) :
    (2 * expectedWinding P pi_dist ξ t) ^ 2
      ≤ (t : ℝ) ^ 2 * (KillingDefectDT P pi_dist
          * ∑ u : V, ∑ v : V, (ξ u v) ^ 2) := by
  rw [expectedWinding_eq_time_mul_flux P pi_dist ξ hstat t]
  have h := flux_sq_le_killingDefect P pi_dist ξ hξ
  have ht : (0:ℝ) ≤ (t : ℝ) ^ 2 := sq_nonneg _
  calc (2 * ((t : ℝ) * flux P pi_dist ξ)) ^ 2
      = (t : ℝ) ^ 2 * (2 * flux P pi_dist ξ) ^ 2 := by ring
    _ ≤ (t : ℝ) ^ 2 * (KillingDefectDT P pi_dist
          * ∑ u : V, ∑ v : V, (ξ u v) ^ 2) :=
        mul_le_mul_of_nonneg_left h ht

end SGC.Bridge.TopologicalSensing
