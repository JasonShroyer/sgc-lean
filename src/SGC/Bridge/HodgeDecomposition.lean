/-
Copyright (c) 2026 Jason Shroyer. All rights reserved.
Released under Apache 2.0 license.
-/
import SGC.Bridge.TopologicalSensing

/-!
# The Discrete Hodge Decomposition: the holonomy ring fused

The capstone named by the Consolidation (insights/0012, Insight II): the
Kolmogorov obstruction, NESS protection, gauge sensing protection, and the
dissipation bound are one statement in four costumes. This module states it
once.

**Every antisymmetric edge field splits, explicitly and uniquely, into an
exact (gauge) part and a divergence-free (circulating) part — and both
holonomy and drift see ONLY the circulating part.**

## The construction (fully explicit — no linear-algebra machinery)

Working over the complete graph with the unweighted edge inner product
`⟨ξ,η⟩ = Σ_{u,v} ξ(u,v)η(u,v)`, the Poisson equation is solvable in closed
form: the potential of `ξ` is `g_ξ(v) = div(ξ)(v) / |V|`, because the
complete-graph Laplacian is `n·I − (sum projector)` and total divergence of
an antisymmetric field vanishes. Hence:

* `hodge_decomposition_eq` — `ξ = dPot(g_ξ) + γ` with `div γ = 0`
  (`div_harmonicPart_eq_zero`), both parts antisymmetric;
* `inner_dPot_divFree_eq_zero` — exact ⊥ divergence-free;
* `hodge_pythagoras` — `‖ξ‖² = ‖dPot g_ξ‖² + ‖γ‖²`;
* `hodge_unique` — the split is unique.

## The fusion theorems

* `div_currentMatrix_eq_zero` (**Kirchhoff**): the stationary probability
  current is divergence-free — the current IS a pure circulation; the
  Killing defect is a cycle-space quantity.
* `cycleSum_eq_cycleSum_harmonicPart`: holonomy sees only the circulating
  part (gauge part telescopes away).
* `flux_eq_flux_harmonicPart`: drift sees only the circulating part
  (gauge flux is silenced by stationarity).
* **`flux_sq_le_killingDefect_sharp`** (DISCOVERED EN ROUTE — a strict
  sharpening of `flux_sq_le_killingDefect`): the dissipation bound holds
  with the CIRCULATING norm only,
  `(2·flux ξ)² ≤ KillingDefectDT · ‖harmonicPart ξ‖²`,
  which improves on the old bound by exactly `‖exact part‖²` (Pythagoras).
  Loop drift couples to the current only through the observable's Hodge
  class.
* `killingDefectDT_eq_zero_iff_detailedBalance`: zero defect = detailed
  balance = flat current.
* **`holonomy_ring_unification`** (the capstone bundle): for every
  antisymmetric observable, holonomy and drift factor through the Hodge
  class, and the drift is priced by the defect against the circulating
  norm alone.

## Prior art (honesty ledger)

Discrete Hodge/Helmholtz theory on graphs is classical (Eckmann 1944;
Jiang–Lim–Yao–Ye 2011 for the statistical-ranking formulation); the
decomposition of NESS currents over cycles is Schnakenberg network theory
(1976; also Zia–Schmittmann). The contributions here are: the explicit
complete-graph closed form, the kernel-checked fusion with the SGC
defect/holonomy/dissipation theorems, and the sharpened dissipation bound.
All results close over `[propext, Classical.choice, Quot.sound]`.
-/

namespace SGC.Bridge.HodgeDecomposition

open Finset Matrix
open SGC.Bridge.TopologicalSensing

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## §1. Divergence and the explicit potential -/

/-- Divergence (net inflow) of an edge field at a vertex: `Σ_u ξ(u,v)`. -/
def divergence (ξ : V → V → ℝ) (v : V) : ℝ := ∑ u : V, ξ u v

/-- Total divergence of an antisymmetric field vanishes (pair cancellation). -/
theorem divergence_total_zero (ξ : V → V → ℝ) (hξ : Antisymm ξ) :
    ∑ v : V, divergence ξ v = 0 := by
  unfold divergence
  have hswap : (∑ v : V, ∑ u : V, ξ u v) = ∑ v : V, ∑ u : V, ξ v u :=
    Finset.sum_comm
  have hneg : (∑ v : V, ∑ u : V, ξ v u) = -∑ v : V, ∑ u : V, ξ u v := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun u _ => by rw [← hξ u v]
  have h := hswap.trans hneg
  linarith

/-- The explicit Hodge potential: `g_ξ(v) = div(ξ)(v)/|V|`. On the complete
graph the Poisson equation `div(dPot g) = div ξ` has this closed-form
solution — no matrix inversion needed. -/
noncomputable def hodgePotential (ξ : V → V → ℝ) (v : V) : ℝ :=
  divergence ξ v / (Fintype.card V : ℝ)

/-- The exact (gauge) part of an edge field. -/
noncomputable def exactPart (ξ : V → V → ℝ) : V → V → ℝ :=
  dPot (hodgePotential ξ)

/-- The circulating (divergence-free / cycle-space) part. -/
noncomputable def harmonicPart (ξ : V → V → ℝ) : V → V → ℝ :=
  fun u v => ξ u v - exactPart ξ u v

/-- The decomposition identity (definitional split). -/
theorem hodge_decomposition_eq (ξ : V → V → ℝ) (u v : V) :
    ξ u v = exactPart ξ u v + harmonicPart ξ u v := by
  unfold harmonicPart
  ring

/-- Divergence of an exact field: `div(dPot g)(v) = n·g(v) − Σ g`. -/
theorem div_dPot (g : V → ℝ) (v : V) :
    divergence (dPot g) v = (Fintype.card V : ℝ) * g v - ∑ u : V, g u := by
  unfold divergence dPot
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]

/-- **The circulating part is divergence-free** — the heart of the
decomposition, via the closed-form potential and total-divergence
cancellation. -/
theorem div_harmonicPart_eq_zero [Nonempty V] (ξ : V → V → ℝ)
    (hξ : Antisymm ξ) (v : V) :
    divergence (harmonicPart ξ) v = 0 := by
  have hn : (0:ℝ) < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hsplit : divergence (harmonicPart ξ) v
      = divergence ξ v - divergence (exactPart ξ) v := by
    unfold divergence harmonicPart
    rw [Finset.sum_sub_distrib]
  rw [hsplit]
  unfold exactPart
  rw [div_dPot]
  have hmean : (∑ u : V, hodgePotential ξ u) = 0 := by
    unfold hodgePotential
    rw [← Finset.sum_div, divergence_total_zero ξ hξ, zero_div]
  rw [hmean]
  unfold hodgePotential
  have hne : (Fintype.card V : ℝ) ≠ 0 := hn.ne'
  field_simp
  ring

/-- Both parts inherit antisymmetry. -/
theorem exactPart_antisymm (ξ : V → V → ℝ) : Antisymm (exactPart ξ) := by
  intro u v
  unfold exactPart dPot
  ring

theorem harmonicPart_antisymm (ξ : V → V → ℝ) (hξ : Antisymm ξ) :
    Antisymm (harmonicPart ξ) := by
  intro u v
  unfold harmonicPart
  rw [hξ u v, exactPart_antisymm ξ u v]
  ring

/-! ## §2. Orthogonality, Pythagoras, uniqueness -/

/-- Exact fields are orthogonal to divergence-free antisymmetric fields in
the edge inner product `⟨ξ,η⟩ = Σ_{u,v} ξ(u,v)η(u,v)`. -/
theorem inner_dPot_divFree_eq_zero (h : V → ℝ) (γ : V → V → ℝ)
    (hγa : Antisymm γ) (hγ : ∀ v, divergence γ v = 0) :
    ∑ u : V, ∑ v : V, dPot h u v * γ u v = 0 := by
  unfold dPot
  have hsplit : (∑ u : V, ∑ v : V, (h v - h u) * γ u v)
      = (∑ u : V, ∑ v : V, h v * γ u v)
        - ∑ u : V, ∑ v : V, h u * γ u v := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [hsplit]
  have h1 : (∑ u : V, ∑ v : V, h v * γ u v) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [← Finset.mul_sum]
    have : (∑ u : V, γ u v) = 0 := hγ v
    rw [this, mul_zero]
  have h2 : (∑ u : V, ∑ v : V, h u * γ u v) = 0 := by
    refine Finset.sum_eq_zero fun u _ => ?_
    rw [← Finset.mul_sum]
    have hrow : (∑ v : V, γ u v) = 0 := by
      have : (∑ v : V, γ u v) = -∑ v : V, γ v u := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun v _ => hγa v u
      rw [this]
      have := hγ u
      unfold divergence at this
      rw [this, neg_zero]
    rw [hrow, mul_zero]
  rw [h1, h2, sub_self]

/-- **Hodge–Pythagoras**: the edge norm splits over the decomposition. -/
theorem hodge_pythagoras [Nonempty V] (ξ : V → V → ℝ) (hξ : Antisymm ξ) :
    (∑ u : V, ∑ v : V, (ξ u v) ^ 2)
      = (∑ u : V, ∑ v : V, (exactPart ξ u v) ^ 2)
        + ∑ u : V, ∑ v : V, (harmonicPart ξ u v) ^ 2 := by
  have hcross := inner_dPot_divFree_eq_zero (hodgePotential ξ)
    (harmonicPart ξ) (harmonicPart_antisymm ξ hξ)
    (div_harmonicPart_eq_zero ξ hξ)
  have hexpand : ∀ u v, (ξ u v) ^ 2
      = (exactPart ξ u v) ^ 2 + 2 * (exactPart ξ u v * harmonicPart ξ u v)
        + (harmonicPart ξ u v) ^ 2 := by
    intro u v
    rw [hodge_decomposition_eq ξ u v]
    ring
  have hu : ∀ u : V, (∑ v : V, (ξ u v) ^ 2)
      = (∑ v : V, (exactPart ξ u v) ^ 2)
        + (∑ v : V, 2 * (exactPart ξ u v * harmonicPart ξ u v))
        + ∑ v : V, (harmonicPart ξ u v) ^ 2 := by
    intro u
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => hexpand u v
  have houter : (∑ u : V, ∑ v : V, (ξ u v) ^ 2)
      = (∑ u : V, ∑ v : V, (exactPart ξ u v) ^ 2)
        + (∑ u : V, ∑ v : V, 2 * (exactPart ξ u v * harmonicPart ξ u v))
        + ∑ u : V, ∑ v : V, (harmonicPart ξ u v) ^ 2 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => hu u
  have hzero : (∑ u : V, ∑ v : V,
      2 * (exactPart ξ u v * harmonicPart ξ u v)) = 0 := by
    have hpull : (∑ u : V, ∑ v : V,
        2 * (exactPart ξ u v * harmonicPart ξ u v))
        = 2 * ∑ u : V, ∑ v : V, exactPart ξ u v * harmonicPart ξ u v := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum]
    have hc : (∑ u : V, ∑ v : V, exactPart ξ u v * harmonicPart ξ u v)
        = 0 := by
      unfold exactPart
      exact hcross
    rw [hpull, hc, mul_zero]
  rw [houter, hzero, add_zero]

/-- **Uniqueness**: an antisymmetric field that is both exact and
divergence-free is zero (it is orthogonal to itself). -/
theorem hodge_unique (h : V → ℝ) (hdiv : ∀ v, divergence (dPot h) v = 0) :
    ∀ u v, dPot h u v = 0 := by
  have hanti : Antisymm (dPot h) := by
    intro u v
    unfold dPot
    ring
  have hself := inner_dPot_divFree_eq_zero h (dPot h) hanti hdiv
  have hsq : (∑ u : V, ∑ v : V, (dPot h u v) ^ 2) = 0 := by
    rw [← hself]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl
      fun v _ => pow_two (dPot h u v)
  intro u v
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun x _ => Finset.sum_nonneg fun y _ => sq_nonneg (dPot h x y))).mp
    hsq u (Finset.mem_univ u)
  have := (Finset.sum_eq_zero_iff_of_nonneg
    (fun y _ => sq_nonneg (dPot h u y))).mp hterm v (Finset.mem_univ v)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this

/-! ## §3. Kirchhoff: the stationary current is a pure circulation -/

/-- **Kirchhoff's law**: at stationarity, the probability current is
divergence-free — the current lives entirely in the cycle space, so the
Killing defect is a cycle-space (topological) quantity. -/
theorem div_currentMatrix_eq_zero (P : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hrow : ∀ u, ∑ v, P u v = 1)
    (hstat : ∀ v, ∑ u, pi_dist u * P u v = pi_dist v) (v : V) :
    divergence (currentMatrix P pi_dist) v = 0 := by
  unfold divergence currentMatrix
  rw [Finset.sum_sub_distrib]
  have h1 : (∑ u : V, pi_dist u * P u v) = pi_dist v := hstat v
  have h2 : (∑ u : V, pi_dist v * P v u) = pi_dist v := by
    rw [← Finset.mul_sum, hrow v, mul_one]
  rw [h1, h2, sub_self]

/-! ## §4. The fusion: holonomy and drift see only the Hodge class -/

/-- Holonomy factors through the Hodge class: the gauge part telescopes
away on every closed cycle. -/
theorem cycleSum_eq_cycleSum_harmonicPart (ξ : V → V → ℝ)
    (c : ℕ → V) (len : ℕ) (hc : c 0 = c len) :
    cycleSum ξ c len = cycleSum (harmonicPart ξ) c len := by
  have hgauge := cycleSum_exact_eq_zero (hodgePotential ξ) c len hc
  unfold cycleSum windingSum at *
  have hsplit : (∑ k ∈ Finset.range len, ξ (c k) (c (k + 1)))
      = (∑ k ∈ Finset.range len, dPot (hodgePotential ξ) (c k) (c (k + 1)))
        + ∑ k ∈ Finset.range len, harmonicPart ξ (c k) (c (k + 1)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := hodge_decomposition_eq ξ (c k) (c (k + 1))
    unfold exactPart at this
    linarith
  rw [hsplit, hgauge, zero_add]

/-- Flux is additive over the decomposition. -/
lemma flux_add (P : Matrix V V ℝ) (pi_dist : V → ℝ) (ξ η : V → V → ℝ) :
    flux P pi_dist (fun u v => ξ u v + η u v)
      = flux P pi_dist ξ + flux P pi_dist η := by
  unfold flux
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun v _ => by ring

/-- Drift factors through the Hodge class: gauge flux is silenced by
stationarity, so `flux ξ = flux (harmonicPart ξ)`. -/
theorem flux_eq_flux_harmonicPart (P : Matrix V V ℝ) (pi_dist : V → ℝ)
    (ξ : V → V → ℝ)
    (hrow : ∀ u, ∑ v, P u v = 1)
    (hstat : ∀ v, ∑ u, pi_dist u * P u v = pi_dist v) :
    flux P pi_dist ξ = flux P pi_dist (harmonicPart ξ) := by
  have hdecomp : flux P pi_dist ξ
      = flux P pi_dist (exactPart ξ) + flux P pi_dist (harmonicPart ξ) := by
    rw [← flux_add]
    unfold flux
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    have hb : (fun u v => exactPart ξ u v + harmonicPart ξ u v) u v
        = exactPart ξ u v + harmonicPart ξ u v := rfl
    rw [hb, ← hodge_decomposition_eq ξ u v]
  have hgauge : flux P pi_dist (exactPart ξ) = 0 :=
    flux_exact_eq_zero_of_stationary P pi_dist (hodgePotential ξ) hrow hstat
  rw [hdecomp, hgauge, zero_add]

/-- **THE SHARPENED DISSIPATION BOUND** (discovered en route): the drift of
an antisymmetric observable is priced by the Killing defect against the
CIRCULATING norm only — strictly stronger than `flux_sq_le_killingDefect`
whenever the observable has a nonzero gauge component (Pythagoras gives
the improvement exactly). -/
theorem flux_sq_le_killingDefect_sharp (P : Matrix V V ℝ) (pi_dist : V → ℝ)
    (ξ : V → V → ℝ) (hξ : Antisymm ξ)
    (hrow : ∀ u, ∑ v, P u v = 1)
    (hstat : ∀ v, ∑ u, pi_dist u * P u v = pi_dist v) :
    (2 * flux P pi_dist ξ) ^ 2
      ≤ KillingDefectDT P pi_dist
        * ∑ u : V, ∑ v : V, (harmonicPart ξ u v) ^ 2 := by
  rw [flux_eq_flux_harmonicPart P pi_dist ξ hrow hstat]
  exact flux_sq_le_killingDefect P pi_dist (harmonicPart ξ)
    (harmonicPart_antisymm ξ hξ)

/-- Zero Killing defect is exactly detailed balance (flat current). -/
theorem killingDefectDT_eq_zero_iff_detailedBalance (P : Matrix V V ℝ)
    (pi_dist : V → ℝ) :
    KillingDefectDT P pi_dist = 0 ↔ DetailedBalanceDT P pi_dist := by
  unfold KillingDefectDT DetailedBalanceDT
  constructor
  · intro h0 u v
    have hu := (Finset.sum_eq_zero_iff_of_nonneg
      (fun x _ => Finset.sum_nonneg fun y _ =>
        sq_nonneg (currentMatrix P pi_dist x y))).mp h0 u (Finset.mem_univ u)
    have huv := (Finset.sum_eq_zero_iff_of_nonneg
      (fun y _ => sq_nonneg (currentMatrix P pi_dist u y))).mp hu v
      (Finset.mem_univ v)
    have : currentMatrix P pi_dist u v = 0 :=
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp huv
    unfold currentMatrix at this
    linarith
  · intro hdb
    refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => ?_
    unfold currentMatrix
    rw [hdb u v, sub_self]
    ring

/-! ## §5. The capstone bundle -/

/-- **THE HOLONOMY RING, UNIFIED.** For every antisymmetric edge observable
on a stationary chain: (i) its holonomy on every closed cycle, and (ii) its
mean drift rate, both factor through its circulating (cycle-space) Hodge
component; and (iii) the drift is priced by the Killing defect against the
circulating norm alone. Gauge clutter is invisible to loops and to drift;
the cycle space carries the charge, the current, and the dissipation. -/
theorem holonomy_ring_unification (P : Matrix V V ℝ) (pi_dist : V → ℝ)
    (ξ : V → V → ℝ) (hξ : Antisymm ξ)
    (hrow : ∀ u, ∑ v, P u v = 1)
    (hstat : ∀ v, ∑ u, pi_dist u * P u v = pi_dist v) :
    (∀ (c : ℕ → V) (len : ℕ), c 0 = c len →
        cycleSum ξ c len = cycleSum (harmonicPart ξ) c len)
    ∧ flux P pi_dist ξ = flux P pi_dist (harmonicPart ξ)
    ∧ (2 * flux P pi_dist ξ) ^ 2
        ≤ KillingDefectDT P pi_dist
          * ∑ u : V, ∑ v : V, (harmonicPart ξ u v) ^ 2 :=
  ⟨fun c len hc => cycleSum_eq_cycleSum_harmonicPart ξ c len hc,
   flux_eq_flux_harmonicPart P pi_dist ξ hrow hstat,
   flux_sq_le_killingDefect_sharp P pi_dist ξ hξ hrow hstat⟩

end SGC.Bridge.HodgeDecomposition
