/-
Copyright (c) 2025 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Evolution.FormanRicci
import SGC.Evolution.Surgery
import SGC.Thermodynamics.EntropyProduction

/-!
# The Thermodynamics of Topological Surgery

**Phase 6: The Cost of Change**

## Overview

This module answers the question: *If "Geometry is Logic," then what is "Surgery"?*

Answer: **The Cost of Change.**

You cannot simply "delete an edge" in a physical universe. An edge represents a
correlation, a binding energy. To delete it is to erase information, and by
**Landauer's Principle**, that requires energy.

## The Four Layers

### Layer 1: The Energetics of Structure
Edge weights are interpreted as mutual information (binding strength).
Strong weights (high probability flow) → low potential energy (deep wells).
Weak weights → high energy, unstable bonds.

### Layer 2: The Perturbation (Surgery)
Surgery is a **thermodynamic process**, not just a graph operation.
- **Cutting**: Infinite potential barrier insertion (w → 0, U → ∞)
- **Sewing**: Potential barrier removal

### Layer 3: The First Law of Evolution
Energy balance: Geometric relief (ΔE_Yamabe) pays for entropy cost (Q_heat).
Why do systems evolve? Because curvature stress pays for the cost of change.

### Layer 4: The Criticality
**The Evolution Inequality**: Spontaneous surgery occurs when
  |F_Ricci(e)| > D_KL(π_new ‖ π_old) / w_ij

This is a **phase transition**—emergence happens when accumulated curvature
stress exceeds the information cost of breaking a topological bond.

## References

- Landauer (1961), "Irreversibility and Heat Generation in the Computing Process"
- Bennett (1982), "The Thermodynamics of Computation"
- Parrondo, Horowitz & Sagawa (2015), "Thermodynamics of information"
-/

namespace SGC.Thermodynamics

open SGC.Evolution

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-! ### Layer 1: The Energetics of Structure -/

section BondEnergetics

/-- **Bond Energy**: The potential energy stored in an edge.

    U(e) = -k_B T · ln(w_ij)

    In natural units (k_B T = 1):
    U(e) = -ln(w_ij)

    **Physical Interpretation**:
    - Strong bonds (high weight) → low energy (deep potential wells)
    - Weak bonds (low weight) → high energy (unstable, easy to break)

    This is the "surprise" of the edge weight viewed as a probability. -/
noncomputable def BondEnergy (w : ℝ) : ℝ := -Real.log w

/-- Bond energy is high for weak bonds. -/
theorem bond_energy_weak_high (w : ℝ) (hw : 0 < w) (hweak : w < 1) :
    BondEnergy w > 0 := by
  simp only [BondEnergy, neg_pos]
  exact Real.log_neg hw hweak

/-- Bond energy is low (negative) for strong bonds. -/
theorem bond_energy_strong_low (w : ℝ) (hstrong : w > 1) :
    BondEnergy w < 0 := by
  simp only [BondEnergy, neg_neg_iff_pos]
  exact Real.log_pos hstrong

/-- **Edge Energy**: Bond energy for a specific edge in a graph. -/
noncomputable def EdgeEnergy (G : WeightedGraph V) (u v : V) : ℝ :=
  if G.adj u v then BondEnergy (G.edgeWeight u v) else 0

/-- **Structural Energy**: Total bond energy of the graph.

    U_total = Σ_{(i,j) ∈ E} U(i,j)

    This measures the total "binding energy" of the topology. -/
noncomputable def StructuralEnergy (G : WeightedGraph V) : ℝ :=
  (1/2) * ∑ u : V, ∑ v : V, EdgeEnergy G u v

end BondEnergetics

/-! ### Layer 2: The Information Cost of Surgery -/

section SurgeryCost

/-- **Stationary Distribution**: The equilibrium distribution of a weighted graph.

    For a graph G, π_G(v) is the probability of being at vertex v at equilibrium.

    **Axiomatized**: Computing stationary distributions requires solving
    the eigenvalue problem Lπ = 0. We axiomatize its existence. -/
axiom StationaryDistribution (G : WeightedGraph V) : V → ℝ

/-- Stationary distribution is a valid probability distribution. -/
axiom stationary_is_probability (G : WeightedGraph V) :
  (∀ v, 0 ≤ StationaryDistribution G v) ∧
  (∑ v : V, StationaryDistribution G v = 1)

/-- **KL Divergence**: The information distance between distributions.

    D_KL(p ‖ q) = Σ_v p(v) · ln(p(v) / q(v))

    Measures how much "surprise" p has about q. -/
noncomputable def KLDivergence (p q : V → ℝ) : ℝ :=
  ∑ v : V, p v * Real.log (p v / q v)

/-- KL divergence is non-negative (Gibbs' inequality).

    **Signature note (Apr 26 2026)**: the previous axiom omitted the
    sum-to-1 hypotheses `hp_sum, hq_sum` and was therefore
    *mathematically incorrect* — the inequality `KL ≥ 0` fails for
    arbitrary non-negative `p, q` (e.g., `p = (½, 0), q = (1, 1)` gives
    `KL = -½ log 2 < 0`).  This refactor converts the broken axiom to a
    correctly-hypothesised theorem and updates the single downstream
    caller `surgery_cost_nonneg` to supply the missing hypotheses (which
    come for free from `stationary_is_probability`).

    **Proof**: pointwise Gibbs inequality via
    `Real.one_sub_inv_le_log_of_pos`, summed and combined with
    `∑ p = ∑ q = 1`.  Mirrors `KLDiv_nonneg` in
    `@c:\Lean4 Projects\src\SGC\Thermodynamics\EntropyProduction.lean`. -/
theorem kl_divergence_nonneg (p q : V → ℝ)
    (hp : ∀ v, 0 ≤ p v) (hq : ∀ v, 0 < q v)
    (hp_sum : ∑ v, p v = 1) (hq_sum : ∑ v, q v = 1) :
    KLDivergence p q ≥ 0 := by
  -- Pointwise bound: `p v - q v ≤ p v * log (p v / q v)`.  No `if`
  -- guard here because the definition of `KLDivergence` in this file
  -- does not have one (Mathlib convention `Real.log 0 = 0` makes the
  -- `p v = 0` case automatic via `0 * Real.log 0 = 0`).
  have h_point : ∀ v ∈ (Finset.univ : Finset V),
      p v - q v ≤ p v * Real.log (p v / q v) := by
    intro v _
    by_cases hpv : p v = 0
    · -- `p v = 0`: LHS = `-q v ≤ 0`, RHS = `0 * log 0 = 0`.
      rw [hpv]
      simp only [zero_sub, zero_mul]
      linarith [(hq v).le]
    · have hpv_pos : 0 < p v := lt_of_le_of_ne (hp v) (Ne.symm hpv)
      have hqv_pos : 0 < q v := hq v
      have hpq_pos : 0 < p v / q v := div_pos hpv_pos hqv_pos
      have h_log : 1 - (p v / q v)⁻¹ ≤ Real.log (p v / q v) :=
        Real.one_sub_inv_le_log_of_pos hpq_pos
      rw [show (p v / q v)⁻¹ = q v / p v from by rw [inv_div]] at h_log
      have h_mul := mul_le_mul_of_nonneg_left h_log (le_of_lt hpv_pos)
      have h_simp : p v * (1 - q v / p v) = p v - q v := by field_simp
      linarith [h_simp ▸ h_mul]
  unfold KLDivergence
  show 0 ≤ ∑ v, p v * Real.log (p v / q v)
  calc (0 : ℝ)
      = (∑ v, p v) - (∑ v, q v) := by rw [hp_sum, hq_sum]; ring
    _ = ∑ v, (p v - q v) := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ v, p v * Real.log (p v / q v) := Finset.sum_le_sum h_point

/-- KL divergence is zero iff distributions are equal.

    **Signature note (May 1 2026)**: like `kl_divergence_nonneg` above,
    the previous axiom omitted the sum-to-1 hypotheses and was therefore
    *mathematically incorrect* — e.g., `p = (½, 0), q = (1, 1)` gives
    `KLDivergence p q = 0` but `p ≠ q`.  This refactor converts the
    broken axiom to a correctly-hypothesised theorem and updates the
    sole downstream caller `surgery_cost_zero_iff` to supply the missing
    hypotheses (which come for free from `stationary_is_probability`).

    **Proof**: same strategy as `KLDiv_eq_zero_iff` in
    `@c:\Lean4 Projects\src\SGC\Thermodynamics\EntropyProduction.lean`,
    adapted to the no-`if`-guard `KLDivergence` definition used here
    (Mathlib convention `Real.log 0 = 0` makes the `p v = 0` case
    handle itself: `0 * log 0 = 0`). -/
theorem kl_divergence_zero_iff (p q : V → ℝ)
    (hp : ∀ v, 0 ≤ p v) (hq : ∀ v, 0 < q v)
    (hp_sum : ∑ v, p v = 1) (hq_sum : ∑ v, q v = 1) :
    KLDivergence p q = 0 ↔ p = q := by
  constructor
  · intro h_zero
    -- Pointwise Gibbs bound (no `if` guard).
    have h_point : ∀ v ∈ (Finset.univ : Finset V),
        p v - q v ≤ p v * Real.log (p v / q v) := by
      intro v _
      by_cases hpv : p v = 0
      · rw [hpv]; simp only [zero_sub, zero_mul]; linarith [(hq v).le]
      · have hpv_pos : 0 < p v := lt_of_le_of_ne (hp v) (Ne.symm hpv)
        have hpq_pos : 0 < p v / q v := div_pos hpv_pos (hq v)
        have h_log : 1 - (p v / q v)⁻¹ ≤ Real.log (p v / q v) :=
          Real.one_sub_inv_le_log_of_pos hpq_pos
        rw [show (p v / q v)⁻¹ = q v / p v from by rw [inv_div]] at h_log
        have h_mul := mul_le_mul_of_nonneg_left h_log (le_of_lt hpv_pos)
        have h_simp : p v * (1 - q v / p v) = p v - q v := by field_simp
        linarith [h_simp ▸ h_mul]
    have h_sum_eq :
        ∑ v, (p v - q v) = ∑ v, p v * Real.log (p v / q v) := by
      rw [Finset.sum_sub_distrib, hp_sum, hq_sum, sub_self]
      exact h_zero.symm
    have h_pt_eq : ∀ v ∈ (Finset.univ : Finset V),
        p v - q v = p v * Real.log (p v / q v) :=
      (Finset.sum_eq_sum_iff_of_le h_point).mp h_sum_eq
    funext v
    have h_v := h_pt_eq v (Finset.mem_univ v)
    by_cases hpv : p v = 0
    · -- `p v = 0`: tightness equation reduces to `-q v = 0`,
      -- contradiction with `q v > 0`.
      rw [hpv] at h_v
      simp only [zero_sub, zero_mul] at h_v
      linarith [hq v]
    · have hpv_pos : 0 < p v := lt_of_le_of_ne (hp v) (Ne.symm hpv)
      have hqv_pos : 0 < q v := hq v
      by_contra hne
      have hqp_pos : 0 < q v / p v := div_pos hqv_pos hpv_pos
      have hqp_ne : q v / p v ≠ 1 := by
        intro h
        apply hne
        have hp_ne : p v ≠ 0 := ne_of_gt hpv_pos
        field_simp at h
        linarith
      have h_strict : Real.log (q v / p v) < q v / p v - 1 :=
        Real.log_lt_sub_one_of_pos hqp_pos hqp_ne
      have h_inv : Real.log (p v / q v) = -Real.log (q v / p v) := by
        rw [show p v / q v = (q v / p v)⁻¹ from by rw [inv_div]]
        rw [Real.log_inv]
      have h_pos_log : Real.log (p v / q v) > 1 - q v / p v := by
        rw [h_inv]; linarith
      have h_pos_mul : p v * Real.log (p v / q v) > p v * (1 - q v / p v) :=
        mul_lt_mul_of_pos_left h_pos_log hpv_pos
      have h_simp : p v * (1 - q v / p v) = p v - q v := by field_simp
      linarith [h_simp ▸ h_pos_mul]
  · intro h_eq
    rw [h_eq]
    unfold KLDivergence
    apply Finset.sum_eq_zero
    intro v _
    by_cases hqv : q v = 0
    · rw [hqv, div_zero, Real.log_zero, mul_zero]
    · rw [div_self hqv, Real.log_one, mul_zero]

/-- **Stationary distribution is strictly positive** for connected graphs.

    For an irreducible Markov chain (connected weighted graph), the unique
    stationary distribution has π(v) > 0 for all states v.

    This is the Perron-Frobenius theorem applied to stochastic matrices. -/
axiom stationary_strictly_positive (G : WeightedGraph V) :
    ∀ v, 0 < StationaryDistribution G v

/-- **Surgery Cost**: The information cost of changing topology.

    W_surg ≥ k_B T · D_KL(π_G ‖ π_G')

    This is Landauer's principle applied to topological change:
    the cost of restructuring is proportional to how much your
    "worldview" (stationary distribution) must shift.

    "Radical metamorphosis is expensive." -/
noncomputable def SurgeryCost (G G' : WeightedGraph V) : ℝ :=
  KLDivergence (StationaryDistribution G) (StationaryDistribution G')

/-- Surgery cost is non-negative. -/
theorem surgery_cost_nonneg (G G' : WeightedGraph V) :
    SurgeryCost G G' ≥ 0 := by
  apply kl_divergence_nonneg
  · exact fun v => (stationary_is_probability G).1 v
  · exact stationary_strictly_positive G'
  · exact (stationary_is_probability G).2
  · exact (stationary_is_probability G').2

/-- Surgery cost is zero iff topology change doesn't affect equilibrium. -/
theorem surgery_cost_zero_iff (G G' : WeightedGraph V)
    (hpos : ∀ v, 0 < StationaryDistribution G' v) :
    SurgeryCost G G' = 0 ↔ StationaryDistribution G = StationaryDistribution G' := by
  apply kl_divergence_zero_iff
  · exact fun v => (stationary_is_probability G).1 v
  · exact hpos
  · exact (stationary_is_probability G).2
  · exact (stationary_is_probability G').2

end SurgeryCost

/-! ### Layer 3: The Evolution Inequality -/

section EvolutionInequality

/-- **Curvature Stress**: The absolute Forman-Ricci curvature.

    This measures how "stressed" an edge is—both positive (cluster)
    and negative (bottleneck) curvature indicate instability. -/
noncomputable def CurvatureStress (G : WeightedGraph V) (u v : V) : ℝ :=
  |FormanRicci G u v|

/-- **Normalized Surgery Cost**: Cost per unit bond strength.

    The denominator w_ij reflects that stronger bonds "justify"
    more radical changes—if you're deeply connected, you can
    afford more disruption. -/
noncomputable def NormalizedCost (G : WeightedGraph V) (u v : V) : ℝ :=
  if h : G.adj u v then
    SurgeryCost G (SurgeryCut G (FormanRicci G u v - 1)) / G.edgeWeight u v
  else 0

/-- **The Evolution Inequality**: Condition for spontaneous surgery.

    A topological change can occur spontaneously if:
      |F_Ricci(e)| > D_KL(π_new ‖ π_old) / w_ij

    **Physical Interpretation**:
    - LHS: Geometric stress (accumulated curvature)
    - RHS: Information inertia (resistance to worldview change)

    When stress exceeds inertia, the system undergoes structural change. -/
def SatisfiesEvolutionInequality (G : WeightedGraph V) (u v : V) : Prop :=
  CurvatureStress G u v > NormalizedCost G u v

/-- **Spontaneous Evolution**: An edge can evolve if it satisfies the inequality.

    This is the **selection criterion** for which topological changes
    are thermodynamically permitted. Not all surgeries are "affordable." -/
def CanEvolve (G : WeightedGraph V) (u v : V) : Prop :=
  G.adj u v ∧ SatisfiesEvolutionInequality G u v

/-- High curvature stress enables evolution. -/
theorem high_stress_enables_evolution (G : WeightedGraph V) (u v : V)
    (hadj : G.adj u v) (hstress : CurvatureStress G u v > NormalizedCost G u v) :
    CanEvolve G u v :=
  ⟨hadj, hstress⟩

end EvolutionInequality

/-! ### Layer 4: The Emergence Phase Transition -/

section EmergencePhaseTransition

/-- **Evolution Potential**: Total evolvability of the graph.

    Σ_e max(0, |F(e)| - Cost(e))

    Positive values indicate edges "ready" to evolve. -/
noncomputable def EvolutionPotential (G : WeightedGraph V) : ℝ :=
  (1/2) * ∑ u : V, ∑ v : V,
    if G.adj u v then max 0 (CurvatureStress G u v - NormalizedCost G u v) else 0

/-- **Critical State**: A graph where some edge is ready to evolve.

    This is the "tipping point" before a phase transition. -/
def IsCritical (G : WeightedGraph V) : Prop :=
  ∃ u v, CanEvolve G u v

/-- **Subcritical State**: No edges can afford to evolve.

    The system is "stuck" in its current topology—not enough
    curvature stress has accumulated. -/
def IsSubcritical (G : WeightedGraph V) : Prop :=
  ∀ u v, G.adj u v → ¬SatisfiesEvolutionInequality G u v

/-- Subcritical is the negation of critical. -/
theorem subcritical_iff_not_critical (G : WeightedGraph V) :
    IsSubcritical G ↔ ¬IsCritical G := by
  constructor
  · intro hsub ⟨u, v, hadj, hsat⟩
    exact hsub u v hadj hsat
  · intro hncrit u v hadj hsat
    apply hncrit
    exact ⟨u, v, hadj, hsat⟩

/-- **The Emergence Conjecture**: Geometric flow accumulates stress.

    As the system evolves via Yamabe/Ricci flow on a fixed topology,
    curvature stress accumulates until it exceeds the information cost
    of breaking bonds. This is when **emergence** happens.

    **Axiomatized**: Full proof requires coupling the flow equations
    to the thermodynamic cost function. -/
axiom emergence_conjecture (G : WeightedGraph V) (t : ℕ) :
  let flow := surgeryFlow G 0 0  -- Trivial surgery (no cutting)
  -- After sufficient time, the system becomes critical
  ∃ T, ∀ t' ≥ T, IsCritical (flow t') ∨ IsSurgeryEquilibrium (flow t') 0 0

end EmergencePhaseTransition

/-! ### The Complete Engine -/

section CompleteEngine

/-- **The First Law of Topology**: Energy is conserved across surgery.

    The Engine of Creation - the complete evolutionary cycle:
    1. Thermodynamics drives Flow (L updates)
    2. Flow creates Curvature (geometric stress)
    3. Curvature accumulates Stress
    4. Stress pays for Surgery (when > Cost)
    5. Surgery changes Topology
    6. New Topology resets Thermodynamics

    ΔE_system = ΔE_Yamabe + Q_heat

    The geometric relief (curvature smoothing) pays for the
    entropy cost (information erasure).

    **Axiomatized**: The full proof requires coupling thermodynamic
    and geometric flow equations. -/
axiom first_law_of_topology (G G' : WeightedGraph V) :
  let ΔE_struct := StructuralEnergy G' - StructuralEnergy G
  let ΔE_yamabe := totalFormanRicci G' - totalFormanRicci G
  let Q_heat := SurgeryCost G G'
  ΔE_struct = ΔE_yamabe + Q_heat

end CompleteEngine

/-! ### Summary

**The Thermodynamics of Topological Surgery** completes the SGC framework:

1. **Bond Energy**: U(e) = -ln(w) maps edge weights to potential energy
2. **Surgery Cost**: W ≥ D_KL(π_old ‖ π_new) via Landauer's principle
3. **Evolution Inequality**: |F(e)| > Cost(e)/w enables spontaneous change
4. **First Law of Topology**: Geometric relief pays for entropy cost

This grounds the abstract surgery operations in physical reality:
- Not all surgeries are "affordable"
- Evolution requires accumulated curvature stress
- Emergence is a **phase transition** at criticality

The cycle is complete:
  Thermodynamics → Flow → Curvature → Stress → Surgery → Topology → ⟲
-/

end SGC.Thermodynamics
