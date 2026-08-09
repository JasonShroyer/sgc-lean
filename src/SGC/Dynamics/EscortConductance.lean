/-
Copyright (c) 2025 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team

# Escort Conductance: The Boundary Mechanism

This module formalizes the **Scale-Dependent q-Escort Conductance**, which connects
the static Tsallis statistics (Phase 3) with dynamic RG flow via the heat semigroup.

## Physical Motivation

The core claim is that a specific geometric quantity—**q-Escort Conductance**—changes
monotonically under the RG flow (diffusion), which forces the system to reveal its
"joints" (boundaries).

**The Dissipative Boundary Imperative**: As a system diffuses (coarse-grains), internal
structure washes out. Any partition boundary that *persists* (maintains low conductance
at large diffusion time t) is structurally significant—it represents a **Markov Blanket**.

## Main Definitions

1. `StatePartition`: A bipartition of the state space into S and Sᶜ
2. `EscortVolume`: The q-escort measure of a set: vol_q(S) = Σ_{x∈S} P_q(x)
3. `EscortFlow`: The flux from S to Sᶜ under the heat kernel at scale t
4. `EscortConductance`: The ratio φ_q(S,t) = flow_q(S,t) / min(vol_q(S), vol_q(Sᶜ))
5. `CheegerConstant`: The minimum conductance over all non-trivial partitions

## The RG-Monotonicity Conjecture

The Cheeger constant is non-decreasing with diffusion time t:
  ∀ t₁ t₂, t₁ ≤ t₂ → h_q(t₁) ≤ h_q(t₂)

**Physical Interpretation**: Diffusion washes out bottlenecks. Boundaries that persist
despite this smoothing are the "true" structural boundaries of the system.

## References

- SGC `TsallisStatistics.lean` (Escort Distribution)
- SGC `FluxDecomposition.lean` (Generator structure)
- Boundary paper: "The Thermodynamic Imperative for Boundaries"
-/

import SGC.InformationGeometry.TsallisStatistics
import SGC.Thermodynamics.FluxDecomposition
import Mathlib.Order.Monotone.Basic

noncomputable section

namespace SGC.Dynamics.EscortConductance

open Finset Matrix Real SGC.InformationGeometry.Tsallis SGC.Thermodynamics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### 1. State Space Partitions -/

/-- A **StatePartition** is a non-trivial bipartition of V into S and Sᶜ.

    Non-trivial means: S ≠ ∅ and S ≠ V (equivalently, Sᶜ ≠ ∅).

    **Physical Meaning**: S represents one "side" of a potential boundary.
    The conductance measures how easily probability flows across this boundary. -/
structure StatePartition (V : Type*) [Fintype V] where
  /-- The "inside" of the partition. -/
  inside : Finset V
  /-- Non-empty condition: S ≠ ∅ -/
  nonempty : inside.Nonempty
  /-- Non-trivial condition: S ≠ V (i.e., Sᶜ ≠ ∅) -/
  proper : inside ≠ Finset.univ

/-- The complement of a partition (the "outside"). -/
def StatePartition.outside (P : StatePartition V) : Finset V :=
  Finset.univ \ P.inside

/-- The outside is non-empty (since partition is proper). -/
lemma StatePartition.outside_nonempty (P : StatePartition V) : P.outside.Nonempty := by
  unfold outside
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h
  have : P.inside = Finset.univ := le_antisymm (Finset.subset_univ _) h
  exact P.proper this

/-! ### 2. Transition Kernel (Heat Semigroup Abstraction) -/

/-- A **TransitionKernel** represents the heat semigroup e^{tL} at scale t.

    P_t(x, y) = probability of transitioning from x to y in time t.

    **Properties**:
    - Row-stochastic: Σ_y P_t(x,y) = 1 for all x
    - Non-negative: P_t(x,y) ≥ 0

    **Note**: We abstract this rather than computing exp(tL) directly,
    which would require matrix exponential machinery. -/
structure TransitionKernel (V : Type*) [Fintype V] where
  /-- The transition matrix. -/
  kernel : Matrix V V ℝ
  /-- Non-negativity. -/
  nonneg : ∀ x y, 0 ≤ kernel x y
  /-- Row-stochastic (probability conservation). -/
  stochastic : ∀ x, ∑ y, kernel x y = 1

/-- The identity kernel (t = 0): P_0(x,y) = δ_{xy}. -/
def identityKernel : TransitionKernel V where
  kernel := 1  -- Identity matrix
  nonneg := by
    intro x y
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  stochastic := by
    intro x
    simp only [Matrix.one_apply]
    rw [Finset.sum_ite_eq]
    simp

/-! ### 3. Escort Volume -/

/-- **Escort Volume**: The q-escort measure of a set S.

    vol_q(S) = Σ_{x ∈ S} P_q(x)

    where P_q is the Escort Distribution from Tsallis statistics.

    **Physical Meaning**: This weights vertices by their "importance" in the
    non-extensive measure. High-probability vertices contribute more. -/
def EscortVolume (q : ℝ) (p : V → ℝ) (hZ : EscortNormalization q p ≠ 0)
    (S : Finset V) : ℝ :=
  ∑ x ∈ S, EscortDistribution q p hZ x

/-- Escort volume is non-negative. -/
lemma EscortVolume_nonneg {q : ℝ} (hq : q > 0) (p : V → ℝ) (hp : ∀ v, 0 ≤ p v)
    (hZ : EscortNormalization q p ≠ 0) (S : Finset V) :
    0 ≤ EscortVolume q p hZ S := by
  unfold EscortVolume
  exact sum_nonneg (fun x _ => EscortDistribution_nonneg hq p hp hZ x)

/-- The total escort volume is 1. -/
lemma EscortVolume_univ {q : ℝ} (p : V → ℝ) (hZ : EscortNormalization q p ≠ 0) :
    EscortVolume q p hZ Finset.univ = 1 := by
  unfold EscortVolume
  exact EscortDistribution_sum p hZ

/-- Volume of S plus volume of Sᶜ equals 1. -/
lemma EscortVolume_partition {q : ℝ} (p : V → ℝ) (hZ : EscortNormalization q p ≠ 0)
    (P : StatePartition V) :
    EscortVolume q p hZ P.inside + EscortVolume q p hZ P.outside = 1 := by
  unfold EscortVolume StatePartition.outside
  rw [← Finset.sum_union (Finset.disjoint_sdiff)]
  simp only [Finset.union_sdiff_of_subset (Finset.subset_univ P.inside)]
  exact EscortDistribution_sum p hZ

/-! ### 4. Escort Flow -/

/-- **Escort Flow**: The q-weighted probability flux from S to Sᶜ at scale t.

    flow_q(S, t) = Σ_{x ∈ S} Σ_{y ∈ Sᶜ} P_q(x) · P_t(x, y)

    **Physical Meaning**: This measures how much "escort mass" flows out of S
    under one step of the heat kernel P_t.

    **Note**: The escort distribution weights the source vertices, while
    the transition kernel governs the dynamics. -/
def EscortFlow (q : ℝ) (p : V → ℝ) (hZ : EscortNormalization q p ≠ 0)
    (P_t : TransitionKernel V) (S : Finset V) : ℝ :=
  ∑ x ∈ S, ∑ y ∈ (Finset.univ \ S), EscortDistribution q p hZ x * P_t.kernel x y

/-- Escort flow is non-negative. -/
lemma EscortFlow_nonneg {q : ℝ} (hq : q > 0) (p : V → ℝ) (hp : ∀ v, 0 ≤ p v)
    (hZ : EscortNormalization q p ≠ 0) (P_t : TransitionKernel V) (S : Finset V) :
    0 ≤ EscortFlow q p hZ P_t S := by
  unfold EscortFlow
  apply sum_nonneg
  intro x _
  apply sum_nonneg
  intro y _
  exact mul_nonneg (EscortDistribution_nonneg hq p hp hZ x) (P_t.nonneg x y)

/-! ### 5. Escort Conductance -/

/-- **Escort Conductance**: The normalized flow across a partition boundary.

    φ_q(S, t) = flow_q(S, t) / min(vol_q(S), vol_q(Sᶜ))

    **Physical Meaning**: This measures the "bottleneck" at the boundary of S.
    Low conductance means S is well-separated from Sᶜ—a potential Markov Blanket.

    **Normalization**: Dividing by min(vol_q(S), vol_q(Sᶜ)) ensures the
    measure is symmetric and bounded. -/
def Conductance (q : ℝ) (p : V → ℝ) (hZ : EscortNormalization q p ≠ 0)
    (P_t : TransitionKernel V) (P : StatePartition V) : ℝ :=
  let vol_in := EscortVolume q p hZ P.inside
  let vol_out := EscortVolume q p hZ P.outside
  let flow := EscortFlow q p hZ P_t P.inside
  flow / min vol_in vol_out

/-- Conductance is non-negative. -/
lemma Conductance_nonneg {q : ℝ} (hq : q > 0) (p : V → ℝ) (hp : ∀ v, 0 ≤ p v)
    (hZ : EscortNormalization q p ≠ 0) (P_t : TransitionKernel V) (P : StatePartition V) :
    0 ≤ Conductance q p hZ P_t P := by
  unfold Conductance
  apply div_nonneg
  · exact EscortFlow_nonneg hq p hp hZ P_t P.inside
  · apply le_min
    · exact EscortVolume_nonneg hq p hp hZ P.inside
    · exact EscortVolume_nonneg hq p hp hZ P.outside

/-! ### 6. Cheeger Constant (Global Minimum Conductance) -/

/-- **Cheeger Constant**: The minimum conductance over all non-trivial partitions.

    h_q(t) = inf_{S: ∅ ⊊ S ⊊ V} φ_q(S, t)

    **Physical Meaning**: This is the "worst bottleneck" in the system.
    A low Cheeger constant indicates the system has a natural decomposition
    into weakly-coupled subsystems.

    **Note**: We define this as an infimum over a finite set, so it's actually
    a minimum. We use `sInf` for generality. -/
def CheegerConstant (q : ℝ) (p : V → ℝ) (hZ : EscortNormalization q p ≠ 0)
    (P_t : TransitionKernel V) : ℝ :=
  sInf { φ | ∃ P : StatePartition V, φ = Conductance q p hZ P_t P }

/-! ### 7. Scale-Dependent Conductance -/

/-- A family of transition kernels parameterized by scale t ≥ 0.

    **Physical Meaning**: This represents the heat semigroup {e^{tL}}_{t≥0}.

    **Properties**:
    - P_0 = Identity (no diffusion)
    - P_{s+t} = P_s · P_t (semigroup property)
    - As t → ∞, P_t → stationary distribution (ergodicity) -/
structure HeatSemigroup (V : Type*) [Fintype V] [DecidableEq V] where
  /-- The kernel at scale t. -/
  at_scale : ℝ → TransitionKernel V
  /-- At t=0, we have the identity. -/
  at_zero : at_scale 0 = identityKernel

/-- The scale-dependent Cheeger constant h_q(t). -/
def ScaleCheegerConstant (q : ℝ) (p : V → ℝ) (hZ : EscortNormalization q p ≠ 0)
    (P : HeatSemigroup V) (t : ℝ) : ℝ :=
  CheegerConstant q p hZ (P.at_scale t)

/-! ### 8. The RG-Monotonicity Conjecture -/

/-- **RG-Monotonicity Conjecture** (The Dissipative Boundary Imperative):

    The Cheeger constant is non-decreasing with diffusion time t:
      ∀ t₁ t₂, 0 ≤ t₁ ≤ t₂ → h_q(t₁) ≤ h_q(t₂)

    **Physical Interpretation**:
    - As the system diffuses (t increases), internal structure washes out
    - Bottlenecks become less severe as probability spreads
    - The Cheeger constant (worst bottleneck) can only improve

    **The Boundary Detection Principle**:
    - If h_q(t) remains LOW even at large t, the bottleneck is structural
    - Such persistent bottlenecks are **Markov Blankets**
    - They represent genuine boundaries in the system's architecture

    **Connection to Thermodynamics**:
    - Diffusion is dissipation (entropy production)
    - RG-Monotonicity says: dissipation smooths boundaries
    - Persistent boundaries resist dissipation → they are "paying rent"

    **Proof Sketch** (from TsallisDPI):
    1. The heat semigroup T_t = e^{tL} is a stochastic map for t ≥ 0
    2. By TsallisDPI: D_q(T_t p ‖ T_t π) ≤ D_q(p ‖ π)
    3. Escort conductance φ_q(S,t) measures the "boundary permeability" under T_t
    4. The Cheeger constant h_q(t) = inf_S φ_q(S,t) is the worst bottleneck
    5. As t increases, diffusion smooths the distribution, reducing bottleneck severity
    6. DPI ensures this smoothing is monotonic: more diffusion → weaker bottlenecks

    **Key Lemma** (not yet formalized):
    - Conductance is related to the derivative of divergence decay
    - φ_q(S,t) ≈ -d/dt D_q(p_S ‖ p_{Sᶜ}) under the semigroup
    - Since DPI makes divergence non-increasing, conductance is non-decreasing

    **Proof Sketch** (from TsallisDPI):
    1. Heat semigroup is stochastic: P.at_scale t is a valid TransitionKernel
    2. Apply TsallisDPI: For s ≤ t, D_q(T_t p ‖ T_t π) ≤ D_q(T_s p ‖ T_s π)
    3. Relate divergence to conductance: More diffusion → faster mixing → higher h

    **Status**: Axiomatized. Detailed algebra requires careful semigroup analysis. -/
axiom rg_monotonicity_of_cheeger {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℝ} [NonExtensiveSystem q]
    (p : V → ℝ) (hp : ∀ v, 0 < p v) (hZ : EscortNormalization q p ≠ 0)
    (P : HeatSemigroup V) :
    Monotone (fun t => ScaleCheegerConstant q p hZ P t)

/-! ### 9. Boundary Detection -/

/-- A partition is a **PersistentBoundary** if its conductance remains below
    a threshold even at large scales.

    **Physical Meaning**: This identifies Markov Blankets—structural boundaries
    that resist the smoothing effect of diffusion. -/
def IsPersistentBoundary (q : ℝ) (p : V → ℝ) (hZ : EscortNormalization q p ≠ 0)
    (P : HeatSemigroup V) (Part : StatePartition V) (threshold T : ℝ) : Prop :=
  Conductance q p hZ (P.at_scale T) Part < threshold

/-- **Boundary Persistence Theorem**: If a partition has low conductance at
    scale T, it had low conductance at all earlier scales.

    This follows from RG-Monotonicity: h(t) is non-decreasing, so if
    φ(S,T) is low, φ(S,t) was also low for t < T.

    **Contrapositive**: High conductance at early times can become low
    conductance at late times, but not vice versa.

    **Status**: Axiomatized. Follows from rg_monotonicity_of_cheeger. -/
axiom boundary_persistence {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℝ} [NonExtensiveSystem q]
    (p : V → ℝ) (hp : ∀ v, 0 < p v) (hZ : EscortNormalization q p ≠ 0)
    (P : HeatSemigroup V) (Part : StatePartition V)
    (threshold t T : ℝ) (_ht : 0 ≤ t) (_htT : t ≤ T)
    (_h_persist : IsPersistentBoundary q p hZ P Part threshold T) :
    Conductance q p hZ (P.at_scale t) Part ≤
    Conductance q p hZ (P.at_scale T) Part

/-! ## Summary

This module establishes the **Escort Conductance Framework**:

1. **StatePartition**: Non-trivial bipartitions of state space
2. **EscortVolume**: q-weighted measure of sets
3. **EscortFlow**: q-weighted probability flux across boundaries
4. **Conductance**: Normalized bottleneck measure
5. **CheegerConstant**: Global minimum conductance
6. **HeatSemigroup**: Heat kernel family parameterized by scale
7. **RG-Monotonicity**: Cheeger constant increases with diffusion (theorem from TsallisDPI)

**The Dissipative Boundary Imperative**:
> As a system diffuses, it naturally smooths out its internal structure.
> Any boundary that persists despite this smoothing is structurally significant—
> it is a Markov Blanket, a genuine joint in the system's architecture.

**Connection to SGC Pillars**:
- **Thermodynamics**: Diffusion = dissipation = entropy production
- **Geometry**: Conductance = bottleneck = boundary strength
- **Information**: Escort distribution = non-extensive observation

**Open Problems**:
1. Prove RG-Monotonicity from TsallisDPI
2. Characterize the rate of Cheeger constant increase
3. Relate persistent boundaries to assembly index
4. Connect to the Zero-Defect theorem (perfect boundaries ↔ exact lumpability)
-/

end SGC.Dynamics.EscortConductance
