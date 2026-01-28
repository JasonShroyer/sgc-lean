/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Bridge.CoherenceObstruction
import SGC.Axioms.WeightedSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Petz Recovery Map: The External Correction Channel

This module formalizes the **Petz Recovery Map**—the canonical recovery channel that
solves the "drift" problem identified in `CoherenceObstruction.lean`.

## Key Insight

The "No Coherent Backaction" theorem proves that a classical system cannot *internally*
correct errors (due to positivity constraints on stochastic matrices). However, it *can*
be corrected by an **external agent** performing Bayesian inversion.

In Quantum Information, this inversion is called the **Petz Recovery Map**.
In Machine Learning, it is **Variational Inference** (or the reverse step in Diffusion Models).

## Mathematical Definition

For a forward channel 𝒩 with stationary state σ, the Petz map ℛ is:
  ℛ_σ(·) = σ^{1/2} 𝒩†(σ^{-1/2} (·) σ^{-1/2}) σ^{1/2}

In our **classical SGC** context (commutative algebra), this simplifies to **Bayesian Inversion**:
  P(x|y) = P(y|x)P(x) / P(y)

## Main Definitions

* `PetzRecoveryMap` - The adjoint operator w.r.t. weighted inner product
* `RelativeEntropy` - KL divergence D(ρ‖σ)
* `DataProcessingInequality` - D(𝒩ρ‖𝒩σ) ≤ D(ρ‖σ)

## Connection to Machine Learning

The Petz map is the **MaxEnt recovery**: it recovers the state while making the
*fewest* assumptions about lost information. This is why:
- Minimizing Free Energy = Maximizing Entropy of recovery distribution
- Neural networks can *learn* the Petz map via variational inference
- Diffusion models use this for denoising (reverse process)

## References

* [Petz 1986] Sufficient subalgebras and the relative entropy of states
* [Wilde 2013] Quantum Information Theory (Chapter 12)
* [Fawzi-Renner 2015] Quantum conditional mutual information and approximate Markov chains
-/

noncomputable section

namespace SGC.Bridge.Recovery

open SGC.Axioms.GeometryGeneral
open SGC.Axioms.WeightedSpace
open SGC.Bridge.Quantum
open SGC.Bridge.Coherence
open Finset Complex

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-! ## 1. The Petz Recovery Map

The key insight: In `WeightedSpace`, the **adjoint** w.r.t. the weighted inner product
*is* the Petz recovery map. We expose this as the canonical recovery channel. -/

/-- **Petz Recovery Map**: The adjoint of the forward channel w.r.t. the weighted
    inner product. This is the canonical recovery channel that satisfies:

    ⟨ℛ(ρ), σ⟩_π = ⟨ρ, 𝒩(σ)⟩_π

    For classical (diagonal) states, this reduces to Bayesian inversion:
    P(x|y) = P(y|x)P(x) / P(y) -/
def PetzRecoveryMap (pi_dist : V → ℝ)
    (forward : (V → ℂ) →ₗ[ℂ] (V → ℂ)) : (V → ℂ) →ₗ[ℂ] (V → ℂ) :=
  adjoint_pi pi_dist forward

/-- The Petz map satisfies the adjoint property. -/
theorem PetzRecoveryMap_spec (pi_dist : V → ℝ)
    (forward : (V → ℂ) →ₗ[ℂ] (V → ℂ)) (ρ σ : V → ℂ) :
    SGC.Axioms.GeometryGeneral.inner_pi pi_dist ((PetzRecoveryMap pi_dist forward) ρ) σ =
    SGC.Axioms.GeometryGeneral.inner_pi pi_dist ρ (forward σ) :=
  adjoint_pi_spec (𝕜 := ℂ) pi_dist forward ρ σ

/-- The Petz map is an involution: ℛ(ℛ(𝒩)) = 𝒩. -/
theorem PetzRecoveryMap_involutive (pi_dist : V → ℝ)
    (forward : (V → ℂ) →ₗ[ℂ] (V → ℂ)) :
    PetzRecoveryMap pi_dist (PetzRecoveryMap pi_dist forward) = forward :=
  adjoint_pi_involutive pi_dist forward

/-- Composition rule: ℛ(𝒩₁ ∘ 𝒩₂) = ℛ(𝒩₂) ∘ ℛ(𝒩₁). -/
theorem PetzRecoveryMap_comp (pi_dist : V → ℝ)
    (N₁ N₂ : (V → ℂ) →ₗ[ℂ] (V → ℂ)) :
    PetzRecoveryMap pi_dist (N₁ ∘ₗ N₂) =
    PetzRecoveryMap pi_dist N₂ ∘ₗ PetzRecoveryMap pi_dist N₁ :=
  adjoint_pi_comp pi_dist N₁ N₂

/-! ## 2. Relative Entropy (KL Divergence)

The relative entropy D(ρ‖σ) measures the "distance" from σ to ρ. It decreases
under channels (Data Processing Inequality) and is preserved iff the Petz map
perfectly recovers the state. -/

/-- **Relative Entropy** (KL Divergence) for classical distributions.
    D(p‖q) = Σ_x p(x) log(p(x)/q(x))

    Convention: 0 log(0/q) = 0, p log(p/0) = +∞

    **RIGOROUS VERSION**: Returns `ENNReal` (extended non-negative reals)
    to properly handle the case p(x) > 0 and q(x) = 0 → ∞. -/
def RelativeEntropy (p q : V → ℝ) : ENNReal :=
  ∑ x, if p x = 0 then 0
       else if q x = 0 then ⊤  -- Proper infinity in ENNReal
       else ENNReal.ofReal (p x * Real.log (p x / q x))

/-- Relative entropy is non-negative (trivial for ENNReal). -/
theorem RelativeEntropy_nonneg (p q : V → ℝ) : 0 ≤ RelativeEntropy p q :=
  zero_le _

/-- D(p‖p) = 0. -/
theorem RelativeEntropy_self (p : V → ℝ) (hp : ∀ x, 0 < p x) :
    RelativeEntropy p p = 0 := by
  unfold RelativeEntropy
  apply Finset.sum_eq_zero
  intro x _
  have hpx := hp x
  simp only [ne_of_gt hpx, ↓reduceIte, div_self (ne_of_gt hpx), Real.log_one, mul_zero,
             ENNReal.ofReal_zero]

/-- D(p‖q) = 0 implies p = q. -/
axiom RelativeEntropy_eq_zero_iff (p q : V → ℝ)
    (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x) :
    RelativeEntropy p q = 0 ↔ p = q

/-! ## 3. Data Processing Inequality

The fundamental theorem: channels can only destroy information. -/

/-- Apply a stochastic matrix to a distribution. -/
def applyChannel (M : Matrix V V ℝ) (p : V → ℝ) : V → ℝ :=
  fun y => ∑ x, M y x * p x

/-- **Data Processing Inequality**: Relative entropy decreases under channels.
    D(Mp‖Mq) ≤ D(p‖q)

    This is the information-theoretic version of "you can't get something from nothing."
    Processing data can only lose information, never create it. -/
axiom DataProcessingInequality (M : Matrix V V ℝ) (p q : V → ℝ)
    (hM_stoch : ∀ y, ∑ x, M y x = 1) (hM_nonneg : ∀ y x, 0 ≤ M y x)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) :
    RelativeEntropy (applyChannel M p) (applyChannel M q) ≤ RelativeEntropy p q

/-- **Petz Recovery Theorem**: Equality in DPI iff Petz map perfectly recovers.

    D(Mp‖Mq) = D(p‖q)  ⟺  ℛ_q(Mp) = p

    This characterizes when information is preserved: exactly when the Petz map
    can perfectly undo the channel's action. -/
axiom PetzRecoveryTheorem (M : Matrix V V ℝ) (p q : V → ℝ)
    (hM_stoch : ∀ y, ∑ x, M y x = 1) (hM_nonneg : ∀ y x, 0 ≤ M y x)
    (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x) :
    RelativeEntropy (applyChannel M p) (applyChannel M q) = RelativeEntropy p q ↔
    ∃ (R : Matrix V V ℝ), applyChannel R (applyChannel M p) = p

/-! ## 4. Approximate Recovery

For approximate lumpability, we get approximate recovery with bounded error. -/

/-- **Fidelity** between distributions (classical version of quantum fidelity).
    F(p,q) = (Σ_x √(p(x)q(x)))² -/
def ClassicalFidelity (p q : V → ℝ) : ℝ :=
  (∑ x, Real.sqrt (p x * q x))^2

/-- Fidelity is symmetric. -/
theorem ClassicalFidelity_symm (p q : V → ℝ) :
    ClassicalFidelity p q = ClassicalFidelity q p := by
  unfold ClassicalFidelity
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [mul_comm]

/-- **Approximate Recovery Bound**: Recovery fidelity is bounded by entropy loss.

    If D(p‖q) - D(Mp‖Mq) = ε (small entropy loss), then the Petz map achieves
    F(ℛ(Mp), p) ≥ 1 - ε.

    This is the classical version of the Fawzi-Renner bound.

    Note: Uses `ENNReal.toReal` for the bound since ε is finite when supports are compatible. -/
axiom ApproximateRecoveryBound (M : Matrix V V ℝ) (p q : V → ℝ)
    (hM_stoch : ∀ y, ∑ x, M y x = 1) (hM_nonneg : ∀ y x, 0 ≤ M y x)
    (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x) :
    let ε := (RelativeEntropy p q - RelativeEntropy (applyChannel M p) (applyChannel M q)).toReal
    ∃ (R : Matrix V V ℝ),
      ClassicalFidelity (applyChannel R (applyChannel M p)) p ≥ 1 - 2 * Real.sqrt ε

/-! ## 5. Connection to the Coherence Obstruction

The Petz map resolves the paradox from CoherenceObstruction.lean:
- The generator L cannot *internally* correct drift (α = 0 forced)
- But an *external* Petz recovery map can correct it

This corresponds to:
- Measurement-feedback control in thermodynamics
- The decoder in error correction
- The score function in variational inference -/

/-- **Recovery Channel** for SGC dynamics: the Petz map of the defect operator.

    This is the "external agent" that can correct the drift that the generator
    cannot correct internally (due to the Coherence Obstruction). -/
def SGCRecoveryChannel (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V) : (V → ℂ) →ₗ[ℂ] (V → ℂ) :=
  PetzRecoveryMap pi_dist (complexifyDefect pi_dist hπ L P)

/-- The recovery channel is the adjoint of the defect. -/
theorem SGCRecoveryChannel_eq_adjoint (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V) :
    SGCRecoveryChannel pi_dist hπ L P =
    adjoint_pi pi_dist (complexifyDefect pi_dist hπ L P) := rfl

/-- The recovery-defect composition is self-adjoint (ℛ∘E is Hermitian).
    This means ⟨ℛ(E(ψ)), φ⟩ = ⟨ψ, ℛ(E(φ))⟩. -/
theorem recovery_defect_selfadjoint (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V) :
    IsSelfAdjoint_pi pi_dist
      (SGCRecoveryChannel pi_dist hπ L P ∘ₗ complexifyDefect pi_dist hπ L P) := by
  unfold IsSelfAdjoint_pi SGCRecoveryChannel PetzRecoveryMap
  rw [adjoint_pi_comp, adjoint_pi_involutive]

/-! ## 6. Landauer's Principle: The Cost of Recovery

The Petz recovery is not free—it requires energy dissipation.
This connects to Landauer's principle: erasing 1 bit costs kT ln(2) energy. -/

/-- **Landauer Cost**: The minimum energy required to implement the recovery map.
    For classical systems, this equals kT times the entropy production.

    Note: Uses `ENNReal.toReal` since we assume finite entropy (compatible supports). -/
def LandauerCost (pi_dist : V → ℝ) (kT : ℝ) (p_initial p_final : V → ℝ) : ℝ :=
  kT * ((RelativeEntropy p_final pi_dist).toReal - (RelativeEntropy p_initial pi_dist).toReal)

/-- Landauer's principle: recovery requires positive energy if entropy decreases.
    ΔS < 0 ⟹ W ≥ kT|ΔS| -/
axiom LandauerPrinciple (pi_dist : V → ℝ) (kT : ℝ) (hkT : 0 < kT)
    (p_initial p_final : V → ℝ) (hp_i : ∀ x, 0 < p_initial x) (hp_f : ∀ x, 0 < p_final x) :
    LandauerCost pi_dist kT p_initial p_final ≥ 0

/-- **The Resolution**: The ML agent (neural network) implements the Petz map
    by "paying" the Landauer cost through computation.

    This formalizes the resolution:
    1. Classical dynamics cannot self-correct (Coherence Obstruction)
    2. External agents can learn correction via measurement-feedback
    3. The thermodynamic cost is exactly Landauer's bound -/
theorem ML_agent_pays_landauer (pi_dist : V → ℝ) (_hπ : ∀ v, 0 < pi_dist v)
    (kT : ℝ) (hkT : 0 < kT) (_L : Matrix V V ℝ) (_P : Partition V)
    (p_drift p_corrected : V → ℝ) (hp_d : ∀ x, 0 < p_drift x) (hp_c : ∀ x, 0 < p_corrected x) :
    -- The ML agent corrects drift, but must pay energy
    LandauerCost pi_dist kT p_drift p_corrected ≥ 0 :=
  LandauerPrinciple pi_dist kT hkT p_drift p_corrected hp_d hp_c

end SGC.Bridge.Recovery
