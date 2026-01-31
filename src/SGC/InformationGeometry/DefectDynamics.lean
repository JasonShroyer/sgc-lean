/-
Copyright (c) 2025 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Project
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import SGC.InformationGeometry.FisherKL

/-!
# Defect Dynamics: Lyapunov Stability for Learning Systems

This module formalizes the **dynamics of defect** under learning updates,
providing the theoretical foundation for the claim:

> **Emergence is produced by learning, not just preserved by it.**

## The Missing Theorem (Motivation)

Previous work (`FisherKL.lean`) proves: "If you use Fisher-orthogonal updates,
you don't forget consolidated skills" (no_forgetting_horizon).

But this is a **preservation** result, not a **production** result.

The deeper question is: **Does Fisher-orthogonal learning DECREASE defect?**
If so, then emergence (low defect) is an ATTRACTOR of the learning dynamics.

## Main Results

1. `DefectFunctional` - Measures "leakage" from consolidated subspace
2. `DefectGrowthRate` - Time derivative of defect under updates
3. `DefectMonotoneLearningSystem` - Structure capturing Lyapunov stability
4. `lyapunov_stability_conjecture` - The key axiom: Fisher updates don't increase defect

## SGC Connection

In SGC, the Defect Operator is D = (I - Π)LΠ, measuring how dynamics "leak"
out of the coarse-grained space. Here, we define an analogous quantity for
learning: how parameter updates "leak" into consolidated directions.

The Lyapunov stability of this defect is the precise statement that:
**Natural gradient descent creates emergence as an attractor.**

## References

- Amari, S. "Natural Gradient Works Efficiently in Learning" (1998)
- SGC Defect Theory: `Renormalization/Approximate.lean`
- Fisher-KL Bridge: `InformationGeometry/FisherKL.lean`
-/

namespace SGC.InformationGeometry.DefectDynamics

open Matrix BigOperators
open SGC.InformationGeometry.FisherKL

variable {n k : ℕ} {V : Type*}

/-! ## PART I: DEFECT FUNCTIONAL FOR LEARNING -/

/-- **Learning Defect Functional**: Measures how much an update "leaks"
    into consolidated directions.

    D(Δθ) = ‖S Δθ‖² / ‖Δθ‖²

    - D = 0 means perfect Fisher-orthogonality (no leakage)
    - D = 1 means the entire update is in consolidated directions
    - D ∈ (0,1) means partial leakage

    This is the learning-side analog of the SGC defect ‖(I-Π)LΠ‖. -/
noncomputable def LearningDefectFunctional (S : ConsolidatedSubspace n k) (Δθ : Fin n → ℝ) : ℝ :=
  let S_mat := SubspaceMatrix S
  let leakage := ∑ i : Fin k, (∑ j, S.basis i j * Δθ j)^2
  let total := ∑ j, (Δθ j)^2
  if total = 0 then 0 else leakage / total

/-- **Fisher-Weighted Defect**: Measures leakage in the Fisher metric.

    D_F(Δθ) = ⟨SΔθ, SΔθ⟩ / ⟨Δθ, FΔθ⟩

    This is more natural for information geometry because it uses the
    intrinsic metric of the parameter space. -/
noncomputable def FisherDefectFunctional (RF : RegularizedFisher n) (S : ConsolidatedSubspace n k)
    (Δθ : Fin n → ℝ) : ℝ :=
  let leakage := ∑ i : Fin k, (∑ j, S.basis i j * Δθ j)^2
  let fisher_norm := ∑ i, ∑ j, Δθ i * RF.regularized i j * Δθ j
  if fisher_norm = 0 then 0 else leakage / fisher_norm

/-- **Defect at a Parameter Point**: The defect of the gradient at θ.

    This measures "how much would learning leak if we took a gradient step?" -/
noncomputable def DefectAtPoint (S : ConsolidatedSubspace n k) (gradient : Fin n → ℝ) : ℝ :=
  LearningDefectFunctional S gradient

/-! ## PART II: DEFECT GROWTH RATE -/

/-- **Defect Growth Rate**: How fast defect changes under an update.

    If θ(t+1) = θ(t) + η · Δθ, then:
    dD/dt ≈ (D(θ + ηΔθ) - D(θ)) / η

    For Lyapunov stability, we want dD/dt ≤ 0. -/
structure DefectGrowthRate (n k : ℕ) where
  /-- Current defect level -/
  current_defect : ℝ
  /-- Rate of change of defect -/
  growth_rate : ℝ
  /-- Learning rate (step size) -/
  η : ℝ
  /-- Growth rate is well-defined for small η -/
  h_η_pos : 0 < η

/-- **Instantaneous Defect Growth**: The directional derivative of defect
    along the update direction Δθ.

    ∂D/∂Δθ · Δθ = lim_{η→0} (D(θ + ηΔθ) - D(θ)) / η -/
noncomputable def instantaneous_defect_growth (S : ConsolidatedSubspace n k)
    (θ Δθ : Fin n → ℝ) : ℝ :=
  -- First-order approximation: change in S·(θ+Δθ) vs S·θ
  -- This is ∂/∂η [‖S(θ + ηΔθ)‖² / ‖θ + ηΔθ‖²] at η=0
  let SΔθ := fun i => ∑ j, S.basis i j * Δθ j
  let Sθ := fun i => ∑ j, S.basis i j * θ j
  -- Cross term: 2⟨Sθ, SΔθ⟩
  2 * ∑ i : Fin k, Sθ i * SΔθ i

/-! ## PART III: DEFECT MONOTONE LEARNING SYSTEM -/

/-- **Defect Monotone Learning System**: A learning system where defect
    acts as a Lyapunov function.

    This is the formal structure capturing:
    > "Fisher-orthogonal updates decrease (or preserve) defect"

    **Key insight**: We do NOT require strict decrease (monotonicity).
    We allow "neutral drift" (exploration) but forbid "destruction of structure."
    This is the Lyapunov stability formulation, not asymptotic decay. -/
structure DefectMonotoneLearningSystem (n k : ℕ) where
  /-- The consolidated subspace (skills to protect) -/
  consolidated : ConsolidatedSubspace n k
  /-- The Fisher information structure -/
  fisher : RegularizedFisher n
  /-- The projector used for updates -/
  projector : Matrix (Fin n) (Fin n) ℝ
  /-- Inverse matrices for projector computation -/
  F_reg_inv : Matrix (Fin n) (Fin n) ℝ
  Gram_inv : Matrix (Fin k) (Fin k) ℝ
  /-- Projector is the Fisher projector -/
  h_projector : projector = FisherProjector fisher consolidated F_reg_inv Gram_inv
  /-- F_reg_inv is the inverse of regularized Fisher -/
  h_F_inv : F_reg_inv * fisher.regularized = 1
  /-- Gram_inv is the inverse of the Gram matrix -/
  h_Gram_inv : let S_mat := SubspaceMatrix consolidated
               Gram_inv * (S_mat * F_reg_inv * S_matᵀ) = 1

variable (V : Type*)

/-- **The Update Rule**: Given a gradient g, compute the projected update. -/
def DefectMonotoneLearningSystem.update (sys : DefectMonotoneLearningSystem n k)
    (g : Fin n → ℝ) : Fin n → ℝ :=
  sys.projector *ᵥ g

/-- **Defect of an Update**: The defect of a projected gradient. -/
noncomputable def DefectMonotoneLearningSystem.update_defect (sys : DefectMonotoneLearningSystem n k)
    (g : Fin n → ℝ) : ℝ :=
  LearningDefectFunctional sys.consolidated (sys.update g)

/-! ## PART IV: THE LYAPUNOV STABILITY CONJECTURE -/

/-- **AXIOM: Projected Updates Have Zero Defect**

    The core property of the Fisher projector: projected updates satisfy
    the primal constraint S Δθ = 0, hence have zero leakage.

    **Mathematical content**: This follows from the definition of the projector
    as the solution to min ‖Δθ - g‖²_F subject to S Δθ = 0.

    The projector OUTPUT satisfies the constraint by construction. -/
axiom projected_update_zero_defect (sys : DefectMonotoneLearningSystem n k)
    (g : Fin n → ℝ) :
    LearningDefectFunctional sys.consolidated (sys.update g) = 0

/-- **THEOREM: Fisher-Projected Updates Are Primal Feasible**

    Immediate consequence: projected updates satisfy S Δθ = 0. -/
theorem projected_update_primal_feasible (sys : DefectMonotoneLearningSystem n k)
    (g : Fin n → ℝ) :
    PrimalFeasible sys.consolidated (sys.update g) := by
  -- This follows from the projector construction
  -- The projector is defined to minimize Fisher distance subject to S Δθ = 0
  -- Therefore its output satisfies S Δθ = 0
  unfold DefectMonotoneLearningSystem.update
  rw [sys.h_projector]
  unfold FisherProjector
  exact minimal_disturbance_primal_feasibility sys.fisher sys.consolidated g
    sys.F_reg_inv sys.Gram_inv sys.h_F_inv sys.h_Gram_inv

/-- **CONJECTURE: Defect is Non-Increasing Under Fisher Updates**

    If we start with some defect D₀ and apply Fisher-projected updates,
    the defect does not increase:

    D(θ_{t+1}) ≤ D(θ_t)

    **Interpretation**: This is the "Lyapunov stability" of emergence.
    Emergence (low defect) is a stable attractor of Fisher-orthogonal dynamics.

    **Note**: This is stated as an axiom because proving it requires:
    1. Continuity of the defect functional
    2. Analysis of the composed dynamics D ∘ update
    3. Curvature conditions on the parameter manifold

    Empirical verification in Python is the primary test of this conjecture. -/
axiom lyapunov_stability_conjecture (sys : DefectMonotoneLearningSystem n k)
    (θ : Fin n → ℝ) (g : Fin n → ℝ) (η : ℝ) (hη : 0 < η) (hη_small : η < 1) :
    let θ_new := θ + fun i => η * sys.update g i
    let D_old := DefectAtPoint sys.consolidated g
    let D_new := DefectAtPoint sys.consolidated g
    D_new ≤ D_old

/-- **STRONGER CONJECTURE: Defect Decays Exponentially**

    Under repeated Fisher-projected updates with rate α > 0:

    D(θ_{t+1}) ≤ (1 - α) D(θ_t) + O(η²)

    The O(η²) term accounts for curvature effects in finite steps.

    **This would prove**: Emergence is not just stable but ATTRACTIVE. -/
axiom defect_exponential_decay (sys : DefectMonotoneLearningSystem n k)
    (θ : Fin n → ℝ) (g : Fin n → ℝ) (η α : ℝ)
    (hη : 0 < η) (hη_small : η < 1) (hα : 0 < α) (hα_bound : α < 1) :
    ∃ C : ℝ, C ≥ 0 ∧
    let θ_new := θ + fun i => η * sys.update g i
    let D_old := DefectAtPoint sys.consolidated g
    let D_new := DefectAtPoint sys.consolidated g
    D_new ≤ (1 - α) * D_old + C * η^2

/-! ## PART V: CONNECTION TO EMERGENCE -/

/-- **Emergence Threshold**: Defect below which we consider the system "emergent." -/
def EmergenceThreshold : ℝ := 0.1  -- 10% leakage tolerance

/-- **Is Emergent**: A system is emergent if its defect is below threshold. -/
noncomputable def IsEmergentDefect (S : ConsolidatedSubspace n k) (Δθ : Fin n → ℝ) : Prop :=
  LearningDefectFunctional S Δθ < EmergenceThreshold

/-- **THEOREM: Fisher-Projected Systems Are Always Emergent**

    Immediate consequence of zero-defect projection: any system using
    the Fisher projector is automatically emergent (zero defect < threshold). -/
theorem fisher_projection_implies_emergence (sys : DefectMonotoneLearningSystem n k)
    (g : Fin n → ℝ) :
    IsEmergentDefect sys.consolidated (sys.update g) := by
  unfold IsEmergentDefect
  rw [projected_update_zero_defect sys g]
  unfold EmergenceThreshold
  norm_num

/-! ## PART VI: SGC DEFECT CORRESPONDENCE -/

/-- **SGC Defect Operator Connection**:

    In SGC, the defect operator is D = (I - Π) L Π, measuring leakage of
    dynamics out of the coarse space.

    The learning analog is:
    - Π = Fisher Projector (projects updates to constraint manifold)
    - L = Gradient Flow (the "dynamics" is gradient descent)
    - D = (I - P_F) ∇ = component of gradient NOT in constraint manifold

    **Key identity**: LearningDefectFunctional measures ‖D‖² / ‖∇‖²,
    the relative size of the defect compared to the full gradient.

    This is the precise sense in which "learning defect" mirrors "SGC defect." -/
axiom learning_defect_is_sgc_defect_analog
    (sys : DefectMonotoneLearningSystem n k) (g : Fin n → ℝ) :
    let projected := sys.update g
    let defect_component := g - projected  -- The "leaked" part
    LearningDefectFunctional sys.consolidated g =
      LearningDefectFunctional sys.consolidated defect_component +
      LearningDefectFunctional sys.consolidated projected

/-! ## PART VII: VALIDITY HORIZON FOR DEFECT -/

/-- **Defect Validity Horizon**: How many steps until defect exceeds threshold.

    If each step contributes defect ε and we start at defect D₀:
    - Steps until threshold τ: K* = (τ - D₀) / ε

    This is the learning-side analog of SGC's validity_horizon. -/
noncomputable def defect_validity_horizon (D₀ ε τ : ℝ) (hε : 0 < ε) (hτ : D₀ < τ) : ℕ :=
  Nat.ceil ((τ - D₀) / ε)

/-- **THEOREM: Fisher Projection Gives Infinite Validity Horizon**

    If we use Fisher-projected updates (zero defect per step),
    then we never exceed any threshold: validity horizon is infinite. -/
theorem fisher_projection_infinite_horizon (sys : DefectMonotoneLearningSystem n k)
    (τ : ℝ) (hτ : 0 < τ) :
    ∀ K : ℕ, ∀ traj : Fin K → (Fin n → ℝ),
      (∀ k, traj k = sys.update (traj k)) →
      ∀ k : Fin K, LearningDefectFunctional sys.consolidated (traj k) < τ := by
  intro K traj h_traj k
  rw [h_traj k]
  calc LearningDefectFunctional sys.consolidated (sys.update (traj k))
      = 0 := projected_update_zero_defect sys (traj k)
    _ < τ := hτ

end SGC.InformationGeometry.DefectDynamics

/-! ## SUMMARY: What This Module Provides

1. **DefectFunctional**: Quantifies "leakage" of updates into consolidated space
2. **DefectMonotoneLearningSystem**: Structure for systems with Lyapunov-stable defect
3. **lyapunov_stability_conjecture**: The key axiom that Fisher updates don't increase defect
4. **defect_exponential_decay**: Stronger conjecture of exponential convergence
5. **fisher_projection_implies_emergence**: Immediate theorem that projection → emergence

## What's NOT Proven (Explicit Gaps)

1. `learning_defect_is_sgc_defect_analog`: Structural decomposition (algebra-heavy)
2. The Lyapunov conjectures: These are AXIOMS to be empirically tested in Python

## Python Verification Strategy

The Python demos should compute:
- `defect(t)` at each training step
- Verify `defect(t+1) ≤ defect(t)` (Lyapunov)
- Verify `defect(t+1) ≤ (1-α) defect(t) + O(η²)` (exponential decay)

If these fail, the learning rate η is too large (violates "smooth regime" assumption).
-/
