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

## Main Results (revised 2026-06-10 hygiene pass)

1. `DefectFunctional` - Measures "leakage" from consolidated subspace
2. `DefectGrowthRate` - Time derivative of defect under updates
3. `DefectMonotoneLearningSystem` - Structure capturing Lyapunov stability
4. `projected_update_zero_defect` - THEOREM (was axiom): projected updates have
   zero leakage, via primal feasibility
5. `IsLyapunovStable` / `IsExponentiallyAttracting` - the honest VOCABULARY for
   the Lyapunov program (the former "conjecture axioms" were vacuous `X ≤ X`
   tautologies and were deleted; see Part IV)

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

/-! ## PART IV: ZERO DEFECT IS A THEOREM; THE LYAPUNOV PROGRAM IS VOCABULARY -/

/-- **THEOREM: Fisher-Projected Updates Are Primal Feasible**

    Projected updates satisfy S Δθ = 0, by the projector construction. -/
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

/-- **THEOREM (un-axiomatized 2026-06-10): Projected Updates Have Zero Defect**

    The core property of the Fisher projector: projected updates satisfy the
    primal constraint S Δθ = 0, hence every leakage summand vanishes and the
    defect functional is zero in both branches of its definition.

    Formerly an AXIOM; the content was always a consequence of
    `projected_update_primal_feasible`, which is proven. Zero new assumptions. -/
theorem projected_update_zero_defect (sys : DefectMonotoneLearningSystem n k)
    (g : Fin n → ℝ) :
    LearningDefectFunctional sys.consolidated (sys.update g) = 0 := by
  have hpf : ∀ i : Fin k, ∑ j, sys.consolidated.basis i j * sys.update g j = 0 :=
    projected_update_primal_feasible sys g
  simp only [LearningDefectFunctional]
  have hleak : ∑ i : Fin k, (∑ j, sys.consolidated.basis i j * sys.update g j) ^ 2 = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hpf i]; norm_num
  rw [hleak]
  split_ifs <;> simp

/-! ### The Lyapunov program: honest vocabulary, no vacuous axioms

**REFUTATION-BY-INSPECTION (kernel hygiene finding, 2026-06-10)**: this file
previously carried two "conjecture" AXIOMS (`lyapunov_stability_conjecture`,
`defect_exponential_decay`) whose bodies bound `D_old` and `D_new` to the SAME
expression `DefectAtPoint sys.consolidated g` — the `θ_new` binding was unused.
Both axioms asserted `X ≤ X` (and `X ≤ (1-α)·X + Cη²` with a free C ≥ 0): pure
tautologies wearing a conjecture's name. They carried ZERO mathematical content
and have been DELETED. (Fifth and sixth defective formal statements caught this
week — same disease family: symbols not bound to the intended referents.)

The REAL Lyapunov statement requires θ-dependence of the gradient — a gradient
FIELD ∇F : θ ↦ ∇F(θ) — which the previous vocabulary lacked entirely
(`DefectAtPoint` takes a gradient, not a parameter point). The definitions
below supply that vocabulary. We deliberately do NOT restate the conjecture as
an unconstrained universal over all gradient fields: that statement is FALSE
(an adversarial field can steer the new gradient anywhere) — it would be the
week's disease, instance seven. The truth requires coupling ∇F to an actual
loss with curvature/smoothness bounds. Until that coupling is formalizable,
the conjecture lives where it honestly belongs: as the named PROPERTY
`IsLyapunovStable sys ∇F` to be (a) verified empirically in Python per
training run, and (b) eventually PROVEN for specific loss classes (Layer-3
Lyapunov program — the open dynamics arrows of the master cascade). -/

/-- A **gradient field**: the gradient of a loss as a function of the current
    parameter point. This is the θ-dependence the Lyapunov program needs. -/
structure GradientField (n : ℕ) where
  /-- θ ↦ ∇F(θ) -/
  grad : (Fin n → ℝ) → (Fin n → ℝ)

/-- One step of Fisher-projected natural-gradient descent on a gradient field. -/
def lyapunovStep (sys : DefectMonotoneLearningSystem n k) (gfield : GradientField n)
    (η : ℝ) (θ : Fin n → ℝ) : Fin n → ℝ :=
  fun i => θ i + η * sys.update (gfield.grad θ) i

/-- **The Lyapunov stability PROPERTY** (not asserted; to be proven per loss
    class or verified empirically): along Fisher-projected updates, the defect
    of the gradient field does not increase. -/
def IsLyapunovStable (sys : DefectMonotoneLearningSystem n k)
    (gfield : GradientField n) : Prop :=
  ∀ (θ : Fin n → ℝ) (η : ℝ), 0 < η → η < 1 →
    DefectAtPoint sys.consolidated (gfield.grad (lyapunovStep sys gfield η θ))
      ≤ DefectAtPoint sys.consolidated (gfield.grad θ)

/-- **The exponential attraction PROPERTY** (strictly stronger than stability):
    defect contracts at rate α up to O(η²) curvature error. -/
def IsExponentiallyAttracting (sys : DefectMonotoneLearningSystem n k)
    (gfield : GradientField n) (α C : ℝ) : Prop :=
  ∀ (θ : Fin n → ℝ) (η : ℝ), 0 < η → η < 1 →
    DefectAtPoint sys.consolidated (gfield.grad (lyapunovStep sys gfield η θ))
      ≤ (1 - α) * DefectAtPoint sys.consolidated (gfield.grad θ) + C * η ^ 2

/-- Exponential attraction implies Lyapunov stability in the small-η limit is a
    FUTURE lemma; at fixed η it holds when α·D ≥ Cη². Stated and proven here
    in that honest fixed-η form to keep the two properties formally linked. -/
theorem attracting_implies_stable_of_curvature_dominated
    (sys : DefectMonotoneLearningSystem n k) (gfield : GradientField n)
    (α C : ℝ)
    (h : IsExponentiallyAttracting sys gfield α C)
    (θ : Fin n → ℝ) (η : ℝ) (hη : 0 < η) (hη₁ : η < 1)
    (hdom : C * η ^ 2 ≤ α * DefectAtPoint sys.consolidated (gfield.grad θ)) :
    DefectAtPoint sys.consolidated (gfield.grad (lyapunovStep sys gfield η θ))
      ≤ DefectAtPoint sys.consolidated (gfield.grad θ) := by
  have := h θ η hη hη₁
  nlinarith [this, hdom]

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

/-! ### SGC defect correspondence — the true identity is numerator-level

**REFUTATION (kernel hygiene finding, 2026-06-10)**: this file previously
axiomatized a "Pythagorean" decomposition

    D(g) = D(g - Pg) + D(Pg)

for the RATIO functional D. That statement is FALSE: since S(Pg) = 0, the
numerators of D(g) and D(g - Pg) agree, but the DENOMINATORS differ
(‖g‖² vs ‖g - Pg‖²). Counterexample: n = 2, k = 1, S = (1,0), F = I,
g = (1,1): then Pg = (0,1), D(g) = 1/2, while D(g-Pg) + D(Pg) = 1 + 0 = 1.
The axiom was DELETED (seventh defective statement of the week; disease:
intuition transcribed without tracking denominators).

What IS true — and now PROVEN below — is the numerator-level identity: the
leakage of the full gradient equals the leakage of its rejected component,
because the projected component carries exactly zero leakage. This is the
precise (and correctly scoped) sense in which the learning defect mirrors the
SGC defect operator D = (I-Π)LΠ. -/

/-- **THEOREM: Leakage lives entirely in the rejected component.**
    ‖S g‖² = ‖S (g - Pg)‖², because S(Pg) = 0 (primal feasibility). -/
theorem leakage_invariant_under_projection
    (sys : DefectMonotoneLearningSystem n k) (g : Fin n → ℝ) :
    ∑ i : Fin k, (∑ j, sys.consolidated.basis i j * (g j - sys.update g j)) ^ 2
      = ∑ i : Fin k, (∑ j, sys.consolidated.basis i j * g j) ^ 2 := by
  have hpf : ∀ i : Fin k, ∑ j, sys.consolidated.basis i j * sys.update g j = 0 :=
    projected_update_primal_feasible sys g
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have hsplit : (∑ j, sys.consolidated.basis i j * (g j - sys.update g j))
      = (∑ j, sys.consolidated.basis i j * g j)
        - ∑ j, sys.consolidated.basis i j * sys.update g j := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit, hpf i, sub_zero]

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

/-! ## SUMMARY: What This Module Provides (refreshed 2026-06-10)

PROVEN (kernel-checked, zero axioms in this file):
1. **projected_update_primal_feasible**: projector output satisfies S Δθ = 0
2. **projected_update_zero_defect**: projected updates have zero leakage
   (was an axiom; now a theorem)
3. **leakage_invariant_under_projection**: ‖S g‖² = ‖S(g - Pg)‖² — the correct,
   numerator-level SGC-defect correspondence
4. **fisher_projection_implies_emergence**, **fisher_projection_infinite_horizon**
5. **attracting_implies_stable_of_curvature_dominated**: fixed-η link between
   the two Lyapunov properties

VOCABULARY (definitions, no truth claims):
6. **GradientField**, **lyapunovStep**, **IsLyapunovStable**,
   **IsExponentiallyAttracting** — the honest statement language for the
   Layer-3 Lyapunov program

DELETED THIS PASS (2026-06-10):
- `lyapunov_stability_conjecture`, `defect_exponential_decay` — vacuous
  `X ≤ X` tautology-axioms (unused θ_new; D_old ≡ D_new syntactically)
- `learning_defect_is_sgc_defect_analog` — FALSE ratio-level Pythagorean
  claim (denominators differ; 2D counterexample in Part VI note)

## Python Verification Strategy

The Python demos should compute, for the system's ACTUAL loss gradient field:
- `defect(t)` at each training step
- Verify `IsLyapunovStable` empirically: defect(t+1) ≤ defect(t)
- Verify `IsExponentiallyAttracting`: defect(t+1) ≤ (1-α) defect(t) + Cη²

If these fail, the learning rate η is too large (violates "smooth regime"
assumption) — or the conjecture is false for that loss class, which would be
a publishable negative result.
-/
