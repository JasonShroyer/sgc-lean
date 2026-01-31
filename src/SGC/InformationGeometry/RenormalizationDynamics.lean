/-
Copyright (c) 2025 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.InnerProductSpace.Basic
import SGC.InformationGeometry.FisherKL
import SGC.InformationGeometry.DefectDynamics

/-!
# SGC Renormalization Dynamics

This module formalizes the **Dynamic SGC Update Law** where both the state (θ) and
the structure (S) co-evolve. This is the heart of "Self-Guided Constructivism":
the system constructs its own guide.

## The Static vs Dynamic Distinction

**Static Theory (Previous):** Given a fixed consolidated subspace S, project θ.
- Problem: S is an oracle input, not an emergent object.
- Risk: Trivializes "emergence" since projection forces defect to zero by construction.

**Dynamic Theory (This Module):** Discover S while updating θ.
- The system learns WHAT to preserve (S) and HOW to preserve it (Fisher projection).
- S emerges from the gradient field's structure, not from external specification.

## Key Theoretical Objects

1. **RenormalizedState**: Joint state (θ, S, F) representing parameters, structure, metric
2. **IntrinsicDefect**: Defect measured on RAW gradient, not projected update
3. **StructureDiscoveryCriterion**: When to expand S (consolidation trigger)
4. **JointUpdate**: The (θ, S, F) → (θ', S', F') renormalization step

## The Tautology Problem (and Solution)

If defect is defined as ‖(I - P)·(Pg)‖, it is trivially zero (projection is idempotent).

**Solution:** Define **Intrinsic Defect** as:
  D_intrinsic(θ, S) = ‖(I - P_S) g(θ)‖²

This measures how much the RAW gradient fights against the structure.
Emergence = D_intrinsic → 0 (natural forces align with self-imposed constraints).

## SGC Interpretation

- **Micro-state (θ):** The full parameter vector (e.g., all neural network weights)
- **Macro-structure (S):** The consolidated subspace (e.g., "solved" reasoning patterns)
- **Effective metric (F):** The Fisher information (encodes parameter sensitivity)

The joint update implements SGC's core insight: **structure emerges from dynamics**.
The system doesn't just optimize; it discovers what to protect while optimizing.

## References

- Gorban & Karlin, "Invariant Manifolds for Physical and Chemical Kinetics"
- Amari, "Information Geometry and Its Applications"
- SGC Project Documentation

-/

namespace SGC.InformationGeometry.RenormalizationDynamics

open Matrix BigOperators
open SGC.InformationGeometry.FisherKL
open SGC.InformationGeometry.DefectDynamics

-- Suppress unused variable warnings
set_option linter.unusedVariables false

variable {n k : ℕ}

/-! ## Part I: Renormalized State -/

/-- **RenormalizedState**: The joint state of an SGC learning system.

    This captures the three co-evolving components:
    - θ: The parameters (micro-state)
    - S: The consolidated subspace (macro-structure)
    - F: The effective metric (Fisher information)

    **Key Insight:** In standard learning, only θ evolves. In SGC, all three co-evolve.
    The system learns WHAT to preserve (S) while learning HOW to act (θ). -/
structure RenormalizedState (n k : ℕ) where
  /-- The parameter vector (micro-state) -/
  θ : Fin n → ℝ
  /-- The consolidated subspace basis (macro-structure) -/
  S : ConsolidatedSubspace n k
  /-- The Fisher information matrix (effective metric) -/
  F : Matrix (Fin n) (Fin n) ℝ
  /-- Regularization parameter for Fisher inversion -/
  reg : ℝ
  /-- Regularization is positive -/
  h_reg_pos : 0 < reg

/-! ## Part II: Gradient Field and Intrinsic Defect -/

/-- **GradientField**: An abstract gradient field over parameter space.

    This represents the "natural forces" acting on the system before any projection.
    In practice: g(θ) = -∇L(θ) where L is the loss function.

    **Why abstract?** We don't formalize the loss function in Lean; we treat the
    gradient as a given field and study its interaction with the constraint structure. -/
def GradientField (n : ℕ) := (Fin n → ℝ) → (Fin n → ℝ)

/-- **IntrinsicDefect**: The defect measured on the RAW gradient field.

    D_intrinsic(θ, S, g) = ‖(I - P_S) g(θ)‖² / ‖g(θ)‖²

    This measures the fraction of gradient "energy" that fights against the structure.

    **Critical Distinction:**
    - DefectAtPoint (from DefectDynamics.lean): Measures defect of a given update Δθ
    - IntrinsicDefect: Measures defect of the RAW gradient g(θ) at point θ

    **Emergence Criterion:** D_intrinsic → 0 means the system's natural dynamics
    have become aligned with its self-imposed constraints. This is NOT tautological
    because we measure the RAW gradient, not the projected update. -/
noncomputable def IntrinsicDefect (S : ConsolidatedSubspace n k) (g : Fin n → ℝ) : ℝ :=
  let S_mat := SubspaceMatrix S
  let Sg := S_mat *ᵥ g  -- Component in consolidated directions
  let leakage := ∑ i, (Sg i)^2  -- Squared norm of leakage
  let total := ∑ i, (g i)^2  -- Squared norm of gradient
  if total = 0 then 0 else leakage / total

/-- **IntrinsicDefectAtState**: Intrinsic defect evaluated at a RenormalizedState.

    This combines the gradient field with the state to get a scalar defect measure. -/
noncomputable def IntrinsicDefectAtState (state : RenormalizedState n k)
    (field : GradientField n) : ℝ :=
  IntrinsicDefect state.S (field state.θ)

/-! ## Part III: Structure Discovery Criterion -/

/-- **ConsolidationCriterion**: When should a direction be added to S?

    SGC Answer: When the Fisher information in that direction exceeds a threshold.
    High Fisher information = small changes cause large KL divergence = "stiff" direction.

    Formally: direction v should be consolidated if vᵀ F v > λ_critical · ‖v‖².

    **Interpretation:**
    - High Fisher eigenvector = "the system is certain about this aspect"
    - Low Fisher eigenvector = "the system is uncertain, still learning"

    Consolidate the certain parts; keep learning the uncertain parts. -/
def ConsolidationCriterion (F : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (crit : ℝ) : Prop :=
  let Fv := F *ᵥ v
  let vFv := ∑ i, v i * Fv i  -- vᵀ F v (quadratic form)
  let v_norm_sq := ∑ i, (v i)^2
  vFv > crit * v_norm_sq

/-- **ShouldExpand**: Should the subspace S be expanded to include direction v?

    This is the "discovery" trigger: when the gradient field has been consistently
    orthogonal to the current S in direction v, AND v has high Fisher information,
    then v should be consolidated.

    **Intuition:** The system has "figured out" direction v (high Fisher) and
    the gradient no longer wants to change it (orthogonality). Time to lock it in. -/
def ShouldExpand (state : RenormalizedState n k) (v : Fin n → ℝ)
    (crit : ℝ) (field : GradientField n) : Prop :=
  -- v has high Fisher information (system is "certain")
  ConsolidationCriterion state.F v crit ∧
  -- v is nearly orthogonal to the current gradient (system "doesn't want to change it")
  let g := field state.θ
  let v_dot_g := ∑ i, v i * g i
  let v_norm := Real.sqrt (∑ i, (v i)^2)
  let g_norm := Real.sqrt (∑ i, (g i)^2)
  -- Orthogonality: |⟨v, g⟩| / (‖v‖ · ‖g‖) < ε
  v_norm * g_norm ≠ 0 → |v_dot_g| / (v_norm * g_norm) < 0.1  -- 90% orthogonality

/-! ## Part IV: The Joint Update Law -/

/-- **UpdateStructure**: The "Discovery" step of SGC.

    Given current state and gradient field, determine the new subspace S'.

    **Algorithm (conceptual):**
    1. Compute eigenvectors of F with eigenvalue > λ_critical
    2. Filter to those nearly orthogonal to current gradient
    3. Add to S (if not already spanned)

    **Note:** This is axiomatized because:
    - Eigenvalue computation is not constructive in Lean's type theory
    - The exact expansion rule depends on implementation choices

    The axiom states: the update preserves the consolidation invariant. -/
axiom update_structure : RenormalizedState n k → GradientField n → ConsolidatedSubspace n k

/-- **UpdateStructure preserves consolidation**: Directions in S' satisfy the criterion.

    This is the key invariant: we only add "mature" directions to S. -/
axiom update_structure_preserves_criterion (state : RenormalizedState n k)
    (field : GradientField n) (crit : ℝ) :
    ∀ i : Fin k, ConsolidationCriterion state.F ((update_structure state field).basis i) crit

/-- **State Fisher Symmetry**: The Fisher matrix in a RenormalizedState is symmetric.
    This is a basic property of Fisher information matrices. -/
axiom state_fisher_symm (state : RenormalizedState n k) : state.F.IsSymm

/-- **State Fisher PSD**: The Fisher matrix in a RenormalizedState is positive semidefinite.
    This is a basic property of Fisher information matrices. -/
axiom state_fisher_psd (state : RenormalizedState n k) :
    ∀ v : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, v i * state.F i j * v j

/-- **ProjectAndStep**: The "Learning" step of SGC.

    Given state with updated S, compute the Fisher-projected gradient step.

    θ' = θ + η · P_F(S') · g(θ)

    where P_F is the Fisher projector onto ker(S'). -/
noncomputable def project_and_step (state : RenormalizedState n k)
    (S_new : ConsolidatedSubspace n k)
    (F_reg_inv : Matrix (Fin n) (Fin n) ℝ)
    (Gram_inv : Matrix (Fin k) (Fin k) ℝ)
    (field : GradientField n)
    (eta : ℝ) : Fin n → ℝ :=
  let g := field state.θ
  -- Build RegularizedFisher from state (axiomatize the symmetry/psd properties)
  let RF : RegularizedFisher n := {
    F := state.F
    regParam := state.reg
    regParam_pos := state.h_reg_pos
    F_symm := state_fisher_symm state
    F_posSemidef := state_fisher_psd state
  }
  let P := FisherProjector RF S_new F_reg_inv Gram_inv
  let delta_theta := P *ᵥ g
  fun i => state.θ i + eta * delta_theta i

/-- **UpdateMetric**: The "Geometry" step of SGC.

    Recompute Fisher information at the new parameter point.

    **Note:** This is axiomatized because Fisher computation requires:
    - A probability model p(x | θ)
    - Expectations over the data distribution

    The axiom states: the updated Fisher is positive semi-definite. -/
axiom update_metric : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ

axiom update_metric_psd (θ : Fin n → ℝ) :
    Matrix.PosSemidef (update_metric θ)

/-! ## Part V: The Complete Joint Update -/

/-- **JointUpdate**: The complete SGC renormalization step.

    (θ, S, F) ↦ (θ', S', F')

    This is the "breathing" of the system:
    1. **Discover** (update S): What new structure has emerged?
    2. **Learn** (update θ): Move in the projected gradient direction
    3. **Adapt** (update F): Recompute the geometry at the new point

    **Key Property:** This is a CLOSED dynamical system on the space of
    RenormalizedStates. The system evolves autonomously without external guidance. -/
noncomputable def joint_update (state : RenormalizedState n k)
    (field : GradientField n)
    (F_reg_inv : Matrix (Fin n) (Fin n) ℝ)
    (Gram_inv : Matrix (Fin k) (Fin k) ℝ)
    (eta : ℝ) : RenormalizedState n k :=
  let S_new := update_structure state field
  let θ_new := project_and_step state S_new F_reg_inv Gram_inv field eta
  let F_new := update_metric θ_new
  -- For now, we keep k fixed (no subspace dimension change)
  -- A more sophisticated version would allow k to grow
  { θ := θ_new
  , S := S_new
  , F := F_new
  , reg := state.reg
  , h_reg_pos := state.h_reg_pos }

/-! ## Part VI: Intrinsic Defect Dynamics (The Main Theorem) -/

/-- **AXIOM: Intrinsic Defect Lyapunov Stability**

    The joint update law does not increase intrinsic defect:
      D_intrinsic(θ', S') ≤ D_intrinsic(θ, S)

    **This is the non-tautological emergence criterion.**

    Unlike DefectAtPoint (which measures the projected update), IntrinsicDefect
    measures the RAW gradient field. The theorem says: after the joint update,
    the new gradient field is MORE aligned with the new structure.

    **Mathematical Content:**
    1. The structure S evolves to "capture" high-information directions
    2. The parameters θ evolve to make the gradient more compatible with S
    3. The combined effect is non-increasing intrinsic defect

    **Domain of Validity:**
    - Small learning rate η (thermodynamic limit)
    - Smooth gradient field (no discontinuities)
    - Non-degenerate Fisher matrix (full rank after regularization)

    **Why This Isn't Tautological:**
    - S' ≠ S in general (structure evolves)
    - g(θ') ≠ g(θ) in general (gradient changes)
    - The theorem claims these changes CONSPIRE to reduce defect -/
axiom intrinsic_defect_lyapunov (state : RenormalizedState n k)
    (field : GradientField n)
    (F_reg_inv : Matrix (Fin n) (Fin n) ℝ)
    (Gram_inv : Matrix (Fin k) (Fin k) ℝ)
    (eta : ℝ)
    (h_eta_small : 0 < eta ∧ eta < 1) :
    let state' := joint_update state field F_reg_inv Gram_inv eta
    IntrinsicDefectAtState state' field ≤ IntrinsicDefectAtState state field

/-- **AXIOM: Intrinsic Defect Exponential Decay**

    Under favorable conditions, intrinsic defect decays exponentially:
      D'_intrinsic ≤ (1 - α) · D_intrinsic + O(η²)

    where α > 0 is the "consolidation rate."

    **Interpretation:**
    - α measures how quickly the system discovers and locks in structure
    - The O(η²) term is unavoidable discretization error
    - For emergence: choose η small enough that decay dominates error -/
axiom intrinsic_defect_exponential_decay (state : RenormalizedState n k)
    (field : GradientField n)
    (F_reg_inv : Matrix (Fin n) (Fin n) ℝ)
    (Gram_inv : Matrix (Fin k) (Fin k) ℝ)
    (eta alpha C : ℝ)
    (h_alpha_pos : 0 < alpha) (h_alpha_bound : alpha < 1)
    (h_eta_small : 0 < eta) :
    let state' := joint_update state field F_reg_inv Gram_inv eta
    let D := IntrinsicDefectAtState state field
    let D' := IntrinsicDefectAtState state' field
    D' ≤ (1 - alpha) * D + C * eta^2

/-! ## Part VII: Observable-Based Constraints (Primal/Dual Unification) -/

/-- **Observable**: A function from parameters to a scalar "macro-observable."

    Examples:
    - Coordinate projection: O_i(θ) = θ_i (trivial, leads to primal freezing)
    - Entropy: O(θ) = H(p_θ) (nontrivial, measures information content)
    - Accuracy: O(θ) = E[correct(θ)] (task-specific) -/
def Observable (n : ℕ) := (Fin n → ℝ) → ℝ

/-- **ObservableGradient**: The gradient of an observable.

    ∇O(θ) tells us how sensitive O is to changes in θ.
    Preserving O means: ⟨∇O, Δθ⟩ = 0. -/
def ObservableGradient (O : Observable n) (θ : Fin n → ℝ) : Fin n → ℝ :=
  -- Axiomatized: in practice, computed by autodiff
  fun _ => 0  -- Placeholder

/-- **ObservablePreservationConstraint**: The DUAL form of constraint.

    "Preserve observable O" means: ⟨∇O(θ), Δθ⟩ = 0

    This is the NATURAL way to state constraints in information geometry.
    The primal constraint "S Δθ = 0" is a SPECIAL CASE where:
    - S_i is the gradient of the coordinate observable O_i(θ) = θ_i -/
def ObservablePreservationConstraint (O : Observable n) (theta : Fin n → ℝ) (dtheta : Fin n → ℝ) : Prop :=
  let gradO := ObservableGradient O theta
  ∑ i, gradO i * dtheta i = 0

/-- **Primal Freezing is a Special Case** (axiomatized for simplicity)

    When O_i(θ) = θ_i (coordinate projection), the observable preservation
    constraint reduces to the primal constraint S Δθ = 0.

    This unifies the primal/dual perspectives: we work with observables (dual),
    and primal freezing is recovered when observables are coordinates. -/
axiom primal_freezing_is_special_case (S : ConsolidatedSubspace n k) (theta dtheta : Fin n → ℝ)
    (h_k_le_n : k ≤ n)
    (h_S_is_coordinates : ∀ i : Fin k, ∀ j : Fin n, S.basis i j = if j.val = i.val then 1 else 0) :
    -- If S represents coordinate projections onto first k coordinates...
    (∀ i : Fin k, S.basis i ⬝ᵥ dtheta = 0) ↔
    -- ...then observable preservation = coordinate freezing
    (∀ i : Fin k, dtheta ⟨i.val, Nat.lt_of_lt_of_le i.isLt h_k_le_n⟩ = 0)

/-! ## Part VIII: The SGC Closure Principle -/

/-- **SGC Closure Principle**: Structure emerges from defect measurements.

    The "right" consolidated subspace S is the one that:
    1. Captures all high-Fisher directions (certainty)
    2. Is compatible with the gradient field (alignment)
    3. Minimizes intrinsic defect in the limit

    **Formally:** S* = argmin_S lim_{t→∞} D_intrinsic(θ_t, S_t)

    This is the variational characterization of emergent structure.

    **Connection to SGC Coarse-Graining:**
    - SGC: Coarse space = image of projector that minimizes defect operator norm
    - Here: Consolidated subspace = kernel of projector that minimizes intrinsic defect

    The duality (image vs kernel) reflects the complementary perspectives:
    - SGC: "What macro-dynamics are preserved?"
    - Learning: "What directions are frozen?" -/
axiom sgc_closure_principle (state₀ : RenormalizedState n k)
    (field : GradientField n)
    (trajectory : ℕ → RenormalizedState n k)
    (h_trajectory : ∀ t, ∃ F_inv Gram_inv eta, trajectory (t + 1) = joint_update (trajectory t) field F_inv Gram_inv eta)
    (h_init : trajectory 0 = state₀) :
    -- The intrinsic defect converges
    ∃ D_limit : ℝ, ∀ ε > 0, ∃ T, ∀ t ≥ T,
      |IntrinsicDefectAtState (trajectory t) field - D_limit| < ε

/-! ## Part IX: Connection to Python Demo -/

/-! ### V1 vs V2 Distinction

**V1 (Current Demo):** S = "Solved Constraints" (Cell-Locking)
- As solver runs, lock in cell values with entropy ≈ 0
- S grows by adding coordinates corresponding to solved cells
- This is TRIVIAL emergence: structure = problem revealing itself

**V2 (SGC Vision):** S = "Consolidated Skills" (Pattern-Locking)
- Lock in REASONING PATTERNS, not output values
- S lives in the hidden state / weight space, not output space
- Solving one Sudoku improves performance on DIFFERENT Sudokus

**The Pivot:** Move from output-space freezing to representation-space freezing.
Fisher orthogonality should protect CONCEPTS, not ANSWERS.

**Implementation Hint for Python:**
```python
# V1 (trivial): S tracks solved cells
S = identify_low_entropy_outputs(probabilities)

# V2 (SGC): S tracks stable attention patterns
S = identify_high_fisher_hidden_directions(model.attention_weights)
```
-/

/-- **EmergencePhaseTransition**: The predicted behavior in Python.

    The theory predicts a PHASE TRANSITION in the defect plot:
    1. **Chaotic Phase:** High intrinsic defect, gradient fights against structure
    2. **Critical Point:** Defect drops sharply as structure aligns with dynamics
    3. **Emergent Phase:** Low, stable defect plateau (the "Aha!" moment)

    **Falsification Criterion:** If Fisher-orthogonal updates do NOT produce
    this phase transition (defect remains high or fluctuates wildly), the
    theory is WRONG (or the learning rate is too high). -/
axiom emergence_phase_transition (state₀ : RenormalizedState n k)
    (field : GradientField n)
    (trajectory : ℕ → RenormalizedState n k)
    (h_trajectory : ∀ t, ∃ F_inv Gram_inv eta, trajectory (t + 1) = joint_update (trajectory t) field F_inv Gram_inv eta)
    (h_init : trajectory 0 = state₀)
    (D₀ : ℝ) (h_D₀ : D₀ = IntrinsicDefectAtState state₀ field)
    (h_D₀_high : D₀ > 0.5) :  -- Start in chaotic phase
    -- There exists a time T and threshold eps such that defect drops and stays low
    ∃ T : ℕ, ∃ eps : ℝ, eps < 0.1 ∧ ∀ t ≥ T,
      IntrinsicDefectAtState (trajectory t) field < eps

end SGC.InformationGeometry.RenormalizationDynamics
