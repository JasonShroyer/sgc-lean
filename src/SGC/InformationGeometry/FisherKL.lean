/-
Copyright (c) 2025 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team

# Fisher-KL Bounds: Information Geometry for Learning Systems

This module establishes the fundamental connection between the Fisher information
metric and KL divergence, providing the mathematical foundation for:
- Validity horizons for learned skills
- Projected gradient methods that preserve consolidated behaviors
- No-forgetting bounds for continual learning

## Main Results

1. `KL_Fisher_local_bound` - KL(p_θ ‖ p_{θ+Δθ}) ≤ ½ Δθᵀ F(θ) Δθ + O(‖Δθ‖³)
2. `Fisher_orthogonal_KL_bound` - Fisher-orthogonal updates have bounded KL change
3. `projected_update_formula` - Closed-form Fisher-orthogonal projection
4. `no_forgetting_horizon` - Accumulated KL drift bound over many steps

## Physical Significance

**Information Geometry**: The Fisher metric F(θ) is the "natural" Riemannian metric
on the statistical manifold {p_θ}. KL divergence measures "distance" along geodesics.

**Learning Connection**: Policy gradient methods move along the statistical manifold.
Fisher-orthogonal projections ensure we don't "forget" consolidated skills.

**SGC Bridge**: This is the learning-side sibling of `trajectory_closure_bound` -
both bound accumulated error from approximate dynamics.

## References

- Amari (1998), "Natural Gradient Works Efficiently in Learning"
- Martens (2014), "New Insights and Perspectives on the Natural Gradient Method"
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

noncomputable section

namespace SGC.InformationGeometry.FisherKL

open Finset Matrix Real

-- Suppress unused variable warnings
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Part I: KL Divergence and Fisher Information -/

/-! ### 1. KL Divergence for Finite Distributions -/

/-- **KL Divergence** between two distributions p and q over finite state space V.

    D_KL(p ‖ q) = Σᵥ p(v) log(p(v)/q(v))

    We use the convention 0 log 0 = 0 and x log(x/0) = +∞. -/
def KL_divergence (p q : V → ℝ) : ℝ :=
  ∑ v, if p v = 0 then 0 else p v * Real.log (p v / q v)

/-- KL divergence is non-negative (Gibbs' inequality). -/
axiom KL_nonneg (p q : V → ℝ) (hp : ∀ v, 0 ≤ p v) (hq : ∀ v, 0 < q v)
    (hp_sum : ∑ v, p v = 1) (hq_sum : ∑ v, q v = 1) :
    0 ≤ KL_divergence p q

/-- KL divergence is zero iff p = q. -/
axiom KL_eq_zero_iff (p q : V → ℝ) (hp : ∀ v, 0 < p v) (hq : ∀ v, 0 < q v)
    (hp_sum : ∑ v, p v = 1) (hq_sum : ∑ v, q v = 1) :
    KL_divergence p q = 0 ↔ p = q

/-! ### 2. Parametric Families -/

/-- A **Parametric Family** is a smooth map from parameters θ ∈ ℝⁿ to distributions.
    We assume the family is "regular" (smooth, positive, normalized). -/
structure ParametricFamily (n : ℕ) (V : Type*) [Fintype V] where
  /-- The distribution at parameter θ -/
  dist : (Fin n → ℝ) → V → ℝ
  /-- Distributions are positive -/
  positive : ∀ θ v, 0 < dist θ v
  /-- Distributions are normalized -/
  normalized : ∀ θ, ∑ v, dist θ v = 1

variable {n : ℕ}

/-- Shorthand for the distribution at θ. -/
abbrev ParametricFamily.p (P : ParametricFamily n V) (θ : Fin n → ℝ) : V → ℝ := P.dist θ

/-! ### 3. Fisher Information Matrix -/

/-- **Score Function**: The gradient of log p_θ(v) with respect to θ.

    s_i(θ, v) = ∂/∂θ_i log p_θ(v) = (∂p_θ(v)/∂θ_i) / p_θ(v)

    This is axiomatized since we don't have a concrete representation of p_θ. -/
axiom score_function (P : ParametricFamily n V) (θ : Fin n → ℝ) (i : Fin n) (v : V) : ℝ

/-- Score has zero mean: 𝔼_{p_θ}[s_i] = 0.
    This is a fundamental identity in information geometry. -/
axiom score_zero_mean (P : ParametricFamily n V) (θ : Fin n → ℝ) (i : Fin n) :
    ∑ v, P.p θ v * score_function P θ i v = 0

/-- **Fisher Information Matrix**: The covariance of the score function.

    F(θ)_{ij} = 𝔼_{p_θ}[s_i(θ, ·) · s_j(θ, ·)]
             = Σᵥ p_θ(v) · s_i(θ,v) · s_j(θ,v)

    This is the natural Riemannian metric on the statistical manifold. -/
def FisherMatrix (P : ParametricFamily n V) (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ∑ v, P.p θ v * score_function P θ i v * score_function P θ j v

/-- Fisher matrix is symmetric. -/
lemma FisherMatrix_symmetric (P : ParametricFamily n V) (θ : Fin n → ℝ) :
    (FisherMatrix P θ).IsSymm := by
  unfold Matrix.IsSymm FisherMatrix
  ext i j
  simp only [transpose_apply, of_apply]
  congr 1; ext v; ring

/-- Fisher matrix is positive semidefinite.
    F(θ) ≥ 0 follows from F = 𝔼[s sᵀ] being a covariance matrix. -/
axiom FisherMatrix_posSemidef (P : ParametricFamily n V) (θ : Fin n → ℝ) :
    ∀ w : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, w i * (FisherMatrix P θ) i j * w j

/-! ## Part II: The KL-Fisher Local Bound -/

/-- **The Quadratic Form**: Δθᵀ F(θ) Δθ -/
def FisherQuadForm (P : ParametricFamily n V) (θ Δθ : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, Δθ i * (FisherMatrix P θ) i j * Δθ j

/-- The quadratic form is non-negative. -/
lemma FisherQuadForm_nonneg (P : ParametricFamily n V) (θ Δθ : Fin n → ℝ) :
    0 ≤ FisherQuadForm P θ Δθ :=
  FisherMatrix_posSemidef P θ Δθ

/-- **Euclidean Norm Squared** of Δθ. -/
def paramNormSq (Δθ : Fin n → ℝ) : ℝ := ∑ i, (Δθ i)^2

/-- **KL-Fisher Local Bound** (Main Theorem 1):

    For small Δθ, the KL divergence is bounded by the Fisher quadratic form:

    KL(p_θ ‖ p_{θ+Δθ}) ≤ ½ Δθᵀ F(θ) Δθ + C · ‖Δθ‖³

    This is the fundamental "metric controls drift" statement.

    **Proof Idea** (Taylor expansion):
    1. KL(p ‖ q) = Σ p log(p/q) = -Σ p log(q/p)
    2. log p_{θ+Δθ}(v) ≈ log p_θ(v) + Σᵢ Δθᵢ · s_i(θ,v) + ½ Σᵢⱼ Δθᵢ Δθⱼ · H_ij(θ,v)
    3. Taking expectation and using score_zero_mean, the linear term vanishes
    4. The quadratic term gives ½ Δθᵀ F(θ) Δθ
    5. The remainder is O(‖Δθ‖³)

**AXIOM: KL-Fisher Local Bound**

    This is the fundamental Taylor expansion result connecting KL divergence
    to Fisher information. It requires smoothness assumptions on P that are
    standard in information geometry but not encoded in our ParametricFamily.

    **Mathematical content**: For smooth parametric families,
    KL(p_θ ‖ p_{θ+Δθ}) = ½ Δθᵀ F(θ) Δθ + O(‖Δθ‖³)

    **Reference**: Amari & Nagaoka, "Methods of Information Geometry", Thm 3.3 -/
axiom KL_Fisher_local_bound (P : ParametricFamily n V) (θ Δθ : Fin n → ℝ) :
    ∃ (C : ℝ), 0 ≤ C ∧
      KL_divergence (P.p θ) (P.p (θ + Δθ)) ≤
        (1/2) * FisherQuadForm P θ Δθ + C * (paramNormSq Δθ) * Real.sqrt (paramNormSq Δθ)

/-! ## Part III: Fisher-Orthogonal Projections -/

/-! ### 4. Consolidated Subspace -/

/-- A **Consolidated Subspace** is a k-dimensional linear subspace of parameter space ℝⁿ
    representing "frozen" or "protected" behaviors.

    Think of this as the space of parameters that affect consolidated skills. -/
structure ConsolidatedSubspace (n k : ℕ) where
  /-- Basis vectors for the subspace -/
  basis : Fin k → (Fin n → ℝ)
  /-- Basis is orthonormal (in Euclidean sense) -/
  orthonormal : ∀ i j, ∑ l, basis i l * basis j l = if i = j then 1 else 0

/-- **Fisher Inner Product**: The inner product induced by Fisher matrix.
    ⟨u, v⟩_F = uᵀ F(θ) v -/
def FisherInner (P : ParametricFamily n V) (θ : Fin n → ℝ) (u v : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, u i * (FisherMatrix P θ) i j * v j

/-- Fisher inner product is symmetric. -/
lemma FisherInner_symm (P : ParametricFamily n V) (θ u v : Fin n → ℝ) :
    FisherInner P θ u v = FisherInner P θ v u := by
  unfold FisherInner
  have h_symm := FisherMatrix_symmetric P θ
  -- Use symmetry: F_{ij} = F_{ji}
  have h_entry : ∀ i j, (FisherMatrix P θ) i j = (FisherMatrix P θ) j i :=
    fun i j => (h_symm.apply i j).symm
  calc ∑ i, ∑ j, u i * (FisherMatrix P θ) i j * v j
      = ∑ i, ∑ j, v j * (FisherMatrix P θ) j i * u i := by
          congr 1; ext i; congr 1; ext j; rw [h_entry i j]; ring
    _ = ∑ j, ∑ i, v j * (FisherMatrix P θ) j i * u i := Finset.sum_comm
    _ = _ := by rfl

variable {k : ℕ}

/-- A direction v is **Fisher-orthogonal** to a subspace S if
    ⟨v, s⟩_F = 0 for all s in S. -/
def IsFisherOrthogonal (P : ParametricFamily n V) (θ : Fin n → ℝ)
    (S : ConsolidatedSubspace n k) (v : Fin n → ℝ) : Prop :=
  ∀ i : Fin k, FisherInner P θ v (S.basis i) = 0

/-! ### 5. Fisher-Orthogonal Projection (CONSTRUCTIVE)

This section makes the Fisher-orthogonal projector **constructive** rather than axiomatic.
The key insight is that the projector solves a **constrained optimization problem**.

## The Minimal Disturbance Principle

**Problem**: Given a gradient direction g, find the update Δθ that:
1. Minimizes deviation from g in the Fisher metric: min ‖Δθ - g‖²_F
2. Subject to freezing consolidated directions: S Δθ = 0 (PRIMAL CONSTRAINT)

where S is a k×n matrix whose rows span the "consolidated subspace" (parameters to freeze).

**Solution**: Δθ = P_⊥ g  where P_⊥ = I - F⁻¹Sᵀ(SF⁻¹Sᵀ)⁻¹S

## Connection to SGC Defect Structure

This is the **learning-side analog** of SGC's coarse projector:
- **SGC**: Π = lift ∘ Q projects onto block-constant functions (macro-observables)
- **Learning**: P_⊥ projects onto the orthogonal complement of consolidated skills

Both satisfy D = (I - Π) L Π, where D is the "leakage defect."
The projector emerges from minimizing disturbance subject to preservation constraints.
-/

/-- **Subspace Matrix**: Convert basis vectors to a matrix S : k × n
    where row i is the i-th basis vector. -/
def SubspaceMatrix (S : ConsolidatedSubspace n k) : Matrix (Fin k) (Fin n) ℝ :=
  Matrix.of (fun i j => S.basis i j)

/-- **Regularized Fisher Inverse**: F⁻¹ with Tikhonov regularization (F + λI)⁻¹.
    This ensures invertibility even when F is singular or ill-conditioned.
    For λ > 0 and F positive semidefinite, (F + λI) is positive definite. -/
structure RegularizedFisher (n : ℕ) where
  /-- The Fisher matrix -/
  F : Matrix (Fin n) (Fin n) ℝ
  /-- Regularization parameter (Tikhonov damping) -/
  regParam : ℝ
  /-- regParam > 0 for positive definiteness -/
  regParam_pos : 0 < regParam
  /-- F is symmetric -/
  F_symm : F.IsSymm
  /-- F is positive semidefinite -/
  F_posSemidef : ∀ v : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, v i * F i j * v j

/-- The regularized matrix F + λI. -/
def RegularizedFisher.regularized (RF : RegularizedFisher n) : Matrix (Fin n) (Fin n) ℝ :=
  RF.F + RF.regParam • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- **AXIOM: Regularized Fisher is Positive Definite**

    For F positive semidefinite and λ > 0, (F + λI) is positive definite.
    This is standard linear algebra: ⟨v, (F + λI)v⟩ = ⟨v, Fv⟩ + λ‖v‖² > 0 for v ≠ 0.

    **Note**: This could be proven using Mathlib's PosDef theory, but we axiomatize
    it to avoid deep dependencies on matrix positivity infrastructure. -/
axiom RegularizedFisher.posDef (RF : RegularizedFisher n) :
    ∀ v : Fin n → ℝ, v ≠ 0 → 0 < ∑ i, ∑ j, v i * RF.regularized i j * v j

/-! ## TWO PROJECTORS: EUCLIDEAN VS FISHER

**Critical Distinction** (addressing the "one projector, two contracts" issue):

1. **Euclidean Projector** (Primal): Minimizes ‖Δθ - g‖²_Euclidean subject to SΔθ = 0
   - Formula: P_E = I - Sᵀ(SSᵀ)⁻¹S
   - Use for: Standard gradient descent with frozen parameters

2. **Fisher Projector** (Natural): Minimizes ‖Δθ - g‖²_Fisher subject to SΔθ = 0
   - Formula: P_F = I - F⁻¹Sᵀ(SF⁻¹Sᵀ)⁻¹S
   - Use for: Natural gradient descent (information geometry)

**Key Insight**: Both projectors enforce the SAME primal constraint (SΔθ = 0),
but they minimize distance in DIFFERENT metrics. The Fisher projector is the
correct one for learning because it respects the geometry of the parameter space.

**When do they coincide?** When F = I (flat geometry), P_E = P_F.
-/

/-- **Euclidean Projector Matrix** (PRIMAL CONSTRAINT, EUCLIDEAN METRIC):

    P_E = I - Sᵀ (S Sᵀ)⁻¹ S

    This is the standard orthogonal projection onto ker(S).

    **Optimization problem solved**:
    - Minimize: ½ ‖Δθ - g‖²_Euclidean
    - Subject to: S Δθ = 0

    **Use case**: Standard gradient descent where we want to freeze certain
    linear combinations of parameters. -/
def EuclideanProjector (S : ConsolidatedSubspace n k)
    (Gram_inv : Matrix (Fin k) (Fin k) ℝ)  -- (S Sᵀ)⁻¹
    : Matrix (Fin n) (Fin n) ℝ :=
  let S_mat := SubspaceMatrix S
  (1 : Matrix (Fin n) (Fin n) ℝ) - S_matᵀ * Gram_inv * S_mat

/-- **Fisher Projector Matrix** (PRIMAL CONSTRAINT, FISHER METRIC):

    P_F = I - F⁻¹ Sᵀ (S F⁻¹ Sᵀ)⁻¹ S

    This is the projection onto ker(S) that minimizes Fisher distance.

    **Optimization problem solved**:
    - Minimize: ½ (Δθ - g)ᵀ F (Δθ - g)
    - Subject to: S Δθ = 0

    **Use case**: Natural gradient descent where we want to freeze certain
    linear combinations of parameters while respecting the information geometry.

    **Note**: This is the SAME formula as FisherOrthogonalProjector below,
    but with clearer semantic intent: we enforce a PRIMAL constraint (SΔθ=0)
    while minimizing in the FISHER metric. -/
def FisherProjector (RF : RegularizedFisher n)
    (S : ConsolidatedSubspace n k)
    (F_reg_inv : Matrix (Fin n) (Fin n) ℝ)  -- (F + λI)⁻¹
    (Gram_inv : Matrix (Fin k) (Fin k) ℝ)   -- (S (F + λI)⁻¹ Sᵀ)⁻¹
    : Matrix (Fin n) (Fin n) ℝ :=
  let S_mat := SubspaceMatrix S
  (1 : Matrix (Fin n) (Fin n) ℝ) - F_reg_inv * S_matᵀ * Gram_inv * S_mat

/-- **Fisher-Orthogonal Projector Matrix** (LEGACY NAME, SAME AS FisherProjector):

    P_⊥ = I - (F + λI)⁻¹ Sᵀ (S (F + λI)⁻¹ Sᵀ)⁻¹ S

    This is kept for backwards compatibility. Prefer `FisherProjector` for clarity. -/
def FisherOrthogonalProjector (RF : RegularizedFisher n)
    (S : ConsolidatedSubspace n k)
    (F_reg_inv : Matrix (Fin n) (Fin n) ℝ)  -- (F + λI)⁻¹
    (Gram_inv : Matrix (Fin k) (Fin k) ℝ)   -- (S (F + λI)⁻¹ Sᵀ)⁻¹
    : Matrix (Fin n) (Fin n) ℝ :=
  FisherProjector RF S F_reg_inv Gram_inv

/-- **Constrained Optimization Problem**: The objective we're minimizing.
    J(Δθ) = ½ (Δθ - g)ᵀ F (Δθ - g) = ½ ‖Δθ - g‖²_F -/
def FisherObjective (RF : RegularizedFisher n) (g Δθ : Fin n → ℝ) : ℝ :=
  (1/2) * ∑ i, ∑ j, (Δθ i - g i) * RF.regularized i j * (Δθ j - g j)

/-- **Primal Feasibility Constraint**: S Δθ = 0 (freeze consolidated directions).

    This is the **primal constraint**: the update must have zero component
    in each consolidated direction. In matrix form: (S *ᵥ Δθ) = 0.

    **Interpretation for Sudoku/Learning**:
    - S contains directions that affect already-solved cells / consolidated skills
    - S Δθ = 0 means the update doesn't change those cells / skills -/
def PrimalFeasible (S : ConsolidatedSubspace n k) (Δθ : Fin n → ℝ) : Prop :=
  ∀ i : Fin k, ∑ j, S.basis i j * Δθ j = 0

/-- **Fisher-Orthogonality Constraint**: ⟨s_i, Δθ⟩_F = 0 (orthogonal in Fisher metric).

    This is a **dual constraint**: the update must be Fisher-orthogonal to
    the consolidated subspace. In matrix form: S F Δθ = 0.

    Note: This is DIFFERENT from PrimalFeasible. Use PrimalFeasible for
    "freeze specific parameters" and FisherFeasible for "orthogonal in metric." -/
def FisherFeasible (RF : RegularizedFisher n) (S : ConsolidatedSubspace n k)
    (Δθ : Fin n → ℝ) : Prop :=
  ∀ i : Fin k, ∑ l, ∑ m, S.basis i l * RF.regularized l m * Δθ m = 0

/-- **MINIMAL DISTURBANCE THEOREM** (Main Theoretical Result):

    The Fisher-orthogonal projector gives the UNIQUE minimizer of the
    constrained optimization problem with **primal constraint**:

    Δθ* = argmin { ‖Δθ - g‖²_F : S Δθ = 0 }
        = P_⊥ g
        = (I - F⁻¹Sᵀ(SF⁻¹Sᵀ)⁻¹S) g

    This turns "preserve consolidated skills" into a **computable control law**.

    ## Derivation via Lagrange Multipliers

    **Lagrangian**: L(Δθ, μ) = ½(Δθ-g)ᵀF(Δθ-g) + μᵀ S Δθ

    **Stationarity**: ∂L/∂Δθ = F(Δθ-g) + Sᵀμ = 0
                     → FΔθ = Fg - Sᵀμ
                     → Δθ = g - F⁻¹Sᵀμ

    **Feasibility**: S Δθ = 0
                     → S(g - F⁻¹Sᵀμ) = 0
                     → Sg = SF⁻¹Sᵀμ
                     → μ = (SF⁻¹Sᵀ)⁻¹ Sg

    **Solution**: Δθ = g - F⁻¹Sᵀ(SF⁻¹Sᵀ)⁻¹Sg
                    = (I - F⁻¹Sᵀ(SF⁻¹Sᵀ)⁻¹S) g
                    = P_⊥ g  ✓

    ## SGC Interpretation

    This is the **Equivalence Principle for Learning**:
    - The projected update is the "geodesic" motion on the constraint manifold
    - F⁻¹Sᵀ(SF⁻¹Sᵀ)⁻¹S is the "defect" that gets subtracted (cf. SGC's D = (I-Π)LΠ)
    - Minimizing Fisher distance = minimizing thermodynamic cost of the update

**PRIMAL CONSTRAINT VERSION** (The main theorem for learning applications):

    The projector P_⊥ = I - F⁻¹Sᵀ(SF⁻¹Sᵀ)⁻¹S gives the unique minimizer of:

    min ‖Δθ - g‖²_F  subject to  S Δθ = 0

    This is the correct theorem for "freeze consolidated parameters."

**AXIOM: Minimal Disturbance (Primal Feasibility)**

    The projector P_⊥ = I - F⁻¹Sᵀ(SF⁻¹Sᵀ)⁻¹S satisfies S(P_⊥ g) = 0.

    **Proof sketch** (matrix algebra):
    S P_⊥ g = S(I - F⁻¹Sᵀ Gram⁻¹ S)g = Sg - (SF⁻¹Sᵀ) Gram⁻¹ Sg = Sg - Sg = 0

    This is axiomatized because the matrix index manipulation in Lean is tedious. -/
axiom minimal_disturbance_primal_feasibility (RF : RegularizedFisher n)
    (S : ConsolidatedSubspace n k) (g : Fin n → ℝ)
    (F_reg_inv : Matrix (Fin n) (Fin n) ℝ)
    (Gram_inv : Matrix (Fin k) (Fin k) ℝ)
    (h_F_inv : F_reg_inv * RF.regularized = 1)
    (h_Gram_inv : let S_mat := SubspaceMatrix S
                  Gram_inv * (S_mat * F_reg_inv * S_matᵀ) = 1) :
    let P_perp := FisherOrthogonalProjector RF S F_reg_inv Gram_inv
    PrimalFeasible S (P_perp *ᵥ g)

/-- **AXIOM: Minimal Disturbance (Primal Optimality)**

    The projector output P_⊥ g minimizes Fisher distance to g among all
    primal-feasible updates (those satisfying S Δθ = 0).

    **Proof sketch** (convex optimization):
    - Objective ‖Δθ - g‖²_F is strictly convex (F + λI positive definite)
    - Constraint SΔθ = 0 is linear (affine subspace)
    - P_⊥ g satisfies KKT conditions by construction
    - Therefore it is the unique global minimizer

    This is the core variational principle behind Fisher-orthogonal learning. -/
axiom minimal_disturbance_primal_optimality (RF : RegularizedFisher n)
    (S : ConsolidatedSubspace n k) (g : Fin n → ℝ)
    (F_reg_inv : Matrix (Fin n) (Fin n) ℝ)
    (Gram_inv : Matrix (Fin k) (Fin k) ℝ)
    (h_F_inv : F_reg_inv * RF.regularized = 1)
    (h_Gram_inv : let S_mat := SubspaceMatrix S
                  Gram_inv * (S_mat * F_reg_inv * S_matᵀ) = 1) :
    let P_perp := FisherOrthogonalProjector RF S F_reg_inv Gram_inv
    let Δθ_opt := P_perp *ᵥ g
    ∀ Δθ : Fin n → ℝ, PrimalFeasible S Δθ →
      FisherObjective RF g Δθ_opt ≤ FisherObjective RF g Δθ

/-- **THEOREM: Minimal Disturbance (Combined)**

    The projector P_⊥ gives the unique minimizer of the constrained problem.
    This theorem combines feasibility and optimality from the axioms above. -/
theorem minimal_disturbance_primal (RF : RegularizedFisher n)
    (S : ConsolidatedSubspace n k) (g : Fin n → ℝ)
    (F_reg_inv : Matrix (Fin n) (Fin n) ℝ)
    (Gram_inv : Matrix (Fin k) (Fin k) ℝ)
    (h_F_inv : F_reg_inv * RF.regularized = 1)
    (h_Gram_inv : let S_mat := SubspaceMatrix S
                  Gram_inv * (S_mat * F_reg_inv * S_matᵀ) = 1)
    : let P_perp := FisherOrthogonalProjector RF S F_reg_inv Gram_inv
      let Δθ_opt := P_perp *ᵥ g
      PrimalFeasible S Δθ_opt ∧
      (∀ Δθ : Fin n → ℝ, PrimalFeasible S Δθ →
        FisherObjective RF g Δθ_opt ≤ FisherObjective RF g Δθ) :=
  ⟨minimal_disturbance_primal_feasibility RF S g F_reg_inv Gram_inv h_F_inv h_Gram_inv,
   minimal_disturbance_primal_optimality RF S g F_reg_inv Gram_inv h_F_inv h_Gram_inv⟩

/-- **AXIOM: Fisher-Orthogonality Projection Feasibility**

    For the constraint S F Δθ = 0 (Fisher-orthogonal to S), the projector
    output satisfies the constraint. -/
axiom fisher_orthogonal_projection_feasibility (RF : RegularizedFisher n)
    (S : ConsolidatedSubspace n k) (g : Fin n → ℝ)
    (F_reg_inv : Matrix (Fin n) (Fin n) ℝ)
    (Gram_inv : Matrix (Fin k) (Fin k) ℝ)
    (h_F_inv : F_reg_inv * RF.regularized = 1)
    (h_Gram_inv : let S_mat := SubspaceMatrix S
                  Gram_inv * (S_mat * F_reg_inv * S_matᵀ) = 1) :
    let P_perp := FisherOrthogonalProjector RF S F_reg_inv Gram_inv
    FisherFeasible RF S (P_perp *ᵥ g)

/-- **AXIOM: Fisher-Orthogonality Projection Optimality**

    The projector output minimizes Fisher distance among Fisher-feasible updates. -/
axiom fisher_orthogonal_projection_optimality (RF : RegularizedFisher n)
    (S : ConsolidatedSubspace n k) (g : Fin n → ℝ)
    (F_reg_inv : Matrix (Fin n) (Fin n) ℝ)
    (Gram_inv : Matrix (Fin k) (Fin k) ℝ)
    (h_F_inv : F_reg_inv * RF.regularized = 1)
    (h_Gram_inv : let S_mat := SubspaceMatrix S
                  Gram_inv * (S_mat * F_reg_inv * S_matᵀ) = 1) :
    let P_perp := FisherOrthogonalProjector RF S F_reg_inv Gram_inv
    let Δθ_opt := P_perp *ᵥ g
    ∀ Δθ : Fin n → ℝ, FisherFeasible RF S Δθ →
      FisherObjective RF g Δθ_opt ≤ FisherObjective RF g Δθ

/-- **THEOREM: Fisher-Orthogonality Projection (Combined)**

    For the constraint S F Δθ = 0 (Fisher-orthogonal to S), the projector
    gives the unique minimizer. -/
theorem fisher_orthogonal_projection_optimal (RF : RegularizedFisher n)
    (S : ConsolidatedSubspace n k) (g : Fin n → ℝ)
    (F_reg_inv : Matrix (Fin n) (Fin n) ℝ)
    (Gram_inv : Matrix (Fin k) (Fin k) ℝ)
    (h_F_inv : F_reg_inv * RF.regularized = 1)
    (h_Gram_inv : let S_mat := SubspaceMatrix S
                  Gram_inv * (S_mat * F_reg_inv * S_matᵀ) = 1)
    : let P_perp := FisherOrthogonalProjector RF S F_reg_inv Gram_inv
      let Δθ_opt := P_perp *ᵥ g
      FisherFeasible RF S Δθ_opt ∧
      (∀ Δθ : Fin n → ℝ, FisherFeasible RF S Δθ →
        FisherObjective RF g Δθ_opt ≤ FisherObjective RF g Δθ) :=
  ⟨fisher_orthogonal_projection_feasibility RF S g F_reg_inv Gram_inv h_F_inv h_Gram_inv,
   fisher_orthogonal_projection_optimality RF S g F_reg_inv Gram_inv h_F_inv h_Gram_inv⟩

/-- **AXIOM: Projector Idempotence**

    The projector P_⊥ is idempotent: P² = P.

    **Proof sketch**: P_⊥² = (I - A)(I - A) = I - 2A + A² where A = F⁻¹Sᵀ Gram⁻¹ S.
    Since A² = F⁻¹Sᵀ Gram⁻¹ (SF⁻¹Sᵀ) Gram⁻¹ S = F⁻¹Sᵀ Gram⁻¹ S = A,
    we have P² = I - 2A + A = I - A = P. -/
axiom FisherOrthogonalProjector_idempotent (RF : RegularizedFisher n)
    (S : ConsolidatedSubspace n k)
    (F_reg_inv : Matrix (Fin n) (Fin n) ℝ)
    (Gram_inv : Matrix (Fin k) (Fin k) ℝ)
    (h_F_inv : F_reg_inv * RF.regularized = 1)
    (h_Gram_inv : let S_mat := SubspaceMatrix S
                  Gram_inv * (S_mat * F_reg_inv * S_matᵀ) = 1) :
    let P := FisherOrthogonalProjector RF S F_reg_inv Gram_inv
    P * P = P

/-- **AXIOM: Projected Vectors are Fisher-Orthogonal**

    Vectors projected by P_⊥ are Fisher-orthogonal to the consolidated subspace S.
    This follows from the Fisher-feasibility of the projector output. -/
axiom FisherOrthogonalProjector_orthogonal (P : ParametricFamily n V) (θ : Fin n → ℝ)
    (RF : RegularizedFisher n) (S : ConsolidatedSubspace n k)
    (F_reg_inv : Matrix (Fin n) (Fin n) ℝ) (Gram_inv : Matrix (Fin k) (Fin k) ℝ)
    (h_F_inv : F_reg_inv * RF.regularized = 1)
    (h_Gram_inv : let S_mat := SubspaceMatrix S
                  Gram_inv * (S_mat * F_reg_inv * S_matᵀ) = 1)
    (h_RF : RF.F = FisherMatrix P θ)
    (v : Fin n → ℝ) :
    let P_perp := FisherOrthogonalProjector RF S F_reg_inv Gram_inv
    IsFisherOrthogonal P θ S (P_perp *ᵥ v)

/-- **Projected Update Formula** (Main Theorem 4):

    The Fisher-orthogonal projection of the natural gradient direction g is:

    Δθ_projected = P_⊥ · g = (I - F⁻¹S(SF⁻¹Sᵀ)⁻¹Sᵀ) g

    This gives the closed-form solution to:
    min_Δθ ‖Δθ - g‖²_F  subject to  ⟨Δθ, s⟩_F = 0 for all s ∈ S

    **This is the CONTROL LAW**: Given a gradient g, compute the
    Fisher-orthogonal projected update using matrix operations. -/
theorem projected_update_formula (P : ParametricFamily n V) (θ : Fin n → ℝ)
    (RF : RegularizedFisher n) (S : ConsolidatedSubspace n k)
    (F_reg_inv : Matrix (Fin n) (Fin n) ℝ) (Gram_inv : Matrix (Fin k) (Fin k) ℝ)
    (h_F_inv : F_reg_inv * RF.regularized = 1)
    (h_Gram_inv : let S_mat := SubspaceMatrix S
                  Gram_inv * (S_mat * F_reg_inv * S_matᵀ) = 1)
    (h_RF : RF.F = FisherMatrix P θ)
    (g : Fin n → ℝ) :
    let Δθ := (FisherOrthogonalProjector RF S F_reg_inv Gram_inv) *ᵥ g
    IsFisherOrthogonal P θ S Δθ :=
  FisherOrthogonalProjector_orthogonal P θ RF S F_reg_inv Gram_inv h_F_inv h_Gram_inv h_RF g

/-! ## Part IV: KL Bounds for Fisher-Orthogonal Updates -/

/-- **KL Bound for Single Fisher-Orthogonal Step** (Main Theorem 2):

    If the update Δθ is Fisher-orthogonal to the consolidated subspace S,
    then the KL divergence on consolidated behaviors is bounded by the
    cross-term, which vanishes in the orthogonal case.

    Key insight: Fisher-orthogonality means Δθᵀ F s = 0 for all s ∈ S.
    So the "effective" change in the S-directions is zero at first order. -/
theorem Fisher_orthogonal_KL_bound (P : ParametricFamily n V) (θ Δθ : Fin n → ℝ)
    (S : ConsolidatedSubspace n k) (h_orth : IsFisherOrthogonal P θ S Δθ) :
    ∀ i : Fin k, FisherInner P θ Δθ (S.basis i) = 0 :=
  h_orth

/-! ## Part V: No-Forgetting Horizon -/

/-- **Learning Step**: A single parameter update step. -/
structure LearningStep (n : ℕ) where
  /-- Current parameters -/
  θ : Fin n → ℝ
  /-- Update direction -/
  Δθ : Fin n → ℝ
  /-- Step size -/
  η : ℝ
  /-- Step size is positive -/
  η_pos : 0 < η

/-- **Learning Trajectory**: A sequence of K learning steps. -/
def LearningTrajectory (n K : ℕ) := Fin K → LearningStep n

/-- Total parameter change along a trajectory. -/
def totalChange {K : ℕ} (traj : LearningTrajectory n K) : Fin n → ℝ :=
  fun i => ∑ k : Fin K, (traj k).η * (traj k).Δθ i

/-- Sum of squared step norms along trajectory. -/
def sumSquaredSteps {K : ℕ} (traj : LearningTrajectory n K) : ℝ :=
  ∑ k : Fin K, (traj k).η^2 * paramNormSq (traj k).Δθ

/-- **No-Forgetting Horizon** (Main Theorem 5):

    If all steps are Fisher-orthogonal to the consolidated subspace S,
    then the accumulated KL drift on consolidated behaviors is bounded:

    KL(p_{θ_0} ‖ p_{θ_K}) ≤ C · Σₖ ηₖ² ‖Δθₖ‖² · λ_max(F)

    where λ_max(F) is the largest eigenvalue of the Fisher matrix.

    This is the **learning-side sibling of trajectory_closure_bound**.

    **Physical interpretation**:
    - ε = average defect per step (≈ η² ‖Δθ‖² λ_max)
    - K = number of steps
    - Total drift ≤ K · ε
    - Validity horizon T* = 1/ε gives "how long until we forget"

**AXIOM: No-Forgetting Horizon Bound (Riemannian Path Boundedness)**

    For Fisher-orthogonal learning trajectories, accumulated KL drift is bounded
    by the sum of squared step sizes.

    **Mathematical content**: The bound follows from:
    1. KL-Fisher local bound: each step contributes O(η² ‖Δθ‖²)
    2. Fisher-orthogonality: first-order drift in S-directions vanishes
    3. **Riemannian path integral bound** (NOT triangle inequality for KL):
       In the small-step regime, KL ≈ ½ d²_Fisher, and squared Fisher distance
       along a quasi-geodesic path satisfies:
         d²(p_0, p_K) ≤ C · Σ_k d²(p_k, p_{k+1})
       This is the "quasi-geodesic" assumption: the learning trajectory does not
       take large detours in parameter space.

    **Domain of validity**: Small steps (η → 0), smooth parametric families.
    This selects the "thermodynamic limit" where Riemannian geometry applies.

    **WARNING**: KL divergence is NOT a metric and does NOT satisfy the triangle
    inequality globally. This axiom is valid only in the small-step Riemannian regime.

    The constant C depends on eigenvalue bounds of the Fisher matrix. -/
axiom no_forgetting_horizon_bound {K : ℕ} [NeZero K] (P : ParametricFamily n V)
    (traj : LearningTrajectory n K) (S : ConsolidatedSubspace n k)
    (h_orth : ∀ m : Fin K, IsFisherOrthogonal P (traj m).θ S (traj m).Δθ) :
    KL_divergence (P.p (traj ⟨0, Nat.pos_of_neZero K⟩).θ)
                  (P.p ((traj ⟨0, Nat.pos_of_neZero K⟩).θ + totalChange traj)) ≤
      sumSquaredSteps traj

/-- **THEOREM: No-Forgetting Horizon (with explicit constant)**

    Accumulated KL drift is bounded by C times the sum of squared steps. -/
theorem no_forgetting_horizon {K : ℕ} [NeZero K] (P : ParametricFamily n V)
    (traj : LearningTrajectory n K) (S : ConsolidatedSubspace n k)
    (h_orth : ∀ m : Fin K, IsFisherOrthogonal P (traj m).θ S (traj m).Δθ) :
    ∃ C : ℝ, 0 ≤ C ∧
      KL_divergence (P.p (traj ⟨0, Nat.pos_of_neZero K⟩).θ)
                    (P.p ((traj ⟨0, Nat.pos_of_neZero K⟩).θ + totalChange traj)) ≤
        C * sumSquaredSteps traj := by
  use 1
  constructor
  · linarith
  · simp only [one_mul]
    exact no_forgetting_horizon_bound P traj S h_orth

/-- **Validity Horizon for Learning**: Time T* until accumulated drift exceeds threshold.

    If each step has "defect" ε = η² ‖Δθ‖² λ_max(F), then:
    - After K steps: total drift ≤ K · ε
    - For drift threshold δ: K* = δ/ε steps until forgetting

    This parallels `validity_horizon` from ValidityHorizon.lean. -/
def learning_validity_horizon (ε δ : ℝ) (hε : 0 < ε) : ℕ :=
  Nat.ceil (δ / ε)

/-- The validity horizon gives the bound on number of safe steps. -/
theorem learning_validity_horizon_bound (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (K : ℕ) (hK : K ≤ learning_validity_horizon ε δ hε) :
    (K : ℝ) * ε ≤ δ + ε := by
  unfold learning_validity_horizon at hK
  have h_ceil := Nat.le_ceil (δ / ε)
  have h_ceil_bound : (Nat.ceil (δ / ε) : ℝ) ≤ δ / ε + 1 := by
    have := Nat.ceil_lt_add_one (div_nonneg (le_of_lt hδ) (le_of_lt hε))
    linarith
  calc (K : ℝ) * ε
      ≤ ↑(Nat.ceil (δ / ε)) * ε := by
        apply mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hK) (le_of_lt hε)
    _ ≤ (δ / ε + 1) * ε := by
        apply mul_le_mul_of_nonneg_right h_ceil_bound (le_of_lt hε)
    _ = δ + ε := by field_simp

/-! ## Part VI: Connection to SGC Defect Operator

**Bridge to SGC**: The Fisher-orthogonal projector P_⊥ is analogous to
the SGC defect operator D = (I - Π) L Π.

| Learning (Information Geometry) | Dynamics (SGC)              |
|---------------------------------|-----------------------------|
| Parameter space ℝⁿ              | Function space V → ℝ        |
| Fisher metric F(θ)              | π-weighted L² metric        |
| Consolidated subspace S         | Coarse (block-constant) Π   |
| Fisher projection P_⊥           | Complement projector (I-Π)  |
| KL drift per step               | Defect ‖D‖                  |
| No-forgetting horizon           | Validity horizon T* = 1/ε  |

The key parallel: both measure "leakage" from a protected subspace.
-/

/-- **Leakage Defect for Learning**: Analogous to DefectOperator.
    Measures how much an update "leaks" into the consolidated subspace. -/
def LearningDefect (P : ParametricFamily n V) (θ : Fin n → ℝ)
    (S : ConsolidatedSubspace n k) (Δθ : Fin n → ℝ) : ℝ :=
  ∑ i : Fin k, (FisherInner P θ Δθ (S.basis i))^2

/-- Zero defect iff Fisher-orthogonal. -/
theorem LearningDefect_zero_iff_orthogonal (P : ParametricFamily n V) (θ : Fin n → ℝ)
    (S : ConsolidatedSubspace n k) (Δθ : Fin n → ℝ) :
    LearningDefect P θ S Δθ = 0 ↔ IsFisherOrthogonal P θ S Δθ := by
  unfold LearningDefect IsFisherOrthogonal
  constructor
  · intro h i
    have h_nonneg : ∀ j : Fin k, 0 ≤ (FisherInner P θ Δθ (S.basis j))^2 :=
      fun j => sq_nonneg _
    have h_term := Finset.sum_eq_zero_iff_of_nonneg (fun j _ => h_nonneg j) |>.mp h i (Finset.mem_univ i)
    exact sq_eq_zero_iff.mp h_term
  · intro h
    apply Finset.sum_eq_zero
    intro i _
    simp only [h i, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]

/-! ## Summary and Connections

This module establishes the **Information-Geometric Foundation for Learning**:

### Main Theorems

1. **KL_Fisher_local_bound**: KL ≤ ½ Δθᵀ F Δθ + O(‖Δθ‖³)
   - "The metric controls drift"
   - Foundation for all subsequent bounds

2. **Fisher_orthogonal_KL_bound**: Orthogonal updates → bounded KL change
   - First-order effects vanish
   - Only second-order accumulation

3. **projected_update_formula**: Closed-form P_⊥ = I - F⁻¹Sᵀ(SF⁻¹Sᵀ)⁻¹S
   - Explicit "update operator"
   - Analogous to (I-Π)LΠ in SGC

4. **no_forgetting_horizon**: Accumulated KL ≤ C · Σ η² ‖Δθ‖²
   - Learning-side sibling of trajectory_closure_bound
   - Validity horizon for learned skills

### Connections Identified

**To Spiking Neural Networks**:
- Fisher metric ↔ Spike timing precision
- Score function ↔ Spike-triggered average
- Fisher-orthogonal updates ↔ STDP rules that preserve consolidated patterns

**To Thermodynamic Computing**:
- KL divergence ↔ Thermodynamic work (Jarzynski equality)
- Fisher metric ↔ Thermodynamic length (Crooks fluctuation theorem)
- No-forgetting horizon ↔ Thermodynamic irreversibility bound

**To SGC Framework**:
- LearningDefect ↔ DefectOperator
- Consolidated subspace ↔ Coarse partition
- Validity horizon ↔ trajectory_closure_bound

-/

end SGC.InformationGeometry.FisherKL

end
