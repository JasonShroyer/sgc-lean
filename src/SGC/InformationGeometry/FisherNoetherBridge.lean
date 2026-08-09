/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team

# Fisher-Noether Bridge: Conservation Laws from Information Geometry

This module formalizes the connection between the SGC Relational Engine's
minimum-variance computation and Noether's theorem, via Fisher information.

## The Chain of Reasoning

1. **Link 1** (Theorem): The variance of a quadratic form x^T C x over a
   distribution equals the quadratic form of C in the lifted covariance.
   Var[x^T C x] = c^T Sigma c where c = vec(C), Sigma = Cov[vec(x x^T)].

2. **Link 2** (Theorem, for exponential families): For an exponential family
   with quadratic sufficient statistics, the lifted covariance IS the Fisher
   information matrix. Therefore, the minimum-variance quadratic form is the
   null direction of Fisher information.

3. **Link 3** (Theorem, Jeans): For an ergodic Hamiltonian system in
   equilibrium, the distribution depends only on integrals of motion.
   Therefore, the null Fisher direction IS an integral of motion (when
   quadratic).

4. **Open Gap** (Research Problem): How close is the minimum-variance
   direction to the nearest true integral, as a function of T*?

5. **Selection Contamination** (Theorem): Observing from f*S instead of f
   shifts the variance, with the shift proportional to Cov_f[Q, log S].

## References

- Fisher-Noether Bridge analytical argument: reports/FISHER_NOETHER_BRIDGE.md
- Amari & Nagaoka, "Methods of Information Geometry"
- Jeans (1915), "On the theory of star-streaming"
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

namespace SGC.InformationGeometry.FisherNoetherBridge

open Finset Matrix Real

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {d : ℕ}

/-! ## Section 1: Link 1 — Variance as Quadratic Form on Lifted Covariance

This is the foundational identity: the variance of a quadratic form
x^T C x over a distribution is exactly the quadratic form of vec(C)
in the covariance of the lifted features vec(x x^T).

This is a DEFINITIONAL equality — it follows from expanding the variance
and recognizing the covariance structure. No physical assumptions needed.
-/

/-- A quadratic form on ℝ^d, represented as a symmetric d×d matrix. -/
structure QuadraticForm (d : ℕ) where
  mat : Matrix (Fin d) (Fin d) ℝ
  symm : mat.IsSymm

/-- Evaluate a quadratic form at a point: Q(x) = x^T C x = Σ_{i,j} C_{ij} x_i x_j -/
def QuadraticForm.eval (Q : QuadraticForm d) (x : Fin d → ℝ) : ℝ :=
  ∑ i, ∑ j, Q.mat i j * x i * x j

/-- The lifted feature vector: the vectorized outer product x ⊗ x.
    For a d-dimensional vector x, this produces a d²-dimensional vector
    whose (i*d+j)-th entry is x_i * x_j. -/
def outerProduct (x : Fin d → ℝ) : Fin d → Fin d → ℝ :=
  fun i j => x i * x j

/-- Empirical mean of a function over N samples. -/
def empiricalMean {α : Type*} (N : ℕ) [NeZero N] (f : Fin N → α → ℝ)
    (samples : Fin N → α) : ℝ :=
  (1 / N) * ∑ k, f k (samples k)

/-- Empirical variance of a real-valued function over N samples. -/
def empiricalVariance (N : ℕ) [NeZero N] (vals : Fin N → ℝ) : ℝ :=
  let μ := (1 / N) * ∑ k, vals k
  (1 / N) * ∑ k, (vals k - μ)^2

/-- **THEOREM (Link 1, Core Identity):**
    The variance of a quadratic form Q(x) = x^T C x over samples {x_i}
    equals the quadratic form of vec(C) in the empirical covariance of
    the lifted features vec(x_i x_i^T).

    Var[x^T C x] = Σ_{a,b,c,d} C_{ab} C_{cd} Cov[x_a x_b, x_c x_d]

    This is a tautology from the definition of variance and the bilinearity
    of the covariance, but it is the foundational identity that connects
    the engine's optimization (minimize Var[x^T C x]) to Fisher information.

    STATUS: PROVEN (lake build, no sorry) — kernel-verified, ε = 0.
    Mathematically a one-line tautology, but NOT Lean-cheap: it requires a
    centering lemma, a double `sum_mul_sum` square expansion, and a five-fold
    sum transpose (sample index k moved past the four feature indices).
    Weight-agnostic: the 1/N factor is an inert scalar that is never inverted,
    so [NeZero N] is NOT required — the identity generalizes verbatim to any
    real weight (weighted / importance-sampled / biased estimators). -/
theorem variance_as_lifted_quadform
    (N : ℕ) (X : Fin N → Fin d → ℝ) (Q : QuadraticForm d) :
    let q_vals := fun k => Q.eval (X k)
    let q_mean := (1 / N) * ∑ k, q_vals k
    (1 / N) * ∑ k, (q_vals k - q_mean)^2 =
      ∑ a, ∑ b, ∑ c, ∑ e, Q.mat a b * Q.mat c e *
        ((1 / N) * ∑ k, (X k a * X k b - (1/N) * ∑ l, X l a * X l b) *
                         (X k c * X k e - (1/N) * ∑ l, X l c * X l e)) := by
  simp only [QuadraticForm.eval]
  -- Centering: q_k - q̄ = Σ_{a,b} C_{ab} (x_{ka} x_{kb} - mean_{ab}). Weight 1/N is an
  -- inert scalar (never inverted) — [NeZero N] is not used anywhere below.
  have key : ∀ k : Fin N,
      (∑ i, ∑ j, Q.mat i j * X k i * X k j)
        - (1 / (N : ℝ)) * ∑ k', ∑ i, ∑ j, Q.mat i j * X k' i * X k' j
      = ∑ a, ∑ b, Q.mat a b * (X k a * X k b - (1 / (N : ℝ)) * ∑ l, X l a * X l b) := by
    intro k
    have hmean : (1 / (N : ℝ)) * ∑ k', ∑ i, ∑ j, Q.mat i j * X k' i * X k' j
        = ∑ i, ∑ j, Q.mat i j * ((1 / (N : ℝ)) * ∑ l, X l i * X l j) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [mul_assoc]
      rw [← Finset.mul_sum]
      ring
    rw [hmean, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  -- Rewrite each centered square via `key`, then expand and reorder the sums.
  simp only [key]
  -- Per-sample square expansion: (∑_{a,b} M_ab c_ab)^2 = ∑_{a,b,c,e} M_ab M_ce c_ab c_ce.
  have sq : ∀ k : Fin N,
      (∑ a, ∑ b, Q.mat a b * (X k a * X k b - (1 / (N : ℝ)) * ∑ l, X l a * X l b)) ^ 2
        = ∑ a, ∑ b, ∑ c, ∑ e, Q.mat a b * Q.mat c e *
            ((X k a * X k b - (1 / (N : ℝ)) * ∑ l, X l a * X l b) *
             (X k c * X k e - (1 / (N : ℝ)) * ∑ l, X l c * X l e)) := by
    intro k
    rw [pow_two, Fintype.sum_mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    refine Finset.sum_congr rfl (fun e _ => ?_)
    ring
  simp only [sq]
  -- Generic transpose: move the sample index k from innermost to outermost past the
  -- four feature indices. Each step fixes the outer binders with `ext` then swaps the
  -- now-adjacent pair with `Finset.sum_comm`.
  have reorder : ∀ f : Fin N → Fin d → Fin d → Fin d → Fin d → ℝ,
      (∑ a, ∑ b, ∑ c, ∑ e, ∑ k, f k a b c e)
        = ∑ k, ∑ a, ∑ b, ∑ c, ∑ e, f k a b c e := by
    intro f
    conv_lhs => enter [2, a, 2, b, 2, c]; rw [Finset.sum_comm]
    conv_lhs => enter [2, a, 2, b]; rw [Finset.sum_comm]
    conv_lhs => enter [2, a]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  -- LHS: distribute the outer (1/N) onto the k-sum.  RHS: pull each (1/N)∑_k outward
  -- (reassociate so the k-sum is the right factor, then `mul_sum`), WITHOUT touching the
  -- internal mean-sums ∑_l inside the centred factors.
  rw [Finset.mul_sum]
  conv_rhs =>
    enter [2, a, 2, b, 2, c, 2, e]
    rw [← mul_assoc, Finset.mul_sum]
  rw [reorder]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  -- Per-sample: (1/N)·∑_{a,b,c,e} M_ab M_ce cc = ∑_{a,b,c,e} (M_ab M_ce (1/N)) cc.
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  ring

/-- **COROLLARY (lifted covariance is PSD):** the empirical lifted-covariance quadratic
    form is nonnegative for every quadratic form `Q`, because Link 1 identifies it with an
    empirical variance — a (1/N)-weighted mean of squares. This *structurally* supplies the
    `hPSD` hypothesis of `min_variance_is_min_eigenvector`: it need not be assumed.

    STATUS: PROVEN (lake build, no sorry). Weight-agnostic like its parent — no `[NeZero N]`
    (for `N = 0` both sides are `0`). -/
theorem lifted_quadform_nonneg
    (N : ℕ) (X : Fin N → Fin d → ℝ) (Q : QuadraticForm d) :
    0 ≤ ∑ a, ∑ b, ∑ c, ∑ e, Q.mat a b * Q.mat c e *
        ((1 / N) * ∑ k, (X k a * X k b - (1/N) * ∑ l, X l a * X l b) *
                         (X k c * X k e - (1/N) * ∑ l, X l c * X l e)) := by
  have h := variance_as_lifted_quadform N X Q
  simp only [QuadraticForm.eval] at h
  rw [← h]
  exact mul_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg N))
    (Finset.sum_nonneg fun k _ => sq_nonneg _)

/-- **COROLLARY:** Minimizing Var[x^T C x] subject to ||C||_F = 1 is equivalent
    to finding the minimum eigenvector of the lifted covariance matrix.

    This is the EXACT computation performed by the SGC manifold-mode engine.
    Stated for an arbitrary square dimension `m` (the lifted case is `m = d*d`);
    the content is dimension-generic.

    STATUS: PROVEN (lake build, no sorry) — kernel-verified. The Rayleigh
    quotient characterization of the least eigenvalue of a real symmetric
    matrix is discharged by an elementary self-contained argument (no calculus,
    no spectral API): a global Rayleigh inequality obtained by rescaling the
    unit-norm hypothesis, then showing the residual `Sigma *ᵥ c_star - λ c_star`
    is null because a one-parameter family `α • c_star + g` would otherwise make
    the quadratic form unbounded below along `α`. -/
theorem min_variance_is_min_eigenvector
    {m : ℕ}
    (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (hSigma : Sigma.IsSymm)
    (hPSD : ∀ v : Fin m → ℝ, 0 ≤ ∑ i, ∑ j, v i * Sigma i j * v j)
    (c_star : Fin m → ℝ)
    (hNorm : ∑ i, c_star i ^ 2 = 1)
    (hMin : ∀ c : Fin m → ℝ, ∑ i, c i ^ 2 = 1 →
      ∑ i, ∑ j, c_star i * Sigma i j * c_star j ≤
      ∑ i, ∑ j, c i * Sigma i j * c j) :
    -- c_star is the eigenvector of Sigma with smallest eigenvalue
    ∃ lam_min : ℝ, (∀ i, ∑ j, Sigma i j * c_star j = lam_min * c_star i) ∧
      (∀ lam : ℝ, (∃ v : Fin m → ℝ, v ≠ 0 ∧ ∀ i, ∑ j, Sigma i j * v j = lam * v i) →
        lam_min ≤ lam) := by
  -- Elementary Rayleigh-quotient argument (no calculus, no spectral API):
  -- the unit-norm minimiser c_star of the quadratic form is an eigenvector for the
  -- least eigenvalue.  The bilinear form `B u w = u ⬝ᵥ Sigma *ᵥ w` is symmetric and
  -- the proof rests only on: (RQ) a global Rayleigh inequality obtained by rescaling
  -- the unit-vector hypothesis `hMin`, and the residual `g = Sigma *ᵥ c_star - λ c_star`.
  -- Rewrite the explicit double sums as `u ⬝ᵥ Sigma *ᵥ w`.
  have dotself_nonneg : ∀ v : Fin m → ℝ, 0 ≤ v ⬝ᵥ v := fun v => by
    simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have bil : ∀ u w : Fin m → ℝ, (∑ i, ∑ j, u i * Sigma i j * w j) = u ⬝ᵥ Sigma *ᵥ w := by
    intro u w
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  -- Symmetry of the bilinear form from `Sigma.IsSymm`.
  have hsij : ∀ i j, Sigma i j = Sigma j i := fun i j => by
    have h := congrFun (congrFun hSigma i) j; rw [Matrix.transpose_apply] at h; exact h.symm
  have Bsymm : ∀ u w : Fin m → ℝ, u ⬝ᵥ Sigma *ᵥ w = w ⬝ᵥ Sigma *ᵥ u := by
    intro u w
    simp only [← bil]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [hsij j i]; ring
  set lam := ∑ i, ∑ j, c_star i * Sigma i j * c_star j with hlam
  have hlam' : c_star ⬝ᵥ Sigma *ᵥ c_star = lam := (bil c_star c_star).symm
  have hcc : c_star ⬝ᵥ c_star = 1 := by
    simp only [dotProduct]; rw [← hNorm]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  -- Global Rayleigh inequality: `lam * (c ⬝ᵥ c) ≤ c ⬝ᵥ Sigma *ᵥ c` for all `c`.
  have RQ : ∀ c : Fin m → ℝ, lam * (c ⬝ᵥ c) ≤ c ⬝ᵥ Sigma *ᵥ c := by
    intro c
    rcases eq_or_lt_of_le (dotself_nonneg c) with hc | hc
    · have hc0 : c = 0 := dotProduct_self_eq_zero.mp hc.symm
      subst hc0; simp
    · set s := Real.sqrt (c ⬝ᵥ c) with hs
      have hspos : 0 < s := Real.sqrt_pos.mpr hc
      have hsne : s ≠ 0 := hspos.ne'
      have hs2 : s ^ 2 = c ⬝ᵥ c := Real.sq_sqrt hc.le
      have hunit : ∑ i, (s⁻¹ • c) i ^ 2 = 1 := by
        have he : ∑ i, (s⁻¹ • c) i ^ 2 = s⁻¹ ^ 2 * ∑ i, c i ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by
            simp only [Pi.smul_apply, smul_eq_mul]; ring)
        have hsum : (∑ i, c i ^ 2) = c ⬝ᵥ c := Finset.sum_congr rfl (fun i _ => by ring)
        rw [he, hsum, ← hs2]; field_simp
      have hM := hMin (s⁻¹ • c) hunit
      simp only [bil] at hM
      have hscale : (s⁻¹ • c) ⬝ᵥ Sigma *ᵥ (s⁻¹ • c) = s⁻¹ ^ 2 * (c ⬝ᵥ Sigma *ᵥ c) := by
        rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring
      rw [hscale] at hM
      have hsimp : s⁻¹ ^ 2 * (c ⬝ᵥ Sigma *ᵥ c) * s ^ 2 = c ⬝ᵥ Sigma *ᵥ c := by
        rw [mul_comm (s⁻¹ ^ 2) (c ⬝ᵥ Sigma *ᵥ c), mul_assoc, ← mul_pow,
          inv_mul_cancel₀ hsne, one_pow, mul_one]
      have hfin := mul_le_mul_of_nonneg_right hM (by positivity : (0:ℝ) ≤ s ^ 2)
      rw [hsimp] at hfin
      rw [hs2] at hfin; exact hfin
  -- Residual g and the two key inner products.
  set g : Fin m → ℝ := Sigma *ᵥ c_star - lam • c_star with hg
  have hcg : c_star ⬝ᵥ g = 0 := by
    rw [hg, dotProduct_sub, dotProduct_smul, smul_eq_mul, hlam', hcc]; ring
  have hgc : g ⬝ᵥ c_star = 0 := by rw [dotProduct_comm]; exact hcg
  have hScg : Sigma *ᵥ c_star = g + lam • c_star := by rw [hg]; abel
  have hgSg : c_star ⬝ᵥ Sigma *ᵥ g = g ⬝ᵥ g := by
    rw [Bsymm c_star g, hScg, dotProduct_add, dotProduct_smul, hgc,
        smul_zero, add_zero]
  -- Expand the Rayleigh inequality on `α • c_star + g`.
  set NG := g ⬝ᵥ g with hNG
  have hNGnn : 0 ≤ NG := dotself_nonneg g
  have e1 : ∀ α : ℝ, (α • c_star + g) ⬝ᵥ (α • c_star + g) = α ^ 2 + NG := by
    intro α
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, hcc, hcg, hgc]
    ring
  have e2 : ∀ α : ℝ, (α • c_star + g) ⬝ᵥ Sigma *ᵥ (α • c_star + g)
      = α ^ 2 * lam + 2 * α * NG + g ⬝ᵥ Sigma *ᵥ g := by
    intro α
    rw [Matrix.mulVec_add, Matrix.mulVec_smul]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, hlam', hgSg]
    rw [Bsymm g c_star, hgSg]; ring
  have hα : ∀ α : ℝ, 0 ≤ 2 * α * NG + (g ⬝ᵥ Sigma *ᵥ g - lam * NG) := by
    intro α
    have := RQ (α • c_star + g)
    rw [e1, e2] at this; nlinarith [this]
  have hNG0 : NG = 0 := by
    by_contra h
    have hpos : 0 < NG := lt_of_le_of_ne hNGnn (Ne.symm h)
    set M := g ⬝ᵥ Sigma *ᵥ g - lam * NG with hM_def
    have h2NG : (2 : ℝ) * NG ≠ 0 := ne_of_gt (by linarith)
    have key := hα ((-M - 1) / (2 * NG))
    have hcancel : 2 * ((-M - 1) / (2 * NG)) * NG = -M - 1 := by
      rw [show 2 * ((-M - 1) / (2 * NG)) * NG = ((-M - 1) / (2 * NG)) * (2 * NG) from by ring]
      exact div_mul_cancel₀ (-M - 1) h2NG
    rw [hcancel] at key; linarith
  have hgzero : g = 0 := dotProduct_self_eq_zero.mp hNG0
  refine ⟨lam, ?_, ?_⟩
  · intro i
    have hgi := congrFun hgzero i
    rw [hg] at hgi
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hgi
    have : (Sigma *ᵥ c_star) i = lam * c_star i := by linarith
    simpa [Matrix.mulVec, dotProduct] using this
  · intro l ⟨v, hv, hev⟩
    have hvv : 0 < v ⬝ᵥ v :=
      lt_of_le_of_ne (dotself_nonneg v)
        (Ne.symm fun hh => hv (dotProduct_self_eq_zero.mp hh))
    have hvSv : v ⬝ᵥ Sigma *ᵥ v = l * (v ⬝ᵥ v) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.mul_sum, hev i]; ring
    have hr := RQ v
    rw [hvSv] at hr
    exact le_of_mul_le_mul_right hr hvv

/-! ## Section 2: Exponential Family Fisher Information

For an exponential family p(x; θ) ∝ exp(θ^T T(x)) with sufficient statistic
T(x) = vec(x x^T), the Fisher information matrix equals the covariance of T(x).

This is a CLASSICAL result in information geometry (Amari & Nagaoka, Ch. 3).
-/

/-- An exponential family with sufficient statistic T and natural parameter θ.
    p(x; θ) = h(x) exp(θ^T T(x) - A(θ))
    where A(θ) = log ∫ h(x) exp(θ^T T(x)) dx is the log-partition function. -/
structure ExponentialFamily (m : ℕ) where
  /-- Dimension of the sufficient statistic -/
  statDim : ℕ := m
  -- The sufficient statistic T : X → ℝ^m is axiomatized
  /-- The natural parameter θ ∈ ℝ^m -/
  theta : Fin m → ℝ
  /-- The log-partition function A(θ) -/
  logPartition : (Fin m → ℝ) → ℝ

/-! **Link 2 (Amari–Nagaoka Thm 3.3): Fisher information = covariance of the
sufficient statistic.** For an exponential family p(x; θ) ∝ exp(θᵀ T(x)),
I(θ) = ∇²A(θ) = Cov_θ[T(x)].

**REFUTATION OF THE AXIOMATIZED FORM (kernel finding, 2026-06-10)**: an earlier
version of this file carried

    axiom expfam_fisher_is_covariance (E) (Sigma_T : Matrix (Fin m) (Fin m) ℝ) :
        expFamFisherInfo E = Sigma_T

with `Sigma_T` universally quantified and UNCONSTRAINED, and `expFamFisherInfo`
a placeholder `0`-matrix. That axiom is not merely false — it is logically
INCONSISTENT: instantiating `Sigma_T := 0` and `Sigma_T := 1` derives
`(0 : Matrix (Fin m) (Fin m) ℝ) = 1`, hence `False` for m ≥ 1. It was never
reachable from the build gate, so no wired theorem ever depended on it; the
containment held by construction.

Both the placeholder definition and the axiom are DELETED rather than repaired:
the honest statement needs a real measure-theoretic Fisher information
(∇²A(θ) as a second Fréchet derivative of the log-partition function), which is
bedrock calculus, deliberately deferred. Until that exists, the identification
"lifted covariance = Fisher information" enters downstream results ONLY through
the docstring interpretation of `min_variance_is_null_fisher`, whose statement
is now purely about the (well-defined) lifted covariance matrix. Never as an
axiom. -/

/-- **COROLLARY (The Bridge):**
    Combining Link 1 and Link 2: for an exponential family with quadratic
    sufficient statistics, the minimum-variance quadratic form is the null
    direction of the Fisher information matrix.

    min_{||C||=1} Var[x^T C x] = min eigval of I(θ)

    The engine's computation IS finding the null Fisher direction.

    The statement is about the lifted covariance `Sigma_lifted` directly — the
    reading of `Sigma_lifted` as the Fisher information I(θ) is Amari–Nagaoka
    (Link 2, see the refutation note above), which is interpretation, not a
    formal premise. Symmetry and positive semidefiniteness are honest
    hypotheses; in the engine's instantiation hPSD is SUPPLIED STRUCTURALLY by
    `lifted_quadform_nonneg` (Link 1), not assumed.

    STATUS (2026-06-10): PROVEN by direct application of the Rayleigh
    characterization; the single remaining plank is the deferred-standard
    `min_variance_is_min_eigenvector`. -/
theorem min_variance_is_null_fisher
    {m : ℕ}
    (Sigma_lifted : Matrix (Fin m) (Fin m) ℝ)
    (hSymm : Sigma_lifted.IsSymm)
    (hPSD : ∀ v : Fin m → ℝ, 0 ≤ ∑ i, ∑ j, v i * Sigma_lifted i j * v j)
    (c_star : Fin m → ℝ) (hNorm : ∑ i, c_star i ^ 2 = 1)
    (hMin : ∀ c_test : Fin m → ℝ, ∑ i, c_test i ^ 2 = 1 →
      ∑ i, ∑ j, c_star i * Sigma_lifted i j * c_star j ≤
      ∑ i, ∑ j, c_test i * Sigma_lifted i j * c_test j) :
    -- c_star is a null (or minimum) eigenvector of the Fisher information
    ∃ lam_min, (∀ i, ∑ j, Sigma_lifted i j * c_star j = lam_min * c_star i) ∧
      ∀ lam, (∃ w : Fin m → ℝ, w ≠ 0 ∧ ∀ i, ∑ j, Sigma_lifted i j * w j = lam * w i) →
        lam_min ≤ lam :=
  min_variance_is_min_eigenvector Sigma_lifted hSymm hPSD c_star hNorm hMin


/-! ## Section 3: Open Gap — Minimum Variance ↔ Nearest Integral of Motion

This is the OPEN RESEARCH QUESTION identified in the Fisher-Noether Bridge.

For an ergodic Hamiltonian system with integrals of motion I_1, ..., I_k,
the minimum-variance quadratic form Q* is "close" to the nearest quadratic
integral. How close? The answer depends on T* = 1/λ_min.

The precise bound requires:
- Spectral gap theory for the lifted covariance operator
- A Poincaré inequality relating the eigenvalue gap to the distance
  from the conserved subspace
- The Jeans theorem (f = F(I_1,...,I_k) for ergodic equilibrium)

This is labeled as a RESEARCH PROBLEM for Phase 16.
-/

/-- A Hamiltonian system on phase space ℝ^d with Hamiltonian H. -/
structure HamiltonianSystem (d : ℕ) where
  /-- The Hamiltonian function H : ℝ^d → ℝ -/
  hamiltonian : (Fin d → ℝ) → ℝ
  -- The equations of motion dq/dt = ∂H/∂p, dp/dt = -∂H/∂q are axiomatized.
  -- Full formalization requires smooth manifold structure not yet available.

/-- An ergodic equilibrium distribution for a Hamiltonian system.
    Satisfies the Vlasov equation df/dt = 0 and is ergodic on level sets. -/
structure ErgodicEquilibrium (d : ℕ) (sys : HamiltonianSystem d) where
  /-- The distribution density on phase space -/
  density : (Fin d → ℝ) → ℝ
  /-- Density is non-negative -/
  density_nonneg : ∀ x, 0 ≤ density x
  -- Satisfies Vlasov equation (axiomatized)
  -- Is ergodic on each energy surface (axiomatized)

/-- An integral of motion of a Hamiltonian system. -/
structure IntegralOfMotion (d : ℕ) where
  /-- The conserved quantity as a function on phase space -/
  value : (Fin d → ℝ) → ℝ
  /-- The quantity is constant along trajectories (axiomatized) -/
  is_conserved : Prop := True

/-- A quadratic integral of motion: one that can be written as x^T A x. -/
structure QuadraticIntegral (d : ℕ) extends IntegralOfMotion d where
  /-- The matrix defining the quadratic form -/
  quadMat : Matrix (Fin d) (Fin d) ℝ
  /-- The matrix is symmetric -/
  quadSymm : quadMat.IsSymm
  /-- The value equals the quadratic form -/
  value_eq_quad : ∀ x, value x = ∑ i, ∑ j, quadMat i j * x i * x j

/-- Frobenius norm squared of the difference of two matrices. -/
def frobeniusDistSq (A B : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j - B i j) ^ 2

/-- Frobenius norm squared of a matrix. -/
def frobeniusNormSq (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

/-- Normalize a matrix to unit Frobenius norm (when nonzero). -/
noncomputable def normalizeMatrix (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : 0 < frobeniusNormSq A) : Matrix (Fin d) (Fin d) ℝ :=
  (1 / Real.sqrt (frobeniusNormSq A)) • A

/-- The validity horizon T* = 1/λ_min where λ_min is the minimum eigenvalue
    of the lifted covariance (= Fisher information for exponential families). -/
def validityHorizon (lam_min : ℝ) (h_lam : 0 < lam_min) : ℝ := 1 / lam_min

/-- **OPEN RESEARCH QUESTION (Conjecture 1 — The T* Bound):**

    For an ergodic Hamiltonian system with a quadratic integral I,
    the minimum-variance quadratic form Q* satisfies:

        ||Q*.mat - normalize(I.quadMat)||²_F ≤ C · λ_min

    where λ_min is the smallest eigenvalue of the lifted covariance,
    T* = 1/λ_min is the validity horizon, and C depends on the spectral
    gap of the Hamiltonian and the dimension of the integral subspace.

    REQUIRED MACHINERY (not in Mathlib as of March 2026):
    1. Davis-Kahan sin(θ) theorem for eigenvector perturbation
       — not in Mathlib, not in any Lean 4 library
    2. Jeans' theorem formalized for ergodic Hamiltonian systems
    3. Poincaré inequality on energy surfaces of Hamiltonian flows

    The proof strategy (if attempted):
    - The lifted covariance Σ has an eigenvalue decomposition
    - The quadratic integral I corresponds to a specific eigenvector
    - λ_min measures how close Q* is to the null space
    - Davis-Kahan bounds the angle between Q* and I in terms of the
      eigenvalue gap — this is the missing piece

    SORRY CLASSIFICATION: OPEN RESEARCH QUESTION -/
theorem minvar_approximates_integral
    {d : ℕ}
    (sys : HamiltonianSystem d)
    (f : ErgodicEquilibrium d sys)
    (I : QuadraticIntegral d)
    (hI_nonzero : 0 < frobeniusNormSq I.quadMat)
    (Q_star : QuadraticForm d)
    (lam_min : ℝ) (h_lam : 0 < lam_min)
    -- Q_star is the minimum-variance quadratic form under f:
    -- ∀ Q, Var_f[Q.eval] ≥ lam_min (Q_star achieves this minimum)
    -- I is a quadratic integral of sys (conserved along trajectories)
    :
    -- THE CLAIM: distance from Q* to the normalized integral ≤ C · λ_min
    ∃ (C : ℝ), 0 ≤ C ∧
      frobeniusDistSq Q_star.mat (normalizeMatrix I.quadMat hI_nonzero) ≤ C * lam_min := by
  -- OPEN RESEARCH QUESTION: requires Davis-Kahan theorem (not in Mathlib)
  -- Davis-Kahan sin(θ) theorem (1970): for symmetric matrices A, Ã with
  -- eigenvalues λ_i, λ̃_i and corresponding eigenvectors v_i, ṽ_i:
  --   sin(θ(v_1, ṽ_1)) ≤ ||A - Ã||_op / gap
  -- where gap = min_{j≥2} |λ̃_j - λ_1|.
  -- Applied here: A = true Fisher info, Ã = empirical Fisher info,
  -- v_1 = true integral direction, ṽ_1 = discovered Q*.
  -- The bound gives ||Q* - I_normalized||_F ≤ C · ||A - Ã|| / gap.
  -- When Ã converges to A (N → ∞), the bound is O(λ_min) if the spectral
  -- gap is bounded away from zero.
  --
  -- Reference: Davis & Kahan (1970), "The rotation of eigenvectors by a
  -- perturbation. III", SIAM J. Numer. Anal. 7(1), 1-46.
  sorry


/-! ## Section 4: Selection Contamination — the Exact Variance-Shift Identity

When the observed distribution is the tilted measure f·S/E_f[S] (true
distribution f reweighted by a selection function S), the variance of any
observable q shifts by an EXACT amount. With μ := E_f[q] and Z := E_f[S]:

  E_{f·S}[q]        = μ + Cov_f[S, q]/Z
  E_{f·S}[(q−μ)²]   = Var_f[q] + Cov_f[S, (q−μ)²]/Z
  Var_{f·S}[q]      = E_{f·S}[(q−μ)²] − (E_{f·S}[q] − μ)²

  ⟹  Var_{f·S}[q] − Var_f[q] = Cov_f[S, (q−μ)²]/Z − (Cov_f[S, q]/Z)²

This is the formal statement of why Gaia's magnitude-limited selection
function contaminates the manifold-mode result: the shift vanishes exactly
when S is uncorrelated with both q and its squared deviation. Derivation
re-verified by hand 2026-06-10 before formalization; proven below at ε = 0
for the empirical (uniform-base) measure — finite-sum algebra only.

This section REPLACES the former `selection_contamination_variance_shift`
placeholder (vacuous ∃-statement, deleted 2026-06-10). -/

/-- Uniform empirical mean of a vector of values: `E[v] = (1/N) Σ v`. -/
def uniformMean (N : ℕ) (v : Fin N → ℝ) : ℝ := (1 / N) * ∑ i, v i

/-- Uniform empirical covariance: `Cov[a,b] = E[ab] − E[a]E[b]`. -/
def uniformCov (N : ℕ) (a b : Fin N → ℝ) : ℝ :=
  uniformMean N (fun i => a i * b i) - uniformMean N a * uniformMean N b

/-- Selection-tilted mean: `E_{f·S}[q] = (Σ S q)/(Σ S)` (uniform base f). -/
def selectionMean (N : ℕ) (S q : Fin N → ℝ) : ℝ :=
  (∑ i, S i * q i) / (∑ i, S i)

/-- Selection-tilted variance: the variance of `q` under the tilted measure
    `f·S/E_f[S]`, i.e. `(Σ S (q − m_S)²)/(Σ S)` with `m_S` the tilted mean.
    NOTE: this reweights the MEASURE, not the values — the former placeholder
    took the variance of the rescaled values `q·S/S̄`, which is a different
    (and physically wrong) object. -/
def selectionVariance (N : ℕ) (S q : Fin N → ℝ) : ℝ :=
  (∑ i, S i * (q i - selectionMean N S q)^2) / (∑ i, S i)

/-- Weighted sum-of-squared-deviations expansion (the workhorse):
    `Σ w (q − m)² = Σ w q² − 2m Σ w q + m² Σ w`. -/
private lemma sum_mul_sq_dev (N : ℕ) (w q : Fin N → ℝ) (m : ℝ) :
    ∑ k, w k * (q k - m)^2
      = (∑ k, w k * (q k)^2) - 2*m*(∑ k, w k * q k) + m^2 * (∑ k, w k) := by
  have h : ∀ k : Fin N, w k * (q k - m)^2
      = w k * (q k)^2 - 2*m*(w k * q k) + m^2 * w k := fun k => by ring
  simp_rw [h]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]

/-- Unweighted specialization: `Σ (q − m)² = Σ q² − 2m Σ q + m² N`. -/
private lemma sum_sq_dev (N : ℕ) (q : Fin N → ℝ) (m : ℝ) :
    ∑ k, (q k - m)^2 = (∑ k, (q k)^2) - 2*m*(∑ k, q k) + m^2 * N := by
  have h := sum_mul_sq_dev N (fun _ => 1) q m
  simp only [one_mul] at h
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at h
  exact h

/-- **THEOREM (Exact Empirical Selection-Variance Identity):**

    `Var_{f·S}[q] − Var_f[q] = Cov_f[S,(q−μ)²]/Z − (Cov_f[S,q]/Z)²`

    with `μ = E_f[q]`, `Z = E_f[S]`, `f` the uniform empirical measure.
    EXACT at ε = 0 — no small-S expansion, no measure theory, pure
    finite-sum algebra. The two covariance terms are the complete
    decomposition of selection contamination:
    - `Cov_f[S,(q−μ)²]/Z`: selection inflates/deflates the spread directly;
    - `(Cov_f[S,q]/Z)²`: selection shifts the mean, which always REDUCES
      the apparent variance about the new center (the term enters with a
      minus sign — Galtonian regression toward the selected mean).

    STATUS: PROVEN (kernel-checked). Replaces the vacuous placeholder. -/
theorem selection_variance_shift_exact
    (N : ℕ) [NeZero N] (q S : Fin N → ℝ) (hS_pos : ∀ i, 0 < S i) :
    selectionVariance N S q - empiricalVariance N q =
      uniformCov N S (fun i => (q i - uniformMean N q)^2) / uniformMean N S
        - (uniformCov N S q / uniformMean N S)^2 := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hc : 0 < ∑ i, S i := Finset.sum_pos (fun i _ => hS_pos i) Finset.univ_nonempty
  have hcne : (∑ i, S i) ≠ 0 := ne_of_gt hc
  simp only [selectionVariance, selectionMean, empiricalVariance,
             uniformCov, uniformMean]
  rw [sum_mul_sq_dev N S q ((∑ i, S i * q i) / (∑ i, S i)),
      sum_sq_dev N q ((1 / N) * ∑ i, q i),
      sum_mul_sq_dev N S q ((1 / N) * ∑ i, q i)]
  field_simp
  ring

/-- **COROLLARY (No correlation ⟹ no contamination):** if the selection
    function is uncorrelated with both the observable and its squared
    deviation, the tilted variance equals the true variance. This is the
    precise condition under which manifold mode is selection-safe. -/
theorem selection_uncorrelated_no_contamination
    (N : ℕ) [NeZero N] (q S : Fin N → ℝ) (hS_pos : ∀ i, 0 < S i)
    (hcov_q : uniformCov N S q = 0)
    (hcov_sq : uniformCov N S (fun i => (q i - uniformMean N q)^2) = 0) :
    selectionVariance N S q = empiricalVariance N q := by
  have h := selection_variance_shift_exact N q S hS_pos
  rw [hcov_q, hcov_sq] at h
  simp only [zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
             zero_pow, sub_zero] at h
  linarith

/-- **COROLLARY (Gaia reading):** the identity instantiated for a quadratic
    form `Q` evaluated on samples `X` — the exact contamination law for the
    manifold-mode variance functional under a selection function `S`.
    Cited by the Gaia benchmark analysis: `L_z` correlates with the
    magnitude-limited `S`, so both covariance terms are nonzero. -/
theorem selection_contamination_quadform
    (N : ℕ) [NeZero N] (X : Fin N → Fin d → ℝ) (Q : QuadraticForm d)
    (S : Fin N → ℝ) (hS_pos : ∀ i, 0 < S i) :
    selectionVariance N S (fun i => Q.eval (X i))
      - empiricalVariance N (fun i => Q.eval (X i)) =
      uniformCov N S
          (fun i => (Q.eval (X i) - uniformMean N (fun j => Q.eval (X j)))^2)
        / uniformMean N S
        - (uniformCov N S (fun i => Q.eval (X i)) / uniformMean N S)^2 :=
  selection_variance_shift_exact N (fun i => Q.eval (X i)) S hS_pos

/-- **COROLLARY (Contamination Detection via Shuffle Gap):**

    The shuffle gap — the ratio of shuffled variance to real variance —
    measures the mutual information between Q and the temporal/dynamical
    structure. When selection contamination is present, the shuffle gap
    is reduced because S introduces non-dynamical correlations that
    survive shuffling (if S depends on marginal distributions).

    SORRY CLASSIFICATION: OPEN — connecting the shuffle gap formally to
    the correction term requires a model of what shuffling preserves
    (marginal distributions) vs what it destroys (joint structure). -/
theorem shuffle_gap_detects_contamination
    (N : ℕ) [NeZero N]
    (X : Fin N → Fin d → ℝ)
    (Q : QuadraticForm d)
    (S : Fin N → ℝ) (hS_pos : ∀ i, 0 < S i)
    -- shuffle_gap := Var_shuffled[Q] / Var_real[Q]
    -- contamination reduces shuffle_gap toward 1
    : True := by
  -- OPEN: requires formalization of permutation-invariant statistics
  -- and their relationship to the selection function structure
  trivial


/-! ## Summary: Epistemic State of the File (refreshed 2026-06-10)

PROVEN (kernel-checked, ε = 0):
1. `variance_as_lifted_quadform` — Link 1 core identity (proven 2026-06-03)
2. `lifted_quadform_nonneg` — structural PSD supply for the bridge
3. `min_variance_is_null_fisher` — the Bridge, by composition (2026-06-10);
   inherits exactly one deferred-standard plank (below)
4. `selection_variance_shift_exact` — the exact empirical selection-variance
   identity (2026-06-10; replaced the vacuous placeholder), with corollaries
   `selection_uncorrelated_no_contamination` + `selection_contamination_quadform`

SORRIED, DEFERRED-STANDARD (bedrock, not SGC content — no attention spent):
5. `min_variance_is_min_eigenvector` — Rayleigh / spectral theorem

SORRIED, OPEN RESEARCH (the genuine frontier):
6. `minvar_approximates_integral` — Davis–Kahan sin(θ) machinery (Phase 16)

PLACEHOLDERS (compile, but carry no content — must not be cited):
7. `shuffle_gap_detects_contamination` — `True`-conclusion stub

DELETED (2026-06-10, second pass): `selection_contamination_variance_shift`
— the vacuous ∃-statement; superseded by `selection_variance_shift_exact`
above. Note its `var_weighted` also measured the WRONG object (variance of
rescaled values rather than variance under the tilted measure).

DELETED (2026-06-10): `expFamFisherInfo` placeholder def + the
`expfam_fisher_is_covariance` axiom — the axiom was logically INCONSISTENT
(universally quantified unconstrained RHS; two instantiations derive `False`).
See the Link 2 refutation note in Section 2.
-/

end SGC.InformationGeometry.FisherNoetherBridge
