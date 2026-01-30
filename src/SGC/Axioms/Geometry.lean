import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

/-!
  # SGC/Axioms/Geometry.lean

  Core L²(π) Geometry for the Stochastic Geometry of Consolidation.

  This file provides the foundational weighted inner product space structure
  used throughout SGC, using explicit structures to handle the dynamic sigma-algebras
  required by renormalization.

  ## Design Pattern: Explicit Weight Pattern
  - All geometry takes `pi_dist : V → ℝ` explicitly
  - Positivity via `(hπ : ∀ v, 0 < pi_dist v)` hypothesis
  - No custom wrapper types like WeightedSpace

  **NOTE**: This module uses an **Explicit Weight Pattern** (`pi_dist` as an argument)
  rather than Mathlib's `InnerProductSpace` typeclasses. This design handles the
  dynamic sigma-algebras required by renormalization (where standard static typeclasses
  imply a single fixed measure). See `ARCHITECTURE.md` for the full rationale.

  **TODO (Bridge Module)**: Prove that at any fixed snapshot, these structures instantiate
  `Mathlib.Probability.Kernel` and are isomorphic to `PhysLean.IsHamiltonian` generators.
-/

noncomputable section

namespace SGC
section Geometry
open Finset LinearMap Matrix Real ContinuousLinearMap Submodule Topology EuclideanSpace

-- Suppress unused variable warnings (many lemmas don't need all type constraints)
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### 1. Probability Measure Structure -/

/-- A probability measure on a finite type V.
    Bundles the mass function with positivity and normalization hypotheses.

    This structure is intentionally NOT a typeclass. It is passed explicitly to
    support measure transformations in renormalization (π → π̄) without type coercions.

    **Usage:** For new code, prefer passing `μ : ProbabilityMeasure V` over the
    unbundled triple `(pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) (h_sum : ...)`.
    Existing code uses the unbundled form for compatibility. -/
structure ProbabilityMeasure (V : Type*) [Fintype V] where
  /-- The mass function π : V → ℝ -/
  mass : V → ℝ
  /-- Positivity: π(v) > 0 for all v -/
  pos : ∀ v, 0 < mass v
  /-- Normalization: Σ π(v) = 1 -/
  sum_one : ∑ v, mass v = 1

namespace ProbabilityMeasure

/-- Coercion to function for convenient access. -/
instance : CoeFun (ProbabilityMeasure V) (fun _ => V → ℝ) where
  coe μ := μ.mass

/-- The mass at any point is non-negative. -/
lemma mass_nonneg (μ : ProbabilityMeasure V) (v : V) : 0 ≤ μ.mass v :=
  le_of_lt (μ.pos v)

/-- The mass at any point is at most 1. -/
lemma mass_le_one (μ : ProbabilityMeasure V) (v : V) : μ.mass v ≤ 1 := by
  have h := μ.sum_one
  have hv : μ.mass v ≤ ∑ w, μ.mass w := Finset.single_le_sum (fun w _ => μ.mass_nonneg w) (Finset.mem_univ v)
  linarith

end ProbabilityMeasure

/-! ### 2. Weighted L²(π) Inner Product -/

/-- The constant vector of ones. Using `abbrev` ensures definitional equality
    with `fun _ => 1` is immediate for the elaborator. -/
abbrev constant_vec_one : V → ℝ := fun _ => 1

/-- The weighted L²(π) inner product: ⟨u, v⟩_π = Σ π(x) u(x) v(x). -/
def inner_pi (pi_dist : V → ℝ) (u v : V → ℝ) : ℝ :=
  ∑ x, pi_dist x * u x * v x

/-- The weighted squared norm: ‖v‖²_π = ⟨v, v⟩_π. -/
def norm_sq_pi (pi_dist : V → ℝ) (v : V → ℝ) : ℝ :=
  inner_pi pi_dist v v

/-- The weighted norm: ‖v‖_π = √(‖v‖²_π). -/
def norm_pi (pi_dist : V → ℝ) (f : V → ℝ) : ℝ :=
  Real.sqrt (norm_sq_pi pi_dist f)

/-! ### 2. Bilinearity Lemmas -/

lemma inner_pi_add_left {pi_dist : V → ℝ} (u v w : V → ℝ) :
    inner_pi pi_dist (u + v) w = inner_pi pi_dist u w + inner_pi pi_dist v w := by
  simp only [inner_pi, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  congr 1; ext x; ring

lemma inner_pi_add_right {pi_dist : V → ℝ} (u v w : V → ℝ) :
    inner_pi pi_dist u (v + w) = inner_pi pi_dist u v + inner_pi pi_dist u w := by
  simp [inner_pi, mul_add, Finset.sum_add_distrib]

lemma inner_pi_smul_left {pi_dist : V → ℝ} (c : ℝ) (u v : V → ℝ) :
    inner_pi pi_dist (c • u) v = c * inner_pi pi_dist u v := by
  simp only [inner_pi, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  congr 1; ext x; ring

lemma inner_pi_smul_right {pi_dist : V → ℝ} (c : ℝ) (u v : V → ℝ) :
    inner_pi pi_dist u (c • v) = c * inner_pi pi_dist u v := by
  simp [inner_pi, mul_left_comm, mul_assoc, Finset.mul_sum]

lemma inner_pi_comm {pi_dist : V → ℝ} (u v : V → ℝ) :
    inner_pi pi_dist u v = inner_pi pi_dist v u := by
  simp [inner_pi, mul_comm, mul_left_comm]

lemma inner_pi_zero_left {pi_dist : V → ℝ} (v : V → ℝ) :
    inner_pi pi_dist 0 v = 0 := by
  simp [inner_pi]

lemma inner_pi_zero_right {pi_dist : V → ℝ} (u : V → ℝ) :
    inner_pi pi_dist u 0 = 0 := by
  simp [inner_pi]

lemma inner_pi_sub_left {pi_dist : V → ℝ} (u v w : V → ℝ) :
    inner_pi pi_dist (u - v) w = inner_pi pi_dist u w - inner_pi pi_dist v w := by
  simp only [inner_pi, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  congr 1; ext x; ring

lemma inner_pi_sub_right {pi_dist : V → ℝ} (u v w : V → ℝ) :
    inner_pi pi_dist u (v - w) = inner_pi pi_dist u v - inner_pi pi_dist u w := by
  simp only [inner_pi, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  congr 1; ext x; ring

/-! ### 3. Norm Helpers -/

/-- norm_sq_pi as a sum of weighted squares. -/
lemma norm_sq_pi_eq_sum (pi_dist : V → ℝ) (h : V → ℝ) :
    norm_sq_pi pi_dist h = ∑ v, pi_dist v * (h v)^2 := by
  unfold norm_sq_pi inner_pi
  congr 1
  ext v
  rw [pow_two, mul_assoc]

/-- norm_sq_pi is positive for nonzero vectors when weights are positive. -/
lemma norm_sq_pi_pos {pi_dist : V → ℝ} (hπ : ∀ v, 0 < pi_dist v) {u : V → ℝ} (hu : u ≠ 0) :
    0 < norm_sq_pi pi_dist u := by
  rw [norm_sq_pi, inner_pi]
  have hex : ∃ v, u v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu (funext h)
  obtain ⟨v₀, hv₀⟩ := hex
  have h_term_pos : 0 < pi_dist v₀ * u v₀ * u v₀ := by
    have hπ₀ : 0 < pi_dist v₀ := hπ v₀
    have h_usq : 0 < u v₀ * u v₀ := mul_self_pos.mpr hv₀
    calc 0 < pi_dist v₀ * (u v₀ * u v₀) := mul_pos hπ₀ h_usq
      _ = pi_dist v₀ * u v₀ * u v₀ := by ring
  apply Finset.sum_pos'
  · intro v _
    have hπv : 0 ≤ pi_dist v := le_of_lt (hπ v)
    have h_usq : 0 ≤ u v * u v := mul_self_nonneg (u v)
    calc 0 ≤ pi_dist v * (u v * u v) := mul_nonneg hπv h_usq
      _ = pi_dist v * u v * u v := by ring
  · exact ⟨v₀, Finset.mem_univ _, h_term_pos⟩

/-- norm_sq_pi is always nonnegative. -/
lemma norm_sq_pi_nonneg (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) (h : V → ℝ) :
    0 ≤ norm_sq_pi pi_dist h := by
  rw [norm_sq_pi_eq_sum]
  apply sum_nonneg
  intro v _
  apply mul_nonneg (le_of_lt (h_pos v)) (sq_nonneg _)

/-- norm_sq_pi = 0 iff the function is zero. -/
lemma norm_sq_pi_eq_zero_iff (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) (h : V → ℝ) :
    norm_sq_pi pi_dist h = 0 ↔ ∀ v, h v = 0 := by
  constructor
  · intro h_zero v
    rw [norm_sq_pi_eq_sum] at h_zero
    have h_nonneg : ∀ x ∈ univ, 0 ≤ pi_dist x * (h x)^2 :=
      fun x _ => mul_nonneg (le_of_lt (h_pos x)) (sq_nonneg (h x))
    have h_term := Finset.sum_eq_zero_iff_of_nonneg h_nonneg
    have h_eq : pi_dist v * (h v)^2 = 0 := h_term.mp h_zero v (mem_univ v)
    rw [pow_two] at h_eq
    have : h v * h v = 0 := (mul_eq_zero.mp h_eq).resolve_left (ne_of_gt (h_pos v))
    exact mul_self_eq_zero.mp this
  · intro h_zero
    rw [norm_sq_pi_eq_sum]
    apply Finset.sum_eq_zero
    intro v _
    simp [h_zero v]

/-- norm_sq_pi of constant_vec_one equals the sum of weights (which is 1). -/
lemma norm_sq_pi_one {pi_dist : V → ℝ} (h_sum : ∑ v, pi_dist v = 1) :
    norm_sq_pi pi_dist constant_vec_one = 1 := by
  simp only [norm_sq_pi, inner_pi, constant_vec_one, mul_one, h_sum]

/-- norm_pi = 0 iff f = 0. -/
lemma norm_pi_eq_zero_iff (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) (f : V → ℝ) :
    norm_pi pi_dist f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    ext v
    have h_sq : norm_sq_pi pi_dist f = 0 := by
      unfold norm_pi at hf
      have := Real.sqrt_eq_zero (norm_sq_pi_nonneg pi_dist h_pos f)
      exact this.mp hf
    exact (norm_sq_pi_eq_zero_iff pi_dist h_pos f).mp h_sq v
  · intro hf
    simp [hf, norm_pi, norm_sq_pi, inner_pi]

/-- norm_pi is positive for nonzero functions. -/
lemma norm_pi_pos_of_ne_zero (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) (f : V → ℝ)
    (hf : f ≠ 0) : 0 < norm_pi pi_dist f := by
  unfold norm_pi
  apply Real.sqrt_pos_of_pos
  have : norm_sq_pi pi_dist f ≠ 0 := by
    intro h_eq
    exact hf ((norm_sq_pi_eq_zero_iff pi_dist h_pos f).mp h_eq |> funext)
  exact (norm_sq_pi_nonneg pi_dist h_pos f).lt_of_ne' this

/-! ### 4. Cauchy-Schwarz -/

/-- Helper: discriminant inequality from squares. -/
lemma sqrt_ineq_of_sq_le (a b c : ℝ) (ha : 0 ≤ a) (_hc : 0 ≤ c) (h : b^2 ≤ a * c) :
    |b| ≤ Real.sqrt a * Real.sqrt c := by
  have : Real.sqrt (b^2) ≤ Real.sqrt (a * c) := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq_eq_abs] at this
  rw [Real.sqrt_mul ha] at this
  exact this

/-- Helper: Pointwise quadratic expansion. -/
lemma pointwise_quad (f g : V → ℝ) (t : ℝ) (v : V) :
    (f v + t * g v)^2 = (f v)^2 + 2 * t * (f v * g v) + t^2 * (g v)^2 := by
  have : (f v + t * g v)^2 = (f v)^2 + 2 * t * (f v * g v) + t^2 * (g v)^2 := by ring
  simpa [pow_two] using this

/-- Helper: Sum-level quadratic expansion. -/
lemma sum_quad (pi_dist : V → ℝ) (f g : V → ℝ) (t : ℝ) :
    ∑ v, pi_dist v * (f v + t * g v)^2 =
    ∑ v, pi_dist v * (f v)^2 + 2 * t * (∑ v, pi_dist v * (f v * g v)) +
      t^2 * (∑ v, pi_dist v * (g v)^2) := by
  have h1 : ∑ v, pi_dist v * (f v + t * g v)^2 =
            ∑ v, pi_dist v * ((f v)^2 + 2 * t * (f v * g v) + t^2 * (g v)^2) := by
    congr 1; ext v; rw [pointwise_quad]
  have h2 : ∑ v, pi_dist v * ((f v)^2 + 2 * t * (f v * g v) + t^2 * (g v)^2) =
            ∑ v, pi_dist v * (f v)^2 + ∑ v, pi_dist v * (2 * t * (f v * g v)) +
              ∑ v, pi_dist v * (t^2 * (g v)^2) := by
    simp only [mul_add, sum_add_distrib]
  have h3 : ∑ v, pi_dist v * (2 * t * (f v * g v)) = 2 * t * ∑ v, pi_dist v * (f v * g v) := by
    simp only [mul_assoc, mul_comm (pi_dist _), mul_left_comm, mul_sum]
  have h4 : ∑ v, pi_dist v * (t^2 * (g v)^2) = t^2 * ∑ v, pi_dist v * (g v)^2 := by
    simp only [mul_assoc, mul_comm (pi_dist _), mul_left_comm, mul_sum]
  calc ∑ v, pi_dist v * (f v + t * g v)^2
      = ∑ v, pi_dist v * ((f v)^2 + 2 * t * (f v * g v) + t^2 * (g v)^2) := h1
    _ = ∑ v, pi_dist v * (f v)^2 + ∑ v, pi_dist v * (2 * t * (f v * g v)) +
          ∑ v, pi_dist v * (t^2 * (g v)^2) := h2
    _ = ∑ v, pi_dist v * (f v)^2 + 2 * t * ∑ v, pi_dist v * (f v * g v) +
          t^2 * ∑ v, pi_dist v * (g v)^2 := by rw [h3, h4]

/-- **Cauchy-Schwarz for L²(π)**.
    Proven explicitly using the polynomial discriminant method. -/
lemma cauchy_schwarz_pi (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) (f g : V → ℝ) :
    |inner_pi pi_dist f g| ≤ norm_pi pi_dist f * norm_pi pi_dist g := by
  let a := norm_sq_pi pi_dist g
  let b := inner_pi pi_dist f g
  let c := norm_sq_pi pi_dist f
  let P (t : ℝ) := norm_sq_pi pi_dist (fun v => f v + t * g v)
  have hP_nonneg : ∀ t, 0 ≤ P t := fun t => by
    unfold P
    exact norm_sq_pi_nonneg pi_dist h_pos _
  have hP_quad : ∀ t, P t = c + 2 * t * b + t^2 * a := by
    intro t
    unfold P a b c
    have h_left : norm_sq_pi pi_dist (fun v => f v + t * g v) =
                  ∑ v, pi_dist v * (f v + t * g v)^2 :=
      norm_sq_pi_eq_sum pi_dist (fun v => f v + t * g v)
    have h_c : norm_sq_pi pi_dist f = ∑ v, pi_dist v * (f v)^2 :=
      norm_sq_pi_eq_sum pi_dist f
    have h_a : norm_sq_pi pi_dist g = ∑ v, pi_dist v * (g v)^2 :=
      norm_sq_pi_eq_sum pi_dist g
    have h_b : inner_pi pi_dist f g = ∑ v, pi_dist v * (f v * g v) := by
      unfold inner_pi; congr 1; ext v; rw [mul_assoc]
    have h_sum := sum_quad pi_dist f g t
    calc norm_sq_pi pi_dist (fun v => f v + t * g v)
        = ∑ v, pi_dist v * (f v + t * g v)^2 := h_left
      _ = ∑ v, pi_dist v * (f v)^2 + 2 * t * (∑ v, pi_dist v * (f v * g v)) +
            t^2 * (∑ v, pi_dist v * (g v)^2) := h_sum
      _ = norm_sq_pi pi_dist f + 2 * t * inner_pi pi_dist f g + t^2 * norm_sq_pi pi_dist g := by
          rw [← h_c, ← h_b, ← h_a]
  by_cases ha : a = 0
  · have hg : ∀ v, g v = 0 := (norm_sq_pi_eq_zero_iff pi_dist h_pos g).mp ha
    have hb : b = 0 := by unfold b inner_pi; simp [hg]
    unfold b at hb
    rw [hb, abs_zero]
    apply mul_nonneg <;> exact Real.sqrt_nonneg _
  · have ha_pos : 0 < a := by
      have ha_nn := norm_sq_pi_nonneg pi_dist h_pos g
      unfold a at ha_nn ha ⊢
      exact ha_nn.lt_of_ne (Ne.symm ha)
    have h_vertex := hP_nonneg (-b / a)
    rw [hP_quad] at h_vertex
    have h_disc : b^2 ≤ a * c := by
      have h_simp : c + 2 * (-b / a) * b + (-b / a)^2 * a = c - b^2 / a := by
        field_simp; ring
      rw [h_simp] at h_vertex
      have : b^2 / a ≤ c := by linarith
      calc b^2 = a * (b^2 / a) := by field_simp [ne_of_gt ha_pos]
        _ ≤ a * c := mul_le_mul_of_nonneg_left this (le_of_lt ha_pos)
    have ha_nn := norm_sq_pi_nonneg pi_dist h_pos g
    have hc_nn := norm_sq_pi_nonneg pi_dist h_pos f
    have h_sqrt := sqrt_ineq_of_sq_le a b c ha_nn hc_nn h_disc
    calc |b| = |inner_pi pi_dist f g| := rfl
      _ ≤ Real.sqrt a * Real.sqrt c := h_sqrt
      _ = Real.sqrt c * Real.sqrt a := mul_comm _ _
      _ = norm_pi pi_dist f * norm_pi pi_dist g := by unfold norm_pi a c; rfl

/-! ### 5. Operator Norm -/

/-- The set of constants bounding ‖A f‖_π / ‖f‖_π. -/
def opNorm_set (pi_dist : V → ℝ) (_h_pos : ∀ v, 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] (V → ℝ)) : Set ℝ :=
  { c | 0 ≤ c ∧ ∀ f, norm_pi pi_dist (A f) ≤ c * norm_pi pi_dist f }

/-- **L²(π) Operator Norm**.
    Defined as the infimum of all constants c such that ‖A f‖_π ≤ c ‖f‖_π. -/
def opNorm_pi (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] (V → ℝ)) : ℝ :=
  sInf (opNorm_set pi_dist h_pos A)

/-- Scaling isometry for Euclidean transport. -/
def iso_L2_to_std (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) : (V → ℝ) ≃ₗ[ℝ] (V → ℝ) where
  toFun f v := f v * Real.sqrt (pi_dist v)
  invFun g v := g v / Real.sqrt (pi_dist v)
  left_inv f := by funext v; field_simp [Real.sqrt_ne_zero'.mpr (h_pos v)]
  right_inv g := by funext v; field_simp [Real.sqrt_ne_zero'.mpr (h_pos v)]
  map_add' f g := by ext; simp [add_mul]
  map_smul' r f := by ext; simp [mul_assoc]

/-- The isometry property: norm_sq_pi f = Σ (iso f v)². -/
lemma norm_sq_pi_eq_euclidean (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) (f : V → ℝ) :
    norm_sq_pi pi_dist f = ∑ v, (iso_L2_to_std pi_dist h_pos f v)^2 := by
  unfold iso_L2_to_std norm_sq_pi inner_pi
  simp only [LinearEquiv.coe_mk]
  apply Finset.sum_congr rfl
  intro v _
  show pi_dist v * f v * f v = (f v * Real.sqrt (pi_dist v)) ^ 2
  rw [mul_pow, Real.sq_sqrt (le_of_lt (h_pos v))]
  ring

/-- norm_pi expressed in terms of iso. -/
lemma norm_pi_eq_sqrt_sum_sq (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) (f : V → ℝ) :
    norm_pi pi_dist f = Real.sqrt (∑ v, (iso_L2_to_std pi_dist h_pos f v)^2) := by
  unfold norm_pi
  rw [norm_sq_pi_eq_euclidean]

/-- Key isometry: norm_pi f equals the EuclideanSpace norm of iso(f). -/
lemma norm_pi_eq_euclidean_norm (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) (f : V → ℝ) :
    norm_pi pi_dist f = ‖(WithLp.equiv 2 (V → ℝ)).symm (iso_L2_to_std pi_dist h_pos f)‖ := by
  rw [norm_pi_eq_sqrt_sum_sq pi_dist h_pos]
  rw [EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  rw [Real.norm_eq_abs, sq_abs]
  rfl

/-- The operator norm set is nonempty. -/
lemma opNorm_set_nonempty (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v)
    (A : (V → ℝ) →ₗ[ℝ] (V → ℝ)) : (opNorm_set pi_dist h_pos A).Nonempty := by
  let iso := iso_L2_to_std pi_dist h_pos
  let E := EuclideanSpace ℝ V
  let toE : (V → ℝ) → E := (WithLp.equiv 2 (V → ℝ)).symm
  let fromE : E → (V → ℝ) := WithLp.equiv 2 (V → ℝ)
  let A_E : E →ₗ[ℝ] E :=
    { toFun := fun g => toE (iso (A (iso.symm (fromE g))))
      map_add' := fun x y => by
        change toE (iso (A (iso.symm (fromE (x + y))))) =
               toE (iso (A (iso.symm (fromE x)))) + toE (iso (A (iso.symm (fromE y))))
        have h1 : fromE (x + y) = fromE x + fromE y := rfl
        rw [h1, map_add, map_add, map_add]
        rfl
      map_smul' := fun m x => by
        change toE (iso (A (iso.symm (fromE (m • x))))) =
               m • toE (iso (A (iso.symm (fromE x))))
        have h1 : fromE (m • x) = m • fromE x := rfl
        rw [h1, map_smul, map_smul, map_smul]
        rfl }
  let C := ‖A_E.toContinuousLinearMap‖
  use C
  refine ⟨norm_nonneg _, ?_⟩
  intro f
  have h_Af : norm_pi pi_dist (A f) = ‖toE (iso (A f))‖ :=
    norm_pi_eq_euclidean_norm pi_dist h_pos (A f)
  have h_f : norm_pi pi_dist f = ‖toE (iso f)‖ :=
    norm_pi_eq_euclidean_norm pi_dist h_pos f
  have h_conj : toE (iso (A f)) = A_E (toE (iso f)) := by
    simp only [A_E, LinearMap.coe_mk, AddHom.coe_mk, iso, fromE, toE]
    congr 1
    rw [Equiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  have h_bound : ‖A_E (toE (iso f))‖ ≤ C * ‖toE (iso f)‖ :=
    ContinuousLinearMap.le_opNorm A_E.toContinuousLinearMap (toE (iso f))
  calc norm_pi pi_dist (A f)
      = ‖toE (iso (A f))‖ := h_Af
    _ = ‖A_E (toE (iso f))‖ := by rw [h_conj]
    _ ≤ C * ‖toE (iso f)‖ := h_bound
    _ = C * norm_pi pi_dist f := by rw [h_f]

/-- The operator norm set is bounded below by 0. -/
lemma opNorm_set_bddBelow (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v)
    (A : (V → ℝ) →ₗ[ℝ] (V → ℝ)) : BddBelow (opNorm_set pi_dist h_pos A) :=
  ⟨0, fun _ hc => hc.1⟩

/-- The L²(π) operator norm is nonnegative. -/
lemma opNorm_pi_nonneg (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] (V → ℝ)) :
    0 ≤ opNorm_pi pi_dist h_pos A := by
  unfold opNorm_pi
  apply Real.sInf_nonneg
  intro c hc
  exact hc.1

/-- **The Bound Lemma**: ‖A f‖_π ≤ ‖A‖_π * ‖f‖_π. -/
lemma opNorm_pi_bound (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v)
    (A : (V → ℝ) →ₗ[ℝ] (V → ℝ)) (f : V → ℝ) :
    norm_pi pi_dist (A f) ≤ opNorm_pi pi_dist h_pos A * norm_pi pi_dist f := by
  unfold opNorm_pi
  by_cases hf : f = 0
  · simp [hf, norm_pi, norm_sq_pi, inner_pi]
  · have hf_pos : 0 < norm_pi pi_dist f := norm_pi_pos_of_ne_zero pi_dist h_pos f hf
    have h_ratio_le : ∀ c ∈ opNorm_set pi_dist h_pos A,
        norm_pi pi_dist (A f) / norm_pi pi_dist f ≤ c := by
      intro c hc
      rw [div_le_iff₀ hf_pos]
      exact hc.2 f
    have h_ratio_le_sInf : norm_pi pi_dist (A f) / norm_pi pi_dist f ≤
        sInf (opNorm_set pi_dist h_pos A) := by
      apply le_csInf (opNorm_set_nonempty pi_dist h_pos A)
      exact h_ratio_le
    calc norm_pi pi_dist (A f)
        = (norm_pi pi_dist (A f) / norm_pi pi_dist f) * norm_pi pi_dist f := by field_simp
      _ ≤ sInf (opNorm_set pi_dist h_pos A) * norm_pi pi_dist f := by
          apply mul_le_mul_of_nonneg_right h_ratio_le_sInf (le_of_lt hf_pos)

/-- **Submultiplicativity**: ‖A ∘ B‖_π ≤ ‖A‖_π * ‖B‖_π. -/
lemma opNorm_pi_comp (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) (A B : (V → ℝ) →ₗ[ℝ] (V → ℝ)) :
    opNorm_pi pi_dist h_pos (A ∘ₗ B) ≤ opNorm_pi pi_dist h_pos A * opNorm_pi pi_dist h_pos B := by
  unfold opNorm_pi
  apply csInf_le (opNorm_set_bddBelow pi_dist h_pos (A ∘ₗ B))
  constructor
  · apply mul_nonneg
    · apply Real.sInf_nonneg; intro c hc; exact hc.1
    · apply Real.sInf_nonneg; intro c hc; exact hc.1
  · intro f
    calc norm_pi pi_dist ((A ∘ₗ B) f)
        = norm_pi pi_dist (A (B f)) := rfl
      _ ≤ sInf (opNorm_set pi_dist h_pos A) * norm_pi pi_dist (B f) := by
          have := opNorm_pi_bound pi_dist h_pos A (B f)
          unfold opNorm_pi at this
          exact this
      _ ≤ sInf (opNorm_set pi_dist h_pos A) * (sInf (opNorm_set pi_dist h_pos B) * norm_pi pi_dist f) := by
          apply mul_le_mul_of_nonneg_left
          · have := opNorm_pi_bound pi_dist h_pos B f
            unfold opNorm_pi at this
            exact this
          · apply Real.sInf_nonneg; intro c hc; exact hc.1
      _ = sInf (opNorm_set pi_dist h_pos A) * sInf (opNorm_set pi_dist h_pos B) * norm_pi pi_dist f := by ring

/-- If c ≥ 0 and ‖A f‖_π ≤ c * ‖f‖_π for all f, then ‖A‖_π ≤ c. -/
lemma opNorm_pi_le_of_bound (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v)
    (A : (V → ℝ) →ₗ[ℝ] (V → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (h_bound : ∀ f, norm_pi pi_dist (A f) ≤ c * norm_pi pi_dist f) :
    opNorm_pi pi_dist h_pos A ≤ c := by
  unfold opNorm_pi
  apply csInf_le (opNorm_set_bddBelow pi_dist h_pos A)
  exact ⟨hc, h_bound⟩

/-! ### 6. Orthogonal Projector -/

/-- **Orthogonal Projector onto 1⊥**.
    P f = f - ⟨f, 1⟩_π · 1 projects onto the orthogonal complement of constants. -/
def P_ortho_pi (pi_dist : V → ℝ) (_h_sum : ∑ v, pi_dist v = 1) (_h_pos : ∀ v, 0 < pi_dist v) :
    (V → ℝ) →ₗ[ℝ] (V → ℝ) :=
  let P_inner : (V → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => inner_pi pi_dist f (fun _ => 1)
      map_add' := by intros; simp [inner_pi_add_left]
      map_smul' := by intros; simp [inner_pi_smul_left] }
  LinearMap.id - (LinearMap.smulRight P_inner (fun _ => 1))

end Geometry
end SGC
