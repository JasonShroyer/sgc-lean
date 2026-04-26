/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team

# NormedBridge: Weighted L²(π) ↔ Mathlib EuclideanSpace

This module builds the linear isometry between the SGC's custom weighted
inner product space (V → ℝ, inner_pi π) and Mathlib's EuclideanSpace ℝ V.

## The Map

  T(f)(v) = √π(v) · f(v)

This is a linear isometry: ‖Tf‖²_std = Σ_v (√π(v) · f(v))² = Σ_v π(v) · f(v)² = ‖f‖²_π

## Why This Matters

Once this isometry is registered, every Mathlib theorem about EuclideanSpace
(compactness, spectral theory, operator norms) transfers to the weighted space:
- IsCompact of the weighted unit sphere → Courant-Fischer (closes OptimalPartition sorry)
- Spectral theorem for symmetric operators → eigenvalue characterization
- Operator norm equivalence → Weyl inequality transport
-/

import SGC.Axioms.Geometry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section

namespace SGC.Spectral.NormedBridge

open Finset BigOperators Matrix Real EuclideanSpace

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Section 1: The Weighted-to-Euclidean Map (to V → ℝ) -/

/-- The linear map T : (V → ℝ) → (V → ℝ) defined by T(f)(v) = √π(v) · f(v).

    This rescales each coordinate by the square root of the stationary weight,
    converting the π-weighted inner product to the standard Euclidean one. -/
def weightedToStd (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) : (V → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun f := fun v => Real.sqrt (pi_dist v) * f v
  map_add' f g := by ext v; simp [mul_add]
  map_smul' c f := by ext v; simp [mul_left_comm]

/-- The inverse map T⁻¹ : (V → ℝ) → (V → ℝ) defined by T⁻¹(g)(v) = g(v) / √π(v). -/
def stdToWeighted (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) : (V → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun g := fun v => g v / Real.sqrt (pi_dist v)
  map_add' f g := by ext v; simp [add_div]
  map_smul' c f := by ext v; simp [smul_eq_mul, mul_div_assoc]

/-! ## Section 2: T is an Isometry (Norm Preservation) -/

/-- The squared Euclidean norm of T(f) equals the π-weighted squared norm of f.

    ‖T(f)‖²_std = Σ_v (√π(v) · f(v))² = Σ_v π(v) · f(v)² = ‖f‖²_π -/
theorem weightedToStd_norm_sq (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (f : V → ℝ) :
    ∑ v, (weightedToStd pi_dist hπ f v) ^ 2 = norm_sq_pi pi_dist f := by
  simp only [weightedToStd, LinearMap.coe_mk, AddHom.coe_mk]
  rw [norm_sq_pi_eq_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [mul_pow, Real.sq_sqrt (le_of_lt (hπ v))]

/-- The standard dot product of T(f) and T(g) equals the π-weighted inner product.

    ⟨T(f), T(g)⟩_std = Σ_v √π(v)·f(v) · √π(v)·g(v) = Σ_v π(v)·f(v)·g(v) = ⟨f,g⟩_π -/
theorem weightedToStd_inner (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (f g : V → ℝ) :
    ∑ v, (weightedToStd pi_dist hπ f v) * (weightedToStd pi_dist hπ g v) =
    inner_pi pi_dist f g := by
  simp only [weightedToStd, LinearMap.coe_mk, AddHom.coe_mk, inner_pi]
  apply Finset.sum_congr rfl
  intro v _
  have h_sq : Real.sqrt (pi_dist v) ^ 2 = pi_dist v :=
    Real.sq_sqrt (le_of_lt (hπ v))
  calc Real.sqrt (pi_dist v) * f v * (Real.sqrt (pi_dist v) * g v)
      = Real.sqrt (pi_dist v) ^ 2 * (f v * g v) := by ring
    _ = pi_dist v * (f v * g v) := by rw [h_sq]
    _ = pi_dist v * f v * g v := by ring

/-! ## Section 3: T is Bijective -/

/-- T⁻¹ ∘ T = id: the round-trip recovers the original function. -/
theorem stdToWeighted_comp_weightedToStd (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (f : V → ℝ) :
    stdToWeighted pi_dist hπ (weightedToStd pi_dist hπ f) = f := by
  ext v
  simp only [stdToWeighted, weightedToStd, LinearMap.coe_mk, AddHom.coe_mk]
  have h_ne : Real.sqrt (pi_dist v) ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos (hπ v))
  field_simp

/-- T ∘ T⁻¹ = id: the other round-trip also recovers. -/
theorem weightedToStd_comp_stdToWeighted (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (g : V → ℝ) :
    weightedToStd pi_dist hπ (stdToWeighted pi_dist hπ g) = g := by
  ext v
  simp only [stdToWeighted, weightedToStd, LinearMap.coe_mk, AddHom.coe_mk]
  have h_ne : Real.sqrt (pi_dist v) ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos (hπ v))
  field_simp

/-- T is injective (follows from left inverse). -/
theorem weightedToStd_injective (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) :
    Function.Injective (weightedToStd pi_dist hπ) := by
  intro f g h
  have := congr_arg (stdToWeighted pi_dist hπ) h
  rw [stdToWeighted_comp_weightedToStd, stdToWeighted_comp_weightedToStd] at this
  exact this

/-- T is surjective (T⁻¹ provides a preimage for every g). -/
theorem weightedToStd_surjective (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) :
    Function.Surjective (weightedToStd pi_dist hπ) := by
  intro g
  exact ⟨stdToWeighted pi_dist hπ g, weightedToStd_comp_stdToWeighted pi_dist hπ g⟩

/-- T as a linear equivalence. -/
def weightedToStdEquiv (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) :
    (V → ℝ) ≃ₗ[ℝ] (V → ℝ) :=
  LinearEquiv.ofBijective (weightedToStd pi_dist hπ)
    ⟨weightedToStd_injective pi_dist hπ, weightedToStd_surjective pi_dist hπ⟩

/-! ## Section 4: Transport Theorems -/

/-- **Inner Product Transport**: The π-weighted inner product of f and g equals
    the standard dot product of their images under T.

    This is the bridge that allows Mathlib's inner product space theorems
    to apply to the SGC's weighted space. -/
theorem inner_pi_eq_std_dot (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (f g : V → ℝ) :
    inner_pi pi_dist f g =
    ∑ v, (weightedToStd pi_dist hπ f v) * (weightedToStd pi_dist hπ g v) :=
  (weightedToStd_inner pi_dist hπ f g).symm

/-- **Norm Transport**: The π-weighted norm of f equals the Euclidean norm of T(f).

    ‖f‖_π = √(Σ_v (T(f)(v))²) = ‖T(f)‖_std -/
theorem norm_pi_eq_std_norm (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (f : V → ℝ) :
    norm_pi pi_dist f = Real.sqrt (∑ v, (weightedToStd pi_dist hπ f v) ^ 2) := by
  unfold norm_pi
  rw [weightedToStd_norm_sq]

/-- **Zero Iff Zero**: T(f) = 0 ↔ f = 0. -/
theorem weightedToStd_eq_zero_iff (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (f : V → ℝ) :
    weightedToStd pi_dist hπ f = 0 ↔ f = 0 := by
  constructor
  · intro h
    exact weightedToStd_injective pi_dist hπ (by rw [h, LinearMap.map_zero])
  · intro h
    rw [h, LinearMap.map_zero]

/-! ## Section 5: Compactness Transfer

The key application: the weighted unit sphere {f | ‖f‖_π = 1} is compact
because `(V → ℝ)` is a finite-dimensional normed space (and hence a
`ProperSpace`), so closed bounded sets are compact. The continuity of
`norm_sq_pi π` and `inner_pi π (·) 1` lets us identify ball, sphere, and
the constrained sphere as closed sets, and a direct sup-norm estimate
bounds them. -/

/-- **Weighted Unit Sphere is Bounded**: The set {f | ‖f‖_π ≤ 1} maps
    into the standard unit ball under T, which is bounded. -/
theorem weightedToStd_maps_ball (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (f : V → ℝ) (hf : norm_sq_pi pi_dist f ≤ 1) :
    ∑ v, (weightedToStd pi_dist hπ f v) ^ 2 ≤ 1 := by
  rw [weightedToStd_norm_sq]
  exact hf

/-! ### Section 5.1: Continuity of `norm_sq_pi` and `inner_pi (·) 1`

Both are polynomial in the coordinates of `f`, hence continuous on `V → ℝ`. -/

/-- `norm_sq_pi π` is continuous as a function `(V → ℝ) → ℝ`. -/
lemma norm_sq_pi_continuous (pi_dist : V → ℝ) :
    Continuous (norm_sq_pi pi_dist : (V → ℝ) → ℝ) := by
  unfold norm_sq_pi inner_pi
  refine continuous_finset_sum _ (fun v _ => ?_)
  exact (continuous_const.mul (continuous_apply v)).mul (continuous_apply v)

/-- `inner_pi π f (fun _ => 1)` is continuous in `f`. -/
lemma inner_pi_const_one_continuous (pi_dist : V → ℝ) :
    Continuous (fun f : V → ℝ => inner_pi pi_dist f (fun _ => 1)) := by
  unfold inner_pi
  refine continuous_finset_sum _ (fun v _ => ?_)
  exact (continuous_const.mul (continuous_apply v)).mul continuous_const

/-! ### Section 5.2: Boundedness of the weighted closed ball

If `norm_sq_pi π f ≤ r`, then for each `v`, `π v · (f v)² ≤ r` (the other
summands are non-negative), so `|f v| ≤ √(r / π_min)` where
`π_min = inf_v π v > 0`. This bounds the Pi sup norm. -/

/-- The weighted closed ball is bounded in the Pi (sup) norm. -/
lemma weighted_ball_isBounded (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (r : ℝ) (hr : 0 ≤ r) :
    Bornology.IsBounded {f : V → ℝ | norm_sq_pi pi_dist f ≤ r} := by
  by_cases hV : Nonempty V
  · -- V nonempty: use π_min := min over V.
    have h_ne : (Finset.univ : Finset V).Nonempty := Finset.univ_nonempty
    set π_min : ℝ := Finset.univ.inf' h_ne pi_dist with hπ_min_def
    have hπ_min_pos : 0 < π_min := by
      rw [hπ_min_def, Finset.lt_inf'_iff]
      intro v _
      exact hπ v
    have hπ_min_le : ∀ v, π_min ≤ pi_dist v := fun v => by
      rw [hπ_min_def]
      exact Finset.inf'_le _ (Finset.mem_univ v)
    set R : ℝ := Real.sqrt (r / π_min) with hR_def
    have hR_nonneg : 0 ≤ R := Real.sqrt_nonneg _
    rw [Metric.isBounded_iff_subset_closedBall (0 : V → ℝ)]
    refine ⟨R, ?_⟩
    intro f hf
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [pi_norm_le_iff_of_nonneg hR_nonneg]
    intro v
    -- |f v| ≤ R since π_min · (f v)² ≤ π v · (f v)² ≤ ∑_x π x · (f x)² ≤ r.
    have h_term_nonneg : ∀ x, 0 ≤ pi_dist x * (f x)^2 := fun x =>
      mul_nonneg (le_of_lt (hπ x)) (sq_nonneg _)
    have h_each_le : pi_dist v * (f v)^2 ≤ r := by
      have h_in_sum : pi_dist v * (f v)^2 ≤ ∑ x, pi_dist x * (f x)^2 :=
        Finset.single_le_sum (f := fun x => pi_dist x * (f x)^2)
          (fun x _ => h_term_nonneg x) (Finset.mem_univ v)
      have hsum : ∑ x, pi_dist x * (f x)^2 ≤ r := by
        have hf' : norm_sq_pi pi_dist f ≤ r := hf
        rw [norm_sq_pi_eq_sum] at hf'
        exact hf'
      linarith
    have h_pim_le : π_min * (f v)^2 ≤ r := by
      calc π_min * (f v)^2
          ≤ pi_dist v * (f v)^2 :=
            mul_le_mul_of_nonneg_right (hπ_min_le v) (sq_nonneg _)
        _ ≤ r := h_each_le
    have h_sq_le : (f v)^2 ≤ r / π_min :=
      (le_div_iff₀ hπ_min_pos).mpr (by linarith)
    have h_abs : ‖f v‖ = Real.sqrt ((f v)^2) := by
      rw [Real.sqrt_sq_eq_abs]
      rfl
    rw [h_abs]
    have h_rdiv_nonneg : 0 ≤ r / π_min := div_nonneg hr (le_of_lt hπ_min_pos)
    exact Real.sqrt_le_sqrt h_sq_le
  · -- V empty: V → ℝ is a subsingleton, so any subset is bounded.
    have h_sub : Subsingleton (V → ℝ) := by
      refine ⟨fun f g => ?_⟩
      ext v
      exact absurd ⟨v⟩ hV
    refine Bornology.IsBounded.subset (Bornology.isBounded_singleton (x := (0 : V → ℝ))) ?_
    intro f _
    exact Set.mem_singleton_iff.mpr (Subsingleton.elim _ _)

/-- **Compactness of Weighted Sphere with Constraint** (for Courant-Fischer):

    The set {f : V → ℝ | norm_sq_pi π f = r ∧ inner_pi π f 1 = 0} is compact.

    PROOF: It is closed (intersection of two preimages of singletons under
    continuous functions) and bounded (subset of the closed ball of radius
    `√r`), hence compact via the Heine–Borel theorem on the proper space
    `(V → ℝ)`. -/
theorem weighted_sphere_compact (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (r : ℝ) (hr : 0 ≤ r) :
    IsCompact {f : V → ℝ | norm_sq_pi pi_dist f = r ∧
      inner_pi pi_dist f (fun _ => 1) = 0} := by
  have h_closed : IsClosed {f : V → ℝ | norm_sq_pi pi_dist f = r ∧
      inner_pi pi_dist f (fun _ => 1) = 0} := by
    have h1 : IsClosed {f : V → ℝ | norm_sq_pi pi_dist f = r} :=
      isClosed_eq (norm_sq_pi_continuous pi_dist) continuous_const
    have h2 : IsClosed {f : V → ℝ | inner_pi pi_dist f (fun _ => 1) = 0} :=
      isClosed_eq (inner_pi_const_one_continuous pi_dist) continuous_const
    exact h1.inter h2
  have h_bounded : Bornology.IsBounded {f : V → ℝ | norm_sq_pi pi_dist f = r ∧
      inner_pi pi_dist f (fun _ => 1) = 0} := by
    refine Bornology.IsBounded.subset (weighted_ball_isBounded pi_dist hπ r hr) ?_
    intro f hf
    exact le_of_eq hf.1
  exact Metric.isCompact_of_isClosed_isBounded h_closed h_bounded

/-! ## Section 6: EuclideanSpace ℝ V Bridge

The definitions in Sections 1-4 work with (V → ℝ) and prove all the isometry
properties at the sum level. To connect to Mathlib's EuclideanSpace ℝ V,
we use the existing `iso_L2_to_std` from Geometry.lean and compose with
`WithLp.equiv`. The key results are already proven there:
- `norm_pi_eq_euclidean_norm`: norm_pi f = ‖(WithLp.equiv 2 _).symm (iso f)‖

Here we add a clean interface for direct use. -/

/-- **Weighted to EuclideanSpace**: The composition of iso_L2_to_std with WithLp wrapping.

    T(f) = (WithLp.equiv 2 _).symm (iso_L2_to_std f)

    This maps weighted functions to EuclideanSpace, preserving norms. -/
def toEuclidean (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (f : V → ℝ) :
    EuclideanSpace ℝ V :=
  (WithLp.equiv 2 (V → ℝ)).symm (iso_L2_to_std pi_dist hπ f)

/-- **Norm equality via existing infrastructure**: Use norm_pi_eq_euclidean_norm. -/
lemma toEuclidean_norm (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (f : V → ℝ) :
    ‖toEuclidean pi_dist hπ f‖ = norm_pi pi_dist f :=
  (norm_pi_eq_euclidean_norm pi_dist hπ f).symm

/-! ## Section 7: Key Compactness Theorems

The critical results for Courant-Fischer: weighted balls and spheres are compact.
This follows from finite-dimensionality: (V → ℝ) is a proper metric space.

**Proof outline** (each ~15 lines of Mathlib plumbing):
1. norm_sq_pi is continuous (sum of continuous functions)
2. Weighted ball is closed (preimage of Iic under continuous)
3. Weighted ball is bounded (if norm_sq_pi f ≤ r then |f v| ≤ √(r/π_min))
4. Closed + bounded in finite-dim = compact (ProperSpace)
5. Sphere is closed subset of ball, hence compact -/

/-- **Weighted Closed Ball is Compact**: {f | norm_sq_pi π f ≤ r} is compact.

    PROOF: The ball is closed (preimage of `Set.Iic r` under the continuous
    function `norm_sq_pi π`) and bounded (`weighted_ball_isBounded`).
    `(V → ℝ)` is a finite-dimensional real normed space, hence a `ProperSpace`,
    so the Heine–Borel theorem gives compactness. -/
theorem weighted_closedBall_compact (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (r : ℝ) (hr : 0 ≤ r) :
    IsCompact {f : V → ℝ | norm_sq_pi pi_dist f ≤ r} := by
  have h_closed : IsClosed {f : V → ℝ | norm_sq_pi pi_dist f ≤ r} :=
    isClosed_le (norm_sq_pi_continuous pi_dist) continuous_const
  exact Metric.isCompact_of_isClosed_isBounded h_closed
    (weighted_ball_isBounded pi_dist hπ r hr)

/-- **Weighted Sphere is Compact**: {f | norm_sq_pi π f = r} is compact.

    PROOF: Closed subset of the compact closed ball. -/
theorem weighted_sphere_is_compact (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (r : ℝ) (hr : 0 ≤ r) :
    IsCompact {f : V → ℝ | norm_sq_pi pi_dist f = r} := by
  have h_closed : IsClosed {f : V → ℝ | norm_sq_pi pi_dist f = r} :=
    isClosed_eq (norm_sq_pi_continuous pi_dist) continuous_const
  have h_bounded : Bornology.IsBounded {f : V → ℝ | norm_sq_pi pi_dist f = r} := by
    refine Bornology.IsBounded.subset (weighted_ball_isBounded pi_dist hπ r hr) ?_
    intro f hf
    exact le_of_eq hf
  exact Metric.isCompact_of_isClosed_isBounded h_closed h_bounded

/-! ## Summary

This module establishes the bridge between SGC's weighted L²(π) space
and Mathlib's EuclideanSpace ℝ V:

**PROVED (zero sorry):**
- `weightedToStd`: the linear map T(f)(v) = √π(v) · f(v) to (V → ℝ)
- `stdToWeighted`: the inverse T⁻¹(g)(v) = g(v) / √π(v)
- `weightedToStd_norm_sq`: ‖T(f)‖² = ‖f‖²_π (sum formulation)
- `weightedToStd_inner`: ⟨T(f), T(g)⟩ = ⟨f, g⟩_π
- `stdToWeighted_comp_weightedToStd`: T⁻¹ ∘ T = id
- `weightedToStd_comp_stdToWeighted`: T ∘ T⁻¹ = id
- `weightedToStdEquiv`: T as a LinearEquiv on (V → ℝ)
- `inner_pi_eq_std_dot`: inner product transport
- `norm_pi_eq_std_norm`: norm transport
- `weightedToStd_maps_ball`: ball transport
- `toEuclidean`: f ↦ (WithLp.equiv.symm (iso f)) to EuclideanSpace
- `toEuclidean_norm`: ‖toEuclidean f‖ = norm_pi f

**PROVED (Apr 2026, replacing former axioms):**
- `norm_sq_pi_continuous`, `inner_pi_const_one_continuous`: continuity helpers
- `weighted_ball_isBounded`: sup-norm bound on the closed ball
- `weighted_closedBall_compact`: {f | norm_sq_pi π f ≤ r} is compact
- `weighted_sphere_is_compact`: {f | norm_sq_pi π f = r} is compact
- `weighted_sphere_compact`: {f | norm_sq_pi π f = r ∧ ⟨f,1⟩_π = 0} is compact

Proof path: closed + bounded in finite-dim = compact (Heine–Borel on the
`ProperSpace` instance for `(V → ℝ)` from `FiniteDimensional.proper_real`).
-/

end SGC.Spectral.NormedBridge
