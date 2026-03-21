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
because it is the preimage of the standard unit sphere under the
continuous bijection T. Since V is Fintype, V → ℝ is finite-dimensional,
and closed bounded sets are compact. -/

/-- **Weighted Unit Sphere is Bounded**: The set {f | ‖f‖_π ≤ 1} maps
    into the standard unit ball under T, which is bounded. -/
theorem weightedToStd_maps_ball (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (f : V → ℝ) (hf : norm_sq_pi pi_dist f ≤ 1) :
    ∑ v, (weightedToStd pi_dist hπ f v) ^ 2 ≤ 1 := by
  rw [weightedToStd_norm_sq]
  exact hf

/-- **Compactness of Weighted Sphere with Constraint** (for Courant-Fischer):

    The set {f : V → ℝ | norm_sq_pi π f = r ∧ inner_pi π f 1 = 0} is compact.

    PROOF: Intersection of compact sphere (axiom) with closed hyperplane. -/
axiom weighted_sphere_compact (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (r : ℝ) (hr : 0 ≤ r) :
    IsCompact {f : V → ℝ | norm_sq_pi pi_dist f = r ∧
      inner_pi pi_dist f (fun _ => 1) = 0}

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

    PROOF: The ball is closed (preimage of [0,r] under continuous norm_sq_pi)
    and bounded (norm_sq_pi f ≤ r implies ‖f‖_∞ ≤ √(r/π_min)).
    In finite dimensions, closed + bounded = compact. -/
axiom weighted_closedBall_compact (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (r : ℝ) (hr : 0 ≤ r) :
    IsCompact {f : V → ℝ | norm_sq_pi pi_dist f ≤ r}

/-- **Weighted Sphere is Compact**: {f | norm_sq_pi π f = r} is compact.

    PROOF: Closed subset of compact ball. -/
axiom weighted_sphere_is_compact (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (r : ℝ) (hr : 0 ≤ r) :
    IsCompact {f : V → ℝ | norm_sq_pi pi_dist f = r}

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

**AXIOMS (3, with documented proof paths):**
- `weighted_sphere_compact`: {f | norm_sq_pi π f = r ∧ ⟨f,1⟩_π = 0} is compact
- `weighted_closedBall_compact`: {f | norm_sq_pi π f ≤ r} is compact
- `weighted_sphere_is_compact`: {f | norm_sq_pi π f = r} is compact

Proof path: closed + bounded in finite-dim = compact (ProperSpace).
-/

end SGC.Spectral.NormedBridge
