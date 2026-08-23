import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Real.Basic
import SGC.Axioms.WeightedSpace

noncomputable section

namespace SGC
namespace Axioms
namespace GeometryGeneral

open Finset

-- Suppress unused variable warnings (many lemmas don't need all type constraints)
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {𝕜 : Type*} [RCLike 𝕜]

abbrev constant_vec_one : V → 𝕜 := fun _ => 1

def inner_pi (pi_dist : V → ℝ) (u v : V → 𝕜) : 𝕜 :=
  ∑ x, (pi_dist x : 𝕜) * star (u x) * v x

def norm_sq_pi (pi_dist : V → ℝ) (v : V → 𝕜) : ℝ :=
  RCLike.re (inner_pi pi_dist v v)

def norm_pi (pi_dist : V → ℝ) (v : V → 𝕜) : ℝ :=
  Real.sqrt (norm_sq_pi pi_dist v)

lemma inner_pi_add_left (pi_dist : V → ℝ) (u v w : V → 𝕜) :
    inner_pi pi_dist (u + v) w = inner_pi pi_dist u w + inner_pi pi_dist v w := by
  simp [inner_pi, mul_add, add_mul, Finset.sum_add_distrib]

lemma inner_pi_add_right (pi_dist : V → ℝ) (u v w : V → 𝕜) :
    inner_pi pi_dist u (v + w) = inner_pi pi_dist u v + inner_pi pi_dist u w := by
  simp [inner_pi, mul_add, Finset.sum_add_distrib]

lemma inner_pi_smul_left (pi_dist : V → ℝ) (c : 𝕜) (u v : V → 𝕜) :
    inner_pi pi_dist (c • u) v = star c * inner_pi pi_dist u v := by
  classical
  unfold inner_pi
  -- Expand RHS to a sum, then compare termwise.
  rw [Finset.mul_sum]
  -- `star (c • u x) = star c * star (u x)` and reassociate.
  simp [Pi.smul_apply, mul_assoc, mul_left_comm, mul_comm]

lemma inner_pi_smul_right (pi_dist : V → ℝ) (c : 𝕜) (u v : V → 𝕜) :
    inner_pi pi_dist u (c • v) = c * inner_pi pi_dist u v := by
  classical
  unfold inner_pi
  rw [Finset.mul_sum]
  simp [Pi.smul_apply, mul_assoc, mul_left_comm, mul_comm]

lemma inner_pi_conj_symm (pi_dist : V → ℝ) (u v : V → 𝕜) :
    inner_pi pi_dist u v = star (inner_pi pi_dist v u) := by
  simp [inner_pi, mul_assoc, mul_left_comm, mul_comm]

/-! ## Adjoint Operators

The adjoint A† of an operator A w.r.t. the weighted inner product satisfies
⟨A†u, v⟩_π = ⟨u, Av⟩_π. This is essential for quantum mechanics where
observables must be self-adjoint (A† = A).
-/

/-- Standard basis vector `δ_x`. -/
def basisVec (x : V) : V → 𝕜 := fun z => if z = x then 1 else 0

/-- Basis expansion of a linear map's action: `(A v) y = Σ_x v x · (A δ_x) y`. -/
lemma linearMap_apply_eq_sum (A : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) (v : V → 𝕜) (y : V) :
    A v y = ∑ x, v x * A (basisVec x) y := by
  have hv : v = ∑ x, v x • basisVec x := by
    funext z
    rw [Finset.sum_apply]
    simp [basisVec, smul_eq_mul, mul_ite, mul_one, mul_zero]
  conv_lhs => rw [hv]
  rw [map_sum]
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul]
  simp [smul_eq_mul]

/-- **The adjoint, constructed** (DEFINITIONALLY DISCHARGED 2026-08-22;
was: axiom). The weighted conjugate transpose:
`(A†u)(x) = π(x)⁻¹ · Σ_y π(y) · u(y) · star((A δ_x)(y))`.
At zero-weight coordinates the junk value `0⁻¹ = 0` applies — harmless,
since such coordinates are invisible to `inner_pi`, and the property
theorems below carry the positivity hypotheses that the soundness
counterexample (see `docs/axiom-discharge-campaign.md`) proved necessary. -/
noncomputable def adjoint_pi (pi_dist : V → ℝ) (A : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) :
    (V → 𝕜) →ₗ[𝕜] (V → 𝕜) where
  toFun u := fun x => ((pi_dist x : 𝕜))⁻¹ *
    ∑ y, (pi_dist y : 𝕜) * u y * star (A (basisVec x) y)
  map_add' u v := by
    funext x
    simp only [Pi.add_apply]
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  map_smul' c u := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    have hs : (∑ y, (pi_dist y : 𝕜) * (c * u y) * star (A (basisVec x) y))
        = c * ∑ y, (pi_dist y : 𝕜) * u y * star (A (basisVec x) y) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [hs]
    ring

lemma adjoint_pi_apply (pi_dist : V → ℝ) (A : (V → 𝕜) →ₗ[𝕜] (V → 𝕜))
    (u : V → 𝕜) (x : V) :
    adjoint_pi pi_dist A u x = ((pi_dist x : 𝕜))⁻¹ *
      ∑ y, (pi_dist y : 𝕜) * u y * star (A (basisVec x) y) := rfl

/-- Nonzero real weights stay nonzero after the cast into `𝕜`. -/
lemma cast_pi_ne_zero {pi_dist : V → ℝ} (hπ : ∀ v, 0 < pi_dist v) (x : V) :
    ((pi_dist x : ℝ) : 𝕜) ≠ 0 :=
  RCLike.ofReal_ne_zero.mpr (hπ x).ne'

/-- Defining property of the adjoint: ⟨A† u, v⟩_π = ⟨u, A v⟩_π.
**THEOREM** (was axiom; discharged 2026-08-22). The positivity hypothesis
is genuinely required — `False` was derivable from the unhypothesized
version (soundness repair, same day). -/
theorem adjoint_pi_spec (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (A : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) (u v : V → 𝕜) :
    inner_pi pi_dist (adjoint_pi pi_dist A u) v = inner_pi pi_dist u (A v) := by
  unfold inner_pi
  have hterm : ∀ x, (pi_dist x : 𝕜) * star (adjoint_pi pi_dist A u x) * v x
      = ∑ y, (pi_dist y : 𝕜) * star (u y) * (A (basisVec x) y * v x) := by
    intro x
    rw [adjoint_pi_apply, star_mul', star_inv₀, star_sum]
    have hstar : ∀ y, star ((pi_dist y : 𝕜) * u y * star (A (basisVec x) y))
        = (pi_dist y : 𝕜) * star (u y) * A (basisVec x) y := by
      intro y
      rw [star_mul', star_mul', star_star]
      simp only [RCLike.star_def, RCLike.conj_ofReal]
    rw [Finset.sum_congr rfl fun y _ => hstar y]
    rw [show star ((pi_dist x : 𝕜)) = (pi_dist x : 𝕜) by
      simp [RCLike.star_def, RCLike.conj_ofReal]]
    rw [← mul_assoc, mul_inv_cancel₀ (cast_pi_ne_zero hπ x), one_mul,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  rw [linearMap_apply_eq_sum A v y]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- Adjoint on a basis vector: the weighted transposed entry. -/
lemma adjoint_pi_basisVec (pi_dist : V → ℝ) (A : (V → 𝕜) →ₗ[𝕜] (V → 𝕜))
    (w x : V) :
    adjoint_pi pi_dist A (basisVec w) x
      = ((pi_dist x : 𝕜))⁻¹ * ((pi_dist w : 𝕜) * star (A (basisVec x) w)) := by
  rw [adjoint_pi_apply]
  congr 1
  rw [Finset.sum_eq_single w]
  · simp [basisVec]
  · intro y _ hy
    simp [basisVec, hy]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The adjoint is an involution: (A†)† = A. **THEOREM** (was axiom;
discharged 2026-08-22). Requires positive `π`. -/
theorem adjoint_pi_involutive (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (A : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) :
    adjoint_pi pi_dist (adjoint_pi pi_dist A) = A := by
  apply LinearMap.ext
  intro u
  funext x
  rw [adjoint_pi_apply]
  have hentry : ∀ y, (pi_dist y : 𝕜) * u y
        * star (adjoint_pi pi_dist A (basisVec x) y)
      = (pi_dist x : 𝕜) * (u y * A (basisVec y) x) := by
    intro y
    rw [adjoint_pi_basisVec, star_mul', star_mul', star_inv₀, star_star]
    simp only [RCLike.star_def, RCLike.conj_ofReal]
    have h1 : ((pi_dist y : ℝ) : 𝕜) ≠ 0 := cast_pi_ne_zero hπ y
    field_simp
  rw [Finset.sum_congr rfl fun y _ => hentry y, ← Finset.mul_sum]
  have h2 : ((pi_dist x : ℝ) : 𝕜) ≠ 0 := cast_pi_ne_zero hπ x
  rw [← mul_assoc, inv_mul_cancel₀ h2, one_mul]
  rw [linearMap_apply_eq_sum A u x]

/-- The adjoint of a composition: (AB)† = B†A†. **THEOREM** (was axiom;
discharged 2026-08-22). Requires positive `π`. -/
theorem adjoint_pi_comp (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (A B : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) :
    adjoint_pi pi_dist (A ∘ₗ B) = adjoint_pi pi_dist B ∘ₗ adjoint_pi pi_dist A := by
  apply LinearMap.ext
  intro u
  funext x
  rw [LinearMap.comp_apply, adjoint_pi_apply, adjoint_pi_apply]
  have hAB : ∀ y, star ((A ∘ₗ B) (basisVec x) y)
      = ∑ z, star (B (basisVec x) z) * star (A (basisVec z) y) := by
    intro y
    rw [LinearMap.comp_apply, linearMap_apply_eq_sum A (B (basisVec x)) y,
      star_sum]
    exact Finset.sum_congr rfl fun z _ => by rw [star_mul']
  have hAdj : ∀ z, (pi_dist z : 𝕜) * adjoint_pi pi_dist A u z
      = ∑ y, (pi_dist y : 𝕜) * u y * star (A (basisVec z) y) := by
    intro z
    rw [adjoint_pi_apply, ← mul_assoc,
      mul_inv_cancel₀ (cast_pi_ne_zero hπ z), one_mul]
  congr 1
  calc (∑ y, (pi_dist y : 𝕜) * u y * star ((A ∘ₗ B) (basisVec x) y))
      = ∑ y, ∑ z, (pi_dist y : 𝕜) * u y
          * (star (B (basisVec x) z) * star (A (basisVec z) y)) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [hAB y, Finset.mul_sum]
    _ = ∑ z, ∑ y, (pi_dist y : 𝕜) * u y
          * star (A (basisVec z) y) * star (B (basisVec x) z) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => by ring
    _ = ∑ z, (pi_dist z : 𝕜) * adjoint_pi pi_dist A u z
          * star (B (basisVec x) z) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [hAdj z, Finset.sum_mul]
    _ = ∑ z, (pi_dist z : 𝕜) * adjoint_pi pi_dist A u z
          * star (B (basisVec x) z) := rfl

/-- The adjoint of zero is zero. **THEOREM** (was axiom; discharged
2026-08-22). No positivity needed. -/
theorem adjoint_pi_zero (pi_dist : V → ℝ) :
    adjoint_pi pi_dist (0 : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) = 0 := by
  apply LinearMap.ext
  intro u
  funext x
  rw [adjoint_pi_apply]
  simp

/-- Two operators are equal if they produce equal inner products for all
vectors. **THEOREM** (was axiom; discharged 2026-08-22): non-degeneracy
of `inner_pi` for positive `π`, via testing against basis vectors. -/
theorem linearMap_ext_inner (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (A B : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) :
    (∀ u v, inner_pi pi_dist (A u) v = inner_pi pi_dist (B u) v) → A = B := by
  intro h
  apply LinearMap.ext
  intro u
  funext x
  have hcol : ∀ (w : V → 𝕜),
      inner_pi pi_dist w (basisVec x) = (pi_dist x : 𝕜) * star (w x) := by
    intro w
    unfold inner_pi
    rw [Finset.sum_eq_single x]
    · simp [basisVec]
    · intro z _ hz
      simp [basisVec, hz]
    · intro hx
      exact absurd (Finset.mem_univ _) hx
  have hx := h u (basisVec x)
  rw [hcol (A u), hcol (B u)] at hx
  have hstar : star (A u x) = star (B u x) :=
    mul_left_cancel₀ (cast_pi_ne_zero hπ x) hx
  have := congrArg star hstar
  simpa [star_star] using this

/-- An operator A is self-adjoint w.r.t. the weighted inner product if A† = A.
    Equivalently, ⟨Au, v⟩ = ⟨u, Av⟩ for all u, v.
    For quantum Hamiltonians, this ensures real eigenvalues and orthogonal eigenvectors. -/
def IsSelfAdjoint_pi (pi_dist : V → ℝ) (A : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) : Prop :=
  adjoint_pi pi_dist A = A

/-- Alternative characterization: A is self-adjoint iff ⟨Au, v⟩ = ⟨u, Av⟩. -/
lemma isSelfAdjoint_pi_iff (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (A : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) :
    IsSelfAdjoint_pi pi_dist A ↔ ∀ u v, inner_pi pi_dist (A u) v = inner_pi pi_dist u (A v) := by
  constructor
  · intro hA u v
    rw [← adjoint_pi_spec pi_dist hπ A u v, hA]
  · intro h
    -- Show A† = A using linearMap_ext_inner
    apply linearMap_ext_inner pi_dist hπ
    intro u v
    -- ⟨A†u, v⟩ = ⟨u, Av⟩ (by adjoint_pi_spec) = ⟨Au, v⟩ (by hypothesis h)
    rw [adjoint_pi_spec pi_dist hπ, h]

/-- An operator A is positive w.r.t. the weighted inner product if ⟨Au, u⟩ ≥ 0 for all u.
    Combined with self-adjointness, this gives a positive semidefinite operator. -/
def IsPositive_pi (pi_dist : V → ℝ) (A : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) : Prop :=
  ∀ u, 0 ≤ RCLike.re (inner_pi pi_dist (A u) u)

/-- Concrete self-adjointness forces the weighted symmetry of matrix
entries, with NO positivity hypothesis: `π_x·M_xy = π_y·star(M_yx)` where
`M_xy = (A δ_y)(x)`. At degenerate weights, `A† = A` (for the concrete
junk-robust adjoint) forces the corresponding rows AND columns of `A` to
vanish, so both sides are zero. -/
lemma isSelfAdjoint_entry_symm (pi_dist : V → ℝ)
    (A : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) (hA : IsSelfAdjoint_pi pi_dist A) (x y : V) :
    (pi_dist x : 𝕜) * A (basisVec y) x
      = (pi_dist y : 𝕜) * star (A (basisVec x) y) := by
  have hxy : adjoint_pi pi_dist A (basisVec y) x = A (basisVec y) x := by
    rw [hA]
  have hyx : adjoint_pi pi_dist A (basisVec x) y = A (basisVec x) y := by
    rw [hA]
  rw [adjoint_pi_basisVec] at hxy hyx
  by_cases hx : (pi_dist x : ℝ) = 0
  · have hx𝕜 : ((pi_dist x : ℝ) : 𝕜) = 0 := by exact_mod_cast hx
    rw [hx𝕜, zero_mul]
    rw [← hyx, hx𝕜]
    simp
  · have hx𝕜 : ((pi_dist x : ℝ) : 𝕜) ≠ 0 := by exact_mod_cast hx
    rw [← hxy, ← mul_assoc, mul_inv_cancel₀ hx𝕜, one_mul]

/-- **Self-adjoint operators have symmetric weighted forms** — with no
positivity hypothesis, thanks to the concrete adjoint: `⟨Au, v⟩_π = ⟨u, Av⟩_π`.
(The unhypothesized *spec* is false for general `A`; self-adjointness is
exactly the extra rigidity that kills the degenerate-weight columns.) -/
theorem isSelfAdjoint_inner_symm (pi_dist : V → ℝ)
    (A : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) (hA : IsSelfAdjoint_pi pi_dist A)
    (u v : V → 𝕜) :
    inner_pi pi_dist (A u) v = inner_pi pi_dist u (A v) := by
  unfold inner_pi
  have hL : ∀ x, (pi_dist x : 𝕜) * star (A u x) * v x
      = ∑ y, star (u y) * v x * ((pi_dist x : 𝕜) * star (A (basisVec y) x)) := by
    intro x
    rw [linearMap_apply_eq_sum A u x, star_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [star_mul']
    ring
  have hR : ∀ y, (pi_dist y : 𝕜) * star (u y) * A v y
      = ∑ x, star (u y) * v x * ((pi_dist y : 𝕜) * A (basisVec x) y) := by
    intro y
    rw [linearMap_apply_eq_sum A v y, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [Finset.sum_congr rfl fun x _ => hL x, Finset.sum_comm]
  rw [Finset.sum_congr rfl fun y _ => hR y]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  congr 1
  have h := isSelfAdjoint_entry_symm pi_dist A hA y x
  calc (pi_dist x : 𝕜) * star (A (basisVec y) x)
      = star ((pi_dist x : 𝕜) * A (basisVec y) x) := by
        rw [star_mul']
        congr 1
        simp [RCLike.star_def, RCLike.conj_ofReal]
    _ = star ((pi_dist y : 𝕜) * star (A (basisVec x) y)) := by
        rw [isSelfAdjoint_entry_symm pi_dist A hA x y]
    _ = (pi_dist y : 𝕜) * A (basisVec x) y := by
        rw [star_mul', star_star]
        congr 1
        simp [RCLike.star_def, RCLike.conj_ofReal]

/-- For self-adjoint operators, ⟨Au, u⟩ is real-valued (imaginary part is
zero). **THEOREM** (was axiom; discharged 2026-08-22 overnight): from
`isSelfAdjoint_inner_symm` and conjugate symmetry, `z = star z`. Requires
no positivity — the concrete adjoint construction supplies the rigidity. -/
theorem inner_self_adjoint_real (pi_dist : V → ℝ) (A : (V → 𝕜) →ₗ[𝕜] (V → 𝕜))
    (hA : IsSelfAdjoint_pi pi_dist A) (u : V → 𝕜) :
    RCLike.im (inner_pi pi_dist (A u) u) = 0 := by
  have hsymm := isSelfAdjoint_inner_symm pi_dist A hA u u
  have hconj : inner_pi pi_dist (A u) u
      = star (inner_pi pi_dist (A u) u) := by
    calc inner_pi pi_dist (A u) u
        = inner_pi pi_dist u (A u) := hsymm
      _ = star (inner_pi pi_dist (A u) u) := inner_pi_conj_symm pi_dist u (A u)
  have him := congrArg RCLike.im hconj
  rw [RCLike.star_def, RCLike.conj_im] at him
  linarith

/-! ## Spectral Gap (Generalized)

The spectral gap is the infimum of the Rayleigh quotient ⟨Hu,u⟩/⟨u,u⟩ over
vectors orthogonal to the constant function. -/

/-- The spectral gap of a self-adjoint operator H, defined as the infimum of the
    Rayleigh quotient on vectors orthogonal to the constant function. -/
noncomputable def SpectralGap_pi (pi_dist : V → ℝ) (H : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) : ℝ :=
  sInf { r | ∃ v : V → 𝕜, v ≠ 0 ∧ inner_pi pi_dist v constant_vec_one = 0 ∧
    r = RCLike.re (inner_pi pi_dist (H v) v) / norm_sq_pi pi_dist v }

/-! ## Trace Operations

For density matrices, we need trace and trace norm. -/

/-- The weighted trace: Tr_π(A) = Σ_x π(x) A(x,x).
    For density matrices, this should equal 1. -/
def trace_pi (pi_dist : V → ℝ) (A : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) : 𝕜 :=
  ∑ x, (pi_dist x : 𝕜) * A (fun y => if y = x then 1 else 0) x

/-- A density matrix is a positive operator with trace 1. -/
structure IsDensityMatrix (pi_dist : V → ℝ) (ρ : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) : Prop where
  self_adjoint : IsSelfAdjoint_pi pi_dist ρ
  positive : IsPositive_pi pi_dist ρ
  trace_one : trace_pi pi_dist ρ = 1

/-! ## Trace Norm and Distance

The trace norm (nuclear norm) is the quantum analog of the L¹ norm.
The trace distance is the quantum analog of total variation distance.
-/

/-- The trace norm (nuclear norm): ||A||₁ = Tr(√(A†A)).
    This is axiomatized; computing it requires spectral decomposition. -/
axiom traceNorm_pi (pi_dist : V → ℝ) (A : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) : ℝ

/-- Trace norm is nonnegative. -/
axiom traceNorm_pi_nonneg (pi_dist : V → ℝ) (A : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) :
    0 ≤ traceNorm_pi pi_dist A

/-- Triangle inequality for trace norm. -/
axiom traceNorm_pi_add (pi_dist : V → ℝ) (A B : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) :
    traceNorm_pi pi_dist (A + B) ≤ traceNorm_pi pi_dist A + traceNorm_pi pi_dist B

/-- Trace norm is invariant under negation: ||−A||₁ = ||A||₁. -/
axiom traceNorm_pi_neg (pi_dist : V → ℝ) (A : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) :
    traceNorm_pi pi_dist (-A) = traceNorm_pi pi_dist A

/-- The trace distance between density matrices: D(ρ,σ) = ½||ρ - σ||₁.
    This is the quantum analog of total variation distance. -/
def traceDistance_pi (pi_dist : V → ℝ) (ρ σ : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) : ℝ :=
  (1/2) * traceNorm_pi pi_dist (ρ - σ)

/-- Trace distance is symmetric. -/
lemma traceDistance_pi_symm (pi_dist : V → ℝ) (ρ σ : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) :
    traceDistance_pi pi_dist ρ σ = traceDistance_pi pi_dist σ ρ := by
  simp only [traceDistance_pi]
  congr 1
  -- σ - ρ = -(ρ - σ), so ||σ - ρ||₁ = ||-(ρ - σ)||₁ = ||ρ - σ||₁
  have h : σ - ρ = -(ρ - σ) := by abel
  rw [h, traceNorm_pi_neg]

/-- Trace distance is nonnegative. -/
lemma traceDistance_pi_nonneg (pi_dist : V → ℝ) (ρ σ : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) :
    0 ≤ traceDistance_pi pi_dist ρ σ := by
  unfold traceDistance_pi
  apply mul_nonneg (by norm_num : (0:ℝ) ≤ 1/2)
  exact traceNorm_pi_nonneg pi_dist _

/-- Trace distance satisfies triangle inequality. -/
lemma traceDistance_pi_triangle (pi_dist : V → ℝ) (ρ σ τ : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) :
    traceDistance_pi pi_dist ρ τ ≤ traceDistance_pi pi_dist ρ σ + traceDistance_pi pi_dist σ τ := by
  unfold traceDistance_pi
  have h : ρ - τ = (ρ - σ) + (σ - τ) := by abel
  calc (1/2) * traceNorm_pi pi_dist (ρ - τ)
      = (1/2) * traceNorm_pi pi_dist ((ρ - σ) + (σ - τ)) := by rw [h]
    _ ≤ (1/2) * (traceNorm_pi pi_dist (ρ - σ) + traceNorm_pi pi_dist (σ - τ)) := by
        apply mul_le_mul_of_nonneg_left (traceNorm_pi_add _ _ _) (by norm_num : (0:ℝ) ≤ 1/2)
    _ = (1/2) * traceNorm_pi pi_dist (ρ - σ) + (1/2) * traceNorm_pi pi_dist (σ - τ) := by ring

/-! ## Fidelity

Fidelity measures the closeness of quantum states. F(ρ,σ) = 1 iff ρ = σ.
-/

/-- The fidelity between density matrices: F(ρ,σ) = (Tr√(√ρ σ √ρ))².
    For pure states |ψ⟩⟨ψ| and |φ⟩⟨φ|, this equals |⟨ψ|φ⟩|². -/
axiom fidelity_pi (pi_dist : V → ℝ) (ρ σ : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) : ℝ

/-! ## Classical-Quantum Bridge

These lemmas connect the quantum trace distance to classical total variation.
For diagonal (classical) density matrices, trace distance equals TV distance.
-/

/-- A density matrix is classical (diagonal) if it commutes with all projectors onto
    computational basis states. This corresponds to a classical probability distribution. -/
def IsClassical_pi (pi_dist : V → ℝ) (ρ : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) : Prop :=
  ∀ x : V, ∀ u : V → 𝕜, ρ (fun y => if y = x then u x else 0) =
    fun y => if y = x then ρ u x else 0

/-! ## Complex Specialization via WeightedSpace

For the complex case (𝕜 = ℂ), we can use the `WeightedSpace` infrastructure to prove
properties that are axiomatized in the general case. This section provides the bridge. -/

section ComplexBridge

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Convert a function V → ℂ to WeightedSpace V. -/
@[inline] def toWeightedSpace (f : V → ℂ) : WeightedSpace V := WeightedSpace.mk f

/-- Convert WeightedSpace V back to V → ℂ. -/
@[inline] def fromWeightedSpace (f : WeightedSpace V) : V → ℂ := f

/-- The inner product on V → ℂ equals the weighted inner product on WeightedSpace V. -/
theorem inner_pi_eq_weightedInner (pi_dist : V → ℝ) (u v : V → ℂ) :
    inner_pi pi_dist u v = WeightedSpace.weightedInner pi_dist (toWeightedSpace u) (toWeightedSpace v) := by
  unfold inner_pi WeightedSpace.weightedInner toWeightedSpace WeightedSpace.mk
  rfl

/-- **THEOREM** (replaces axiom for ℂ): The weighted inner product is non-degenerate. -/
theorem inner_pi_nondegenerate_complex (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (x : V → ℂ) :
    (∀ y, inner_pi pi_dist x y = 0) → x = 0 := by
  intro h
  have h' : ∀ y : WeightedSpace V, WeightedSpace.weightedInner pi_dist (toWeightedSpace x) y = 0 := by
    intro y
    have := h (fromWeightedSpace y)
    rw [inner_pi_eq_weightedInner] at this
    convert this
  have := WeightedSpace.weightedInner_nondegenerate pi_dist hπ (toWeightedSpace x) h'
  exact this

/-- **THEOREM** (replaces axiom for ℂ): Two operators equal if they produce equal inner products. -/
theorem linearMap_ext_inner_complex (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (A B : (V → ℂ) →ₗ[ℂ] (V → ℂ)) :
    (∀ u v, inner_pi pi_dist (A u) v = inner_pi pi_dist (B u) v) → A = B := by
  intro h
  apply LinearMap.ext
  intro f
  -- Show A f - B f = 0 by non-degeneracy, then conclude A f = B f
  have h_diff : A f - B f = 0 := by
    apply inner_pi_nondegenerate_complex pi_dist hπ
    intro v
    have h1 := h f v
    calc inner_pi pi_dist (A f - B f) v
        = inner_pi pi_dist (A f) v + inner_pi pi_dist ((-1 : ℂ) • B f) v := by
          rw [sub_eq_add_neg, ← neg_one_smul ℂ (B f), inner_pi_add_left]
        _ = inner_pi pi_dist (A f) v + star (-1 : ℂ) * inner_pi pi_dist (B f) v := by
          rw [inner_pi_smul_left]
        _ = inner_pi pi_dist (A f) v - inner_pi pi_dist (B f) v := by
          simp only [star_neg, star_one, neg_mul, one_mul]; ring
        _ = 0 := by rw [h1, sub_self]
  simp only [sub_eq_zero] at h_diff
  exact h_diff

/-- **THEOREM** (replaces axiom for ℂ): For any vector, ⟨f, f⟩ is real. -/
theorem inner_self_real_complex (pi_dist : V → ℝ) (f : V → ℂ) :
    RCLike.im (inner_pi pi_dist f f) = 0 := by
  rw [inner_pi_eq_weightedInner]
  exact WeightedSpace.weightedInner_self_real pi_dist (toWeightedSpace f)

/-- inner_pi with zero in left argument gives zero. -/
lemma inner_pi_zero_left_complex (pi_dist : V → ℝ) (v : V → ℂ) :
    inner_pi pi_dist 0 v = 0 := by
  unfold inner_pi
  simp only [Pi.zero_apply, star_zero, mul_zero, zero_mul, Finset.sum_const_zero]

/-- inner_pi with zero in right argument gives zero. -/
lemma inner_pi_zero_right_complex (pi_dist : V → ℝ) (u : V → ℂ) :
    inner_pi pi_dist u 0 = 0 := by
  unfold inner_pi
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]

end ComplexBridge

end GeometryGeneral
end Axioms
end SGC
