import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Real.Basic

noncomputable section

namespace SGC
namespace Axioms
namespace GeometryGeneral

open Finset

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

end GeometryGeneral
end Axioms
end SGC
