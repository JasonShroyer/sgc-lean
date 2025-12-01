import FHDT.Core.Assumptions
import FHDT.Core.Projector
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

noncomputable section
open Matrix Real NormedSpace

namespace FHDT

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {L H : Matrix V V ℝ} {pi_dist : V → ℝ}

/-- Heat semigroup K(t) = e^{tL}. -/
def HeatKernel (L : Matrix V V ℝ) (t : ℝ) : Matrix V V ℝ :=
  exp ℝ (t • L)

/--
**Pillar 2 Interface: `EnvelopeSpec`**
A typeclass defining the contract for a transient envelope `B(t)`.
-/
class EnvelopeSpec (L H : Matrix V V ℝ) (pi_dist : V → ℝ) where
  B : ℝ → ℝ
  B_zero : B 0 = 1
  r : ℝ
  r_ge_gap : r ≥ SpectralGap_pi pi_dist H
  /--
  The core bounding inequality: ‖e^{tL} P_⊥‖_π ≤ B(t) * e^{-rt}.
  P is the projector onto (span{1})⊥ in the L²(pi) space.
  -/
  bound :
    ∀ t ≥ 0, ∀ (h_pos : ∀ v, 0 < pi_dist v) (P : (V → ℝ) →ₗ[ℝ] (V → ℝ)),
    opNorm_pi pi_dist h_pos (toLin' (HeatKernel L t) ∘ₗ P) ≤ B t * Real.exp (-r * t)

end FHDT
