import FHDT.Envelope
import FHDT.Envelope.Sector
import FHDT.Core.Assumptions
import FHDT.Core.Projector
import FHDT.Diagonal
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.Real.Basic
-- Removed dead import: Mathlib.Analysis.Calculus.FDeriv.Matrix

noncomputable section
open Matrix Real Finset LinearMap

namespace FHDT

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {L H : Matrix V V ℝ} {pi_dist : V → ℝ} {ε : ℝ}

/-- The normalized return probability observable: 1 - K_xx(t)/π_x. -/
def K_norm (L : Matrix V V ℝ) (t : ℝ) (x : V) (pix : ℝ) : ℝ :=
  1 - (HeatKernel L t) x x / pix

/-- The expected log-observable. -/
def E_log_K_norm (L : Matrix V V ℝ) (pi_dist : V → ℝ) (ε : ℝ) (t : ℝ) : ℝ :=
  ∑ x, pi_dist x * Real.log (K_norm L t x (pi_dist x) + ε)

/-- The stability flow β(t) is the time derivative of the expected log-observable. -/
def beta_t (L : Matrix V V ℝ) (pi_dist : V → ℝ) (ε : ℝ) (t : ℝ) : ℝ :=
  deriv (E_log_K_norm L pi_dist ε) t

/--
**The Functorial Heat Dominance Theorem (FHDT)**
If the system has a spectral gap > 0, the stability flow β(t) is bounded by
an exponential envelope determined by the spectral gap.
-/
theorem FunctorialHeatDominanceTheorem
  [Nontrivial V]
  (h_irred : IrreducibilityAssumptions L H pi_dist)
  (h_gap_pos : SpectralGap_pi pi_dist H > 0)
  (hL1 : toLin' L (fun _ => 1) = 0)
  (hK1 : toLin' (HeatKernel L t) (fun _ => 1) = (fun _ => 1))
  (hH_const : H *ᵥ constant_vec_one = 0)
  (h_sa : ∀ u v, inner_pi pi_dist (H *ᵥ u) v = inner_pi pi_dist u (H *ᵥ v))
  (h_psd : ∀ u, 0 ≤ inner_pi pi_dist (H *ᵥ u) u)
  (h_rel : ∀ u v, inner_pi pi_dist (L *ᵥ u) v + inner_pi pi_dist u (L *ᵥ v) = -2 * inner_pi pi_dist (H *ᵥ u) v)
  (h_pos' : ∀ x t, K_norm L t x (pi_dist x) + ε > 0)
  (h_eps_min : ∃ ε_min > 0, ∀ x t, K_norm L t x (pi_dist x) + ε ≥ ε_min)
  (t : ℝ) (ht : 0 ≤ t) :
  ∃ C ≥ 0, |beta_t L pi_dist ε t| ≤ C * Real.exp (-(SpectralGap_pi pi_dist H) * t) := by
  sorry

end FHDT
