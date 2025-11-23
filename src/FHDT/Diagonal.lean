import FHDT.Core.Projector
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section
open Finset LinearMap Matrix Real

namespace FHDT

variable {V : Type*} [Fintype V]

/-- The diagonal operator norm bound: Pillar 3 calculus lemma. -/
lemma sum_abs_diag_le_card_opNorm ... := sorry

end FHDT
