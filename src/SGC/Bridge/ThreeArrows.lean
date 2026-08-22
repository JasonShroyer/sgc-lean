/-
Copyright (c) 2026 Jason Shroyer. All rights reserved.
Released under Apache 2.0 license.
-/
import SGC.Renormalization.CurvatureQuotient
import SGC.Thermodynamics.EntropyProduction

/-!
# The Three Arrows of Coarse-Graining — the capstone

One operation, one quotient operator, three one-way laws, one theorem.

For an exactly lumpable coarse-graining `P` of a generator `L`, the SAME
structural quotient chain `(QuotientGeneratorSimple L P, π̄)` satisfies:

1. **the geometric arrow** — curvature only improves:
   `CD(ρ,∞)` upstairs forces `CD(ρ,∞)` downstairs
   (`RicciCurvatureBound_quotient`);
2. **the thermodynamic arrow** — entropy production only decreases:
   `σ(L̄, π̄) ≤ σ(L, π)` (`hidden_entropy_nonneg` transported through the
   Unification Lemma `coarseGenerator_eq_quotientGeneratorSimple`, which
   fuses the physical `π`-weighted coarse generator with the structural
   quotient at ε = 0);
3. **the informational arrow** — KL divergence only contracts along the
   quotient map (`data_processing_inequality` at `P.quot_map`).

The macro-level is provably smoother, quieter, and less informative than
the micro-level — in three registers, about one object. This is the ε = 0
skeleton of the SGC theory of emergence, packaged.

## Honest scope

* Exact lumpability only. The ε > 0 versions (approximate arrows with
  quantified degradation) are the open quantitative frontier
  (`Approximate.lean`, the validity-horizon machinery).
* The three arrows are one-way statements; no strictness or tightness is
  claimed here (the star example witnesses strictness for the geometric
  arrow; strictness for the other two is not packaged).
* Hypotheses are the union of the three theorems' needs; nothing new is
  assumed.
-/

namespace SGC.Bridge.ThreeArrows

open Finset Matrix
open SGC SGC.Bridge.GeometricClosure SGC.Thermodynamics
open SGC.Renormalization.CurvatureQuotient

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **THE THREE ARROWS.** For an exactly lumpable coarse-graining, the
single structural quotient chain is at least as curved, at most as
dissipative, and at most as informative as the fine chain. One operation —
coarse-graining — is provably monotone in the geometric, thermodynamic,
and informational registers simultaneously. -/
theorem three_arrows (L : Matrix V V ℝ) (P : Partition V)
    (hL : IsStronglyLumpable L P)
    (pi_dist : V → ℝ) (hπ : ∀ x, 0 < pi_dist x)
    (hL_gen : ∀ x y, x ≠ y → 0 ≤ L x y)
    (hL_pos : ∀ x y, x ≠ y → L x y > 0 → L y x > 0)
    (rho : ℝ) (hcurv : RicciCurvatureBound L rho)
    (p q : V → ℝ) (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 < q x) :
    RicciCurvatureBound (QuotientGeneratorSimple L P) rho ∧
    EntropyProductionRate (QuotientGeneratorSimple L P) (pi_bar P pi_dist)
        ≤ EntropyProductionRate L pi_dist ∧
    KLDiv (pushforward P.quot_map p) (pushforward P.quot_map q)
        ≤ KLDiv p q := by
  refine ⟨RicciCurvatureBound_quotient L P hL rho hcurv, ?_,
    data_processing_inequality P.quot_map p q hp hq⟩
  have hhid := hidden_entropy_nonneg L P pi_dist hπ hL_gen hL_pos
  unfold HiddenEntropyProduction at hhid
  rw [coarse_ep_eq_quotient_ep L P hL hπ] at hhid
  linarith

end SGC.Bridge.ThreeArrows
