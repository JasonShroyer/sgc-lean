import SGC.Thermodynamics.EntropyProduction

/-!
# The equilibrium exemption: reversible chains hide no entropy production

For a reversible generator (detailed balance `π_x L_{xy} = π_y L_{yx}`) every lumped chain is
again reversible: the block aggregate `S(ā,b̄) = Σ_{x∈ā, y∈b̄} π_x L_{xy}` is symmetric, and
`π̄_ā L̄_{āb̄} = S(ā,b̄)`. Hence the coarse Schnakenberg entropy production vanishes and

  `HiddenEntropyProduction L P π = 0`   for **every** partition `P`.

Consequence (recorded in `docs/axiom-discharge-campaign.md`, 2026-10-04): no inequality of the
form `c · ‖(I−Π)LΠ‖² ≤ σ_hid` can hold in general, since reversible chains have positive leakage
for every non-lumpable partition. "To persist is to predict" is therefore **false at
equilibrium** — persistence there is free — and can only be a statement about systems held away
from equilibrium, where it remains an open conjecture (and fails for 87% of random
non-reversible generators in the witness `experiments/gauge_lumpability/gaspard_witness_v1.py`).
-/

noncomputable section

namespace SGC.Thermodynamics

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Block aggregate of the stationary flux: `S(ā,b̄) = Σ_{x∈ā, y∈b̄} π_x L_{xy}`. -/
def blockFlux (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) (a b : P.Quot) : ℝ :=
  ∑ x : V, ∑ y : V, if P.quot_map x = a ∧ P.quot_map y = b then pi_dist x * L x y else 0

/-- Detailed balance makes the block flux symmetric. -/
lemma blockFlux_symm (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (h_db : ∀ x y, pi_dist x * L x y = pi_dist y * L y x) (a b : P.Quot) :
    blockFlux L P pi_dist a b = blockFlux L P pi_dist b a := by
  unfold blockFlux
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  rw [h_db x y]
  by_cases h1 : P.quot_map x = a <;> by_cases h2 : P.quot_map y = b <;> simp [h1, h2]

/-- `π̄_ā · L̄_{āb̄} = S(ā,b̄)` when `π` is positive. -/
lemma pi_bar_mul_coarseGenerator' (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hπ : ∀ x, 0 < pi_dist x) (a b : P.Quot) :
    CoarseStationaryDist P pi_dist a * CoarseGenerator L P pi_dist a b = blockFlux L P pi_dist a b := by
  unfold CoarseGenerator CoarseStationaryDist blockFlux
  have hpos : pi_bar P pi_dist a ≠ 0 := (pi_bar_pos P hπ a).ne'
  simp only [hpos, if_false]
  field_simp

/-- **Lumping preserves detailed balance.** -/
theorem coarse_detailed_balance (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ)
    (hπ : ∀ x, 0 < pi_dist x) (h_db : ∀ x y, pi_dist x * L x y = pi_dist y * L y x) (a b : P.Quot) :
    CoarseStationaryDist P pi_dist a * CoarseGenerator L P pi_dist a b =
      CoarseStationaryDist P pi_dist b * CoarseGenerator L P pi_dist b a := by
  rw [pi_bar_mul_coarseGenerator' L P pi_dist hπ a b, pi_bar_mul_coarseGenerator' L P pi_dist hπ b a,
    blockFlux_symm L P pi_dist h_db a b]

/-- **The equilibrium exemption**: a reversible chain has zero hidden entropy production
under every partition. -/
theorem hidden_entropy_zero_of_detailed_balance (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (hπ : ∀ x, 0 < pi_dist x)
    (h_db : ∀ x y, pi_dist x * L x y = pi_dist y * L y x) :
    HiddenEntropyProduction L P pi_dist = 0 := by
  unfold HiddenEntropyProduction CoarseEntropyProduction
  rw [entropy_production_zero_of_detailed_balance L pi_dist h_db,
    entropy_production_zero_of_detailed_balance _ _ (coarse_detailed_balance L P pi_dist hπ h_db)]
  ring

/-- **No leakage bound from hidden entropy production, in general.** If some constant `c > 0`
satisfied `c · ‖D‖² ≤ σ_hid` for a reversible chain, the partition would have to be exactly
approximately-lumpable with `ε = 0`. Contrapositive form: any reversible chain with a
non-lumpable partition is a counterexample to every such inequality. -/
theorem no_leakage_bound_of_reversible (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (hπ : ∀ x, 0 < pi_dist x)
    (h_db : ∀ x y, pi_dist x * L x y = pi_dist y * L y x)
    (c : ℝ) (hc : 0 < c)
    (hineq : c * (opNorm_pi pi_dist hπ (Approximate.DefectOperator L P pi_dist hπ)) ^ 2 ≤
      HiddenEntropyProduction L P pi_dist) :
    opNorm_pi pi_dist hπ (Approximate.DefectOperator L P pi_dist hπ) = 0 := by
  rw [hidden_entropy_zero_of_detailed_balance L P pi_dist hπ h_db] at hineq
  set d := opNorm_pi pi_dist hπ (Approximate.DefectOperator L P pi_dist hπ) with hd
  have h0 : 0 ≤ d := opNorm_pi_nonneg pi_dist hπ _
  have hsq : d ^ 2 ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    have : 0 < c * d ^ 2 := mul_pos hc hpos
    linarith
  have : d ^ 2 = 0 := le_antisymm hsq (sq_nonneg d)
  exact pow_eq_zero_iff (two_ne_zero) |>.mp this

end SGC.Thermodynamics
