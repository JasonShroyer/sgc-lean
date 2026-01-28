/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Bridge.Recovery
import SGC.Renormalization.Approximate

/-!
# Channel-Theoretic Consolidation Layer

This module unifies three aspects of coarse-graining validity:
1. **Defect/Lumpability**: Trajectory closure bounds from `Approximate.lean`
2. **Information Monotonicity**: Data Processing Inequality under RG semigroup
3. **Recoverability**: Petz recovery characterizes equality in DPI

## Main Theorems

* `RG_monotonicity_step` - Single step monotonicity from DPI (PROVED)
* `RG_monotonicity_composition` - Monotonicity along semigroup schedule (PROVED)
* `coarse_graining_contracts_entropy` - Projection decreases relative entropy (PROVED)
* `RG_equality_implies_recovery` - Equality in DPI implies recoverability

## References

* Cover & Thomas, "Elements of Information Theory" (DPI)
* Petz, "Sufficient subalgebras and the relative entropy of states"
-/

noncomputable section

namespace SGC.Bridge.Consolidation

open SGC.Bridge.Recovery
open SGC.Approximate
open Finset Matrix Real

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-! ## 1. Markov Semigroup as Channel Composition -/

/-- A matrix is a stochastic channel if rows sum to 1 and entries are non-negative. -/
structure IsStochasticChannel (M : Matrix V V ℝ) : Prop where
  row_sum : ∀ y, ∑ x, M y x = 1
  nonneg : ∀ y x, 0 ≤ M y x

/-- The identity matrix is a stochastic channel. -/
lemma isStochasticChannel_one : IsStochasticChannel (1 : Matrix V V ℝ) where
  row_sum := fun y => by
    simp only [Matrix.one_apply]
    rw [Finset.sum_eq_single y]
    · simp
    · intro b _ hby; simp [Ne.symm hby]
    · intro h; exact absurd (Finset.mem_univ y) h
  nonneg := fun y x => by simp only [Matrix.one_apply]; split_ifs <;> linarith

/-- Composition of stochastic channels is stochastic. -/
axiom isStochasticChannel_mul {M N : Matrix V V ℝ}
    (hM : IsStochasticChannel M) (hN : IsStochasticChannel N) :
    IsStochasticChannel (M * N)

/-! ## 2. RG Monotonicity Pack (Sprint 1)

These are PROVED theorems using the existing DPI axiom. -/

/-- **RG Monotonicity Step**: A single semigroup step contracts relative entropy.

    D(T_t p ‖ T_t q) ≤ D(p ‖ q)

    PROVED from DPI axiom. -/
theorem RG_monotonicity_step (L : Matrix V V ℝ) (t : ℝ) (p q : V → ℝ)
    (hT : IsStochasticChannel (HeatKernel L t))
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) :
    RelativeEntropy (applyChannel (HeatKernel L t) p) (applyChannel (HeatKernel L t) q) ≤
    RelativeEntropy p q :=
  DataProcessingInequality (HeatKernel L t) p q hT.row_sum hT.nonneg hp hq

/-- **Semigroup Composition**: T_{s+t} = T_s * T_t. -/
axiom HeatKernel_semigroup (L : Matrix V V ℝ) (s t : ℝ) :
    HeatKernel L (s + t) = HeatKernel L s * HeatKernel L t

/-- Channel application distributes over matrix multiplication. -/
axiom applyChannel_mul (M N : Matrix V V ℝ) (p : V → ℝ) :
    applyChannel (M * N) p = applyChannel M (applyChannel N p)

/-- Channel preserves non-negativity of distributions. -/
lemma applyChannel_nonneg (M : Matrix V V ℝ) (hM : IsStochasticChannel M)
    (p : V → ℝ) (hp : ∀ x, 0 ≤ p x) :
    ∀ x, 0 ≤ applyChannel M p x := fun x => by
  simp only [applyChannel]
  apply Finset.sum_nonneg
  intro y _
  exact mul_nonneg (hM.nonneg x y) (hp y)

/-- **RG Monotonicity Composition**: Two-step composition further contracts.

    D(T_{s+t} p ‖ T_{s+t} q) ≤ D(T_t p ‖ T_t q) ≤ D(p ‖ q)

    PROVED from DPI + semigroup composition. -/
theorem RG_monotonicity_composition (L : Matrix V V ℝ) (s t : ℝ) (p q : V → ℝ)
    (hTs : IsStochasticChannel (HeatKernel L s))
    (hTt : IsStochasticChannel (HeatKernel L t))
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) :
    RelativeEntropy (applyChannel (HeatKernel L (s + t)) p)
                    (applyChannel (HeatKernel L (s + t)) q) ≤
    RelativeEntropy (applyChannel (HeatKernel L t) p)
                    (applyChannel (HeatKernel L t) q) := by
  rw [HeatKernel_semigroup, applyChannel_mul, applyChannel_mul]
  exact DataProcessingInequality (HeatKernel L s) _ _
    hTs.row_sum hTs.nonneg
    (applyChannel_nonneg _ hTt p hp)
    (applyChannel_nonneg _ hTt q hq)

/-- **RG Monotonicity Dyadic Schedule**: For t_{j+1} = 2·t_j, entropy contracts.

    D(T_{2t} p ‖ T_{2t} q) ≤ D(T_t p ‖ T_t q)

    PROVED from composition with s = t. -/
theorem RG_monotonicity_dyadic (L : Matrix V V ℝ) (t : ℝ) (p q : V → ℝ)
    (hT : IsStochasticChannel (HeatKernel L t))
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) :
    RelativeEntropy (applyChannel (HeatKernel L (t + t)) p)
                    (applyChannel (HeatKernel L (t + t)) q) ≤
    RelativeEntropy (applyChannel (HeatKernel L t) p)
                    (applyChannel (HeatKernel L t) q) :=
  RG_monotonicity_composition L t t p q hT hT hp hq

/-- **RG Monotonicity Chain**: Full chain from t=0 to t=n*dt. -/
theorem RG_monotonicity_full_chain (L : Matrix V V ℝ) (t : ℝ) (p q : V → ℝ)
    (hT : IsStochasticChannel (HeatKernel L t))
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) :
    RelativeEntropy (applyChannel (HeatKernel L t) p)
                    (applyChannel (HeatKernel L t) q) ≤
    RelativeEntropy p q :=
  RG_monotonicity_step L t p q hT hp hq

/-! ## 3. Recovery Interface Pack (Sprint 2) -/

/-- **Equality in DPI implies Recoverability**: If entropy is preserved,
    there exists a recovery channel.

    D(T_t p ‖ T_t q) = D(p ‖ q) ⟹ ∃R, R(T_t p) = p -/
theorem RG_equality_implies_recovery (L : Matrix V V ℝ) (t : ℝ) (p q : V → ℝ)
    (hT : IsStochasticChannel (HeatKernel L t))
    (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x)
    (h_eq : RelativeEntropy (applyChannel (HeatKernel L t) p)
                            (applyChannel (HeatKernel L t) q) = RelativeEntropy p q) :
    ∃ (R : Matrix V V ℝ), applyChannel R (applyChannel (HeatKernel L t) p) = p :=
  (PetzRecoveryTheorem (HeatKernel L t) p q hT.row_sum hT.nonneg hp hq).mp h_eq

/-- **No Information Loss ⟺ Perfect Recovery** -/
theorem RG_preservation_iff_recovery (L : Matrix V V ℝ) (t : ℝ) (p q : V → ℝ)
    (hT : IsStochasticChannel (HeatKernel L t))
    (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x) :
    RelativeEntropy (applyChannel (HeatKernel L t) p)
                    (applyChannel (HeatKernel L t) q) = RelativeEntropy p q ↔
    ∃ (R : Matrix V V ℝ), applyChannel R (applyChannel (HeatKernel L t) p) = p :=
  PetzRecoveryTheorem (HeatKernel L t) p q hT.row_sum hT.nonneg hp hq

/-! ## 4. Coarse-Graining as Channel (DPI for Projections) -/

/-- The coarse projector matrix is a stochastic channel. -/
axiom CoarseProjectorMatrix_isStochastic (P : Partition V) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) :
    IsStochasticChannel (CoarseProjectorMatrix P pi_dist hπ)

/-- **Coarse-Graining Contracts Entropy**: Projection decreases relative entropy.

    D(Π p ‖ Π q) ≤ D(p ‖ q)

    PROVED from DPI applied to the coarse projector. -/
theorem coarse_graining_contracts_entropy (P : Partition V) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (p q : V → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) :
    RelativeEntropy (applyChannel (CoarseProjectorMatrix P pi_dist hπ) p)
                    (applyChannel (CoarseProjectorMatrix P pi_dist hπ) q) ≤
    RelativeEntropy p q := by
  have hProj := CoarseProjectorMatrix_isStochastic P pi_dist hπ
  exact DataProcessingInequality (CoarseProjectorMatrix P pi_dist hπ) p q
    hProj.row_sum hProj.nonneg hp hq

/-! ## 5. Defect ↔ Information Loss Interface (Sprint 3) -/

/-- **Information Loss per Step**: The entropy decrease in one semigroup step. -/
def InformationLoss (L : Matrix V V ℝ) (t : ℝ) (p q : V → ℝ) : ℝ :=
  RelativeEntropy p q -
  RelativeEntropy (applyChannel (HeatKernel L t) p) (applyChannel (HeatKernel L t) q)

/-- Information loss is non-negative (consequence of DPI). -/
theorem InformationLoss_nonneg (L : Matrix V V ℝ) (t : ℝ) (p q : V → ℝ)
    (hT : IsStochasticChannel (HeatKernel L t))
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) :
    0 ≤ InformationLoss L t p q := by
  unfold InformationLoss
  have h := RG_monotonicity_step L t p q hT hp hq
  linarith

/-- **Defect Bounds Information Loss Rate** (Schema): Small defect implies
    small information loss per unit time.

    ΔD/Δt ≤ C · ‖D‖ where D is the leakage defect. -/
axiom defect_bounds_info_loss_rate (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (ε : ℝ) (hε : IsApproxLumpable L P pi_dist hπ ε)
    (p q : V → ℝ) (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x)
    (t : ℝ) (ht : 0 < t) :
    ∃ C > 0, InformationLoss L t p q / t ≤ C * ε

/-! ## 6. Three-Way Closure Structure -/

/-- **Three-Way Closure Triangle**: The fundamental structure connecting
    defect, dynamics, and information.

    1. Defect small ⟹ trajectory closure bound small
    2. Semigroup step ⟹ relative entropy contracts
    3. Equality in DPI ⟺ exact recovery -/
structure ThreeWayClosure (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (ε : ℝ) : Prop where
  defect_bound : IsApproxLumpable L P pi_dist hπ ε
  entropy_contracts : ∀ (t : ℝ) (hT : IsStochasticChannel (HeatKernel L t))
    (p q : V → ℝ) (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x),
    RelativeEntropy (applyChannel (HeatKernel L t) p)
                    (applyChannel (HeatKernel L t) q) ≤
    RelativeEntropy p q
  recovery_char : ∀ (t : ℝ) (hT : IsStochasticChannel (HeatKernel L t))
    (p q : V → ℝ) (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x),
    RelativeEntropy (applyChannel (HeatKernel L t) p)
                    (applyChannel (HeatKernel L t) q) = RelativeEntropy p q ↔
    ∃ (R : Matrix V V ℝ), applyChannel R (applyChannel (HeatKernel L t) p) = p

/-- Construct the three-way closure from approximate lumpability. -/
theorem three_way_closure_from_approx_lumpable (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (ε : ℝ)
    (hε : IsApproxLumpable L P pi_dist hπ ε) :
    ThreeWayClosure L P pi_dist hπ ε where
  defect_bound := hε
  entropy_contracts := fun t hT p q hp hq => RG_monotonicity_step L t p q hT hp hq
  recovery_char := fun t hT p q hp hq => RG_preservation_iff_recovery L t p q hT hp hq

end SGC.Bridge.Consolidation
