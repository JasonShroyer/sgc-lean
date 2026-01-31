/-
  # SGC/Renormalization/OptimalPartition.lean

  Existence of Optimal Coarse-Graining Partitions.

  This module proves that for any generator L and distribution π, there exists
  a partition P that minimizes the leakage defect ‖(I - Π)LΠ‖.
  This formally justifies the "Observer-Relative Emergence" principle:
  emergence is not just about L, but about finding the P that fits L.

  ## Main Theorems
  - `optimal_partition_exists`: Existence of a defect-minimizing partition.
-/

import SGC.Renormalization.Approximate
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Setoid.Partition

noncomputable section

namespace SGC
namespace Renormalization

open Matrix Real NormedSpace SGC.Approximate SGC.Lumpability

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- There are finitely many partitions of a finite type.
    We assume this instance or derive it from Setoid V.
    Since we are in noncomputable section, we can map Setoid to Partition using Classical.dec. -/
instance : Fintype (Partition V) := by
  -- Construct an equivalence between Partition V and Setoid V
  let toSetoid : Partition V → Setoid V := fun P => P.rel
  let fromSetoid : Setoid V → Partition V := fun s => { rel := s, decRel := Classical.decRel s.r }
  have left_inv : Function.LeftInverse fromSetoid toSetoid := by
    intro P
    cases P
    congr
    -- DecidableRel is a subsingleton
    apply Subsingleton.elim
  have right_inv : Function.RightInverse fromSetoid toSetoid := by
    intro s
    rfl
  -- Since Setoid V is a Fintype (from Mathlib), Partition V is a Fintype
  exact Fintype.ofSurjective fromSetoid right_inv

/-- **Optimal Partition Existence Theorem**.

    For any micro-dynamics L and stationary distribution π, there exists a partition P
    that minimizes the leakage defect ‖(I - Π)LΠ‖_π.

    This P defines the "most emergent" macro-scale description of the system.
    If the minimum defect is small (≤ ε), the system admits a valid effective theory.

    **Proof**: The set of partitions is finite. The function P ↦ ‖D(P)‖ is real-valued.
    A real-valued function on a finite non-empty set attains its minimum.
    (The set of partitions is non-empty because the trivial partition {{x} | x ∈ V} exists). -/
theorem optimal_partition_exists (L : Matrix V V ℝ) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) :
    ∃ P : Partition V, ∀ P' : Partition V,
      opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) ≤
      opNorm_pi pi_dist hπ (DefectOperator L P' pi_dist hπ) := by
  -- 1. Define the cost function
  let cost (P : Partition V) := opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ)
  -- 2. The set of all partitions is finite (from instance above)
  -- 3. Use standard min-existence on fintype
  exact Finite.exists_min (Set.univ : Set (Partition V)) cost Set.univ_nonempty (fun _ _ => rfl)

end Renormalization
end SGC
