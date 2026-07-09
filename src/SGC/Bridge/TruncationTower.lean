import SGC.Bridge.TruncationProjector
import SGC.Topology.PadicPathSpace

/-!
  # SGC/Bridge/TruncationTower.lean

  Ties the knot between the Renormalization layer (`TruncationProjector`) and the
  Cantor / p-adic tower (`PadicPathSpace`):

  * the coarse-grained state space of the depth-`n` truncation partition is the
    depth-`n` symbol space `Fin n → Fin p` (equivalently `ZMod (p^n)`), and
  * the coarse-graining quotient map **is** the p-adic residue map
    `ZMod.castHom : ZMod (p^(n+1)) → ZMod (p^n)`, via the genuine Horner
    `digitEncoding`.
-/

noncomputable section

namespace SGC.Bridge.TruncationTower

open SGC SGC.Bridge.TruncationProjector SGC.Topology.PadicPathSpace

/-- The coarse-grained state space of the depth-`n` truncation partition is canonically
    the depth-`n` symbol space `Fin n → Fin p`, by dropping the top (last) digit. -/
def truncationQuotientEquiv (p n : ℕ) [NeZero p] :
    (truncationPartition p n).Quot ≃ (Fin n → Fin p) where
  toFun := Quotient.lift (fun f i => f i.castSucc) (by
    intro a b h
    funext i
    exact h i)
  invFun := fun g => (truncationPartition p n).quot_map (Fin.snoc g 0)
  left_inv := fun q => Quotient.inductionOn q (fun f => by
    simp only [Partition.quot_map, Quotient.lift_mk]
    apply Quotient.sound
    intro i
    simp only [Fin.snoc_castSucc])
  right_inv := fun g => by
    funext i
    simp only [Partition.quot_map, Quotient.lift_mk, Fin.snoc_castSucc]

/-- The depth-`n` coarse-grained state space, identified with the arithmetic ring
    `ZMod (p^n)` via the genuine Horner `digitEncoding`. -/
def truncationQuotientZModEquiv (p n : ℕ) [NeZero p] :
    (truncationPartition p n).Quot ≃ ZMod (p ^ n) :=
  (truncationQuotientEquiv p n).trans (digitEncoding p n)

/-- **The knot.** Under `digitEncoding`, the coarse-graining quotient map of the
    truncation partition is exactly the p-adic residue map
    `ZMod.castHom : ZMod (p^(n+1)) → ZMod (p^n)`. -/
theorem digitEncoding_truncationQuotient (p n : ℕ) [NeZero p] (f : Fin (n + 1) → Fin p) :
    digitEncoding p n (truncationQuotientEquiv p n ((truncationPartition p n).quot_map f))
      = ZMod.castHom (pow_dvd_pow p n.le_succ) (ZMod (p ^ n)) (digitEncoding p (n + 1) f) := by
  have h : truncationQuotientEquiv p n ((truncationPartition p n).quot_map f)
      = fun i => f i.castSucc := rfl
  rw [h, castHom_digitEncoding]

/-- The knot, packaged on `ZMod (p^n)`: the renormalization coarse-graining map equals
    the p-adic residue `castHom` applied to the depth-`(n+1)` value. -/
theorem truncationQuotientZModEquiv_quot_map (p n : ℕ) [NeZero p] (f : Fin (n + 1) → Fin p) :
    truncationQuotientZModEquiv p n ((truncationPartition p n).quot_map f)
      = ZMod.castHom (pow_dvd_pow p n.le_succ) (ZMod (p ^ n)) (digitEncoding p (n + 1) f) := by
  simp only [truncationQuotientZModEquiv, Equiv.trans_apply]
  exact digitEncoding_truncationQuotient p n f

end SGC.Bridge.TruncationTower
