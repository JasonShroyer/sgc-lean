import SGC.Renormalization.Approximate

noncomputable section

namespace SGC.Bridge.TruncationProjector

open SGC SGC.Approximate Finset

def truncationSetoid (p n : ℕ) : Setoid (Fin (n + 1) → Fin p) where
  r f g := ∀ (i : Fin n), f i.castSucc = g i.castSucc
  iseqv :=
    { refl := fun _ _ => rfl
      symm := fun h i => (h i).symm
      trans := fun h1 h2 i => (h1 i).trans (h2 i) }

def truncationPartition (p n : ℕ) : Partition (Fin (n + 1) → Fin p) where
  rel := truncationSetoid p n
  decRel := fun f g => by
    change Decidable (∀ (i : Fin n), f i.castSucc = g i.castSucc)
    infer_instance

def uniform_dist (p n : ℕ) : (Fin n → Fin p) → ℝ :=
  fun _ => (p : ℝ) ^ (-(n : ℤ))

lemma uniform_dist_pos (p n : ℕ) [Fact p.Prime] :
    ∀ v : Fin n → Fin p, 0 < uniform_dist p n v := by
  intro v
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  unfold uniform_dist
  positivity

theorem coarseProjector_eq_truncation_average
    (p n : ℕ) [Fact p.Prime] (f : (Fin (n + 1) → Fin p) → ℝ) (x : Fin (n + 1) → Fin p) :
    CoarseProjector (truncationPartition p n) (uniform_dist p (n + 1))
        (uniform_dist_pos p (n + 1)) f x =
      (1 / (p : ℝ)) * ∑ a : Fin p, f (Function.update x (Fin.last n) a) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt hp
  set P := truncationPartition p n with hP
  set c : ℝ := (p : ℝ) ^ (-((n : ℤ) + 1)) with hc
  have hc0 : c ≠ 0 := by rw [hc]; positivity
  have hmem : ∀ y : Fin (n + 1) → Fin p,
      (P.quot_map y = P.quot_map x) ↔ (∀ i : Fin n, y i.castSucc = x i.castSucc) :=
    fun y => ⟨fun h => Quotient.eq'.mp h, fun h => Quotient.sound h⟩
  have hrep : ∀ y : Fin (n + 1) → Fin p, (∀ i : Fin n, y i.castSucc = x i.castSucc) →
      Function.update x (Fin.last n) (y (Fin.last n)) = y := by
    intro y h; funext j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · rw [Function.update_of_ne (Fin.castSucc_lt_last i).ne]; exact (h i).symm
    · rw [Function.update_self]
  have huni : ∀ y : Fin (n + 1) → Fin p, uniform_dist p (n + 1) y = c := by
    intro y; simp only [uniform_dist, hc, Nat.cast_add, Nat.cast_one]
  have hcard : (Finset.univ.filter
      (fun y : Fin (n + 1) → Fin p => P.quot_map y = P.quot_map x)).card = p := by
    have h := Finset.card_bij'
      (fun (y : Fin (n + 1) → Fin p) _ => y (Fin.last n))
      (fun (a : Fin p) _ => Function.update x (Fin.last n) a)
      (fun y _ => Finset.mem_univ _)
      (fun a _ => by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, (hmem _).mpr
          (fun i => by simp only [Function.update_of_ne (Fin.castSucc_lt_last i).ne])⟩)
      (fun y hy => hrep y ((hmem y).mp (Finset.mem_filter.mp hy).2))
      (fun a _ => by simp)
    simpa using h
  rw [CoarseProjector_apply]
  have hbij : (∑ y : Fin (n + 1) → Fin p,
        if P.quot_map y = P.quot_map x then uniform_dist p (n + 1) y * f y else 0) =
      c * ∑ a : Fin p, f (Function.update x (Fin.last n) a) := by
    rw [Finset.mul_sum, ← Finset.sum_filter]
    apply Finset.sum_bij'
      (fun (y : Fin (n + 1) → Fin p) _ => y (Fin.last n))
      (fun (a : Fin p) _ => Function.update x (Fin.last n) a)
      (fun y _ => Finset.mem_univ _)
      (fun a _ => by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, (hmem _).mpr
          (fun i => by simp only [Function.update_of_ne (Fin.castSucc_lt_last i).ne])⟩)
      (fun y hy => hrep y ((hmem y).mp (Finset.mem_filter.mp hy).2))
      (fun a _ => by simp)
    intro y hy
    rw [huni, hrep y ((hmem y).mp (Finset.mem_filter.mp hy).2)]
  have hbar : pi_bar P (uniform_dist p (n + 1)) (P.quot_map x) = c * p := by
    rw [pi_bar_eq_sum_class, ← Finset.sum_filter,
        Finset.sum_congr rfl (fun y _ => huni y), Finset.sum_const, hcard, nsmul_eq_mul]
    ring
  rw [hbij, hbar]
  field_simp

end SGC.Bridge.TruncationProjector
