import SGC.InformationGeometry.ScoreProjection
import SGC.Observation.DeterministicReadout

noncomputable section

namespace SGC.InformationGeometry.StochasticObservation

open Finset

set_option linter.unusedSectionVars false

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

structure Channel (X Y : Type*) [Fintype Y] where
  prob : X → Y → ℝ
  nonneg : ∀ x y, 0 ≤ prob x y
  row_sum : ∀ x, ∑ y, prob x y = 1

namespace Channel

variable (K : Channel X Y)

def ofKernel (M : Matrix X Y ℝ) (hM : SGC.Observation.IsKernel M) : Channel X Y :=
  ⟨M, hM.nonneg, hM.row_sum_one⟩

theorem isKernel : SGC.Observation.IsKernel K.prob := ⟨K.nonneg, K.row_sum⟩

def push (p : X → ℝ) (y : Y) : ℝ := ∑ x, p x * K.prob x y

def numerator (p s : X → ℝ) : Y → ℝ := K.push (fun x => p x * s x)

def mean (p s : X → ℝ) (y : Y) : ℝ := K.numerator p s y / K.push p y

def loss (p s : X → ℝ) : ℝ :=
  ∑ x, p x * s x ^ 2 - ∑ y, K.numerator p s y ^ 2 / K.push p y

theorem hasDerivAt_push (p : ℝ → X → ℝ) (d : X → ℝ) (θ : ℝ)
    (hd : ∀ x, HasDerivAt (fun t => p t x) (d x) θ) (y : Y) :
    HasDerivAt (fun t => K.push (p t) y) (K.push d y) θ := by
  exact HasDerivAt.fun_sum (fun x _ => (hd x).mul_const (K.prob x y))

lemma push_nonneg {p : X → ℝ} (hp : ∀ x, 0 ≤ p x) (y : Y) : 0 ≤ K.push p y :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (hp x) (K.nonneg x y))

theorem push_total (p : X → ℝ) : ∑ y, K.push p y = ∑ x, p x := by
  unfold push
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, K.row_sum, mul_one]

lemma numerator_eq_zero_of_push_zero {p : X → ℝ} (hp : ∀ x, 0 ≤ p x)
    (s : X → ℝ) {y : Y} (hy : K.push p y = 0) : K.numerator p s y = 0 := by
  have ht := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
    mul_nonneg (hp x) (K.nonneg x y))).mp hy
  unfold numerator push
  refine Finset.sum_eq_zero (fun x _ => ?_)
  calc p x * s x * K.prob x y = (p x * K.prob x y) * s x := by ring
    _ = 0 := by rw [ht x (Finset.mem_univ x), zero_mul]

lemma push_mul_mean {p : X → ℝ} (hp : ∀ x, 0 ≤ p x) (s : X → ℝ) (y : Y) :
    K.push p y * K.mean p s y = K.numerator p s y := by
  unfold mean
  by_cases hy : K.push p y = 0
  · rw [hy, K.numerator_eq_zero_of_push_zero hp s hy]
    simp
  · field_simp

lemma fiber_identity {p : X → ℝ} (hp : ∀ x, 0 ≤ p x) (s : X → ℝ) (y : Y) :
    ∑ x, p x * K.prob x y * (s x - K.mean p s y) ^ 2 =
      (∑ x, p x * K.prob x y * s x ^ 2) - K.numerator p s y ^ 2 / K.push p y := by
  have he : ∑ x, p x * K.prob x y * (s x - K.mean p s y) ^ 2 =
      (∑ x, p x * K.prob x y * s x ^ 2)
        - 2 * K.mean p s y * K.numerator p s y + K.mean p s y ^ 2 * K.push p y := by
    unfold numerator push
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  rw [he]
  unfold mean
  by_cases hy : K.push p y = 0
  · rw [hy, K.numerator_eq_zero_of_push_zero hp s hy]
    simp
  · field_simp
    ring

theorem loss_eq_conditional_variance {p : X → ℝ} (hp : ∀ x, 0 ≤ p x) (s : X → ℝ) :
    K.loss p s = ∑ y, ∑ x, p x * K.prob x y * (s x - K.mean p s y) ^ 2 := by
  simp_rw [K.fiber_identity hp s]
  rw [Finset.sum_sub_distrib]
  unfold loss
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  calc p x * s x ^ 2 = p x * s x ^ 2 * ∑ y, K.prob x y := by rw [K.row_sum, mul_one]
    _ = ∑ y, p x * K.prob x y * s x ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun y _ => by ring)

theorem loss_nonneg {p : X → ℝ} (hp : ∀ x, 0 ≤ p x) (s : X → ℝ) : 0 ≤ K.loss p s := by
  rw [K.loss_eq_conditional_variance hp s]
  exact Finset.sum_nonneg (fun y _ => Finset.sum_nonneg (fun x _ =>
    mul_nonneg (mul_nonneg (hp x) (K.nonneg x y)) (sq_nonneg _)))

theorem loss_eq_zero_iff {p : X → ℝ} (hp : ∀ x, 0 ≤ p x) (s : X → ℝ) :
    K.loss p s = 0 ↔ ∀ x y, 0 < p x * K.prob x y → s x = K.mean p s y := by
  rw [K.loss_eq_conditional_variance hp s]
  constructor
  · intro h x y hxy
    have hy := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => Finset.sum_nonneg (fun x _ =>
      mul_nonneg (mul_nonneg (hp x) (K.nonneg x y)) (sq_nonneg _)))).mp h y (Finset.mem_univ y)
    have hx := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
      mul_nonneg (mul_nonneg (hp x) (K.nonneg x y)) (sq_nonneg _))).mp hy x (Finset.mem_univ x)
    have hz := (mul_eq_zero.mp hx).resolve_left hxy.ne'
    nlinarith [sq_nonneg (s x - K.mean p s y)]
  · intro h
    refine Finset.sum_eq_zero (fun y _ => Finset.sum_eq_zero (fun x _ => ?_))
    by_cases hxy : p x * K.prob x y = 0
    · rw [hxy, zero_mul]
    · have hpos := lt_of_le_of_ne (mul_nonneg (hp x) (K.nonneg x y)) (Ne.symm hxy)
      rw [h x y hpos, sub_self, zero_pow (by decide), mul_zero]

theorem loss_eq_fisherLoss {p : X → ℝ} (hp : ∀ x, 0 < p x) (s : X → ℝ) :
    K.loss p s = ScoreProjection.fineFisher p (fun x => p x * s x)
      - ScoreProjection.fineFisher (K.push p) (K.numerator p s) := by
  unfold loss ScoreProjection.fineFisher
  congr 1
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have hx := (hp x).ne'
  field_simp

def comp (H : Channel Y Z) : Channel X Z where
  prob x z := ∑ y, K.prob x y * H.prob y z
  nonneg x z := Finset.sum_nonneg (fun y _ => mul_nonneg (K.nonneg x y) (H.nonneg y z))
  row_sum x := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, H.row_sum, mul_one]
    exact K.row_sum x

theorem push_comp (H : Channel Y Z) (p : X → ℝ) :
    (K.comp H).push p = H.push (K.push p) := by
  funext z
  simp only [push, comp, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x _ => by ring))

theorem loss_chain (H : Channel Y Z) {p : X → ℝ} (hp : ∀ x, 0 ≤ p x) (s : X → ℝ) :
    (K.comp H).loss p s = K.loss p s + H.loss (K.push p) (K.mean p s) := by
  have hm : (fun y => K.push p y * K.mean p s y) = K.numerator p s :=
    funext (K.push_mul_mean hp s)
  have he : ∑ y, K.push p y * K.mean p s y ^ 2 = ∑ y, K.numerator p s y ^ 2 / K.push p y := by
    refine Finset.sum_congr rfl (fun y _ => ?_)
    unfold mean
    by_cases hy : K.push p y = 0
    · simp [hy]
    · field_simp
  unfold loss
  rw [he]
  simp only [numerator, push_comp]
  rw [hm]
  simp only [numerator]
  ring

theorem loss_le_comp_loss (H : Channel Y Z) {p : X → ℝ} (hp : ∀ x, 0 ≤ p x) (s : X → ℝ) :
    K.loss p s ≤ (K.comp H).loss p s := by
  rw [K.loss_chain H hp s]
  exact le_add_of_nonneg_right (H.loss_nonneg (K.push_nonneg hp) (K.mean p s))

def deterministic [DecidableEq Y] (q : X → Y) : Channel X Y where
  prob x y := if q x = y then 1 else 0
  nonneg x y := by split_ifs <;> norm_num
  row_sum x := by simp

theorem push_deterministic [DecidableEq Y] (q : X → Y) (p : X → ℝ) :
    (deterministic q).push p = ScoreProjection.blockMass q p := by
  funext y
  simp [push, deterministic, ScoreProjection.blockMass, Finset.sum_filter]

theorem loss_deterministic [DecidableEq Y] (q : X → Y) {p : X → ℝ}
    (hp : ∀ x, 0 < p x) (s : X → ℝ) :
    (deterministic q).loss p s = ScoreProjection.fineFisher p (fun x => p x * s x)
      - ScoreProjection.coarseFisher q p (fun x => p x * s x) := by
  rw [(deterministic q).loss_eq_fisherLoss hp s]
  simp only [numerator, push_deterministic]
  rfl

theorem loss_zero_implies_constant [Nonempty Y] {p : X → ℝ} (hp : ∀ x, 0 < p x)
    (hK : ∀ x y, 0 < K.prob x y) (s : X → ℝ) (hzero : K.loss p s = 0) :
    ∀ x x', s x = s x' := by
  classical
  obtain ⟨y⟩ := ‹Nonempty Y›
  have h := (K.loss_eq_zero_iff (fun x => (hp x).le) s).mp hzero
  intro x x'
  exact (h x y (mul_pos (hp x) (hK x y))).trans (h x' y (mul_pos (hp x') (hK x' y))).symm

def gated (h : Y → Channel X Z) : Channel X Z where
  prob x z := ∑ y, K.prob x y * (h y).prob x z
  nonneg x z := Finset.sum_nonneg (fun y _ => mul_nonneg (K.nonneg x y) ((h y).nonneg x z))
  row_sum x := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, Channel.row_sum, mul_one]
    exact K.row_sum x

theorem gated_deterministic [DecidableEq Y] (q : X → Y) (h : Y → Channel X Z) (x : X) (z : Z) :
    ((deterministic q).gated h).prob x z = (h (q x)).prob x z := by
  simp [gated, deterministic]

end Channel

end SGC.InformationGeometry.StochasticObservation
