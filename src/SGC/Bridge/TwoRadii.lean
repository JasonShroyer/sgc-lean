/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Bridge.DecisionHorizon

/-!
# Two radii: coarse-graining plus estimation, in total variation

`DecisionHorizon` bounds the distance between the true law `p_t` and the prediction `p̄_t` of
the **true** coarse model by the orbit radius. A learning agent predicts with an **estimated**
coarse model `K̂` instead. The extra error is an estimation term, and its transfer from kernel
error to prediction error is the L¹ (total-variation) face of the contractive perturbation
bound: stochastic kernels contract the L¹ norm of signed measures, so for laws evolved as row
vectors

  `‖w·(X̂ⁿ − Xⁿ)‖₁ ≤ Σ_{k<n} ‖(w·X̂ᵏ)·(X̂ − X)‖₁ ≤ n · ‖w‖₁ · max_a ‖X̂_a − X_a‖₁`.

No semigroup, spectral gap, or reversibility is needed: only row-stochasticity of `X̂`.
The two-radii certificate then reads

  `‖p_t − p̂_t‖₁ ≤ orbitRadius + estimationRadius`,

and `EstimatedDecision` turns any such radius into refine/stop certificates. The
concentration input — how large `max_a ‖K̂_a − K_a‖₁` is with probability `1 − δ` — is a
hypothesis here, as the L¹ radius was in `EstimatedDecision`; it is the one place where
sampling statistics enter.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SGC.Bridge.TwoRadii

open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- L¹ norm of a (signed) measure on `V`. -/
def l1 (w : V → ℝ) : ℝ := ∑ x, |w x|

/-- Row-wise L¹ distance between two kernels, maximised over rows: `max_a Σ_b |X a b − Y a b|`. -/
def rowL1Dist [Nonempty V] (X Y : Matrix V V ℝ) : ℝ :=
  univ.sup' univ_nonempty (fun a => ∑ b, |X a b - Y a b|)

lemma l1_nonneg (w : V → ℝ) : 0 ≤ l1 w := Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma l1_add_le (v w : V → ℝ) : l1 (v + w) ≤ l1 v + l1 w := by
  unfold l1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun x _ => abs_add_le _ _

/-- **Stochastic kernels contract total variation**: if `X` has nonnegative entries and unit row
sums, `‖w·X‖₁ ≤ ‖w‖₁`. -/
lemma l1_vecMul_le_of_stochastic (X : Matrix V V ℝ) (hnn : ∀ a b, 0 ≤ X a b)
    (hrow : ∀ a, ∑ b, X a b = 1) (w : V → ℝ) : l1 (w ᵥ* X) ≤ l1 w := by
  unfold l1
  calc ∑ b, |(w ᵥ* X) b|
      = ∑ b, |∑ a, w a * X a b| := by simp [Matrix.vecMul, dotProduct]
    _ ≤ ∑ b, ∑ a, |w a| * X a b := by
        apply Finset.sum_le_sum; intro b _
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun a _ => by rw [abs_mul, abs_of_nonneg (hnn a b)]
    _ = ∑ a, |w a| * ∑ b, X a b := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]
    _ = ∑ a, |w a| := by simp [hrow]

/-- A single kernel step moves a measure by at most its L¹ mass times the row-L¹ kernel gap. -/
lemma l1_vecMul_sub_le [Nonempty V] (X Y : Matrix V V ℝ) (w : V → ℝ) :
    l1 (w ᵥ* (X - Y)) ≤ l1 w * rowL1Dist X Y := by
  unfold l1 rowL1Dist
  calc ∑ b, |(w ᵥ* (X - Y)) b|
      = ∑ b, |∑ a, w a * (X a b - Y a b)| := by simp [Matrix.vecMul, dotProduct]
    _ ≤ ∑ b, ∑ a, |w a| * |X a b - Y a b| := by
        apply Finset.sum_le_sum; intro b _
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun a _ => abs_mul _ _
    _ = ∑ a, |w a| * ∑ b, |X a b - Y a b| := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]
    _ ≤ ∑ a, |w a| * univ.sup' univ_nonempty (fun a => ∑ b, |X a b - Y a b|) := by
        apply Finset.sum_le_sum; intro a _
        exact mul_le_mul_of_nonneg_left (Finset.le_sup' (fun a => ∑ b, |X a b - Y a b|) (mem_univ a))
          (abs_nonneg _)
    _ = (∑ a, |w a|) * _ := by rw [Finset.sum_mul]

/-- **Orbit telescoping in total variation.** For a row-stochastic `X̂` and any `Y`,
`‖w·(X̂ⁿ − Yⁿ)‖₁ ≤ Σ_{k<n} ‖(w·Yᵏ)·(X̂ − Y)‖₁`. -/
theorem l1_vecMul_pow_sub_pow_le_sum (Xh Y : Matrix V V ℝ)
    (hnn : ∀ a b, 0 ≤ Xh a b) (hrow : ∀ a, ∑ b, Xh a b = 1) (w : V → ℝ) (n : ℕ) :
    l1 (w ᵥ* (Xh ^ n - Y ^ n)) ≤ ∑ k ∈ Finset.range n, l1 ((w ᵥ* Y ^ k) ᵥ* (Xh - Y)) := by
  induction n with
  | zero => simp [l1]
  | succ m ih =>
    have key : w ᵥ* (Xh ^ (m + 1) - Y ^ (m + 1)) =
        (w ᵥ* (Xh ^ m - Y ^ m)) ᵥ* Xh + (w ᵥ* Y ^ m) ᵥ* (Xh - Y) := by
      rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.vecMul_add]
      congr 1
      rw [pow_succ, pow_succ]
      noncomm_ring
    rw [key, Finset.sum_range_succ]
    refine le_trans (l1_add_le _ _) (add_le_add ?_ le_rfl)
    exact le_trans (l1_vecMul_le_of_stochastic Xh hnn hrow _) ih

/-- **Estimation radius**: a row-stochastic estimate `X̂` and the true kernel `X` with
row-L¹ gap `η` give `‖w·(X̂ⁿ − Xⁿ)‖₁ ≤ n · η · ‖w‖₁`. Together with the orbit radius this is
the two-radii bound: the first radius pays for coarse-graining, this one for estimation. -/
theorem estimation_radius [Nonempty V] (Xh X : Matrix V V ℝ)
    (hnn : ∀ a b, 0 ≤ Xh a b) (hrow : ∀ a, ∑ b, Xh a b = 1)
    (hX : ∀ a b, 0 ≤ X a b) (hXrow : ∀ a, ∑ b, X a b = 1)
    (w : V → ℝ) (n : ℕ) {η : ℝ} (hη : rowL1Dist Xh X ≤ η) :
    l1 (w ᵥ* (Xh ^ n - X ^ n)) ≤ (n : ℝ) * η * l1 w := by
  refine le_trans (l1_vecMul_pow_sub_pow_le_sum Xh X hnn hrow w n) ?_
  have hterm : ∀ k ∈ Finset.range n, l1 ((w ᵥ* X ^ k) ᵥ* (Xh - X)) ≤ η * l1 w := by
    intro k _
    have hpow : ∀ j : ℕ, l1 (w ᵥ* X ^ j) ≤ l1 w := by
      intro j
      induction j with
      | zero => simp
      | succ j ihj =>
        rw [pow_succ, ← Matrix.vecMul_vecMul]
        exact le_trans (l1_vecMul_le_of_stochastic X hX hXrow _) ihj
    have hdist0 : 0 ≤ rowL1Dist Xh X := by
      unfold rowL1Dist
      exact le_trans (Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.le_sup' (fun a => ∑ b, |Xh a b - X a b|) (mem_univ (Classical.arbitrary V)))
    calc l1 ((w ᵥ* X ^ k) ᵥ* (Xh - X))
        ≤ l1 (w ᵥ* X ^ k) * rowL1Dist Xh X := l1_vecMul_sub_le Xh X _
      _ ≤ l1 w * η := mul_le_mul (hpow k) hη hdist0 (l1_nonneg w)
      _ = η * l1 w := mul_comm _ _
  calc ∑ k ∈ Finset.range n, l1 ((w ᵥ* X ^ k) ᵥ* (Xh - X))
      ≤ ∑ _k ∈ Finset.range n, η * l1 w := Finset.sum_le_sum hterm
    _ = (n : ℝ) * η * l1 w := by simp [Finset.sum_const, Finset.card_range]; ring

/-! ## §2. Dobrushin contraction and the saturating estimation radius

The linear radius `n·η` grows without bound while the actual estimation error saturates, because
the coarse chain forgets. Dobrushin's ergodic coefficient quantifies the forgetting in total
variation: for a row-stochastic `Y` with `τ(Y) := max_{a,b} ½ Σ_c |Y a c − Y b c|`, every
**mean-zero** signed measure contracts, `‖v·Y‖₁ ≤ τ(Y)·‖v‖₁`. Since each telescoping term
`(w·Xᵏ)·(X − Y)` is mean-zero, the later factors `Y^{n−1−k}` contract it, and the radius becomes
`η·‖w‖₁·Σ_k τᵏ ≤ η·‖w‖₁/(1 − τ)`. The coefficient is that of the **estimated** kernel `Y`, so an
agent can compute it. This is the L¹ counterpart of the library's `ε/γ` NCD bound: no spectral
hypothesis, no reversibility, finite arithmetic only. -/

/-- Dobrushin's total-variation diameter of the rows of `Y`: `max_{a,b} ½ Σ_c |Y a c − Y b c|`. -/
def tvDiam [Nonempty V] (Y : Matrix V V ℝ) : ℝ :=
  univ.sup' univ_nonempty (fun ab : V × V => (1/2 : ℝ) * ∑ c, |Y ab.1 c - Y ab.2 c|)

lemma tvDiam_nonneg [Nonempty V] (Y : Matrix V V ℝ) : 0 ≤ tvDiam Y := by
  unfold tvDiam
  refine le_trans ?_ (Finset.le_sup' (fun ab : V × V => (1/2 : ℝ) * ∑ c, |Y ab.1 c - Y ab.2 c|)
    (mem_univ (Classical.arbitrary V, Classical.arbitrary V)))
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

lemma half_sum_abs_le_tvDiam [Nonempty V] (Y : Matrix V V ℝ) (a b : V) :
    (1/2 : ℝ) * ∑ c, |Y a c - Y b c| ≤ tvDiam Y :=
  Finset.le_sup' (fun ab : V × V => (1/2 : ℝ) * ∑ c, |Y ab.1 c - Y ab.2 c|) (mem_univ (a, b))

/-- Positive and negative parts of a signed measure. -/
def posPart (v : V → ℝ) : V → ℝ := fun a => max (v a) 0
def negPart (v : V → ℝ) : V → ℝ := fun a => max (-v a) 0

lemma posPart_sub_negPart (v : V → ℝ) : v = posPart v - negPart v := by
  funext a; simp only [posPart, negPart, Pi.sub_apply]
  rcases le_total 0 (v a) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

lemma abs_eq_posPart_add_negPart (v : V → ℝ) (a : V) : |v a| = posPart v a + negPart v a := by
  simp only [posPart, negPart]
  rcases le_total 0 (v a) with h | h
  · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith)]; ring

lemma posPart_nonneg (v : V → ℝ) (a : V) : 0 ≤ posPart v a := le_max_right _ _
lemma negPart_nonneg (v : V → ℝ) (a : V) : 0 ≤ negPart v a := le_max_right _ _

/-- For a mean-zero `v`, the positive and negative parts have equal mass `‖v‖₁/2`. -/
lemma mass_posPart_of_sum_zero (v : V → ℝ) (hv : ∑ a, v a = 0) :
    ∑ a, posPart v a = l1 v / 2 ∧ ∑ a, negPart v a = l1 v / 2 := by
  have h1 : ∑ a, posPart v a - ∑ a, negPart v a = 0 := by
    rw [← Finset.sum_sub_distrib, ← hv]
    exact Finset.sum_congr rfl fun a _ => by
      have := congr_fun (posPart_sub_negPart v) a; simp only [Pi.sub_apply] at this; linarith
  have h2 : ∑ a, posPart v a + ∑ a, negPart v a = l1 v := by
    unfold l1; rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => (abs_eq_posPart_add_negPart v a).symm
  constructor <;> linarith

/-- **Dobrushin contraction**: a mean-zero signed measure contracts under a stochastic kernel by
the total-variation diameter of its rows. -/
theorem l1_vecMul_le_tvDiam_of_sum_zero [Nonempty V] (Y : Matrix V V ℝ)
    (hrow : ∀ a, ∑ c, Y a c = 1) (v : V → ℝ) (hv : ∑ a, v a = 0) :
    l1 (v ᵥ* Y) ≤ tvDiam Y * l1 v := by
  obtain ⟨hp, hn⟩ := mass_posPart_of_sum_zero v hv
  set m := l1 v / 2 with hm
  have hm0 : 0 ≤ m := by rw [hm]; exact div_nonneg (l1_nonneg v) (by norm_num)
  rcases eq_or_lt_of_le hm0 with hm_zero | hm_pos
  · -- v = 0
    have hv0 : v = 0 := by
      funext a
      have : |v a| = 0 := by
        have hsum : ∑ a, |v a| = 0 := by unfold l1 at hm; linarith
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => abs_nonneg _)).mp hsum a (mem_univ a)
      exact abs_eq_zero.mp this
    subst hv0
    simp [l1, Matrix.zero_vecMul]
  · -- v·Y = (1/m) Σ_{a,b} v⁺_a v⁻_b (Y_a − Y_b)
    have hvY : ∀ c, (v ᵥ* Y) c = (1 / m) * ∑ a, ∑ b, posPart v a * negPart v b * (Y a c - Y b c) := by
      intro c
      have e1 : ∑ a, ∑ b, posPart v a * negPart v b * Y a c =
          (∑ b, negPart v b) * ∑ a, posPart v a * Y a c := by
        rw [Finset.sum_mul, Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
      have e2 : ∑ a, ∑ b, posPart v a * negPart v b * Y b c =
          (∑ a, posPart v a) * ∑ b, negPart v b * Y b c := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
      have e : ∑ a, ∑ b, posPart v a * negPart v b * (Y a c - Y b c) =
          (∑ b, negPart v b) * ∑ a, posPart v a * Y a c - (∑ a, posPart v a) * ∑ b, negPart v b * Y b c := by
        simp_rw [mul_sub, Finset.sum_sub_distrib]
        rw [e1, e2]
      rw [e, hp, hn]
      have : (v ᵥ* Y) c = ∑ a, posPart v a * Y a c - ∑ b, negPart v b * Y b c := by
        simp only [Matrix.vecMul, dotProduct, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        have := congr_fun (posPart_sub_negPart v) a; simp only [Pi.sub_apply] at this
        rw [this]; ring
      rw [this]; field_simp
    unfold l1
    calc ∑ c, |(v ᵥ* Y) c|
        = ∑ c, |(1 / m) * ∑ a, ∑ b, posPart v a * negPart v b * (Y a c - Y b c)| := by
          simp_rw [hvY]
      _ ≤ ∑ c, (1 / m) * ∑ a, ∑ b, posPart v a * negPart v b * |Y a c - Y b c| := by
          apply Finset.sum_le_sum; intro c _
          rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / m)]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => le_of_eq ?_)
          rw [abs_mul, abs_of_nonneg (mul_nonneg (posPart_nonneg v a) (negPart_nonneg v b))]
      _ = (1 / m) * ∑ a, ∑ b, posPart v a * negPart v b * ∑ c, |Y a c - Y b c| := by
          rw [← Finset.mul_sum]; congr 1
          rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.mul_sum]
      _ ≤ (1 / m) * ∑ a, ∑ b, posPart v a * negPart v b * (2 * tvDiam Y) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (posPart_nonneg v a) (negPart_nonneg v b))
          have := half_sum_abs_le_tvDiam Y a b; linarith
      _ = (1 / m) * (2 * tvDiam Y) * ((∑ a, posPart v a) * ∑ b, negPart v b) := by
          have : ∑ a, ∑ b, posPart v a * negPart v b * (2 * tvDiam Y) =
              (2 * tvDiam Y) * ((∑ a, posPart v a) * ∑ b, negPart v b) := by
            have h1 : ∀ a, ∑ b, posPart v a * negPart v b * (2 * tvDiam Y) =
                posPart v a * (2 * tvDiam Y) * ∑ b, negPart v b := by
              intro a; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
            simp_rw [h1]
            rw [← Finset.sum_mul, ← Finset.sum_mul]
            ring
          rw [this]; ring
      _ = tvDiam Y * l1 v := by
          rw [hp, hn]
          have hl1 : l1 v = 2 * m := by rw [hm]; ring
          rw [hl1]; field_simp

/-- Row sums of a product of row-stochastic matrices are one. -/
lemma rowsum_mul_one (A B : Matrix V V ℝ) (hA : ∀ a, ∑ b, A a b = 1) (hB : ∀ b, ∑ c, B b c = 1)
    (a : V) : ∑ c, (A * B) a c = 1 := by
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hB, mul_one]
  exact hA a

lemma rowsum_pow_one (A : Matrix V V ℝ) (hA : ∀ a, ∑ b, A a b = 1) (n : ℕ) (a : V) :
    ∑ c, (A ^ n) a c = 1 := by
  induction n generalizing a with
  | zero => simp [Matrix.one_apply]
  | succ m ih => rw [pow_succ]; exact rowsum_mul_one _ _ ih hA a

/-- `u·(X − Y)` is mean-zero when both kernels are row-stochastic. -/
lemma sum_vecMul_sub_eq_zero (X Y : Matrix V V ℝ) (hX : ∀ a, ∑ b, X a b = 1)
    (hY : ∀ a, ∑ b, Y a b = 1) (u : V → ℝ) : ∑ c, (u ᵥ* (X - Y)) c = 0 := by
  simp only [Matrix.vecMul, dotProduct, Matrix.sub_apply]
  rw [Finset.sum_comm]
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, hX, hY]
  simp

/-- **Saturating orbit telescoping.** For row-stochastic `X` (truth) and `Y` (estimate) with
`τ = tvDiam Y`: `‖w(Xⁿ − Yⁿ)‖₁ ≤ Σ_{k<n} τ^{n−1−k} ‖(wXᵏ)(X − Y)‖₁`. -/
theorem l1_vecMul_pow_sub_pow_le_geom [Nonempty V] (X Y : Matrix V V ℝ)
    (hX : ∀ a, ∑ b, X a b = 1) (hY : ∀ a, ∑ b, Y a b = 1) (w : V → ℝ) (n : ℕ) :
    l1 (w ᵥ* (X ^ n - Y ^ n)) ≤
      ∑ k ∈ Finset.range n, tvDiam Y ^ (n - 1 - k) * l1 ((w ᵥ* X ^ k) ᵥ* (X - Y)) := by
  induction n with
  | zero => simp [l1]
  | succ m ih =>
    have key : w ᵥ* (X ^ (m + 1) - Y ^ (m + 1)) =
        (w ᵥ* (X ^ m - Y ^ m)) ᵥ* Y + (w ᵥ* X ^ m) ᵥ* (X - Y) := by
      rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.vecMul_add]
      congr 1
      rw [pow_succ, pow_succ]
      noncomm_ring
    have hmean : ∑ c, (w ᵥ* (X ^ m - Y ^ m)) c = 0 :=
      sum_vecMul_sub_eq_zero (X ^ m) (Y ^ m) (rowsum_pow_one X hX m) (rowsum_pow_one Y hY m) w
    have hcontr := l1_vecMul_le_tvDiam_of_sum_zero Y hY _ hmean
    rw [key, Finset.sum_range_succ]
    refine le_trans (l1_add_le _ _) ?_
    have hτ := tvDiam_nonneg Y
    have hshift : ∑ k ∈ Finset.range m, tvDiam Y ^ (m + 1 - 1 - k) * l1 ((w ᵥ* X ^ k) ᵥ* (X - Y)) =
        tvDiam Y * ∑ k ∈ Finset.range m, tvDiam Y ^ (m - 1 - k) * l1 ((w ᵥ* X ^ k) ᵥ* (X - Y)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k < m := Finset.mem_range.mp hk
      have : m + 1 - 1 - k = (m - 1 - k) + 1 := by omega
      rw [this, pow_succ]; ring
    rw [hshift]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
    have : tvDiam Y * l1 (w ᵥ* (X ^ m - Y ^ m)) ≤
        tvDiam Y * ∑ k ∈ Finset.range m, tvDiam Y ^ (m - 1 - k) * l1 ((w ᵥ* X ^ k) ᵥ* (X - Y)) :=
      mul_le_mul_of_nonneg_left ih hτ
    linarith

/-- **Saturating estimation radius**: with row-L¹ gap `η` between the estimate `Y` and the truth
`X`, and `τ = tvDiam Y < 1`, `‖w(Xⁿ − Yⁿ)‖₁ ≤ η·‖w‖₁/(1 − τ)` for every `n`. -/
theorem estimation_radius_saturating [Nonempty V] (X Y : Matrix V V ℝ)
    (hXnn : ∀ a b, 0 ≤ X a b) (hX : ∀ a, ∑ b, X a b = 1) (hY : ∀ a, ∑ b, Y a b = 1)
    (w : V → ℝ) (n : ℕ) {η : ℝ} (hη : rowL1Dist Y X ≤ η) (hτ : tvDiam Y < 1) :
    l1 (w ᵥ* (X ^ n - Y ^ n)) ≤ η * l1 w / (1 - tvDiam Y) := by
  have hτ0 := tvDiam_nonneg Y
  have hdist0 : 0 ≤ rowL1Dist Y X := by
    unfold rowL1Dist
    exact le_trans (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (Finset.le_sup' (fun a => ∑ b, |Y a b - X a b|) (mem_univ (Classical.arbitrary V)))
  have hη0 : 0 ≤ η := le_trans hdist0 hη
  have hterm : ∀ k ∈ Finset.range n,
      tvDiam Y ^ (n - 1 - k) * l1 ((w ᵥ* X ^ k) ᵥ* (X - Y)) ≤ tvDiam Y ^ (n - 1 - k) * (η * l1 w) := by
    intro k _
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hτ0 _)
    have hpow : ∀ j : ℕ, l1 (w ᵥ* X ^ j) ≤ l1 w := by
      intro j
      induction j with
      | zero => simp
      | succ j ihj =>
        rw [pow_succ, ← Matrix.vecMul_vecMul]
        exact le_trans (l1_vecMul_le_of_stochastic X hXnn hX _) ihj
    have hsub : (w ᵥ* X ^ k) ᵥ* (X - Y) = -((w ᵥ* X ^ k) ᵥ* (Y - X)) := by
      rw [← Matrix.vecMul_neg, neg_sub]
    calc l1 ((w ᵥ* X ^ k) ᵥ* (X - Y)) = l1 ((w ᵥ* X ^ k) ᵥ* (Y - X)) := by
          rw [hsub]; unfold l1; simp [abs_neg]
      _ ≤ l1 (w ᵥ* X ^ k) * rowL1Dist Y X := l1_vecMul_sub_le Y X _
      _ ≤ l1 w * η := mul_le_mul (hpow k) hη hdist0 (l1_nonneg w)
      _ = η * l1 w := mul_comm _ _
  have hgeom : ∑ k ∈ Finset.range n, tvDiam Y ^ (n - 1 - k) ≤ 1 / (1 - tvDiam Y) := by
    have hre : ∑ k ∈ Finset.range n, tvDiam Y ^ (n - 1 - k) = ∑ k ∈ Finset.range n, tvDiam Y ^ k := by
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k < n := Finset.mem_range.mp hk
      congr 1
      omega
    rw [hre]
    have h1τ : 0 < 1 - tvDiam Y := by linarith
    -- Σ_{k<n} τ^k = (1 − τ^n)/(1 − τ) ≤ 1/(1 − τ)
    have hsum : ∑ k ∈ Finset.range n, tvDiam Y ^ k = (1 - tvDiam Y ^ n) / (1 - tvDiam Y) := by
      have := geom_sum_eq (x := tvDiam Y) (by linarith : tvDiam Y ≠ 1) n
      rw [this]
      have h2 : tvDiam Y - 1 ≠ 0 := by linarith
      field_simp
      ring
    rw [hsum]
    apply div_le_div_of_nonneg_right _ h1τ.le
    have := pow_nonneg hτ0 n
    linarith
  calc l1 (w ᵥ* (X ^ n - Y ^ n))
      ≤ ∑ k ∈ Finset.range n, tvDiam Y ^ (n - 1 - k) * l1 ((w ᵥ* X ^ k) ᵥ* (X - Y)) :=
        l1_vecMul_pow_sub_pow_le_geom X Y hX hY w n
    _ ≤ ∑ k ∈ Finset.range n, tvDiam Y ^ (n - 1 - k) * (η * l1 w) := Finset.sum_le_sum hterm
    _ = (∑ k ∈ Finset.range n, tvDiam Y ^ (n - 1 - k)) * (η * l1 w) := by rw [Finset.sum_mul]
    _ ≤ (1 / (1 - tvDiam Y)) * (η * l1 w) :=
        mul_le_mul_of_nonneg_right hgeom (mul_nonneg hη0 (l1_nonneg w))
    _ = η * l1 w / (1 - tvDiam Y) := by ring

/-! ## §3. Per-mode accumulation: buy for slow modes, rent for fast ones

Project the discrete telescoping `Xⁿ − Yⁿ = Σ_k X^{n−1−k}(X − Y)Yᵏ` onto a **left eigenvector**
`v·X = μ·v` of the fine kernel (`0 ≤ μ < 1`: a decaying mode). The source seen by the mode at
step `k` is `s_k := v·((X − Y)·(Yᵏ f))`; if `|s_k| ≤ S` for all `k`, then

  `|v·((Xⁿ − Yⁿ) f)| ≤ S·(1 − μⁿ)/(1 − μ) ≤ S·min(n, 1/(1 − μ))`.

A slow mode (`μ` near 1) accumulates `≈ S·n`; a fast mode saturates at the quasi-static level
`S/(1 − μ)` and stays there while the source persists. This is the discrete-time form of the
`S_k·min(t, 1/λ_k)` law of decision 0088 (4,264 numerical checks), and it needs no spectral
theorem — one eigenvector and a source bound. The hypothesis on the source is the sup over
steps, as a reviewer requested. -/

/-- A left eigenvector sees the telescoping as a geometric sum of its own sources. -/
lemma dot_pow_sub_pow_eq_sum (X Y : Matrix V V ℝ) (v f : V → ℝ) {μ : ℝ} (hv : v ᵥ* X = μ • v) (n : ℕ) :
    v ⬝ᵥ ((X ^ n - Y ^ n) *ᵥ f) = ∑ k ∈ Finset.range n, μ ^ (n - 1 - k) * (v ⬝ᵥ ((X - Y) *ᵥ (Y ^ k *ᵥ f))) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have key : (X ^ (m + 1) - Y ^ (m + 1)) *ᵥ f =
        X *ᵥ ((X ^ m - Y ^ m) *ᵥ f) + (X - Y) *ᵥ (Y ^ m *ᵥ f) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec]
      congr 1
      rw [pow_succ', pow_succ']
      noncomm_ring
    have hvX : ∀ u : V → ℝ, v ⬝ᵥ (X *ᵥ u) = μ * (v ⬝ᵥ u) := by
      intro u
      rw [Matrix.dotProduct_mulVec, hv, smul_dotProduct, smul_eq_mul]
    rw [key, dotProduct_add, hvX, ih, Finset.sum_range_succ, Finset.mul_sum]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < m := Finset.mem_range.mp hk
    have : m - k = (m - 1 - k) + 1 := by omega
    rw [this, pow_succ]; ring

/-- **Per-mode accumulation bound.** For a left eigenvector `v·X = μ·v` with `0 ≤ μ < 1` and a
source bound `|v·((X − Y)·(Yᵏ f))| ≤ S` for all `k`:
`|v·((Xⁿ − Yⁿ)f)| ≤ S·(1 − μⁿ)/(1 − μ)`. -/
theorem abs_dot_pow_sub_pow_le (X Y : Matrix V V ℝ) (v f : V → ℝ) {μ S : ℝ}
    (hv : v ᵥ* X = μ • v) (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) (hS0 : 0 ≤ S)
    (hsrc : ∀ k : ℕ, |v ⬝ᵥ ((X - Y) *ᵥ (Y ^ k *ᵥ f))| ≤ S) (n : ℕ) :
    |v ⬝ᵥ ((X ^ n - Y ^ n) *ᵥ f)| ≤ S * (1 - μ ^ n) / (1 - μ) := by
  rw [dot_pow_sub_pow_eq_sum X Y v f hv n]
  have h1μ : 0 < 1 - μ := by linarith
  calc |∑ k ∈ Finset.range n, μ ^ (n - 1 - k) * (v ⬝ᵥ ((X - Y) *ᵥ (Y ^ k *ᵥ f)))|
      ≤ ∑ k ∈ Finset.range n, |μ ^ (n - 1 - k) * (v ⬝ᵥ ((X - Y) *ᵥ (Y ^ k *ᵥ f)))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, μ ^ (n - 1 - k) * S := by
        apply Finset.sum_le_sum; intro k _
        rw [abs_mul, abs_of_nonneg (pow_nonneg hμ0 _)]
        exact mul_le_mul_of_nonneg_left (hsrc k) (pow_nonneg hμ0 _)
    _ = (∑ k ∈ Finset.range n, μ ^ k) * S := by
        rw [Finset.sum_mul]
        rw [← Finset.sum_range_reflect]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' : k < n := Finset.mem_range.mp hk
        congr 2; omega
    _ = S * (1 - μ ^ n) / (1 - μ) := by
        rw [geom_sum_eq (by linarith : μ ≠ 1) n]
        have h2 : μ - 1 ≠ 0 := by linarith
        field_simp
        ring

/-- The rent-or-buy corollary: `S·(1 − μⁿ)/(1 − μ) ≤ S·min(n, 1/(1 − μ))`. -/
theorem geom_accum_le_min {μ S : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) (hS0 : 0 ≤ S) (n : ℕ) :
    S * (1 - μ ^ n) / (1 - μ) ≤ S * min (n : ℝ) (1 / (1 - μ)) := by
  have h1μ : 0 < 1 - μ := by linarith
  have hμn : 0 ≤ μ ^ n := pow_nonneg hμ0 n
  have hμn1 : μ ^ n ≤ 1 := pow_le_one₀ hμ0 hμ1.le
  rw [mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ hS0
  apply le_min
  · -- (1 − μⁿ)/(1 − μ) = Σ_{k<n} μᵏ ≤ n
    rw [div_le_iff₀ h1μ]
    -- 1 − μⁿ ≤ n(1 − μ): Bernoulli, i.e. μⁿ ≥ 1 − n(1 − μ)
    have hb := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ -(1 - μ)) n
    have : 1 + (n : ℝ) * (-(1 - μ)) = 1 - (n : ℝ) * (1 - μ) := by ring
    rw [this] at hb
    have : (1 + -(1 - μ)) = μ := by ring
    rw [this] at hb
    linarith
  · rw [div_le_div_iff_of_pos_right h1μ]
    linarith

/-! ## §4. One certificate, two radii -/

lemma l1Error_triangle {Ω : Type*} [Fintype Ω] (p q r : Ω → ℝ) :
    SGC.InformationGeometry.EstimatedDecision.l1Error p r ≤
      SGC.InformationGeometry.EstimatedDecision.l1Error p q +
      SGC.InformationGeometry.EstimatedDecision.l1Error q r := by
  unfold SGC.InformationGeometry.EstimatedDecision.l1Error
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun ω _ => by
    have := abs_sub_le (p ω) (q ω) (r ω); exact this

/-- **Two-radii refine certificate.** If the true law `p` is within `r₁` of the true coarse
prediction `p̄` (coarse-graining: the orbit radius) and `p̄` is within `r₂` of the agent's
estimated prediction `p̂` (estimation: `η/(1 − τ)` or `n·η`), then an estimated VOI clearing
`cost + 2M(r₁ + r₂)` certifies refinement under the truth. -/
theorem two_radii_refine_certificate {Ω β γ α : Type*} [Fintype Ω] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype α] [Nonempty α]
    (q : Ω → β) (f : β → γ) (rule : β → α) (p pbar phat : Ω → ℝ) (u : α → Ω → ℝ)
    (hopt : ∀ b, SGC.InformationGeometry.DecisionValue.blockUtility q phat u b (rule b) =
      SGC.InformationGeometry.DecisionValue.blockValue q phat u b)
    {M r₁ r₂ cost : ℝ} (hM0 : 0 ≤ M) (hM : ∀ a ω, |u a ω| ≤ M)
    (h₁ : SGC.InformationGeometry.EstimatedDecision.l1Error p pbar ≤ r₁)
    (h₂ : SGC.InformationGeometry.EstimatedDecision.l1Error pbar phat ≤ r₂)
    (hmargin : cost + 2 * M * (r₁ + r₂) < SGC.InformationGeometry.DecisionValue.voi q f phat u) :
    SGC.InformationGeometry.DecisionValue.value (f ∘ q) p u <
      SGC.InformationGeometry.EstimatedDecision.policyValue q p u rule - cost :=
  SGC.InformationGeometry.EstimatedDecision.empirical_refinement_safe_of_radius q p phat u f rule hopt hM0 hM
    (le_trans (l1Error_triangle p pbar phat) (add_le_add h₁ h₂)) hmargin

/-- **Two-radii stop certificate.** -/
theorem two_radii_stop_certificate {Ω β γ α : Type*} [Fintype Ω] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype α] [Nonempty α]
    (q : Ω → β) (f : β → γ) (p pbar phat : Ω → ℝ) (u : α → Ω → ℝ)
    {M r₁ r₂ cost : ℝ} (hM0 : 0 ≤ M) (hM : ∀ a ω, |u a ω| ≤ M)
    (h₁ : SGC.InformationGeometry.EstimatedDecision.l1Error p pbar ≤ r₁)
    (h₂ : SGC.InformationGeometry.EstimatedDecision.l1Error pbar phat ≤ r₂)
    (hmargin : SGC.InformationGeometry.DecisionValue.voi q f phat u + 2 * M * (r₁ + r₂) ≤ cost) :
    SGC.InformationGeometry.DecisionValue.value q p u - cost ≤
      SGC.InformationGeometry.DecisionValue.value (f ∘ q) p u :=
  SGC.InformationGeometry.EstimatedDecision.refinement_not_profitable_of_radius q p phat u f hM0 hM
    (le_trans (l1Error_triangle p pbar phat) (add_le_add h₁ h₂)) hmargin

end SGC.Bridge.TwoRadii
