/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Bridge.TwoRadii

/-!
# Coarse-graining certificates in total variation, for any chain

`DecisionHorizon` certifies decisions from a leaky coarse model through `L²(π)` and needs
reversibility to identify the law evolution with the adjoint. The total-variation telescoping of
`TwoRadii` removes both: it needs two row-stochastic kernels and nothing else.

* The **lifted coarse kernel** `Ŷ(x,y) = K̄(q x, q y)·π(y | q y)` is the fine-state kernel an agent
  implicitly uses when it predicts with a quotient chain `K̄` and re-expands with the in-block
  conditionals. It is row-stochastic whenever `K̄` is and the conditionals sum to one per block.
* **TV orbit radius**: `‖p₀(Xⁿ − Ŷⁿ)‖₁ ≤ Σ_{k<n} ‖(p₀Ŷᵏ)(X − Ŷ)‖₁` — the one-step discrepancy
  summed along the agent's own predicted orbit. No `π`-weighted norm, no reversibility, no spectral
  hypothesis. This is the certificate radius for irreversible environments.
* **Mixing radius**: if `π` is stationary for both kernels, `‖p₀(Xⁿ − Ŷⁿ)‖₁ ≤ (τ(Xⁿ) + τ(Ŷⁿ))·‖p₀ − π‖₁`
  with `τ` the Dobrushin coefficient. Both models forget the initial macrostate, so the
  coarse-graining error vanishes at long horizons even though the orbit radius cannot decrease.
  The certificate radius is the minimum of the two.
* **Task-invariant quotients are sufficient**: if the utility is constant on the blocks of `q`,
  refining `q` to the fine state has zero value of information. This turns the task-aware filter
  for symmetry learning (decision 0089) into a theorem.
-/

noncomputable section

namespace SGC.Bridge.OrbitRadiusTV

open Finset Matrix SGC.Bridge.TwoRadii

set_option linter.unusedSectionVars false

variable {V β : Type*} [Fintype V] [DecidableEq V] [Fintype β] [DecidableEq β]

/-- The fine-state kernel implicitly used by a quotient model: move the block by `K̄`, then
re-expand with the in-block conditional `pin`. -/
def liftedCoarse (Kbar : Matrix β β ℝ) (q : V → β) (pin : V → ℝ) : Matrix V V ℝ :=
  fun x y => Kbar (q x) (q y) * pin y

lemma liftedCoarse_nonneg (Kbar : Matrix β β ℝ) (q : V → β) (pin : V → ℝ)
    (hK : ∀ a b, 0 ≤ Kbar a b) (hpin : ∀ y, 0 ≤ pin y) (x y : V) :
    0 ≤ liftedCoarse Kbar q pin x y :=
  mul_nonneg (hK _ _) (hpin y)

/-- The lifted kernel is row-stochastic when `K̄` is and the conditionals sum to one per block. -/
lemma liftedCoarse_rowsum (Kbar : Matrix β β ℝ) (q : V → β) (pin : V → ℝ)
    (hKrow : ∀ a, ∑ b, Kbar a b = 1)
    (hblock : ∀ b : β, ∑ y ∈ univ.filter (fun y => q y = b), pin y = 1) (x : V) :
    ∑ y, liftedCoarse Kbar q pin x y = 1 := by
  unfold liftedCoarse
  calc ∑ y, Kbar (q x) (q y) * pin y
      = ∑ b, ∑ y ∈ univ.filter (fun y => q y = b), Kbar (q x) (q y) * pin y := by
        rw [← Finset.sum_fiberwise (s := univ) (g := q)]
    _ = ∑ b, Kbar (q x) b * ∑ y ∈ univ.filter (fun y => q y = b), pin y := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [(Finset.mem_filter.mp hy).2]
    _ = ∑ b, Kbar (q x) b := by simp [hblock]
    _ = 1 := hKrow (q x)

/-- **TV orbit radius for any chain.** `X` the true one-step kernel, `Y` any row-stochastic
model kernel (e.g. `liftedCoarse`): the error of the model's `n`-step law is at most the sum of the
one-step discrepancies along the **model's own predicted orbit**. -/
theorem tv_orbit_radius (X Y : Matrix V V ℝ) (hXnn : ∀ a b, 0 ≤ X a b) (hX : ∀ a, ∑ b, X a b = 1)
    (p₀ : V → ℝ) (n : ℕ) :
    l1 (p₀ ᵥ* (X ^ n - Y ^ n)) ≤ ∑ k ∈ Finset.range n, l1 ((p₀ ᵥ* Y ^ k) ᵥ* (X - Y)) :=
  l1_vecMul_pow_sub_pow_le_sum X Y hXnn hX p₀ n

/-- **Mixing radius.** If `π` is stationary for both kernels, both `n`-step laws are within a
Dobrushin factor of `π`, so their distance is bounded by `(τ(Xⁿ) + τ(Yⁿ))·‖p₀ − π‖₁`: the
coarse-graining error vanishes as both models forget the initial law. -/
theorem mixing_radius [Nonempty V] (X Y : Matrix V V ℝ) (π p₀ : V → ℝ)
    (hX : ∀ a, ∑ b, X a b = 1) (hY : ∀ a, ∑ b, Y a b = 1)
    (hπX : π ᵥ* X = π) (hπY : π ᵥ* Y = π) (hπ1 : ∑ x, π x = 1) (hp1 : ∑ x, p₀ x = 1) (n : ℕ) :
    l1 (p₀ ᵥ* (X ^ n - Y ^ n)) ≤ (tvDiam (X ^ n) + tvDiam (Y ^ n)) * l1 (p₀ - π) := by
  have hstat : ∀ (Z : Matrix V V ℝ), π ᵥ* Z = π → ∀ m : ℕ, π ᵥ* Z ^ m = π := by
    intro Z hZ m
    induction m with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hZ]
  have hπXn : π ᵥ* X ^ n = π := hstat X hπX n
  have hπYn : π ᵥ* Y ^ n = π := hstat Y hπY n
  have hmean : ∑ x, (p₀ - π) x = 0 := by
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, hπ1, hp1, sub_self]
  have hsplit : p₀ ᵥ* (X ^ n - Y ^ n) = (p₀ - π) ᵥ* X ^ n - (p₀ - π) ᵥ* Y ^ n := by
    rw [Matrix.vecMul_sub, Matrix.sub_vecMul, Matrix.sub_vecMul, hπXn, hπYn]
    abel
  have hneg : ∀ v : V → ℝ, l1 (-v) = l1 v := by
    intro v; unfold l1; simp [abs_neg]
  rw [hsplit]
  calc l1 ((p₀ - π) ᵥ* X ^ n - (p₀ - π) ᵥ* Y ^ n)
      = l1 ((p₀ - π) ᵥ* X ^ n + -((p₀ - π) ᵥ* Y ^ n)) := by rw [sub_eq_add_neg]
    _ ≤ l1 ((p₀ - π) ᵥ* X ^ n) + l1 (-((p₀ - π) ᵥ* Y ^ n)) := l1_add_le _ _
    _ = l1 ((p₀ - π) ᵥ* X ^ n) + l1 ((p₀ - π) ᵥ* Y ^ n) := by rw [hneg]
    _ ≤ tvDiam (X ^ n) * l1 (p₀ - π) + tvDiam (Y ^ n) * l1 (p₀ - π) :=
        add_le_add (l1_vecMul_le_tvDiam_of_sum_zero (X ^ n) (rowsum_pow_one X hX n) _ hmean)
          (l1_vecMul_le_tvDiam_of_sum_zero (Y ^ n) (rowsum_pow_one Y hY n) _ hmean)
    _ = (tvDiam (X ^ n) + tvDiam (Y ^ n)) * l1 (p₀ - π) := by ring

/-- **Two-sided horizon**: the certificate radius is the smaller of the orbit and mixing radii. -/
theorem two_sided_radius [Nonempty V] (X Y : Matrix V V ℝ) (π p₀ : V → ℝ)
    (hXnn : ∀ a b, 0 ≤ X a b) (hX : ∀ a, ∑ b, X a b = 1) (hY : ∀ a, ∑ b, Y a b = 1)
    (hπX : π ᵥ* X = π) (hπY : π ᵥ* Y = π) (hπ1 : ∑ x, π x = 1) (hp1 : ∑ x, p₀ x = 1) (n : ℕ) :
    l1 (p₀ ᵥ* (X ^ n - Y ^ n)) ≤
      min (∑ k ∈ Finset.range n, l1 ((p₀ ᵥ* Y ^ k) ᵥ* (X - Y)))
          ((tvDiam (X ^ n) + tvDiam (Y ^ n)) * l1 (p₀ - π)) :=
  le_min (tv_orbit_radius X Y hXnn hX p₀ n) (mixing_radius X Y π p₀ hX hY hπX hπY hπ1 hp1 n)

/-! ## Task-invariant quotients are sufficient -/

/-- `c * sup' f = sup' (c * f)` for `c ≥ 0`. -/
lemma mul_sup'_of_nonneg {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    c * s.sup' hs f = s.sup' hs (fun i => c * f i) := by
  rcases eq_or_lt_of_le hc with h0 | hpos
  · subst h0; simp
  · exact Finset.mul₀_sup' hpos f s hs

open SGC.InformationGeometry.DecisionValue in
/-- If the utility is constant on the blocks of `q` (e.g. `q` is the orbit map of a symmetry
group under which the task is invariant), observing the fine state adds no value over observing
the block: `voi id q w u = 0`. -/
theorem voi_id_eq_zero_of_block_constant {Ω α : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype α] [Nonempty α]
    (q : Ω → β) (w : Ω → ℝ) (u : α → Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hu : ∀ a ω ω', q ω = q ω' → u a ω = u a ω') :
    voi (id : Ω → Ω) q w u = 0 := by
  unfold voi
  have hfine : value (id : Ω → Ω) w u = ∑ ω, w ω * univ.sup' univ_nonempty (fun a => u a ω) := by
    unfold value blockValue blockUtility
    refine Finset.sum_congr rfl fun ω _ => ?_
    have hfilter : univ.filter (fun ω' : Ω => id ω' = ω) = {ω} := by
      ext ω'; simp [eq_comm]
    simp only [hfilter, Finset.sum_singleton]
    rw [mul_sup'_of_nonneg univ univ_nonempty _ (hw ω)]
  have hcoarse : value (q ∘ id) w u = ∑ ω, w ω * univ.sup' univ_nonempty (fun a => u a ω) := by
    unfold value blockValue blockUtility
    simp only [Function.comp_id]
    rw [← Finset.sum_fiberwise (s := univ) (g := q)]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : (univ.filter (fun ω => q ω = b)).Nonempty
    · obtain ⟨ω₀, hω₀⟩ := hb
      have hω₀b : q ω₀ = b := (Finset.mem_filter.mp hω₀).2
      -- on the block every utility equals its value at ω₀
      have hrow : ∀ a, ∑ ω ∈ univ.filter (fun ω => q ω = b), w ω * u a ω =
          (∑ ω ∈ univ.filter (fun ω => q ω = b), w ω) * u a ω₀ := by
        intro a
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun ω hω => ?_
        rw [hu a ω ω₀ (by rw [(Finset.mem_filter.mp hω).2, hω₀b])]
      have hsup_u : ∀ ω ∈ univ.filter (fun ω => q ω = b),
          univ.sup' univ_nonempty (fun a => u a ω) = univ.sup' univ_nonempty (fun a => u a ω₀) := by
        intro ω hω
        congr 1; funext a
        exact hu a ω ω₀ (by rw [(Finset.mem_filter.mp hω).2, hω₀b])
      have hW : 0 ≤ ∑ ω ∈ univ.filter (fun ω => q ω = b), w ω := Finset.sum_nonneg fun ω _ => hw ω
      calc univ.sup' univ_nonempty (fun a => ∑ ω ∈ univ.filter (fun ω => q ω = b), w ω * u a ω)
          = univ.sup' univ_nonempty (fun a => (∑ ω ∈ univ.filter (fun ω => q ω = b), w ω) * u a ω₀) := by
            congr 1; funext a; exact hrow a
        _ = (∑ ω ∈ univ.filter (fun ω => q ω = b), w ω) * univ.sup' univ_nonempty (fun a => u a ω₀) :=
            (mul_sup'_of_nonneg univ univ_nonempty _ hW).symm
        _ = ∑ ω ∈ univ.filter (fun ω => q ω = b), w ω * univ.sup' univ_nonempty (fun a => u a ω₀) := by
            rw [Finset.sum_mul]
        _ = ∑ ω ∈ univ.filter (fun ω => q ω = b), w ω * univ.sup' univ_nonempty (fun a => u a ω) :=
            Finset.sum_congr rfl fun ω hω => by rw [hsup_u ω hω]
    · rw [Finset.not_nonempty_iff_eq_empty] at hb
      simp [hb]
  rw [hfine, hcoarse, sub_self]

end SGC.Bridge.OrbitRadiusTV
