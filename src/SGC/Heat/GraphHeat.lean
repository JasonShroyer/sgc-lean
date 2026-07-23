/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# Graph Heat Flow: Dirichlet Energy Dissipation (Phase 4 vertical slice)

The discrete-heat archetype for the formal-artifact pipeline: explicit-Euler
heat flow on a finite simple graph dissipates Dirichlet energy under the CFL
step bound `h * maxDegree ≤ 1`.

Main results:
* `energy_nonneg`      : `0 ≤ E(x)` where `E(x) = xᵀ L x` (Laplacian PSD).
* `quadForm_le_two_maxDegree_mul` : `yᵀ L y ≤ 2·Δ·‖y‖²` — the spectral
  bound `λ_max(L) ≤ 2Δ` in quadratic-form clothing, proved from the edge-sum
  Dirichlet identity, no eigenvalues needed.
* `energy_nonincreasing` : one explicit-Euler step `x ← x − h·Lx` with
  `0 ≤ h` and `h·Δ ≤ 1` satisfies `E(x') ≤ E(x)`.

The proof of dissipation is the exact expansion
`E(x − h·a) = E(x) − 2h·⟨a,a⟩ + h²·aᵀLa` with `a = Lx` (symmetry of `L`
turns both cross terms into `⟨a,a⟩`), then the quadratic-form bound absorbs
the second-order term: `h²·aᵀLa ≤ h²·2Δ·⟨a,a⟩ ≤ 2h·⟨a,a⟩`.

This is the exact-real side of the `sgc-heat-graph-1d-energy-dissipation`
artifact contract; the float64 companion receipt lives in the vault.
-/

namespace SGC.Heat

open Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Dirichlet energy of a state: `E(x) = xᵀ L x`. -/
def dirichletEnergy (x : V → ℝ) : ℝ := x ⬝ᵥ (G.lapMatrix ℝ *ᵥ x)

/-- One explicit-Euler heat step: `x ← x − h·Lx`. -/
def eulerStep (h : ℝ) (x : V → ℝ) : V → ℝ := x - h • (G.lapMatrix ℝ *ᵥ x)

/-- The Dirichlet energy is the edge sum `(∑_{i~j} (x i − x j)²)/2`. -/
theorem dirichletEnergy_eq_sum (x : V → ℝ) :
    dirichletEnergy G x =
      (∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j) ^ 2 else 0) / 2 := by
  rw [dirichletEnergy, ← Matrix.toLinearMap₂'_apply',
    SimpleGraph.lapMatrix_toLinearMap₂']

/-- Dirichlet energy is non-negative (the Laplacian is PSD). -/
theorem energy_nonneg (x : V → ℝ) : 0 ≤ dirichletEnergy G x := by
  rw [dirichletEnergy_eq_sum]
  have : (0:ℝ) ≤ ∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j) ^ 2 else 0 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      by_cases hij : G.Adj i j <;> simp [hij, sq_nonneg]
  linarith

omit [DecidableEq V] in
private lemma sum_ite_adj_const (i : V) (c : ℝ) :
    (∑ j : V, if G.Adj i j then c else 0) = (G.degree i : ℝ) * c := by
  have hcard : (Finset.univ.filter (G.Adj i)).card = G.degree i := by
    rw [← SimpleGraph.neighborFinset_eq_filter]; rfl
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
    nsmul_eq_mul, hcard]

/-- Quadratic-form degree bound: `yᵀ L y ≤ 2·Δ·⟨y,y⟩`. This packages the
spectral fact `λ_max(L) ≤ 2·maxDegree` without touching eigenvalues. -/
theorem quadForm_le_two_maxDegree_mul (y : V → ℝ) :
    y ⬝ᵥ (G.lapMatrix ℝ *ᵥ y) ≤ 2 * (G.maxDegree : ℝ) * (y ⬝ᵥ y) := by
  rw [← dirichletEnergy, dirichletEnergy_eq_sum]
  have step1 : (∑ i : V, ∑ j : V, if G.Adj i j then (y i - y j) ^ 2 else 0)
      ≤ ∑ i : V, ∑ j : V, if G.Adj i j then 2 * y i ^ 2 + 2 * y j ^ 2 else 0 := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    by_cases hij : G.Adj i j
    · simpa [hij] using by nlinarith [sq_nonneg (y i + y j)]
    · simp [hij]
  have split : (∑ i : V, ∑ j : V,
        if G.Adj i j then 2 * y i ^ 2 + 2 * y j ^ 2 else 0)
      = (∑ i : V, (G.degree i : ℝ) * (2 * y i ^ 2))
        + ∑ j : V, (G.degree j : ℝ) * (2 * y j ^ 2) := by
    have pointwise : ∀ i j : V,
        (if G.Adj i j then 2 * y i ^ 2 + 2 * y j ^ 2 else 0)
          = (if G.Adj i j then 2 * y i ^ 2 else 0)
            + (if G.Adj i j then 2 * y j ^ 2 else 0) := by
      intro i j; by_cases hij : G.Adj i j <;> simp [hij]
    simp_rw [pointwise, Finset.sum_add_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => sum_ite_adj_const G i _
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      have flip : ∀ i : V, (if G.Adj i j then 2 * y j ^ 2 else 0)
          = (if G.Adj j i then 2 * y j ^ 2 else 0) := fun i => by
        rw [if_congr (SimpleGraph.adj_comm G i j) rfl rfl]
      simp_rw [flip]
      exact sum_ite_adj_const G j _
  have cap : (∑ i : V, (G.degree i : ℝ) * (2 * y i ^ 2))
      ≤ ∑ i : V, (G.maxDegree : ℝ) * (2 * y i ^ 2) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have hd : (G.degree i : ℝ) ≤ (G.maxDegree : ℝ) :=
      Nat.cast_le.mpr (G.degree_le_maxDegree i)
    have hy : (0:ℝ) ≤ 2 * y i ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right hd hy
  have norm_eq : (y ⬝ᵥ y) = ∑ i : V, y i ^ 2 := by
    simp [dotProduct, sq]
  have total : (∑ i : V, ∑ j : V, if G.Adj i j then (y i - y j) ^ 2 else 0)
      ≤ 4 * (G.maxDegree : ℝ) * ∑ i : V, y i ^ 2 := by
    calc (∑ i : V, ∑ j : V, if G.Adj i j then (y i - y j) ^ 2 else 0)
        ≤ (∑ i : V, (G.degree i : ℝ) * (2 * y i ^ 2))
          + ∑ j : V, (G.degree j : ℝ) * (2 * y j ^ 2) := by
          rw [← split]; exact step1
      _ ≤ (∑ i : V, (G.maxDegree : ℝ) * (2 * y i ^ 2))
          + ∑ i : V, (G.maxDegree : ℝ) * (2 * y i ^ 2) := add_le_add cap cap
      _ = 4 * (G.maxDegree : ℝ) * ∑ i : V, y i ^ 2 := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
  rw [norm_eq]
  linarith

/-- **Energy dissipation.** One explicit-Euler heat step never increases the
Dirichlet energy, provided `0 ≤ h` and the CFL bound `h·maxDegree ≤ 1`. -/
theorem energy_nonincreasing (h : ℝ) (hh : 0 ≤ h)
    (hCFL : h * (G.maxDegree : ℝ) ≤ 1) (x : V → ℝ) :
    dirichletEnergy G (eulerStep G h x) ≤ dirichletEnergy G x := by
  classical
  set L : Matrix V V ℝ := G.lapMatrix ℝ with hLdef
  set a : V → ℝ := L *ᵥ x with hadef
  have hsymm : Lᵀ = L := SimpleGraph.isSymm_lapMatrix G
  have cross : x ⬝ᵥ (L *ᵥ a) = a ⬝ᵥ a := by
    rw [dotProduct_mulVec, ← hsymm, Matrix.vecMul_transpose]
  have expand : dirichletEnergy G (eulerStep G h x)
      = dirichletEnergy G x - 2 * h * (a ⬝ᵥ a) + h ^ 2 * (a ⬝ᵥ (L *ᵥ a)) := by
    have lhs : eulerStep G h x = x - h • a := rfl
    rw [dirichletEnergy, lhs, Matrix.mulVec_sub, Matrix.mulVec_smul,
      sub_dotProduct, dotProduct_sub, dotProduct_sub,
      smul_dotProduct, smul_dotProduct, dotProduct_smul,
      dotProduct_smul, cross, dirichletEnergy]
    simp only [smul_eq_mul]
    ring
  have hA : (0:ℝ) ≤ a ⬝ᵥ a :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg (a i)
  have hQ : a ⬝ᵥ (L *ᵥ a) ≤ 2 * (G.maxDegree : ℝ) * (a ⬝ᵥ a) :=
    quadForm_le_two_maxDegree_mul G a
  have second_order : h ^ 2 * (a ⬝ᵥ (L *ᵥ a)) ≤ 2 * h * (a ⬝ᵥ a) := by
    have hsq : (0:ℝ) ≤ h ^ 2 := sq_nonneg h
    have step : h ^ 2 * (a ⬝ᵥ (L *ᵥ a))
        ≤ h ^ 2 * (2 * (G.maxDegree : ℝ) * (a ⬝ᵥ a)) :=
      mul_le_mul_of_nonneg_left hQ hsq
    have absorb : h ^ 2 * (2 * (G.maxDegree : ℝ) * (a ⬝ᵥ a))
        ≤ 2 * h * (a ⬝ᵥ a) := by
      have base : h * (G.maxDegree : ℝ) * (h * (a ⬝ᵥ a))
          ≤ 1 * (h * (a ⬝ᵥ a)) :=
        mul_le_mul_of_nonneg_right hCFL (mul_nonneg hh hA)
      nlinarith [base]
    linarith
  rw [expand]
  linarith

end SGC.Heat
