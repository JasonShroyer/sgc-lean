import SGC.Renormalization.Lumpability

/-!
# Sign convention of `DirichletGap`, and the spectral gap of a generator

`SGC.DirichletGap L π = sInf { ⟨u, L u⟩_π / ⟨u, u⟩_π | u ≠ 0, u ⊥_π 1 }` is a
convention-neutral set-theoretic quantity: `dirichlet_gap_non_decrease` holds for every
matrix `L`. Its *interpretation* as a spectral gap, however, requires `L` to be the
**positive** Laplacian `H = I − K` (or `−L` for a rate generator). For a genuine rate
generator — nonnegative off-diagonal entries and a stationary weight `π` with
`Σ_u π_u L_{u v} = 0` — the Dirichlet form is nonpositive on the test vector
`e_v − (π_v / Σπ)·1`, so `DirichletGap L π ≤ 0`
(`dirichletGap_nonpos_of_stationary`). Consequently any hypothesis set that contains both
"`L` is a generator" and "`0 < γ ≤ DirichletGap L π`" is unsatisfiable; the retired axiom
`gaspard_path_space_identity` in `Thermodynamics/EntropyProduction.lean` was of this form.

The generator-convention gap is `SpectralGap L π := DirichletGap (−L) π`.

Numerical witness (lattice gauge theory, `docs/experiments/gauge_lumpability_v1`): for the
Z₂ transfer chain at `β = 0.76`, `DirichletGap (K − I) π = −0.99911` while the spectral gaps
of `I − K` are `0.0898` (fine) and `0.2304` (gauge quotient).
-/

noncomputable section

namespace SGC

open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The spectral gap in the **generator** convention: the Dirichlet gap of the positive
Laplacian `−L`. For a reversible rate generator this is the smallest nonzero eigenvalue
of `−L` in `L²(π)`. -/
def SpectralGap (L : Matrix V V ℝ) (pi_dist : V → ℝ) : ℝ :=
  DirichletGap (-L) pi_dist

omit [DecidableEq V] in
lemma spectralGap_eq_dirichletGap_neg (L : Matrix V V ℝ) (pi_dist : V → ℝ) :
    SpectralGap L pi_dist = DirichletGap (-L) pi_dist := rfl

/-- Diagonal entries of a stationary generator are nonpositive, weighted by `π`:
`π_v L_{v v} = −Σ_{u ≠ v} π_u L_{u v} ≤ 0`. -/
lemma pi_mul_diag_nonpos (L : Matrix V V ℝ) (pi_dist : V → ℝ) (hπ : ∀ x, 0 < pi_dist x)
    (hL_gen : ∀ x y, x ≠ y → 0 ≤ L x y)
    (h_stat : ∀ v, ∑ u, pi_dist u * L u v = 0) (v : V) :
    pi_dist v * L v v ≤ 0 := by
  have h := h_stat v
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)] at h
  have hrest : 0 ≤ ∑ u ∈ Finset.univ.erase v, pi_dist u * L u v :=
    Finset.sum_nonneg fun u hu =>
      mul_nonneg (hπ u).le (hL_gen u v (Finset.ne_of_mem_erase hu))
  linarith

/-- The test vector `e_v − c·1` with `c = π_v / Σπ`: nonzero when `V` has two elements,
orthogonal to the constants, and with nonpositive Dirichlet form for a stationary
generator. -/
lemma dirichletForm_test_nonpos (L : Matrix V V ℝ) (pi_dist : V → ℝ) (hπ : ∀ x, 0 < pi_dist x)
    (hL_gen : ∀ x y, x ≠ y → 0 ≤ L x y)
    (h_stat : ∀ v, ∑ u, pi_dist u * L u v = 0) (v : V) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    inner_pi pi_dist (fun x => (if x = v then (1 : ℝ) else 0) - c)
      (L *ᵥ (fun x => (if x = v then (1 : ℝ) else 0) - c)) ≤ 0 := by
  set u : V → ℝ := fun x => (if x = v then (1 : ℝ) else 0) - c with hu
  -- (L u)_x = L x v − c · (row sum)_x
  have hLu : ∀ x, (L *ᵥ u) x = L x v - c * ∑ y, L x y := by
    intro x
    simp only [Matrix.mulVec, dotProduct, hu]
    have : ∀ y, L x y * ((if y = v then (1:ℝ) else 0) - c) =
        (if y = v then L x y else 0) - c * L x y := by
      intro y; split_ifs <;> ring
    simp_rw [this, Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ v,
      if_pos (Finset.mem_univ v), Finset.mul_sum]
  -- expand the inner product
  have hexp : inner_pi pi_dist u (L *ᵥ u) =
      ∑ x, pi_dist x * ((if x = v then (1:ℝ) else 0) - c) * (L x v - c * ∑ y, L x y) := by
    unfold inner_pi
    exact Finset.sum_congr rfl fun x _ => by rw [hLu x]
  rw [hexp]
  have hsplit : ∀ x, pi_dist x * ((if x = v then (1:ℝ) else 0) - c) * (L x v - c * ∑ y, L x y) =
      (if x = v then pi_dist x * (L x v - c * ∑ y, L x y) else 0)
        - c * (pi_dist x * L x v) + c * c * (pi_dist x * ∑ y, L x y) := by
    intro x; split_ifs <;> ring
  simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq'
    Finset.univ v, if_pos (Finset.mem_univ v), ← Finset.mul_sum, h_stat v]
  -- Σ_x π_x Σ_y L_{x y} = Σ_y (Σ_x π_x L_{x y}) = 0
  have hrows : ∑ x, pi_dist x * ∑ y, L x y = 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp [h_stat]
  rw [hrows]
  simp only [mul_zero, sub_zero, add_zero]
  -- remaining: π_v (L_{v v} − c Σ_y L_{v y}) ≤ 0
  have hdiag := pi_mul_diag_nonpos L pi_dist hπ hL_gen h_stat v
  have hoff : 0 ≤ ∑ y ∈ Finset.univ.erase v, L v y :=
    Finset.sum_nonneg fun y hy => hL_gen v y (Finset.ne_of_mem_erase hy).symm
  have hrow : ∑ y, L v y = L v v + ∑ y ∈ Finset.univ.erase v, L v y :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ v)).symm
  rw [hrow]
  have hπv := hπ v
  nlinarith [mul_nonneg hπv.le hoff, mul_nonneg hc0 (mul_nonneg hπv.le hoff)]

/-- **The Dirichlet gap of a stationary generator is nonpositive.** The Rayleigh set either
contains the nonpositive quotient of the test vector (when `V` has two points) or is empty
(`sInf ∅ = 0`). Either way `DirichletGap L π ≤ 0`. -/
theorem dirichletGap_nonpos_of_stationary (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ x, 0 < pi_dist x)
    (hL_gen : ∀ x y, x ≠ y → 0 ≤ L x y)
    (h_stat : ∀ v, ∑ u, pi_dist u * L u v = 0) :
    DirichletGap L pi_dist ≤ 0 := by
  unfold DirichletGap
  by_cases hV : ∃ v w : V, v ≠ w
  · obtain ⟨v, w, hvw⟩ := hV
    set S : ℝ := ∑ x, pi_dist x with hS
    have hSpos : 0 < S := Finset.sum_pos (fun x _ => hπ x) ⟨v, Finset.mem_univ v⟩
    set c : ℝ := pi_dist v / S with hc
    have hc0 : 0 ≤ c := div_nonneg (hπ v).le hSpos.le
    have hc1 : c ≤ 1 := by
      rw [hc, div_le_one hSpos]
      exact Finset.single_le_sum (fun x _ => (hπ x).le) (Finset.mem_univ v)
    set u : V → ℝ := fun x => (if x = v then (1 : ℝ) else 0) - c with hu
    have hu_ne : u ≠ 0 := by
      intro h0
      have := congr_fun h0 w
      simp only [hu, Pi.zero_apply, if_neg (Ne.symm hvw), zero_sub, neg_eq_zero] at this
      have : 0 < c := div_pos (hπ v) hSpos
      linarith
    have hu_orth : inner_pi pi_dist u constant_vec_one = 0 := by
      unfold inner_pi constant_vec_one
      simp only [mul_one, hu]
      have : ∀ x, pi_dist x * ((if x = v then (1:ℝ) else 0) - c) =
          (if x = v then pi_dist x else 0) - c * pi_dist x := by
        intro x; split_ifs <;> ring
      simp_rw [this, Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ v,
        if_pos (Finset.mem_univ v), ← Finset.mul_sum, ← hS, hc]
      field_simp
      ring
    have hR_nonpos : RayleighQuotient L pi_dist u ≤ 0 := by
      unfold RayleighQuotient
      rw [dirichlet_form_eq]
      have hnum := dirichletForm_test_nonpos L pi_dist hπ hL_gen h_stat v c hc0 hc1
      have hden : 0 ≤ inner_pi pi_dist u u := by
        unfold inner_pi
        exact Finset.sum_nonneg fun x _ => by
          have := hπ x
          nlinarith [sq_nonneg (u x)]
      exact div_nonpos_of_nonpos_of_nonneg hnum hden
    have hmem : RayleighQuotient L pi_dist u ∈ RayleighSet L pi_dist :=
      ⟨u, hu_ne, hu_orth, rfl⟩
    by_cases hbdd : BddBelow (RayleighSet L pi_dist)
    · exact le_trans (csInf_le hbdd hmem) hR_nonpos
    · rw [Real.sInf_of_not_bddBelow hbdd]
  · -- at most one point: no nonzero vector is orthogonal to the constants
    push_neg at hV
    have hempty : RayleighSet L pi_dist = ∅ := by
      ext r
      simp only [RayleighSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨u, hu_ne, hu_orth, _⟩
      apply hu_ne
      funext x
      have hx : ∀ y, u y = u x := fun y => by rw [hV y x]
      unfold inner_pi constant_vec_one at hu_orth
      simp only [mul_one] at hu_orth
      have : (∑ y, pi_dist y) * u x = 0 := by
        rw [Finset.sum_mul]; rw [← hu_orth]
        exact Finset.sum_congr rfl fun y _ => by rw [hx y]
      have hSpos : 0 < ∑ y, pi_dist y := Finset.sum_pos (fun y _ => hπ y) ⟨x, Finset.mem_univ x⟩
      simpa [hSpos.ne'] using this
    rw [hempty, Real.sInf_empty]

end SGC
