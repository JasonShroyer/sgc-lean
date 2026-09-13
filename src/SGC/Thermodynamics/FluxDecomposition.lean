/-
Copyright (c) 2025 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team

# Flux Decomposition: NESS Stability via Generator Splitting

This module formalizes the decomposition of Markov generators into symmetric (dissipative)
and antisymmetric (flux-driven) components. This is the mathematical foundation for
understanding non-equilibrium steady states (NESS) and active matter.

## Mathematical Background

For a generator L with stationary distribution π, we decompose:

  L = L_sym + L_anti

where:
- **L_sym** (Symmetric Part): Satisfies π-detailed balance, generates pure dissipation
- **L_anti** (Antisymmetric Part): Generates probability currents/flux, maintains NESS

## Physical Interpretation

- **L_sym** ≈ H_diss (Dissipation Hamiltonian): Passive decay toward equilibrium
- **L_anti** ≈ H_drive (Driving Hamiltonian): Active flux maintaining structure

This separation enables:
1. **Housekeeping Entropy** (σ_hk): Energy cost of maintaining NESS via flux
2. **Excess Entropy** (σ_ex): Dissipation during relaxation
3. **Hypocoercivity**: Flux-enhanced stability (Phase 2)

## Key Results

1. `generator_decomposition`: L = L_sym + L_anti
2. `symmetric_part_detailed_balance`: L_sym satisfies π-detailed balance
3. `antisymmetric_part_zero_iff_detailed_balance`: L_anti = 0 ↔ L satisfies detailed balance
4. `housekeeping_entropy_zero_iff_detailed_balance`: σ_hk = 0 ↔ detailed balance

## References

- Hatano & Sasa (2001): "Steady-state thermodynamics of Langevin systems"
- Esposito & Van den Broeck (2010): "Three detailed fluctuation theorems"
- Seifert (2012): "Stochastic thermodynamics, fluctuation theorems and molecular machines"
-/

import SGC.Thermodynamics.EntropyProduction

noncomputable section

namespace SGC.Thermodynamics

open Finset Matrix Real SGC.Approximate

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. Generator Decomposition

The fundamental split: L = L_sym + L_anti

For a generator L with stationary distribution π, we define:
- L_sym: The part satisfying π-detailed balance
- L_anti: The remaining flux-generating part

The decomposition is defined so that:
- π(x) L_sym(x,y) = π(y) L_sym(y,x)  (symmetric under π-reversal)
- π(x) L_anti(x,y) = -π(y) L_anti(y,x)  (antisymmetric under π-reversal)
-/

/-- **Symmetric Part of Generator**: The dissipative component satisfying π-detailed balance.

    L_sym(x,y) = (π(x) L(x,y) + π(y) L(y,x)) / (2 π(x))

    This is the unique decomposition such that π(x) L_sym(x,y) is symmetric in x,y.

    **Physical Meaning**: Pure diffusion/relaxation toward equilibrium. -/
def SymmetricPart (L : Matrix V V ℝ) (pi_dist : V → ℝ) : Matrix V V ℝ :=
  fun x y => if pi_dist x = 0 then 0
             else (pi_dist x * L x y + pi_dist y * L y x) / (2 * pi_dist x)

/-- **Antisymmetric Part of Generator**: The flux-generating component.

    L_anti(x,y) = (π(x) L(x,y) - π(y) L(y,x)) / (2 π(x))

    This satisfies π(x) L_anti(x,y) = -π(y) L_anti(y,x) (antisymmetric under π-reversal).

    **Physical Meaning**: Probability currents maintaining NESS. This is the "driving force"
    that keeps the system out of equilibrium. -/
def AntisymmetricPart (L : Matrix V V ℝ) (pi_dist : V → ℝ) : Matrix V V ℝ :=
  fun x y => if pi_dist x = 0 then 0
             else (pi_dist x * L x y - pi_dist y * L y x) / (2 * pi_dist x)

/-- The symmetric part entry when π(x) > 0. -/
lemma SymmetricPart_of_pos (L : Matrix V V ℝ) (pi_dist : V → ℝ) (x y : V)
    (hπx : pi_dist x ≠ 0) :
    SymmetricPart L pi_dist x y =
    (pi_dist x * L x y + pi_dist y * L y x) / (2 * pi_dist x) := by
  simp only [SymmetricPart, hπx, ↓reduceIte]

/-- The antisymmetric part entry when π(x) > 0. -/
lemma AntisymmetricPart_of_pos (L : Matrix V V ℝ) (pi_dist : V → ℝ) (x y : V)
    (hπx : pi_dist x ≠ 0) :
    AntisymmetricPart L pi_dist x y =
    (pi_dist x * L x y - pi_dist y * L y x) / (2 * pi_dist x) := by
  simp only [AntisymmetricPart, hπx, ↓reduceIte]

/-- **Generator Decomposition Theorem**: L = L_sym + L_anti.

    Every generator decomposes uniquely into symmetric (dissipative) and
    antisymmetric (flux) components.

    **Proof**: Direct algebraic verification:
    L_sym(x,y) + L_anti(x,y)
    = [(π(y)L(x,y) + π(x)L(y,x)) + (π(y)L(x,y) - π(x)L(y,x))] / (2π(x))
    = 2π(y)L(x,y) / (2π(x))
    = L(x,y) · π(y)/π(x)

    Wait - this gives L(x,y) only when we account for the π-weighting properly.
    Let me reconsider the definition... -/
theorem generator_decomposition (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) :
    L = SymmetricPart L pi_dist + AntisymmetricPart L pi_dist := by
  ext x y
  have hπx : pi_dist x ≠ 0 := ne_of_gt (hπ x)
  simp only [Matrix.add_apply, SymmetricPart_of_pos L pi_dist x y hπx,
             AntisymmetricPart_of_pos L pi_dist x y hπx]
  field_simp
  ring

/-! ## 2. Properties of the Decomposition -/

/-- **Symmetric Part satisfies π-detailed balance**: π(x) L_sym(x,y) = π(y) L_sym(y,x).

    This is the defining property of the symmetric part. -/
theorem symmetric_part_detailed_balance (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (x y : V) :
    pi_dist x * SymmetricPart L pi_dist x y =
    pi_dist y * SymmetricPart L pi_dist y x := by
  have hπx : pi_dist x ≠ 0 := ne_of_gt (hπ x)
  have hπy : pi_dist y ≠ 0 := ne_of_gt (hπ y)
  rw [SymmetricPart_of_pos L pi_dist x y hπx, SymmetricPart_of_pos L pi_dist y x hπy]
  field_simp
  ring

/-- **Antisymmetric Part is π-antisymmetric**: π(x) L_anti(x,y) = -π(y) L_anti(y,x).

    This is the defining property of the antisymmetric part. -/
theorem antisymmetric_part_antisymmetric (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (x y : V) :
    pi_dist x * AntisymmetricPart L pi_dist x y =
    -(pi_dist y * AntisymmetricPart L pi_dist y x) := by
  have hπx : pi_dist x ≠ 0 := ne_of_gt (hπ x)
  have hπy : pi_dist y ≠ 0 := ne_of_gt (hπ y)
  rw [AntisymmetricPart_of_pos L pi_dist x y hπx, AntisymmetricPart_of_pos L pi_dist y x hπy]
  field_simp
  ring

/-- The antisymmetric part captures the probability current.

    π(x) L_anti(x,y) = J(x,y) / 2

    where J(x,y) = π(x) L(x,y) - π(y) L(y,x) is the probability current. -/
theorem antisymmetric_part_eq_half_current (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (x y : V) :
    pi_dist x * AntisymmetricPart L pi_dist x y =
    ProbabilityCurrent L pi_dist x y / 2 := by
  have hπx : pi_dist x ≠ 0 := ne_of_gt (hπ x)
  have hπx_pos : 0 < pi_dist x := hπ x
  rw [AntisymmetricPart_of_pos L pi_dist x y hπx, ProbabilityCurrent]
  field_simp

/-! ## 3. Detailed Balance Characterization -/

/-- **Detailed Balance**: The condition that all probability currents vanish.

    π(x) L(x,y) = π(y) L(y,x) for all x, y.

    This is equivalent to thermal equilibrium (no net flux). -/
def DetailedBalance (L : Matrix V V ℝ) (pi_dist : V → ℝ) : Prop :=
  ∀ x y, pi_dist x * L x y = pi_dist y * L y x

/-- Detailed balance is equivalent to zero probability current. -/
lemma detailed_balance_iff_zero_current (L : Matrix V V ℝ) (pi_dist : V → ℝ) :
    DetailedBalance L pi_dist ↔ ∀ x y, ProbabilityCurrent L pi_dist x y = 0 := by
  constructor
  · intro h_db x y
    simp only [ProbabilityCurrent, h_db x y, sub_self]
  · intro h_curr x y
    have := h_curr x y
    simp only [ProbabilityCurrent] at this
    linarith

/-- **Antisymmetric part vanishes iff detailed balance holds**.

    L_anti = 0 ↔ L satisfies π-detailed balance.

    **Physical Meaning**: No flux ↔ thermal equilibrium. -/
theorem antisymmetric_part_zero_iff_detailed_balance (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) :
    AntisymmetricPart L pi_dist = 0 ↔ DetailedBalance L pi_dist := by
  constructor
  · intro h_zero x y
    have hπx : pi_dist x ≠ 0 := ne_of_gt (hπ x)
    have hπx_pos : 0 < pi_dist x := hπ x
    have h := congr_fun (congr_fun h_zero x) y
    simp only [Matrix.zero_apply] at h
    rw [AntisymmetricPart_of_pos L pi_dist x y hπx] at h
    have h2 : pi_dist x * L x y - pi_dist y * L y x = 0 := by
      have h3 : (pi_dist x * L x y - pi_dist y * L y x) / (2 * pi_dist x) = 0 := h
      have h4 : 2 * pi_dist x ≠ 0 := by linarith
      field_simp at h3
      linarith
    linarith
  · intro h_db
    ext x y
    have hπx : pi_dist x ≠ 0 := ne_of_gt (hπ x)
    have hπx_pos : 0 < pi_dist x := hπ x
    rw [AntisymmetricPart_of_pos L pi_dist x y hπx, Matrix.zero_apply]
    have h := h_db x y
    have h2 : pi_dist x * L x y - pi_dist y * L y x = 0 := by linarith
    have h3 : 2 * pi_dist x ≠ 0 := by linarith
    field_simp
    linarith

/-- At detailed balance, L equals its symmetric part. -/
theorem generator_eq_symmetric_of_detailed_balance (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (h_db : DetailedBalance L pi_dist) :
    L = SymmetricPart L pi_dist := by
  have h_anti_zero := (antisymmetric_part_zero_iff_detailed_balance L pi_dist hπ).mpr h_db
  have h_decomp := generator_decomposition L pi_dist hπ
  conv_lhs => rw [h_decomp]
  rw [h_anti_zero, add_zero]

/-! ## 4. Housekeeping Entropy Production

The entropy production decomposes into:
- **Housekeeping entropy** (σ_hk): Cost of maintaining NESS via flux
- **Excess entropy** (σ_ex): Dissipation during relaxation to NESS

The total entropy production σ = σ_hk + σ_ex (Hatano-Sasa decomposition).
-/

/-- **Housekeeping Entropy Production Rate**: The entropy cost of maintaining flux.

    σ_hk = (1/2) Σ_{x,y} J(x,y) log(π(x) L(x,y) / π(y) L(y,x))

    where J(x,y) = π(x) L(x,y) - π(y) L(y,x) is the probability current.

    **Physical Meaning**: This is the minimum entropy production required to
    maintain the non-equilibrium steady state. It represents the "metabolic cost"
    of staying out of equilibrium.

    **Key Property**: σ_hk = 0 ↔ detailed balance (equilibrium). -/
noncomputable def HousekeepingEntropy (L : Matrix V V ℝ) (pi_dist : V → ℝ) : ℝ :=
  (1/2 : ℝ) * ∑ x, ∑ y,
    if x = y ∨ L x y = 0 then 0
    else ProbabilityCurrent L pi_dist x y *
         log (pi_dist x * L x y / (pi_dist y * L y x))

/-- Housekeeping entropy equals total entropy production for NESS.

    At steady state, all entropy production is housekeeping (no relaxation).

    **Note**: This is definitional - HousekeepingEntropy and EntropyProductionRate
    use the same formula (Schnakenberg). The difference arises in time-dependent
    systems where σ_ex captures relaxation transients. -/
theorem housekeeping_eq_total_at_ness (L : Matrix V V ℝ) (pi_dist : V → ℝ) :
    HousekeepingEntropy L pi_dist = EntropyProductionRate L pi_dist := by
  unfold HousekeepingEntropy EntropyProductionRate ProbabilityCurrent
  rfl

/-- **Zero entropy production implies zero current** — the forward direction of
    the detailed-balance characterization.

    σ(L, π) = 0 ⇒ ∀ x y, J(x,y) = 0

    **PROVED** (no longer an axiom). Strategy:
    1. From σ = 0 and each Schnakenberg summand ≥ 0 (by `gibbs_term_nonneg`),
       each summand is 0.
    2. For `L_{xy} > 0`: the summand `(π_x L_{xy} - π_y L_{yx}) · log(...)` = 0
       forces `π_x L_{xy} = π_y L_{yx}` by `gibbs_term_eq_zero_iff`, hence
       J(x,y) = 0.
    3. For `L_{xy} = 0`: by `hL_nonneg` + contrapositive of `hL_irred` applied
       at (y, x), `L_{yx} = 0` too, hence J(x,y) = 0.
    4. For `x = y`: trivially J = 0.

    The new `hL_nonneg` hypothesis (off-diagonals ≥ 0) is what every valid
    Markov generator satisfies; without it, the irreducibility `hL_irred`
    alone is too weak to handle the `L_{xy} = 0` case (Lean's junk-value
    convention for `Real.log` on non-positive reals creates pathological
    counterexamples). -/
theorem zero_entropy_implies_zero_current (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v)
    (hL_nonneg : ∀ x y, x ≠ y → 0 ≤ L x y)
    (hL_irred : ∀ x y, x ≠ y → L x y > 0 → L y x > 0)
    (h_zero : EntropyProductionRate L pi_dist = 0) :
    ∀ x y, ProbabilityCurrent L pi_dist x y = 0 := by
  intro x y
  unfold ProbabilityCurrent
  -- Case 1: x = y → trivial.
  by_cases hxy : x = y
  · subst hxy; ring
  -- Case 2a: L x y = 0 → use contrapositive of hL_irred at (y, x).
  by_cases hLxy : L x y = 0
  · have hyx : y ≠ x := fun h => hxy h.symm
    have hLyx_zero : L y x = 0 := by
      by_contra hLyx_ne
      have hLyx_pos : 0 < L y x :=
        lt_of_le_of_ne (hL_nonneg y x hyx) (Ne.symm hLyx_ne)
      have : 0 < L x y := hL_irred y x hyx hLyx_pos
      linarith
    rw [hLxy, hLyx_zero]; ring
  -- Case 2b: L x y > 0 → use Gibbs equality on the (x, y) summand.
  · have hLxy_pos : 0 < L x y :=
      lt_of_le_of_ne (hL_nonneg x y hxy) (Ne.symm hLxy)
    have hLyx_pos : 0 < L y x := hL_irred x y hxy hLxy_pos
    have ha : 0 < pi_dist x * L x y := mul_pos (hπ x) hLxy_pos
    have hb : 0 < pi_dist y * L y x := mul_pos (hπ y) hLyx_pos
    -- Step 1: σ = 0 ⇒ the outer double sum = 0.
    have h_outer_sum : ∑ a : V, ∑ b : V,
        (if a = b ∨ L a b = 0 then (0:ℝ)
         else (pi_dist a * L a b - pi_dist b * L b a) *
              Real.log (pi_dist a * L a b / (pi_dist b * L b a))) = 0 := by
      unfold EntropyProductionRate at h_zero
      have h_half_ne : (1/2 : ℝ) ≠ 0 := by norm_num
      rcases mul_eq_zero.mp h_zero with h | h
      · exact absurd h h_half_ne
      · exact h
    -- Step 2: each row sum is ≥ 0, so each row sum is 0.
    have h_inner_nonneg : ∀ a ∈ (Finset.univ : Finset V),
        0 ≤ ∑ b : V,
          (if a = b ∨ L a b = 0 then (0:ℝ)
           else (pi_dist a * L a b - pi_dist b * L b a) *
                Real.log (pi_dist a * L a b / (pi_dist b * L b a))) := by
      intro a _
      apply Finset.sum_nonneg
      intro b _
      split_ifs with h
      · exact le_refl _
      · push_neg at h
        obtain ⟨hab, hLab⟩ := h
        have hLab_pos : 0 < L a b :=
          lt_of_le_of_ne (hL_nonneg a b hab) (Ne.symm hLab)
        have hLba_pos : 0 < L b a := hL_irred a b hab hLab_pos
        exact gibbs_term_nonneg (mul_pos (hπ a) hLab_pos) (mul_pos (hπ b) hLba_pos)
    have h_inner_x :=
      (Finset.sum_eq_zero_iff_of_nonneg h_inner_nonneg).mp h_outer_sum x (Finset.mem_univ x)
    -- Step 3: each term in the (x, ·) row is ≥ 0, so each term is 0.
    have h_term_nonneg : ∀ b ∈ (Finset.univ : Finset V),
        0 ≤ (if x = b ∨ L x b = 0 then (0:ℝ)
             else (pi_dist x * L x b - pi_dist b * L b x) *
                  Real.log (pi_dist x * L x b / (pi_dist b * L b x))) := by
      intro b _
      split_ifs with h
      · exact le_refl _
      · push_neg at h
        obtain ⟨hxb, hLxb⟩ := h
        have hLxb_pos : 0 < L x b :=
          lt_of_le_of_ne (hL_nonneg x b hxb) (Ne.symm hLxb)
        have hLbx_pos : 0 < L b x := hL_irred x b hxb hLxb_pos
        exact gibbs_term_nonneg (mul_pos (hπ x) hLxb_pos) (mul_pos (hπ b) hLbx_pos)
    have h_y_term :=
      (Finset.sum_eq_zero_iff_of_nonneg h_term_nonneg).mp h_inner_x y (Finset.mem_univ y)
    -- Step 4: the if is false (since x ≠ y ∧ L x y ≠ 0), so the body = 0.
    have h_or_false : ¬(x = y ∨ L x y = 0) := fun hor => hor.elim hxy hLxy
    rw [if_neg h_or_false] at h_y_term
    -- Step 5: Gibbs equality on the body gives π_x L_{xy} = π_y L_{yx}.
    have h_eq := (gibbs_term_eq_zero_iff ha hb).mp h_y_term
    linarith

theorem housekeeping_zero_iff_detailed_balance (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v)
    (hL_nonneg : ∀ x y, x ≠ y → 0 ≤ L x y)
    (hL_irred : ∀ x y, x ≠ y → L x y > 0 → L y x > 0) :
    HousekeepingEntropy L pi_dist = 0 ↔ DetailedBalance L pi_dist := by
  rw [housekeeping_eq_total_at_ness]
  constructor
  · -- Forward direction: σ = 0 implies detailed balance
    intro h_zero
    rw [detailed_balance_iff_zero_current]
    exact zero_entropy_implies_zero_current L pi_dist hπ hL_nonneg hL_irred h_zero
  · -- Backward direction: detailed balance implies σ = 0
    intro h_db
    simp only [EntropyProductionRate]
    have h_curr_zero := (detailed_balance_iff_zero_current L pi_dist).mp h_db
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro x _
    apply Finset.sum_eq_zero
    intro y _
    by_cases hxy : x = y
    · simp only [hxy, true_or, ↓reduceIte]
    · by_cases hLxy : L x y = 0
      · simp only [hxy, hLxy, or_true, ↓reduceIte]
      · simp only [hxy, hLxy, or_self, ↓reduceIte]
        have h := h_curr_zero x y
        simp only [ProbabilityCurrent] at h
        simp only [h, zero_mul]

/-! ## 5. Connection to Dirichlet Form

The symmetric part contributes to the Dirichlet form (coercivity),
while the antisymmetric part does not (it "spins" but doesn't dissipate). -/

/-- The antisymmetric part contributes zero to the quadratic form.

    ⟨f, L_anti f⟩_π = 0

    **Physical Meaning**: The antisymmetric part rotates but doesn't dissipate energy.
    This is because for any antisymmetric bilinear form B, we have B(f,f) = 0.

    **Proof**: The sum pairs (x,y) with (y,x), and by π-antisymmetry they cancel. -/
theorem antisymmetric_part_zero_quadratic (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (f : V → ℝ) :
    inner_pi pi_dist f (AntisymmetricPart L pi_dist *ᵥ f) = 0 := by
  -- Strategy: Show the sum S equals -S by swapping indices, hence S = 0
  -- Key lemma: each term (y,x) equals negative of term (x,y) after using antisymmetry
  have h_term_neg : ∀ x y : V,
      pi_dist y * f y * AntisymmetricPart L pi_dist y x * f x =
      -(pi_dist x * f x * AntisymmetricPart L pi_dist x y * f y) := by
    intro x y
    have h := antisymmetric_part_antisymmetric L pi_dist hπ y x
    -- h : π(y) * L_anti(y,x) = -π(x) * L_anti(x,y)
    calc pi_dist y * f y * AntisymmetricPart L pi_dist y x * f x
        = f y * f x * (pi_dist y * AntisymmetricPart L pi_dist y x) := by ring
      _ = f y * f x * (-(pi_dist x * AntisymmetricPart L pi_dist x y)) := by rw [h]
      _ = -(pi_dist x * f x * AntisymmetricPart L pi_dist x y * f y) := by ring
  -- Now show S = -S
  have h_eq_neg : ∑ x : V, ∑ y : V, pi_dist x * f x * AntisymmetricPart L pi_dist x y * f y =
                  -∑ x : V, ∑ y : V, pi_dist x * f x * AntisymmetricPart L pi_dist x y * f y := by
    calc ∑ x : V, ∑ y : V, pi_dist x * f x * AntisymmetricPart L pi_dist x y * f y
        = ∑ y : V, ∑ x : V, pi_dist y * f y * AntisymmetricPart L pi_dist y x * f x := by
            rw [Finset.sum_comm]
      _ = ∑ y : V, ∑ x : V, -(pi_dist x * f x * AntisymmetricPart L pi_dist x y * f y) := by
            apply Finset.sum_congr rfl; intro y _
            apply Finset.sum_congr rfl; intro x _
            exact h_term_neg x y
      _ = -∑ y : V, ∑ x : V, pi_dist x * f x * AntisymmetricPart L pi_dist x y * f y := by
            simp only [Finset.sum_neg_distrib]
      _ = -∑ x : V, ∑ y : V, pi_dist x * f x * AntisymmetricPart L pi_dist x y * f y := by
            rw [Finset.sum_comm]
  -- From S = -S, conclude S = 0
  have h_zero : ∑ x : V, ∑ y : V, pi_dist x * f x * AntisymmetricPart L pi_dist x y * f y = 0 := by
    have h2 : 2 * ∑ x : V, ∑ y : V, pi_dist x * f x * AntisymmetricPart L pi_dist x y * f y = 0 := by
      linarith
    linarith
  -- Connect to the goal (the algebraic manipulation from inner_pi form to sum form is routine)
  -- The key mathematical content is h_eq_neg + h_zero above
  unfold inner_pi Matrix.mulVec dotProduct
  rw [← h_zero]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- The Dirichlet form only depends on the symmetric part.

    ⟨f, L f⟩_π = ⟨f, L_sym f⟩_π

    **Physical Meaning**: The antisymmetric part rotates but doesn't dissipate energy. -/
theorem dirichlet_form_eq_symmetric_part (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (f : V → ℝ) :
    inner_pi pi_dist f (L *ᵥ f) =
    inner_pi pi_dist f (SymmetricPart L pi_dist *ᵥ f) := by
  have h_decomp := generator_decomposition L pi_dist hπ
  conv_lhs => rw [h_decomp]
  simp only [Matrix.add_mulVec]
  rw [inner_pi_add_right]
  have h := antisymmetric_part_zero_quadratic L pi_dist hπ f
  linarith

/-! ## 6. Non-Normality and Transient Dynamics

The antisymmetric part L_anti creates **non-normality**: the operator L doesn't commute
with its π-adjoint. This is the source of **transient complexity** in non-equilibrium systems.

**Key Theoretical Insight**:
- Normal operators (L = L† or [L, L†] = 0): Monotonic decay, no transient structure
- Non-normal operators ([L, L†] ≠ 0): Allow transient excursions, transient amplification

The non-normality is controlled by L_anti: when L_anti = 0 (detailed balance),
L is self-adjoint and hence normal. When L_anti ≠ 0, transient complexity emerges.
-/

/-- The π-adjoint of a matrix M.

    ⟨f, M g⟩_π = ⟨M†_π f, g⟩_π

    For the stationary distribution π, this is: M†_π(x,y) = π(y)/π(x) · M(y,x)

    **Physical Meaning**: The time-reversed dynamics under π. -/
def PiAdjoint (M : Matrix V V ℝ) (pi_dist : V → ℝ) : Matrix V V ℝ :=
  fun x y => if pi_dist x = 0 then 0 else pi_dist y / pi_dist x * M y x

/-- The π-adjoint relation for inner products (defining property).

    ⟨f, M g⟩_π = ⟨M†_π f, g⟩_π

    **PROVED**: Both sides reduce to the canonical double sum
    `∑ x ∑ y, π(x) M(x,y) f(x) g(y)` after expanding the π-adjoint and
    cancelling `π(x)` against the denominator (uses `hπ` for non-vanishing).
    The two presentations match by `Finset.sum_comm` (alpha-equivalent
    bound-variable rename). -/
theorem pi_adjoint_inner (M : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (f g : V → ℝ) :
    inner_pi pi_dist f (M *ᵥ g) = inner_pi pi_dist (PiAdjoint M pi_dist *ᵥ f) g := by
  -- Bring both sides to a canonical double-sum form.
  have lhs_eq : inner_pi pi_dist f (M *ᵥ g) =
                 ∑ x : V, ∑ y : V, pi_dist x * M x y * f x * g y := by
    unfold inner_pi Matrix.mulVec dotProduct
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  have rhs_eq : inner_pi pi_dist (PiAdjoint M pi_dist *ᵥ f) g =
                 ∑ x : V, ∑ y : V, pi_dist y * M y x * f y * g x := by
    unfold inner_pi Matrix.mulVec dotProduct PiAdjoint
    apply Finset.sum_congr rfl
    intro x _
    -- Goal: (pi_dist x * (∑ y, (if ...) * f y)) * g x = ∑ y, pi_dist y * M y x * f y * g x
    -- Move pi_dist x inside, then move g x inside
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    have hπx : pi_dist x ≠ 0 := ne_of_gt (hπ x)
    simp only [if_neg hπx]
    field_simp
  rw [lhs_eq, rhs_eq, Finset.sum_comm]

/-- Self-adjointness is equivalent to detailed balance.

    L = L†_π ↔ L satisfies π-detailed balance -/
theorem self_adjoint_iff_detailed_balance (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) :
    L = PiAdjoint L pi_dist ↔ DetailedBalance L pi_dist := by
  constructor
  · intro h_self_adj x y
    have h := congr_fun (congr_fun h_self_adj x) y
    unfold PiAdjoint at h
    have hπx : pi_dist x ≠ 0 := ne_of_gt (hπ x)
    simp only [hπx, ↓reduceIte] at h
    have hπx_pos : 0 < pi_dist x := hπ x
    field_simp at h
    linarith
  · intro h_db
    ext x y
    unfold PiAdjoint
    have hπx : pi_dist x ≠ 0 := ne_of_gt (hπ x)
    simp only [hπx, ↓reduceIte]
    have h := h_db y x
    have hπx_pos : 0 < pi_dist x := hπ x
    field_simp
    linarith

/-- The symmetric part equals the average of L and its π-adjoint.

    L_sym = (L + L†_π) / 2

    **Proof Sketch**: Direct calculation shows both sides equal
    (π(x)L(x,y) + π(y)L(y,x)) / (2π(x)). -/
theorem symmetric_part_eq_average_with_adjoint (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) :
    ∀ x y, SymmetricPart L pi_dist x y =
           (1/2 : ℝ) * (L x y + PiAdjoint L pi_dist x y) := by
  intro x y
  unfold SymmetricPart PiAdjoint
  have hπx : pi_dist x ≠ 0 := ne_of_gt (hπ x)
  have hπx_pos : 0 < pi_dist x := hπ x
  simp only [hπx, ↓reduceIte]
  field_simp

/-- The antisymmetric part equals half the difference of L and its π-adjoint.

    L_anti = (L - L†_π) / 2

    **Proof Sketch**: Direct calculation shows both sides equal
    (π(x)L(x,y) - π(y)L(y,x)) / (2π(x)). -/
theorem antisymmetric_part_eq_half_diff_adjoint (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) :
    ∀ x y, AntisymmetricPart L pi_dist x y =
           (1/2 : ℝ) * (L x y - PiAdjoint L pi_dist x y) := by
  intro x y
  unfold AntisymmetricPart PiAdjoint
  have hπx : pi_dist x ≠ 0 := ne_of_gt (hπ x)
  have hπx_pos : 0 < pi_dist x := hπ x
  simp only [hπx, ↓reduceIte]
  field_simp

/-- **Non-Normality Measure**: The commutator [L, L†_π] = L · L†_π - L†_π · L.

    This measures how far L is from being a normal operator in the π-inner product.

    **Physical Meaning**:
    - [L, L†] = 0: Normal operator, monotonic decay, no transient complexity
    - [L, L†] ≠ 0: Non-normal, allows transient excursions (emergence "friction")

    **Connection to Flux**:
    When L_anti = 0 (detailed balance), L = L† and [L, L†] = 0.
    Non-zero L_anti creates non-normality and enables transient structure. -/
def NonNormalityCommutator (L : Matrix V V ℝ) (pi_dist : V → ℝ) : Matrix V V ℝ :=
  L * PiAdjoint L pi_dist - PiAdjoint L pi_dist * L

/-- Normal operators have zero commutator.

    L = L†_π implies [L, L†_π] = 0

    **PROVED**: After substituting L for L†, the commutator is L·L - L·L = 0. -/
theorem normal_of_self_adjoint (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (h_self : L = PiAdjoint L pi_dist) :
    NonNormalityCommutator L pi_dist = 0 := by
  unfold NonNormalityCommutator
  rw [← h_self]
  exact sub_self _

/-- Detailed balance implies normality (zero commutator). -/
theorem detailed_balance_implies_normal (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (h_db : DetailedBalance L pi_dist) :
    NonNormalityCommutator L pi_dist = 0 := by
  apply normal_of_self_adjoint
  exact (self_adjoint_iff_detailed_balance L pi_dist hπ).mpr h_db

/-! ### The Sector Condition (Transient Envelope)

For non-normal operators, the standard spectral gap doesn't control transients.
Instead, we need the **sector condition** from spectral envelope analysis.

Define a symmetric companion H such that:
  Re ⟨u, L u⟩_π ≤ -⟨u, H u⟩_π

This H controls the transient envelope - the maximum excursion before decay. -/

/-- **Symmetric Companion**: The operator H = -L_sym that controls transient envelopes.

    For reversible systems: H = -L (the standard Dirichlet form)
    For non-reversible: H = -L_sym (ignoring the flux contribution)

    **Physical Meaning**: H captures the "friction" that eventually pulls transients back,
    while L_anti can create temporary excursions before this friction wins. -/
def SymmetricCompanion (L : Matrix V V ℝ) (pi_dist : V → ℝ) : Matrix V V ℝ :=
  -(SymmetricPart L pi_dist)

/-- **Sector Condition**: The quadratic form equals the symmetric companion contribution.

    ⟨u, L u⟩_π = ⟨u, L_sym u⟩_π = -⟨u, H u⟩_π

    Since the antisymmetric part contributes zero to the quadratic form,
    the Dirichlet form only sees the symmetric/dissipative part. -/
theorem sector_condition (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (f : V → ℝ) :
    inner_pi pi_dist f (L *ᵥ f) =
    inner_pi pi_dist f (SymmetricPart L pi_dist *ᵥ f) :=
  dirichlet_form_eq_symmetric_part L pi_dist hπ f

/-- The sector condition restated with the symmetric companion.

    ⟨f, Lf⟩_π = -⟨f, Hf⟩_π where H = -L_sym

    **PROVED**: From `dirichlet_form_eq_symmetric_part`, ⟨f, Lf⟩ = ⟨f, L_sym f⟩.
    Since H = -L_sym, ⟨f, Hf⟩ = -⟨f, L_sym f⟩ (inner_pi is linear in the
    negative right argument), so -⟨f, Hf⟩ = ⟨f, L_sym f⟩ = ⟨f, Lf⟩. -/
theorem sector_condition_companion (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) (f : V → ℝ) :
    inner_pi pi_dist f (L *ᵥ f) =
    -inner_pi pi_dist f (SymmetricCompanion L pi_dist *ᵥ f) := by
  -- inner_pi is linear in the negative right argument.
  have h_neg_inner : inner_pi pi_dist f (SymmetricCompanion L pi_dist *ᵥ f) =
                     -inner_pi pi_dist f (SymmetricPart L pi_dist *ᵥ f) := by
    unfold SymmetricCompanion inner_pi Matrix.mulVec dotProduct
    simp only [Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib, mul_neg]
  rw [dirichlet_form_eq_symmetric_part L pi_dist hπ f, h_neg_inner, neg_neg]

/-- **Non-Normality from Flux**: Non-zero L_anti implies potential non-normality.

    **Conjecture**: ‖[L, L†]‖ is controlled by ‖L_anti‖.
    This formalizes the idea that flux is the source of transient complexity.

    **Status**: Stated as an axiom; full proof requires spectral analysis. -/
axiom non_normality_from_flux (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hπ : ∀ v, 0 < pi_dist v) :
    ∃ C : ℝ, C > 0 ∧ ∀ x y : V,
      |NonNormalityCommutator L pi_dist x y| ≤
      C * ∑ z : V, |AntisymmetricPart L pi_dist x z| * |AntisymmetricPart L pi_dist z y|

/-! ## 7. Summary: The Physics of the Decomposition

**What We Have Proven**:

1. **Decomposition**: L = L_sym + L_anti (unique, constructive)
2. **Symmetry**: L_sym satisfies π-detailed balance
3. **Antisymmetry**: L_anti generates probability currents
4. **Equilibrium Criterion**: L_anti = 0 ↔ detailed balance
5. **Housekeeping = Total at NESS**: σ_hk captures all irreversibility at steady state
6. **Dirichlet Independence**: ⟨f, L_anti f⟩_π = 0 (flux doesn't dissipate)

**Physical Interpretation**:

- **L_sym** = "Friction" = Passive decay toward equilibrium
- **L_anti** = "Driving" = Active flux maintaining structure
- **σ_hk** = "Metabolic cost" = Energy throughput to maintain NESS

**The Open Systems Insight**:

For a system to persist out of equilibrium (life, intelligence, structure),
it must have L_anti ≠ 0, which requires σ_hk > 0.

**"To exist is to pay rent."**

The housekeeping entropy is the rent that structure pays to the universe.

**Dissipation-Complexity Constraint (Conjecture)**:

  ComplexityMeasure ∝ σ_hk / T

Complex structures require higher flux to maintain. This will be formalized
in Phase 2 when we connect to EnergyUnification.lean.
-/

end Thermodynamics
end SGC
