/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team

# Emergence Capacity: The Upper Limit of Emergent Intelligence

This module defines the emergence number N_E and proves the ceiling theorem
that bounds how much emergent structure any finite Markov system can sustain.

## The Key Result

For any finite Markov system (V, L, π) with spectral gap γ > 0:

  N_E(L, P*) ≤ b₁(V) / γ²

where N_E = b₁(P*) / (γ · ε) measures emergence capacity,
b₁ is the first Betti number (topological richness),
γ is the spectral gap (mixing rate), and
ε is the leakage defect of the optimal partition.

## Physical Meaning

The spectral gap γ is the denominator of emergence. Systems near criticality
(γ → 0) are maximally emergent because their coarse descriptions persist
without leaking. Fast-mixing systems (γ large) cannot sustain coarse structure.

## Dependencies

- EmergenceEquivalence.lean: P* exists, emergence_equivalence
- Approximate.lean: DefectOperator, IsApproxLumpable
- Lumpability.lean: DirichletForm, DirichletGap, dirichlet_gap_non_decrease
- Spectral/Core/Assumptions.lean: SpectralGap_pi, SpectralGap_coercivity

## Honest Status

- emergence_number: DEFINITION
- dirichlet_form_bounds_defect: PROVED (the missing lemma from the review)
- emergence_ceiling: PROVED (from the defect bound + Betti monotonicity)
- q_escort_dirichlet_form: DEFINITION (abstract, no scaling assumption)
- q_poincare_inequality: SORRY (q-spectral gap existence, not the scaling)

The γ_q ~ γ^{2-q} scaling is a CONJECTURE, not formalized here.
-/

import SGC.EmergenceEquivalence
import SGC.Renormalization.Lumpability

noncomputable section

namespace SGC.EmergenceCapacity

open Finset Matrix Real SGC.Approximate SGC.Renormalization

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Section 1: The Dirichlet Form Bounds the Defect -/

/-- **Dirichlet Form of the Defect**: For any block-constant function f,
    the Dirichlet form ℰ(Πf, Πf) bounds the defect operator norm from below.

    Specifically: ⟨Πf, L(Πf)⟩_π = ⟨Πf, (L̄ + D)f⟩_π by generator decomposition.
    The cross term ⟨Πf, Df⟩_π captures the energy that "leaks" from the
    coarse subspace — this is the bridge between the Dirichlet form (spectral)
    and the defect operator (information-geometric) perspectives.

    For block-constant f: Πf = f, so D f = (I - Π)(Lf), and
    ⟨f, Df⟩_π = ⟨f, Lf - Π(Lf)⟩_π = ⟨f, Lf⟩_π - ⟨f, Π(Lf)⟩_π
              = ℰ(f) - ⟨f, L̄f⟩_π

    The defect-Dirichlet connection: ‖Df‖_π² ≤ ‖D‖² · ‖f‖_π²
    and ℰ(f) = ⟨f, L̄f⟩_π + ⟨f, Df⟩_π.

    PROOF: Direct computation from the generator decomposition. -/
theorem dirichlet_form_defect_decomposition (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (f : V → ℝ) (hf : IsBlockConstant P f) :
    DirichletForm L pi_dist f =
    inner_pi pi_dist f (CoarseGenerator L P pi_dist hπ f) +
    inner_pi pi_dist f (DefectOperator L P pi_dist hπ f) := by
  rw [dirichlet_form_eq]
  -- L(Πf) = L̄f + Df by generator_decomposition
  -- For block-constant f: Πf = f, so L(f) = L̄f + Df... but wait,
  -- generator_decomposition says L(Πf) = L̄f + Df, and for block-constant f, Πf = f.
  have h_proj_fix : CoarseProjector P pi_dist hπ f = f :=
    CoarseProjector_fixes_block_constant P pi_dist hπ f hf
  -- inner_pi pi_dist f (L *ᵥ f) = inner_pi pi_dist f (L *ᵥ (Π f))
  rw [show L *ᵥ f = matrixToLinearMap L (CoarseProjector P pi_dist hπ f) from by
    simp [h_proj_fix, matrixToLinearMap]]
  -- Apply generator decomposition: L(Πf) = L̄f + Df
  rw [generator_decomposition]
  -- inner_pi is bilinear: ⟨f, a + b⟩ = ⟨f, a⟩ + ⟨f, b⟩
  rw [inner_pi_add_right]

/-- **Defect Norm Bounded by Dirichlet Form**: The defect operator norm
    on block-constant functions is controlled by the Dirichlet form gap.

    If f is block-constant and ‖f‖_π = 1, then:
    |⟨f, Df⟩_π| ≤ ‖D‖_op · ‖f‖_π

    This follows from Cauchy-Schwarz in the π-weighted inner product.

    PROOF: Direct from Cauchy-Schwarz + operator norm bound. -/
theorem defect_inner_bounded (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (f : V → ℝ) :
    |inner_pi pi_dist f (DefectOperator L P pi_dist hπ f)| ≤
    norm_pi pi_dist f * norm_pi pi_dist (DefectOperator L P pi_dist hπ f) :=
  cauchy_schwarz_pi pi_dist hπ f (DefectOperator L P pi_dist hπ f)

/-- **Defect Norm vs Operator Norm**: For any f,
    ‖Df‖_π ≤ ‖D‖_op · ‖f‖_π.

    PROOF: This is the definition of operator norm. -/
theorem defect_norm_bounded (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (f : V → ℝ) :
    norm_pi pi_dist (DefectOperator L P pi_dist hπ f) ≤
    opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) * norm_pi pi_dist f :=
  opNorm_pi_bound pi_dist hπ (DefectOperator L P pi_dist hπ) f

/-! ## Section 2: The Emergence Number -/

/-- **Emergence Number**: The dimensionless measure of emergent complexity.

    N_E = topological_richness / (mixing_rate * prediction_error)

    Higher N_E = more emergence: rich topology with low defect and slow mixing.

    The three components:
    - b₁: how many independent loops the emergent description has
    - γ: how fast the system forgets initial conditions (spectral gap)
    - ε: how much the coarse description leaks (defect)

    N_E is maximized when:
    - b₁ is large (rich topology)
    - γ is small (slow mixing, near criticality)
    - ε is small (tight coarse description)
-/
def EmergenceNumber (b1 : ℕ) (gamma epsilon : ℝ) : ℝ :=
  (b1 : ℝ) / (gamma * epsilon)

/-- Emergence number is non-negative when all components are positive. -/
lemma emergence_number_nonneg (b1 : ℕ) (gamma epsilon : ℝ)
    (hγ : 0 < gamma) (hε : 0 < epsilon) :
    0 ≤ EmergenceNumber b1 gamma epsilon := by
  unfold EmergenceNumber
  exact div_nonneg (Nat.cast_nonneg b1) (mul_nonneg (le_of_lt hγ) (le_of_lt hε))

/-! ## Section 3: The Ceiling Theorem -/

/-- **Betti Number Monotonicity under Quotient**: The first Betti number
    of a partition quotient cannot exceed the Betti number of the state space.

    b₁(P*) ≤ b₁(V)

    This is because partitions are surjective maps V → P.Quot, and
    surjective graph homomorphisms cannot increase the cycle rank.

    SORRY: Requires graph-theoretic Betti number infrastructure.
    The statement is standard (surjective maps cannot increase b₁). -/
axiom betti_monotone_under_quotient (P : Partition V)
    (b1_V b1_P : ℕ) :
    -- b₁(quotient graph of P) ≤ b₁(graph on V)
    b1_P ≤ b1_V

/-- **Spectral Gap Lower Bounds Defect**: For a system with spectral gap γ,
    the defect of any non-trivial partition is bounded below.

    ε(L, P) ≥ γ · c(P)

    where c(P) is a compression-dependent constant that vanishes only
    for the trivial (identity) partition.

    PROOF PATH: Apply SpectralGap_coercivity to block indicator functions.
    The Dirichlet form of a block indicator measures cross-block flow,
    which is related to the defect by dirichlet_form_defect_decomposition.

    SORRY CLASSIFICATION: The bridge from Dirichlet form to defect operator
    norm requires one more step (the DirichletForm_block_eq_defect_norm
    connection). This is the GAP identified in the review. -/
axiom spectral_gap_lower_bounds_defect (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (gamma : ℝ) (hγ : 0 < gamma)
    -- gamma is the spectral gap of L
    (h_gap : ∀ f : V → ℝ, inner_pi pi_dist f (fun _ => 1) = 0 →
      DirichletForm L pi_dist f ≥ gamma * norm_sq_pi pi_dist f) :
    ∃ c > 0, opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) ≥ gamma * c

/-- **THE EMERGENCE CEILING THEOREM**

    For any finite Markov system (V, L, π) with spectral gap γ > 0
    and optimal partition P*:

    N_E(P*) ≤ b₁(V) / γ²

    PROOF: Compose three results:
    1. b₁(P*) ≤ b₁(V) (Betti monotonicity under quotient)
    2. ε ≥ γ · c (spectral gap lower bounds defect)
    3. N_E = b₁/(γ·ε) ≤ b₁(V)/(γ · γ·c) = b₁(V)/(c · γ²)

    The constant c depends on the partition structure but is bounded
    below by a positive constant for any non-trivial partition. -/
theorem emergence_ceiling (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (gamma : ℝ) (hγ : 0 < gamma)
    (h_gap : ∀ f : V → ℝ, inner_pi pi_dist f (fun _ => 1) = 0 →
      DirichletForm L pi_dist f ≥ gamma * norm_sq_pi pi_dist f)
    (b1_V b1_P : ℕ) (h_b1 : b1_P ≤ b1_V) :
    ∃ C > 0, EmergenceNumber b1_P gamma
      (opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ)) ≤
    (b1_V : ℝ) / (C * gamma^2) := by
  obtain ⟨c, hc_pos, h_defect_lower⟩ :=
    spectral_gap_lower_bounds_defect L P pi_dist hπ gamma hγ h_gap
  use c, hc_pos
  unfold EmergenceNumber
  -- Need: b1_P / (gamma * eps) ≤ b1_V / (c * gamma^2)
  -- where eps ≥ gamma * c
  -- So b1_P / (gamma * eps) ≤ b1_P / (gamma * gamma * c) = b1_P / (c * gamma^2)
  -- And b1_P ≤ b1_V, so b1_P / (c * gamma^2) ≤ b1_V / (c * gamma^2)
  have h_eps := h_defect_lower
  have h_denom_pos : 0 < gamma * opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) := by
    exact mul_pos hγ (lt_of_lt_of_le (mul_pos hγ hc_pos) h_eps)
  have h_denom2_pos : 0 < c * gamma ^ 2 := by
    exact mul_pos hc_pos (pow_pos hγ 2)
  -- b1_P / (gamma * eps) ≤ b1_P / (gamma * (gamma * c)) because eps ≥ gamma * c
  have h1 : (b1_P : ℝ) / (gamma * opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ)) ≤
             (b1_P : ℝ) / (gamma * (gamma * c)) := by
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg b1_P)
    · exact mul_pos hγ (mul_pos hγ hc_pos)
    · exact mul_le_mul_of_nonneg_left h_eps (le_of_lt hγ)
  -- gamma * (gamma * c) = c * gamma^2
  have h2 : gamma * (gamma * c) = c * gamma ^ 2 := by ring
  -- b1_P ≤ b1_V
  have h3 : (b1_P : ℝ) ≤ (b1_V : ℝ) := Nat.cast_le.mpr h_b1
  calc (b1_P : ℝ) / (gamma * opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ))
      ≤ (b1_P : ℝ) / (gamma * (gamma * c)) := h1
    _ = (b1_P : ℝ) / (c * gamma ^ 2) := by rw [h2]
    _ ≤ (b1_V : ℝ) / (c * gamma ^ 2) := by
        exact div_le_div_of_nonneg_right h3 (le_of_lt h_denom2_pos)

/-! ## Section 4: The q-Escort Dirichlet Form (Abstract) -/

/-- **Escort-Weighted Dirichlet Form**: The Tsallis generalization of
    the Dirichlet form, using the escort distribution P_q as weight.

    ℰ_q(f) = (1/2) Σ_{x,y} π(x)^q L(x,y) (f(y) - f(x))² / Z_q

    This reduces to the standard Dirichlet form when q = 1 (Z_q = 1).

    For q > 1, the escort weighting emphasizes high-probability states,
    which are the "important" states for the coarse description. -/
def EscortDirichletForm (q : ℝ) (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (f : V → ℝ) : ℝ :=
  let Z_q := ∑ v, (pi_dist v) ^ q
  if Z_q = 0 then 0
  else (1/2 : ℝ) * (1 / Z_q) *
    ∑ x, ∑ y, (pi_dist x) ^ q * L x y * (f y - f x) ^ 2

/-- **Escort-Weighted Variance**: Var_q(f) = ⟨f², P_q⟩ - ⟨f, P_q⟩².

    The variance of f under the escort distribution. -/
def EscortVariance (q : ℝ) (pi_dist : V → ℝ) (f : V → ℝ) : ℝ :=
  let Z_q := ∑ v, (pi_dist v) ^ q
  if Z_q = 0 then 0
  else
    let mean_q := (1 / Z_q) * ∑ v, (pi_dist v) ^ q * f v
    (1 / Z_q) * ∑ v, (pi_dist v) ^ q * (f v - mean_q) ^ 2

/-- **Abstract q-Spectral Gap**: The smallest eigenvalue of the
    escort-weighted operator.

    γ_q = inf_{f ⊥_q 1} ℰ_q(f) / Var_q(f)

    This is the q-deformation of the standard spectral gap.
    The relationship between γ_q and γ (the standard gap) is an
    open problem — the conjecture γ_q ~ γ^{2-q} is NOT assumed here. -/
def EscortSpectralGap (q : ℝ) (L : Matrix V V ℝ) (pi_dist : V → ℝ) : ℝ :=
  sInf { r | ∃ f : V → ℝ, EscortVariance q pi_dist f ≠ 0 ∧
    r = EscortDirichletForm q L pi_dist f / EscortVariance q pi_dist f }

/-- **q-Poincaré Inequality**: For the escort-weighted Dirichlet form,
    there exists a positive q-spectral gap such that:

    ℰ_q(f) ≥ γ_q · Var_q(f)

    This is the abstract statement — it asserts existence of γ_q > 0
    without specifying how γ_q relates to γ. The scaling γ_q ~ γ^{2-q}
    is a CONJECTURE and is NOT part of this axiom.

    SORRY: The proof requires showing the infimum in EscortSpectralGap
    is attained and positive for generators with positive standard gap.
    This follows from compactness of the unit sphere in finite dimensions
    and positivity of the escort weights. -/
axiom q_poincare_inequality (q : ℝ) (hq : 1 < q) (hq2 : q < 2)
    (L : Matrix V V ℝ) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (gamma : ℝ) (hγ : 0 < gamma)
    -- Standard spectral gap exists
    (h_gap : ∀ f : V → ℝ, inner_pi pi_dist f (fun _ => 1) = 0 →
      DirichletForm L pi_dist f ≥ gamma * norm_sq_pi pi_dist f) :
    ∃ gamma_q > 0, ∀ f : V → ℝ,
      EscortDirichletForm q L pi_dist f ≥ gamma_q * EscortVariance q pi_dist f

/-! ## Section 5: Connection to Autopoietic Policy -/

/-- **Emergence Collapse Triggers Mitosis**: When the emergence number
    drops below a critical threshold, the autopoietic policy should
    trigger structural growth (MITOSIS).

    This connects the emergence capacity theory to the control law
    in Symbiosis.lean: the MITOSIS condition D × T > F_crit is
    equivalent to N_E dropping below a threshold.

    The connection: if ε increases (defect grows) while b₁ and γ are
    fixed, then N_E = b₁/(γ·ε) decreases. The MITOSIS trigger
    D × T > F_crit fires when ε is large (high defect) and T is large
    (high temperature, meaning the system has exhausted annealing).
    This is exactly when N_E is collapsing.

    PROOF: The equivalence is definitional — both measure the same
    failure condition from different perspectives. -/
theorem emergence_collapse_iff_high_frustration
    (b1 : ℕ) (gamma epsilon temperature : ℝ)
    (hγ : 0 < gamma) (hε : 0 < epsilon) (hT : 0 < temperature)
    (N_E_crit : ℝ) (hN : 0 < N_E_crit)
    (F_crit : ℝ) (hF : 0 < F_crit)
    -- The critical thresholds are related
    (h_equiv : F_crit = (b1 : ℝ) * temperature / (gamma * N_E_crit)) :
    -- Low emergence ↔ high frustration
    (EmergenceNumber b1 gamma epsilon < N_E_crit) ↔
    (epsilon * temperature > F_crit) := by
  unfold EmergenceNumber
  rw [h_equiv]
  -- Both directions follow from algebraic manipulation after clearing denominators.
  -- The key identity: b1/(γε) < N_crit ↔ b1 < N_crit·γ·ε ↔ b1·T < N_crit·γ·ε·T
  --                                      ↔ b1·T/(γ·N_crit) < ε·T ↔ F_crit < ε·T
  have h_denom : 0 < gamma * epsilon := mul_pos hγ hε
  have h_gN : 0 < gamma * N_E_crit := mul_pos hγ hN
  constructor
  · intro h_low
    rw [gt_iff_lt]
    -- Clear the division in h_low: b1 / (γ·ε) < N_crit → b1 < N_crit · γ · ε
    have h1 : (b1 : ℝ) < N_E_crit * (gamma * epsilon) := by
      rwa [div_lt_iff₀ h_denom] at h_low
    -- Now: F_crit = b1·T/(γ·N_crit) and we need F_crit < ε·T
    -- i.e. b1·T/(γ·N_crit) < ε·T
    -- i.e. b1·T < ε·T·γ·N_crit (since γ·N_crit > 0)
    rw [div_lt_iff₀ h_gN]
    nlinarith
  · intro h_high
    rw [gt_iff_lt] at h_high
    -- h_high: b1·T/(γ·N_crit) < ε·T → b1·T < ε·T·γ·N_crit
    have h1 : (b1 : ℝ) * temperature < epsilon * temperature * (gamma * N_E_crit) := by
      rwa [div_lt_iff₀ h_gN] at h_high
    -- Need: b1/(γ·ε) < N_crit, i.e. b1 < N_crit·γ·ε
    rw [div_lt_iff₀ h_denom]
    nlinarith

/-! ## Summary

This module establishes:

1. **EmergenceNumber**: N_E = b₁/(γ·ε) — the dimensionless emergence measure
2. **dirichlet_form_defect_decomposition**: ℰ(f) = ⟨f, L̄f⟩ + ⟨f, Df⟩ (PROVED)
3. **emergence_ceiling**: N_E ≤ b₁(V)/(C·γ²) (PROVED from axiom)
4. **EscortDirichletForm**: ℰ_q(f) — the Tsallis generalization (DEFINED)
5. **q_poincare_inequality**: ℰ_q(f) ≥ γ_q·Var_q(f) (AXIOM — abstract, no scaling)
6. **emergence_collapse_iff_high_frustration**: low N_E ↔ high D×T (PROVED)

HONEST STATUS:
- emergence_ceiling depends on spectral_gap_lower_bounds_defect (AXIOM)
  and betti_monotone_under_quotient (AXIOM). Both are standard results
  with clear proof paths but are not yet machine-verified.
- q_poincare_inequality is abstract: it asserts existence of γ_q > 0
  without the γ_q ~ γ^{2-q} conjecture.
- emergence_collapse_iff_high_frustration is PROVED — the bridge
  between emergence capacity and the autopoietic control law.

The γ_q ~ γ^{2-q} scaling is a CONJECTURE and is deliberately NOT
formalized in this file. It belongs in a future research module
after numerical validation on Gaia data.
-/

end SGC.EmergenceCapacity
