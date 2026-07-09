import SGC.Thermodynamics.EntropyProduction

/-!
# The SGC ↔ Singular Learning Theory (SLT) bridge

An **honest, non-vacuous** correspondence between SGC's hidden entropy production and the
asymptotic Bayesian free-energy correction of Watanabe's Singular Learning Theory.

## What is proven here (and what is assumed)

SGC supplies a rigorous two-sided bound (modulo the documented `gaspard_path_space_identity`
axiom and the trajectory axiom behind `hidden_entropy_bounded_by_defect`):

    γ · ‖D‖²_π  ≤  σ_hid(L,P,π)  ≤  C · ε²        (C = |V|, γ = spectral gap)

i.e. the coarse-graining defect ε and the hidden dissipation σ_hid are equivalent up to
the spectral gap and the state-space size (`hidden_entropy_lower_bound`,
`hidden_entropy_bounded_by_defect`).

SLT supplies the asymptotic Bayesian free energy (Watanabe 2009):

    F_n(β) = n·S + (λ / β)·log n + o(log n),

whose only model-dependent correction RATE is `λ / β`, with `λ` the real log-canonical
threshold (RLCT / learning coefficient): smaller `λ` ⟺ lower free energy ⟺ better
generalization.  We deliberately DO NOT compute `λ`: it is a resolution-of-singularities
invariant with no honest finite-`Fintype` surrogate (encoding it as e.g. `1/|basin|`
would be a fiction).  Instead we keep the SLT correction rate ABSTRACT (`F_rate : ℝ`) and
make the SGC↔SLT identification an EXPLICIT, named hypothesis:

    `bridge : F_rate = κ · σ_hid(L,P,π)`           (κ ≥ 0, the SGC↔SLT coupling)

Under that single conjectural hypothesis the SGC sandwich transports verbatim to the SLT
correction rate.  That is the honest content of the bridge: *if* the free-energy
correction is the thermodynamic shadow of hidden dissipation, *then* low SGC defect ⟺ low
SLT complexity (good generalization).  The conjecture is isolated in one hypothesis rather
than smuggled into a definition.

## Caveat against a tempting conflation

`SGC.Lifshitz.freeEnergyExponent d = d/2 + 1` (proven `= 5/2` at `d = 3`) is the band-edge
SCALING EXPONENT of the spectral free energy — a *different* object from the SLT RLCT `λ`.
They must not be identified; this module keeps `λ` (hence `F_rate`) abstract on purpose.

## References
* Watanabe (2009) *Algebraic Geometry and Statistical Learning Theory*.
* Gaspard (2004) JSP 117:599; Maes–Netočný (2003); arXiv:2602.15663 — the σ_hid ~ ε² staging.
-/

namespace SGC.Bridge.SingularLearning

open Finset BigOperators Matrix Real
open SGC.Thermodynamics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **SGC → SLT free-energy UPPER transport.**

Under the bridge identification `F_rate = κ · σ_hid`, the SLT free-energy correction rate
inherits SGC's defect bound: a small coarse-graining defect `ε` forces a small free-energy
correction (i.e. good generalization).  The constant `C` is exactly the one from
`hidden_entropy_bounded_by_defect` (`= |V|`); it does not depend on `F_rate`, so the bound
is non-vacuous. -/
theorem slt_free_energy_le_defect
    (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ x, 0 < pi_dist x)
    (ε : ℝ) (hε : 0 ≤ ε) (hL : Approximate.IsApproxLumpable L P pi_dist hπ ε)
    (F_rate κ : ℝ) (hκ : 0 ≤ κ)
    (bridge : F_rate = κ * HiddenEntropyProduction L P pi_dist) :
    ∃ C : ℝ, 0 ≤ C ∧ F_rate ≤ κ * C * ε ^ 2 := by
  obtain ⟨C, hC, hub⟩ := hidden_entropy_bounded_by_defect L P pi_dist hπ ε hε hL
  refine ⟨C, hC, ?_⟩
  rw [bridge]
  calc κ * HiddenEntropyProduction L P pi_dist
        ≤ κ * (C * ε ^ 2) := mul_le_mul_of_nonneg_left hub hκ
    _ = κ * C * ε ^ 2 := by ring

/-- **SGC → SLT free-energy LOWER transport.**

Under the same identification the SLT correction rate is bounded BELOW by the spectral gap
times the squared defect-operator norm.  Together with `slt_free_energy_le_defect` this
SANDWICHES the SLT free-energy correction rate by the SGC defect — the singular-learning
restatement of "efficiency requires prediction": a low free-energy correction is impossible
without a correspondingly small defect. -/
theorem defect_le_slt_free_energy
    (L : Matrix V V ℝ) (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ x, 0 < pi_dist x)
    (hL_gen : ∀ x y, x ≠ y → 0 ≤ L x y)
    (h_stat : ∀ v, ∑ u, pi_dist u * L u v = 0)
    (γ : ℝ) (hγ : γ > 0) (hγ_gap : γ ≤ DirichletGap L pi_dist)
    (F_rate κ : ℝ) (hκ : 0 ≤ κ)
    (bridge : F_rate = κ * HiddenEntropyProduction L P pi_dist) :
    γ * κ * (opNorm_pi pi_dist hπ (Approximate.DefectOperator L P pi_dist hπ)) ^ 2 ≤ F_rate := by
  have hlow := hidden_entropy_lower_bound L P pi_dist hπ hL_gen h_stat γ hγ hγ_gap
  rw [bridge]
  calc γ * κ * (opNorm_pi pi_dist hπ (Approximate.DefectOperator L P pi_dist hπ)) ^ 2
        = κ * (γ * (opNorm_pi pi_dist hπ (Approximate.DefectOperator L P pi_dist hπ)) ^ 2) := by
          ring
    _ ≤ κ * HiddenEntropyProduction L P pi_dist := mul_le_mul_of_nonneg_left hlow hκ

end SGC.Bridge.SingularLearning
