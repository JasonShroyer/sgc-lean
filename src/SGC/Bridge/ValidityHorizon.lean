/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Bridge.PhaseClassifier
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The Emergence Loophole: drives, inherited vorticity, and the validity horizon

`rg_flow_crystalward` (PhaseClassifier) says: under PERFECT, autonomous,
strongly-lumpable coarse-graining, universality is never created — the flow is
one-way toward the crystal. Yet life exists and humans build computers. This
module seals the three escape routes by which emergent computation is possible,
resolving the apparent paradox.

## Route 1 — Drive injection (§1, EXACT)

The probability current is LINEAR in the generator. Driving a crystal substrate
`L` (detailed balance) with any drive `D` gives
`KillingDefect (L + D) π = KillingDefect D π` — **the crystal is transparent to
the drive**: the driven system carries exactly the drive's own vorticity, no
more, no less. Universality is never coarse-grained into being, but it can be
INJECTED by a drive (`drive_injects_vorticity`). A computer is its power supply's
vorticity, hosted on a transparent crystal.

## Route 2 — Inherited vorticity (already sealed, cited here)

`uniformLift_quotient_realizes` (DFD §3): any coarse generator — including a
Universal one — is realized as a strongly-lumpable quotient of a fine system.
`coarse_vorticity_certifies_fine` (PhaseClassifier): every such fine realization
is itself non-crystal. Flexibility + rigidity: emergent universality is always
vorticity already present at the fine scale, reorganized — never created.
§2 adds the contrapositive packaging: `no_spontaneous_universality`.

## Route 3 — The validity horizon T* ~ 1/ε (§3, the analytic engine)

Real coarse-grainings are not perfectly lumpable. Splitting the true fine
dynamics as `A + B` — `A` the ideal (lumpable) part, `B` the leakage with
ε := ‖B‖ — the semigroup perturbation bound (proved here from the exponential
series, no axioms) gives

  `‖exp(t(A+B)) − exp(tA)‖ ≤ t·ε·exp(t(‖A‖+ε))`,

so on any window where `t·(‖A‖+ε) ≤ 1` (one mixing time), the ideal coarse
model is accurate to tolerance δ for all `t ≤ δ/(e·ε)` — **the validity horizon
scales as 1/ε** (`validity_horizon_inverse_leakage`). Within the horizon the
system behaves as its idealized (possibly Universal) coarse model; beyond it,
leakage accumulates and `rg_flow_crystalward` reasserts itself.

## Honest scope

* `A`, `B` live in an abstract real Banach algebra; the identification of `B`
  with a concrete lumpability-defect matrix (and ε with a computable matrix
  norm) is future work — it needs a chosen matrix-norm instance and a defect
  operator, neither of which this module fixes.
* "Active error correction rewinds the T* clock" (the open-system story) is
  physical vocabulary, NOT a theorem here: these theorems cover passive
  evolution between interventions.
* Miranda's topological shielding ("ε = 0 for the computing mode") is the
  already-sealed `stationary_current_orthogonal_gradients` (DFD §8) — the
  orthogonality is exact, not approximate, which is why that route needs no
  horizon at all.
-/

noncomputable section

namespace SGC.Bridge.ValidityHorizon

open Finset Matrix NormedSpace
open scoped Nat
open SGC.Thermodynamics
open SGC.Bridge.DiscreteFluidDynamics
open SGC.Bridge.PhaseClassifier

/-! ## §1. Drive injection: the crystal is transparent -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The probability current is linear in the generator (fixed weights). -/
lemma probabilityCurrent_add (L D : Matrix V V ℝ) (pi_dist : V → ℝ) (x y : V) :
    ProbabilityCurrent (L + D) pi_dist x y
      = ProbabilityCurrent L pi_dist x y + ProbabilityCurrent D pi_dist x y := by
  simp only [ProbabilityCurrent, Matrix.add_apply]
  ring

/-- **Crystal transparency** (current level): driving a detailed-balance
    substrate, the current of the driven system IS the current of the drive. -/
theorem current_driven_crystal (L D : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hdb : DetailedBalance L pi_dist) (x y : V) :
    ProbabilityCurrent (L + D) pi_dist x y = ProbabilityCurrent D pi_dist x y := by
  rw [probabilityCurrent_add,
      (detailed_balance_iff_zero_current L pi_dist).mp hdb x y, zero_add]

/-- **Crystal transparency** (defect level): the Killing defect of a driven
    crystal equals the Killing defect of the drive alone — exact, not
    perturbative. The substrate contributes zero vorticity of its own. -/
theorem killingDefect_driven_crystal (L D : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hdb : DetailedBalance L pi_dist) :
    KillingDefect (L + D) pi_dist = KillingDefect D pi_dist := by
  simp only [KillingDefect]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
    rw [current_driven_crystal L D pi_dist hdb x y]

/-- **Universality is injected, never emergent**: a vortical drive on a crystal
    substrate takes the system out of the crystal phase. Together with
    `rg_flow_crystalward` (passive coarse-graining cannot do this), this is the
    precise resolution of the emergence paradox: the vorticity of a computer is
    exactly the vorticity of its drive. -/
theorem drive_injects_vorticity (L D : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hdb : DetailedBalance L pi_dist) (hD : 0 < KillingDefect D pi_dist) :
    ¬ CrystalPhase (L + D) pi_dist := by
  intro hc
  unfold CrystalPhase at hc
  rw [killingDefect_driven_crystal L D pi_dist hdb] at hc
  rw [hc] at hD
  exact lt_irrefl 0 hD

/-- Removing the drive kills the computation: the substrate alone is crystal.
    (Unplugged computers relax to equilibrium.) -/
theorem substrate_alone_is_crystal (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hdb : DetailedBalance L pi_dist) : CrystalPhase L pi_dist :=
  (crystal_iff_reversible L pi_dist).mpr hdb

/-! ## §2. No spontaneous universality (contrapositive packaging) -/

/-- A crystal fine system never presents a Universal coarse face, for any
    partition and any threshold: emergence of universality by passive
    aggregation alone is impossible. -/
theorem no_spontaneous_universality (γ : ℝ) (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (h : CrystalPhase L pi_dist) :
    ¬ UniversalPhase γ (CoarseGenerator L P pi_dist) (pi_bar P pi_dist) := fun hu =>
  crystal_not_universal γ (CoarseGenerator L P pi_dist) (pi_bar P pi_dist)
    ⟨crystal_rg_stable L P pi_dist hπ h, hu⟩

/-! ## §3. The validity horizon: T* ~ 1/ε

Abstract real Banach algebra throughout; for the SGC reading, take `A` to be
the idealized (strongly lumpable) fine generator and `B` the lumpability
leakage, ε := ‖B‖. -/

variable {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸] [NormedAlgebra ℝ 𝔸]
  [CompleteSpace 𝔸]

/-- Norm of a power is at most the power of the norm. -/
private lemma norm_pow_le_pow (x : 𝔸) (n : ℕ) : ‖x ^ n‖ ≤ ‖x‖ ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
    calc ‖x ^ (m + 1)‖ = ‖x ^ m * x‖ := by rw [pow_succ]
      _ ≤ ‖x ^ m‖ * ‖x‖ := norm_mul_le _ _
      _ ≤ ‖x‖ ^ m * ‖x‖ := mul_le_mul_of_nonneg_right ih (norm_nonneg x)
      _ = ‖x‖ ^ (m + 1) := (pow_succ _ _).symm

/-- Telescoping bound: `‖(A+B)^n − A^n‖ ≤ n‖B‖(‖A‖+‖B‖)^(n−1)`. -/
private lemma norm_pow_sub_pow_le (A B : 𝔸) (n : ℕ) :
    ‖(A + B) ^ n - A ^ n‖ ≤ (n : ℝ) * ‖B‖ * (‖A‖ + ‖B‖) ^ (n - 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hM : ‖A‖ ≤ ‖A‖ + ‖B‖ := le_add_of_nonneg_right (norm_nonneg B)
    have key : (A + B) ^ (m + 1) - A ^ (m + 1)
        = ((A + B) ^ m - A ^ m) * A + (A + B) ^ m * B := by
      rw [pow_succ, pow_succ]
      noncomm_ring
    rw [key, Nat.add_sub_cancel]
    calc ‖((A + B) ^ m - A ^ m) * A + (A + B) ^ m * B‖
        ≤ ‖((A + B) ^ m - A ^ m) * A‖ + ‖(A + B) ^ m * B‖ := norm_add_le _ _
      _ ≤ ‖(A + B) ^ m - A ^ m‖ * ‖A‖ + ‖(A + B) ^ m‖ * ‖B‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ ((m : ℝ) * ‖B‖ * (‖A‖ + ‖B‖) ^ (m - 1)) * (‖A‖ + ‖B‖)
            + (‖A‖ + ‖B‖) ^ m * ‖B‖ := by
          apply add_le_add
          · exact mul_le_mul ih hM (norm_nonneg A) (by positivity)
          · refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg B)
            refine le_trans (norm_pow_le_pow _ m) ?_
            gcongr
            exact norm_add_le A B
      _ ≤ ((m + 1 : ℕ) : ℝ) * ‖B‖ * (‖A‖ + ‖B‖) ^ m := by
          push_cast
          rcases Nat.eq_zero_or_pos m with hm | hm
          · subst hm; simp
          · have hpow : (‖A‖ + ‖B‖) ^ (m - 1) * (‖A‖ + ‖B‖) = (‖A‖ + ‖B‖) ^ m := by
              rw [← pow_succ, Nat.sub_add_cancel hm]
            rw [mul_assoc ((m : ℝ) * ‖B‖), hpow]
            apply le_of_eq
            ring

/-- **Semigroup perturbation bound** (Duhamel-type, proved from the exponential
    series): `‖exp(A+B) − exp(A)‖ ≤ ‖B‖·e^(‖A‖+‖B‖)`. The deviation of the true
    evolution from the ideal one is first-order in the leakage. -/
theorem exp_perturbation_bound (A B : 𝔸) :
    ‖NormedSpace.exp ℝ (A + B) - NormedSpace.exp ℝ A‖
      ≤ ‖B‖ * Real.exp (‖A‖ + ‖B‖) := by
  set M : ℝ := ‖A‖ + ‖B‖ with hMdef
  have h1 : Summable fun n : ℕ => (n !⁻¹ : ℝ) • (A + B) ^ n :=
    expSeries_summable' (𝕂 := ℝ) (A + B)
  have h2 : Summable fun n : ℕ => (n !⁻¹ : ℝ) • A ^ n :=
    expSeries_summable' (𝕂 := ℝ) A
  have e1 : NormedSpace.exp ℝ (A + B) = ∑' n : ℕ, (n !⁻¹ : ℝ) • (A + B) ^ n := by
    rw [exp_eq_tsum]
  have e2 : NormedSpace.exp ℝ A = ∑' n : ℕ, (n !⁻¹ : ℝ) • A ^ n := by
    rw [exp_eq_tsum]
  have hdiff : NormedSpace.exp ℝ (A + B) - NormedSpace.exp ℝ A
      = ∑' n : ℕ, (n !⁻¹ : ℝ) • ((A + B) ^ n - A ^ n) := by
    rw [e1, e2, ← h1.tsum_sub h2]
    exact tsum_congr fun n => (smul_sub _ _ _).symm
  have hterm : ∀ n : ℕ, ‖(n !⁻¹ : ℝ) • ((A + B) ^ n - A ^ n)‖
      ≤ (n !⁻¹ : ℝ) * ((n : ℝ) * ‖B‖ * M ^ (n - 1)) := by
    intro n
    rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (n !⁻¹ : ℝ))]
    exact mul_le_mul_of_nonneg_left (norm_pow_sub_pow_le A B n) (by positivity)
  have hswap : ∀ n : ℕ, ((n + 1)!⁻¹ : ℝ) * (((n : ℝ) + 1) * ‖B‖ * M ^ (n + 1 - 1))
      = ‖B‖ * (M ^ n / (n ! : ℝ)) := by
    intro n
    have hfne : ((n ! : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    rw [Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    field_simp
  have hmaj : Summable fun n : ℕ => (n !⁻¹ : ℝ) * ((n : ℝ) * ‖B‖ * M ^ (n - 1)) := by
    refine (summable_nat_add_iff 1).mp
      (Summable.congr ((Real.summable_pow_div_factorial M).mul_left ‖B‖)
        fun n => ?_)
    push_cast
    exact (hswap n).symm
  have hnorm : Summable fun n : ℕ => ‖(n !⁻¹ : ℝ) • ((A + B) ^ n - A ^ n)‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hmaj
  have hexp : Real.exp M = ∑' n : ℕ, M ^ n / (n ! : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, exp_eq_tsum_div]
  rw [hdiff]
  calc ‖∑' n : ℕ, (n !⁻¹ : ℝ) • ((A + B) ^ n - A ^ n)‖
      ≤ ∑' n : ℕ, ‖(n !⁻¹ : ℝ) • ((A + B) ^ n - A ^ n)‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, (n !⁻¹ : ℝ) * ((n : ℝ) * ‖B‖ * M ^ (n - 1)) :=
        Summable.tsum_le_tsum hterm hnorm hmaj
    _ = ‖B‖ * ∑' n : ℕ, M ^ n / (n ! : ℝ) := by
        rw [hmaj.tsum_eq_zero_add, ← tsum_mul_left]
        simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add]
        exact tsum_congr fun n => by push_cast; exact hswap n
    _ = ‖B‖ * Real.exp M := by rw [← hexp]

/-- **The validity horizon bound**: the coarse/ideal model `exp(tA)` tracks the
    true evolution `exp(t(A+B))` with error at most `t·ε·e^(t(‖A‖+ε))`,
    ε = ‖B‖ the leakage. -/
theorem validity_horizon (A B : 𝔸) (t : ℝ) (ht : 0 ≤ t) :
    ‖NormedSpace.exp ℝ (t • (A + B)) - NormedSpace.exp ℝ (t • A)‖
      ≤ t * ‖B‖ * Real.exp (t * (‖A‖ + ‖B‖)) := by
  have h := exp_perturbation_bound (t • A) (t • B)
  rw [← smul_add] at h
  have hA : ‖t • A‖ = t * ‖A‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  have hB : ‖t • B‖ = t * ‖B‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  rw [hA, hB, ← mul_add] at h
  exact h

/-- **T\* ~ 1/ε** (the emergence window): within one mixing time
    (`t·(‖A‖+ε) ≤ 1`), the ideal coarse model is accurate to tolerance δ for
    all `t ≤ δ/(e·ε)` — the validity horizon is inversely proportional to the
    lumpability leakage. As ε → 0 the window diverges: perfect lumpability is
    the infinite-horizon limit, and `rg_flow_crystalward` becomes exact. -/
theorem validity_horizon_inverse_leakage (A B : 𝔸) (hB : B ≠ 0) (δ t : ℝ)
    (ht : 0 ≤ t) (hwin : t * (‖A‖ + ‖B‖) ≤ 1)
    (hT : t ≤ δ / (Real.exp 1 * ‖B‖)) :
    ‖NormedSpace.exp ℝ (t • (A + B)) - NormedSpace.exp ℝ (t • A)‖ ≤ δ := by
  have hBpos : 0 < ‖B‖ := norm_pos_iff.mpr hB
  have hc : (0 : ℝ) < Real.exp 1 * ‖B‖ := by positivity
  have h1 := validity_horizon A B t ht
  have h2 : t * ‖B‖ * Real.exp (t * (‖A‖ + ‖B‖)) ≤ t * ‖B‖ * Real.exp 1 := by
    have := Real.exp_le_exp.mpr hwin
    have htB : 0 ≤ t * ‖B‖ := by positivity
    exact mul_le_mul_of_nonneg_left this htB
  have h3 : t * (Real.exp 1 * ‖B‖) ≤ δ := by
    have := mul_le_mul_of_nonneg_right hT hc.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hc)] at this
  have h4 : t * ‖B‖ * Real.exp 1 ≤ δ := by
    calc t * ‖B‖ * Real.exp 1 = t * (Real.exp 1 * ‖B‖) := by ring
      _ ≤ δ := h3
  linarith

end SGC.Bridge.ValidityHorizon
