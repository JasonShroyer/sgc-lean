/-
Copyright (c) 2026 Jason Shroyer. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Matrix.Normed

/-!
# Deterministic Readout: the observation channel as a first-class object

Phase I of the observation stack (Astrolabe `ARCHITECTURE.md`, 2026-09-03).
The Kuramoto observation-ladder case study established *empirically* that a
quantized readout of a Markov process manufactures memory: the latent
continuous phase was closed under a scalar first-order wrapped law, while
every binned observable retained memory at all tested resolutions. This
file is the exact finite-state mathematics of that phenomenon — the
"telescope theorem" layer: when is the *observed* process faithfully
represented by an effective kernel, and what is the price when it is not?

## Objects

* `IsKernel` — row-stochastic (rectangular) kernels. The lifting kernel
  `Λ : Y ⇝ X` assigns each observed state a latent fiber law.
* `push` — pushforward of a row measure through a deterministic readout
  `π : X → Y` (quantization/binning as the 0/1 special case of a channel;
  genuinely stochastic channels are Phase II, deliberately NOT here).
* `Compatible π Λ` — `π♯Λ = I_Y`: lift-then-read is the identity (fiber-
  supported lifts).
* `Intertwines P P̄ Λ` — the observation intertwining `Λ·P = P̄·Λ`
  (lift-then-evolve = evolve-then-lift), the exact observation-closure
  condition. `obsDefect 𝒟 = Λ·P − P̄·Λ` is its failure.

## Main results

* **`observation_closure_exact`** — WITH its initial-condition condition
  (2026-09-03 review): under compatibility, intertwining, and compatible
  initialization `μ_X = μ_Y·Λ`, the latent evolution is represented
  exactly: `μ_X·Pⁿ = (μ_Y·P̄ⁿ)·Λ`, and the readout marginal is
  `π♯(μ_X·Pⁿ) = μ_Y·P̄ⁿ` for all `n`. An intertwining alone does NOT
  license "every observed process is Markov from every initial law".
* **`observation_telescoping`** — the discrete Duhamel identity for the
  observation defect: `Λ·Pⁿ − P̄ⁿ·Λ = Σ_{k<n} P̄ᵏ·𝒟·P^{n−1−k}`.
* **`observation_error_le`** — `‖Λ·Pⁿ − P̄ⁿ·Λ‖ ≤ n·‖𝒟‖` in the L∞
  operator norm: the observed-path discrepancy horizon. Zero defect gives
  eternal observational closure; small defect gives a linear horizon —
  the same certificate calculus as the dynamical quotient, now for the
  measurement map.

## Honest scope

Finite state spaces; deterministic readout only (stochastic channels =
hidden-Markov/filtering territory, Phase II); the bound is an upper bound
(mixing refinements as in the dynamical case are future work). This is
the formal core of the audit principle: *memory can be a property of the
world-plus-readout pair* — `𝒟 ≠ 0` sources observed memory without any
unmodeled latent dynamics.
-/

namespace SGC.Observation

open Finset Matrix
open scoped NNReal

attribute [local instance] Matrix.linftyOpNormedAddCommGroup

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-! ## §1. Kernels, readouts, lifts -/

/-- A row-stochastic (possibly rectangular) kernel. -/
structure IsKernel (M : Matrix Y X ℝ) : Prop where
  nonneg : ∀ y x, 0 ≤ M y x
  row_sum_one : ∀ y, ∑ x, M y x = 1

/-- Pushforward of a row measure through a deterministic readout. -/
def push (pi_map : X → Y) (mu : X → ℝ) : Y → ℝ :=
  fun y => ∑ x ∈ Finset.univ.filter (fun x => pi_map x = y), mu x

/-- Compatibility `π♯Λ = I_Y`: the fiber law of `y` reads out as `y`. -/
def Compatible (pi_map : X → Y) (Lam : Matrix Y X ℝ) : Prop :=
  ∀ y y', (∑ x ∈ Finset.univ.filter (fun x => pi_map x = y'), Lam y x)
    = if y' = y then 1 else 0

/-- The observation intertwining: lift-then-evolve = evolve-then-lift. -/
def Intertwines (P : Matrix X X ℝ) (Pbar : Matrix Y Y ℝ)
    (Lam : Matrix Y X ℝ) : Prop := Lam * P = Pbar * Lam

/-- The observation defect `𝒟 = Λ·P − P̄·Λ`: the exact obstruction to
observational closure. -/
def obsDefect (P : Matrix X X ℝ) (Pbar : Matrix Y Y ℝ)
    (Lam : Matrix Y X ℝ) : Matrix Y X ℝ := Lam * P - Pbar * Lam

/-! ## §2. Exact observation closure (with its initialization condition) -/

/-- Intertwining propagates to all powers. -/
lemma intertwines_pow {P : Matrix X X ℝ} {Pbar : Matrix Y Y ℝ}
    {Lam : Matrix Y X ℝ} (h : Intertwines P Pbar Lam) (n : ℕ) :
    Lam * P ^ n = Pbar ^ n * Lam := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, ← Matrix.mul_assoc, ih,
        Matrix.mul_assoc, h, ← Matrix.mul_assoc]

/-- Lift-then-read returns the observed measure (compatibility, in
measure form). -/
lemma push_vecMul_lift (pi_map : X → Y) (Lam : Matrix Y X ℝ)
    (hcomp : Compatible pi_map Lam) (nu : Y → ℝ) :
    push pi_map (Matrix.vecMul nu Lam) = nu := by
  funext y'
  unfold push
  have hswap : ∀ x, Matrix.vecMul nu Lam x = ∑ y, nu y * Lam y x := by
    intro x
    rfl
  simp_rw [hswap]
  rw [Finset.sum_comm]
  have hinner : ∀ y, (∑ x ∈ Finset.univ.filter (fun x => pi_map x = y'),
      nu y * Lam y x) = nu y * (if y' = y then 1 else 0) := by
    intro y
    rw [← Finset.mul_sum, hcomp y y']
  simp_rw [hinner]
  simp [Finset.sum_ite_eq]

/-- **Exact observation closure.** Under compatibility, intertwining, and
the compatible initialization `μ_X = μ_Y·Λ`:
latent evolution is represented by the observed kernel,
`μ_X·Pⁿ = (μ_Y·P̄ⁿ)·Λ`, and the readout marginal evolves by `P̄` alone,
`π♯(μ_X·Pⁿ) = μ_Y·P̄ⁿ`. The initialization hypothesis is essential: the
intertwining identity alone does not govern incompatible initial laws. -/
theorem observation_closure_exact (P : Matrix X X ℝ) (Pbar : Matrix Y Y ℝ)
    (Lam : Matrix Y X ℝ) (pi_map : X → Y)
    (hcomp : Compatible pi_map Lam) (hint : Intertwines P Pbar Lam)
    (muY : Y → ℝ) (n : ℕ) :
    Matrix.vecMul (Matrix.vecMul muY Lam) (P ^ n)
        = Matrix.vecMul (Matrix.vecMul muY (Pbar ^ n)) Lam
    ∧ push pi_map (Matrix.vecMul (Matrix.vecMul muY Lam) (P ^ n))
        = Matrix.vecMul muY (Pbar ^ n) := by
  have hrep : Matrix.vecMul (Matrix.vecMul muY Lam) (P ^ n)
      = Matrix.vecMul (Matrix.vecMul muY (Pbar ^ n)) Lam := by
    rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, intertwines_pow hint]
  exact ⟨hrep, by rw [hrep, push_vecMul_lift pi_map Lam hcomp]⟩

/-! ## §3. The observation Duhamel identity and the horizon bound -/

/-- **Observation telescoping** (discrete Duhamel for the measurement
map): the `n`-step observational closure error is a sum of single
observation-defect events, propagated by the observed law before the
event and the latent dynamics after it:
`Λ·Pⁿ − P̄ⁿ·Λ = Σ_{k<n} P̄ᵏ·𝒟·P^{n−1−k}`. -/
theorem observation_telescoping (P : Matrix X X ℝ) (Pbar : Matrix Y Y ℝ)
    (Lam : Matrix Y X ℝ) (n : ℕ) :
    Lam * P ^ n - Pbar ^ n * Lam
      = ∑ k ∈ Finset.range n,
          Pbar ^ k * obsDefect P Pbar Lam * P ^ (n - 1 - k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have expand : Lam * P ^ (n + 1) - Pbar ^ (n + 1) * Lam
        = (Lam * P ^ n - Pbar ^ n * Lam) * P
          + Pbar ^ n * obsDefect P Pbar Lam := by
      unfold obsDefect
      rw [pow_succ P, pow_succ Pbar]
      rw [Matrix.sub_mul, Matrix.mul_sub]
      simp only [Matrix.mul_assoc]
      abel
    rw [expand, ih, Matrix.sum_mul, Finset.sum_range_succ]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hkn : k < n := Finset.mem_range.mp hk
      have harith : n + 1 - 1 - k = (n - 1 - k) + 1 := by omega
      rw [harith, pow_succ P]
      simp only [Matrix.mul_assoc]
    · have : n + 1 - 1 - n = 0 := by omega
      rw [this, pow_zero, Matrix.mul_one]

/-- Nonnegative rows summing to ≤ 1 are non-expansive in the L∞ operator
norm (rectangular version of the dynamical lemma). -/
lemma linfty_le_one_of_rows (M : Matrix Y X ℝ)
    (hnn : ∀ y x, 0 ≤ M y x) (hrow : ∀ y, ∑ x, M y x ≤ 1) :
    ‖M‖ ≤ 1 := by
  rw [Matrix.linfty_opNorm_def]
  rw [show (1 : ℝ) = ((1 : ℝ≥0) : ℝ) by norm_num]
  rw [NNReal.coe_le_coe]
  refine Finset.sup_le fun y _ => ?_
  have hcoe : ((∑ x, ‖M y x‖₊ : ℝ≥0) : ℝ) = ∑ x, M y x := by
    push_cast
    exact Finset.sum_congr rfl fun x _ => Real.norm_of_nonneg (hnn y x)
  have : ((∑ x, ‖M y x‖₊ : ℝ≥0) : ℝ) ≤ ((1 : ℝ≥0) : ℝ) := by
    rw [hcoe]; simpa using hrow y
  exact_mod_cast this

lemma kernel_norm_le_one {M : Matrix Y X ℝ} (h : IsKernel M) : ‖M‖ ≤ 1 :=
  linfty_le_one_of_rows M h.nonneg fun y => (h.row_sum_one y).le

/-- Powers of a square kernel are non-expansive. -/
lemma kernel_pow_norm_le_one {P : Matrix X X ℝ} (h : IsKernel P) (n : ℕ) :
    ‖P ^ n‖ ≤ 1 := by
  induction n with
  | zero =>
    rw [pow_zero]
    refine linfty_le_one_of_rows _ ?_ ?_
    · intro i j
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · intro i
      simp [Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ]
    calc ‖P ^ n * P‖ ≤ ‖P ^ n‖ * ‖P‖ := Matrix.linfty_opNorm_mul _ _
      _ ≤ 1 * 1 := mul_le_mul ih (kernel_norm_le_one h)
            (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num

/-- **The observation horizon bound**: the `n`-step observational
discrepancy is at most `n` single defect events —
`‖Λ·Pⁿ − P̄ⁿ·Λ‖ ≤ n·‖𝒟‖`. At `𝒟 = 0`: eternal observational closure.
Small `𝒟`: a linear validity horizon for the measurement map, the same
certificate calculus as the dynamical quotient. -/
theorem observation_error_le (P : Matrix X X ℝ) (Pbar : Matrix Y Y ℝ)
    (Lam : Matrix Y X ℝ) (hP : IsKernel P) (hPbar : IsKernel Pbar)
    (n : ℕ) :
    ‖Lam * P ^ n - Pbar ^ n * Lam‖
      ≤ (n : ℝ) * ‖obsDefect P Pbar Lam‖ := by
  rw [observation_telescoping]
  calc ‖∑ k ∈ Finset.range n,
        Pbar ^ k * obsDefect P Pbar Lam * P ^ (n - 1 - k)‖
      ≤ ∑ k ∈ Finset.range n,
          ‖Pbar ^ k * obsDefect P Pbar Lam * P ^ (n - 1 - k)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range n, ‖obsDefect P Pbar Lam‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        calc ‖Pbar ^ k * obsDefect P Pbar Lam * P ^ (n - 1 - k)‖
            ≤ ‖Pbar ^ k * obsDefect P Pbar Lam‖ * ‖P ^ (n - 1 - k)‖ :=
              Matrix.linfty_opNorm_mul _ _
          _ ≤ ‖Pbar ^ k‖ * ‖obsDefect P Pbar Lam‖ * ‖P ^ (n - 1 - k)‖ := by
              refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
              exact Matrix.linfty_opNorm_mul _ _
          _ ≤ 1 * ‖obsDefect P Pbar Lam‖ * 1 := by
              refine mul_le_mul ?_ (kernel_pow_norm_le_one hP _)
                (norm_nonneg _) (by positivity)
              exact mul_le_mul_of_nonneg_right
                (kernel_pow_norm_le_one hPbar _) (norm_nonneg _)
          _ = ‖obsDefect P Pbar Lam‖ := by ring
    _ = (n : ℝ) * ‖obsDefect P Pbar Lam‖ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end SGC.Observation
