/-
Copyright (c) 2026 Jason Shroyer. All rights reserved.
Released under Apache 2.0 license.
-/
import SGC.Observation.Composition
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Finite Classical Observational Entropy (T1) and the Bayes Lift (T2)

The entropic-bridge program (insight 0020; arXiv:2503.15612 Schindler–
Strasberg–Galke–Winter–Jabbour read classically). Everything finite,
everything explicit — the paper's quantum subtleties are deliberately out
of scope (Phase II).

## Objects

* `klDiv p q = Σ p·log(p/q)` — classical relative entropy.
* `pushforward M p = p·M` — action of a channel on a distribution.
* `measuredKL M p τ = klDiv (pM) (τM)` — measured relative entropy.
* `observationalEntropy M τ p = S(τ) − D_M(p‖τ)` — the paper's Eq. (10),
  classical form: prior entropy minus the informational value of the
  measurement.
* `bayesLift M τ` — the prior-conditioned recovery kernel
  `Λ_τ(x|y) = τ(x)M(y|x)/(Mτ)(y)`: the classical Petz/Bayes inverse.

## Main results

* **`klDiv_nonneg`** (Gibbs) and **`klDiv_dpi`** (the data-processing
  inequality, proven from Jensen via `Real.convexOn_mul_log`): channels
  cannot increase relative entropy. The general classical DPI — the
  prerequisite the Tsallis-specific `FDivergence` machinery did not
  provide.
* `measuredKL_nonneg`, `measuredKL_le_klDiv` — hence
  **`observationalEntropy_le_prior`** (`S_M^τ ≤ S(τ)`) and
  **`observationalEntropy_ge`** (`S_M^τ ≥ S(τ) − D(p‖τ)`): the
  two-sided sandwich of the paper's Sec. VII, classical case.
* `bayesLift_isKernel`, **`bayesLift_reconstructs_prior`** (`(τM)·Λ_τ =
  τ`: lifting the prior's statistics returns the prior), and
  **`bayesLift_deterministic_compatible`**: for a deterministic readout,
  the Bayes lift is fiber-supported and `Compatible` — welding the
  entropic recovery object to the telescope theorems of
  `DeterministicReadout`.

## Honest scope

Positivity hypotheses are explicit everywhere (`q > 0`, `(qM) > 0`,
prior mass on every fiber): entropy is unstable near vanishing reference
mass, and that instability is physics, not bookkeeping. `p ≥ 0` suffices
on the state side (0·log 0 = 0 under Mathlib's `Real.log 0 = 0`).
-/

namespace SGC.Observation

open Finset Matrix
open scoped NNReal

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-! ## §1. Divergence, entropy, pushforward -/

/-- Classical relative entropy (KL divergence), finite form. -/
noncomputable def klDiv (p q : X → ℝ) : ℝ :=
  ∑ x, p x * Real.log (p x / q x)

/-- Shannon entropy, finite form. -/
noncomputable def shannonEntropy (p : X → ℝ) : ℝ :=
  -∑ x, p x * Real.log (p x)

/-- Pushforward of a distribution through a channel (row convention). -/
noncomputable def pushforward (M : Matrix X Y ℝ) (p : X → ℝ) : Y → ℝ :=
  Matrix.vecMul p M

lemma pushforward_apply (M : Matrix X Y ℝ) (p : X → ℝ) (y : Y) :
    pushforward M p y = ∑ x, p x * M x y := rfl

lemma pushforward_nonneg {M : Matrix X Y ℝ} (hM : IsKernel M)
    {p : X → ℝ} (hp : ∀ x, 0 ≤ p x) (y : Y) : 0 ≤ pushforward M p y :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hp x) (hM.nonneg x y)

lemma pushforward_sum_one {M : Matrix X Y ℝ} (hM : IsKernel M)
    {p : X → ℝ} (hp : ∑ x, p x = 1) : ∑ y, pushforward M p y = 1 := by
  simp only [pushforward_apply]
  rw [Finset.sum_comm]
  have : ∀ x, ∑ y, p x * M x y = p x := by
    intro x
    rw [← Finset.mul_sum, hM.row_sum_one x, mul_one]
  rw [Finset.sum_congr rfl fun x _ => this x, hp]

/-! ## §2. Gibbs' inequality -/

/-- **Gibbs' inequality**: relative entropy is nonnegative on probability
vectors (reference strictly positive; state may touch zero). -/
theorem klDiv_nonneg {p q : X → ℝ} (hp : ∀ x, 0 ≤ p x)
    (hq : ∀ x, 0 < q x) (hps : ∑ x, p x = 1) (hqs : ∑ x, q x = 1) :
    0 ≤ klDiv p q := by
  have key : ∀ x, p x - q x ≤ p x * Real.log (p x / q x) := by
    intro x
    rcases eq_or_lt_of_le (hp x) with h0 | hpos
    · rw [← h0]
      simp only [zero_mul]
      linarith [(hq x).le]
    · have hlog : Real.log (q x / p x) ≤ q x / p x - 1 :=
        Real.log_le_sub_one_of_pos (div_pos (hq x) hpos)
      have hrev : Real.log (q x / p x) = -Real.log (p x / q x) := by
        rw [← Real.log_inv, inv_div]
      rw [hrev] at hlog
      have := mul_le_mul_of_nonneg_left
        (neg_le_neg hlog) hpos.le
      -- this : p x * (1 - q x / p x) ≤ p x * log (p x / q x)
      have hexp : p x * (1 - q x / p x) = p x - q x := by
        field_simp
      rw [neg_neg, neg_sub] at this
      rw [← hexp]
      exact this
  calc (0 : ℝ) = (∑ x, p x) - (∑ x, q x) := by rw [hps, hqs]; ring
    _ = ∑ x, (p x - q x) := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ x, p x * Real.log (p x / q x) :=
        Finset.sum_le_sum fun x _ => key x
    _ = klDiv p q := rfl

/-! ## §3. The Data-Processing Inequality -/

/-- **The classical data-processing inequality**: pushing both state and
reference through a channel cannot increase relative entropy. Proven by
Jensen's inequality applied to the convex function `t ↦ t·log t`
(`Real.convexOn_mul_log`), with weights given by the reference-weighted
channel. The general classical DPI — the foundation for observational
entropy's second laws. -/
theorem klDiv_dpi (M : Matrix X Y ℝ) (hM : IsKernel M)
    (p q : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 < q x)
    (hqM : ∀ y, 0 < pushforward M q y) :
    klDiv (pushforward M p) (pushforward M q) ≤ klDiv p q := by
  -- Per-outcome Jensen step.
  have key : ∀ y, pushforward M p y
        * Real.log (pushforward M p y / pushforward M q y)
      ≤ ∑ x, (q x * M x y) * ((p x / q x) * Real.log (p x / q x)) := by
    intro y
    have hDpos : 0 < pushforward M q y := hqM y
    have hw0 : ∀ x ∈ Finset.univ, 0 ≤ q x * M x y / pushforward M q y :=
      fun x _ => div_nonneg (mul_nonneg (hq x).le (hM.nonneg x y))
        hDpos.le
    have hw1 : ∑ x, q x * M x y / pushforward M q y = 1 := by
      rw [← Finset.sum_div]
      exact div_self (ne_of_gt hDpos)
    have hmem : ∀ x ∈ Finset.univ, p x / q x ∈ Set.Ici (0 : ℝ) :=
      fun x _ => Set.mem_Ici.mpr (div_nonneg (hp x) (hq x).le)
    have hjen := Real.convexOn_mul_log.map_sum_le hw0 hw1 hmem
    simp only [smul_eq_mul] at hjen
    have hmean : ∑ x, (q x * M x y / pushforward M q y) * (p x / q x)
        = pushforward M p y / pushforward M q y := by
      have hterm : ∀ x, (q x * M x y / pushforward M q y) * (p x / q x)
          = p x * M x y / pushforward M q y := by
        intro x
        have hqx : q x ≠ 0 := (hq x).ne'
        field_simp <;> try ring
      rw [Finset.sum_congr rfl fun x _ => hterm x, ← Finset.sum_div]
      rfl
    rw [hmean] at hjen
    -- Multiply Jensen by the positive mass `pushforward M q y`.
    have hmul := mul_le_mul_of_nonneg_left hjen hDpos.le
    have hL : pushforward M q y
        * (pushforward M p y / pushforward M q y
          * Real.log (pushforward M p y / pushforward M q y))
        = pushforward M p y
          * Real.log (pushforward M p y / pushforward M q y) := by
      rw [← mul_assoc, mul_div_cancel₀ _ (ne_of_gt hDpos)]
    have hR : pushforward M q y
        * ∑ x, (q x * M x y / pushforward M q y)
            * (p x / q x * Real.log (p x / q x))
        = ∑ x, (q x * M x y) * ((p x / q x) * Real.log (p x / q x)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hD : pushforward M q y ≠ 0 := ne_of_gt hDpos
      field_simp <;> try ring
    rw [hL, hR] at hmul
    exact hmul
  -- Sum over outcomes and untangle the double sum.
  calc klDiv (pushforward M p) (pushforward M q)
      = ∑ y, pushforward M p y
          * Real.log (pushforward M p y / pushforward M q y) := rfl
    _ ≤ ∑ y, ∑ x, (q x * M x y)
          * ((p x / q x) * Real.log (p x / q x)) :=
        Finset.sum_le_sum fun y _ => key y
    _ = ∑ x, ∑ y, (q x * M x y)
          * ((p x / q x) * Real.log (p x / q x)) := Finset.sum_comm
    _ = ∑ x, q x * ((p x / q x) * Real.log (p x / q x)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_mul, ← Finset.mul_sum, hM.row_sum_one x, mul_one]
    _ = klDiv p q := by
        refine Finset.sum_congr rfl fun x _ => ?_
        have hqx : q x ≠ 0 := (hq x).ne'
        rw [← mul_assoc, mul_div_cancel₀ _ hqx]

/-! ## §4. Observational entropy -/

/-- Measured relative entropy: the informational value of the
measurement `M` for distinguishing `p` from the prior `τ`. -/
noncomputable def measuredKL (M : Matrix X Y ℝ) (p τ : X → ℝ) : ℝ :=
  klDiv (pushforward M p) (pushforward M τ)

/-- **Observational entropy with a MaxEnt prior** (classical form of
arXiv:2503.15612 Eq. 10): `S_M^τ(p) = S(τ) − D_M(p‖τ)`. -/
noncomputable def observationalEntropy (M : Matrix X Y ℝ) (τ p : X → ℝ) :
    ℝ := shannonEntropy τ - measuredKL M p τ

theorem observationalEntropy_def (M : Matrix X Y ℝ) (τ p : X → ℝ) :
    observationalEntropy M τ p = shannonEntropy τ - measuredKL M p τ :=
  rfl

theorem measuredKL_nonneg (M : Matrix X Y ℝ) (hM : IsKernel M)
    {p τ : X → ℝ} (hp : ∀ x, 0 ≤ p x) (hτ : ∀ x, 0 < τ x)
    (hps : ∑ x, p x = 1) (hτs : ∑ x, τ x = 1)
    (hτM : ∀ y, 0 < pushforward M τ y) :
    0 ≤ measuredKL M p τ :=
  klDiv_nonneg (pushforward_nonneg hM hp) hτM
    (pushforward_sum_one hM hps) (pushforward_sum_one hM hτs)

/-- Measurement is a channel: `D_M(p‖τ) ≤ D(p‖τ)`. -/
theorem measuredKL_le_klDiv (M : Matrix X Y ℝ) (hM : IsKernel M)
    {p τ : X → ℝ} (hp : ∀ x, 0 ≤ p x) (hτ : ∀ x, 0 < τ x)
    (hτM : ∀ y, 0 < pushforward M τ y) :
    measuredKL M p τ ≤ klDiv p τ :=
  klDiv_dpi M hM p τ hp hτ hτM

/-- `S_M^τ(p) ≤ S(τ)`: a measurement cannot report more missing
information than the prior contains. -/
theorem observationalEntropy_le_prior (M : Matrix X Y ℝ)
    (hM : IsKernel M) {p τ : X → ℝ} (hp : ∀ x, 0 ≤ p x)
    (hτ : ∀ x, 0 < τ x) (hps : ∑ x, p x = 1) (hτs : ∑ x, τ x = 1)
    (hτM : ∀ y, 0 < pushforward M τ y) :
    observationalEntropy M τ p ≤ shannonEntropy τ := by
  have := measuredKL_nonneg M hM hp hτ hps hτs hτM
  unfold observationalEntropy
  linarith

/-- `S_M^τ(p) ≥ S(τ) − D(p‖τ)`: the open-system bound (classical Eq. 22
of the paper) — the coarse view can lose, never manufacture,
distinguishability. -/
theorem observationalEntropy_ge (M : Matrix X Y ℝ) (hM : IsKernel M)
    {p τ : X → ℝ} (hp : ∀ x, 0 ≤ p x) (hτ : ∀ x, 0 < τ x)
    (hτM : ∀ y, 0 < pushforward M τ y) :
    shannonEntropy τ - klDiv p τ ≤ observationalEntropy M τ p := by
  have := measuredKL_le_klDiv M hM hp hτ hτM
  unfold observationalEntropy
  linarith

/-! ## §5. The Bayes lift (T2) -/

/-- The prior-conditioned recovery kernel (classical Petz / Bayes
inverse): `Λ_τ(x|y) = τ(x)·M(x,y) / (τM)(y)`. -/
noncomputable def bayesLift (M : Matrix X Y ℝ) (τ : X → ℝ) :
    Matrix Y X ℝ := fun y x => τ x * M x y / pushforward M τ y

/-- The Bayes lift is a kernel (rows are the posterior fiber laws). -/
theorem bayesLift_isKernel (M : Matrix X Y ℝ) (hM : IsKernel M)
    {τ : X → ℝ} (hτ : ∀ x, 0 ≤ τ x)
    (hτM : ∀ y, 0 < pushforward M τ y) :
    IsKernel (bayesLift M τ) where
  nonneg := fun y x => div_nonneg
    (mul_nonneg (hτ x) (hM.nonneg x y)) (hτM y).le
  row_sum_one := by
    intro y
    unfold bayesLift
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (hτM y))

/-- **Reconstruction identity**: lifting the prior's observation
statistics returns the prior — `(τM)·Λ_τ = τ`. -/
theorem bayesLift_reconstructs_prior (M : Matrix X Y ℝ)
    (hM : IsKernel M) {τ : X → ℝ}
    (hτM : ∀ y, 0 < pushforward M τ y) :
    Matrix.vecMul (pushforward M τ) (bayesLift M τ) = τ := by
  funext x
  have : Matrix.vecMul (pushforward M τ) (bayesLift M τ) x
      = ∑ y, pushforward M τ y * (τ x * M x y / pushforward M τ y) :=
    rfl
  rw [this]
  have hterm : ∀ y, pushforward M τ y
      * (τ x * M x y / pushforward M τ y) = τ x * M x y := by
    intro y
    rw [mul_div_assoc']
    rw [mul_comm (pushforward M τ y) (τ x * M x y)]
    rw [mul_div_assoc, div_self (ne_of_gt (hτM y)), mul_one]
  rw [Finset.sum_congr rfl fun y _ => hterm y, ← Finset.mul_sum,
      hM.row_sum_one x, mul_one]

/-- The deterministic readout channel of a map `π`. -/
def detChannel (pi_map : X → Y) : Matrix X Y ℝ :=
  fun x y => if pi_map x = y then 1 else 0

theorem detChannel_isKernel (pi_map : X → Y) :
    IsKernel (detChannel pi_map) where
  nonneg := by
    intro x y
    unfold detChannel
    by_cases h : pi_map x = y <;> simp [h]
  row_sum_one := by
    intro x
    unfold detChannel
    simp

/-- **The Bayes lift of a deterministic readout is `Compatible`**: the
posterior fiber law of `y` is supported on `π⁻¹(y)` and lift-then-read
is the identity. This welds the entropic recovery object (T2) to the
telescope theorems (`DeterministicReadout`): the recovery map that the
observational-entropy literature builds from `(M, τ)` IS a lifting
kernel in the sense of the observation intertwining stack. -/
theorem bayesLift_deterministic_compatible (pi_map : X → Y)
    {τ : X → ℝ}
    (hτM : ∀ y, 0 < pushforward (detChannel pi_map) τ y) :
    Compatible pi_map (bayesLift (detChannel pi_map) τ) := by
  intro y y'
  have hpush : ∀ z : Y, pushforward (detChannel pi_map) τ z
      = ∑ x ∈ Finset.univ.filter (fun x => pi_map x = z), τ x := by
    intro z
    rw [pushforward_apply, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold detChannel
    by_cases h : pi_map x = z <;> simp [h]
  by_cases hyy : y' = y
  · rw [if_pos hyy]
    have hterm : ∀ x ∈ Finset.univ.filter (fun x => pi_map x = y'),
        bayesLift (detChannel pi_map) τ y x
          = τ x / pushforward (detChannel pi_map) τ y := by
      intro x hx
      have hπ : pi_map x = y := ((Finset.mem_filter.mp hx).2).trans hyy
      unfold bayesLift detChannel
      rw [if_pos hπ, mul_one]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
    have h2 : (∑ x ∈ Finset.univ.filter (fun x => pi_map x = y'), τ x)
        = pushforward (detChannel pi_map) τ y := by
      rw [← hpush y', hyy]
    rw [h2]
    exact div_self (ne_of_gt (hτM y))
  · rw [if_neg hyy]
    refine Finset.sum_eq_zero fun x hx => ?_
    have hπ : pi_map x = y' := (Finset.mem_filter.mp hx).2
    have hne : pi_map x ≠ y := by rw [hπ]; exact hyy
    unfold bayesLift detChannel
    rw [if_neg hne, mul_zero, zero_div]

/-! ## §6. Static information-loss composition (G1)

The Blackwell-flavored monotonicity: composing channels can only lose
distinguishability, hence observational entropy is MONOTONE along the
ladder — a coarser telescope reports more missing information. The
static twin of `composite_observation_horizon`. -/

variable {Z : Type*} [Fintype Z] [DecidableEq Z]

lemma pushforward_comp (M : Matrix X Y ℝ) (N : Matrix Y Z ℝ)
    (p : X → ℝ) :
    pushforward (M * N) p = pushforward N (pushforward M p) := by
  unfold pushforward
  rw [Matrix.vecMul_vecMul]

/-- **Static loss composes monotonically**: measuring through a longer
ladder distinguishes less. `D_{M·N}(p‖τ) ≤ D_M(p‖τ)`. -/
theorem measuredKL_comp_le (M : Matrix X Y ℝ) (N : Matrix Y Z ℝ)
    (hM : IsKernel M) (hN : IsKernel N) {p τ : X → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hτM : ∀ y, 0 < pushforward M τ y)
    (hτMN : ∀ z, 0 < pushforward N (pushforward M τ) z) :
    measuredKL (M * N) p τ ≤ measuredKL M p τ := by
  unfold measuredKL
  rw [pushforward_comp, pushforward_comp]
  exact klDiv_dpi N hN (pushforward M p) (pushforward M τ)
    (pushforward_nonneg hM hp) hτM hτMN

/-- **Observational entropy is monotone along the ladder**:
`S_{M·N}^τ(p) ≥ S_M^τ(p)`. Every additional readout stage can only
increase the reported missing information. (G1: the static composition
law, completing the square calculus's Blackwell face at the level the
finite theory supports.) -/
theorem observationalEntropy_comp_ge (M : Matrix X Y ℝ)
    (N : Matrix Y Z ℝ) (hM : IsKernel M) (hN : IsKernel N)
    {p τ : X → ℝ} (hp : ∀ x, 0 ≤ p x)
    (hτM : ∀ y, 0 < pushforward M τ y)
    (hτMN : ∀ z, 0 < pushforward N (pushforward M τ) z) :
    observationalEntropy M τ p ≤ observationalEntropy (M * N) τ p := by
  unfold observationalEntropy
  have := measuredKL_comp_le M N hM hN hp hτM hτMN
  linarith

/-! ## §7. The static ledger (Phase II, Workstream C)

`staticLoss M τ p = D(p‖τ) − D(Mp‖Mτ)`: the distinguishability lost at
one measurement stage. The STATIC LEDGER composes exactly — a chain
rule, not a bound — pairing with the dynamic ledger's
`composite_defect_identity`. Together a receipt can answer: what was
LOST through each stage (static), and which stage stops commuting with
evolution (dynamic). -/

/-- Stage-wise information loss relative to a prior. -/
noncomputable def staticLoss (M : Matrix X Y ℝ) (τ p : X → ℝ) : ℝ :=
  klDiv p τ - measuredKL M p τ

/-- Each stage's loss is nonnegative (DPI). -/
theorem staticLoss_nonneg (M : Matrix X Y ℝ) (hM : IsKernel M)
    {p τ : X → ℝ} (hp : ∀ x, 0 ≤ p x) (hτ : ∀ x, 0 < τ x)
    (hτM : ∀ y, 0 < pushforward M τ y) :
    0 ≤ staticLoss M τ p := by
  unfold staticLoss
  have := measuredKL_le_klDiv M hM hp hτ hτM
  linarith

/-- **The static composition law** (exact chain rule, not a bound):
`Δ_{M·N}^τ(p) = Δ_M^τ(p) + Δ_N^{Mτ}(Mp)`. Losses along a ladder add
stage by stage, each stage priced against the pushed-forward prior. -/
theorem staticLoss_comp (M : Matrix X Y ℝ) (N : Matrix Y Z ℝ)
    (τ p : X → ℝ) :
    staticLoss (M * N) τ p
      = staticLoss M τ p
        + staticLoss N (pushforward M τ) (pushforward M p) := by
  unfold staticLoss measuredKL
  rw [pushforward_comp, pushforward_comp]
  ring

end SGC.Observation
