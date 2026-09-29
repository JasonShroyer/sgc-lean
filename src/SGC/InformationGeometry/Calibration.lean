/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.InformationGeometry.ScoreProjection

/-!
# Calibration and the Murphy decomposition as coarse-graining identities

A forecaster reports a value `P b` on each block `b` of a partition `q` of a
finite outcome space with positive weights `w`; the target is `Y`. Writing
`a b` for the `w`-weighted block mean of `Y` (`ScoreProjection.blockAvg`):

* `within  = Σ w (Y − a (q ω))²`      — what no forecaster on `q` can recover;
* `reliability P = Σ w (a (q ω) − P (q ω))²` — distance of the report from its block mean;
* `brier P = Σ w (Y − P (q ω))²`.

**Murphy / DeGroot–Fienberg decomposition:** `brier P = within + reliability P`.
With a constant report `P ≡ c` this is the variance decomposition
`Σ w (Y − c)² = within + Σ w (a (q ω) − c)²` (uncertainty = within + resolution).

**Calibration** (Dawid's `E[Y | P] = P`, finite form): `P b = a b` on every
nonempty block. It holds iff `reliability P = 0`, iff `brier P = within`.

The within term is the coarse-graining loss of `ScoreProjection` with `Y` as the
score. So: uncertainty is the fine quantity, resolution the coarse quantity,
the within-block variance the loss, and reliability an *additional* term that a
report incurs by departing from the block mean. Calibration says nothing about
the within-block variance — a calibrated forecaster on an irrelevant partition
has `reliability = 0` and large `within` (decisions 0074, 0078).
-/

noncomputable section

namespace SGC.InformationGeometry.Calibration

open Finset SGC.InformationGeometry

set_option linter.unusedSectionVars false

variable {Ω β : Type*} [Fintype Ω] [Fintype β] [DecidableEq β]
variable (q : Ω → β) (w Y : Ω → ℝ)

/-- Block mean of the target. -/
def blockMean (b : β) : ℝ := ScoreProjection.blockAvg q w Y b

/-- Within-block variance of the target (the coarse-graining loss). -/
def within : ℝ := ∑ ω, w ω * (Y ω - blockMean q w Y (q ω)) ^ 2

/-- Reliability: squared distance of the report from the block mean. -/
def reliability (P : β → ℝ) : ℝ := ∑ ω, w ω * (blockMean q w Y (q ω) - P (q ω)) ^ 2

/-- Brier score of the report. -/
def brier (P : β → ℝ) : ℝ := ∑ ω, w ω * (Y ω - P (q ω)) ^ 2

/-- Resolution relative to a baseline `c`. -/
def resolution (c : ℝ) : ℝ := ∑ ω, w ω * (blockMean q w Y (q ω) - c) ^ 2

/-- Finite Dawid calibration: the report equals the block mean on nonempty blocks. -/
def IsCalibrated (P : β → ℝ) : Prop :=
  ∀ b, 0 < ScoreProjection.blockMass q w b → P b = blockMean q w Y b

lemma fiber_centered (hw : ∀ ω, 0 < w ω) (b : β) :
    ∑ ω ∈ univ.filter (fun ω => q ω = b), w ω * (Y ω - blockMean q w Y b) = 0 := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  unfold blockMean ScoreProjection.blockAvg
  by_cases hM : ScoreProjection.blockMass q w b = 0
  · have hempty : ∑ ω ∈ univ.filter (fun ω => q ω = b), w ω * Y ω = 0 :=
      ScoreProjection.blockDeriv_eq_zero_of_mass q (fun ω => w ω * Y ω) hw hM
    unfold ScoreProjection.blockMass at hM
    rw [hM, hempty]
    simp
  · unfold ScoreProjection.blockMass at hM ⊢
    field_simp
    ring

/-- **Murphy decomposition:** `brier P = within + reliability P`. -/
theorem brier_eq_within_add_reliability (hw : ∀ ω, 0 < w ω) (P : β → ℝ) :
    brier q w Y P = within q w Y + reliability q w Y P := by
  unfold brier within reliability
  have hpt : ∀ ω, w ω * (Y ω - P (q ω)) ^ 2
      = w ω * (Y ω - blockMean q w Y (q ω)) ^ 2
        + w ω * (blockMean q w Y (q ω) - P (q ω)) ^ 2
        + 2 * ((blockMean q w Y (q ω) - P (q ω)) * (w ω * (Y ω - blockMean q w Y (q ω)))) := by
    intro ω
    ring
  simp only [hpt, Finset.sum_add_distrib]
  have hcross : ∑ ω, 2 * ((blockMean q w Y (q ω) - P (q ω)) * (w ω * (Y ω - blockMean q w Y (q ω))))
      = 0 := by
    rw [← Finset.mul_sum, ScoreProjection.sum_fibers q]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero (fun b _ => ?_))
    have hconst : ∀ ω ∈ univ.filter (fun ω => q ω = b),
        (blockMean q w Y (q ω) - P (q ω)) * (w ω * (Y ω - blockMean q w Y (q ω)))
          = (blockMean q w Y b - P b) * (w ω * (Y ω - blockMean q w Y b)) := by
      intro ω hω
      rw [(Finset.mem_filter.mp hω).2]
    rw [Finset.sum_congr rfl hconst, ← Finset.mul_sum, fiber_centered q w Y hw b, mul_zero]
  rw [hcross, add_zero]

/-- **Variance decomposition:** uncertainty about any baseline = within + resolution. -/
theorem variance_eq_within_add_resolution (hw : ∀ ω, 0 < w ω) (c : ℝ) :
    ∑ ω, w ω * (Y ω - c) ^ 2 = within q w Y + resolution q w Y c :=
  brier_eq_within_add_reliability q w Y hw (fun _ => c)

lemma reliability_nonneg (hw : ∀ ω, 0 < w ω) (P : β → ℝ) : 0 ≤ reliability q w Y P :=
  Finset.sum_nonneg (fun ω _ => mul_nonneg (hw ω).le (sq_nonneg _))

/-- The within-block variance is the floor of the Brier score over all reports. -/
theorem within_le_brier (hw : ∀ ω, 0 < w ω) (P : β → ℝ) : within q w Y ≤ brier q w Y P := by
  rw [brier_eq_within_add_reliability q w Y hw P]
  linarith [reliability_nonneg q w Y hw P]

/-- **Calibration iff zero reliability.** -/
theorem reliability_eq_zero_iff (hw : ∀ ω, 0 < w ω) (P : β → ℝ) :
    reliability q w Y P = 0 ↔ IsCalibrated q w Y P := by
  unfold reliability IsCalibrated
  constructor
  · intro h0 b hb
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun ω _ =>
      mul_nonneg (hw ω).le (sq_nonneg _))).mp h0
    obtain ⟨ω, hω⟩ : ∃ ω, q ω = b := by
      by_contra hne
      push_neg at hne
      have : ScoreProjection.blockMass q w b = 0 := by
        unfold ScoreProjection.blockMass
        exact Finset.sum_eq_zero (fun ω hω => absurd (Finset.mem_filter.mp hω).2 (hne ω))
      exact absurd this hb.ne'
    have := hterm ω (Finset.mem_univ ω)
    rcases mul_eq_zero.mp this with hw0 | hsq
    · exact absurd hw0 (hw ω).ne'
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
      rw [hω] at this
      linarith
  · intro hc
    refine Finset.sum_eq_zero (fun ω _ => ?_)
    have hpos : 0 < ScoreProjection.blockMass q w (q ω) :=
      Finset.sum_pos (fun ω' _ => hw ω') ⟨ω, by simp⟩
    rw [hc (q ω) hpos, sub_self]
    ring

/-- **A calibrated report attains the floor:** `brier P = within`. -/
theorem brier_eq_within_of_calibrated (hw : ∀ ω, 0 < w ω) (P : β → ℝ)
    (hc : IsCalibrated q w Y P) : brier q w Y P = within q w Y := by
  rw [brier_eq_within_add_reliability q w Y hw P,
    (reliability_eq_zero_iff q w Y hw P).mpr hc, add_zero]

/-- **Calibration does not constrain the within-block variance.** The block-mean
report is calibrated on every partition; the loss it leaves is the partition's. -/
theorem blockMean_isCalibrated : IsCalibrated q w Y (blockMean q w Y) := fun _ _ => rfl

end SGC.InformationGeometry.Calibration
