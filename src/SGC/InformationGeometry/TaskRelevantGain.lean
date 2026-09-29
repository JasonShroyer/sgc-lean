import SGC.InformationGeometry.Calibration

noncomputable section

namespace SGC.InformationGeometry.TaskRelevantGain

open Finset Calibration

set_option linter.unusedSectionVars false

variable {Ω β γ δ : Type*} [Fintype Ω] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]

variable (q : Ω → β) (f : β → γ) (w Z : Ω → ℝ)

def gain : ℝ :=
  ∑ ω, w ω * (blockMean q w Z (q ω) - blockMean (f ∘ q) w Z (f (q ω))) ^ 2

theorem within_coarse_eq_within_fine_add_gain (hw : ∀ ω, 0 < w ω) :
    within (f ∘ q) w Z = within q w Z + gain q f w Z := by
  exact brier_eq_within_add_reliability q w Z hw (fun b => blockMean (f ∘ q) w Z (f b))

theorem gain_eq_risk_reduction (hw : ∀ ω, 0 < w ω) :
    gain q f w Z = within (f ∘ q) w Z - within q w Z := by
  have h := within_coarse_eq_within_fine_add_gain q f w Z hw
  linarith

theorem gain_nonneg (hw : ∀ ω, 0 ≤ w ω) : 0 ≤ gain q f w Z :=
  Finset.sum_nonneg (fun ω _ => mul_nonneg (hw ω) (sq_nonneg _))

theorem within_fine_le_coarse (hw : ∀ ω, 0 < w ω) :
    within q w Z ≤ within (f ∘ q) w Z := by
  rw [within_coarse_eq_within_fine_add_gain q f w Z hw]
  exact le_add_of_nonneg_right (gain_nonneg q f w Z (fun ω => (hw ω).le))

theorem gain_eq_zero_iff (hw : ∀ ω, 0 < w ω) :
    gain q f w Z = 0 ↔
      ∀ ω, blockMean q w Z (q ω) = blockMean (f ∘ q) w Z (f (q ω)) := by
  constructor
  · intro h ω
    have ht := (Finset.sum_eq_zero_iff_of_nonneg (fun ω _ =>
      mul_nonneg (hw ω).le (sq_nonneg _))).mp h ω (Finset.mem_univ ω)
    have hs := (mul_eq_zero.mp ht).resolve_left (hw ω).ne'
    nlinarith [sq_nonneg (blockMean q w Z (q ω) - blockMean (f ∘ q) w Z (f (q ω)))]
  · intro h
    unfold gain
    simp [h]

theorem gain_pos_iff (hw : ∀ ω, 0 < w ω) :
    0 < gain q f w Z ↔
      ∃ ω, blockMean q w Z (q ω) ≠ blockMean (f ∘ q) w Z (f (q ω)) := by
  rw [lt_iff_le_and_ne]
  simp only [gain_nonneg q f w Z (fun ω => (hw ω).le), true_and, ne_eq]
  rw [eq_comm, gain_eq_zero_iff q f w Z hw]
  push_neg
  rfl

theorem gain_chain (g : γ → δ) (hw : ∀ ω, 0 < w ω) :
    gain q (g ∘ f) w Z = gain q f w Z + gain (f ∘ q) g w Z := by
  rw [gain_eq_risk_reduction q (g ∘ f) w Z hw,
    gain_eq_risk_reduction q f w Z hw, gain_eq_risk_reduction (f ∘ q) g w Z hw]
  have h : (g ∘ f) ∘ q = g ∘ (f ∘ q) := rfl
  rw [h]
  ring

theorem calibrated_report_improvement (hw : ∀ ω, 0 < w ω)
    (fine : β → ℝ) (coarse : γ → ℝ)
    (hf : IsCalibrated q w Z fine) (hc : IsCalibrated (f ∘ q) w Z coarse) :
    brier (f ∘ q) w Z coarse - brier q w Z fine = gain q f w Z := by
  rw [brier_eq_within_of_calibrated q w Z hw fine hf,
    brier_eq_within_of_calibrated (f ∘ q) w Z hw coarse hc,
    gain_eq_risk_reduction q f w Z hw]

end SGC.InformationGeometry.TaskRelevantGain
