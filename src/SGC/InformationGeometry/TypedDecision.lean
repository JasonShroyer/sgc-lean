/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.InformationGeometry.DecisionValue

/-!
# Typed decisions: calibrated and closed does not imply sufficient

A typed decision induces a coarse-graining `q` of the fine state, reports a
value per block, and carries semantic labels. Three properties are kept apart:

* **closed** — by construction (the codomain `β` is declared);
* **calibrated** — the report equals the block mean of the target
  (`Calibration.IsCalibrated`);
* **sufficient** — the target is constant on every block (`within = 0`).

## Results

* `sufficientFor_iff_constant_on_fibers` — sufficiency is exactly fiber-constancy
  of the target.
* `within_rename` — relabeling the blocks by a bijection changes neither the
  within-block variance nor sufficiency: **the information content of a typed
  decision is invariant under renaming its options**. Any renaming effect on a
  deployed head (Sun–Xu) must therefore come from the head changing `q`, not from
  the schema.
* `brier_eq_within_of_calibrated'` — a calibrated report's Brier score is the
  within-block variance: calibration fixes reliability, not sufficiency.
* `calibrated_not_sufficient` — a concrete typed decision that is calibrated on
  every block and loses a quarter of the target variance. Closed + calibrated does
  not imply sufficient.
-/

noncomputable section

namespace SGC.InformationGeometry.TypedDecision

open Finset Calibration

set_option linter.unusedSectionVars false
set_option linter.dupNamespace false

/-- A typed decision on fine state `Ω` with declared option set `β`. -/
structure TypedDecision (Ω β : Type*) where
  q : Ω → β
  report : β → ℝ
  names : β → String

variable {Ω β : Type*} [Fintype Ω] [Fintype β] [DecidableEq β]
variable (d : TypedDecision Ω β) (w Y : Ω → ℝ)

def IsCalibrated : Prop := Calibration.IsCalibrated d.q w Y d.report

def SufficientFor : Prop := within d.q w Y = 0

lemma blockMean_of_const_on_fiber (hw : ∀ ω, 0 < w ω) {q : Ω → β} (b : β)
    (hc : ∀ ω, q ω = b → Y ω = c) (hb : ∃ ω, q ω = b) : blockMean q w Y b = c := by
  obtain ⟨ω₀, hω₀⟩ := hb
  unfold blockMean ScoreProjection.blockAvg
  have hM : 0 < ScoreProjection.blockMass q w b :=
    Finset.sum_pos (fun ω _ => hw ω) ⟨ω₀, by simp [hω₀]⟩
  have hnum : ∑ ω ∈ univ.filter (fun ω => q ω = b), w ω * Y ω
      = c * ScoreProjection.blockMass q w b := by
    unfold ScoreProjection.blockMass
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun ω hω => by
      rw [hc ω (Finset.mem_filter.mp hω).2]; ring)
  rw [hnum]
  field_simp

/-- **Sufficiency is fiber-constancy of the target.** -/
theorem sufficientFor_iff_constant_on_fibers (hw : ∀ ω, 0 < w ω) :
    SufficientFor d w Y ↔ ∀ ω ω', d.q ω = d.q ω' → Y ω = Y ω' := by
  unfold SufficientFor within
  constructor
  · intro h ω ω' hq
    have ht := (Finset.sum_eq_zero_iff_of_nonneg (fun ω _ =>
      mul_nonneg (hw ω).le (sq_nonneg _))).mp h
    have h1 := (mul_eq_zero.mp (ht ω (mem_univ ω))).resolve_left (hw ω).ne'
    have h2 := (mul_eq_zero.mp (ht ω' (mem_univ ω'))).resolve_left (hw ω').ne'
    have e1 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
    have e2 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    rw [hq] at e1
    linarith
  · intro h
    refine Finset.sum_eq_zero (fun ω _ => ?_)
    have : blockMean d.q w Y (d.q ω) = Y ω :=
      blockMean_of_const_on_fiber w Y hw (d.q ω) (fun ω' hω' => h ω' ω hω') ⟨ω, rfl⟩
    rw [this, sub_self]
    ring

/-- **Renaming options is information-neutral.** -/
theorem within_rename {γ : Type*} [Fintype γ] [DecidableEq γ] (σ : β → γ)
    (hσ : Function.Injective σ) (q : Ω → β) :
    within (σ ∘ q) w Y = within q w Y := by
  unfold within
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  have hfib : univ.filter (fun ω' => σ (q ω') = σ (q ω)) = univ.filter (fun ω' => q ω' = q ω) := by
    ext ω'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => hσ h, fun h => by rw [h]⟩
  have hbm : blockMean (σ ∘ q) w Y ((σ ∘ q) ω) = blockMean q w Y (q ω) := by
    unfold blockMean ScoreProjection.blockAvg ScoreProjection.blockMass
    simp only [Function.comp]
    rw [hfib]
  rw [hbm]

theorem sufficientFor_rename {γ : Type*} [Fintype γ] [DecidableEq γ] (σ : β → γ)
    (hσ : Function.Injective σ) (r : γ → ℝ) (n : γ → String) :
    SufficientFor ⟨σ ∘ d.q, r, n⟩ w Y ↔ SufficientFor d w Y := by
  unfold SufficientFor
  simp only
  rw [within_rename w Y σ hσ d.q]

/-- Calibration fixes the Brier score at the within-block floor — it says nothing
about that floor. -/
theorem brier_eq_within_of_calibrated' (hw : ∀ ω, 0 < w ω) (hc : IsCalibrated d w Y) :
    brier d.q w Y d.report = within d.q w Y :=
  Calibration.brier_eq_within_of_calibrated d.q w Y hw d.report hc

/-! ### The witness -/

/-- Two independent fair bits; the decision observes the *second* bit and reports its
block mean of the *first*. -/
def wrongBit : TypedDecision (Fin 2 × Fin 2) (Fin 2) where
  q := fun x => x.2
  report := fun _ => 1 / 2
  names := fun b => if b = 0 then "no" else "yes"

def fair : Fin 2 × Fin 2 → ℝ := fun _ => 1 / 4

def firstBit : Fin 2 × Fin 2 → ℝ := fun x => x.1.val

theorem wrongBit_calibrated : IsCalibrated wrongBit fair firstBit := by
  intro b _
  unfold blockMean ScoreProjection.blockAvg ScoreProjection.blockMass
  simp only [wrongBit, Finset.sum_filter]
  fin_cases b <;> norm_num [fair, firstBit, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem wrongBit_within : within wrongBit.q fair firstBit = 1 / 4 := by
  unfold within blockMean ScoreProjection.blockAvg ScoreProjection.blockMass
  simp only [wrongBit, Finset.sum_filter]
  norm_num [fair, firstBit, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- **Closed and calibrated does not imply sufficient.** -/
theorem calibrated_not_sufficient :
    ∃ (d : TypedDecision (Fin 2 × Fin 2) (Fin 2)) (w Y : Fin 2 × Fin 2 → ℝ),
      (∀ ω, 0 < w ω) ∧ IsCalibrated d w Y ∧ ¬ SufficientFor d w Y := by
  refine ⟨wrongBit, fair, firstBit, fun _ => by norm_num [fair], wrongBit_calibrated, ?_⟩
  unfold SufficientFor
  rw [wrongBit_within]
  norm_num

end SGC.InformationGeometry.TypedDecision
