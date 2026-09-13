/-
Copyright (c) 2026 Jason Shroyer. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen

/-!
# The Log-Sum Engine

The two finite inequalities that power the Three Arrows sprint
(`docs/three-arrows-design.md`): the classical **log-sum inequality** and
its two-sided **Gibbs superadditivity** corollary. Both are pure finite
convexity (Jensen for `x ↦ x·log x`, `Real.convexOn_mul_log`), stated with
Lean's junk-value conventions handled (`0·log(0/b) = 0`, empty sums).

These are the shared engine for retiring the two thermodynamic axioms in
`SGC.Thermodynamics.EntropyProduction`:
* `data_processing_inequality` — log-sum applied fiberwise along a
  deterministic pushforward;
* `hidden_entropy_nonneg` — Gibbs superadditivity applied per coarse block
  pair of the Schnakenberg sum.
-/

namespace SGC.Thermodynamics.LogSum

open Finset

variable {ι : Type*}

/-- **The log-sum inequality.** For nonnegative `a` and positive `b` on a
finite index set, `(Σa)·log(Σa/Σb) ≤ Σ aᵢ·log(aᵢ/bᵢ)`. Jensen for the
convex function `x ↦ x·log x` with weights `bᵢ` at points `aᵢ/bᵢ`. -/
theorem log_sum_inequality (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i)) ≤
      ∑ i ∈ s, a i * Real.log (a i / b i) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hB : 0 < ∑ i ∈ s, b i := Finset.sum_pos hb hs
  have hjensen := (Real.convexOn_mul_log).map_centerMass_le
    (t := s) (w := b) (p := fun i => a i / b i)
    (fun i hi => (hb i hi).le) hB
    (fun i hi => Set.mem_Ici.mpr (div_nonneg (ha i hi) (hb i hi).le))
  have hcm : s.centerMass b (fun i => a i / b i)
      = (∑ i ∈ s, a i) / (∑ i ∈ s, b i) := by
    rw [Finset.centerMass]
    have hnum : ∑ i ∈ s, b i • (a i / b i) = ∑ i ∈ s, a i :=
      Finset.sum_congr rfl fun i hi => by
        rw [smul_eq_mul, mul_comm, div_mul_cancel₀ _ (hb i hi).ne']
    rw [hnum, smul_eq_mul, inv_mul_eq_div]
  have hrhs : s.centerMass b ((fun x => x * Real.log x) ∘ fun i => a i / b i)
      = (∑ i ∈ s, b i)⁻¹ * ∑ i ∈ s, a i * Real.log (a i / b i) := by
    rw [Finset.centerMass, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    show b i • ((a i / b i) * Real.log (a i / b i)) = a i * Real.log (a i / b i)
    rw [smul_eq_mul, ← mul_assoc, mul_comm (b i), div_mul_cancel₀ _ (hb i hi).ne']
  rw [hcm, hrhs] at hjensen
  have hchain : (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i))
      = (∑ i ∈ s, b i) *
        (((∑ i ∈ s, a i) / (∑ i ∈ s, b i)) *
          Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i))) := by
    field_simp
  rw [hchain]
  calc (∑ i ∈ s, b i) *
      (((∑ i ∈ s, a i) / (∑ i ∈ s, b i)) *
        Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i)))
      ≤ (∑ i ∈ s, b i) *
        ((∑ i ∈ s, b i)⁻¹ * ∑ i ∈ s, a i * Real.log (a i / b i)) :=
        mul_le_mul_of_nonneg_left hjensen hB.le
    _ = ∑ i ∈ s, a i * Real.log (a i / b i) := by field_simp

/-- **Gibbs superadditivity.** For strictly positive `a, b` on a finite
index set, the aggregated Gibbs term is dominated by the sum of the
pointwise Gibbs terms:
`(Σa − Σb)·log(Σa/Σb) ≤ Σ (aᵢ − bᵢ)·log(aᵢ/bᵢ)`.
Two applications of the log-sum inequality, one in each direction. -/
theorem gibbs_superadditive (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) (hb : ∀ i ∈ s, 0 < b i) :
    (∑ i ∈ s, a i - ∑ i ∈ s, b i) *
        Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i)) ≤
      ∑ i ∈ s, (a i - b i) * Real.log (a i / b i) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hA : 0 < ∑ i ∈ s, a i := Finset.sum_pos ha hs
  have hB : 0 < ∑ i ∈ s, b i := Finset.sum_pos hb hs
  have h1 := log_sum_inequality s a b (fun i hi => (ha i hi).le) hb
  have h2 := log_sum_inequality s b a (fun i hi => (hb i hi).le) ha
  have hsplit : ∑ i ∈ s, (a i - b i) * Real.log (a i / b i)
      = (∑ i ∈ s, a i * Real.log (a i / b i))
        + ∑ i ∈ s, b i * Real.log (b i / a i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hlog : Real.log (b i / a i) = -Real.log (a i / b i) := by
      rw [← Real.log_inv, inv_div]
    rw [hlog]
    ring
  have hagg : (∑ i ∈ s, a i - ∑ i ∈ s, b i) *
      Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i))
      = (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i))
        + (∑ i ∈ s, b i) * Real.log ((∑ i ∈ s, b i) / (∑ i ∈ s, a i)) := by
    have hlog : Real.log ((∑ i ∈ s, b i) / (∑ i ∈ s, a i))
        = -Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i)) := by
      rw [← Real.log_inv, inv_div]
    rw [hlog]
    ring
  rw [hsplit, hagg]
  exact add_le_add h1 h2

end SGC.Thermodynamics.LogSum
