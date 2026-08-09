/-
Copyright (c) 2024 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Project
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Basic

/-!
# Scalar ODE Lemmas for Energy Methods

This file contains scalar ODE lemmas used in the Lyapunov/energy method approach
to proving semigroup decay bounds. The key result is the Grönwall-type decay lemma.

## Main Results

* `gronwall_decay`: If `f' ≤ -c * f` for `c > 0`, then `f(t) ≤ f(0) * e^{-ct}`.

## Strategy

The proof uses the auxiliary function `g(t) = f(t) * e^{ct}`. If `f' ≤ -c * f`,
then `g' = (f' + c * f) * e^{ct} ≤ 0`, so `g` is non-increasing. Hence
`g(t) ≤ g(0) = f(0)`, which gives `f(t) ≤ f(0) * e^{-ct}`.
-/

noncomputable section
open Real Filter Topology Set

namespace SGC.Spectral

/-- Scalar Grönwall decay lemma: if a differentiable function satisfies
    `deriv f t ≤ -c * f t` for all `t ≥ 0` and `c > 0`, then
    `f t ≤ f 0 * exp (-c * t)` for all `t ≥ 0`.
    
    This is the core ODE lemma for the Lyapunov/energy method. -/
lemma gronwall_decay
    {f : ℝ → ℝ} {c : ℝ}
    (hc_pos : 0 < c)
    (hf_diff : Differentiable ℝ f)
    (h_deriv : ∀ t ≥ 0, deriv f t ≤ -c * f t) :
    ∀ t ≥ 0, f t ≤ f 0 * Real.exp (-c * t) := by
  intro t ht
  -- ══════════════════════════════════════════════════════════════════════════
  -- Define auxiliary function g(t) = f(t) * exp(c * t)
  -- ══════════════════════════════════════════════════════════════════════════
  let g : ℝ → ℝ := fun s => f s * Real.exp (c * s)
  
  -- ══════════════════════════════════════════════════════════════════════════
  -- Step 1: g is differentiable and we can compute its derivative explicitly
  -- ══════════════════════════════════════════════════════════════════════════
  
  -- Derivative of exp(c * s) at any point s
  -- d/ds exp(c*s) = c * exp(c*s)
  have h_exp_deriv : ∀ s, HasDerivAt (fun x => Real.exp (c * x)) (c * Real.exp (c * s)) s := by
    intro s
    -- First: d/ds (c*s) = c using const_mul
    have h1 : HasDerivAt (fun x => c * x) c s := by
      have := (hasDerivAt_id s).const_mul c
      simp only [mul_one] at this
      exact this
    -- Then compose with exp: d/ds exp(c*s) = exp(c*s) * c
    have h2 := h1.exp
    -- h2 : HasDerivAt (fun x => exp(c*x)) (exp(c*s) * c) s
    -- We need c * exp(c*s), so use mul_comm
    convert h2 using 1
    ring
  
  -- g is differentiable
  have hg_diff : Differentiable ℝ g := by
    intro s
    exact (hf_diff s).mul (h_exp_deriv s).differentiableAt
  
  -- Explicit derivative of g using product rule:
  -- g'(s) = f'(s) * exp(cs) + f(s) * c * exp(cs) = (f'(s) + c * f(s)) * exp(cs)
  have hg_hasderiv : ∀ s, HasDerivAt g ((deriv f s + c * f s) * Real.exp (c * s)) s := by
    intro s
    have hf_at : HasDerivAt f (deriv f s) s := (hf_diff s).hasDerivAt
    have hexp_at : HasDerivAt (fun x => Real.exp (c * x)) (c * Real.exp (c * s)) s := 
      h_exp_deriv s
    -- Product rule: (f * exp)'(s) = f'(s) * exp(cs) + f(s) * c * exp(cs)
    have h_prod := hf_at.mul hexp_at
    -- h_prod : HasDerivAt g (deriv f s * exp(cs) + f s * (c * exp(cs))) s
    -- We need to show this equals (deriv f s + c * f s) * exp(cs)
    convert h_prod using 1
    ring
  
  have hg_deriv_eq : ∀ s, deriv g s = (deriv f s + c * f s) * Real.exp (c * s) := by
    intro s
    exact (hg_hasderiv s).deriv
  
  -- ══════════════════════════════════════════════════════════════════════════
  -- Step 2: Show g' ≤ 0 on [0, ∞) using the derivative bound on f
  -- ══════════════════════════════════════════════════════════════════════════
  have hg_deriv_nonpos : ∀ s ∈ Ioo 0 t, deriv g s ≤ 0 := by
    intro s ⟨hs_pos, hs_lt⟩
    rw [hg_deriv_eq]
    -- From h_deriv: deriv f s ≤ -c * f s for s ≥ 0
    have hs_nonneg : s ≥ 0 := le_of_lt hs_pos
    have h_f_bound : deriv f s ≤ -c * f s := h_deriv s hs_nonneg
    -- So deriv f s + c * f s ≤ 0
    have h_sum_nonpos : deriv f s + c * f s ≤ 0 := by linarith
    -- exp(cs) > 0
    have h_exp_pos : 0 < Real.exp (c * s) := Real.exp_pos _
    -- (nonpos) * (pos) ≤ 0
    exact mul_nonpos_of_nonpos_of_nonneg h_sum_nonpos (le_of_lt h_exp_pos)
  
  -- ══════════════════════════════════════════════════════════════════════════
  -- Step 3: Use Mean Value Theorem to show g(t) ≤ g(0)
  -- ══════════════════════════════════════════════════════════════════════════
  have hg_bound : g t ≤ g 0 := by
    by_cases ht_eq : t = 0
    · -- If t = 0, trivially g(t) = g(0)
      simp [ht_eq]
    · -- If t > 0, apply MVT
      have ht_pos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht_eq)
      -- g is continuous on [0, t]
      have hg_cont : ContinuousOn g (Icc 0 t) := hg_diff.continuous.continuousOn
      -- g is differentiable on (0, t)
      have hg_diff_on : DifferentiableOn ℝ g (Ioo 0 t) := hg_diff.differentiableOn
      -- By MVT: ∃ ξ ∈ (0, t), deriv g ξ = (g t - g 0) / (t - 0)
      obtain ⟨ξ, hξ_mem, hξ_eq⟩ := exists_deriv_eq_slope g ht_pos hg_cont hg_diff_on
      -- hξ_eq : deriv g ξ = (g t - g 0) / (t - 0)
      -- Rearranging: g t - g 0 = deriv g ξ * t
      have ht_ne : t - 0 ≠ 0 := by linarith
      have h_diff : g t - g 0 = deriv g ξ * t := by
        have := hξ_eq
        field_simp at this ⊢
        linarith
      -- Since deriv g ξ ≤ 0 and t > 0, we have g t - g 0 ≤ 0
      have h_deriv_neg : deriv g ξ ≤ 0 := hg_deriv_nonpos ξ hξ_mem
      have h_diff_neg : g t - g 0 ≤ 0 := by
        rw [h_diff]
        exact mul_nonpos_of_nonpos_of_nonneg h_deriv_neg (le_of_lt ht_pos)
      linarith
  
  -- ══════════════════════════════════════════════════════════════════════════
  -- Step 4: Unpack g to get the desired inequality for f
  -- ══════════════════════════════════════════════════════════════════════════
  -- hg_bound : g(t) ≤ g(0), i.e., f(t) * exp(ct) ≤ f(0) * exp(0) = f(0)
  -- First simplify g(0) = f(0) * exp(0) = f(0) * 1 = f(0)
  have hg0 : g 0 = f 0 := by
    show f 0 * Real.exp (c * 0) = f 0
    simp only [mul_zero, Real.exp_zero, mul_one]
  -- Combine: f(t) * exp(ct) ≤ f(0)
  have h_ineq : f t * Real.exp (c * t) ≤ f 0 := by
    calc f t * Real.exp (c * t) = g t := rfl
      _ ≤ g 0 := hg_bound
      _ = f 0 := hg0
  -- Divide by exp(ct) > 0:
  have h_exp_pos : 0 < Real.exp (c * t) := Real.exp_pos _
  -- f(t) ≤ f(0) / exp(ct) = f(0) * exp(-ct)
  calc f t = f t * Real.exp (c * t) / Real.exp (c * t) := by 
        field_simp [ne_of_gt h_exp_pos]
    _ ≤ f 0 / Real.exp (c * t) := by
        apply div_le_div_of_nonneg_right h_ineq (le_of_lt h_exp_pos)
    _ = f 0 * Real.exp (-(c * t)) := by rw [Real.exp_neg]; field_simp
    _ = f 0 * Real.exp (-c * t) := by ring_nf

/-- Variant: Grönwall for non-negative functions.
    Often useful when the energy E(t) ≥ 0 is known a priori. -/
lemma gronwall_decay_nonneg
    {f : ℝ → ℝ} {c : ℝ}
    (hc_pos : 0 < c)
    (hf_diff : Differentiable ℝ f)
    (_hf_nonneg : ∀ t ≥ 0, 0 ≤ f t)
    (h_deriv : ∀ t ≥ 0, deriv f t ≤ -c * f t) :
    ∀ t ≥ 0, f t ≤ f 0 * Real.exp (-c * t) :=
  gronwall_decay hc_pos hf_diff h_deriv

/-- sqrt(exp(-2ct)) = exp(-ct) for use in energy decay. -/
lemma sqrt_exp_neg_two_mul (c t : ℝ) :
    Real.sqrt (Real.exp (-2 * c * t)) = Real.exp (-c * t) := by
  have h : Real.exp (-2 * c * t) = Real.exp (-c * t) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [h, Real.sqrt_sq (Real.exp_nonneg _)]

/-- Grönwall for energy: E(t) ≥ 0 and E' ≤ -2*gap*E implies norm decay.
    This is the form we'll apply in the sector bound proof. -/
lemma energy_decay_implies_norm_decay
    {E : ℝ → ℝ} {gap : ℝ}
    (hgap_pos : 0 < gap)
    (hE_diff : Differentiable ℝ E)
    (hE_nonneg : ∀ t ≥ 0, 0 ≤ E t)
    (h_deriv : ∀ t ≥ 0, deriv E t ≤ -2 * gap * E t) :
    ∀ t ≥ 0, Real.sqrt (E t) ≤ Real.sqrt (E 0) * Real.exp (-gap * t) := by
  intro t ht
  -- First apply Grönwall to E with c = 2*gap
  have hc : 0 < 2 * gap := by linarith
  -- Need to convert -2 * gap * E t to -(2 * gap) * E t
  have h_deriv' : ∀ t ≥ 0, deriv E t ≤ -(2 * gap) * E t := by
    intro s hs
    have := h_deriv s hs
    linarith
  have h_E_decay := gronwall_decay hc hE_diff h_deriv' t ht
  -- E(t) ≤ E(0) * exp(-2*gap*t)
  -- Taking square roots: sqrt(E(t)) ≤ sqrt(E(0) * exp(-2*gap*t))
  have h1 : Real.sqrt (E t) ≤ Real.sqrt (E 0 * Real.exp (-(2 * gap) * t)) := 
    Real.sqrt_le_sqrt h_E_decay
  -- sqrt(a * b) = sqrt(a) * sqrt(b) for a ≥ 0
  have h2 : Real.sqrt (E 0 * Real.exp (-(2 * gap) * t)) = 
            Real.sqrt (E 0) * Real.sqrt (Real.exp (-(2 * gap) * t)) := 
    Real.sqrt_mul (hE_nonneg 0 (le_refl 0)) _
  -- sqrt(exp(-2*gap*t)) = exp(-gap*t)
  have h3 : Real.sqrt (Real.exp (-(2 * gap) * t)) = Real.exp (-gap * t) := by
    have : -(2 * gap) * t = -2 * gap * t := by ring
    rw [this, sqrt_exp_neg_two_mul]
  rw [h2, h3] at h1
  exact h1

end SGC.Spectral

end
