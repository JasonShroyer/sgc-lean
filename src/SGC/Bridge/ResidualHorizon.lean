/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import Mathlib.Analysis.ODE.Gronwall

/-!
# The Residual Horizon theorem: nonlinear validity horizons are set by the residual

This is the nonlinear form of the Kernel Horizon theorem
(`SGC.Renormalization.KernelHorizon.kernel_closure_error_le`), obtained as a wrapper
around Mathlib's approximate-trajectories Gronwall lemma
(`dist_le_of_approx_trajectories_ODE_of_mem`).

## Setting

A *coarse law* is a (time-dependent) vector field `v : ℝ → E → E` on a normed space `E`,
Lipschitz with constant `K` on a region `s t`. A *coarse trajectory* `g` solves it exactly.
A *projected fine trajectory* `f` (think: `P_N u(t)`, the truncation of a true solution)
does not solve it; its **residual** is

    residual v f f' t := f' t - v t (f t),

the amount by which the projected fine dynamics fails to be autonomous in the coarse
variables. For Galerkin Navier-Stokes with `f = P_N u` and `v` the Galerkin vector field,
this residual is the closure term `C_N(u) = P_N B(u,u) - B(P_N u, P_N u)`: the effect of
unresolved modes re-entering the resolved ones (the subgrid-scale closure term of LES).

## Results

* `residual_horizon` - if the residual is bounded by `ε` on `[0, T)` and `f 0 = g 0`, then
  `dist (f t) (g t) ≤ gronwallBound 0 K ε t`, i.e. `≤ ε (e^{Kt} - 1) / K`.
* `residual_horizon_explicit` - the same with the explicit exponential.
* `exact_tracking_of_zero_residual` - zero residual forces exact tracking: the coarse law
  is exact on `[0, T]`. This is the nonlinear `ε = 0` pole: a coarse description with no
  re-entry is a closed law, with infinite validity horizon.
* `within_tolerance_of_residual_small` - the horizon reading: if
  `ε (e^{KT} - 1) / K ≤ η` then the coarse law is within tolerance `η` on all of `[0, T]`.

## What is and is not claimed

PROVEN: the statements above for arbitrary `E`, `v`, `f`, `g` satisfying the hypotheses.
The content is entirely Gronwall; the value is the *reading* and the exact hypotheses.

NOT CLAIMED: any bound on the residual for a fluid. Bounding `‖C_N(u)‖` along a
Navier-Stokes solution - in terms of the unresolved reservoir `‖(I - P_N) u‖`, of the
flux through `N`, or of anything else - is the closure problem, and is level L1 of the
ladder. Note also that on `T^3` a bounded kinetic energy bounds `‖C_N(u)‖ ≲ N · E` at
every fixed `N`, so at fixed resolution the residual stays bounded even through a
finite-energy singularity (external review, 2026-09-12): what escapes to infinity is
the resolution `N` needed for a given tolerance, not any fixed-`N` quantity.

The Lipschitz constant `K` of the Galerkin field grows with `N`; `residual_horizon` is
therefore an honest *fixed-`N`* statement, not a uniform-in-`N` one.
-/

noncomputable section

namespace SGC.Bridge.ResidualHorizon

open Set Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The residual of a trajectory `f` (with derivative `f'`) in the coarse law `v`. -/
def residual (v : ℝ → E → E) (f f' : ℝ → E) (t : ℝ) : E := f' t - v t (f t)

/-- **Residual Horizon theorem.** A projected fine trajectory `f` with residual at most `ε`
and a coarse trajectory `g` solving the coarse law exactly, agreeing at time `0`, stay
within `gronwallBound 0 K ε t` of each other on `[0, T]`. -/
theorem residual_horizon
    {v : ℝ → E → E} {s : ℝ → Set E} {K : NNReal} {f f' g : ℝ → E} {T ε : ℝ}
    (hv : ∀ t ∈ Ico 0 T, LipschitzOnWith K (v t) (s t))
    (hf : ContinuousOn f (Icc 0 T))
    (hf' : ∀ t ∈ Ico 0 T, HasDerivWithinAt f (f' t) (Ici t) t)
    (hres : ∀ t ∈ Ico 0 T, ‖residual v f f' t‖ ≤ ε)
    (hfs : ∀ t ∈ Ico 0 T, f t ∈ s t)
    (hg : ContinuousOn g (Icc 0 T))
    (hg' : ∀ t ∈ Ico 0 T, HasDerivWithinAt g (v t (g t)) (Ici t) t)
    (hgs : ∀ t ∈ Ico 0 T, g t ∈ s t)
    (h0 : f 0 = g 0) :
    ∀ t ∈ Icc 0 T, dist (f t) (g t) ≤ gronwallBound 0 K ε t := by
  intro t ht
  have h := dist_le_of_approx_trajectories_ODE_of_mem (εg := 0) (δ := 0) hv hf hf'
    (fun t ht => by simpa [dist_eq_norm, residual] using hres t ht) hfs hg hg'
    (fun t _ => by simp) hgs (by simp [h0]) t ht
  simpa using h

/-- Explicit form: `dist (f t) (g t) ≤ ε / K * (exp (K t) - 1)` for `K ≠ 0`. -/
theorem residual_horizon_explicit
    {v : ℝ → E → E} {s : ℝ → Set E} {K : NNReal} {f f' g : ℝ → E} {T ε : ℝ}
    (hK : (K : ℝ) ≠ 0)
    (hv : ∀ t ∈ Ico 0 T, LipschitzOnWith K (v t) (s t))
    (hf : ContinuousOn f (Icc 0 T))
    (hf' : ∀ t ∈ Ico 0 T, HasDerivWithinAt f (f' t) (Ici t) t)
    (hres : ∀ t ∈ Ico 0 T, ‖residual v f f' t‖ ≤ ε)
    (hfs : ∀ t ∈ Ico 0 T, f t ∈ s t)
    (hg : ContinuousOn g (Icc 0 T))
    (hg' : ∀ t ∈ Ico 0 T, HasDerivWithinAt g (v t (g t)) (Ici t) t)
    (hgs : ∀ t ∈ Ico 0 T, g t ∈ s t)
    (h0 : f 0 = g 0) :
    ∀ t ∈ Icc 0 T, dist (f t) (g t) ≤ ε / K * (exp (K * t) - 1) := by
  intro t ht
  have h := residual_horizon hv hf hf' hres hfs hg hg' hgs h0 t ht
  rw [gronwallBound_of_K_ne_0 hK] at h
  simpa using h

/-- **Exact tracking.** Zero residual forces the coarse law to be exact: the nonlinear
`ε = 0` pole, with infinite validity horizon. -/
theorem exact_tracking_of_zero_residual
    {v : ℝ → E → E} {s : ℝ → Set E} {K : NNReal} {f f' g : ℝ → E} {T : ℝ}
    (hv : ∀ t ∈ Ico 0 T, LipschitzOnWith K (v t) (s t))
    (hf : ContinuousOn f (Icc 0 T))
    (hf' : ∀ t ∈ Ico 0 T, HasDerivWithinAt f (f' t) (Ici t) t)
    (hres : ∀ t ∈ Ico 0 T, residual v f f' t = 0)
    (hfs : ∀ t ∈ Ico 0 T, f t ∈ s t)
    (hg : ContinuousOn g (Icc 0 T))
    (hg' : ∀ t ∈ Ico 0 T, HasDerivWithinAt g (v t (g t)) (Ici t) t)
    (hgs : ∀ t ∈ Ico 0 T, g t ∈ s t)
    (h0 : f 0 = g 0) :
    ∀ t ∈ Icc 0 T, f t = g t := by
  intro t ht
  have h := residual_horizon (ε := 0) hv hf hf'
    (fun t ht => by simp [hres t ht]) hfs hg hg' hgs h0 t ht
  rw [gronwallBound_ε0_δ0] at h
  exact dist_le_zero.mp h

/-- **Horizon reading.** If the accumulated residual budget `ε (e^{KT} - 1) / K` is within
tolerance `η`, the coarse law is within `η` on all of `[0, T]`: the validity horizon is at
least `T`. -/
theorem within_tolerance_of_residual_small
    {v : ℝ → E → E} {s : ℝ → Set E} {K : NNReal} {f f' g : ℝ → E} {T ε η : ℝ}
    (hK : (K : ℝ) ≠ 0)
    (hv : ∀ t ∈ Ico 0 T, LipschitzOnWith K (v t) (s t))
    (hf : ContinuousOn f (Icc 0 T))
    (hf' : ∀ t ∈ Ico 0 T, HasDerivWithinAt f (f' t) (Ici t) t)
    (hres : ∀ t ∈ Ico 0 T, ‖residual v f f' t‖ ≤ ε)
    (hε : 0 ≤ ε)
    (hfs : ∀ t ∈ Ico 0 T, f t ∈ s t)
    (hg : ContinuousOn g (Icc 0 T))
    (hg' : ∀ t ∈ Ico 0 T, HasDerivWithinAt g (v t (g t)) (Ici t) t)
    (hgs : ∀ t ∈ Ico 0 T, g t ∈ s t)
    (h0 : f 0 = g 0)
    (hbudget : ε / K * (exp (K * T) - 1) ≤ η) :
    ∀ t ∈ Icc 0 T, dist (f t) (g t) ≤ η := by
  intro t ht
  have h := residual_horizon_explicit hK hv hf hf' hres hfs hg hg' hgs h0 t ht
  have hKpos : (0 : ℝ) < K := lt_of_le_of_ne K.2 (Ne.symm hK)
  have hmono : exp (K * t) - 1 ≤ exp (K * T) - 1 := by
    have : (K : ℝ) * t ≤ K * T := mul_le_mul_of_nonneg_left ht.2 hKpos.le
    linarith [exp_le_exp.mpr this]
  have hεK : 0 ≤ ε / K := div_nonneg hε hKpos.le
  calc dist (f t) (g t) ≤ ε / K * (exp (K * t) - 1) := h
    _ ≤ ε / K * (exp (K * T) - 1) := mul_le_mul_of_nonneg_left hmono hεK
    _ ≤ η := hbudget

end SGC.Bridge.ResidualHorizon

end
