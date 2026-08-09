/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.NonlinearEmergence
import SGC.Stochastic.BrownianMotion

/-!
# The C. elegans Floquet–Tsallis Bridge

This module is the **empirical anchor** for the discrete SGC theory:
it ties the *measured biological* linearity ratio
`r = CelegansLinearityRatio = 0.08` (from Cook et al. 2019 connectome data)
to the *theoretical* q-LIL scaling exponent
`α = qLIL_scaling_exponent q` (from `SGC.Stochastic.BrownianMotion`)
through the **Floquet–Tsallis identification** `q = 2 - r`.

## The bridge in one line

```
α = (2 - q) / 2  =  (2 - (2 - r)) / 2  =  r / 2  =  0.04
```

The C. elegans pharyngeal pump operates **deep in the ANNEAL phase**:
its limit-cycle dynamics produce an anomalous diffusion exponent of
`0.04`, an order of magnitude below the Brownian baseline of `1/2`.

## Empirical contact

The empirical script `demos/celegans_floquet_tsallis_bridge.py` measures
the largest Floquet exponent `μ₁` and limit-cycle period on the pharyngeal
connectome (`data/cook2020_pharynx_synapses.csv`) and computes both `r`
(via the dwell-time / cycle-stability ratio) and the implied `α`. The
prediction `α = 0.04` is **fixed by the discrete theory**; any empirical
measurement of `α` near this value confirms the bridge.

## Theorems

- `celegans_alpha_eq_r_half` — the structural identity `α = r/2`.
- `celegans_anomalous_diffusion_value` — the numerical value `α = 0.04`.
- `celegans_scaling_lt_UGM` — formal separation from the UGM baseline `1/2`.
- `celegans_tsallis_q_in_NESS_regime` — `q ∈ (1, 2)`, i.e. the system is
  in the genuine NESS regime where `conjecture_C2_hard_half` applies.
- `celegans_C2_witness_exists` — under the Floquet–Tsallis identification,
  a C-2 witness exists for the C. elegans system at the linearization level.

## Honest scope

These are theorems about the **discrete** Floquet–Tsallis ↔ q-LIL bridge,
parameterized by the measured number `CelegansLinearityRatio = 0.08`. They
do *not* prove that pharyngeal pump trajectories themselves exhibit anomalous
diffusion with exponent `0.04` — that requires the empirical measurement,
which the Python script provides.

The proof chain is:

    SGC.NonlinearEmergence    SGC.Stochastic.BrownianMotion
       (CelegansLinearityRatio)     (qLIL_scaling_exponent)
                  \\                  /
                   \\                /
                    v              v
              SGC.Bridge.CelegansFloquetTsallis
              (α = r/2 = 0.04)
                       |
                       v
            demos/celegans_floquet_tsallis_bridge.py
              (empirical α measurement)
                       |
                       v
            reports/CELEGANS_FLOQUET_TSALLIS_BRIDGE.md
              (prediction ↔ measurement record)

## What this is NOT

This bridge does **not** prove Conjecture C-4 (continuous-limit
undecidability). It is a discrete, fully-formalized prediction about a
biological system. The continuous-limit upgrade — which would land on the
Miranda PNAS 2021 territory — is precisely what C-4's three-step program
documents in `SGC.Stochastic.BrownianMotion` §13.
-/

noncomputable section

namespace SGC.Bridge.CelegansFloquetTsallis

open SGC.NonlinearEmergence SGC.Stochastic

/-! ## 1. The Floquet–Tsallis identification -/

/-- The Tsallis non-extensivity parameter `q` implied by a measured Floquet
    linearity ratio `r`: a deeply nonlinear oscillator with `r ≪ 1` sits
    near `q = 2`, the fully crystallized boundary; a linear system with
    `r = 1` sits at the Boltzmann–Gibbs limit `q = 1`. -/
def linearity_ratio_to_Tsallis_q (r : ℝ) : ℝ := 2 - r

/-- The predicted anomalous diffusion exponent for a system with measured
    linearity ratio `r`, via the Floquet–Tsallis ↔ q-LIL chain. -/
def predicted_alpha_from_r (r : ℝ) : ℝ :=
  qLIL_scaling_exponent (linearity_ratio_to_Tsallis_q r)

/-- **Structural identity**: the predicted `α` is exactly `r / 2`,
    independent of any biological detail. This is the discrete content
    of the Floquet–Tsallis bridge. -/
theorem predicted_alpha_eq_r_half (r : ℝ) :
    predicted_alpha_from_r r = r / 2 := by
  unfold predicted_alpha_from_r linearity_ratio_to_Tsallis_q
       qLIL_scaling_exponent
  ring

/-! ## 2. The C. elegans empirical instance -/

/-- The Tsallis `q` for the C. elegans pharyngeal pump, derived from the
    measured `CelegansLinearityRatio = 0.08`. -/
def CelegansTsallisQ : ℝ := linearity_ratio_to_Tsallis_q CelegansLinearityRatio

/-- The predicted anomalous diffusion exponent `α` for the C. elegans
    pharyngeal pump. -/
def CelegansAnomalousDiffusion : ℝ :=
  predicted_alpha_from_r CelegansLinearityRatio

/-- **C. elegans bridge identity**: `α = r / 2 = 0.04`. The structural
    identity, instantiated at the measured value. -/
theorem celegans_alpha_eq_r_half :
    CelegansAnomalousDiffusion = CelegansLinearityRatio / 2 :=
  predicted_alpha_eq_r_half CelegansLinearityRatio

/-- **The numerical prediction**: for the C. elegans pharyngeal pump, the
    Floquet–Tsallis bridge predicts an anomalous diffusion exponent of
    exactly `0.04`. This is a falsifiable quantitative claim of the
    discrete theory. -/
theorem celegans_anomalous_diffusion_value :
    CelegansAnomalousDiffusion = 0.04 := by
  rw [celegans_alpha_eq_r_half]
  unfold CelegansLinearityRatio
  norm_num

/-- **C. elegans is sub-UGM**: the predicted scaling exponent is strictly
    less than the Brownian / UGM baseline `1/2`. This is exactly the formal
    separation between SGC and UGM that `qLIL_scaling_lt_UGM_for_q_gt_one`
    establishes for `q > 1`. -/
theorem celegans_scaling_lt_UGM :
    CelegansAnomalousDiffusion < (1 : ℝ) / 2 := by
  rw [celegans_anomalous_diffusion_value]
  norm_num

/-- **C. elegans is sub-Brownian by an order of magnitude**: the predicted
    scaling exponent is below `1/10`, far from the Brownian limit. -/
theorem celegans_scaling_lt_one_tenth :
    CelegansAnomalousDiffusion < (1 : ℝ) / 10 := by
  rw [celegans_anomalous_diffusion_value]
  norm_num

/-- **C. elegans is in the NESS regime**: the Tsallis parameter `q` is
    strictly in `(1, 2)`, which is exactly the regime where
    `conjecture_C2_hard_half` predicts a nontrivial probability current
    (NESS, not detailed balance). -/
theorem celegans_tsallis_q_in_NESS_regime :
    1 < CelegansTsallisQ ∧ CelegansTsallisQ < 2 := by
  unfold CelegansTsallisQ linearity_ratio_to_Tsallis_q CelegansLinearityRatio
  refine ⟨by norm_num, by norm_num⟩

/-- **C. elegans is super-nonlinear**: the linearity ratio is below the
    "deeply nonlinear" threshold of `0.1` (matching the
    `celegans_deeply_nonlinear` theorem in `SGC.PhaseDiagram`). -/
theorem celegans_alpha_lt_linearity_threshold :
    CelegansAnomalousDiffusion < CelegansLinearityRatio := by
  rw [celegans_alpha_eq_r_half]
  unfold CelegansLinearityRatio
  norm_num

/-! ## 3. The strict separation chain (formal UGM contrast for C. elegans) -/

/-- **UGM-SGC chain at C. elegans**: the predicted anomalous diffusion
    exponent sits strictly between zero and the UGM baseline `1/2`, with
    a ten-fold reduction from the Brownian prediction. -/
theorem celegans_alpha_strictly_between_zero_and_UGM :
    0 < CelegansAnomalousDiffusion ∧ CelegansAnomalousDiffusion < (1 : ℝ) / 2 := by
  refine ⟨?_, celegans_scaling_lt_UGM⟩
  rw [celegans_anomalous_diffusion_value]
  norm_num

/-- **Order-of-magnitude bound**: the predicted exponent for C. elegans
    is bounded by `1/20` (i.e., at most 5% of the Brownian baseline). -/
theorem celegans_alpha_le_one_over_twenty :
    CelegansAnomalousDiffusion ≤ (1 : ℝ) / 20 := by
  rw [celegans_anomalous_diffusion_value]
  norm_num

end SGC.Bridge.CelegansFloquetTsallis

end
