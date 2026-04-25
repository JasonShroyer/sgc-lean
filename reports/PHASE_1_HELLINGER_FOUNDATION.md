# Phase 1 — Hellinger Foundation (Lean theorem + Python governor)

**Date:** April 24, 2026
**Sprint:** post-Sprint-D foundation work
**Status:** both prongs delivered, zero new `sorry`s, both runs reproducible

This document records the first foundation stone for the EGI Tower programme:
the formal Lean theorem of the **Bhattacharyya / Hellinger square-root
embedding as a local tangent isometry** between the discrete Fisher-Rao
metric and the Euclidean ℓ² metric, paired with the empirical Python
**governor signals** that fire in the precursor window before grokking.

## What changed

| Prong | File | Status |
|---|---|---|
| **1A — Lean** | `src/SGC/InformationGeometry/HellingerLift.lean` (new, 230 lines) | Compiles clean, zero `sorry`, zero warnings |
| **1B — Python** | `demos/fisher_rao_curvature_demo.py` (extended) | New `compute_derived_proxies` + 11 new `--proxy` choices + `--analysis-min-epoch` filter |

Verification command for the Lean theorem:

```bash
lake env lean src/SGC/InformationGeometry/HellingerLift.lean
# exit code 0, no output
```

Verification commands for the Python governors:

```bash
python demos/fisher_rao_curvature_demo.py --proxy eff_rank_collapse_rate \
  --out-csv reports/fisher_rao/governor_eff_rank_collapse_rate.csv
python demos/fisher_rao_curvature_demo.py --proxy d2_curvature_dt2 \
  --out-csv reports/fisher_rao/governor_d2_curvature_dt2.csv
```

## Phase 1A — the Lean theorem

`@c:\Lean4 Projects\src\SGC\InformationGeometry\HellingerLift.lean:158-170` is the
headline statement, named `fisher_euclidean_tangent_isometry`:

```lean
theorem fisher_euclidean_tangent_isometry
    (ψ Δψ : V → ℝ) (hψ : ∀ x, 0 < ψ x) :
    fisherRaoQuadForm (lift ψ) (liftDiff ψ Δψ) = 4 * euclideanQuadForm Δψ := by
  unfold fisherRaoQuadForm lift liftDiff euclideanQuadForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  exact hellinger_pointwise (ψ x) (Δψ x) (hψ x)
```

The proof reduces to a pointwise algebraic identity, `hellinger_pointwise`,
which is dispatched by `field_simp; ring`:

$$\frac{(2 a b)^2}{a^2} = 4 b^2 \qquad (a > 0).$$

The file also exports:

| name | role |
|---|---|
| `lift` | the square-root embedding ψ ↦ ψ² |
| `liftDiff` | the linearised differential `(ψ, Δψ) ↦ 2·ψ·Δψ` (tangent map of `lift` at ψ) |
| `lift_pos`, `lift_nonneg`, `lift_sum_eq_one` | basic structural lemmas: positivity preserved; unit ℓ² maps to probability |
| `fisherRaoQuadForm`, `euclideanQuadForm` | the two discrete tangent quadratic forms |
| `hellinger_pointwise` | the pointwise algebraic kernel |
| `fisher_rao_tangent_eq_four_euclidean` | renamed alias for downstream rewriting |
| `fisher_rao_tangent_le_four_euclidean` | bound corollary |
| `euclideanQuadForm_nonneg`, `fisherRaoQuadForm_lift_nonneg` | nonnegativity, useful as a Lyapunov property |

### Honest scope written into the file

The module docstring is explicit about what the theorem does NOT prove,
because the briefings that motivated it overstated the consequences:

- The amplitude space is **not flat** — it is the unit sphere in ℓ², which
  has constant positive Gaussian curvature 1. The "flatness" lives only in
  the *ambient* ℓ² norm of *tangent vectors*.
- Two amplitudes from different consolidated tasks **cannot** be linearly
  added safely — the sphere is not closed under addition; ψ₁ + ψ₂ leaves
  the amplitude space.
- This theorem **does not resolve** the catastrophic-forgetting question
  for shared-weight architectures. The empirical record on that question
  is `@c:\Lean4 Projects\src\SGC\ContinualLearning\IsolationTheorem.lean` (Sprint C April 2026
  falsified the additive shared-weight pattern; Sprint D moved to isolated
  models per task with sheaf consistency).

The theorem remains a strong tool *inside one crystallised model*: anywhere
the discrete Fisher information at `p = ψ²` is needed, the curved
`Σ (ΔP)² / P` form can be replaced by the flat `4 · Σ (Δψ)²` form, *at the
level of tangent vectors only*.

### Existing-repo touchpoints

The Lean file is wired into the existing structure with no breaking changes:

- Lives under the same namespace tree as `FisherKL`, `TsallisStatistics`,
  `DefectDynamics`, etc.
- Uses the same discrete style (`{V : Type*} [Fintype V] [DecidableEq V]`)
  as `@c:\Lean4 Projects\src\SGC\InformationGeometry\FisherKL.lean:53` — no measure-theoretic imports.
- Imports only what `DefectDynamics.lean` already imports, so adds zero
  build-graph weight.

## Phase 1B — the Python governor

`@c:\Lean4 Projects\demos\fisher_rao_curvature_demo.py:294-361` adds `compute_derived_proxies`,
which augments each curv-row with first and second forward-difference
derivatives of every primary proxy plus three convenience aliases:

- `eff_rank_collapse_rate` = −d(eff_rank)/dt — positive while the
  representation is crystallising, peaks at the steepest moment of collapse.
- `abs_d_eff_rank_dt` — magnitude of the rate of rank change.
- `abs_d2_curvature_dt2` — magnitude of the curvature acceleration.

`@c:\Lean4 Projects\demos\fisher_rao_curvature_demo.py:558-616` upgrades `analyse_alignment`
with a `min_epoch` filter (so the Kaiming-init λ_min ≈ 2e-6 spike at
epoch 1 doesn't dominate derivative peak-detection) and adds a signed
offset plus a human-readable `relation_to_grokking` field
(`precursor` / `coincident` / `aftershock`).

### Empirical findings, seed 42

Grokking occurs at epoch **275** (test_acc 0.954, train_acc 1.000). Two
distinct precursor signals are now formally detected:

| Governor proxy | Peak epoch | Lead time | Peak/baseline | Interpretation |
|---|---:|---:|---:|---|
| `eff_rank_collapse_rate` | 175 | **−100 epochs** | 8.9× | "Crystallisation begins" — λ_min starts to drop, λ_max starts to grow |
| `abs_d2_curvature_dt2` | 225 | **−50 epochs** | 3.6× | "Crystallisation accelerating" — second derivative of `tr Σ⁻¹` peaks |

This is a **two-tier early-warning system**:

- **T − 100 epochs:** `eff_rank_collapse_rate` peaks. The representation
  enters the rapid-compression window. Onset of geometric phase change.
- **T − 50 epochs:** `d²(curvature)/dt²` peaks. The Fisher information is
  accelerating along its rank-collapse direction. Imminent transition.
- **T:** χ_g peaks, test_acc crosses 0.95, eff_rank ≈ 13.7 (≈ k = 8 algebraic
  basis for mod-97 addition's Fourier structure plus margin).

Note that **no derivative proxy peaks exactly at grokking**. The grand
"sharp Fisher-Rao singularity at the Lifshitz transition" claim from the
original brief remains falsified (see
`@c:\Lean4 Projects\reports\FISHER_RAO_CURVATURE_RESULTS.md`). What this
session adds is a clean *predictive* signature that fires 50–100 epochs
ahead of the observable transition, which is far more useful for an
autonomous SGLD governor than a coincident peak would be.

### Operational use for the JAX/SGLD engine

The governor is now ready to be wired into the autonomous training loop:

1. Maintain a sliding buffer of activations, recompute `eff_rank`
   every K = 25 epochs.
2. Compute forward-difference `eff_rank_collapse_rate` online.
3. **Trigger:** when `eff_rank_collapse_rate > 0.4` (≈ baseline × 6),
   flag *crystallisation onset*; budget the next 100 epochs as the
   transition window and prepare gauge-fixing.
4. **Confirm:** when `abs_d2_curvature_dt2 > 8` (≈ baseline × 2.5),
   flag *crystallisation imminent*; freeze cooling schedule, start
   recording the readout subspace for sheaf isolation.
5. **Settle:** when both governors return to baseline and test_acc ≥ 0.95,
   declare the task crystallised and seal the model.

The thresholds above are seed-42 calibration; multi-seed replication is
the obvious next empirical step, and the only one that matters before
shipping the governor into the JAX engine.

## Why this is the right foundation stone

1. **It's an honest theorem.** The proof is six lines, no `sorry`s, no
   axioms beyond what Mathlib provides. The framing in the file explicitly
   refuses the overreach that nucleated this work ("flat Hilbert space →
   safe task superposition") and instead documents the actual scope.

2. **It composes with everything already in the repo.** Same namespace
   tree, same discrete style, same imports as `DefectDynamics.lean`. No
   measure-theoretic invasion. `FisherKL.lean` doesn't need to change to
   use it; future bridges can specialise the existing `FisherQuadForm` to
   the lifted family at a call-site.

3. **The governors give us empirical purchase NOW.** Without re-running
   any GPU training, we got two predictive precursor signals out of the
   16 snapshots we already had. Lead times of 50 and 100 epochs are
   actionable for an autonomous controller — far more so than a peak
   coincident with the observable.

4. **It does not contradict the repo's own findings.** The Sprint C/D
   pivot to spectral isolation (`@c:\Lean4 Projects\src\SGC\ContinualLearning\IsolationTheorem.lean`) stands; the
   Hellinger lift is now a complementary tool *inside* one isolated
   model, not a competitor to the isolation strategy.

5. **It opens the obvious next two phases.** With the algebraic kernel
   in place, the Beck-Cohen → Tsallis superstatistics bridge in
   `@c:\Lean4 Projects\src\SGC\InformationGeometry\TsallisStatistics.lean` and the
   `catastrophic_forgetting_prevention` `sorry` in
   `@c:\Lean4 Projects\src\SGC\ContinualLearning\AdiabaticInvariant.lean:284` are both reachable
   targets — neither requires new `sorry`s upstream.

## Artefacts

```
src/SGC/InformationGeometry/HellingerLift.lean       (NEW)
demos/fisher_rao_curvature_demo.py                   (extended)
reports/fisher_rao/governor_eff_rank_collapse_rate.{csv,html}
reports/fisher_rao/governor_abs_d_eff_rank_dt.{csv,html}
reports/fisher_rao/governor_d2_curvature_dt2.{csv,html}
reports/fisher_rao/governor_abs_d2_curvature_dt2.{csv,html}
reports/PHASE_1_HELLINGER_FOUNDATION.md              (this file)
```

## Next phases (not started this session)

| Phase | Target | Estimated cost | Blocker |
|---|---|---|---|
| **2** | Add `gaussian_amplitude_yields_chi_squared_density` axiom + a Beck-Cohen integration lemma to `@c:\Lean4 Projects\src\SGC\InformationGeometry\TsallisStatistics.lean`. Bridges the Hellinger lift to the Tsallis machinery already in the repo. | ~3 h Lean | None — `TsallisStatistics.lean` already has the q-entropy and escort distribution machinery to receive the bridge. |
| **3** | Use `fisher_euclidean_tangent_isometry` as a rewriting step inside `catastrophic_forgetting_prevention` at `@c:\Lean4 Projects\src\SGC\ContinualLearning\AdiabaticInvariant.lean:284`. The lift simplifies the curved Fisher quadratic form to a flat ℓ², and the adiabatic limit follows from the bound corollary. Scoped to single-task adiabatic protection — does NOT attempt the cross-task superposition claim. | ~5 h Lean | Need to first eliminate the `sorry` at `:129` (`FunctionalDefectGradient` definition); this is independent of the lift. |
| **4** | Multi-seed replication of the governor. Re-run `demos/grok_with_activation_dump.py` for seeds 7, 13, 123, 2026; verify the two-tier precursor signature is robust. | ~3 min training × 4 + ~5 s analysis × 4 | None. |

## Closing posture

The bricks are dry. The Lean compiles, the Python runs, the governors
fire where the data says they should fire, and the file headers are
honest about what was and wasn't proved. The repo is in a stronger
position to push toward the EGI tower than it was four hours ago, and
nothing committed today contradicts anything already in the repo.
