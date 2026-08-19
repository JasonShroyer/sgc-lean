# The Three Arrows of Coarse-Graining — design note (2026-08-18)

The next formalization target, selected from the full connection map
(Miranda / Renner / Jacobson / Langlands / UPAT-TEP; see the strategic
review in the vault, 2026-08-18): **retire the two thermodynamic axioms**
in `SGC.Thermodynamics.EntropyProduction` and package the result as the
monotonicity trinity of coarse-graining.

## The target

One operation — exact coarse-graining (lumping) — is monotone in all three
registers, each as a kernel theorem:

| Arrow | Statement | Status |
|---|---|---|
| Geometric | `CD(ρ,∞)` descends; curvature only improves | PROVEN (`RicciCurvatureBound_quotient`) |
| Informational | KL divergence contracts under pushforward (DPI) | AXIOM → to prove |
| Thermodynamic | Entropy production contracts: `σ(L̄,π̄) ≤ σ(L,π)` (hidden EP ≥ 0) | AXIOM → to prove |

Together: **the macro-level is smoother, less informative, and less
dissipative than the micro-level — provably, in one framework.** This is
the ε = 0 skeleton of the theory of emergence, and it converts two
firewalled axioms into verified core (answers red-team Attack 7; axiom
count −2).

## Why this is the highest-value target

1. **It grounds the September paper retroactively.** "The Physical Basis of
   Computational Complexity" (UPAT↔TEP, Sept 2025) leans on exactly these:
   §5.2 "The Blanket-Respecting Channel and DPI", §5.3 "Connection to
   Bayesian Mechanics and Lumpability". Its Theorem 1 (two-term lower bound
   on physical space via spectral gap + non-normality) presupposes DPI and
   blanket channels. The sprint turns the paper's assumed spine into
   kernel theorems — measured-then-proven, again. (Note: the paper's
   non-normality signature `LLᵀ ≠ LᵀL` is exactly our current/affinity
   register: `detailed_balance_iff_zero_current`.)
2. **It is the honest discrete shadow of the Jacobson direction.**
   Thermodynamics-of-horizons derives macroscopic law from entropy
   bookkeeping at causal boundaries. Our finite form: entropy bookkeeping
   under blanket/lump coarse-graining, with the boundary-readout sandwich
   already proven. No gravity claimed; the dictionary entry writes itself
   afterward, with the same discipline as the KMS table.
3. **Feasibility de-risked.** `Real.convexOn_mul_log` is in the Mathlib
   pin; `Mathlib.InformationTheory.KullbackLeibler.KLFun` exists (check for
   reusable finite log-sum machinery before hand-rolling).

## Proof plan

1. **Log-sum inequality** (the shared engine):
   `∑ aᵢ log(aᵢ/bᵢ) ≥ (∑aᵢ) log(∑aᵢ/∑bᵢ)` for `aᵢ ≥ 0, bᵢ > 0` — Jensen for
   `x ↦ x log x` (`Real.convexOn_mul_log`, `ConvexOn.map_centerMass_le` /
   `inner_smul_le` form), or reuse Mathlib's KL layer if it already
   provides it.
2. **DPI** (`data_processing_inequality`): KL of pushforwards under the
   deterministic quotient map contracts — direct application of log-sum
   over the fibers.
3. **Gibbs superadditivity**: `(a−b)log(a/b)` version by adding the
   log-sum for `(a‖b)` and `(b‖a)`:
   `∑ (aᵢ−bᵢ)log(aᵢ/bᵢ) ≥ (A−B)log(A/B)`.
4. **Hidden EP ≥ 0** (`hidden_entropy_nonneg`): apply 3 per coarse pair
   `(Ā,B̄)`, with `a` = fine weighted rates `π_x L_{xy}` aggregated to
   `π̄ CoarseGenerator`, matching the existing `CoarseGenerator` /
   `CoarseStationaryDist` definitions. Care: guard conventions (`x = y ∨
   L x y = 0`) must be respected on both levels; strict-positivity
   hypotheses as in `DissipationFloor`.
5. **The trinity corollary**: one statement citing all three arrows for an
   exactly lumpable quotient. Optional bonus: coarse EP still respects the
   coarse charge floor (compose with `DissipationFloor` downstairs).

## Acceptance criteria

- Both `axiom` declarations in `EntropyProduction.lean` deleted, replaced
  by theorems (name-stable if possible).
- Axiom audit: new theorems close over the kernel trio; hygiene report
  shows library axiom count reduced by 2.
- No change to any existing theorem statement (only strengthened
  foundations).

## Explicitly out of scope (recorded)

- Jacobson's actual derivation (Rindler horizons, Raychaudhuri): continuum;
  dictionary prose only.
- The TEP side (Williams √space / Cook-Mertz catalytic simulation): a
  large, separate CS formalization; the SGC-side spine (this sprint +
  BoundaryReadout) is the cheap half.
- Langlands: no formalizable statement exists; remains north-star prose.
- Causal states / computational mechanics: next research sprint after this
  one (prior-art sweep first, then predictive-equivalence partitions vs
  lumpability).
