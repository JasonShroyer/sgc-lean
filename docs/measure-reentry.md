# Measure Re-entry — research note (2026-08-22)

The epistemic ledger for the ε > 0 program, per the sprint brief (order 6).
Module: `SGC.Renormalization.MeasureReentry`.

## 1. Kernel-proven (audit-gated, classical trio only)

- `coarseGenerator_eq_conditional_exit_average` — `Q^π` is the conditional
  exit average: canonical, representative-free (ladder 1).
- `residual_all_zero_iff_stronglyLumpable`,
  `defectSq_eq_zero_iff_stronglyLumpable` — the zero-defect equivalence
  (ladder 2–3): `𝔇_π = 0 ⟺ exact strong lumpability`, for any strictly
  positive reference measure.
- `closureCommutator_entry` — `(L·K − K·Q^π) i B = residual i B`: the
  operator obstruction and the pointwise field are the same object.
- `defectSq_eq_weighted_commutator_frobenius` — `𝔇_π²` **equals** the
  π-weighted Frobenius norm² of the closure commutator (identity, not
  bound; stronger than the brief's request).
- `closureCommutator_eq_zero_iff_stronglyLumpable` — operator form; at
  ε = 0 recovers intertwining with the physical quotient.
- `power_closure_telescoping` — discrete Duhamel:
  `L^n·K − K·(Q^π)^n = Σ_{k<n} L^{n−1−k}·𝒞·(Q^π)^k`.
- Toys: `defectSq_Ltoy_eq_zero` (exactly lumpable 3-state),
  `defectSq_Lnl_pos` (minimally non-lumpable 3-state) — the functional
  separates the regimes (ladder item 4, brief order 4).
- Prior sessions, same campaign: the Unification Lemma
  (`coarseGenerator_eq_quotientGeneratorSimple`) and the Trinity capstone
  (`three_arrows`).

## 2. Elementary planned lemmas (not yet formalized)

- `𝔇_π ≤ 𝔇_∞` (worst-case within-block exit spread dominates the weighted
  defect); representative-quotient discrepancy bound
  `|Q^π_{AB} − r_{ρ(A)B}| ≤ max-spread` (ladder 4–5).
- The `B ≠ A` defect variant equals the full defect up to the own-block
  term for conservative generators.
- Norm-level corollary of the telescoping identity: for any
  submultiplicative norm, `‖L^n K − K Q^n‖ ≤ n·max(‖L‖,‖Q‖)^{n−1}·‖𝒞‖`;
  continuous-time (`exp`) Duhamel analogue via Mathlib's
  `NormedSpace.exp`.
- Pinsker (`pinsker_inequality`) remains a LOCAL AXIOM: Mathlib's pin has
  no finite Pinsker; the binary-case reduction is available via our DPI,
  leaving one 1-D convexity inequality — a bounded cleanup item, not done
  (Workstream A cap honored; no consumers depend on it).

## 3. Numerical hypotheses (falsifiable, NOT theorems)

- H-horizon: `T_η` (tolerance-η closure horizon) correlates with
  `1/𝔇_π` at fixed intra-block mixing; scaling may differ by mixing
  regime.
- H-band: task utility of a physical reservoir is maximized in a band
  `0 < 𝔇_π < 𝔇_critical` (the fluid-computation operating regime,
  Workstream D's closure atlas).
- H-homonym (red-team P1): the SVD-tail sensor ε of `sgc_engine.py`
  relates to `𝔇_π` of a spectrally-defined partition under stated
  conditions.

## 4. Physical interpretations (prose, licensed by the theorems)

- At ε = 0 the stationary measure is gauge (Unification Lemma); `𝔇_π`
  measures precisely the leverage the microscopic measure regains over the
  macro future when closure fails — "measure re-entry."
- The telescoping identity reads: every macroscopic prediction error is a
  sum of single re-entry events, propagated by the fine dynamics before
  the event and the macro law after it. Hidden memory = the accumulated
  re-entry series.
- Boundary strain (BoundaryReadout) is the blanket-partition special case
  of the residual field; the sandwich theorems bound its row-sum cousin.

## 5. Open conjectures (do not cite as results)

- Approximate Trinity: quantified degradation of all three arrows in
  `𝔇_π` (geometric/informational/thermodynamic leakage bounds).
- Measure-re-entry ↔ Mori-Zwanzig: the residual series as the leading
  memory kernel; relation to `Approximate.lean`'s trajectory bounds.
- Continuum lift along the Miranda program; universality/computation
  claims (require a constructive encoding theorem, per the brief).
