# The Predictive-Thermodynamics Chain — design note (2026-08-11)

Jason's proposed chain (CRH follow-up):

> boundary dynamical gain ⟹ coarse-graining defect ⟹ finite
> predictive-validity horizon ⟹ thermodynamic selection of stable readouts

Audit verdict: **the spine is right; two links need correction; the
corrected endpoint is stronger than the original.** This note fixes the
statements and scopes the sprints.

## Correction 1 — link 1 is false as stated; the antecedent is STRAIN, not gain

"Gain ⟹ defect" has a kernel-proven counterexample: the shift tower has
maximal boundary throughput (every symbol crosses every truncation
boundary every step) and **exactly zero** defect (`shiftTower_defect_zero`,
`shiftTower_eternal_closure`). Likewise `cd0_driftline`: arbitrary uniform
drift, zero strain, flat. Interfaces do not pay for throughput; they pay
for **inhomogeneity of throughput across a block** — strain, in exactly the
`OperatorStrain` sense (deviation of the coupling field from local
flatness). Corrected link 1:

> **(L1) Strain of the boundary coupling ⟹ coarse-graining defect**,
> with uniform coupling as the calibrated ε = 0 case.

## Correction 2 — link 3 splits into selection dynamics + a floor

"Thermodynamic selection of stable readouts" is two claims:

> **(L3a — selection)** Readout adaptation monotonically descends the
> defect (extends the horizon). Partially formalized: the Adaptive
> Coherence Descent ladder (`ResidualDescent`: dissipation telescopes,
> residual summable, residual → 0; `AttentionGate`: descent for ANY
> policy; `PhaseClassifier.rg_flow_crystalward`: consolidation is one-way).
>
> **(L3b — the floor)** Descent cannot reach zero when topology forbids it:
> `killingDefect_quantitative` lower-bounds Σ J² by the affinity charge for
> ANY positive measure. The thermodynamic shadow: near equilibrium the
> Schnakenberg entropy production `σ = ½ Σ J_xy log(w_xy/w_yx)` is
> quadratically equivalent to Σ J², so a charge floor on the current is a
> **dissipation floor**. Missing bridge (elementary, formalizable):
> `(a − b)·log(a/b) ≥ 2(a − b)²/(a + b)` for `a, b > 0`, giving
> `EntropyProductionRate ≥ Σ J²/(activity)` and then, composed with the
> affinity bound, **EP ≥ f(ε_floor, Q, m, R) > 0**: no readout-maintenance
> process can dissipate below its topological charge.

## The corrected chain

```
strain of boundary coupling            (L1, target: Boundary Readout Thm)
  ⟹ coarse-graining defect ε
  ⟹ finite validity horizon T* ~ 1/ε  (L2, EXISTS: trajectory_closure_bound)
  ⟹ selection descends ε / extends T* (L3a, partially formalized: descent ladder)
  ⟹ down to the topological floor     (L3b, target: EP ≥ floor(Q) — Landauer-for-foresight)
```

Endpoint, stated plainly: **predictive validity is a thermodynamic
resource. Foresight has an energy price, and the price has a topological
floor.** Horizon length, perturbation robustness, and maintenance cost are
three measurements of ONE defect in three registers (geometric strain /
predictive ε / thermodynamic σ); selection can only trade within the
degrees of freedom above the charge floor. This is the anchor
Markov-blanket and reservoir-computing accounts lack.

## Sprints (in value order)

* **Sprint C (first — highest value/effort): the dissipation floor.**
  1. `gibbs_quadratic_bound : 0 < a → 0 < b → 2*(a-b)^2/(a+b) ≤ (a-b)*log(a/b)`
     (Lean cost: needs `log x ≥ 2(x−1)/(x+1)` for `x ≥ 1`; not in Mathlib
     verbatim — derive via `Real.add_one_le_exp`-style bounds or convexity).
  2. `entropy_production_ge_current_sq`: Schnakenberg σ ≥ Σ J²/(2·activity).
  3. Compose with `killingDefect_quantitative` →
     `entropy_production_floor_of_affinityCharge`. Kernel Landauer floor.
* **Sprint A: Boundary Readout Theorem (L1).** Strengthen
  `blanket_implies_approx_lumpable` to use `RespectsBlank`: ε bounded by
  the blanket-coupling inhomogeneity (strain of gain), with the
  uniform-coupling blanket as the ε = 0 calibration (mirrors
  `cd0_driftline`). Then compose with L2 for `T* ≳ 1/strain` corollary.
* **Sprint D: selection statement.** Package descent ladder + floor:
  adaptation extends T*, monotonically, floored by Q.
* **Debt retirement (background):** the two EP axioms
  (`data_processing_inequality`, `hidden_entropy_nonneg`) should become
  theorems inside this program — they are the coarse-graining half of the
  thermodynamic register.
* **Measurement anchor (demos/, after C+A):** lattice reservoir + blanket
  on the RTX 5090: (i) readout error vs coupling inhomogeneity against L1's
  bound; (ii) measured EP vs measured Σ J² against C's inequality; (iii)
  annealing within a fixed charge class cannot descend below the floor —
  the measured-then-proven loop run in the CRH direction.

## Honesty ledger

- L2 exists; L3a partially exists; L1 and L3b are targets, not results.
- "Near equilibrium" in L3b is where the quadratic equivalence is exact
  from below (the inequality direction we need holds globally; the
  *upper* quadratic bound does not, and is not claimed).
- Nothing here formalizes CRH-cosmology; the chain is conditional
  mathematics about boundary projections.
