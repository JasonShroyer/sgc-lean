# Phase G — Quantitative Protection Bound (brief)

**Status**: proposed 2026-07-09, immediately after the Phase 6 shakedown.
**Grounding**: `experiments/charge_anneal/RESULTS.md` in sgc-second-brain (v3, RTX 5090,
16 384 instances) measured the protected arm's KillingDefect plateau:

| δ′ | K★ measured |
|----|-------------|
| 0.25 | 1.90e-5 |
| 0.5  | 7.60e-5 |
| 1.0  | 3.09e-4 |
| 2.0  | 1.74e-3 |

i.e. **K★ ∝ δ′² at small δ′** (sinh steepening at δ′ = 2), and the annealer pins
`π_fiber` to exactly the positivity floor `ε/V` — the bound *binds*. Phase E proved
existence (`killingDefect_pos_of_affinityCharge_ne_zero`: K > 0). The experiment
measured *how much*. Phase G formalizes the *how much*.

## G1 — the headline target

For a generator `L`, cycle `c` of length `m` with `AffinityCharge Q ≠ 0`, measure
floor `∀ x, π x ≥ ε` and rate ceiling `∀ x y, L x y ≤ R`:

```
theorem killingDefect_quantitative
    (hQ : AffinityCharge L c ≠ 0) (hπ : ∀ x, ε ≤ π x) (hR : ∀ x y, L x y ≤ R) :
    KillingDefect L π ≥ (ε * |AffinityCharge L c| / (m * R^(m-1)))² / m
```

(Constant shape to be tuned during proof; the *structure* — quadratic in Q, quadratic
in ε, polynomial degradation in R and m — is the claim.)

## Proof sketch (division-light, staying in the Phase E idiom)

1. **Telescoping product difference**: `∏ aᵢ − ∏ bᵢ = Σᵢ (∏_{j<i} aⱼ)(aᵢ − bᵢ)(∏_{j>i} bⱼ)`.
   Already implicit in Phase E's `prod_range_succ` manipulations; extract as a lemma.
2. **Rate asymmetry → current**: `aᵢ − bᵢ` on edge (x,y) of the cycle equals
   `(J_xy + (π_y − π_x)·L_yx·0)/π_x`-shaped rearrangement of the edge current
   `J_xy = π x * L x y − π y * L y x`: precisely `L x y − L y x = (J_xy − (π_y − π_x) L y x)/π_x`…
   cleaner route: bound `|L x y − (π y/π x) L y x| = |J_xy|/π x ≤ |J_xy|/ε` and
   telescope the *twisted* products (each factor multiplied by measure ratios; the
   ratios cancel around the closed cycle — this is exactly the Kolmogorov telescoping
   from Phase E, now with remainder tracked instead of assumed zero).
3. Combine: `|Q| ≤ m · R^(m−1) · (max_edge |J|)/ε` ⇒ `max_edge J² ≥ (ε|Q|/(m R^(m−1)))²`,
   and `KillingDefect ≥ max_edge J²` (sum of squares ≥ one square).
4. Corollary (fiber triangle, m = 3, exoticLift handle): plug `Q = (a+δ)³ − a³`
   to get the *instantiated* bound the 5090 measured. Small-δ expansion gives the δ′²
   law; the sinh form appears in the exponential-coordinates corollary.

## G2 — falsification loop

Numerically evaluate the G1 constant on the v3 grid (n = 8, ε = 0.2, R from the
run's σ-freeze) and check `K★_measured ≥ bound` with the ratio logged. If the bound
is ever violated the *formalization* is wrong (statement bug), not the experiment —
that's the point of having both.

## G3 — north star (labeled prose, no claims)

Miranda's fluid-computer program (Euler flows simulating Turing machines, via
Cantor-set encodings — cf. her Topological Kleene Field Theory) and Moore's
computation-in-dynamics sit one dictionary away: `DiscreteFluidDynamics` already
maps our generator currents to discrete incompressible flows, and the affinity
charges are the discrete Wilson loops / circulation integrals. Phase G's bound is
then a **computational obstruction**: a fluid computer cannot dissipate a conserved
circulation class below an explicit floor. When the continuum limit enters
(Convergence.lean, Mosco path), Tao's averaged-Navier–Stokes blowup machinery is the
adjacent formal territory. One step at a time: G1 first.

## Execution notes

- New module: `src/SGC/Bridge/AffinityProtectionQuantitative.lean`; imports
  `AffinityProtection` + `SchnakenbergBasis`. Audit section §18 when green.
- Reuse Phase E lessons: ℕ-indexed closed walks, division-free until the final
  corollary, `prod_range_succ`/`prod_range_succ'` for the two orientations.
- CI: `python -m solaris build` after each lemma lands — Forge1 verifies in ~2 min.
