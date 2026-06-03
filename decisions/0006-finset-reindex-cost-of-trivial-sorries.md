---
method: Lake-gated discharge of Fisher–Noether Link 1 (Var[xᵀCx] = vec(C)ᵀ Σ vec(C))
status: VALIDATED
domain: spectral
replaces: []
replaced_by: []
evidence:
  - logs/l105_full2.txt
  - logs/l105_nozero.txt
  - logs/lake_l105_build3.txt
  - src/SGC/InformationGeometry/FisherNoetherBridge.lean
date: 2026-06-04
---
# Lake-gated discharge of Fisher–Noether Link 1 (variance_as_lifted_quadform)

## Verdict

The Link 1 identity — empirical `Var[xᵀCx]` equals the quadratic form of `vec(C)` in
the covariance of the lifted features `vec(x xᵀ)` — is now **machine-verified**:
`lake build` exits 0 with the `sorry` at `FisherNoetherBridge.lean:105` discharged
(file sorry-count 4 → 3, no regressions). **ε = 0 reached for this theorem.** (τ⁺.)

This took **two runs**. Run 1 (2026-06-03) failed (exit 1) on four tactic-structure
errors and was honestly recorded τ⁻. Run 2 (2026-06-04) succeeded with the corrected
scaffold below. The headline lesson stands and is now *paid for*: a `SORRY
CLASSIFICATION: TRIVIAL` banner says nothing about Lean cost — this "trivial" identity
needed an ~80-line proof (centering lemma + double `sum_mul_sum` square expansion +
five-fold sum transpose). **"math-trivial" ≠ "Lean-cheap".**

Bonus τ⁺: `[NeZero N]` was **dropped** and the proof still builds, so the
weight-agnostic claim (below) is no longer a conjecture — the kernel verified it.

## When to use / When NOT to use

- USE the route *expand `Q.eval` → centre each term → square the linear form → swap
  `Σ_k` inward*. The math is correct; budget effort for the reindexing, not the algebra.
- Do NOT read a `SORRY CLASSIFICATION: TRIVIAL` banner as a proxy for Lean cost.
  **"math-trivial" and "Lean-cheap" are different axes.** In tactic terms this needed
  `Finset.sum_comm` transpositions, a double square-expansion, and per-term `ring`.
  That is the recurring tax on the 64-sorry backlog.
- CORRECTION to the run-1 note: `sum_mul_sum` *does* exist and is the right tool.
  `Fintype.sum_mul_sum f g : (Σ i, f i)·(Σ j, g j) = Σ i, Σ j, f i · g j` and its
  `Finset.sum_mul_sum` sibling (Mathlib `Algebra/BigOperators/Ring/Finset.lean:55`)
  expand the square cleanly — no need to roll it by hand.
- Do NOT introduce any `[NeZero N]`-dependent step (see Why): the identity is
  weight-agnostic, and leaning on `N ≠ 0` is both unnecessary and a dead end.

## Why (SGC)

Link 1 is the foundational rung of the Fisher–Noether bridge in
`src/SGC/InformationGeometry/FisherNoetherBridge.lean`: it certifies that the engine's
manifold-mode computation (minimise `Var[xᵀCx]` over `‖C‖_F = 1`) is *exactly* a
minimum-eigenvector problem on the lifted covariance, which Link 2 then identifies with
Fisher information.

**Peripheral discovery (this run): the identity is weight-agnostic.** Both sides are a
polynomial identity in the constant `c = 1/N`; `c` never needs to be inverted or
cancelled. So `[NeZero N]` is *not required* — the theorem holds for an arbitrary real
weight `c`. This is not a proof shortcut but a strengthening: the min-variance ↔ Fisher
bridge does not depend on the sample count being nonzero, and it generalises verbatim to
**weighted / importance-sampled / biased** estimators. That directly feeds the Section-4
selection-contamination theorem (`f·S` reweighting) — the same algebra, different `c`.

## Evidence

- Theorem PROVEN — `src/SGC/InformationGeometry/FisherNoetherBridge.lean:105`, statement
  `(1/N)·Σ_k (Q.eval(X k) − q̄)² = Σ_{a,b,c,e} C_{ab} C_{ce} · Cov̂[x_a x_b, x_c x_e]`,
  now carrying NO `[NeZero N]` hypothesis.
- Build PASSES (the honest gate): "Build completed successfully (2274 jobs)." / "EXIT=0",
  remaining `sorry` warnings only at lines 192/255/364 (the corollary + two unrelated
  declarations) — line 105 is **absent**, i.e. discharged.
  `logs/l105_full2.txt` (with `[NeZero N]`) and `logs/l105_nozero.txt` (without).
- Run-1 failure kept for the contrast that earned the lesson — exit 1 on: premature
  `mul_sum` (the head is a `Σ`, not a product); an associativity gap that needs `ring`,
  not `rw [mul_sub]`; and a stranded `AddCommMonoid ?m` metavariable from distributing
  `1/N` *before* `Finset.sum_comm`. `logs/lake_l105_build3.txt`.

## Canonical implementation

File: `src/SGC/InformationGeometry/FisherNoetherBridge.lean` (`variance_as_lifted_quadform`).
The verified scaffold has four stages:

1. **Centering lemma `key`** — `(Σᵢ Σⱼ C_{ij} x_{ki} x_{kj}) − q̄ = Σ_a Σ_b C_{ab}(x_{ka}x_{kb} − mean_{ab})`.
   Sub-lemma `hmean` commutes `Σ_{k'}` inward with `Finset.sum_comm` FIRST, then `mul_sum`,
   then `ring` at the leaf. (Already correct in run 1.)
2. **Square expansion `sq`** — `(Σ_{a,b} M_{ab} c_{ab})² = Σ_{a,b,c,e} M_{ab} M_{ce} c_{ab} c_{ce}`:
   `rw [pow_two, Fintype.sum_mul_sum]`, descend one level, `rw [Finset.sum_comm]` to fix the
   a,c order, `rw [Finset.sum_mul_sum]`, then `ring` at the innermost leaf.
3. **Five-fold transpose `reorder`** — move the sample index `k` from innermost to outermost
   past the four feature indices. THE KEY TRICK: descend under `Finset.sum` binders in `conv`
   with `enter [2, a, 2, b, …]`, NOT `ext` — `ext` fails ("function or arrow expected")
   because `Σ a, …` is `Finset.sum univ (fun a => …)`, an *application*, not a lambda. At
   each depth `rw [Finset.sum_comm]` swaps the now-adjacent `(feature, k)` pair.
4. **Scalar pulls** — `rw [Finset.mul_sum]` pushes the outer `1/N` onto the `k`-sum on the
   LHS; on the RHS `conv_rhs => enter [...]; rw [← mul_assoc, Finset.mul_sum]` pulls each
   `(1/N)·Σ_k` out. Use TARGETED `rw`, never a blanket `simp [mul_sum]`: the centred factors
   contain internal mean-sums `Σ_l`, and global `mul_sum` would expand those and strand the
   leaf `ring`.

Weight-agnostic confirmed: `[NeZero N]` removed, still builds (`logs/l105_nozero.txt`).
