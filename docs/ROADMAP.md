# Roadmap after two rounds of adversarial review (written 2026-09-12, evening)

Status of the branch at this writing: Lean sources unchanged since commit `0096f90`
(audited by the reviewer, source-and-receipt audit, no fresh build). Documentation
carries one retraction (6.2) and awaits the two correction tables. Nothing below is
started; this is the plan for the next session.

## 0. What the two reviews settled

| Claim in v0.1 | Verdict | Consequence |
|---|---|---|
| Galerkin error is driven by the flux `D_N` | false (`M=3, N=1` counterexample) | driver is the re-entry residual `R_N = P_N[B(u,u) - B(P_N u, P_N u)]`; keep `D_N`, `R_N`, `r_N`, `Pi_N` as four distinct declarations |
| Fixed-cutoff quantities diverge at blowup (6.2) | false (`||D_N|| <= C N^{5/2} ||u||_2^2`) | retracted; successor via "resolution required" also fails for `L^2` tolerance (`||P_N u - v_N|| <= 2M`); any successor must use a continuation-controlling norm |
| Residual-controlled a posteriori error is new | prior art | Morosi-Pizzocchero (6.20), (4.24)-(4.27), Sec. 7; CCRT Thm 3 / Cor 5 / **Thm 8 (completeness)** - cite before any "new" |
| Certified existence interval as horizon (Q1) | sound; `T_N^CCRT -> T*` is a corollary of CCRT Thm 8; monotone only as a running max | adopt "validity horizon = specified certified guarantee"; not a phase boundary |
| `CantorShiftTower` formalizes Moore's shift (Q2) | unsupported by the definitions | it is a **uniform fresh-symbol (Bernoulli) shift tower**, exactly lumpable under deletion of the oldest symbol; Turing simulation is not established; computation axis relabels [KERNEL] -> [FRAMING]; `HaltingCompiler` result stands |
| Statistical bridge via invariant measures (Q3) | promising, with a closure theorem required | a measure gives a transition matrix, not automatically a Markov observation process (four-state counterexample); the reviewer supplies a precise `L^2(mu)` forecast bound `||Pi U^m Pi - A^m Pi|| <= m delta` |
| Monotone quantity across phases | none identified; time reversal forbids sign-even instantaneous ones for Euler; stationarity forbids strictly decreasing averaged ones; deterministic Galerkin has zero carre-du-champ | drop the phase-diagram language; a curvature theory needs a justified stochastic model |
| Receipts | integrity passes (hashes, statements, raw fields) | one mismatch: residual receipt predates removal of `hT`; regenerate |
| Axiom wording | imprecise | "168 closures contained in the standard base; 151 equal all three" |

The audit "does not justify abandoning SGC's finite-state theory. It justifies removing
the unproved equivalences that were making the theory appear to answer a different
question." That is the frame for everything below.

## 1. Morning, block A - documentation only (no Lean edits; no authorization needed)

A1. Apply both correction tables to `docs/two-horizons.md` -> v0.2. Concretely:
    abstract: remove both "iff"s; Theorem 2.5 restated as the Bernoulli tower theorem
    with the exact hypotheses, computation axis relabelled [FRAMING]; 3.1 hypothesis on
    stationary NS corrected (nowhere-vanishing harmonic carrier, deformed metric);
    4.2 row for the SGC budget relabelled; 5 "stationary so no budget spent" fixed
    (`T ||omega||_inf` accrues); 6.1 flux identity: both nonlinear terms carry the output
    projection `P_N`, and the pairing is not exactly the flux; 6.1' Beltrami claim
    restricted to constant `lambda` on the flat torus with a curl-commuting cutoff;
    "vorticity measures stretching" -> "local rotation"; 6.1' Cheskidov-Shvydkoy:
    `Lambda in L^{5/2}` unconditional, `L^2` needs the Besov hypothesis; 6.2 successor
    retracted with the `2M` argument; new Section 6.3: certified horizon via CCRT Thm 8;
    new Section 6.4: statistical horizon theorem statement (attributed to the reviewer's
    derivation, marked [PROPOSED, not in tree]); Section 7 non-claims extended.
A2. `AXIOMS.md` and `README.md`: precise closure wording (168 / 151).
A3. Regenerate the `ResidualHorizon` receipt from the pinned source (post-`hT`), replace
    `docs/receipts/residual-horizon/`, and add the reviewer's
    `review-2-receipt-verification.json` to `docs/reviews/`.
A4. Citation pass: Morosi-Pizzocchero (arXiv:1104.3832), CCRT (arXiv:math/0607181),
    Cheskidov-Shvydkoy (arXiv:1102.1944), Cheskidov-Dai-Kavlie (arXiv:1507.05908),
    Moore (Nonlinearity 4, 1991), Pedrotti-Salez.
A5. Accept the reviewer's offer: an L1 specification (two residual identities,
    certificate-completeness quantifiers, statistical operator construction with the
    four-cycle regression test), written without editing the Lean tree.

## 2. Block B - formalization sprint (requires Jason's authorization)

In the reviewer's recommended order. Each item is small, kernel-checkable, and yields
a regression test rather than a claim.

B1. `SGC/Bridge/StatisticalHorizon.lean` - **the one genuinely new theorem on offer.**
    Hilbert space `H`, isometry `U`, orthogonal projection `Pi`, `A = Pi U Pi`,
    `delta = ||(I - Pi) U Pi||`. Prove `||U^m Pi - A^m Pi|| <= m delta` and
    `||Pi U^m Pi - A^m Pi|| <= m delta` by the Kernel Horizon telescoping. Pure operator
    algebra; Mathlib has everything. Then the **four-state regression test**: a
    deterministic map and partition whose one-step statistics do not compose (the
    reviewer's counterexample), showing `delta > 0` is the rule. Reading: SGC's Kernel
    Horizon, transported to `L^2(mu)` of a dynamical system with invariant measure - the
    statistical bridge, honestly scoped.
B2. `SGC/Fluids/GalerkinResiduals.lean` - explicit Fourier state space on `T^3` (finite
    mode set), definitions of `B`, `P_N`, `D_N`, `R_N`, `r_N`, `Pi_N` as four separate
    declarations; the exact projected error equation; the trilinear cancellation
    `<B(u,v), v> = 0`; the fixed-cutoff bound `||D_N u|| <= C N^{5/2} ||u||^2`; the
    `M = 3, N = 1` counterexample as a theorem (`D_1 = 0`, error `!= 0`).
B3. `SGC/Bridge/InhomogeneousComparison.lean` - the abstract inhomogeneous estimate
    `||z(t)|| <= e^{int a} ||z(0)|| + int_0^t e^{int_s^t a} ||r(s)|| ds` in a normed space
    (fencing-lemma proof as in `AbstractBKM`), then its instantiation to B2 with the
    forcing tail and unresolved initial tail explicit. This is the correct L1 theorem;
    it is not new mathematics and will be cited as such.
B4. `CantorShiftTower.lean` docstring: rename the dictionary to what the theorem says
    (uniform fresh-symbol shift kernels; exact lumpability under deletion of the oldest
    symbol); remove the Moore identification; keep `HaltingCompiler` untouched.
B5. Re-run `lean-triage` on the branch; regenerate `AXIOMS.md`; replay from a clean
    checkout; push.

## 3. Block C - process

C1. Independent replay (Gate 1 of `lean-triage/STATUS.md`) by someone other than this
    session, now that the branch is public to the reviewer.
C2. Sandbox recipe (Gate 3) so the external `openai/NavierStokesAndEuler` artifact can be
    triaged and Comparator-checked rather than read.
C3. One more quiet external review of v0.2 before any wider circulation.

## 4. Decisions needed from Jason in the morning

1. Authorize block B (Lean edits on `cantor-layer-wip`, mirrored to `opus/two-horizons`)?
   Recommended: yes, B1 first - it is the smallest and the only item that adds a theorem
   nobody has written down for this setting.
2. Accept the reviewer's offer to draft the L1 specification? Recommended: yes.
3. Paper authorship line for v0.2: keep "with drafting assistance", or credit the
   reviewer for the counterexamples and the statistical theorem statement (their
   preference to be asked)?

## 5. The honest one-line status

Two theorems added today (`AbstractBKM`, `ResidualHorizon`), one conjecture retracted,
one theorem re-scoped (Bernoulli, not Moore), one prior-art lineage adopted (MP/CCRT),
one new theorem specified for tomorrow (statistical horizon). The finite-state theory
is intact; the fluid bridge is now a specification instead of an analogy.
