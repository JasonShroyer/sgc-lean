# Reply to the adversarial technical review, and three redirected questions

**From:** Jason Shroyer, SGC project
**Date:** 2026-09-12
**Re:** *Two Horizons* - your review of 2026-09-12 (filed verbatim at `docs/reviews/`)

---

## 1. Acknowledgement

Your review is accepted in full. Specifically we now hold:

- The Galerkin error is driven by the re-entry / closure term `R_N`, not by the leakage
  `D_N`; the two-wave `M = 3, N = 1` counterexample settles it without a continuum limit.
- `||D_N(u)||_2 <= C N^{5/2} ||u||_2^2` on `T^3`: bounded energy bounds every
  fixed-cutoff quantity. Conjecture 6.2 was false as stated and is retracted in the paper
  (v0.1.3, Section 6.2, original text kept for the record).
- The residual-controlled a posteriori idea is prior art: Morosi-Pizzocchero (6.20),
  (4.24)-(4.27), Section 7; Chernyshenko-Constantin-Robinson-Titi Thm 3 / Cor 5. We will
  cite both before any novelty sentence, and the correct first L1 theorem is the
  *inhomogeneous* energy/norm comparison with additive residual, not an instantiation of
  the homogeneous L0 hypothesis.
- Cheskidov-Shvydkoy: `Lambda in L^{5/2}` is the unconditional criterion; the `L^2`
  criterion carries `u in L^inf B^{-1}_{inf,inf}`; different determining cutoffs are
  different objects. Our Section 6.1' will be corrected accordingly.
- Time reversal excludes any nontrivial sign-even instantaneous monotone functional for
  unforced Euler at fixed `N`. The carve-outs you list (viscosity, accumulated integrals,
  an irreversible cutoff rule, restricted trajectory classes) are where anything of the
  kind can live.
- The sentence-level table (Section "Sentences requiring correction") is accepted item by
  item and will be applied in the next paper revision.

Per instruction from the project owner, **no change to the formalization is made in
response to this review at this time.** The Lean tree you will find is the state as of
your review plus one module (`ResidualHorizon`, a wrapper of Mathlib's approximate-
trajectories Gronwall, added before your note arrived and consistent with it: it is the
homogeneous-Lipschitz form and is labelled as such; your inhomogeneous energy version is
the correct next target and is *not* claimed).

## 2. Where the formalization is - immutable and accessible

Repository `JasonShroyer/sgc-lean` (private; you have or will receive read access).

- Branch: `opus/two-horizons` - an orphan branch; shares no history with any other branch.
- **Immutable commit for this audit:** `0096f90e5e5b5fdbdb5209b51cf5c25825183ff9`
  (plus one documentation commit adding this reply and your review; the Lean sources
  are byte-identical between the two).

```
git clone -b opus/two-horizons https://github.com/JasonShroyer/sgc-lean.git sgc-two-horizons
cd sgc-two-horizons
git checkout 0096f90e5e5b5fdbdb5209b51cf5c25825183ff9
elan toolchain install leanprover/lean4:v4.25.2
lake exe cache get && lake build       # our clean-checkout replay: 3140 jobs, no errors
```

The working development (everything, including speculative modules) is branch
`cantor-layer-wip`, head `3c8e623`. It is work in progress and is not the object of
this audit.

## 3. Organization of the branch (49 files)

```
README.md               theorem table: Lean declaration name -> informal statement; non-claims
AXIOMS.md               machine-derived ledger: kernel closure of all 170 headline theorems
                        (168 = {propext, Classical.choice, Quot.sound}; the 2 exceptions named),
                        38 declared axioms in supporting modules with consumer counts (0 for
                        headline theorems), cleanup obligations
CITATION.cff, LICENSE   Apache-2.0
lakefile.lean, lean-toolchain (4.25.2), lake-manifest.json (Mathlib pinned)

src/SGC.lean            curated root; headline modules documented first
src/SGC/Bridge/         KernelHorizon's continuous-time twin (DefectHorizonBridge),
                        TrajectoryClosure, ValidityHorizon, CurvatureUndecidability +
                        HaltingCompiler, CantorShiftTower, DiscreteFluidDynamics,
                        AbstractBKM (L0), ResidualHorizon
src/SGC/Renormalization/ Lumpability, Approximate, MeasureReentry, KernelHorizon,
                        CurvatureQuotient
src/SGC/{Axioms,Spectral,Geometry,Thermodynamics,Topology}/  transitive import closure only

docs/two-horizons.md    the paper (v0.1.3): labels KERNEL / EXTERNAL / FRAMING / CONJECTURE,
                        claim map in Section 9, retraction of 6.2 in place
docs/bkm-ladder.md      L0-L3 design note
docs/REVIEWER-COMMISSION.md, docs/REVIEWER-REDIRECT-2.md (this file)
docs/reviews/           your review, verbatim (md, pdf)
docs/receipts/          lean-triage receipts: opus-closure (170 theorems, 10 modules),
                        abstract-bkm, residual-horizon. Each has receipt.json (sealed;
                        verbatim kernel-printed statements + SHA-256, axiom closure with
                        origin, unused hypotheses, definition cone, probe witnesses, raw
                        probe output), findings.json, REPORT.md (rendered from the receipt
                        only). hash_self is computed after canonicalization (sorted keys,
                        compact separators, hash_self excluded).
```

For the theorem-and-receipt audit: `docs/receipts/opus-closure/receipt.json` ->
`evidence.candidates[*]` gives, per theorem, `statement`, `statement_sha256`, `axioms`
(with `origin`), `unused_hypotheses`, `definition_cone`; `evidence.trust_surface.axioms`
is the inventory behind `AXIOMS.md`; `evidence.raw_probe_output` is what the kernel probe
printed. `triage.checks_not_run` lists what did not run (kernel replay with
`lean4checker` was not available for 4.25.2; build was `--skip-build` against oleans
whose provenance is the recorded commit).

## 4. Three redirected questions

Your review answered the previous three. These are the ones your answers make decisive.

### Q1. Is the certified existence interval the right definition of a fluid validity horizon?

Morosi-Pizzocchero turn the Galerkin residual into a *certified existence time*
`T_cert(N; v_N)` computable from the approximate trajectory alone (their (4.26)-(4.27),
Section 7). That is exactly the shape of the SGC validity horizon, but rigorous, a
posteriori, and already in the literature.

*Is `T_cert(N; v_N)`, or the analogous certificate in Chernyshenko-Constantin-Robinson-Titi,
known to be monotone in `N` and to converge to the true maximal lifespan `T*(u_0)` as
`N -> inf` for smooth data? If so, then "the resolution required for a given tolerance
escapes to infinity at a singularity" becomes a statement about a computable functional,
and the retracted 6.2 has a correct successor: `N_eta(t) -> inf` iff `T_cert` saturates
below `T*` at every `N`. If not known, is there an obstruction (e.g. the unresolved
initial tail, or the strong-norm bootstrap) that prevents `T_cert` from being a
determining-resolution functional?*

Why: this decides whether SGC's central object for fluids should be *defined* as a
certified a posteriori interval rather than a norm of any defect - which would make our
"horizon" vocabulary exact, computable, and attributable to prior art in the right way.

### Q2. Definition-cone inspection of `CantorShiftTower`: is the computation axis formalized or only framed?

You asked to inspect the tower's definitions. You should: your suspicion is correct in a
specific way. `SGC.Bridge.CantorShiftTower.shiftKernel p n` is a **uniform Bernoulli
step** - a stochastic one-sided shift on depth-`n` cylinders (`Word p n`), i.e. the
Markov chain of the `p`-adic odometer / Bernoulli shift, not Moore's deterministic
bilateral generalized shift. `shiftTower_defect_zero` is the statement that this
*stochastic* tower is exactly lumpable at every depth (the quotient by `tailPartition`
is again the same Bernoulli step). As you note, finite-window observation of a
deterministic bilateral shift is not an autonomous factor.

*Given the actual definitions (please read `CantorShiftTower.lean`, ~230 lines): does
exact lumpability of the Bernoulli cylinder tower carry any content about Moore's
generalized shifts and their Turing simulation, or must the paper's Theorem 2.5 and the
"epsilon = 0 pole where computation lives" be re-scoped to "i.i.d.-input symbolic
dynamics is renormalization-transparent"? If the latter, what is the correct SGC object
for a deterministic generalized shift - a Markov partition / sofic coding under which the
deterministic map becomes a Markov chain with exact lumpability, or nothing of the kind?*

Why: this decides whether the computation axis of the paper is [KERNEL] or [FRAMING].
We would rather relabel now than defend the wrong label later.

### Q3. Should the SGC-fluid bridge be statistical rather than trajectory-wise?

Every SGC theorem is `pi`-weighted: the defect, the horizon bounds, the curvature
descent, the trust ledger all live on a finite state space *with a stationary measure*.
Fluid trajectories have no such `pi`; but Galerkin Navier-Stokes at fixed `nu > 0` is a
dissipative finite-dimensional system with a global attractor and invariant measures, and
the continuum has statistical solutions (Foias-Prodi determining modes;
Vishik-Fursikov; Constantin-Foias-Temam attractor dimension). Your time-reversal argument
also vanishes at `nu > 0`.

*Is the natural rigorous attachment point for a `pi`-weighted finite-state theory the
invariant measure of Galerkin Navier-Stokes - so that the SGC defect becomes an
expectation of the residual under the invariant measure, the validity horizon a
statistical determining-modes statement, and the "phase" question (Q3 of the earlier
commission) a question about the attractor rather than about individual trajectories?
Concretely: is the number of determining modes the finite-`N` rigorous form of "minimal
valid resolution", and is there any known monotone or Lyapunov-like structure for a
scale-resolved quantity under the invariant measure at `nu > 0` that survives your
reversal obstruction precisely because of dissipation?*

Why: if yes, the whole program moves from PDE trajectory analysis (where we have no edge)
to finite-dimensional dissipative systems with invariant measures (where every SGC tool
applies natively) and the continuum enters only through determining-modes theory. If no,
we learn that `pi`-weighting is the wrong currency for fluids and the finite-state theory
should stop claiming a fluid bridge.

## 5. What we will do with the answers

Record them verbatim under `docs/reviews/`; apply the sentence table to the paper;
then, and only then, decide the first L1 formalization - most likely your prescribed
order: the `M = 3, N = 1` counterexample and the fixed-cutoff energy bound as regression
tests, the residual identity and trilinear cancellation on an explicit Fourier state
space, the inhomogeneous comparison estimate with visible constants, and a citation pass
against Morosi-Pizzocchero and CCRT before any sentence containing the word "new".

Thank you. The exchange rate so far - one conjecture retracted, two mislabels caught,
one prior-art citation supplied, one theorem written - is the one we hoped for.

Jason Shroyer
