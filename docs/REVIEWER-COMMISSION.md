# Commission for external technical review

**From:** Jason Shroyer, SGC project
**To:** [reviewer]
**Date:** 2026-09-12
**Subject:** Review of the *Two Horizons* formalization and three questions that decide our next year

---

## 1. What we are asking you to do

Read one paper, inspect one repository branch, and answer three questions. We are not
asking for endorsement. We are asking for the fastest route to being wrong, if we are
wrong, and for direction if we are not. Your answers will decide whether we spend the
next year on level L1 of the ladder described below, and in which form.

We would rather hear "this is known" or "this is false" this month than build for a year.

## 2. Where everything is

**Repository.** Private GitHub repository `JasonShroyer/sgc-lean`, branch
`opus/two-horizons` (orphan branch, one commit, 48 files). You will receive read access.
Clone and build:

```
git clone -b opus/two-horizons <url> sgc-two-horizons
cd sgc-two-horizons
elan toolchain install leanprover/lean4:v4.25.2
lake exe cache get
lake build          # replayed by us from a clean checkout: 3138 jobs, no errors
```

**Read in this order.**

1. `README.md` - the theorem table with Lean declaration names, and the non-claims.
2. `docs/two-horizons.md` - the position paper. Every mathematical sentence carries a
   label: **[KERNEL]** (kernel-checked, declaration named), **[EXTERNAL]** (cited),
   **[FRAMING]** (analogy we have not proved), **[CONJECTURE]** (precise open target).
   Section 9 is a claim map: what each declaration does and does not establish.
3. `AXIOMS.md` - the axiom ledger, machine-derived. All 170 theorems in the ten headline
   modules have kernel closure `{propext, Classical.choice, Quot.sound}` except two
   documented non-headline theorems in `TrajectoryClosure`. The 38 declared axioms in
   *supporting* modules are listed with consumer counts; none is consumed by a headline
   theorem; cleanup obligations are stated.
4. `docs/bkm-ladder.md` - the L0-L3 ladder toward a Galerkin / continuum theorem.
5. `docs/receipts/` - the audit receipts (see Section 3).
6. The Lean sources, starting with `src/SGC/Bridge/AbstractBKM.lean` (150 lines, proved
   this week) and `src/SGC/Renormalization/KernelHorizon.lean`.

## 3. Why the documentation looks the way it does

The week of 2026-09-08 produced 2.3 million lines of machine-generated Lean and a credit
dispute. A kernel-checked proof settles logic, not modelling. We therefore adopted three
rules and ask you to hold us to them:

- **Labels, not prose.** No sentence in the paper claims more than its label. If you find
  one that does, that is a finding.
- **Receipts, not assertions.** Every number about axioms, statements, and hypotheses in
  `AXIOMS.md` and `README.md` comes from a sealed `receipt.json` produced by our audit
  tool (`lean-triage`): per-theorem kernel axiom closure, verbatim kernel-printed
  statement with SHA-256, unused-hypothesis check, definition cone, budgeted
  vacuity/triviality witnesses, repo-wide axiom inventory. `REPORT.md` is rendered only
  from the receipt. Nothing is hand-transcribed.
- **Closure, not imports.** We ship the full transitive import closure so the branch
  builds; trust is decided by kernel closure per theorem, and the ledger says exactly
  which theorems consume what. We chose to ship supporting axioms *with a ledger* rather
  than hand-prune imports and risk drift from the main development; the pruning is the
  next commit.

We have **not** built or replayed the external `openai/NavierStokesAndEuler` artifact;
we read its public source. Building untrusted Lean projects executes arbitrary code and
our threat model forbids it outside a sandbox. Everything we say about that artifact is
labelled accordingly.

## 4. The setting, in six lines

Finite-state generator `L`, partition `P`, coarse projector `Pi`, defect
`D = (I - Pi) L Pi`, `epsilon = ||D||_pi`. We have kernel-proven:

- **validity horizon** `T* ~ 1/epsilon`: the macro-law tracks the projected micro-dynamics
  for a time inverse in the defect (`kernel_closure_error_le`, `defect_horizon_bound`);
- the flows that *compute* (Moore's shift, realized by Cardona-Miranda-Peralta-Salas as
  Beltrami Euler flows) sit at `epsilon = 0` exactly (`shiftTower_defect_zero`), and a
  Beltrami field has zero Leray-projected nonlinearity, so its spectral truncation defect
  vanishes at every scale;
- an abstract **continuation budget** theorem: `||x'|| <= W ||x||` implies
  `||x(t)|| <= exp(int_0^t W) ||x(0)||` (`norm_le_exp_budget`), the shape of the
  Beale-Kato-Majda criterion.

The proposed L1 object is the spectral truncation defect on Galerkin Navier-Stokes,
`D_N(u) = (I - P_N) P (P_N u . grad) P_N u`, whose pairing with the field is the energy
flux across wavenumber `N`.

## 5. Questions already posed (context)

In an earlier round we asked: (i) is `D_N` the flux fluid dynamicists mean; (ii) is the
conjecture *no renormalization-transparent blowup* (BKM divergence forces
`||D_N|| -> inf` for every fixed `N`) known; (iii) is the correct continuum partner of
the validity horizon the Cheskidov-Shvydkoy determining wavenumber `Lambda(t)`, with
`int Lambda^2 dt` the budget to target. Please answer those if you can, briefly. The
three below are the ones we most need.

## 6. The three questions

### Q1. Is the Galerkin validity horizon a flux-controlled a posteriori error bound - and is that new?

Read our Kernel Horizon theorem on Galerkin Navier-Stokes literally. The SGC *coarse
trajectory* is the `N`-mode Galerkin solution `u_N(t)` (the projected dynamics run as an
autonomous macro-law). The SGC *projected fine trajectory* is `P_N u(t)`, the truncation
of the true solution. The Kernel Horizon theorem bounds their difference by the
accumulated defect along the trajectory:

```
||P_N u(t) - u_N(t)||  <=  int_0^t ||D_N(u(s))|| e^{C (t - s)} ds      (shape of defect_horizon_bound)
```

i.e. **the Galerkin approximation error is controlled by the energy flux through the
cutoff along the true solution**, with Gronwall growth. Classical Galerkin convergence
theory bounds this error by Sobolev norms and `N^{-s}`; flux is not the usual currency.

*Is a flux-controlled a posteriori Galerkin error bound of this form known? If not, is it
true, and is it provable at L1 with Gronwall alone (so that it is an honest corollary of
our L0 theorem), or does the Leray projector and the pressure make the "defect" fail to be
the thing that drives the error?*

Why this is the most valuable question: a yes-and-new answer gives SGC its first theorem
that a fluid dynamicist would want independently of our framing (an a posteriori
estimator for spectral DNS in physical units). A "known" answer gives us the citation and
lets us skip to L2. A "false because of the pressure" answer kills the naive L1 and tells
us what the defect must actually be.

### Q2. Does computation require zero flux?

This is the question our whole two-pole picture stands or falls on.

Every known realization of universal computation in a fluid (Cardona-Miranda-Peralta-Salas
2021; Dyhr et al. 2026) is *steady* or *stationary*, hence has zero energy flux across
every scale; in SGC terms `epsilon = 0`, the validity horizon is infinite, and the
symbolic layer is renormalization-transparent (`shiftTower_defect_zero`). Tao's
"computational blowup" blueprint, by contrast, needs a *time-dependent* flow that
computes while transferring energy to smaller scales. Our conjecture (paper, Section 6.2)
says the two are incompatible in the limit: a singularity destroys transparency at every
scale, so a computer cannot remain faithful through its own blowup.

*Is there any obstruction - known, folklore, or provable - to embedding a Turing machine
in a time-dependent Euler or Navier-Stokes flow with nonzero, scale-nonlocal energy flux?
Concretely: can a Moore shift be realized as a return map of a flow whose truncation
defect `D_N` is nonzero for infinitely many `N` on the time interval where the
computation runs? If yes, exhibit the mechanism or the reference; if no, what is the
theorem?*

Why this is decisive: if computation requires `epsilon = 0`, then (a) our two-pole
picture is a theorem-shaped fact, (b) Tao's program must run its computer in a
scale-window and hand off to an analytic collapse - which is what the 2026 constructions
did without any computer - and (c) our L1 target inherits a clean structural meaning. If
computation does *not* require zero flux, our framing is wrong in an instructive way, and
the counterexample is exactly the object a computational-blowup program needs.

### Q3. What quantity, if any, is monotone across the phase boundary?

Our picture has three phases for a divergence-free flow, indexed by the behaviour of
the truncation defect across scales:

| Phase | Defect `D_N` | Examples | Status |
|---|---|---|---|
| sealed crystal | `= 0` for all `N` | Beltrami / Reeb; Moore shift; the fluids that compute | KERNEL at the symbolic layer |
| finite cascade | `!= 0`, bounded uniformly in `N` on `[0, T]` | (regular turbulence?) | FRAMING |
| collapse | `-> inf` for every `N` as `t -> T*` | the 2026 blowup constructions; BKM divergence | CONJECTURE (6.2) |

If this is right, the unforced Clay question (A)/(B) is *whether an unforced flow can
leave the middle phase*. In every other renormalization picture we know, leaving a phase
requires a monotone quantity to cross a threshold (a c-theorem, an entropy, a free
energy). In SGC on finite state spaces we have candidates - the defect itself, the
Bakry-Emery curvature (which we proved descends along exact quotients), entropy
production - but no monotonicity theorem for the nonlinear flow.

*From the analyst's side: is there a known quantity, functional of the solution and the
scale, that is monotone along Euler or Navier-Stokes dynamics across scales and whose
finiteness or divergence separates regular cascades from collapse? If the honest answer
is "no such quantity is known and that is the problem", say so: it tells us to stop
looking for one in the finite-state theory and to aim L2 at the Cheskidov-Shvydkoy
criterion instead. If there is a candidate - a curvature, a helicity-like invariant, a
Lyapunov functional for the flux - it tells us which SGC observable to formalize first.*

Why this is the deep question: it converts our intuition ("computation lives at
`epsilon = 0`, blowup at `epsilon = inf`, regularity in between") into a testable
statement about an invariant, and it is the one question where a mathematician's
instinct about *what cannot exist* is worth more than any amount of formalization.

## 7. What a useful answer looks like

For each question, one of: **known** (with reference), **false** (with the simplest
counterexample you can state), **open** (with the sharpest formulation you would accept
as a theorem statement), or **ill-posed** (with what is wrong with the question). Two
paragraphs each is enough. If any label in the paper is wrong, name the sentence.

We will record your answers verbatim in the repository, attributed as you prefer, and
the next commit on this branch will be whatever they imply.

Thank you.

Jason Shroyer
